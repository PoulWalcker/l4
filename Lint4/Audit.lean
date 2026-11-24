import Lint4.Rules.AssertionsAndErrors
import Lint4.Rules.Branches
import Lint4.Rules.Calls
import Lint4.Rules.Comments
import Lint4.Rules.DeclarationSafety
import Lint4.Rules.DiscardedResults
import Lint4.Rules.DomainSignatures
import Lint4.Rules.PureModules

namespace Lint4

open Lean System

structure AuditPolicy where
  pureRoot? : Option System.FilePath := none
  specModule : Bool := false

private def resolvePolicy (path root : FilePath) : IO AuditPolicy := do
  let parent ← realPathNormalized (path.parent.getD root)
  let target ← realPathNormalized path
  let policy : AuditPolicy := { specModule := parent.components.contains "spec" || target.components.contains "spec" }
  let pureDir := root / "pure"
  unless ← pureDir.isDir do return policy
  let prefixPath := (← realPathNormalized pureDir).components
  if prefixPath.isPrefixOf parent.components || prefixPath.isPrefixOf target.components then
    return { policy with pureRoot? := some (← realPathNormalized root) }
  return policy

private def checkDeclaration (info : ConstantInfo) (line : Nat) (pureModule : Bool) : CoreM (Array Finding) := do
  let env ← getEnv
  let implementation := ((env.find? (Compiler.mkUnsafeRecName info.name)).filter (·.isPartial)).getD info
  let findings ← DeclarationSafety.checkDeclaration info implementation line
  if pureModule then return findings ++ (PureModules.checkDeclaration env implementation line).toArray
  return findings

private def checkDeclarations (file : ElaboratedFile) (policy : AuditPolicy) : MetaM (Array Finding) := do
  let env ← getEnv
  let signatures := if policy.specModule then DomainSignatures.declarationOffsets file.commands else {}
  let mut findings := #[]
  for (name, info) in env.constants.map₂ do
    let some ranges ← findDeclarationRangesCore? name | continue
    let pos := ranges.selectionRange.pos
    findings := findings ++ (← checkDeclaration info pos.line policy.pureRoot?.isSome)
    if !signatures.isEmpty && signatures.contains (file.input.fileMap.ofPosition pos).byteIdx then
      findings := findings ++ (← DomainSignatures.check info pos.line)
  return findings

private def checkTerm (pureModule : Bool) (context : Elab.ContextInfo)
    (term : Elab.TermInfo) (line : Nat) : IO (Array Finding × Option Syntax.Range) := do
  let expr := (instantiateMVarsCore context.mctx term.expr).1.consumeMData
  let kind := term.stx.getKind
  let mut findings := Calls.check context term expr line ++ DeclarationSafety.checkTerm context.env term.stx expr line
  if pureModule then
    findings := findings ++ (PureModules.checkReference context.env expr line).toArray
  term.runMetaM context do
    let discarded ← DiscardedResults.check term.stx expr line
    let result ← match discarded with
      | some (f, _) => pure (some f)
      | none => AssertionsAndErrors.check term.stx expr context.fileMap line
    let branch ← Branches.check kind expr line
    return (findings ++ result.toArray ++ branch.toArray, discarded.bind Prod.snd)

private def checkTerms (file : ElaboratedFile) (pureModule : Bool) : IO (Array (Nat × Finding)) := do
  let mut findings : Array (Nat × Finding) := #[]
  for tree in file.infoTrees do
    let (rows, _) ← tree.foldInfoM (init := (findings, (#[] : Array Syntax.Range))) fun context info (rows, unused) => do
      let some pos := info.stx.getPos? | return (rows, unused)
      let line := (file.input.fileMap.toPosition pos).line
      if let some traceFinding := Calls.debugTrace? info.stx line then return (rows.push (0, traceFinding), unused)
      let .ofTermInfo term := info | return (rows, unused)
      if term.stx.isToken "example" then
        if let some decl := term.expr.constName?.bind context.env.find? then
          let hits ← context.runCoreM (checkDeclaration decl line pureModule)
          return (rows ++ hits.map (0, ·), unused)
      if term.isBinder then return (rows, unused)
      let (hits, span) ← checkTerm pureModule context term line
      let unused := span.elim unused unused.push
      let located := hits.filterMap fun hit => Id.run do
        if hit.rule == .skippedAssertion || hit.rule == .wholeJsonEquality then
          if unused.any (·.contains pos) then return none
          return some (pos.byteIdx, hit)
        if hit.rule == .emptyHandler || hit.rule == .caughtFailure then return some (pos.byteIdx, hit)
        return some (0, hit)
      return (rows ++ located, unused)
    findings := rows
  return findings

def auditSource (path : FilePath) (source : String) (policy : AuditPolicy) (mainModule : Name) : IO (Array Finding) := do
  let file ← elaborateSource path source mainModule
  let (declarations, _) ← (checkDeclarations file policy).toIO
    { fileName := file.input.fileName, fileMap := file.input.fileMap } { env := file.env }
  let terms ← checkTerms file policy.pureRoot?.isSome
  let imports ← match policy.pureRoot? with
    | some root => PureModules.checkImports file root
    | none => pure #[]
  let findings := (Comments.check file ++ imports ++ declarations).map (0, ·) ++ terms
  let order := fun (a b : Nat × Finding) =>
    (compare a.2.line b.2.line |>.then (compare a.2.rule.code b.2.rule.code)
      |>.then (compare a.2.detail b.2.detail) |>.then (compare a.1 b.1)).isLT
  return (findings.qsort order).toList.eraseReps.toArray.map Prod.snd

def auditFile (path : FilePath) : IO (Array Finding) := do
  IO.withStdout (← IO.getStderr) do
    let packageRoot ← projectRoot? path
    let root ← match packageRoot with
      | some root => pure root
      | none => realPathNormalized (← IO.currentDir)
    let policy ← resolvePolicy path root
    let mainModule ← initializeLean path packageRoot
    auditSource path (← IO.FS.readFile path) policy mainModule

end Lint4
