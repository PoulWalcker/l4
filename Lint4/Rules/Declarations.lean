import Lint4.Finding
import Lint4.Frontend

namespace Lint4.DeclarationChecks

open Lean

private def usesIO (env : Environment) (info : ConstantInfo) : Bool := Id.run do
  let bodyRefs := (info.value? true).toArray.flatMap Expr.getUsedConstants
  let calleeTypes := bodyRefs.filterMap fun name => (env.find? name).map (·.type)
  let mut pending := info.type.getUsedConstants ++ bodyRefs ++ calleeTypes.flatMap Expr.getUsedConstants
  let mut seen : NameSet := {}
  while let some name := pending.back? do
    pending := pending.pop
    if [``IO, ``EIO, ``BaseIO].contains name then return true
    if seen.contains name then continue
    seen := seen.insert name
    if let some (.defnInfo defn) := env.find? name then
      if defn.hints.isAbbrev then
        pending := pending ++ defn.value.getUsedConstants
  return false

def checkOne (info : ConstantInfo) (line : Nat) (pureModule : Bool) : CoreM (Array Finding) := do
  let env ← getEnv
  let mut findings := #[]
  if info.isUnsafe then
    findings := findings.push ⟨line, .noGo, "N03", "Unsafe declaration"⟩
  let implementation := ((env.find? (Compiler.mkUnsafeRecName info.name)).filter (·.isPartial)).getD info
  if implementation.isPartial then
    findings := findings.push ⟨line, .warning, "W10", "Partial recursive definition"⟩
  for axiomName in ← collectAxioms implementation.name do
    if axiomName == ``sorryAx then
      findings := findings.push ⟨line, .noGo, "N05", "Depends on sorryAx"⟩
    else unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      findings := findings.push ⟨line, .warning, "W11", s!"Depends on axiom {axiomName}"⟩
  if pureModule && usesIO env implementation then
    findings := findings.push ⟨line, .noGo, "I01", "Declaration type or body references an IO effect"⟩
  return findings

private def checkDeclarations (pureModule : Bool) : CoreM (Array Finding) := do
  let env ← getEnv
  let mut findings := #[]
  for (name, info) in env.constants.map₂ do
    let some ranges ← findDeclarationRangesCore? name | continue
    findings := findings ++ (← checkOne info ranges.selectionRange.pos.line pureModule)
  return findings

def check (file : ElaboratedFile) (pureModule : Bool) : IO (Array Finding) := do
  let (findings, _) ← (checkDeclarations pureModule).toIO
    { fileName := file.input.fileName, fileMap := file.input.fileMap } { env := file.env }
  return findings

end Lint4.DeclarationChecks
