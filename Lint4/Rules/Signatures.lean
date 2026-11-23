import Lint4.Frontend
import Lint4.Finding

namespace Lint4.SignatureChecks

open Lean Meta

private partial def signaturePositions (stx : Syntax) : Array String.Pos.Raw := Id.run do
  if stx.isQuot then return #[]
  if stx.isOfKind ``Parser.Command.declaration then
    let decl := stx[1]
    if [``Parser.Command.definition, ``Parser.Command.opaque, ``Parser.Command.abbrev].contains decl.getKind then
      return decl[1].getPos?.toArray
  return stx.getArgs.flatMap signaturePositions

private def binderLabel (arg : Expr) (index : Nat) : MetaM String := do
  let name := (← arg.fvarId!.getDecl).userName
  return if name.isAnonymous || name.hasMacroScopes then s!"#{index + 1}" else name.toString

private def constraint? (type : Expr) : MetaM (Option Expr) := do
  unless ← isProp type do return none
  return some (← simp type (← Simp.Context.mkDefault)).1.expr

private partial def inspectType (type : Expr) (atPath : String) (seen : NameMap Expr) : MetaM (Array String) := do
  let type := type.headBeta.consumeMData
  if let .letE _ _ value body _ := type then return ← inspectType (body.instantiate1 value) atPath seen
  if type.isProp || (← isProp type) then return #[]
  if type.isSort || type.isFVar then return #[s!"{atPath}: polymorphic type {← ppExpr type}"]
  if type.isForall then
    return ← forallTelescope type fun args result => do
      let mut issues := #[]
      for arg in args, i in [:args.size] do
        issues := issues ++ (← inspectType (← inferType arg) s!"{atPath} parameter {← binderLabel arg i}" seen)
      return issues ++ (← inspectType result s!"{atPath} result" seen)
  let .const name levels := type.getAppFn | return #[]
  if [``String, ``Int, ``Nat, ``Json].contains name then return #[s!"{atPath}: raw {name}"]
  let args := type.getAppArgs
  if [``IO, ``Option, ``Array, ``List, ``Except, ``Prod, ``Sum].contains name then
    let mut issues := #[]
    for arg in args do
      issues := issues ++ (← inspectType arg s!"{atPath} in {name}" seen)
    return issues
  if let some previous := seen.find? name then
    unless type != previous && type.occurs previous do return #[]
  let seen := seen.insert name type
  let env ← getEnv
  match env.find? name with
  | some (.defnInfo _) =>
    let some body ← unfoldDefinition? type | return #[]
    inspectType body s!"{atPath} via {name}" seen
  | some (.inductInfo ind) =>
    let mut issues := #[]
    for ctor in ind.ctors do
      if isPrivateName ctor then continue
      let ctorType ← inferType (mkAppN (mkConst ctor levels) (args.extract 0 ind.numParams))
      let fields ← forallTelescope ctorType fun fields _ => do
        let mut issues := #[]
        let types ← fields.mapM inferType
        let constraints ← types.filterMapM constraint?
        for field in fields, fieldType in types, i in [:fields.size] do
          if constraints.any (·.containsFVar field.fvarId!) then continue
          let label ← binderLabel field i
          issues := issues ++ (← inspectType fieldType s!"{atPath} field {ctor}.{label}" seen)
        return issues
      issues := issues ++ fields
    return issues
  | _ => return #[]

def check (file : ElaboratedFile) : IO (Array Finding) := do
  let positions := Std.HashSet.ofArray ((file.commands.flatMap signaturePositions).map (·.byteIdx))
  let action : MetaM (Array Finding) := do
    let mut findings := #[]
    for (name, info) in (← getEnv).constants.map₂ do
      let some ranges ← findDeclarationRangesCore? name | continue
      let pos := ranges.selectionRange.pos
      unless positions.contains (file.input.fileMap.ofPosition pos).byteIdx do continue
      let signature ← match info with
        | .defnInfo d =>
          if d.type.getForallBody.isSort && !d.type.getForallBody.isProp then
            unless d.hints.isAbbrev && d.value.getLambdaBody.isForall do continue
            lambdaTelescope d.value fun params body => mkForallFVars params body
          else pure d.type
        | .opaqueInfo d =>
          if d.type.getForallBody.isSort && !d.type.getForallBody.isProp then continue
          pure d.type
        | _ => continue
      let label := (privateToUserName name).toString
      let path := if signature.isForall then label else s!"{label} result"
      let issues ← inspectType signature path {}
      findings := findings ++ issues.map fun detail => ⟨pos.line, .noGo, "N06", detail⟩
    return findings
  let (findings, _) ← action.toIO { fileName := file.input.fileName, fileMap := file.input.fileMap } { env := file.env }
  return findings

end Lint4.SignatureChecks
