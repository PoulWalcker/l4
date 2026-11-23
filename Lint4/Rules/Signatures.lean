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

private partial def disjointIndices (left right : Expr) : MetaM Bool := do
  if left == right || (← isProof left) then return false
  if let .lit a := left then
    if let .lit b := right then return a != b
  let some (a, xs) ← constructorApp? (← whnf left) | return false
  let some (b, ys) ← constructorApp? (← whnf right) | return false
  if a.name != b.name then return true
  for x in xs[a.numParams...*], y in ys[b.numParams...*] do
    if ← disjointIndices x y then return true
  return false

private structure FamilyPath where
  instances : ExprSet := {}
  shapes : ExprSet := {}
  parent? : Option Expr := none
  deriving Inhabited

private def FamilyPath.visit (path : FamilyPath) (type : Expr) (name : Name) : MetaM (Option FamilyPath) := do
  let key := type.abstract ((collectFVars {} type).fvarIds.map mkFVar)
  if path.instances.contains key then return none
  -- Changing a constructor tag changes reachability but does not grow an index.
  let shape := key.replace fun e => if e.isConst then some (mkConst .anonymous) else none
  let maxShapes := 64
  if !path.shapes.contains shape && path.shapes.size >= maxShapes && !path.parent?.any (key.occurs ·) then
    throwError "N06 could not finish inspecting {name} after {maxShapes} distinct instance shapes"
  return some ⟨path.instances.insert key, path.shapes.insert shape, some key⟩

private partial def inspectType (type : Expr) (atPath : String) (seen : NameMap FamilyPath) : MetaM (Array String) := do
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
  let some path ← ((seen.find? name).getD {}).visit type name | return #[]
  let seen := seen.insert name path
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
      let fields ← forallTelescope ctorType fun fields result => do
        let mut fixed : FVarSubst := {}
        for index in args[ind.numParams...*], ctorIndex in result.getAppArgs[ind.numParams...*] do
          let ctorIndex := fixed.apply ctorIndex
          if ← disjointIndices index ctorIndex then return #[]
          if fields.contains ctorIndex then
            fixed := fixed.insert ctorIndex.fvarId! index
        let mut issues := #[]
        let types ← fields.mapM fun field => return fixed.apply (← inferType field)
        let constraints ← types.filterMapM constraint?
        for field in fields, fieldType in types, i in [:fields.size] do
          if fixed.contains field.fvarId! || constraints.any (·.containsFVar field.fvarId!) then continue
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
      findings := findings ++ issues.map fun detail => ⟨pos.line, .unprotectedSignature, detail⟩
    return findings
  let (findings, _) ← action.toIO { fileName := file.input.fileName, fileMap := file.input.fileMap } { env := file.env }
  return findings

end Lint4.SignatureChecks
