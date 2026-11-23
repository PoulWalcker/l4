import Lint4.Finding
import Lint4.Frontend

namespace Lint4.DeclarationChecks

open Lean

private def jsonOnBothSides (signature : Expr) : Bool :=
  let mentionsJson := fun (e : Expr) => e.getUsedConstants.contains ``Json
  let rec visit (type : Expr) (hasInput : Bool) : Bool :=
    match type with
    | .forallE _ domain body _ => visit body (hasInput || mentionsJson domain)
    | _ => hasInput && mentionsJson type
  visit signature false

private def isIOName (name : Name) : Bool :=
  [``IO, ``EIO, ``BaseIO].any (fun root => root.isPrefixOf name)

private def usesIO (env : Environment) (roots : Array Name) : Bool := Id.run do
  let mut todo := roots
  let mut seen : NameSet := {}
  while let some name := todo.back? do
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    if isIOName name then return true
    if let some (.defnInfo info) := env.find? name then
      todo := todo ++ info.value.getUsedConstants
  return false

private def standardAxiom (env : Environment) (name : Name) : Bool :=
  match (env.getModuleIdxFor? name).bind (fun index => env.header.moduleNames[index]?) with
  | some origin => [`Init, `Lean, `Std, `Lake].any (fun root => root.isPrefixOf origin)
  | none => false

private def declarationFindings (pureModule : Bool) (map : FileMap)
    (blocks : Array Syntax) : MetaM (Array Finding) := do
  let env ← getEnv
  let mut findings := #[]
  for (name, info) in env.constants.map₂ do
    let some ranges ← findDeclarationRangesCore? name | continue
    let line := ranges.selectionRange.pos.line
    let source := blocks.find? fun block =>
      (block[1][1].getPos?.map map.toPosition) == some ranges.selectionRange.pos
    if info.isUnsafe then
      findings := findings.push ⟨line, .noGo, "N03", "Unsafe declaration"⟩
    let axioms ← collectAxioms name
    if axioms.contains ``sorryAx then
      findings := findings.push ⟨line, .noGo, "N05", "Declaration depends on sorryAx"⟩
    for axiomName in axioms do
      unless axiomName == ``sorryAx || standardAxiom env axiomName do
        findings := findings.push ⟨line, .warning, "W11", s!"Depends on axiom {axiomName}"⟩
    if pureModule && usesIO env
        (info.type.getUsedConstants ++ (info.value? true).toArray.flatMap Expr.getUsedConstants) then
      findings := findings.push ⟨line, .noGo, "I01", "IO dependency in declared pure module"⟩
    if source.any (fun stx => stx[1].getKind == ``Parser.Command.definition) then
      let strings ← Meta.forallTelescopeReducing info.type fun args _ => do
        return (← args.filterM fun arg => return (← Meta.whnf (← Meta.inferType arg)).isConstOf ``String).size
      if strings >= 2 then
        findings := findings.push ⟨line, .couldBeBetter, "W05", "Several arguments use String; review domain types"⟩
    if let .defnInfo defn := info then
      if jsonOnBothSides defn.type ||
          (defn.hints.isAbbrev && jsonOnBothSides defn.value.getLambdaBody) then
        findings := findings.push ⟨line, .warning, "W06", "JSON used on both sides of an API"⟩
    if source.any (fun stx => stx[1].getKind == ``Parser.Command.structure &&
        stx[1][0].getKind == ``Parser.Command.structureTk) && isStructure env name then
      let types ← Meta.forallTelescopeReducing info.type fun params _ => do
        let type := mkAppN (mkConst name (info.levelParams.map Level.param)) params
        Meta.withLocalDeclD `self type fun self =>
          (getStructureFieldsFlattened env name false).mapM fun field => do
            Meta.whnf (← Meta.inferType (← Meta.mkProjection self field))
      for (type, rule, detail) in
          [(``String, "W07", "Three or more String fields; review domain types"),
           (``Bool, "W08", "Three or more Bool fields; review state model")] do
        if (types.filter (·.isConstOf type)).size >= 3 then
          findings := findings.push ⟨line, .couldBeBetter, rule, detail⟩
  return findings

def check (file : ElaboratedFile) (blocks : Array Syntax) (pureModule : Bool) : IO (Array Finding) := do
  let (findings, _) ← (declarationFindings pureModule file.input.fileMap blocks).toIO
    { fileName := file.input.fileName, fileMap := file.input.fileMap } { env := file.env }
  return findings

end Lint4.DeclarationChecks
