import Lint4.Finding
import Lint4.ReadLeanModule

namespace Lint4.PureModules

open Lean System

private def forbiddenInPure (moduleName : Lean.Name) : Bool :=
  [`io, `jobs].any (·.isPrefixOf moduleName)

private partial def forbiddenChain (env : Environment) (root : FilePath)
    (mod : Name) : StateT (NameMap (Option (List Name))) IO (Option (List Name)) := do
  if forbiddenInPure mod then return some [mod]
  if let some result := (← get).find? mod then return result
  let path ← findOLean mod
  let mut result := none
  if root.components.isPrefixOf (← realPathNormalized path).components then
    let loaded : Option ModuleData := do
      let idx ← env.getModuleIdx? mod
      guard (env.header.modules[idx.toNat]?.any EffectiveImport.hasData)
      env.header.moduleData[idx.toNat]?
    let imports ← match loaded with
      | some data => pure data.imports
      | none => pure (← readModuleData path).1.imports
    for dep in imports do
      if let some tail ← forbiddenChain env root dep.module then
        result := some (mod :: tail)
        break
  modify (·.insert mod result)
  return result

private def findImports (file : ElaboratedFile) (root : FilePath) :
    StateT (NameMap (Option (List Name))) IO (Array Finding) := do
  let `(Parser.Module.header| $[module]? $[prelude]? $imports*) := file.header | return #[]
  let mut findings := #[]
  for stx in imports do
    if let `(Parser.Module.import| $[public]? $[meta]? import $[all]? $mod) := stx then
      if let some chain ← forbiddenChain file.env root mod.getId then
        let line := (file.input.fileMap.toPosition (mod.raw.getPos?.getD 0)).line
        let path := String.intercalate " → " (chain.map toString)
        findings := findings.push ⟨line, .forbiddenDependency, s!"Forbidden module dependency: {path}"⟩
  return findings

def checkImports (file : ElaboratedFile) (root : FilePath) : IO (Array Finding) :=
  (findImports file root).run' {}

def checkReference (env : Environment) (expr : Expr) (line : Nat) : Option Finding := do
  let name ← match expr with
    | .proj structureName _ _ => some structureName
    | _ => expr.getAppFn'.constName?
  let index ← env.getModuleIdxFor? name
  let origin ← env.header.moduleNames[index]?
  guard (forbiddenInPure origin)
  return ⟨line, .forbiddenDependency, s!"Forbidden module dependency: {name} from {origin}"⟩

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

def checkDeclaration (env : Environment) (info : ConstantInfo) (line : Nat) : Option Finding :=
  if usesIO env info then some ⟨line, .effectInPureModule, "Declaration type or body references an IO effect"⟩ else none

end Lint4.PureModules
