import Lint4.Rules.Declarations
import Lint4.Rules.Terms
import Lint4.Rules.Source
import Lint4.Rules.Signatures

namespace Lint4

open Lean System

structure AuditPolicy where
  projectRoot : FilePath := "."
  pureModule : Bool := false
  specModule : Bool := false
  deniedModules : List Name := []

private partial def forbiddenChain (env : Environment) (root : FilePath) (denied : List Name)
    (mod : Name) : StateT (NameMap (Option (List Name))) IO (Option (List Name)) := do
  if denied.any (·.isPrefixOf mod) then return some [mod]
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
      if let some tail ← forbiddenChain env root denied dep.module then
        result := some (mod :: tail)
        break
  modify (·.insert mod result)
  return result

private def checkImports (file : ElaboratedFile) (policy : AuditPolicy) :
    StateT (NameMap (Option (List Name))) IO (Array Finding) := do
  if policy.deniedModules.isEmpty then return #[]
  let `(Parser.Module.header| $[module]? $[prelude]? $imports*) := file.header | return #[]
  let mut findings := #[]
  for stx in imports do
    if let `(Parser.Module.import| $[public]? $[meta]? import $[all]? $mod) := stx then
      if let some chain ← forbiddenChain file.env policy.projectRoot policy.deniedModules mod.getId then
        let line := (file.input.fileMap.toPosition (mod.raw.getPos?.getD 0)).line
        let path := String.intercalate " → " (chain.map toString)
        findings := findings.push ⟨line, .noGo, "I02", s!"Forbidden module dependency: {path}"⟩
  return findings

def auditSource (path : FilePath) (source : String) (policy : AuditPolicy) : IO (Array Finding) := do
  let file ← elaborateSource path source
  let declarations ← DeclarationChecks.check file policy.pureModule
  let terms ← TermChecks.check file policy.deniedModules policy.pureModule
  let signatures ← if policy.specModule then SignatureChecks.check file else pure #[]
  let findings := signatures ++ SourceChecks.check file ++ (← (checkImports file policy).run' {}) ++ declarations ++ terms
  let order := fun (a b : Finding) =>
    (compare a.line b.line |>.then (compare a.rule b.rule) |>.then (compare a.detail b.detail)).isLT
  return (findings.qsort order).toList.eraseReps.toArray

end Lint4
