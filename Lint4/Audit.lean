import Lint4.Rules.Declarations
import Lint4.Rules.Terms
import Lint4.Rules.Source
import Lint4.Rules.Signatures

namespace Lint4

open Lean System

structure AuditPolicy where
  pureModule : Bool := false
  specModule : Bool := false
  deniedModules : List Name := []

private def checkImports (file : ElaboratedFile) (denied : List Name) : Array Finding := Id.run do
  let mut findings := #[]
  let `(Parser.Module.header| $[module]? $[prelude]? $imports*) := file.header | return #[]
  for stx in imports do
    if let `(Parser.Module.import| $[public]? $[meta]? import $[all]? $mod) := stx then
      if denied.any (·.isPrefixOf mod.getId) then
        let line := (file.input.fileMap.toPosition (mod.raw.getPos?.getD 0)).line
        findings := findings.push ⟨line, .noGo, "I02", s!"Forbidden module dependency: {mod.getId}"⟩
  return findings

def auditSource (path : FilePath) (source : String) (policy : AuditPolicy) : IO (Array Finding) := do
  let file ← elaborateSource path source
  let declarations ← DeclarationChecks.check file policy.pureModule
  let terms ← TermChecks.check file policy.deniedModules policy.pureModule
  let signatures ← if policy.specModule then SignatureChecks.check file else pure #[]
  let findings := signatures ++ SourceChecks.check file ++ checkImports file policy.deniedModules ++ declarations ++ terms
  let order := fun (a b : Finding) =>
    (compare a.line b.line |>.then (compare a.rule b.rule) |>.then (compare a.detail b.detail)).isLT
  return (findings.qsort order).toList.eraseReps.toArray

end Lint4
