import Lint4.Rules.Source
import Lint4.Rules.Declarations
import Lint4.Rules.Terms

namespace Lint4

open Lean System

structure AuditPolicy where
  pureModule : Bool := false
  deniedModules : List Name := []

private def checkImports (file : ElaboratedFile) (deniedModules : List Name) : Array Finding :=
  file.importEnv.header.imports.filterMap fun imported =>
    if deniedModules.any (·.isPrefixOf imported.module) then
      some ⟨1, .noGo, "I02", s!"Forbidden module dependency: {imported.module}"⟩
    else none

private def findingsInOrder (left right : Finding) : Bool :=
  if left.line != right.line then left.line < right.line
  else if left.rule != right.rule then left.rule < right.rule
  else left.detail < right.detail

private def sortAndDeduplicate (findings : Array Finding) : Array Finding :=
  ((findings.qsort findingsInOrder).toList.eraseRepsBy fun left right =>
    left.rule != "N04" && left.line == right.line &&
      left.rule == right.rule && left.detail == right.detail).toArray

def auditSource (path : FilePath) (source : String) (policy : AuditPolicy) : IO (Array Finding) := do
  let file ← elaborateSource path source
  let blocks := SourceChecks.declarationBlocks file.commands
  let sourceFindings := SourceChecks.check source file blocks
  let declarationFindings ← DeclarationChecks.check file blocks policy.pureModule
  let importFindings := checkImports file policy.deniedModules
  let termFindings ← TermChecks.check file policy.deniedModules
  return sortAndDeduplicate (sourceFindings ++ declarationFindings ++ importFindings ++ termFindings)

end Lint4
