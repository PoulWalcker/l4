import Lint4.Finding
import Lean

namespace Lint4.DeclarationSafety

open Lean

def checkDeclaration (info implementation : ConstantInfo) (line : Nat) : CoreM (Array Finding) := do
  let mut findings := #[]
  if info.isUnsafe then
    findings := findings.push ⟨line, .unsafeCode, "Unsafe declaration"⟩
  if implementation.isPartial then
    findings := findings.push ⟨line, .partialRecursion, "Partial recursive definition"⟩
  let env ← getEnv
  let attrs := [(isExtern env info.name, "extern"), ((Compiler.getImplementedBy? env info.name).isSome, "implemented_by")]
  let names := attrs.filterMap fun (present, attr) => if present then some attr else none
  unless names.isEmpty do
    findings := findings.push ⟨line, .runtimeImplementation,
      s!"Runtime implementation uses {String.intercalate "/" names}; review the implementation boundary"⟩
  for axiomName in ← collectAxioms implementation.name do
    if axiomName == ``sorryAx then
      findings := findings.push ⟨line, .unfinishedProof, "Depends on sorryAx"⟩
    else unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      findings := findings.push ⟨line, .axiomDependency, s!"Depends on axiom {axiomName}"⟩
  return findings

def checkTerm (env : Environment) (stx : Syntax) (expr : Expr) (line : Nat) : Array Finding := Id.run do
  let mut findings := #[]
  if stx.isIdent || stx.isOfKind `Lean.Parser.Term.identProj then
    if (expr.getAppFn'.constName?.bind env.find?).any (·.isUnsafe) then
      findings := findings.push ⟨line, .unsafeCode, "Unsafe operation"⟩
  if expr.isSorry || expr.isConstOf ``sorryAx then
    findings := findings.push ⟨line, .unfinishedProof, "Depends on sorryAx"⟩
  if stx.isOfKind ``Parser.Term.unsafe then
    findings := findings.push ⟨line, .unsafeCode, "Unsafe operation"⟩
  return findings

end Lint4.DeclarationSafety
