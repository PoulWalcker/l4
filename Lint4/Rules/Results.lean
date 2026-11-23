import Lint4.Expressions
import Lint4.Finding

namespace Lint4.ResultChecks

open Lean

private partial def usesProcessPipe (locals : LocalContext) (expr : Expr) : MetaM Bool := do
  let expr := resolveLocalValue locals expr
  let env ← getEnv
  let structure? := match expr with
    | .proj name _ _ => some name
    | _ => expr.getAppFn'.constName?.bind env.getProjectionStructureName?
  if structure? == some ``IO.Process.Child then
    return (← Meta.whnf (← Meta.inferType expr)).isConstOf ``IO.FS.Handle
  expr.getAppArgs.anyM (usesProcessPipe locals)

private def discardedIOValue (context : Elab.ContextInfo) (term : Elab.TermInfo) : IO Bool := do
  let expr := term.expr.consumeMData
  let kind := term.stx.getKind
  let discardCall := kind == ``Parser.Term.app && expr.isAppOf ``Functor.discard
  let wildcardBind := kind == ``Parser.Term.doLetArrow &&
    term.stx[3][0].getKind == ``Parser.Term.hole && expr.isAppOf ``Bind.bind
  unless discardCall || wildcardBind do return false
  term.runMetaM context do
    let args := (← instantiateMVars expr).getAppArgs
    let discarded := match discardCall, args with
      | true, #[monad, type, _, action] | false, #[monad, _, type, _, action, _] =>
        some (monad, type, action)
      | _, _ => none
    let some (monad, type, action) := discarded | return false
    unless monad.isConstOf ``IO || monad.isAppOf ``EIO do return false
    let action := resolveLocalValue term.lctx action
    let type ← Meta.whnf type
    if type.isConstOf ``Unit || type.isConstOf ``PUnit then return false
    if type.isAppOf ``Except then return true
    if action.isAppOf ``Pure.pure then return false
    if type.isConstOf ``IO.Process.Output then return true
    if action.isAppOf ``IO.Process.spawn || action.isAppOf ``IO.FS.readFile ||
        action.isAppOf ``IO.FS.readBinFile then return true
    usesProcessPipe term.lctx action

private def unusedExcept (context : Elab.ContextInfo) (term : Elab.TermInfo) : IO Bool := do
  unless [``Parser.Term.let, ``Parser.Term.doLet].contains term.stx.getKind do return false
  term.runMetaM context do
    let .letE _ type _ body _ := (← instantiateMVars term.expr).consumeMData | return false
    return (← Meta.whnf type).isAppOf ``Except && !body.hasLooseBVar 0

private def uncheckedProcessOutput (context : Elab.ContextInfo) (term : Elab.TermInfo) : IO Bool := do
  if term.stx.getKind == ``Parser.Term.do then return false
  term.runMetaM context do
    let expr := (← instantiateMVars term.expr).consumeMData
    unless expr.isAppOf ``Bind.bind do return false
    let #[monad, _, type, _, action, continuation] := expr.getAppArgs | return false
    unless monad.isConstOf ``IO || monad.isAppOf ``EIO do return false
    unless (← Meta.whnf type).isConstOf ``IO.Process.Output do return false
    if action.isAppOf ``Pure.pure then return false
    Meta.lambdaTelescope continuation fun binders body => do
      let some output := binders[0]? | return false
      let .fvar id := output | return false
      let fields := [``IO.Process.Output.stdout, ``IO.Process.Output.stderr]
      let env ← getEnv
      let indices := fields.filterMap fun field => (env.getProjectionFnInfo? field).map (·.i)
      let remaining := body.replace fun part =>
        let textField := fields.any (part.isAppOf ·) && part.getAppArgs.back? == some output
        let projection := match part with
          | .proj structName index value => structName == ``IO.Process.Output && indices.contains index && value == output
          | _ => false
        if textField || projection then some (mkStrLit "") else none
      return body.containsFVar id && !remaining.containsFVar id

private partial def knownTruth (locals : LocalContext) (expr : Expr) : MetaM (Option Bool) := do
  let expr := resolveLocalValue locals expr
  if expr.isConstOf ``True || expr.isConstOf ``Bool.true then return some true
  if expr.isConstOf ``False || expr.isConstOf ``Bool.false then return some false
  match expr.getAppFn.constName?, expr.getAppArgs with
  | some ``BEq.beq, #[type, inst, left, right] =>
    if resolveLocalValue locals left != resolveLocalValue locals right then return none
    let law ← Meta.mkAppOptM ``LawfulBEq #[some type, some inst]
    return if (← Meta.synthInstance? law).isSome then some true else none
  | some ``Eq, #[type, left, right] =>
    if resolveLocalValue locals left == resolveLocalValue locals right then return some true
    if type.isConstOf ``Bool && right.isConstOf ``Bool.true then return ← knownTruth locals left
    return none
  | _, _ => return none

private def errorGuard? (expr : Expr) : Option (Expr × Bool) := do
  let some ``ite := expr.getAppFn.constName? | none
  let #[_, condition, _, yes, no] := expr.getAppArgs | none
  let success := fun (e : Expr) => (e.isAppOf ``Pure.pure || e.isAppOf ``Except.ok) &&
    e.getAppArgs.back?.any (fun value => value.isConstOf ``Unit.unit || value.isConstOf ``PUnit.unit)
  let failure := fun (e : Expr) => e.isAppOf ``MonadExcept.throw || e.isAppOf ``MonadExceptOf.throw || e.isAppOf ``Except.error
  if success yes && failure no then some (condition, true)
  else if failure yes && success no then some (condition, false) else none

private partial def checkedCondition? (expr : Expr) (seen : NameSet := {}) : MetaM (Option (Expr × Bool)) := do
  let some name := expr.getAppFn.constName? | return none
  if seen.contains name then return none
  let some (.defnInfo info) := (← getEnv).find? name | return none
  Meta.lambdaTelescope info.value fun params body => do
    let body := resolveLocalValue {} body
    let gate ← match errorGuard? body with
      | some (condition, success) => pure do
        let some ``Eq := condition.getAppFn.constName? | none
        let #[type, input, value] := condition.getAppArgs | none
        if type.isConstOf ``Bool && value.isConstOf ``Bool.true then some (input, success) else none
      | none => checkedCondition? body (seen.insert name)
    let some (input, success) := gate | return none
    let some index := params.findIdx? (· == input) | return none
    return (expr.getAppArgs[index]?).map (·, success)

private def vacuousCheck (context : Elab.ContextInfo) (term : Elab.TermInfo) : IO Bool := do
  if [``Parser.Term.do, ``Parser.Term.let, ``Parser.Term.doLet].contains term.stx.getKind then return false
  term.runMetaM context do
    let expr := resolveLocalValue term.lctx (← instantiateMVars term.expr)
    let gate ← if expr.isAppOf ``IO.ofExcept then
        match expr.getAppArgs.back? with
        | some action => checkedCondition? (resolveLocalValue term.lctx action)
        | none => pure none
      else match errorGuard? expr with
        | some gate => pure (some gate)
        | none => checkedCondition? expr
    let some (condition, success) := gate | return false
    return (← knownTruth term.lctx condition) == some success

private def checkDiscardedResults (context : Elab.ContextInfo) (term : Elab.TermInfo)
    (line : Nat) : IO (Array Finding) := do
  let mut findings := #[]
  if ← discardedIOValue context term then
    findings := findings.push ⟨line, .warning, "W16", "Discarded IO result"⟩
  if ← unusedExcept context term then
    findings := findings.push ⟨line, .warning, "W16", "Unused pure Except result"⟩
  if ← uncheckedProcessOutput context term then
    findings := findings.push ⟨line, .warning, "W16", "Process output text used without observing exit status"⟩
  return findings

def check (context : Elab.ContextInfo) (term : Elab.TermInfo) (line : Nat) : IO (Array Finding) := do
  let findings ← checkDiscardedResults context term line
  if ← vacuousCheck context term then
    return findings.push ⟨line, .warning, "W17", "Check always succeeds"⟩
  return findings

end Lint4.ResultChecks
