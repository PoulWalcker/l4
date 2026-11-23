import Lint4.Expressions
import Lint4.Finding

namespace Lint4.WaitChecks

open Lean

private structure ClockGuard where
  line : Nat
  locals : LocalContext
  boundReadings : List Bool
  condition : Expr

structure Evidence where
  loops : List Syntax.Range
  binders : Std.HashSet (Nat × FVarId) := {}
  clockBindingPositions : Std.HashSet Nat := {}
  clockGuards : List ClockGuard := []

private partial def unlift (locals : LocalContext) (expr : Expr) : Expr :=
  let expr := resolveLocalValue locals expr
  match expr.getAppFn'.constName? with
  | some ``liftM | some ``MonadLift.monadLift | some ``MonadLiftT.monadLift =>
    match expr.getAppArgs.back? with
    | some action => unlift locals action
    | none => expr
  | _ => expr

private def isTimer (locals : LocalContext) (expr : Expr) : Bool :=
  let expr := unlift locals expr
  expr.isAppOf `Std.Async.sleep || expr.isAppOf ``IO.sleep

private def timerBranch (locals : LocalContext) (expr : Expr) : Bool :=
  let expr := unlift locals expr
  if isTimer locals expr then true
  else
    match expr.getAppFn'.constName?, expr.getAppArgs with
    | some ``Bind.bind, #[_, _, _, _, action, .lam _ _ result _] =>
      isTimer locals action && (result.isAppOf ``Pure.pure || result.isAppOf ``MonadExcept.throw)
    | _, _ => false

private def racesAgainstTimer (locals : LocalContext) (expr : Expr) : Bool := Id.run do
  let some name := expr.getAppFn'.constName? | return false
  let args := expr.getAppArgs
  let branches := match name, args with
    | `Std.Async.Async.race, #[_, _, first, second, _]
    | `Std.Async.BaseAsync.race, #[_, _, first, second, _]
    | `Std.Async.ContextAsync.race, #[_, _, first, second, _]
    | `Std.Async.EAsync.race, #[_, _, _, first, second, _] => some (first, second)
    | _, _ => none
  return match branches with
  | some (first, second) => timerBranch locals first != timerBranch locals second
  | none => false

private def readsClock (locals : LocalContext) (action : Expr) : Bool :=
  let action := unlift locals action
  action.isConstOf ``IO.monoMsNow || action.isConstOf ``IO.monoNanosNow

private partial def clockDerived (locals : LocalContext) (bindings : Std.HashSet FVarId)
    (boundReadings : List Bool) (expr : Expr) : Bool :=
  let expr := resolveLocalValue locals expr
  match expr with
  | .bvar index => boundReadings[index]?.getD false
  | .fvar id => bindings.contains id
  | .app .. => expr.getAppArgs.any (clockDerived locals bindings boundReadings)
  | .proj _ _ value => clockDerived locals bindings boundReadings value
  | _ => false

private partial def stopsWaiting (expr : Expr) : Bool :=
  let expr := expr.consumeMData
  match expr.getAppFn'.constName?, expr.getAppArgs with
  | some ``MonadExcept.throw, _ => true
  | some ``Pure.pure, #[_, _, _, value] => value.isAppOf ``ForInStep.done
  | some ``Bind.bind, #[_, _, _, _, action, .lam _ _ body _] =>
    stopsWaiting action || stopsWaiting body
  | _, _ =>
    match expr with
    | .lam _ _ body _ | .letE _ _ _ body _ => stopsWaiting body
    | _ => false

private partial def clockGuard? (line : Nat) (locals : LocalContext)
    (expr : Expr) (boundReadings : List Bool := []) : Option ClockGuard :=
  let expr := resolveLocalValue locals expr
  match expr.getAppFn'.constName?, expr.getAppArgs with
  | some ``Bind.bind, #[_, _, _, _, action, .lam _ _ body _] =>
    clockGuard? line locals body (readsClock locals action :: boundReadings)
  | some ``ite, #[_, condition, _, first, second]
  | some ``dite, #[_, condition, _, first, second] =>
    let condition := resolveLocalValue locals condition
    match condition.getAppFn'.constName? with
    | some ``LT.lt | some ``LE.le | some ``GT.gt | some ``GE.ge =>
      if stopsWaiting first != stopsWaiting second then
        some { line, locals, boundReadings, condition }
      else none
    | _ => none
  | _, _ => none

private partial def loopRanges (stx : Syntax) : List Syntax.Range :=
  let nested := stx.getArgs.toList.flatMap loopRanges
  match stx.getKind with
  | ``Parser.Term.doWhile | ``Parser.Term.doRepeat | ``Parser.Term.doRepeatUntil |
    ``Parser.Term.doFor => stx.getRange?.toList ++ nested
  | _ => nested

private def referencesTimer (env : Environment) (expr : Expr) : Bool := Id.run do
  let mut expr := expr
  let mut seen : NameSet := {}
  repeat
    let some name := (resolveLocalValue {} expr.getLambdaBody).getAppFn'.constName? | return false
    if [``IO.sleep, `Std.Async.sleep, `Std.Async.Selector.sleep].contains name then return true
    if seen.contains name then return false
    seen := seen.insert name
    let some (.defnInfo info) := env.find? name | return false
    expr := info.value
  return false

def start (commands : Array Syntax) : Evidence :=
  { loops := commands.toList.flatMap loopRanges }

def observeBinder (evidence : Evidence) (pos : String.Pos.Raw) (id : FVarId) : Evidence :=
  { evidence with binders := evidence.binders.insert (pos.byteIdx, id) }

private def clockBindingPosition? (term : Elab.TermInfo) (expr : Expr) : Option Nat := do
  guard (term.stx.getKind == ``Parser.Term.doLetArrow)
  guard (expr.isAppOf ``Bind.bind)
  let #[_, _, _, _, action, _] := expr.getAppArgs | none
  guard (readsClock term.lctx action)
  return (← term.stx[3][0].getPos?).byteIdx

def observeTerm (evidence : Evidence) (env : Environment) (term : Elab.TermInfo)
    (expr : Expr) (pos : String.Pos.Raw) (line : Nat) : Evidence × Array Finding := Id.run do
  let mut findings := #[]
  if referencesTimer env (resolveLocalValue term.lctx expr) then
    findings := findings.push ⟨line, .noGo, "N02", "Manual timer or wait"⟩
  if term.stx.getKind == ``Parser.Term.app && racesAgainstTimer term.lctx expr then
    findings := findings.push ⟨line, .warning, "W09", "Race against a timer"⟩

  let mut evidence := evidence
  if let some binder := clockBindingPosition? term expr then
    evidence := { evidence with clockBindingPositions := evidence.clockBindingPositions.insert binder }
  if term.stx.getKind == ``Parser.Term.doIf && evidence.loops.any (fun r => r.start <= pos && pos < r.stop) then
    if let some clockGuard := clockGuard? line term.lctx expr then
      evidence := { evidence with clockGuards := clockGuard :: evidence.clockGuards }
  return (evidence, findings)

def finish (evidence : Evidence) : Array Finding := Id.run do
  let mut readers : Std.HashSet FVarId := {}
  for (pos, id) in evidence.binders.toList do
    if evidence.clockBindingPositions.contains pos then
      readers := readers.insert id
  let mut findings := #[]
  for clockGuard in evidence.clockGuards do
    if clockDerived clockGuard.locals readers clockGuard.boundReadings clockGuard.condition then
      findings := findings.push ⟨clockGuard.line, .warning, "W09", "Clock-based limit on a wait"⟩
  return findings

end Lint4.WaitChecks
