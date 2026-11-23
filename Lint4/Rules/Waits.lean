import Lint4.Frontend
import Lint4.Expressions
import Lint4.Finding

namespace Lint4.WaitChecks

open Lean

private structure ClockGuard where
  line : Nat
  locals : LocalContext
  boundReadings : List Bool
  condition : Expr

private structure Evidence where
  loops : List Syntax.Range
  binders : Std.HashSet (Nat × FVarId) := {}
  clockBindingPositions : Std.HashSet Nat := {}
  clockGuards : List ClockGuard := []

private def readsClock (locals : LocalContext) (action : Expr) : Bool :=
  let action := underlyingAction locals action
  action.isConstOf ``IO.monoMsNow || action.isConstOf ``IO.monoNanosNow

private partial def clockDerived (locals : LocalContext) (bindings : Std.HashSet FVarId)
    (boundReadings : List Bool) (expr : Expr) : Bool :=
  let expr := resolveLocalValue locals expr
  match expr with
  | .bvar index => boundReadings[index]?.getD false
  | .fvar id => bindings.contains id
  | .app .. =>
    let arithmetic := [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div]
    arithmetic.any expr.isAppOf && expr.getAppArgs.any (clockDerived locals bindings boundReadings)
  | .proj _ _ value => clockDerived locals bindings boundReadings value
  | _ => false

private partial def stopsWaiting (expr : Expr) : Bool :=
  let expr := expr.consumeMData
  match expr.getAppFn'.constName?, expr.getAppArgs with
  | some ``MonadExcept.throw, _ | some ``MonadExceptOf.throw, _ => true
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

private def clockBindingPosition? (term : Elab.TermInfo) (expr : Expr) : Option Nat := do
  guard (term.stx.getKind == ``Parser.Term.doLetArrow)
  guard (expr.isAppOf ``Bind.bind)
  let #[_, _, _, _, action, _] := expr.getAppArgs | none
  guard (readsClock term.lctx action)
  return (← term.stx[3][0].getPos?).byteIdx

private def observe (file : ElaboratedFile) (context : Elab.ContextInfo)
    (info : Elab.Info) (evidence : Evidence) : Evidence := Id.run do
  let .ofTermInfo term := info | return evidence
  let some pos := term.stx.getPos? | return evidence
  let kind := term.stx.getKind
  if !(term.isBinder || kind == ``Parser.Term.doLetArrow || kind == ``Parser.Term.doIf) then
    return evidence
  let expr := (instantiateMVarsCore context.mctx term.expr).1.consumeMData
  if term.isBinder then
    let .fvar id := expr | return evidence
    return { evidence with binders := evidence.binders.insert (pos.byteIdx, id) }
  if let some binder := clockBindingPosition? term expr then
    return { evidence with clockBindingPositions := evidence.clockBindingPositions.insert binder }
  if kind == ``Parser.Term.doIf && evidence.loops.any (fun r => r.start <= pos && pos < r.stop) then
    if let some clockGuard := clockGuard? (file.input.fileMap.toPosition pos).line term.lctx expr then
      return { evidence with clockGuards := clockGuard :: evidence.clockGuards }
  return evidence

private def findingsForTree (file : ElaboratedFile) (loops : List Syntax.Range) (tree : Elab.InfoTree) : Array Finding := Id.run do
  let evidence := tree.foldInfo (observe file) { loops }
  let mut readers : Std.HashSet FVarId := {}
  for (pos, id) in evidence.binders.toList do
    if evidence.clockBindingPositions.contains pos then
      readers := readers.insert id
  let mut findings := #[]
  for clockGuard in evidence.clockGuards do
    if clockGuard.condition.getAppArgs.any (clockDerived clockGuard.locals readers clockGuard.boundReadings) then
      findings := findings.push ⟨clockGuard.line, .warning, "W09", "Clock-based limit on a wait"⟩
  return findings

def check (file : ElaboratedFile) : Array Finding := Id.run do
  let loops := file.commands.toList.flatMap loopRanges
  if loops.isEmpty then return #[]
  let mut findings := #[]
  for tree in file.infoTrees do
    findings := findings ++ findingsForTree file loops tree
  return findings

end Lint4.WaitChecks
