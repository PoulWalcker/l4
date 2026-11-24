import Lint4.LeanExpressions
import Lint4.Finding

namespace Lint4.AssertionsAndErrors

open Lean

private def standardUnit (expr : Expr) : Bool :=
  (standardPureResult? expr).any fun v => v.isConstOf ``Unit.unit || v.isConstOf ``PUnit.unit

private def errorChannel (inst : Expr) : Expr :=
  if inst.isAppOf ``instMonadExceptOfMonadExceptOf then inst.appArg! else inst

private def standardChannel (channel : Expr) : Bool :=
  channel.isAppOf ``instMonadExceptOfEIO || channel.isAppOf ``instMonadExceptOfExcept ||
    (channel.isAppOfArity ``instMonadExceptOfExceptTOfMonad 3 && standardMonad channel.appArg!)

private def standardFailure (expr : Expr) : Bool :=
  expr.isAppOf ``Except.error || ((isFailure expr || expr.isAppOf ``throwThe) &&
    expr.getAppArgs[2]?.any fun inst => standardChannel (errorChannel inst))

private def assertionGuard? (locals : LocalContext) (expr : Expr) : MetaM (Option (Expr × Bool)) := do
  let unwrap := fun context e =>
    let action := resolveLocalValue context e
    if action.isAppOf ``IO.ofExcept then resolveLocalValue context action.appArg! else action
  let isIf := fun (e : Expr) => e.isAppOf ``ite || e.isAppOf ``dite
  let expr := unwrap locals expr
  let guardOf (e : Expr) : Option (Expr × Bool) := do
    guard (isIf e)
    let #[_, condition, _, yes, no] := e.getAppArgs | none
    let branch := fun (b : Expr) => resolveLocalValue locals (if e.isAppOf ``dite then b.getLambdaBody else b)
    let yes := branch yes
    let no := branch no
    if standardUnit yes && standardFailure no then some (condition, true)
    else if standardFailure yes && standardUnit no then some (condition, false)
    else none
  if isIf expr then return guardOf expr
  let .const name levels := expr.getAppFn | return none
  let some (.defnInfo info) := (← getEnv).find? name | return none
  unless isIf (unwrap {} info.value.getLambdaBody) do return none
  if ← Meta.isRecursiveDefinition name then return none
  let body := info.value.instantiateLevelParams info.levelParams levels
  return guardOf (unwrap locals (mkAppN body expr.getAppArgs).headBeta)

private def checksBeforeContinuation (success failure : Expr) : Bool := Id.run do
  unless success.isApp && failure.isAppOf ``Bind.bind do return false
  let #[_, inst, _, _, action, tail] := failure.getAppArgs | return false
  unless inst.isAppOf ``Monad.toBind && (inst.appArg!.isAppOf ``instMonadEIO ||
    inst.appArg!.isAppOf ``Except.instMonad) && standardFailure action do return false
  let unit := success.appArg!
  return (unit.isConstOf ``Unit.unit || unit.isConstOf ``PUnit.unit) &&
    tail.etaExpanded? == some success.appFn!

private def skippedAssertion? (locals : LocalContext) (expr : Expr) : MetaM (Option String) := do
  let some matcher ← Meta.matchMatcherApp? expr | return none
  let #[discr] := matcher.discrs | return none
  let type ← Meta.whnf (← Meta.inferType discr)
  let (absent, present) ←
    if type.isAppOfArity ``Option 1 then pure (``Option.none, ``Option.some)
    else if type.isAppOfArity ``Except 2 then pure (``Except.error, ``Except.ok)
    else return none
  if (resolveLocalValue locals discr).isAppOf present then return none
  let branchMatches := fun ctor (test : Expr → MetaM Bool) => do
    let head := mkAppN (mkConst ctor type.getAppFn.constLevels!) type.getAppArgs
    Meta.forallTelescope (← Meta.inferType head) fun fields _ => do
      let .reduced body ← Meta.reduceMatcher? { matcher with discrs := #[mkAppN head fields] }.toExpr
        | return false
      test (resolveLocalValue locals body)
  unless ← branchMatches absent (fun body => pure <| standardUnit body ||
    (standardPureResult? body).any fun v => v.isAppOf ``ForInStep.yield &&
      (v.appArg!.isConstOf ``Unit.unit || v.appArg!.isConstOf ``PUnit.unit)) do return none
  let checks ← branchMatches present fun body => do
    if (← assertionGuard? locals body).isSome then return true
    unless body.isAppOf ``ite do return false
    let #[_, _, _, yes, no] := body.getAppArgs | return false
    return checksBeforeContinuation yes no || checksBeforeContinuation no yes
  return if checks then some s!"{absent} skips a check; review whether absence is acceptable" else none

private partial def comparesWholeJsonObject (locals : LocalContext) (condition : Expr) (positive : Bool) : Bool := Id.run do
  let condition := resolveLocalValue locals condition
  let isObject := fun operand =>
    let value := resolveLocalValue locals operand
    value.isAppOf ``Json.mkObj || value.isAppOf ``Json.obj
  match condition.getAppFn.constName?, condition.getAppArgs with
  | some ``Decidable.decide, #[prop, _] =>
    return comparesWholeJsonObject locals prop positive
  | some ``Not, #[inner] | some ``Bool.not, #[inner] =>
    return comparesWholeJsonObject locals inner (!positive)
  | some name, #[_, inst, lhs, rhs] =>
    return ((name == ``BEq.beq && positive) || (name == ``bne && !positive)) &&
      inst.isConstOf ``Json.instBEq && (isObject lhs || isObject rhs)
  | some name, #[type, lhs, rhs] =>
    unless name == ``Eq || name == ``Ne do return false
    let equality := positive == (name == ``Eq)
    if type.isConstOf ``Bool && (rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false) then
      return comparesWholeJsonObject locals lhs (equality == rhs.isConstOf ``Bool.true)
    return equality && type.isConstOf ``Json && (isObject lhs || isObject rhs)
  | _, _ => return false

private partial def retriesOnAnyError (action : Expr) : MetaM Bool := do
  let action := action.consumeMData
  if let .letE _ _ value body _ := action then
    return ← retriesOnAnyError (body.instantiate1 value)
  if action.isAppOf ``Bind.bind then
    let some tail := action.getAppArgs.back? | return false
    return ← Meta.lambdaTelescope tail fun _ body => retriesOnAnyError body
  if action.isAppOf ``ite then
    let #[_, _, _, yes, no] := action.getAppArgs | return false
    return (← retriesOnAnyError yes) || (← retriesOnAnyError no)
  let some matcher ← Meta.matchMatcherApp? action | return false
  let #[discr] := matcher.discrs | return false
  if discr.consumeMData.isAppOf ``Except.ok then return false
  let type ← Meta.whnf (← Meta.inferType discr)
  unless type.isAppOfArity ``Except 2 do return false
  let #[errorType, valueType] := type.getAppArgs | return false
  Meta.withLocalDeclD `reason errorType fun reason => do
    let error ← Meta.mkAppOptM ``Except.error #[some errorType, some valueType, some reason]
    let .reduced branch ← Meta.reduceMatcher? { matcher with discrs := #[error] }.toExpr | return false
    return branch.isAppOf ``Pure.pure && branch.getAppArgs.back?.any (·.isAppOf ``Option.none)

private def constantFallback (value : Expr) : Bool :=
  let number := if value.isAppOfArity ``Neg.neg 3 then value.appArg! else value
  let numeral := number.isAppOfArity ``OfNat.ofNat 3 && number.getAppArgs[1]!.isLit
  let decimal := match_expr number with
    | OfScientific.ofScientific _ _ digits sign power =>
      digits.isLit && (sign.isConstOf ``Bool.true || sign.isConstOf ``Bool.false) && power.isLit
    | _ => false
  value.isLit || [``Unit.unit, ``PUnit.unit, ``Bool.true, ``Bool.false].any value.isConstOf ||
    value.isAppOfArity ``Option.none 1 || ((numeral || decimal) && !value.hasFVar && !value.hasLooseBVars)

private def constantCatch? (locals : LocalContext) (expr : Expr) : Option (Expr × Bool) := do
  let mut expr := expr
  let mut sameContinuation := false
  if expr.isAppOf ``Bind.bind then
    let #[_, _, _, _, action, tail] := expr.getAppArgs | none
    let next := resolveLocalValue {} tail.getLambdaBody
    guard (!isFailure next)
    if next.isAppOf ``EarlyReturn.runK then
      let branches := next.getAppArgs
      sameContinuation := branches.back? == branches.pop.back?
    expr := action
  guard (expr.isAppOf ``MonadExcept.tryCatch || expr.isAppOf ``MonadExceptOf.tryCatch)
  let #[_, _, inst, _, _, handler] := expr.getAppArgs | none
  let .lam _ _ body _ := handler | none
  let body := body.consumeMData
  if standardUnit body || (sameContinuation && body.isAppOf ``EarlyReturnT.return &&
      body.getAppArgs.back?.any (·.isConstOf ``Unit.unit)) then return (expr, true)
  guard (standardChannel (errorChannel inst) && !body.hasLooseBVar 0)
  let body := resolveLocalValue locals body
  let value ← if sameContinuation && body.isAppOf ``EarlyReturnT.return then some body.appArg!
    else standardPureResult? body
  guard (constantFallback (resolveLocalValue locals value))
  return (expr, false)

private def catchesFinalThrow (caught : Expr) : Bool := Id.run do
  let #[_, _, catchInstance, _, action, _] := caught.getAppArgs | return false
  let mut tail := resolveLocalValue {} action
  unless tail.isAppOf ``Bind.bind do return false
  while tail.isAppOf ``Bind.bind do
    let some (.lam _ _ next _) := tail.getAppArgs.back?.map Expr.consumeMData | return false
    tail := resolveLocalValue {} next
  unless tail.isAppOf ``MonadExcept.throw || tail.isAppOf ``MonadExceptOf.throw || tail.isAppOf ``throwThe do return false
  let channel := errorChannel catchInstance
  return standardChannel channel && tail.getAppArgs[2]?.any (fun inst => errorChannel inst == channel)

private partial def knownTruth (locals : LocalContext) (expr : Expr) : MetaM (Option Bool) := do
  let expr := resolveLocalValue locals expr
  if expr.isConstOf ``True || expr.isConstOf ``Bool.true then return some true
  if expr.isConstOf ``False || expr.isConstOf ``Bool.false then return some false
  match expr.getAppFn.constName?, expr.getAppArgs with
  | some ``Bool.not, #[value] | some ``Not, #[value] => return (← knownTruth locals value).map (!·)
  | some name, #[type, inst, left, right] =>
    unless name == ``BEq.beq || name == ``bne do return none
    unless resolveLocalValue locals left == resolveLocalValue locals right do return none
    let law ← Meta.mkAppOptM ``LawfulBEq #[some type, some inst]
    return if (← Meta.synthInstance? law).isSome then some (name == ``BEq.beq) else none
  | some name, #[type, left, right] =>
    unless name == ``Eq || name == ``Ne do return none
    if resolveLocalValue locals left == resolveLocalValue locals right then return some (name == ``Eq)
    if name == ``Eq && type.isConstOf ``Bool && right.isConstOf ``Bool.true then return ← knownTruth locals left
    return none
  | _, _ => return none

def check (stx : Syntax) (expr : Expr) (fileMap : FileMap) (line : Nat) : MetaM (Option Finding) := do
  let kind := stx.getKind
  let locals ← getLCtx
  if [``Parser.Term.match, ``Parser.Term.doMatch, ``Parser.Term.doIf].contains kind then
    if let some detail ← skippedAssertion? locals expr then
      return some ⟨line, .skippedAssertion, detail⟩
  if kind == ``Parser.Term.app && expr.isAppOf `Spec.untilSome then
    if let some callback := expr.getAppArgs[2]? then
      if ← retriesOnAnyError callback then
        return some ⟨line, .unconditionalRetry, "Polling callback retries on any Except error"⟩
  if kind == ``Parser.Term.doTry then
    if let some (caught, unitHandler) := constantCatch? locals expr then
      let catchLine := ((stx[2][0].getPos?.map fileMap.toPosition).map (·.line)).getD line
      if unitHandler && catchesFinalThrow caught then
        return some ⟨catchLine, .caughtFailure, "Catch suppresses the final throw in its own try block"⟩
      return some ⟨catchLine, .emptyHandler, "Caught exception replaced by a constant result; review the fallback"⟩
  unless [``Parser.Term.app, ``termIfThenElse, ``termDepIfThenElse, ``Parser.Term.doIf].contains kind do return none
  if expr.isAppOf ``IO.ofExcept then return none
  let some (condition, success) ← assertionGuard? locals expr | return none
  if kind == ``Parser.Term.app then
    if let some truth ← knownTruth locals condition then
      if truth == success && expr.isAppOf `Spec.requireThat then
        return some ⟨line, .vacuousAssertion, "Spec.requireThat always succeeds"⟩
      return if truth == success then some ⟨line, .constantSuccess, "Check always succeeds"⟩
        else some ⟨line, .constantFailure, "Check always takes the failure branch"⟩
  if comparesWholeJsonObject locals condition success then
    return some ⟨line, .wholeJsonEquality, "Check requires whole JSON object equality; review whether exact shape is intended"⟩
  return none

end Lint4.AssertionsAndErrors
