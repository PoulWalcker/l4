import Lint4.Expressions
import Lint4.Finding

namespace Lint4.BodyChecks

open Lean

private structure FileFlow where
  derived : Bool := false
  validated : Bool := false
  deriving Inhabited

private inductive ExitCheck where
  | mustFail | mayReturnUnit
  deriving BEq

private def catchMonad (expr : Expr) : Bool :=
  expr.isConstOf ``IO || expr.isAppOf ``EIO || expr.isAppOf ``Except

private partial def catchTail (env : Environment) (expr : Expr) (check : ExitCheck)
    (seen : NameSet := {}) : Bool :=
  let expr := expr.consumeMData
  match expr with
  | .letE _ _ value body _ => catchTail env (body.instantiate1 value) check seen
  | .lam _ _ body _ => catchTail env body check seen
  | _ =>
    let alternatives := fun branches =>
      if check == .mustFail then branches.all (fun alt => catchTail env alt check seen)
      else branches.any (fun alt => catchTail env alt check seen)
    match expr.getAppFn'.constName?, expr.getAppArgs with
    | some ``Bind.bind, #[monad, _, _, _, action, tail] =>
      catchMonad monad &&
        (if catchTail env action .mustFail seen then check == .mustFail else catchTail env tail check seen)
    | some ``EarlyReturnT.return, #[type, monad, _, _, _]
    | some ``Pure.pure, #[monad, _, type, _] =>
      check == .mayReturnUnit && catchMonad monad &&
        (type.isConstOf ``Unit || type.isConstOf ``PUnit)
    | some ``MonadExcept.throw, #[_, monad, _, _, _]
    | some ``MonadExceptOf.throw, #[_, monad, _, _, _] =>
      check == .mustFail && catchMonad monad
    | some ``Except.error, _ => check == .mustFail
    | some ``ite, #[_, _, _, first, second]
    | some ``dite, #[_, _, _, first, second] => alternatives #[first, second]
    | some name, args =>
      if let some info := Meta.getMatcherInfoCore? env name then
        info.numAlts > 0 && args.size >= info.arity &&
          alternatives (args.extract info.getFirstAltPos info.arity)
      else if let some (name, body) := unfoldLocalDefinition? env seen expr then
        catchTail env body check (seen.insert name)
      else false
    | _, _ => false

private partial def fileFlow (env : Environment) (bindings : List Bool) (expr : Expr)
    (seen : NameSet := {}) : FileFlow := Id.run do
  let expr := expr.consumeMData.headBeta.consumeMData
  if expr.isAppOf ``IO.FS.readFile || expr.isAppOf ``IO.FS.readBinFile ||
      expr.isConstOf ``IO.FS.readFile || expr.isConstOf ``IO.FS.readBinFile then
    return { derived := true }
  match expr.getAppFn'.constName?, expr.getAppArgs with
  | some ``Bind.bind, #[monad, _, _, _, action, .lam _ _ body _] =>
    let actionFlow := fileFlow env bindings action seen
    let bodyFlow := fileFlow env (actionFlow.derived :: bindings) body seen
    let derived := bodyFlow.derived || (monad.isAppOf ``Except && actionFlow.derived)
    return { derived, validated := actionFlow.validated || bodyFlow.validated }
  | some ``IO.ofExcept, args =>
    let some value := args.back? | return {}
    let input := fileFlow env bindings value seen
    return { input with validated := input.validated || (input.derived && !value.isAppOf ``Except.ok) }
  | some ``ite, #[_, condition, _, first, second]
  | some ``dite, #[_, condition, _, first, second] =>
    let c := fileFlow env bindings condition seen
    let a := fileFlow env bindings first seen
    let b := fileFlow env bindings second seen
    let validation := c.validated || a.validated || b.validated ||
      (c.derived && (catchTail env first .mustFail != catchTail env second .mustFail))
    return { derived := c.derived || a.derived || b.derived, validated := validation }
  | _, _ =>
    if let some (name, body) := unfoldLocalDefinition? env seen expr then
      return fileFlow env bindings body (seen.insert name)
    match expr with
    | .bvar index => return { derived := bindings[index]?.getD false }
    | .letE _ _ value body _ =>
      if !body.hasLooseBVar 0 then return fileFlow env (false :: bindings) body seen
      let before := fileFlow env bindings value seen
      let after := fileFlow env (before.derived :: bindings) body seen
      return { after with validated := before.validated || after.validated }
    | .lam _ _ body _ => return fileFlow env (false :: bindings) body seen
    | .proj _ _ value => return fileFlow env bindings value seen
    | .app .. =>
      let pieces := expr.getAppArgs.push expr.getAppFn'
      let flows := pieces.map fun piece => fileFlow env bindings piece seen
      return { derived := flows.any (·.derived), validated := flows.any (·.validated) }
    | _ => return {}

private partial def swallowedException (env : Environment) (expr : Expr) : Bool :=
  let expr := expr.consumeMData
  match expr with
  | .letE _ _ value body _ => swallowedException env (body.instantiate1 value)
  | .lam _ _ body _ => swallowedException env body
  | _ =>
    match expr.getAppFn'.constName?, expr.getAppArgs with
    | some ``Bind.bind, #[monad, _, _, _, action, tail] =>
      (!catchMonad monad || !catchTail env tail .mustFail) && swallowedException env action ||
        swallowedException env tail
    | some name, #[_, monad, _, _, action, handler] =>
      if catchMonad monad && (name == ``MonadExcept.tryCatch || name == ``MonadExceptOf.tryCatch) then
        catchTail env handler .mayReturnUnit || swallowedException env action || swallowedException env handler
      else expr.getAppArgs.any (swallowedException env)
    | _, _ => expr.getAppArgs.any (swallowedException env)

def check (env : Environment) (value : Expr) (line : Nat) : Array Finding := Id.run do
  let mut findings := #[]
  if (fileFlow env [] value).validated then
    findings := findings.push ⟨line, .warning, "I03", "File-derived validation; review storage boundary"⟩
  if swallowedException env value then
    findings := findings.push ⟨line, .warning, "W04",
      "Exception handler can return success; review failure propagation"⟩
  return findings

end Lint4.BodyChecks
