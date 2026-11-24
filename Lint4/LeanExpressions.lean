import Lean

namespace Lint4

open Lean

partial def resolveLocalValue (locals : LocalContext) (expr : Expr) : Expr :=
  let expr := expr.consumeMData
  match expr with
  | .fvar id =>
    match (locals.find? id).bind (·.value? (allowNondep := true)) with
    | some value => resolveLocalValue locals value
    | none => expr
  | .letE _ _ value body _ => resolveLocalValue locals (body.instantiate1 value)
  | _ => expr

partial def underlyingAction (locals : LocalContext) (expr : Expr) : Expr :=
  let expr := resolveLocalValue locals expr
  match expr.getAppFn'.constName? with
  | some ``liftM | some ``MonadLift.monadLift | some ``MonadLiftT.monadLift =>
    match expr.getAppArgs.back? with
    | some action => underlyingAction locals action
    | none => expr
  | _ => expr

partial def standardMonad (inst : Expr) : Bool :=
  if inst.isAppOfArity ``ExceptT.instMonad 3 then standardMonad inst.appArg!
  else inst.isAppOf ``Except.instMonad || inst.isAppOf ``instMonadEIO || inst.isConstOf ``Id.instMonad

def standardPureResult? (expr : Expr) : Option Expr := do
  if expr.isAppOfArity ``Except.ok 3 then return expr.appArg!
  guard (expr.isAppOfArity ``Pure.pure 4)
  let inst := expr.getAppArgs[1]!
  guard (inst.isAppOf ``Applicative.toPure && inst.appArg!.isAppOf ``Monad.toApplicative)
  guard (standardMonad inst.appArg!.appArg!)
  return expr.appArg!

def isFailure (expr : Expr) : Bool :=
  expr.isAppOf ``MonadExcept.throw || expr.isAppOf ``MonadExceptOf.throw || expr.isAppOf ``Except.error

end Lint4
