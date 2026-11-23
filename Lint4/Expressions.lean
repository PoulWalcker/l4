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

end Lint4
