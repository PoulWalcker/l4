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

end Lint4
