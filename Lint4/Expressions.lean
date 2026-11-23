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

def unfoldLocalDefinition? (env : Environment) (seen : NameSet) (expr : Expr) : Option (Name × Expr) := do
  let .const name levels := expr.getAppFn' | none
  guard (!seen.contains name && (env.getModuleIdxFor? name).isNone)
  let .defnInfo info ← env.find? name | none
  guard (expr.getAppArgs.size >= info.value.getNumHeadLambdas)
  let body := info.value.instantiateLevelParams info.levelParams levels
  return (name, (mkAppN body expr.getAppArgs).headBeta)

end Lint4
