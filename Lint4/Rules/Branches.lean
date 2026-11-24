import Lint4.LeanExpressions
import Lint4.Finding

namespace Lint4.Branches

open Lean

private partial def branchLiteral? (env : Environment) : Meta.Match.Pattern → Option Expr
  | .val value => some value
  | .ctor ctor _ _ [] =>
    if ctor == ``Bool.true || ctor == ``Bool.false then some (mkConst ctor) else none
  | .ctor ctor _ _ [field] => do
    let some (.ctorInfo c) := env.find? ctor | none
    let some (.inductInfo i) := env.find? c.induct | none
    guard (!isPrivateName ctor && i.numCtors == 1 && i.numIndices == 0)
    branchLiteral? env field
  | .as _ pattern _ => branchLiteral? env pattern
  | _ => none

private def scalarBranch? (kind : SyntaxNodeKind) (expr : Expr) : MetaM (Option String) := do
  let env ← getEnv
  let flag ← if kind == ``Parser.Term.match || kind == ``Parser.Term.doMatch then do
    let some matcher ← Meta.matchMatcherApp? expr | return none
    let #[value] := matcher.discrs | return none
    let literals ← Meta.Match.withMkMatcherInput matcher.matcherName true fun input => do
      return (input.lhss.filterMap fun alt => alt.patterns.head?.bind (branchLiteral? env)).eraseDups
    let first :: _ := literals | return none
    let raw ← Meta.whnf (← Meta.inferType first)
    let type ← Meta.inferType value
    if !(← Meta.whnf type).isConstOf ``Bool then
      unless literals.length >= 2 && [``String, ``Char, ``Int, ``Nat, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``Bool].any raw.isConstOf do return none
      return some s!"Match on {← Meta.ppExpr type} distinguishes {literals.length} literal values of {← Meta.ppExpr raw}"
    unless matcher.alts.size >= 2 do return none
    pure value
  else do
    unless expr.isAppOf ``ite || expr.isAppOf ``dite do return none
    let #[_, cond, _, yesBranch, noBranch] := expr.getAppArgs | return none
    let startsWithFailure := fun (branch : Expr) =>
      let body := branch.getLambdaBody.consumeMData
      let first := if body.isAppOf ``Bind.bind then body.getAppArgs[4]?.getD body else body
      isFailure first || first.isAppOf ``throwThe
    if startsWithFailure yesBranch || startsWithFailure noBranch then return none
    let_expr Eq _ value yes := cond | return none
    unless yes.isConstOf ``Bool.true do return none
    pure value
  let locals ← getLCtx
  let value := resolveLocalValue locals flag
  let isFlag : Bool := match value with
    | .fvar id => (locals.find? id).any fun d => !d.userName.hasMacroScopes && !d.isImplementationDetail
    | .proj struct .. => !isClass env struct
    | _ => (value.getAppFn.constName?.bind env.getProjectionFnInfo?).any fun p =>
      !p.fromClass && value.getAppNumArgs == p.numParams + 1
  unless isFlag do return none
  return some s!"Boolean flag selects a branch: {← Meta.ppExpr flag}"

def check (kind : SyntaxNodeKind) (expr : Expr) (line : Nat) : MetaM (Option Finding) := do
  unless [``Parser.Term.match, ``Parser.Term.doMatch, ``termIfThenElse, ``termDepIfThenElse, ``Parser.Term.doIf].contains kind do return none
  return (← scalarBranch? kind expr).map fun detail => ⟨line, .scalarBranch, detail⟩

end Lint4.Branches
