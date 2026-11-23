import Lint4.Expressions
import Lint4.Finding

namespace Lint4.ResultChecks

open Lean

private def returnsUnit (expr : Expr) : Bool :=
  (expr.isAppOf ``Pure.pure || expr.isAppOf ``Except.ok) &&
    expr.getAppArgs.back?.any fun value => value.isConstOf ``Unit.unit || value.isConstOf ``PUnit.unit

private def fails (expr : Expr) : Bool :=
  expr.isAppOf ``MonadExcept.throw || expr.isAppOf ``MonadExceptOf.throw || expr.isAppOf ``Except.error

private def emptyHandler (expr : Expr) : Bool := Id.run do
  let mut expr := expr
  let mut sameContinuation := false
  if expr.isAppOf ``Bind.bind then
    let #[_, _, _, _, action, tail] := expr.getAppArgs | return false
    let next := tail.getLambdaBody
    if fails next then return false
    if next.isAppOf ``EarlyReturn.runK then
      let branches := next.getAppArgs
      sameContinuation := branches.back? == branches.pop.back?
    expr := action
  unless expr.isAppOf ``MonadExcept.tryCatch || expr.isAppOf ``MonadExceptOf.tryCatch do return false
  let some (.lam _ _ body _) := expr.getAppArgs.back? | return false
  let body := body.consumeMData
  return returnsUnit body || (sameContinuation && body.isAppOf ``EarlyReturnT.return &&
    body.getAppArgs.back?.any (·.isConstOf ``Unit.unit))

private def guardBranches? (expr : Expr) : Option (Expr × Bool) := do
  guard (expr.isAppOf ``ite)
  let #[_, condition, _, yes, no] := expr.getAppArgs | none
  if returnsUnit yes && fails no then some (condition, true)
  else if fails yes && returnsUnit no then some (condition, false)
  else none

private def checkedGuard? (env : Environment) (expr : Expr) : Option (Expr × Bool) := do
  if let some gate := guardBranches? expr then return gate
  let .const name levels := expr.getAppFn | none
  let some (.defnInfo info) := env.find? name | none
  guard ((guardBranches? info.value.getLambdaBody).isSome)
  let body := info.value.instantiateLevelParams info.levelParams levels
  guardBranches? (mkAppN body expr.getAppArgs).headBeta

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

private partial def usesProcessPipe (locals : LocalContext) (expr : Expr) : MetaM Bool := do
  let expr := resolveLocalValue locals expr
  let env ← getEnv
  let structure? := match expr with
    | .proj name _ _ => some name
    | _ => expr.getAppFn'.constName?.bind env.getProjectionStructureName?
  if structure? == some ``IO.Process.Child then
    return (← Meta.whnf (← Meta.inferType expr)).isConstOf ``IO.FS.Handle
  expr.getAppArgs.anyM (usesProcessPipe locals)

private def lostResult? (type : Expr) : MetaM (Option String) := do
  let type ← Meta.whnf type
  if type.isAppOf ``Except then return some "Discarded Except result"
  if type.isConstOf ``IO.Process.Output then return some "Discarded process output and exit status"
  return none

private def ignoresProcessStatus (action continuation : Expr) : MetaM Bool := do
  unless action.isAppOf ``IO.Process.output do return false
  Meta.lambdaTelescope continuation fun args body => do
    let some output := args[0]? | return false
    let body ← Meta.zetaReduce body (zetaDelta := false)
    let fields := getStructureFields (← getEnv) ``IO.Process.Output
    let withoutText := body.replace fun part =>
      let isText := match part with
        | .proj struct index value =>
          struct == ``IO.Process.Output && value == output && fields[index]?.any ([`stdout, `stderr].contains ·)
        | _ => part.getAppArgs.back? == some output &&
          (part.isAppOf ``IO.Process.Output.stdout || part.isAppOf ``IO.Process.Output.stderr)
      if isText then some (mkStrLit "") else none
    return !withoutText.containsFVar output.fvarId!

private def discardedAction? (locals : LocalContext) (monad type action : Expr) : MetaM (Option String) := do
  if let some detail ← lostResult? type then return some detail
  unless monad.isConstOf ``IO || monad.isAppOf ``EIO do return none
  let action := resolveLocalValue locals action
  if action.isAppOf ``IO.Process.spawn || action.isAppOf ``IO.FS.readFile || action.isAppOf ``IO.FS.readBinFile then
    return some "Discarded file read or spawned process"
  let type ← Meta.whnf type
  unless type.isConstOf ``Unit || type.isConstOf ``PUnit do
    if ← usesProcessPipe locals action then return some "Discarded process pipe result"
  return none

private def discardedResult? (locals : LocalContext) (kind : SyntaxNodeKind) (expr : Expr) : MetaM (Option String) := do
  match expr.getAppFn.constName?, expr.getAppArgs with
  | some ``Functor.discard, #[monad, type, _, action] =>
    if kind == ``Parser.Term.app then discardedAction? locals monad type action else return none
  | some ``Bind.bind, #[monad, _, type, _, action, continuation@(.lam _ _ body _)] =>
    unless kind == ``Parser.Term.doLetArrow do return none
    if !body.hasLooseBVar 0 then return ← discardedAction? locals monad type action
    if ← ignoresProcessStatus action continuation then
      return some "Process exit status is unobserved"
    return none
  | _, _ =>
    unless [``Parser.Term.let, ``Parser.Term.doLet].contains kind do return none
    let .letE _ type _ body _ := expr | return none
    if !body.hasLooseBVar 0 then lostResult? type else return none

def check (context : Elab.ContextInfo) (term : Elab.TermInfo) (line : Nat) : IO (Array Finding) := do
  let kind := term.stx.getKind
  let expr := (instantiateMVarsCore context.mctx term.expr).1.consumeMData
  if kind == ``Parser.Term.doTry && emptyHandler expr then
    let catchLine := (term.stx[2][0].getPos?.map context.fileMap.toPosition).map (·.line)
    return #[⟨catchLine.getD line, .warning, "W04", "Exception handler immediately returns success"⟩]
  if let some detail ← term.runMetaM context (discardedResult? term.lctx kind expr) then
    return #[⟨line, .warning, "W16", detail⟩]
  unless kind == ``Parser.Term.app do return #[]
  let some (condition, success) := checkedGuard? context.env expr | return #[]
  let some truth ← term.runMetaM context (knownTruth term.lctx condition) | return #[]
  return if truth == success then #[⟨line, .warning, "W17", "Check always succeeds"⟩]
    else #[⟨line, .warning, "W19", "Check always takes the failure branch"⟩]

end Lint4.ResultChecks
