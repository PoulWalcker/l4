import Lint4.Expressions
import Lint4.Finding

namespace Lint4.ResultChecks

open Lean

private def returnsUnit (expr : Expr) : Bool :=
  (expr.isAppOf ``Pure.pure || expr.isAppOf ``Except.ok) &&
    expr.getAppArgs.back?.any fun value => value.isConstOf ``Unit.unit || value.isConstOf ``PUnit.unit

private def fails (expr : Expr) : Bool :=
  expr.isAppOf ``MonadExcept.throw || expr.isAppOf ``MonadExceptOf.throw || expr.isAppOf ``Except.error

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

private def emptyCatch? (expr : Expr) : Option Expr := do
  let mut expr := expr
  let mut sameContinuation := false
  if expr.isAppOf ``Bind.bind then
    let #[_, _, _, _, action, tail] := expr.getAppArgs | none
    let next := resolveLocalValue {} tail.getLambdaBody
    guard (!fails next)
    if next.isAppOf ``EarlyReturn.runK then
      let branches := next.getAppArgs
      sameContinuation := branches.back? == branches.pop.back?
    expr := action
  guard (expr.isAppOf ``MonadExcept.tryCatch || expr.isAppOf ``MonadExceptOf.tryCatch)
  let .lam _ _ body _ ← expr.getAppArgs.back? | none
  let body := body.consumeMData
  guard (returnsUnit body || (sameContinuation && body.isAppOf ``EarlyReturnT.return &&
    body.getAppArgs.back?.any (·.isConstOf ``Unit.unit)))
  return expr

private def catchesFinalThrow (caught : Expr) : Bool := Id.run do
  let #[_, _, catchInstance, _, action, _] := caught.getAppArgs | return false
  let mut tail := resolveLocalValue {} action
  unless tail.isAppOf ``Bind.bind do return false
  while tail.isAppOf ``Bind.bind do
    let some (.lam _ _ next _) := tail.getAppArgs.back?.map Expr.consumeMData | return false
    tail := resolveLocalValue {} next
  unless tail.isAppOf ``MonadExcept.throw || tail.isAppOf ``MonadExceptOf.throw || tail.isAppOf ``throwThe do return false
  let instanceOf := fun (inst : Expr) =>
    if inst.isAppOf ``instMonadExceptOfMonadExceptOf then inst.getAppArgs.back?.getD inst else inst
  let channel := instanceOf catchInstance
  return (channel.isAppOf ``instMonadExceptOfEIO || channel.isAppOf ``instMonadExceptOfExcept) &&
    tail.getAppArgs[2]?.any (fun inst => instanceOf inst == channel)

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
  if (← Meta.whnfUntil type ``EIO).isSome || (← Meta.whnfUntil type ``BaseIO).isSome then
    return some "Discarded IO action without executing it"
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

def check (context : Elab.ContextInfo) (term : Elab.TermInfo) (kind : SyntaxNodeKind)
    (expr : Expr) (line : Nat) : IO (Array Finding) := do
  if kind == ``Parser.Term.app && expr.isAppOf `Spec.untilSome then
    if let some callback := expr.getAppArgs[2]? then
      if ← term.runMetaM context (retriesOnAnyError callback) then
        return #[⟨line, .warning, "W20", "Polling callback retries on any Except error"⟩]
  if kind == ``Parser.Term.doTry then
    if let some caught := emptyCatch? expr then
      let catchLine := ((term.stx[2][0].getPos?.map context.fileMap.toPosition).map (·.line)).getD line
      if catchesFinalThrow caught then
        return #[⟨catchLine, .noGo, "N09", "Catch suppresses the final throw in its own try block"⟩]
      return #[⟨catchLine, .warning, "W04", "Exception handler immediately returns success"⟩]
  if let some detail ← term.runMetaM context (discardedResult? term.lctx kind expr) then
    if let .letE _ _ value _ _ := expr then
      let assertions := [`Spec.requireThat, `Spec.fieldsMatch]
      if let some name := assertions.find? (fun name => value.consumeMData.isAppOfArity name 2) then
        return #[⟨line, .noGo, "N07", s!"Discarded {name} verdict"⟩]
    return #[⟨line, .warning, "W16", detail⟩]
  unless kind == ``Parser.Term.app do return #[]
  let some (condition, success) := checkedGuard? context.env expr | return #[]
  let some truth ← term.runMetaM context (knownTruth term.lctx condition) | return #[]
  if truth == success && expr.isAppOf `Spec.requireThat then
    return #[⟨line, .noGo, "N08", "Spec.requireThat always succeeds"⟩]
  return if truth == success then #[⟨line, .warning, "W17", "Check always succeeds"⟩]
    else #[⟨line, .warning, "W19", "Check always takes the failure branch"⟩]

end Lint4.ResultChecks
