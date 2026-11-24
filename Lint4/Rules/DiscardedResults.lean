import Lint4.LeanExpressions
import Lint4.Finding

namespace Lint4.DiscardedResults

open Lean

private partial def usesProcessPipe (locals : LocalContext) (expr : Expr) : MetaM Bool := do
  let expr := resolveLocalValue locals expr
  let env ← getEnv
  let structure? := match expr with
    | .proj name _ _ => some name
    | _ => expr.getAppFn'.constName?.bind env.getProjectionStructureName?
  if structure? == some ``IO.Process.Child then
    return (← Meta.whnf (← Meta.inferType expr)).isConstOf ``IO.FS.Handle
  expr.getAppArgs.anyM (usesProcessPipe locals)

private def isIOAction (type : Expr) : MetaM Bool := do
  return (← Meta.whnfUntil type ``EIO).isSome || (← Meta.whnfUntil type ``BaseIO).isSome

private def lostResult? (type : Expr) : MetaM (Option String) := do
  if ← isIOAction type then
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
  unless ← isIOAction (mkApp monad type) do return none
  let action := resolveLocalValue locals action
  if action.isAppOf ``IO.Process.spawn || action.isAppOf ``IO.FS.readFile || action.isAppOf ``IO.FS.readBinFile then
    return some "Discarded file read or spawned process"
  let type ← Meta.whnf type
  unless type.isConstOf ``Unit || type.isConstOf ``PUnit do
    if ← usesProcessPipe locals action then return some "Discarded process pipe result"
  return none

def check (stx : Syntax) (expr : Expr) (line : Nat) : MetaM (Option (Finding × Option Syntax.Range)) := do
  let locals ← getLCtx
  let lost := fun detail span => some (⟨line, Rule.lostResult, detail⟩, span)
  let actionFinding := fun monad type action (rhs : Syntax) => do
    let some detail ← discardedAction? locals monad type action | return none
    let span := if (standardPureResult? action).isSome then rhs.getRange? else none
    return lost detail span
  match expr.getAppFn.constName?, expr.getAppArgs with
  | some ``Functor.discard, #[monad, type, _, action] =>
    unless stx.isOfKind ``Parser.Term.app do return none
    actionFinding monad type action stx
  | some ``Bind.bind, #[monad, _, type, _, action, continuation@(.lam _ _ body _)] =>
    unless stx.isOfKind ``Parser.Term.doLetArrow do return none
    if !body.hasLooseBVar 0 then return ← actionFinding monad type action stx[3][3]
    if ← ignoresProcessStatus action continuation then return lost "Process exit status is unobserved" none
    return none
  | _, _ =>
    unless [``Parser.Term.let, ``Parser.Term.doLet].contains stx.getKind do return none
    let .letE _ type value body _ := expr | return none
    if body.hasLooseBVar 0 then return none
    let some detail ← lostResult? type | return none
    let span := do
      let decl ← stx.getArgs.find? (·.isOfKind ``Parser.Term.letDecl)
      (← decl[0].getArgs.back?).getRange?
    if let some name := [`Spec.requireThat, `Spec.fieldsMatch].find? (value.consumeMData.isAppOfArity · 2) then
      return some (⟨line, .discardedVerdict, s!"Discarded {name} verdict"⟩, span)
    return lost detail span

end Lint4.DiscardedResults
