import Lint4.Rules.Declarations
import Lint4.Rules.Results
import Lint4.Policy

namespace Lint4.TermChecks

open Lean

private def forbiddenReference (env : Environment) (expr : Expr) : Option String := do
  let name ← match expr with
    | .proj structureName _ _ => some structureName
    | _ => expr.getAppFn'.constName?
  let index ← env.getModuleIdxFor? name
  let origin ← env.header.moduleNames[index]?
  guard (forbiddenInPure origin)
  return s!"Forbidden module dependency: {name} from {origin}"

private def partialOperations : List Name := [
  ``GetElem?.getElem!, ``panic, ``panicWithPos, ``panicWithPosWithDecl,
  ``List.head!, ``List.getLast!, ``Option.get!, ``Array.back!, ``Array.set!, ``Array.eraseIdx!,
  ``String.toNat!, ``String.toInt!, ``String.Slice.toNat!, ``String.Slice.toInt!, ``Json.setObjVal!,
  `ByteArray.get!, `ByteSlice.get!, `FloatArray.get!, `Subarray.get!, `String.Pos.get!,
  `Std.HashMap.get!, `Std.DHashMap.get!, `Std.HashSet.get!, `Std.TreeMap.get!, `Std.TreeSet.get!,
  `String.get!, `String.Pos.Raw.get!, `String.Slice.Pos.get!,
  `Lean.LocalContext.get!, `Lean.Parser.SyntaxStack.get!, `Lean.PersistentArray.get!,
  `Std.HashMap.Raw.get!, `Std.HashSet.Raw.get!, `Std.TreeMap.Raw.get!,
  `Std.TreeSet.Raw.get!, `Std.DHashMap.Const.get!, `Std.DHashMap.Raw.get!,
  `Std.DHashMap.Raw.Const.get!, `Std.DHashMap.Internal.AssocList.get!, `Std.DHashMap.Internal.Raw₀.get!,
  `Std.DHashMap.Internal.Raw₀.Const.get!, `Std.DTreeMap.get!, `Std.DTreeMap.Const.get!,
  `Std.DTreeMap.Raw.get!, `Std.DTreeMap.Raw.Const.get!, `Std.DTreeMap.Internal.Impl.get!,
  `Std.DTreeMap.Internal.Impl.Const.get!, `Std.ExtDHashMap.get!, `Std.ExtDHashMap.Const.get!,
  `Std.ExtDTreeMap.get!, `Std.ExtDTreeMap.Const.get!, `Std.ExtHashMap.get!,
  `Std.ExtHashSet.get!, `Std.ExtTreeMap.get!, `Std.ExtTreeSet.get!,
  `Std.Http.Headers.get!, `Std.Internal.IndexMultiMap.get!
]

private partial def timerName? (env : Environment) (name : Name) (seen : NameSet := {}) : Option Name := do
  if [``IO.sleep, `Std.Async.sleep, `Std.Async.Selector.sleep].contains name then return name
  guard (!seen.contains name)
  let .defnInfo info ← env.find? name | none
  let body := underlyingAction {} info.value.getLambdaBody
  let target ← body.getAppFn'.constName?
  timerName? env target (seen.insert name)

private def usesErrorFallback (locals : LocalContext) (action : Expr) : Bool := Id.run do
  if action.isAppOf ``Json.getObjValD && action.getAppArgs.size == 2 then return true
  unless action.isAppOf ``Option.getD do return false
  let #[_, option, _] := action.getAppArgs | return false
  let result := resolveLocalValue locals option
  return result.isAppOf ``Except.toOption &&
    result.getAppArgs.back?.any (fun value => !(resolveLocalValue locals value).isAppOf ``Except.ok)

private def applicationFinding? (locals : LocalContext) (action : Expr) (line : Nat) : Option Finding := do
  if usesErrorFallback locals action then
    return ⟨line, .errorFallback, "Error information replaced by a default"⟩
  if action.isAppOf ``dbgTrace && action.getAppArgs.size == 3 then
    return ⟨line, .debugTrace, "Debug trace"⟩
  guard (action.isAppOf ``String.contains || action.isAppOf ``String.Slice.contains)
  let #[_, _, _, _, receiver, _, _] := action.getAppArgs | none
  let text := resolveLocalValue locals receiver
  if text.isAppOf ``Json.compress || text.isAppOf ``Json.pretty then
    return ⟨line, .serializedJsonSearch, "Substring search over serialized JSON"⟩
  if text.isAppOf ``IO.Error.toString ||
      (text.isAppOf ``ToString.toString && text.getAppArgs[0]?.any (·.isConstOf ``IO.Error)) then
    return ⟨line, .formattedErrorSearch, "Substring search over a formatted IO error"⟩
  none

private def checkTerm (pureModule : Bool) (context : Elab.ContextInfo)
    (term : Elab.TermInfo) (line : Nat) : IO (Array Finding) := do
  let expr := (instantiateMVarsCore context.mctx term.expr).1.consumeMData
  let action := mkAppN (resolveLocalValue term.lctx expr.getAppFn') expr.getAppArgs
  let kind := term.stx.getKind
  let partialFinding := fun (name : Name) => Id.run do
    let detail := s!"Partial operation: {name}"
    if [``GetElem?.getElem!, ``panicWithPosWithDecl, ``panicWithPos].contains name then
      if let some r := term.stx.getRange? then
        if r.stop.byteIdx - r.start.byteIdx <= 80 then
          let source := r.start.extract context.fileMap.source r.stop
          if !source.isEmpty && source != name.toString && source.all (· >= ' ') then
            return ⟨line, .partialOperation, s!"{detail} at {reprStr source}"⟩
    return (⟨line, .partialOperation, detail⟩ : Finding)
  let mut findings := #[]
  if term.stx.isIdent || kind == `Lean.Parser.Term.identProj then
    if let some name := expr.getAppFn'.constName? then
      if let some timer := timerName? context.env name then
        findings := findings.push ⟨line, .manualTimer, s!"Manual timer: {timer}"⟩
      if partialOperations.contains name then
        findings := findings.push (partialFinding name)
      if (context.env.find? name).any (·.isUnsafe) then
        findings := findings.push ⟨line, .unsafeCode, "Unsafe operation"⟩
  if kind == ``Parser.Term.panic then
    findings := findings.push (partialFinding (expr.getAppFn'.constName?.getD ``panic))
  if kind == `«term__[_]_!» then
    findings := findings.push (partialFinding ``GetElem?.getElem!)
  if expr.isSorry || expr.isConstOf ``sorryAx then
    findings := findings.push ⟨line, .unfinishedProof, "Depends on sorryAx"⟩
  if kind == ``Parser.Term.unsafe then
    findings := findings.push ⟨line, .unsafeCode, "Unsafe operation"⟩
  if pureModule then
    if let some detail := forbiddenReference context.env expr then
      findings := findings.push ⟨line, .forbiddenDependency, detail⟩
  if kind == ``Parser.Term.app then
    if let some finding := applicationFinding? term.lctx action line then
      findings := findings.push finding
  if let some finding ← term.runMetaM context (ResultChecks.check term.stx expr context.fileMap line) then
    findings := findings.push finding
  return findings

def check (file : ElaboratedFile) (pureModule : Bool) : IO (Array Finding) := do
  let mut findings := #[]
  for tree in file.infoTrees do
    findings ← tree.foldInfoM (init := findings) fun context info acc => do
      let some pos := info.stx.getPos? | return acc
      let line := (file.input.fileMap.toPosition pos).line
      if [``Parser.Term.dbgTrace, ``Parser.Term.doDbgTrace, ``Parser.Tactic.dbgTrace].contains info.stx.getKind then
        return acc.push ⟨line, .debugTrace, "Debug trace"⟩
      let .ofTermInfo term := info | return acc
      if term.stx.isToken "example" then
        if let some decl := term.expr.constName?.bind context.env.find? then
          return acc ++ (← context.runCoreM (DeclarationChecks.checkOne decl line pureModule))
      if term.isBinder then return acc
      return acc ++ (← checkTerm pureModule context term line)
  return findings

end Lint4.TermChecks
