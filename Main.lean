import Lean
import Lake.Config.InstallPath

open Lean

structure Finding where
  position : Position
  severity : String
  rule : String

private def containsPosition (range : Syntax.Range) (pos : String.Pos.Raw) : Bool :=
  range.start <= pos && pos < range.stop

private partial def loopRanges (stx : Syntax) : List Syntax.Range :=
  let range := match stx.getKind with
    | ``Parser.Term.doWhile | ``Parser.Term.doRepeat | ``Parser.Term.doRepeatUntil =>
      stx.getRange?.toList
    | _ => []
  range ++ stx.getArgs.toList.flatMap loopRanges

private def triviaComments (map : FileMap) (trivia : Substring.Raw) : List Finding := Id.run do
  let mut line := (map.toPosition trivia.startPos).line
  let mut results : List Finding := []
  for text in trivia.toString.splitOn "\n" do
    if text.contains "--" || text.contains "/-" then
      results := ⟨⟨line, 0⟩, "Could Be Better", "code-comments"⟩ :: results
    line := line + 1
  return results

private def commentsAt (map : FileMap) (stx : Syntax) : List Finding :=
  let trivia := match stx with
    | .atom (.original leading _ trailing _) _ | .ident (.original leading _ trailing _) _ _ _ =>
      triviaComments map leading ++ triviaComments map trailing
    | _ => []
  if stx.getKind == ``Parser.Command.docComment || stx.getKind == ``Parser.Command.moduleDoc then
    ⟨⟨(map.toPosition (stx.getPos?.getD 0)).line, 0⟩, "Could Be Better", "code-comments"⟩ :: trivia
  else trivia

private partial def localValue (locals : LocalContext) (expr : Expr) : Expr :=
  let expr := expr.consumeMData
  match expr with
  | .fvar id =>
    match (locals.find? id).bind (·.value?) with
    | some value => localValue locals value
    | none => expr
  | .letE _ _ value body _ => localValue locals (body.instantiate1 value)
  | _ => expr

private def searchedValue? (locals : LocalContext) (expr : Expr) : Option FVarId := do
  guard (expr.isAppOf ``String.contains)
  let #[_, _, _, _, receiver, _, _] := expr.getAppArgs | none
  let text := localValue locals receiver
  let conversion ← text.getAppFn'.constName?
  guard (conversion == ``IO.Error.toString || conversion == ``ToString.toString)
  let value ← text.getAppArgs.back?
  let .fvar id := (localValue locals value) | none
  return id

private structure AuditEvidence where
  findings : List Finding := []
  unitReturns : Std.HashSet Nat := {}
  binders : Std.HashSet (Nat × FVarId) := {}
  searchedValues : List (FVarId × String.Pos.Raw) := []

private def isUnitReturn (expr : Expr) : Bool :=
  if expr.isAppOf ``Pure.pure || expr.isAppOf ``EarlyReturnT.return then
    match expr.getAppArgs.back? with
    | some value =>
      let value := value.consumeMData
      value.isConstOf ``Unit.unit || value.isConstOf ``PUnit.unit
    | none => false
  else false

private def catchRules (evidence : AuditEvidence) (stx : Syntax) : List String :=
  if stx.getKind != ``Parser.Term.doCatch then []
  else
    let swallowed : Bool := match Parser.Term.getDoElems ⟨stx[4]⟩ with
      | #[body] => body.raw.getPos?.any fun pos => evidence.unitReturns.contains pos.byteIdx
      | _ => false
    let searched : Bool := match stx[1].getPos?, stx.getRange? with
      | some binder, some handler => evidence.searchedValues.any fun (id, pos) =>
        containsPosition handler pos && evidence.binders.contains (binder.byteIdx, id)
      | _, _ => false
    match swallowed, searched with
    | true, true => ["swallowed-error", "exception-string-matching"]
    | true, false => ["swallowed-error"]
    | false, true => ["exception-string-matching"]
    | false, false => []

private partial def auditSyntax (map : FileMap) (evidence : AuditEvidence) (stx : Syntax)
    : List Finding :=
  let simple : List (String × String) :=
    match stx with
    | .atom _ "sorry" => [("No-Go", "sorry")]
    | .atom _ "admit" => [("No-Go", "admit")]
    | .atom _ "unsafe" => [("Warning", "unsafe")]
    | .atom _ "partial" => [("Warning", "partial")]
    | .atom _ "axiom" => [("Warning", "axiom")]
    | .atom _ "dbg_trace" => [("Warning", "dbg_trace")]
    | .atom _ "panic!" => [("Warning", "unchecked-panic")]
    | _ => []
  let rules := simple ++ (catchRules evidence stx).map (fun rule => ("Warning", rule))
  let position := map.toPosition (stx.getPos?.getD 0)
  rules.map (fun (severity, rule) => ⟨position, severity, rule⟩) ++ commentsAt map stx ++
    stx.getArgs.toList.flatMap (auditSyntax map evidence)

private def selfComparison (context : Elab.ContextInfo) (term : Elab.TermInfo) (expr : Expr)
    : IO Bool := do
  let some name := expr.getAppFn'.constName? | return false
  unless name == ``BEq.beq || name == ``bne do return false
  let sourceCall := match term.stx with
    | `(term| $_ == $_) | `(term| $_ != $_) => true
    | _ => term.stx.getKind == ``Parser.Term.app
  unless sourceCall do return false
  let #[type, beq, left, right] := (instantiateMVarsCore context.mctx expr).1.getAppArgs
    | return false
  unless left.consumeMData == right.consumeMData && !type.hasMVar && !beq.hasMVar do
    return false
  term.runMetaM context do
    let reflexive ← Meta.mkAppOptM ``ReflBEq #[some type, some beq]
    return (← Meta.synthInstance? reflexive).isSome

private def fallbackRule (locals : LocalContext) (expr : Expr) (name : Name) : Option String := do
  if name == ``Option.some then
    let #[_, value] := expr.getAppArgs | none
    guard ((localValue locals value).isAppOf ``Json.getObjValD)
    return "defaulted-json-success"
  if name == ``Option.getD then
    let #[_, value, _] := expr.getAppArgs | none
    guard ((localValue locals value).isAppOf ``Except.toOption)
    return "silent-error-fallback"
  none

private def apiRule (name : Name) : Option String :=
  match name with
  | ``unsafeCast => some "unsafe-cast"
  | ``Json.getObjValD => some "silent-json-default"
  | ``Json.setObjVal! | ``GetElem?.getElem! | ``List.head! | ``List.getLast! | ``Option.get!
  | ``Subarray.get! | ``ByteArray.get! | ``FloatArray.get!
  | `String.get! | `String.Pos.get! | `String.Pos.Raw.get! | `String.Slice.Pos.get!
  | `Lean.PersistentArray.get! | `Lean.LocalContext.get! | `Lean.Parser.SyntaxStack.get!
  | `Std.ByteSlice.get! | `Std.HashMap.get! | `Std.HashMap.Raw.get! | `Std.HashSet.get! | `Std.HashSet.Raw.get!
  | `Std.DHashMap.get! | `Std.DHashMap.Raw.get! | `Std.DHashMap.Const.get! | `Std.DHashMap.Raw.Const.get!
  | `Std.TreeMap.get! | `Std.TreeMap.Raw.get! | `Std.TreeSet.get! | `Std.TreeSet.Raw.get!
  | `Std.DTreeMap.get! | `Std.DTreeMap.Raw.get! | `Std.DTreeMap.Const.get! | `Std.DTreeMap.Raw.Const.get!
  | `Std.ExtHashMap.get! | `Std.ExtHashSet.get! | `Std.ExtDHashMap.get! | `Std.ExtDHashMap.Const.get!
  | `Std.ExtTreeMap.get! | `Std.ExtTreeSet.get! | `Std.ExtDTreeMap.get! | `Std.ExtDTreeMap.Const.get!
  | `Std.Http.Headers.get! | `Std.Http.Internal.IndexMultiMap.get! => some "unsafe-access"
  | _ => none

private def resolvedRule (term : Elab.TermInfo) (expr : Expr) (loops : List Syntax.Range)
    (pos : String.Pos.Raw) : Option String := do
  guard (!term.isBinder)
  let name ← expr.getAppFn'.constName?
  if term.stx.getKind == ``Parser.Term.app then
    if name == ``IO.sleep then
      return if loops.any (containsPosition · pos) then "polling-with-sleep" else "fixed-sleep"
    if let some rule := fallbackRule term.lctx expr name then return rule
  guard (term.stx.getKind == `Lean.Parser.Term.identProj || (term.stx.isIdent && expr.isConst))
  apiRule name

private def hasTypedError (type : Expr) : Bool :=
  type.isAppOf ``Except || type.isAppOf ``ExceptT

private def successfulValue (expr : Expr) : MetaM Bool := do
  let type := match expr.getAppFn'.constName?, expr.getAppArgs with
    | some ``Pure.pure, #[monad, _, type, _] => if hasTypedError monad then some type else none
    | some ``Except.ok, #[_, type, _] => some type
    | _, _ => none
  let some type := type | return false
  let some head := (← Meta.whnf type).getAppFn'.constName? | return false
  return head != ``Option && head != ``Except && head != ``Bool &&
    head != ``Unit && head != ``PUnit

private def skipsCheckedWork (matcher : Meta.MatcherApp) (locals : LocalContext)
    (failed accepted : Expr) : MetaM Bool := do
  let .reduced failure ← Meta.reduceMatcher? ({ matcher with discrs := #[failed] }.toExpr)
    | return false
  unless ← successfulValue (localValue locals failure) do return false
  let .reduced success ← Meta.reduceMatcher? ({ matcher with discrs := #[accepted] }.toExpr)
    | return false
  let success := localValue locals success
  let action := match success.getAppFn'.constName?, success.getAppArgs with
    | some ``Bind.bind, #[_, _, _, _, action, _] => localValue locals action
    | _, _ => success
  let fn := action.getAppFn'.constName?
  return action.isApp && fn != some ``Pure.pure && fn != some ``Except.ok && fn != some ``Except.error &&
    fn != some ``MonadExcept.throw && hasTypedError (← Meta.inferType action)

private def successOnFailedPattern (context : Elab.ContextInfo) (term : Elab.TermInfo)
    : IO Bool := do
  let kind := term.stx.getKind
  unless kind == ``Parser.Term.doLetElse || kind == ``Parser.Term.doMatch do return false
  term.runMetaM context do
    let expr := (← instantiateMVars term.expr).consumeMData
    let some matcher ← Meta.matchMatcherApp? expr | return false
    let #[subject] := matcher.discrs | return false
    unless matcher.remaining.isEmpty && hasTypedError (← Meta.inferType expr) do return false
    let computed := localValue term.lctx subject
    unless computed.isApp do return false
    if let some name := computed.getAppFn'.constName? then
      if (← getEnv).isConstructor name then return false
    let type ← Meta.whnf (← Meta.inferType subject)
    let .const name levels := type.getAppFn | return false
    match name, type.getAppArgs with
    | ``Option, #[payload] =>
      Meta.withLocalDeclD `payload payload fun item =>
        skipsCheckedWork matcher term.lctx (mkApp (mkConst ``Option.none levels) payload)
          (mkApp2 (mkConst ``Option.some levels) payload item)
    | ``Except, #[error, payload] =>
      Meta.withLocalDeclD `error error fun problem =>
        Meta.withLocalDeclD `payload payload fun item =>
          skipsCheckedWork matcher term.lctx (mkApp3 (mkConst ``Except.error levels) error payload problem)
            (mkApp3 (mkConst ``Except.ok levels) error payload item)
    | _, _ => return false

private partial def usesProcessPipe (locals : LocalContext) (expr : Expr) : MetaM Bool := do
  let expr := localValue locals expr
  let env ← getEnv
  let structure? := match expr with
    | .proj name _ _ => some name
    | _ => expr.getAppFn'.constName?.bind env.getProjectionStructureName?
  if structure? == some ``IO.Process.Child then
    return (← Meta.whnf (← Meta.inferType expr)).isConstOf ``IO.FS.Handle
  expr.getAppArgs.anyM (usesProcessPipe locals)

private def discardedIOValue (context : Elab.ContextInfo) (term : Elab.TermInfo) : IO Bool := do
  let expr := term.expr.consumeMData
  let kind := term.stx.getKind
  let discardCall := kind == ``Parser.Term.app && expr.isAppOf ``Functor.discard
  let wildcardBind := kind == ``Parser.Term.doLetArrow &&
    term.stx[3][0].getKind == ``Parser.Term.hole && expr.isAppOf ``Bind.bind
  unless discardCall || wildcardBind do return false
  term.runMetaM context do
    let args := (← instantiateMVars expr).getAppArgs
    let discarded := match discardCall, args with
      | true, #[monad, type, _, action] | false, #[monad, _, type, _, action, _] =>
        some (monad, type, action)
      | _, _ => none
    let some (monad, type, action) := discarded | return false
    unless monad.isConstOf ``IO || monad.isAppOf ``EIO do return false
    let action := localValue term.lctx action
    if action.isAppOf ``Pure.pure then return false
    let type ← Meta.whnf type
    if type.isConstOf ``Unit || type.isConstOf ``PUnit then return false
    if type.isConstOf ``IO.Process.Output || type.isAppOf ``Except then return true
    usesProcessPipe term.lctx action

private def auditTerm (map : FileMap) (loops : List Syntax.Range) (context : Elab.ContextInfo)
    (info : Elab.Info) (evidence : AuditEvidence) : IO AuditEvidence := do
  let .ofTermInfo term := info | return evidence
  let some pos := term.stx.getPos? | return evidence
  let expr := term.expr.consumeMData
  let evidence := if isUnitReturn expr then
      { evidence with unitReturns := evidence.unitReturns.insert pos.byteIdx }
    else evidence
  let evidence := match term.isBinder, expr with
    | true, .fvar id => { evidence with binders := evidence.binders.insert (pos.byteIdx, id) }
    | _, _ => evidence
  let evidence := match searchedValue? term.lctx expr with
    | some id => { evidence with searchedValues := (id, pos) :: evidence.searchedValues }
    | none => evidence
  let mut rule := resolvedRule term expr loops pos
  if rule.isNone then
    if ← selfComparison context term expr then rule := some "self-comparison"
    else if ← successOnFailedPattern context term then rule := some "success-on-failed-pattern"
    else if ← discardedIOValue context term then rule := some "discarded-io-value"
  match rule with
  | some detected =>
    let severity := if detected == "unsafe-cast" then "No-Go" else "Warning"
    return { evidence with findings := ⟨map.toPosition pos, severity, detected⟩ :: evidence.findings }
  | none => return evidence

private def auditFile (file : System.FilePath) : IO (List Finding) := do
  let source ← IO.FS.readFile file
  let ctx := Parser.mkInputContext source file.toString
  let (header, parserState, headerMessages) ← Parser.parseHeader ctx
  unsafe enableInitializersExecution
  let (env, importMessages) ← Elab.processHeader header {} headerMessages ctx
  if importMessages.hasErrors then
    importMessages.forM fun msg => do
      IO.eprintln (← msg.toString)
    throw <| IO.userError "unable to load Lean imports"
  let elaboration ← Elab.IO.processCommands ctx parserState (Elab.Command.mkState env {} {})
  if elaboration.commandState.messages.hasErrors then
    elaboration.commandState.messages.forM fun msg => do
      IO.eprintln (← msg.toString)
    throw <| IO.userError "Lean reported source errors"
  let commands := header.raw :: elaboration.commands.toList
  let loops := commands.flatMap loopRanges
  let mut evidence : AuditEvidence := {}
  for tree in elaboration.commandState.infoState.trees do
    evidence ← tree.foldInfoM (auditTerm ctx.fileMap loops) evidence
  let findings := commands.flatMap (auditSyntax ctx.fileMap evidence) ++ evidence.findings
  let ordered := findings.mergeSort fun left right =>
    left.position.lt right.position ||
      (decide (left.position = right.position) && left.rule <= right.rule)
  return ordered.eraseRepsBy fun left right =>
    decide (left.position = right.position) && left.rule == right.rule

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: lake exe l4 <file-or-directory>..."
    return 2
  let sysroot ← findSysroot
  initSearchPath sysroot
  let lake := Lake.LakeInstall.ofLean { sysroot }
  if ← lake.sharedLib.pathExists then
    loadDynlib lake.sharedLib
  let mut blocked := false
  let mut failed := false
  let mut count := 0
  for arg in args do
    let path := System.FilePath.mk arg
    let files ← if ← path.isDir then path.walkDir else pure #[path]
    for file in files do
      if !file.toString.endsWith ".lean" then continue
      try
        for finding in (← auditFile file) do
          IO.println s!"{file}:{finding.position.line} [{finding.severity}] {finding.rule}"
          count := count + 1
          if finding.severity == "No-Go" then blocked := true
      catch error =>
        failed := true
        IO.eprintln s!"{file} [Analysis Error] {error}"
  IO.println s!"Findings: {count}"
  return if failed then 2 else if blocked then 1 else 0
