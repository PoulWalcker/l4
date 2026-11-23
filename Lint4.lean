import Lean
import Lake.Config.InstallPath

open Lean System

private def defaultPurePaths : List String := ["pure"]
private def defaultDeniedImports : List (String × String) := [("pure", "io"), ("pure", "jobs")]

structure Finding where
  line : Nat
  level : String
  rule : String
  detail : String

structure SourceLine where
  text : String
  comment : Bool

private def hasAny (text : String) (terms : List String) : Bool :=
  terms.any (fun term => text.contains term)

private def add (hits : Array Finding) (line : Nat) (level rule detail : String) : Array Finding :=
  hits.push ⟨line, level, rule, detail⟩

private def cleanLine (source : String) (initialDepth : Nat) (initialQuoted : Bool) :
    SourceLine × Nat × Bool := Id.run do
  let chars := source.toList.toArray
  let mut depth := initialDepth
  let mut quoted := initialQuoted
  let mut escaped := false
  let mut foundComment := false
  let mut result := ""
  let mut i := 0
  while i < chars.size do
    let c := (chars[i]?).getD ' '
    let next := (chars[i + 1]?).getD ' '
    if depth > 0 then
      if c == '/' && next == '-' then
        depth := depth + 1
        i := i + 2
      else if c == '-' && next == '/' then
        depth := depth - 1
        i := i + 2
      else
        i := i + 1
    else if quoted then
      result := result.push ' '
      if escaped then
        escaped := false
      else if c == '\\' then
        escaped := true
      else if c == '"' then
        quoted := false
      i := i + 1
    else if c == '\'' &&
        ((next != '\\' && (chars[i + 2]?).getD ' ' == '\'') ||
         (next == '\\' && (chars[i + 3]?).getD ' ' == '\'')) then
      i := i + (if next == '\\' then 4 else 3)
    else if c == '"' then
      quoted := true
      result := result.push ' '
      i := i + 1
    else if c == '-' && next == '-' then
      foundComment := true
      i := chars.size
    else if c == '/' && next == '-' then
      foundComment := true
      depth := 1
      i := i + 2
    else
      result := result.push c
      i := i + 1
  return (⟨result, foundComment⟩, depth, quoted)

private def cleanFile (source : String) : Array SourceLine := Id.run do
  let mut depth := 0
  let mut quoted := false
  let mut lines := #[]
  for line in source.splitOn "\n" do
    let (clean, nextDepth, nextQuoted) := cleanLine line depth quoted
    lines := lines.push clean
    depth := nextDepth
    quoted := nextQuoted
  return lines

private def declKeyword (source : String) : String :=
  let words := (source.trimAscii.toString.splitOn " ").filter (· != "")
  (words.dropWhile (fun w =>
    ["private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "scoped"].contains w)).headD ""

private def startsDef (s : String) : Bool :=
  declKeyword s == "def"

private def isBoundary (source : String) : Bool :=
  let s := source.trimAscii.toString
  source.startsWith s && (s.startsWith "#" ||
    (["def", "structure", "inductive", "theorem", "lemma", "example", "instance",
      "abbrev", "class", "opaque", "constant", "axiom", "section", "end",
      "namespace", "open", "initialize", "macro", "syntax", "elab", "mutual",
      "variable", "universe", "export", "attribute", "set_option", "notation",
      "infix", "infixl", "infixr", "prefix", "postfix"].contains (declKeyword s)))

private def lineAt (lines : Array SourceLine) (i : Nat) : String :=
  ((lines[i]?).getD ⟨"", false⟩).text.trimAscii.toString

private def containsWord (source word : String) : Bool :=
  let chars := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'".toList
  let normalized := String.ofList (source.toList.map fun c => if chars.contains c then c else ' ')
  (normalized.splitOn " ").contains word

private def containsSymbol (source name : String) : Bool :=
  let chars := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'.!".toList
  let normalized := String.ofList (source.toList.map fun c => if chars.contains c then c else ' ')
  (normalized.splitOn " ").any (fun token =>
    token == name || token.endsWith ("." ++ name))

private def stringArgumentCount (signature : String) : Nat :=
  let groups := (signature.replace "{" "(").replace "}" ")"
  let groups := (groups.replace "⦃" "(").replace "⦄" ")"
  ((groups.splitOn "(").drop 1).foldl (fun count segment =>
    let binder := ((segment.splitOn ")").headD "").trimAscii.toString
    if binder.endsWith ": String" then
      count + ((((binder.splitOn ": String").headD "").splitOn " ").filter (· != "")).length
    else count) 0

private def usedBeforeRebinding (lines : Array SourceLine) (start : Nat)
    (name suffix : String) : Bool := Id.run do
  let mut j := start
  while j < lines.size do
    let raw := ((lines[j]?).getD ⟨"", false⟩).text
    if isBoundary raw then return false
    let current := raw.trimAscii.toString
    if current.startsWith ("let " ++ name ++ " ") ||
        current.startsWith ("let mut " ++ name ++ " ") then return false
    if containsSymbol current (name ++ suffix) then return true
    j := j + 1
  return false

private def letName (line : String) : String :=
  let parts := (((line.drop 4).toString.trimAscii.toString).splitOn " ").filter (· != "")
  let token := if parts.headD "" == "mut" then (parts.drop 1).headD "" else parts.headD ""
  (token.splitOn ":").headD ""

private def checkLine (line rawLength : Nat) (source : SourceLine) : Array Finding := Id.run do
  let code := source.text
  let stripped := code.trimAscii.toString
  let mut hits := #[]
  if source.comment then
    hits := add hits line "Warning" "N01" "Comment"
  if (["unsafeCoerce", "unsafePerformIO", "unsafeCast", "unsafeRefEq"].any
      (containsWord code)) || containsWord code "unsafe" then
    hits := add hits line "No-Go" "N03" "Unsafe operation"
  if code.contains "Except String" then
    hits := add hits line "Warning" "W01" "Stringly-typed error"
  if hasAny code ["getObjValD", ".toOption.getD", ".getD "] then
    let detail := if code.contains "getObjValD" && code.contains "some" then
      "Defaulted JSON returned as present" else "Silent default or fallback"
    hits := add hits line "Warning" "W02" detail
  if code.contains ".compress.contains" then
    hits := add hits line "Warning" "W03" "Text search over serialized JSON"
  if startsDef stripped && containsWord stripped "partial" then
    hits := add hits line "Warning" "W10" "Partial definition"
  if code.contains "dbg_trace" then
    hits := add hits line "Warning" "W12" "Debug trace"
  if code.contains ".toString.contains" then
    hits := add hits line "Warning" "W13" "String matching over formatted value"
  if rawLength > 160 then
    hits := add hits line "Could Be Better" "C01" "Long source line"
  return hits

private def checkBlocks (lines : Array SourceLine) : Array Finding := Id.run do
  let mut hits := #[]
  for i in [:lines.size] do
    let raw := ((lines[i]?).getD ⟨"", false⟩).text
    let current := lineAt lines i
    let next := lineAt lines (i + 1)
    if current.startsWith "catch " && current.contains "=>" then
      let remainder := ((current.splitOn "=>").getLast?).getD ""
      if ["pure ()", "return ()"].contains remainder.trimAscii.toString ||
          (remainder.trimAscii.toString == "" && ["pure ()", "return ()"].contains next) then
        hits := add hits (i + 1) "Warning" "W04" "Discarded exception"
    if current.startsWith "let " && current.contains ".toString" then
      let name := letName current
      if !name.isEmpty && usedBeforeRebinding lines (i + 1) name ".contains" then
        hits := add hits (i + 1) "Warning" "W13" "String matching over formatted value"
    if current.startsWith "let " && current.contains ".toOption" then
      let name := letName current
      if !name.isEmpty && usedBeforeRebinding lines (i + 1) name ".getD" then
        hits := add hits (i + 1) "Warning" "W02" "Error discarded through Option default"
    if isBoundary raw && startsDef current then
      let mut signature := current
      let mut j := i + 1
      while !(signature.contains ":=") && j < lines.size &&
          !isBoundary ((lines[j]?).getD ⟨"", false⟩).text do
        signature := signature ++ " " ++ ((lines[j]?).getD ⟨"", false⟩).text.trimAscii.toString
        j := j + 1
      let header := (signature.splitOn ":=").headD ""
      if stringArgumentCount header >= 2 then
        hits := add hits (i + 1) "Could Be Better" "W05" "Several arguments use String; review domain types"
      let mut endLine := i + 1
      while endLine < lines.size do
        let next := ((lines[endLine]?).getD ⟨"", false⟩).text
        if isBoundary next then break
        endLine := endLine + 1
      if endLine - i > 60 then
        hits := add hits (i + 1) "Could Be Better" "C02" "Function longer than 60 lines"
      let body := String.intercalate "\n" ((lines.extract i endLine).toList.map (·.text))
      if hasAny body ["IO.FS.readFile", "IO.FS.readBinFile"] && body.contains "Json.parse" then
        hits := add hits (i + 1) "Warning" "I03" "Direct JSON storage read; review contract coupling"
      if hasAny body ["IO.FS.writeFile", "IO.FS.writeBinFile"] &&
          hasAny body [".compress", "toJson", "setObjVal", "Json.parse", "Json.mkObj"] then
        hits := add hits (i + 1) "Warning" "I04" "Direct JSON file write; review storage contract"
    if isBoundary raw && declKeyword current == "structure" then
      let mut stringFields := 0
      let mut boolFields := 0
      let mut j := i + 1
      while j < lines.size do
        let field := ((lines[j]?).getD ⟨"", false⟩).text
        if isBoundary field then break
        if field.contains ": String" then stringFields := stringFields + 1
        if field.contains ": Bool" then boolFields := boolFields + 1
        j := j + 1
      if stringFields >= 3 then
        hits := add hits (i + 1) "Could Be Better" "W07" "Three or more String fields; review domain types"
      if boolFields >= 3 then
        hits := add hits (i + 1) "Could Be Better" "W08" "Three or more Bool fields; review state model"
  return hits

private partial def localValue (locals : LocalContext) (expr : Expr) : Expr :=
  let expr := expr.consumeMData
  match expr with
  | .fvar id =>
    match (locals.find? id).bind (·.value?) with
    | some value => localValue locals value
    | none => expr
  | .letE _ _ value body _ => localValue locals (body.instantiate1 value)
  | _ => expr

private partial def unlift (locals : LocalContext) (expr : Expr) : Expr :=
  let expr := localValue locals expr
  match expr.getAppFn'.constName? with
  | some ``liftM | some ``MonadLift.monadLift | some ``MonadLiftT.monadLift =>
    match expr.getAppArgs.back? with
    | some action => unlift locals action
    | none => expr
  | _ => expr

private def isTimer (locals : LocalContext) (expr : Expr) : Bool :=
  let expr := unlift locals expr
  expr.isAppOf `Std.Async.sleep || expr.isAppOf ``IO.sleep

private def timerBranch (locals : LocalContext) (expr : Expr) : Bool :=
  let expr := unlift locals expr
  if isTimer locals expr then true
  else
    match expr.getAppFn'.constName?, expr.getAppArgs with
    | some ``Bind.bind, #[_, _, _, _, action, .lam _ _ result _] =>
      isTimer locals action && (result.isAppOf ``Pure.pure || result.isAppOf ``MonadExcept.throw)
    | _, _ => false

private def timerRace (locals : LocalContext) (expr : Expr) (name : Name) : Bool :=
  let args := expr.getAppArgs
  let branches := match name, args with
    | `Std.Async.Async.race, #[_, _, first, second, _]
    | `Std.Async.BaseAsync.race, #[_, _, first, second, _]
    | `Std.Async.ContextAsync.race, #[_, _, first, second, _]
    | `Std.Async.EAsync.race, #[_, _, _, first, second, _] => some (first, second)
    | _, _ => none
  match branches with
  | some (first, second) => timerBranch locals first != timerBranch locals second
  | none => false

private def readsClock (locals : LocalContext) (action : Expr) : Bool :=
  let action := unlift locals action
  action.isConstOf ``IO.monoMsNow || action.isConstOf ``IO.monoNanosNow

private partial def clockDerived (locals : LocalContext) (bindings : Std.HashSet FVarId)
    (readings : List Bool) (expr : Expr) : Bool :=
  let expr := localValue locals expr
  match expr with
  | .bvar index => readings[index]?.getD false
  | .fvar id => bindings.contains id
  | .app .. => expr.getAppArgs.any (clockDerived locals bindings readings)
  | .proj _ _ value => clockDerived locals bindings readings value
  | _ => false

private partial def stopsWaiting (expr : Expr) : Bool :=
  let expr := expr.consumeMData
  match expr.getAppFn'.constName?, expr.getAppArgs with
  | some ``MonadExcept.throw, _ => true
  | some ``Pure.pure, #[_, _, _, value] => value.isAppOf ``ForInStep.done
  | some ``Bind.bind, #[_, _, _, _, action, .lam _ _ body _] =>
    stopsWaiting action || stopsWaiting body
  | _, _ =>
    match expr with
    | .lam _ _ body _ | .letE _ _ _ body _ => stopsWaiting body
    | _ => false

private partial def clockGuard? (locals : LocalContext) (readings : List Bool)
    (expr : Expr) : Option (List Bool × Expr) :=
  let expr := localValue locals expr
  match expr.getAppFn'.constName?, expr.getAppArgs with
  | some ``Bind.bind, #[_, _, _, _, action, .lam _ _ body _] =>
    clockGuard? locals (readsClock locals action :: readings) body
  | some ``ite, #[_, condition, _, first, second]
  | some ``dite, #[_, condition, _, first, second] =>
    let condition := localValue locals condition
    match condition.getAppFn'.constName? with
    | some ``LT.lt | some ``LE.le | some ``GT.gt | some ``GE.ge =>
      if stopsWaiting first != stopsWaiting second then some (readings, condition) else none
    | _ => none
  | _, _ => none

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
    if action.isAppOf ``IO.Process.spawn || action.isAppOf ``IO.FS.readFile ||
        action.isAppOf ``IO.FS.readBinFile then return true
    usesProcessPipe term.lctx action

private structure SemanticEvidence where
  hits : Array Finding := #[]
  partialSites : Std.HashSet Nat := {}
  binders : Std.HashSet (Nat × FVarId) := {}
  clockBindings : Std.HashSet Nat := {}
  clockGuards : List (Nat × LocalContext × List Bool × Expr) := []

private partial def loopRanges (stx : Syntax) : List Syntax.Range :=
  let nested := stx.getArgs.toList.flatMap loopRanges
  match stx.getKind with
  | ``Parser.Term.doWhile | ``Parser.Term.doRepeat | ``Parser.Term.doRepeatUntil |
    ``Parser.Term.doFor => stx.getRange?.toList ++ nested
  | _ => nested

private def referencesTimer (env : Environment) (expr : Expr) : Bool := Id.run do
  let mut expr := expr
  let mut seen : NameSet := {}
  repeat
    let some name := (localValue {} expr.getLambdaBody).getAppFn'.constName? | return false
    if [``IO.sleep, `Std.Async.sleep, `Std.Async.Selector.sleep].contains name then return true
    if seen.contains name then return false
    seen := seen.insert name
    let some (.defnInfo info) := env.find? name | return false
    expr := info.value
  return false

private def partialOperation? (stx : Syntax) (expr : Expr) : Option Syntax :=
  if stx.getKind == ``Parser.Term.panic then some stx[0]
  else if stx.getKind == `«term__[_]_!» then some stx[6]
  else if stx.isIdent || stx.getKind == `Lean.Parser.Term.identProj then
    match expr.getAppFn'.constName? with
    | some (.str _ name) =>
      if ["head!", "getLast!", "get!", "setObjVal!", "panic!"].contains name then some stx else none
    | _ => none
  else none

private def auditTerm (map : FileMap) (loops : List Syntax.Range) (context : Elab.ContextInfo) (info : Elab.Info)
    (evidence : SemanticEvidence) : IO SemanticEvidence := do
  let .ofTermInfo term := info | return evidence
  let some pos := term.stx.getPos? | return evidence
  let expr := (instantiateMVarsCore context.mctx term.expr).1.consumeMData
  if term.isBinder then
    let .fvar id := expr | return evidence
    return { evidence with binders := evidence.binders.insert (pos.byteIdx, id) }
  let line := (map.toPosition pos).line
  let kind := term.stx.getKind
  let mut evidence := evidence
  if let some operation := partialOperation? term.stx expr then
    if let some stop := operation.getTailPos? then
      unless evidence.partialSites.contains stop.byteIdx do
        evidence := { evidence with
          partialSites := evidence.partialSites.insert stop.byteIdx
          hits := add evidence.hits (map.toPosition stop).line "No-Go" "N04" "Partial operation" }
  if expr.isSorry || expr.isConstOf ``sorryAx then
    evidence := { evidence with hits := add evidence.hits line "No-Go" "N05" "Unproven placeholder" }
  if referencesTimer context.env (localValue term.lctx expr) then
    evidence := { evidence with hits := add evidence.hits line "No-Go" "N02" "Manual timer or wait" }
  if let some name := expr.getAppFn'.constName? then
    if kind == ``Parser.Term.app && timerRace term.lctx expr name then
      evidence := { evidence with hits := add evidence.hits line "Warning" "W09" "Race against a timer" }
  if kind == ``Parser.Term.doLetArrow then
    if let (some ``Bind.bind, #[_, _, _, _, action, _]) := (expr.getAppFn'.constName?, expr.getAppArgs) then
      if readsClock term.lctx action then
        if let some binder := term.stx[3][0].getPos? then
          evidence := { evidence with clockBindings := evidence.clockBindings.insert binder.byteIdx }
  if kind == ``Parser.Term.doIf && loops.any (fun r => r.start <= pos && pos < r.stop) then
    if let some (readings, condition) := clockGuard? term.lctx [] expr then
      evidence := { evidence with clockGuards := (line, term.lctx, readings, condition) :: evidence.clockGuards }
  if ← discardedIOValue context term then
    evidence := { evidence with hits := add evidence.hits line "Warning" "W16" "Discarded IO result" }
  return evidence

private def findingsInOrder (left right : Finding) : Bool :=
  if left.line == right.line then left.rule < right.rule else left.line < right.line

private def jsonOnBothSides (signature : Expr) : Bool :=
  let mentionsJson := fun (e : Expr) => e.getUsedConstants.contains ``Json
  let rec visit (type : Expr) (hasInput : Bool) : Bool :=
    match type with
    | .forallE _ domain body _ => visit body (hasInput || mentionsJson domain)
    | _ => hasInput && mentionsJson type
  visit signature false

private def isIOName (name : Name) : Bool :=
  [``IO, ``EIO, ``BaseIO].any (fun root => root.isPrefixOf name)

private def usesIO (env : Environment) (roots : Array Name) : Bool := Id.run do
  let mut todo := roots
  let mut seen : NameSet := {}
  while let some name := todo.back? do
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    if isIOName name then return true
    if let some (.defnInfo info) := env.find? name then
      if info.hints.isAbbrev then
        todo := todo ++ info.value.getUsedConstants
  return false

private def standardAxiom (env : Environment) (name : Name) : Bool :=
  match (env.getModuleIdxFor? name).bind (fun index => env.header.moduleNames[index]?) with
  | some origin => [`Init, `Lean, `Std, `Lake].any (fun root => root.isPrefixOf origin)
  | none => false

private def declarationFindings (pureModule : Bool) : CoreM (Array Finding) := do
  let env ← getEnv
  let mut hits := #[]
  for (name, info) in env.constants.map₂ do
    let some ranges ← findDeclarationRangesCore? name | continue
    let line := ranges.selectionRange.pos.line
    let axioms ← collectAxioms name
    if axioms.contains ``sorryAx then
      hits := add hits line "No-Go" "N05" "Declaration depends on sorryAx"
    for axiomName in axioms do
      unless axiomName == ``sorryAx || standardAxiom env axiomName do
        hits := add hits line "Warning" "W11" s!"Depends on axiom {axiomName}"
    if pureModule && usesIO env
        (info.type.getUsedConstants ++ (info.value? true).toArray.flatMap Expr.getUsedConstants) then
      hits := add hits line "No-Go" "I01" "IO dependency in declared pure module"
    if let .defnInfo defn := info then
      if jsonOnBothSides defn.type ||
          (defn.hints.isAbbrev && jsonOnBothSides defn.value.getLambdaBody) then
        hits := add hits line "Warning" "W06" "JSON used on both sides of an API"
  return hits

private partial def executesCode (stx : Syntax) : Bool :=
  [``Parser.Command.eval, ``Parser.Command.evalBang, ``Parser.Command.initialize,
    `Lean.runCmd, `Lean.runElab, `Lean.runMeta].contains stx.getKind ||
      stx.getArgs.any executesCode

open Elab.Frontend in
private partial def elaborateCommands : FrontendM Unit := do
  updateCmdPos
  let state ← get
  let input ← getInputContext
  let scope := state.commandState.scopes.head!
  let context := {
    env := state.commandState.env
    options := scope.opts
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls }
  let (cmd, parserState, messages) :=
    Parser.parseCommand input context state.parserState state.commandState.messages
  if executesCode cmd then
    let line := (input.fileMap.toPosition (cmd.getPos?.getD state.cmdPos)).line
    throw <| IO.userError s!"{input.fileName}:{line}: executable command is unsupported by static audit"
  modify fun s => { s with commands := s.commands.push cmd }
  setParserState parserState
  elabCommandAtFrontend cmd
  modify fun s => { s with commandState := { s.commandState with
    messages := messages ++ s.commandState.messages
    infoState := { s.commandState.infoState.substituteLazy.get with
      trees := state.commandState.infoState.trees.append s.commandState.infoState.substituteLazy.get.trees } } }
  unless Parser.isTerminalCommand cmd do elaborateCommands

private def semanticFindings (path : FilePath) (source : String)
    (pureModule : Bool) (deniedModules : List Name) : IO (Array Finding) := do
  let ctx := Parser.mkInputContext source path.toString
  let (header, parserState, headerMessages) ← Parser.parseHeader ctx
  unsafe enableInitializersExecution
  let (env, messages) ← Elab.processHeader header {} headerMessages ctx
  if messages.hasErrors then
    messages.forM fun message => do
      if message.severity == .error then IO.eprintln (← message.toString)
    throw (IO.userError "Unable to load Lean imports")
  let (_, elaboration) ← (elaborateCommands.run { inputCtx := ctx }).run
    { commandState := Elab.Command.mkState env {} {}, parserState, cmdPos := parserState.pos }
  let messages := elaboration.commandState.messages
  if messages.hasErrors then
    messages.forM fun message => do
      if message.severity == .error then IO.eprintln (← message.toString)
    throw (IO.userError "Lean reported source errors")
  let (declarations, _) ← (declarationFindings pureModule).toIO
    { fileName := path.toString, fileMap := ctx.fileMap } { env := elaboration.commandState.env }
  let loops := elaboration.commands.toList.flatMap loopRanges
  let mut evidence : SemanticEvidence := { hits := declarations }
  for imported in env.header.imports do
    if deniedModules.any (fun denied => denied.isPrefixOf imported.module) then
      evidence := { evidence with hits := add evidence.hits 1 "No-Go" "I02" s!"Forbidden module dependency: {imported.module}" }
  for tree in elaboration.commandState.infoState.substituteLazy.get.trees do
    evidence ← tree.foldInfoM (auditTerm ctx.fileMap loops) evidence
  let readers := evidence.binders.toList.foldl (fun found (pos, id) =>
    if evidence.clockBindings.contains pos then found.insert id else found) ({} : Std.HashSet FVarId)
  let mut hits := evidence.hits
  for (line, locals, readings, condition) in evidence.clockGuards do
    if clockDerived locals readers readings condition then
      hits := add hits line "Warning" "W09" "Clock-based limit on a wait"
  return ((hits.qsort findingsInOrder).toList.eraseRepsBy fun left right =>
    left.rule != "N04" && left.line == right.line && left.rule == right.rule).toArray



private def normalizePath (path : String) : String :=
  String.intercalate "/" <|
    ((path.replace "\\" "/").splitOn "/").filter (fun p => p != "" && p != ".")

private def normalizeSelector (path : String) : String :=
  if path == "." || path == "./" then "." else normalizePath path

private def pathHasPrefix (path selector : String) : Bool :=
  selector == "." || (!selector.isEmpty && (path == selector || path.startsWith (selector ++ "/")))

private def relativePath (root path : FilePath) : String :=
  let base := normalizePath root.toString
  let file := normalizePath path.toString
  if !base.isEmpty && file.startsWith (base ++ "/") then
    (file.drop (base.length + 1)).toString
  else file

private def checkSource (source : String) : Array Finding := Id.run do
  let lines := cleanFile source
  let rawLines := (source.splitOn "\n").toArray
  let mut hits := checkBlocks lines
  for i in [:lines.size] do
    let line := (lines[i]?).getD ⟨"", false⟩
    hits := hits ++ checkLine (i + 1) (((rawLines[i]?).getD "").length) line
  return hits

private def auditFile (path : FilePath) (pureModule : Bool) (deniedModules : List Name) : IO UInt32 := do
  try
    let source ← IO.FS.readFile path
    let hits := ((checkSource source) ++ (← semanticFindings path source pureModule deniedModules)).qsort findingsInOrder
    for hit in hits do
      IO.println s!"{path}:{hit.line}: {hit.level} {hit.rule} {hit.detail}"
    return if hits.any (fun hit => hit.level == "No-Go") then 1 else 0
  catch error =>
    IO.eprintln s!"{path}: Analysis Error: {error}"
    return 2

private def auditorSource : String := by_elab
  return Lean.toExpr (← IO.FS.realPath (← Lean.getFileName)).toString

private def auditInProcess (path : FilePath) (pureModule : Bool) (deniedModules : List Name) : IO UInt32 := do
  let app ← IO.appPath
  let launchArgs := if [some "lean", some "lean.exe"].contains app.fileName then #["--run", auditorSource] else #[]
  let args := launchArgs ++ #[path.toString, "--worker"] ++
    (if pureModule then #["--pure=."] else #[]) ++
    (deniedModules.map fun name => s!"--deny-import=.:{name}").toArray
  let env := #[("LEAN_PATH", some (System.SearchPath.toString (← searchPathRef.get)))]
  let status ← (← IO.Process.spawn { cmd := app.toString, args, env }).wait
  if status > 2 then IO.eprintln s!"{path}: Analysis process exited with code {status}"
  return if status > 2 then 2 else status

private def scan (root : FilePath) (purePaths : List String)
    (deniedImports : List (String × String)) (quiet : Bool) : IO UInt32 := do
  let paths ← if ← root.isDir then root.walkDir (fun path => do
    let normalized := (path.toString.replace "\\" "/") ++ "/"
    return !(hasAny normalized ["/.git/", "/.lake/", "/.build/", "/node_modules/"]))
    else pure #[root]
  let sources := (paths.filter (fun path => path.toString.endsWith ".lean" && path.fileName != some "lakefile.lean")).qsort
    (fun a b => a.toString < b.toString)
  if sources.isEmpty then
    IO.eprintln "No Lean source files found"
    return 2
  let mut blockers := 0
  let mut failures := 0
  let external := paths.filter fun path =>
    [".purs", ".hs", ".js", ".ts"].any
      (fun ext => path.toString.endsWith ext)
  for path in external do
    IO.println s!"{path}:0: Warning B03 Non-Lean source not analyzed"
  for path in sources do
    let selected := fun selector => pathHasPrefix (normalizePath path.toString) selector ||
      pathHasPrefix (relativePath root path) selector
    let pureModule := purePaths.any selected
    let deniedModules := deniedImports.filterMap fun (src, target) =>
      if selected src then some target.toName else none
    let status ← if sources.size > 1 then auditInProcess path pureModule deniedModules
      else auditFile path pureModule deniedModules
    if status == 1 then blockers := blockers + 1
    if status == 2 then failures := failures + 1
  unless quiet do
    IO.println s!"Audited {sources.size} Lean files; {blockers} with No-Go; {failures} analysis errors"
  return if failures > 0 then 2 else if blockers > 0 then 1 else 0

def main (args : List String) : IO UInt32 := do
  let positions := args.filter (fun a => !a.startsWith "--")
  let options := args.filter (·.startsWith "--")
  if positions.length > 1 || options.any (fun a =>
      !a.startsWith "--pure=" && !a.startsWith "--deny-import=" && a != "--source-only" && a != "--worker") then
    IO.eprintln "Usage: Lint4 [PATH] [--pure=PATH] [--deny-import=PATH:MODULE]"
    return 2
  let path := FilePath.mk (positions.headD ".")
  if !(← path.pathExists) then
    IO.eprintln s!"Path does not exist: {path}"
    return 2
  let purePaths := args.filterMap fun a =>
    (a.dropPrefix? "--pure=").map (normalizeSelector ∘ String.Slice.toString)
  let useDefaults := !args.contains "--worker"
  let purePaths := if purePaths.isEmpty && useDefaults then defaultPurePaths else purePaths
  let denyArgs := args.filterMap fun a =>
    (a.dropPrefix? "--deny-import=").map String.Slice.toString
  if purePaths.any (·.isEmpty) || denyArgs.any (fun rule =>
      match rule.splitOn ":" with
      | [src, target] => (normalizeSelector src).isEmpty || target.isEmpty
      | _ => true) then
    IO.eprintln "Invalid --pure or --deny-import argument"
    return 2
  let deniedImports := denyArgs.filterMap fun rule =>
    match rule.splitOn ":" with
    | [src, target] => some (normalizeSelector src, target)
    | _ => none
  let deniedImports := if denyArgs.isEmpty && useDefaults then defaultDeniedImports else deniedImports
  let sysroot ← findSysroot
  let lake := Lake.LakeInstall.ofLean { sysroot }
  let isPackage ← (path / "lakefile.lean").pathExists <||> (path / "lakefile.toml").pathExists
  let mut projectPath : Lean.SearchPath := []
  if isPackage then
    let cmd := (← determineLakePath).toString
    let env ← IO.Process.output { cmd, args := #["env"], cwd := path }
    if env.exitCode != 0 then
      IO.eprintln env.stderr
      return 2
    let some paths := (env.stdout.splitOn "\n").findSome? (·.dropPrefix? "LEAN_PATH=") |
      IO.eprintln "Lake did not provide the package search path"
      return 2
    projectPath := System.SearchPath.parse paths.trimAscii.toString
  initSearchPath sysroot projectPath
  if ← lake.sharedLib.pathExists then
    loadDynlib lake.sharedLib
  scan path purePaths deniedImports (args.contains "--worker")
