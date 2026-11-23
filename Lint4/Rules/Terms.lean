import Lint4.Frontend
import Lint4.Rules.Bodies
import Lint4.Rules.Results
import Lint4.Rules.Text
import Lint4.Rules.Waits

namespace Lint4.TermChecks

open Lean

private def forbiddenReference (env : Environment) (deniedModules : List Name)
    (expr : Expr) : Option String := do
  let name ← match expr.consumeMData with
    | .proj structureName _ _ => some structureName
    | expr => expr.getAppFn'.constName?
  let index ← env.getModuleIdxFor? name
  let origin ← env.header.moduleNames[index]?
  if deniedModules.any (·.isPrefixOf origin) then
    return s!"Forbidden module dependency: {name} from {origin}"
  none

private def partialOperationNames : List Name := [
  ``GetElem?.getElem!, `List.head!, `List.getLast!, `Option.get!,
  `ByteArray.get!, `ByteSlice.get!, `FloatArray.get!, `Subarray.get!,
  `String.get!, `String.Pos.get!, `String.Pos.Raw.get!, `String.Slice.Pos.get!,
  `Lean.Json.setObjVal!, `Lean.LocalContext.get!, `Lean.Parser.SyntaxStack.get!, `Lean.PersistentArray.get!,
  `Std.HashMap.get!, `Std.HashMap.Raw.get!, `Std.HashSet.get!, `Std.HashSet.Raw.get!,
  `Std.TreeMap.get!, `Std.TreeMap.Raw.get!, `Std.TreeSet.get!, `Std.TreeSet.Raw.get!,
  `Std.DHashMap.get!, `Std.DHashMap.Const.get!, `Std.DHashMap.Raw.get!, `Std.DHashMap.Raw.Const.get!,
  `Std.DHashMap.Internal.AssocList.get!, `Std.DHashMap.Internal.Raw₀.get!, `Std.DHashMap.Internal.Raw₀.Const.get!,
  `Std.DTreeMap.get!, `Std.DTreeMap.Const.get!, `Std.DTreeMap.Raw.get!, `Std.DTreeMap.Raw.Const.get!,
  `Std.DTreeMap.Internal.Impl.get!, `Std.DTreeMap.Internal.Impl.Const.get!,
  `Std.ExtDHashMap.get!, `Std.ExtDHashMap.Const.get!, `Std.ExtDTreeMap.get!, `Std.ExtDTreeMap.Const.get!,
  `Std.ExtHashMap.get!, `Std.ExtHashSet.get!, `Std.ExtTreeMap.get!, `Std.ExtTreeSet.get!,
  `Std.Http.Headers.get!, `Std.Internal.IndexMultiMap.get!
]

private def partialOperation? (stx : Syntax) (expr : Expr) : Option Syntax := do
  if stx.getKind == ``Parser.Term.panic then return stx[0]
  if stx.getKind == `«term__[_]_!» then return stx[6]
  guard (stx.isIdent || stx.getKind == `Lean.Parser.Term.identProj)
  let name ← expr.getAppFn'.constName?
  guard (partialOperationNames.contains name)
  return stx

private def stringErrorType (context : Elab.ContextInfo) (term : Elab.TermInfo) : IO Bool :=
  term.runMetaM context do
    let expr := (← instantiateMVars term.expr).consumeMData
    if expr.hasMVar || expr.isLet then return false
    unless ← Meta.isTypeFormer expr do return false
    let expr ← Meta.whnf expr
    unless expr.isAppOf ``Except do return false
    let some errorType := expr.getAppArgs[0]? | return false
    return (← Meta.whnf errorType).isConstOf ``String

private def usesErrorFallback (locals : LocalContext) (action : Expr) : Bool := Id.run do
  if action.isAppOf ``Json.getObjValD && action.getAppArgs.size == 2 then return true
  unless action.isAppOf ``Option.getD && action.getAppArgs.size == 3 do return false
  let option := (action.getAppArgs[1]?).map (resolveLocalValue locals)
  return option.any fun value => value.isAppOf ``Except.toOption &&
    value.getAppArgs.back?.any (fun result => !(resolveLocalValue locals result).isAppOf ``Except.ok)

private def checkDebugSyntax (fileMap : FileMap) (stx : Syntax) : Option Finding := do
  guard ([``Parser.Term.dbgTrace, ``Parser.Term.doDbgTrace, ``Parser.Tactic.dbgTrace].contains stx.getKind)
  let pos ← stx.getPos?
  return ⟨(fileMap.toPosition pos).line, .warning, "W12", "Debug trace"⟩

private def checkUnsafe (fileMap : FileMap) (env : Environment) (stx : Syntax)
    (expr : Expr) (pos : String.Pos.Raw) : Option Finding := do
  if stx.getKind == ``Parser.Term.unsafe then
    return ⟨(fileMap.toPosition pos).line, .noGo, "N03", "Unsafe operation"⟩
  guard (stx.isIdent || stx.getKind == `Lean.Parser.Term.identProj)
  let name ← expr.getAppFn'.constName?
  guard ((env.find? name).any (·.isUnsafe))
  let line := (fileMap.toPosition (stx.getTailPos?.getD pos)).line
  return ⟨line, .noGo, "N03", "Unsafe operation"⟩

private def checkExpression (fileMap : FileMap) (deniedModules : List Name) (context : Elab.ContextInfo)
    (term : Elab.TermInfo) (expr : Expr) (pos : String.Pos.Raw) : IO (Array Finding) := do
  let line := (fileMap.toPosition pos).line
  let mut findings := #[]
  if ← stringErrorType context term then
    findings := findings.push ⟨line, .warning, "W01", "Stringly-typed error"⟩

  let action := mkAppN (resolveLocalValue term.lctx expr.getAppFn') expr.getAppArgs
  if term.stx.getKind != ``Parser.Term.do && expr.isApp &&
      action.isAppOf ``dbgTrace && action.getAppArgs.size == 3 then
    findings := findings.push ⟨line, .warning, "W12", "Debug trace"⟩
  if term.stx.getKind == ``Parser.Term.app then
    if usesErrorFallback term.lctx action then
      findings := findings.push ⟨line, .warning, "W02", "Error information replaced by a fallback; review intent"⟩
    findings := findings ++ (← TextChecks.checkApplication context term expr action line)

  if let some detail := forbiddenReference context.env deniedModules expr then
    findings := findings.push ⟨line, .noGo, "I02", detail⟩
  if let some finding := checkUnsafe fileMap context.env term.stx expr pos then
    findings := findings.push finding
  if expr.isSorry || expr.isConstOf ``sorryAx then
    findings := findings.push ⟨line, .noGo, "N05", "Unproven placeholder"⟩
  return findings ++ (← ResultChecks.check context term line)

private structure Scan where
  waits : WaitChecks.Evidence
  findings : Array Finding := #[]
  seenPartialSites : Std.HashSet Nat := {}

private def recordPartialOperation (scan : Scan) (fileMap : FileMap)
    (stx : Syntax) (expr : Expr) : Scan := Id.run do
  let some stop := (partialOperation? stx expr).bind Syntax.getTailPos? | return scan
  if scan.seenPartialSites.contains stop.byteIdx then return scan
  let line := (fileMap.toPosition stop).line
  return { scan with
    seenPartialSites := scan.seenPartialSites.insert stop.byteIdx
    findings := scan.findings.push ⟨line, .noGo, "N04", "Partial operation"⟩ }

private def visit (fileMap : FileMap) (deniedModules : List Name) (context : Elab.ContextInfo)
    (info : Elab.Info) (scan : Scan) : IO Scan := do
  let scan := match checkDebugSyntax fileMap info.stx with
    | some finding => { scan with findings := scan.findings.push finding }
    | none => scan
  let some pos := info.stx.getPos? | return scan
  let line := (fileMap.toPosition pos).line

  if let some body := Elab.Term.getBodyInfo? info then
    let some value := body.value? | return scan
    let value := (instantiateMVarsCore context.mctx value).1
    return { scan with findings := scan.findings ++ BodyChecks.check context.env value line }

  let .ofTermInfo term := info | return scan
  let expr := (instantiateMVarsCore context.mctx term.expr).1.consumeMData
  if term.isBinder then
    let .fvar id := expr | return scan
    return { scan with waits := WaitChecks.observeBinder scan.waits pos id }

  let findings ← checkExpression fileMap deniedModules context term expr pos
  let scan := recordPartialOperation scan fileMap term.stx expr
  let (waits, waitFindings) := WaitChecks.observeTerm scan.waits context.env term expr pos line
  return { scan with waits, findings := scan.findings ++ findings ++ waitFindings }

def check (file : ElaboratedFile) (deniedModules : List Name) : IO (Array Finding) := do
  let mut scan : Scan := { waits := WaitChecks.start file.commands }
  for tree in file.infoTrees do
    scan ← tree.foldInfoM (visit file.input.fileMap deniedModules) scan
  return scan.findings ++ WaitChecks.finish scan.waits

end Lint4.TermChecks
