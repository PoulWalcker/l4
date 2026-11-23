import Lint4.Expressions
import Lint4.Finding

namespace Lint4.TextChecks

open Lean

private def directFormatter (expr : Expr) : MetaM Bool := do
  unless (← Meta.whnf (← Meta.inferType expr)).isConstOf ``String do return false
  let args := expr.getAppArgs
  let some value := args.back? | return false
  let type ← Meta.whnf (← Meta.inferType value)
  if [``String, ``String.Slice, ``Substring.Raw].any type.isConstOf || (← Meta.isProp type) then return false
  let some formatInstance ← Meta.synthInstance? (← Meta.mkAppM ``ToString #[type]) | return false
  let formatter ← Meta.mkAppOptM ``ToString.toString #[some type, some formatInstance]
  Meta.withTransparency .instances <| Meta.isDefEq (mkAppN expr.getAppFn' args.pop) formatter

private inductive Representation where
  | json | formatted
  deriving BEq

private partial def representationOf (locals : LocalContext) (expr : Expr)
    (seen : NameSet := {}) : MetaM (Option Representation) := do
  let expr := resolveLocalValue locals expr
  let expr := (mkAppN (resolveLocalValue locals expr.getAppFn') expr.getAppArgs).headBeta.consumeMData
  if expr.isAppOf ``Json.compress || expr.isAppOf ``Json.pretty then
    return some .json
  if ← directFormatter expr then return some .formatted
  if [``String.append, ``ByteArray.append, ``String.toUTF8, ``String.toByteArray,
      ``String.toSlice, ``String.Slice.copy].any expr.isAppOf then
    let kinds ← expr.getAppArgs.mapM fun argument => representationOf locals argument seen
    return if kinds.contains (some .json) then some .json else kinds.findSome? id
  if let some reduced ← Meta.unfoldProjInst? expr then
    return ← representationOf locals reduced seen
  if let some (name, reduced) := unfoldLocalDefinition? (← getEnv) seen expr then
    return ← representationOf locals reduced (seen.insert name)
  return none

private def searchReceiver? (locals : LocalContext) (expr : Expr) : Option Expr := do
  let expr := resolveLocalValue locals expr
  let expr := (mkAppN (resolveLocalValue locals expr.getAppFn') expr.getAppArgs).headBeta.consumeMData
  unless [``String.contains, ``String.Slice.contains].contains (expr.getAppFn'.constName?.getD Name.anonymous) do
    none
  expr.getAppArgs[4]?

private def jsonSubstringSearch (locals : LocalContext) (expr : Expr) : MetaM (Option Name) := do
  let expr := expr.headBeta.consumeMData
  unless expr.isAppOf ``String.contains do return none
  let #[patternType, _, _, _, text, _, _] := expr.getAppArgs | return none
  unless (← Meta.whnf patternType).isConstOf ``String do return none
  return [``Json.compress, ``Json.pretty].find? (resolveLocalValue locals text).isAppOf

private def writesSerializedJson (context : Elab.ContextInfo) (term : Elab.TermInfo)
    (action : Expr) : IO Bool := do
  unless action.isAppOf ``IO.FS.writeFile || action.isAppOf ``IO.FS.writeBinFile do return false
  let #[_, payload] := action.getAppArgs | return false
  return (← term.runMetaM context <| representationOf term.lctx payload) == some .json

private def checkTextSearch (context : Elab.ContextInfo) (term : Elab.TermInfo)
    (expr action : Expr) (line : Nat) : IO (Option Finding) := do
  if let some serializer ← term.runMetaM context <| jsonSubstringSearch term.lctx action then
    return some ⟨line, .warning, "BT01", s!"{serializer} → String.contains; review JSON oracle"⟩
  let some receiver := searchReceiver? term.lctx expr | return none
  let some representation ← term.runMetaM context <| representationOf term.lctx receiver | return none
  return some <| match representation with
    | .json => ⟨line, .warning, "W03", "Text search over serialized JSON; review the oracle"⟩
    | .formatted => ⟨line, .warning, "W13", "Text search over a formatted value; review the oracle"⟩


def checkApplication (context : Elab.ContextInfo) (term : Elab.TermInfo)
    (expr action : Expr) (line : Nat) : IO (Array Finding) := do
  let mut findings := #[]
  if ← writesSerializedJson context term action then
    findings := findings.push ⟨line, .warning, "I04", "Serialized JSON reaches a file write; review storage contract"⟩
  if let some finding ← checkTextSearch context term expr action line then
    findings := findings.push finding
  return findings

end Lint4.TextChecks
