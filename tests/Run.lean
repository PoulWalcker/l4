import Lean

open System

private def check (binary project : FilePath) (target : String) (code : UInt32)
    (blocks : List String) (counts : Nat × Nat × Nat) (footer := "") (errorText : List String := []) : IO Unit := do
  let out ← IO.Process.output { cmd := binary.toString, args := #[target], cwd := project }
  let (blockers, warnings, suggestions) := counts
  let summary := s!"Summary:\n  No-Go:           {blockers}\n  Warning:         {warnings}\n  Could Be Better: {suggestions}"
  let expected := String.intercalate "\n\n" (blocks ++ [summary]) ++ footer ++ "\n"
  let stdoutMatches := out.stdout.replace "\r\n" "\n" == expected
  let stderrMatches := if errorText.isEmpty then out.stderr.isEmpty else errorText.all (out.stderr.contains ·)
  unless out.exitCode == code && stdoutMatches && stderrMatches do
    throw <| IO.userError s!"{target}: expected exit {code} and {expected}\ngot {out.exitCode}\n{out.stdout}{out.stderr}"
  IO.println s!"PASS {target}"

def main : IO Unit := do
  let root ← IO.currentDir
  let binary := root / ".lake/build/bin" / (if Platform.isWindows then "l4.exe" else "l4")
  discard <| IO.Process.run { cmd := "lake", args := #["build", "l4"], cwd := root }
  IO.FS.withTempDir fun project => do
    let write := fun (path : FilePath) (source : String) => do
      let target := project / path
      IO.FS.createDirAll target.parent.get!
      IO.FS.writeFile target source
    write "lean-toolchain" (← IO.FS.readFile (root / "lean-toolchain"))
    write "Observe.lean" (include_str "Observe.lean")
    write "spec/Delivery.lean" (include_str "Delivery.lean")
    write "lakefile.lean" r#"import Lake
open Lake DSL
package auditCases
lean_lib Observe
lean_lib Support
lean_lib io
lean_lib Checks where
  srcDir := "client"
"#
    write "io/Driver.lean" r#"module
public def enabled : Bool := true
"#
    write "Support/Adapter.lean" r#"module
import io.Driver
public def ready : Bool := enabled
"#
    discard <| IO.Process.run { cmd := "lake", args := #["build", "+Support.Adapter", "+Observe"], cwd := project }

    check binary project "Observe.lean" 0 [
      "[WARNING] W16 — Process exit status is unobserved\nObserve.lean:9",
      "[WARNING] W16 — Discarded file read or spawned process\nObserve.lean:18",
      "[WARNING] W16 — Discarded Except result\nObserve.lean:65",
      "[WARNING] W16 — Discarded Except result\nObserve.lean:76",
      "[WARNING] W16 — Discarded Except result\nObserve.lean:77",
      "[WARNING] W17 — Check always succeeds\nObserve.lean:82",
      "[WARNING] W19 — Check always takes the failure branch\nObserve.lean:83",
      "[WARNING] W16 — Discarded Except result\nObserve.lean:92",
      "[WARNING] W04 — Caught exception replaced by a constant result; review the fallback\nObserve.lean:97",
      "[WARNING] W04 — Caught exception replaced by a constant result; review the fallback\nObserve.lean:97",
      "[CBB] C03 — Option.none skips a check; review whether absence is acceptable\nObserve.lean:11",
      "[CBB] C05 — Check requires whole JSON object equality; review whether exact shape is intended\nObserve.lean:12",
      "[CBB] C06 — Match on Round distinguishes 2 literal values of Int\nObserve.lean:25",
      "[CBB] C06 — Match on Packet distinguishes 2 literal values of Int\nObserve.lean:27",
      "[CBB] C06 — Boolean flag selects a branch: fast\nObserve.lean:29",
      "[CBB] C06 — Match on String distinguishes 2 literal values of String\nObserve.lean:30",
      "[CBB] C03 — Option.none skips a check; review whether absence is acceptable\nObserve.lean:42",
      "[CBB] C05 — Check requires whole JSON object equality; review whether exact shape is intended\nObserve.lean:43",
      "[CBB] C03 — Except.error skips a check; review whether absence is acceptable\nObserve.lean:52",
      "[CBB] C06 — Match on String distinguishes 2 literal values of String\nObserve.lean:61",
      "[CBB] C05 — Check requires whole JSON object equality; review whether exact shape is intended\nObserve.lean:69",
      "[CBB] C05 — Check requires whole JSON object equality; review whether exact shape is intended\nObserve.lean:69",
      "[CBB] C05 — Check requires whole JSON object equality; review whether exact shape is intended\nObserve.lean:78",
      "[CBB] C05 — Check requires whole JSON object equality; review whether exact shape is intended\nObserve.lean:93"] (0, 10, 14)

    write "client/Checks/Rejection.lean" r##"import Observe
import Lean

def expectRejection (request : IO Bool) : IO Unit := do
  try
    let accepted ← request
    let _verdict := Spec.requireThat "request rejected" (!accepted)
    let failure := IO.userError "request unexpectedly succeeded"
    throw failure
  catch _ => pure ()

example : True := by
  run_tac unless (← Lean.getMainModule) == `Checks.Rejection do throwError "incorrect main module"
  trivial

def fallback (act : IO Bool) : IO Bool := do
  try
    let _ ← act
    throw (IO.userError "rejected")
  catch _ => pure false

def propagate (act : IO Bool) : IO Bool := do
  try act catch err => throw err

@[extern "audit_native_flag"]
opaque nativeFlag : Bool → Bool
def runFlag (b : Bool) : Bool := b
def modelFlag (b : Bool) : Bool := b
attribute [implemented_by runFlag] modelFlag

open Lean
/-- Documentation
    /- nested block -/
-/
def rejectionMarker := r#"-- /- literal"# ++ "--"
-- marker /- line comment
unsafe def unchecked (n : Nat) := n
theorem unfinished : True := by sorry
axiom assumption : True
partial def walk (n : Nat) : Nat := walk n
def trivialGuard := Spec.requireThat "ready" true
def rawCheck (j : Json) (e : IO.Error) : Bool := Id.run do
  dbg_trace "checking"
  return (j.getObjValD "state").compress.contains "done" || e.toString.contains "missing"

def Spec.untilSome (_ : String) (observe : IO (Option α)) : IO α := do
  for _ in [:3] do
    if let some value ← observe then return value
  throw (IO.userError "no observation")
def poll (r : Except String Bool) := Spec.untilSome "ready" do
  match r with
  | .ok value => return some value
  | .error _ => return none
"##
    check binary project "client/Checks/Rejection.lean" 1 [
      "[NO-GO] N07 — Discarded Spec.requireThat verdict\nclient/Checks/Rejection.lean:7",
      "[NO-GO] N09 — Catch suppresses the final throw in its own try block\nclient/Checks/Rejection.lean:10",
      "[NO-GO] N01 — Comment\nclient/Checks/Rejection.lean:32",
      "[NO-GO] N01 — Comment\nclient/Checks/Rejection.lean:33",
      "[NO-GO] N01 — Comment\nclient/Checks/Rejection.lean:36",
      "[NO-GO] N03 — Unsafe declaration\nclient/Checks/Rejection.lean:37",
      "[NO-GO] N05 — Depends on sorryAx\nclient/Checks/Rejection.lean:38",
      "[NO-GO] N08 — Spec.requireThat always succeeds\nclient/Checks/Rejection.lean:41",
      "[WARNING] W04 — Caught exception replaced by a constant result; review the fallback\nclient/Checks/Rejection.lean:20",
      "[WARNING] W21 — Runtime implementation uses extern; review the implementation boundary\nclient/Checks/Rejection.lean:26",
      "[WARNING] W21 — Runtime implementation uses implemented_by; review the implementation boundary\nclient/Checks/Rejection.lean:28",
      "[WARNING] W11 — Depends on axiom assumption\nclient/Checks/Rejection.lean:39",
      "[WARNING] W10 — Partial recursive definition\nclient/Checks/Rejection.lean:40",
      "[WARNING] W12 — Debug trace\nclient/Checks/Rejection.lean:43",
      "[WARNING] W02 — Error information replaced by a default\nclient/Checks/Rejection.lean:44",
      "[WARNING] W03 — Substring search over serialized JSON\nclient/Checks/Rejection.lean:44",
      "[WARNING] W13 — Substring search over a formatted IO error\nclient/Checks/Rejection.lean:44",
      "[WARNING] W20 — Polling callback retries on any Except error\nclient/Checks/Rejection.lean:50"] (8, 10, 0)

    check binary project "spec/Delivery.lean" 1 [
      "[NO-GO] N06 — Unprotected domain type\nspec/Delivery.lean:13\n  - receipt parameter batch in Array field Message.mk.state field Delivery.sent.round via Round uses raw Int",
      "[NO-GO] N06 — Unprotected domain type\nspec/Delivery.lean:21\n  - receive parameter _payload field Payload.nest.item field Payload.raw.value uses raw Nat",
      "[NO-GO] N06 — Unprotected domain type\nspec/Delivery.lean:26\n  - decodeLabel parameter text in Except error uses raw String\n  - decodeLabel parameter text in Except success uses raw String",
      "[NO-GO] N04 — Partial operation: GetElem?.getElem! at \"xs[0]!\"\nspec/Delivery.lean:29",
      "[NO-GO] N04 — Partial operation: List.head!\nspec/Delivery.lean:29",
      "[NO-GO] N06 — Unprotected domain type\nspec/Delivery.lean:39\n  - openBox parameter #1 field Box.mk.payload uses raw Nat"] (7, 0, 0)

    write "pure/Decision.lean" r#"module
import Support.Adapter

public def decision : IO Bool := pure ready
"#
    check binary project "pure/Decision.lean" 1 [
      "[NO-GO] I02 — Forbidden module dependency: Support.Adapter → io.Driver\npure/Decision.lean:2",
      "[NO-GO] I01 — Declaration type or body references an IO effect\npure/Decision.lean:4"] (2, 0, 0)

    write "scan/spec/Growing.lean" r#"inductive Chain : Nat → Type where
  | stop (n : Nat) : Chain n
  | next (n : Nat) (tail : Chain (Nat.succ n)) : Chain n

def check (_ : Chain 0) : IO Unit := pure ()
"#
    write "scan/spec/response.json" "{}"
    write "scan/spec/Broken.lean" "def broken : Nat := true\n"
    write "scan/spec/Boot.lean" "def waitForBoot := IO.sleep 10\ndef boot : IO Unit := waitForBoot\n"
    check binary project "scan" 2 [
      "[NO-GO] N02 — Manual timer: IO.sleep\nscan/spec/Boot.lean:1",
      "[NO-GO] N02 — Manual timer: IO.sleep\nscan/spec/Boot.lean:2",
      "[WARNING] B03 — Non-Lean file under spec/\nscan/spec/response.json"] (2, 1, 0)
      "\nAudit incomplete | Lean files: 3 | Files with No-Go: 1 | Analysis errors: 2"
      ["Broken.lean", "Type mismatch", "Growing.lean", "N06 could not finish inspecting Chain"]
