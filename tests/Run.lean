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
      "[CBB] C03 — Option.none skips \"ready\"\nObserve.lean:11",
      "[CBB] C05 — Assertion compares an entire JSON object for equality\nObserve.lean:12"] (0, 2, 2)

    write "client/Checks/Rejection.lean" r#"import Observe
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
"#
    check binary project "client/Checks/Rejection.lean" 1 [
      "[NO-GO] N07 — Discarded Spec.requireThat verdict\nclient/Checks/Rejection.lean:7",
      "[NO-GO] N09 — Catch suppresses the final throw in its own try block\nclient/Checks/Rejection.lean:10"] (2, 0, 0)

    check binary project "spec/Delivery.lean" 1 [
      "[NO-GO] N06 — Unprotected domain type: receipt parameter batch in Array field Message.mk.state field Delivery.sent.round via Round uses raw Int\nspec/Delivery.lean:13",
      "[NO-GO] N06 — Unprotected domain type: receive parameter _payload field Payload.nest.item field Payload.raw.value uses raw Nat\nspec/Delivery.lean:21",
      "[NO-GO] N06 — Unprotected domain type: decodeLabel parameter text in Except error uses raw String\nspec/Delivery.lean:26",
      "[NO-GO] N06 — Unprotected domain type: decodeLabel parameter text in Except success uses raw String\nspec/Delivery.lean:26",
      "[NO-GO] N04 — Partial operation: GetElem?.getElem! at \"xs[0]!\"\nspec/Delivery.lean:29",
      "[NO-GO] N04 — Partial operation: List.head!\nspec/Delivery.lean:29"] (6, 0, 0)

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
