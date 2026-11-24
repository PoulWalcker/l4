import Lean

open System

private def check (binary project : FilePath) (target : String) (code : UInt32)
    (expected : List String) (errorText : List String := []) : IO Unit := do
  let out ← IO.Process.output { cmd := binary.toString, args := #[target], cwd := project }
  let lines := out.stdout.trimAscii.toString.splitOn "\n"
  let stdoutMatches := lines.length == expected.length &&
    (lines.zip expected).all fun (line, suffix) => line.endsWith suffix
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
      "Observe.lean:9: [Warning] Process exit status is unobserved [W16]",
      "Observe.lean:11: [Could Be Better] Option.none skips \"ready\" [C03]",
      "Observe.lean:12: [Could Be Better] Assertion compares an entire JSON object for equality [C05]",
      "Observe.lean:18: [Warning] Discarded file read or spawned process [W16]"]

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
      "Rejection.lean:7: [No-Go] Discarded Spec.requireThat verdict [N07]",
      "Rejection.lean:10: [No-Go] Catch suppresses the final throw in its own try block [N09]"]

    check binary project "spec/Delivery.lean" 1 [
      "Delivery.lean:13: [No-Go] Unprotected domain type: receipt parameter batch in Array field Message.mk.state field Delivery.sent.round via Round uses raw Int [N06]",
      "Delivery.lean:21: [No-Go] Unprotected domain type: receive parameter _payload field Payload.nest.item field Payload.raw.value uses raw Nat [N06]",
      "Delivery.lean:26: [No-Go] Unprotected domain type: decodeLabel parameter text in Except error uses raw String [N06]",
      "Delivery.lean:26: [No-Go] Unprotected domain type: decodeLabel parameter text in Except success uses raw String [N06]",
      "Delivery.lean:29: [No-Go] Partial operation: GetElem?.getElem! at \"xs[0]!\" [N04]",
      "Delivery.lean:29: [No-Go] Partial operation: List.head! [N04]"]

    write "pure/Decision.lean" r#"module
import Support.Adapter

public def decision : IO Bool := pure ready
"#
    check binary project "pure/Decision.lean" 1 [
      "Decision.lean:2: [No-Go] Forbidden module dependency: Support.Adapter → io.Driver [I02]",
      "Decision.lean:4: [No-Go] Declaration type or body references an IO effect [I01]"]

    write "scan/spec/Growing.lean" r#"inductive Chain : Nat → Type where
  | stop (n : Nat) : Chain n
  | next (n : Nat) (tail : Chain (Nat.succ n)) : Chain n

def check (_ : Chain 0) : IO Unit := pure ()
"#
    write "scan/spec/response.json" "{}"
    write "scan/spec/Broken.lean" "def broken : Nat := true\n"
    write "scan/spec/Boot.lean" "def waitForBoot := IO.sleep 10\ndef boot : IO Unit := waitForBoot\n"
    check binary project "scan" 2 [
      "response.json: [Warning] Non-Lean file under spec/ [B03]",
      "Boot.lean:1: [No-Go] Manual timer: IO.sleep [N02]",
      "Boot.lean:2: [No-Go] Manual timer: IO.sleep [N02]",
      "Audit incomplete | Lean files: 3 | Files with No-Go: 1 | Analysis errors: 2"]
      ["Broken.lean", "Type mismatch", "Growing.lean", "N06 could not finish inspecting Chain"]
