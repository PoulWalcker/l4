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
    let fixtures := root / "tests/fixtures"
    for source in ← fixtures.walkDir (fun dir => pure (dir.fileName != some ".lake")) do
      unless source.extension == some "lean" do continue
      let dest := project / System.mkFilePath (source.components.drop fixtures.components.length)
      IO.FS.createDirAll dest.parent.get!
      IO.FS.writeFile dest (← IO.FS.readFile source)
    IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (root / "lean-toolchain"))
    discard <| IO.Process.run { cmd := "lake", args := #["build", "+Support.Adapter", "+Support.Assertions"], cwd := project }

    check binary project "Observe.lean" 0 [
      "Observe.lean:7: Warning W16 Process exit status is unobserved",
      "Observe.lean:9: Could Be Better C03 Option.none skips \"ready\"",
      "Observe.lean:10: Could Be Better C05 Assertion compares an entire JSON object for equality"]
    check binary project "Rejection.lean" 1 [
      "Rejection.lean:6: No-Go N07 Discarded Spec.requireThat verdict",
      "Rejection.lean:9: No-Go N09 Catch suppresses the final throw in its own try block"]
    check binary project "spec/Delivery.lean" 1 [
      "Delivery.lean:13: No-Go N06 receipt parameter batch in Array field Message.mk.state field Delivery.sent.round via Round: raw Int"]
    check binary project "pure/Decision.lean" 1 [
      "Decision.lean:2: No-Go I02 Forbidden module dependency: Support.Adapter → io.Driver",
      "Decision.lean:4: No-Go I01 Declaration type or body references an IO effect"]

    let scan := project / "scan/spec"
    IO.FS.createDirAll scan
    IO.FS.writeFile (scan / "response.json") "{}"
    IO.FS.writeFile (scan / "Broken.lean") "def broken : Nat := true\n"
    IO.FS.writeFile (scan / "Boot.lean") "def waitForBoot := IO.sleep 10\ndef boot : IO Unit := waitForBoot\n"
    check binary project "scan" 2 [
      "response.json:0: Warning B03 Non-Lean file under spec/",
      "Boot.lean:1: No-Go N02 Manual timer: IO.sleep",
      "Boot.lean:2: No-Go N02 Manual timer: IO.sleep",
      "Audited 2 Lean files; 1 files with No-Go; 1 analysis errors"] ["Broken.lean", "Type mismatch"]
