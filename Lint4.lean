import Lint4.Audit

open Lean System Lint4

private def isLeanSource (path : FilePath) : Bool :=
  path.extension == some "lean" && path.fileName != some "lakefile.lean"

private inductive AuditOutcome where
  | passed | violations | failed

private def AuditOutcome.exitCode : AuditOutcome → UInt32
  | .passed => 0
  | .violations => 1
  | .failed => 2

private def printReport (rows : Array (FilePath × Finding)) : IO Unit := do
  let mut summary := "Summary:\n"
  for (level, tag, label) in [(Severity.noGo, "NO-GO", "No-Go:           "),
      (.warning, "WARNING", "Warning:         "), (.couldBeBetter, "CBB", "Could Be Better: ")] do
    let mut count := 0
    let mut signatureAt := none
    for (path, finding) in rows do
      unless finding.rule.severity == level do continue
      let location := if finding.line == 0 then path.toString else s!"{path}:{finding.line}"
      let signature := finding.rule == .unprotectedSignature
      if !signature || signatureAt != some location then
        if count > 0 then IO.println ""
        let title := if signature then "Unprotected domain type" else finding.detail
        IO.println s!"[{tag}] {finding.rule.code} — {title}\n{location}"
      if signature then IO.println s!"  - {finding.detail}"
      signatureAt := if signature then some location else none
      count := count + 1
    if count > 0 then IO.println ""
    summary := summary ++ s!"  {label}{count}\n"
  IO.print summary

private def auditorSource : String := by_elab
  return Lean.toExpr (← IO.FS.realPath (← Lean.getFileName)).toString

private def auditInChildProcess (root path : FilePath) : IO (Array Finding) := do
  let app ← IO.appPath
  let launchArgs :=
    if [some "lean", some "lean.exe"].contains app.fileName then #["--run", auditorSource] else #[]
  let child ← IO.Process.output { cmd := app.toString, args := launchArgs ++ #["--collect-file", path.toString], cwd := root }
  unless child.exitCode == 0 do
    throw <| IO.userError (if child.stderr.isEmpty then s!"Analysis process exited with code {child.exitCode}"
      else child.stderr.trimAscii.toString)
  (← IO.getStderr).putStr child.stderr
  IO.ofExcept (Json.parse child.stdout >>= fromJson?)

private def scan (target displayRoot : FilePath) : IO AuditOutcome := do
  let paths ← target.walkDir fun dir => do
    return !([".git", ".lake", ".build", "node_modules"].any (some · == dir.fileName)) &&
      (← dir.symlinkMetadata).type != .symlink
  let files ← paths.filterM fun path => return !(← path.isDir)
  let files := files.qsort (fun a b => a.toString < b.toString)
  let displayPath := fun (path : FilePath) =>
    let relative := mkFilePath (path.components.drop target.components.length)
    if displayRoot == "." then relative else displayRoot / relative
  let mut rows : Array (FilePath × Finding) := #[]
  for path in files do
    if path.extension != some "lean" && path.parent.any (·.components.contains "spec") then
      rows := rows.push (displayPath path, ⟨0, .nonLeanFile, "Non-Lean file under spec/"⟩)
  let sources := files.filter isLeanSource
  if sources.isEmpty then
    printReport rows
    IO.eprintln "No Lean source files found"
    return .failed
  let mut blockers := 0
  let mut failures := 0
  for path in sources do
    try
      let findings ← auditInChildProcess target path
      if findings.any (·.rule.severity == .noGo) then blockers := blockers + 1
      rows := rows ++ findings.map (displayPath path, ·)
    catch error =>
      IO.eprintln s!"{displayPath path}: {error}"
      failures := failures + 1
  let (outcome, verdict) := if failures > 0 then (AuditOutcome.failed, "incomplete")
    else if blockers > 0 then (.violations, "blocked") else (.passed, "passed")
  printReport rows
  IO.println s!"Audit {verdict} | Lean files: {sources.size} | Files with No-Go: {blockers} | Analysis errors: {failures}"
  return outcome

private def run (args : List String) : IO AuditOutcome := do
  if let ["--collect-file", file] := args then
    let findings ← auditFile file
    IO.println (toJson findings).compress
    return .passed
  if args.length > 1 then
    IO.eprintln "Usage: l4 [PATH]"
    return .failed
  let target := FilePath.mk (args.headD ".")
  let path := (← IO.currentDir) / target
  if !(← path.pathExists) then
    IO.eprintln s!"Path does not exist: {path}"
    return .failed
  if ← path.isDir then
    return ← scan (← realPathNormalized path) target
  unless isLeanSource path do
    IO.eprintln s!"Expected a Lean source file or directory: {path}"
    return .failed
  let findings ← auditFile path
  printReport (findings.map (target, ·))
  return if findings.any (·.rule.severity == .noGo) then .violations else .passed

def main (args : List String) : IO UInt32 := do
  try
    return (← run args).exitCode
  catch error =>
    let location := if args.head? == some "--collect-file" then "" else s!"{args.headD "."}: "
    IO.eprintln s!"{location}Analysis Error: {error}"
    return 2
