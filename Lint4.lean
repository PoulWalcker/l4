import Lint4.Audit
import Lake.DSL
import Lake.Load.Workspace

open Lean System Lint4

private def projectRoot? (target : FilePath) : IO (Option FilePath) := do
  let mut dir := if ← target.isDir then some target else target.parent
  while let some path := dir do
    if ← ["lakefile.lean", "lakefile.toml"].anyM (fun (name : String) => do
      let marker := path / name
      return (← marker.pathExists) && !(← marker.isDir)) then
      return some path
    dir := path.parent
  return none

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
    for (path, finding) in rows do
      unless finding.rule.severity == level do continue
      let location := if finding.line == 0 then path.toString else s!"{path}:{finding.line}"
      IO.println s!"[{tag}] {finding.rule.code} — {finding.detail}\n{location}\n"
      count := count + 1
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

private def resolvePolicy (path root : FilePath) : IO AuditPolicy := do
  let parent ← realPathNormalized (path.parent.getD root)
  let target ← realPathNormalized path
  let policy : AuditPolicy := { specModule := parent.components.contains "spec" || target.components.contains "spec" }
  let pureDir := root / "pure"
  unless ← pureDir.isDir do return policy
  let prefixPath := (← realPathNormalized pureDir).components
  if prefixPath.isPrefixOf parent.components || prefixPath.isPrefixOf target.components then
    return { policy with pureRoot? := some (← realPathNormalized root) }
  return policy

private def loadWorkspace (root : FilePath) (lean : Lake.LeanInstall) : IO Lake.Workspace := do
  let cwd ← IO.currentDir
  try
    IO.Process.setCurrentDir root
    unsafe enableInitializersExecution
    let env ← (Lake.Env.compute (.ofLean lean) lean (← Lake.findElanInstall?)).toIO IO.userError
    let (ws?, log) ← (Lake.loadWorkspace { lakeEnv := env, wsDir := root }).captureLog
    let some ws := ws? | throw <| IO.userError s!"Unable to load Lake workspace at {root}\n{log}"
    return ws
  finally
    IO.Process.setCurrentDir cwd

private def workspaceSearchPath (ws : Lake.Workspace) : IO Lean.SearchPath := do
  let some cmd ← IO.getEnv "LAKE" | return ws.augmentedLeanPath
  if cmd == ws.lakeEnv.lake.lake.toString then return ws.augmentedLeanPath
  let env ← IO.Process.run {cmd, args := #["env"], cwd := ws.root.dir}
  let some paths := (env.splitOn "\n").findSome? (·.dropPrefix? "LEAN_PATH=") |
    throw <| IO.userError "Lake did not provide the package search path"
  return System.SearchPath.parse paths.trimAscii.toString

private def initializeLean (path : FilePath) (packageRoot : Option FilePath) : IO Name := do
  let sysroot ← findSysroot
  let path ← realPathNormalized path
  let mut roots := [← IO.currentDir]
  if let some root := packageRoot then
    let ws ← loadWorkspace (← realPathNormalized root) { sysroot }
    initSearchPath sysroot (← workspaceSearchPath ws)
    if let some mod := ws.findModuleBySrc? path then return mod.name
    roots := [ws.root.srcDir, root]
  else
    initSearchPath sysroot
  if let some name ← searchModuleNameOfFileName path roots then return name
  moduleNameOfFileName path path.parent

private def collectFile (path : FilePath) : IO (Array Finding) := do
  IO.withStdout (← IO.getStderr) do
    let packageRoot ← projectRoot? path
    let root ← match packageRoot with
      | some root => pure root
      | none => realPathNormalized (← IO.currentDir)
    let policy ← resolvePolicy path root
    let mainModule ← initializeLean path packageRoot
    auditSource path (← IO.FS.readFile path) policy mainModule

private def run (args : List String) : IO AuditOutcome := do
  if let ["--collect-file", file] := args then
    let findings ← collectFile file
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
  let findings ← collectFile path
  printReport (findings.map (target, ·))
  return if findings.any (·.rule.severity == .noGo) then .violations else .passed

def main (args : List String) : IO UInt32 := do
  try
    return (← run args).exitCode
  catch error =>
    let location := if args.head? == some "--collect-file" then "" else s!"{args.headD "."}: "
    IO.eprintln s!"{location}Analysis Error: {error}"
    return 2
