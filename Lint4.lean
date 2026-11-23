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

private def printFinding (path : FilePath) (finding : Finding) : IO Unit := do
  let location := if finding.line == 0 then path.toString else s!"{path}:{finding.line}"
  IO.println s!"{location}: [{finding.rule.severity}] {finding.detail} [{finding.rule.code}]"

private def auditFile (path : FilePath) (policy : AuditPolicy) (mainModule : Name) : IO AuditOutcome := do
  let source ← IO.FS.readFile path
  let findings ← auditSource path source policy mainModule
  for finding in findings do
    printFinding path finding
  return if findings.any (·.rule.severity == .noGo) then .violations else .passed

private def auditorSource : String := by_elab
  return Lean.toExpr (← IO.FS.realPath (← Lean.getFileName)).toString

private def auditInChildProcess (root path : FilePath) : IO AuditOutcome := do
  let app ← IO.appPath
  let launchArgs :=
    if [some "lean", some "lean.exe"].contains app.fileName then #["--run", auditorSource] else #[]
  let status ← (← IO.Process.spawn { cmd := app.toString, args := launchArgs.push path.toString, cwd := root }).wait
  if status > 2 then IO.eprintln s!"{path}: Analysis process exited with code {status}"
  return match status with
    | 0 => .passed
    | 1 => .violations
    | _ => .failed

private def scan (target : FilePath) : IO AuditOutcome := do
  let paths ← target.walkDir fun dir => do
    return !([".git", ".lake", ".build", "node_modules"].any (some · == dir.fileName)) &&
      (← dir.symlinkMetadata).type != .symlink
  let files ← paths.filterM fun path => return !(← path.isDir)
  let files := files.qsort (fun a b => a.toString < b.toString)
  for path in files do
    if path.extension != some "lean" && path.parent.any (·.components.contains "spec") then
      printFinding path ⟨0, .nonLeanFile, "Non-Lean file under spec/"⟩
  let sources := files.filter isLeanSource
  if sources.isEmpty then
    IO.eprintln "No Lean source files found"
    return .failed
  let mut blockers := 0
  let mut failures := 0
  for path in sources do
    match ← auditInChildProcess target path with
    | .passed => pure ()
    | .violations => blockers := blockers + 1
    | .failed => failures := failures + 1
  let (outcome, verdict) := if failures > 0 then (AuditOutcome.failed, "incomplete")
    else if blockers > 0 then (.violations, "blocked") else (.passed, "passed")
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

private def run (args : List String) : IO AuditOutcome := do
  if args.length > 1 then
    IO.eprintln "Usage: l4 [PATH]"
    return .failed
  let path := (← IO.currentDir) / FilePath.mk (args.headD ".")
  if !(← path.pathExists) then
    IO.eprintln s!"Path does not exist: {path}"
    return .failed
  if ← path.isDir then
    return ← scan (← realPathNormalized path)
  unless isLeanSource path do
    IO.eprintln s!"Expected a Lean source file or directory: {path}"
    return .failed
  let packageRoot ← projectRoot? path
  let root ← match packageRoot with
    | some root => pure root
    | none => realPathNormalized (← IO.currentDir)
  let policy ← resolvePolicy path root
  let mainModule ← initializeLean path packageRoot
  auditFile path policy mainModule

def main (args : List String) : IO UInt32 := do
  try
    return (← run args).exitCode
  catch error =>
    IO.eprintln s!"{args.headD "."}: Analysis Error: {error}"
    return 2
