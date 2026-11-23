import Lint4.Audit
import Lake.Config.InstallPath

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

private def auditFile (path : FilePath) (policy : AuditPolicy) : IO AuditOutcome := do
  let source ← IO.FS.readFile path
  let findings ← auditSource path source policy
  for finding in findings do
    IO.println s!"{path}:{finding.line}: {finding.level} {finding.rule} {finding.detail}"
  return if findings.any (·.level == .noGo) then .violations else .passed

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
    if ["purs", "hs", "js", "ts", "html"].any (some · == path.extension) then
      IO.println s!"{path}:0: Warning B03 Non-Lean source outside audit coverage"
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
  IO.println s!"Audited {sources.size} Lean files; {blockers} files with No-Go; {failures} analysis errors"
  return if failures > 0 then .failed else if blockers > 0 then .violations else .passed

private def resolvePolicy (path root : FilePath) : IO AuditPolicy := do
  let pureDir := root / "pure"
  unless ← pureDir.isDir do return {}
  let prefixPath := (← realPathNormalized pureDir).components
  let parent ← realPathNormalized (path.parent.getD root)
  let target ← realPathNormalized path
  if prefixPath.isPrefixOf parent.components || prefixPath.isPrefixOf target.components then
    return { pureModule := true, deniedModules := [`io, `jobs] }
  return {}

private def packageSearchPath (lake : Lake.LakeInstall) (root : FilePath) : IO Lean.SearchPath := do
  let cmd := (← IO.getEnv "LAKE").getD lake.lake.toString
  let env ← IO.Process.run { cmd, args := #["env"], cwd := root }
  let some paths := (env.splitOn "\n").findSome? (·.dropPrefix? "LEAN_PATH=") |
    throw <| IO.userError "Lake did not provide the package search path"
  return System.SearchPath.parse paths.trimAscii.toString

private def initializeLean (packageRoot : Option FilePath) : IO Unit := do
  let sysroot ← findSysroot
  let paths ← match packageRoot with
    | some root => packageSearchPath (Lake.LakeInstall.ofLean { sysroot }) root
    | none => pure []
  initSearchPath sysroot paths

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
  initializeLean packageRoot
  auditFile path policy

def main (args : List String) : IO UInt32 := do
  try
    return (← run args).exitCode
  catch error =>
    IO.eprintln s!"{args.headD "."}: Analysis Error: {error}"
    return 2
