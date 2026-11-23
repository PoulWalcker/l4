import Lint4.Audit
import Lake.Config.InstallPath

open Lean System Lint4

private def defaultPurePaths : List String := ["pure"]
private def defaultDeniedImports : List (String × String) := [("pure", "io"), ("pure", "jobs")]

private def policyPath (root : FilePath) (relative : String) : IO FilePath := do
  let path := root / relative
  if ← path.pathExists then realPathNormalized path else pure path.normalize

private def projectRoot? (target : FilePath) : IO (Option FilePath) := do
  let mut dir := if ← target.isDir then some target else target.parent
  while let some path := dir do
    if ← ["lakefile.lean", "lakefile.toml"].anyM (fun (name : String) => do
      let marker := path / name
      return (← marker.pathExists) && !(← marker.isDir)) then
      return some path
    dir := path.parent
  return none

private def allowedSourceFile (path : FilePath) : IO Bool := do
  for file in #[path, (← realPathNormalized path)] do
    if file.extension == some "lean" then continue
    unless [some "lean-toolchain", some "lake-manifest.json", some "lakefile.toml"].contains file.fileName do
      return false
    unless (← projectRoot? file) == file.parent do return false
  return true

private def reportUnsupportedFile (path : FilePath) : IO Unit :=
  IO.println s!"{path}:0: No-Go B03 Only Lean sources and root Lake metadata are allowed"

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

private def auditInChildProcess (path : FilePath) : IO AuditOutcome := do
  let app ← IO.appPath
  let launchArgs :=
    if [some "lean", some "lean.exe"].contains app.fileName then #["--run", auditorSource] else #[]
  let status ← (← IO.Process.spawn { cmd := app.toString, args := launchArgs.push path.toString }).wait
  if status > 2 then IO.eprintln s!"{path}: Analysis process exited with code {status}"
  return match status with
    | 0 => .passed
    | 1 => .violations
    | _ => .failed

private def scan (target : FilePath) : IO AuditOutcome := do
  let paths ← target.walkDir fun path =>
    pure <| !path.components.any ([".git", ".lake", ".build", "node_modules"].contains ·)
  let paths ← paths.filterM fun path => return !(← path.isDir)
  let paths := paths.qsort (fun a b => a.toString < b.toString)
  let mut sources : Array FilePath := #[]
  let mut blockers := 0
  for path in paths do
    if ← allowedSourceFile path then
      if path.extension == some "lean" && path.fileName != some "lakefile.lean" then sources := sources.push path
    else
      reportUnsupportedFile path
      blockers := blockers + 1
  if sources.isEmpty && blockers == 0 then
    IO.eprintln "No Lean source files found"
    return .failed
  let mut failures := 0
  for path in sources do
    match ← auditInChildProcess path with
    | .passed => pure ()
    | .violations => blockers := blockers + 1
    | .failed => failures := failures + 1
  IO.println s!"Audited {sources.size} Lean files; {blockers} files with No-Go; {failures} analysis errors"
  return if failures > 0 then .failed else if blockers > 0 then .violations else .passed

private def resolvePolicy (path root : FilePath) : IO AuditPolicy := do
  let selected := fun (selector : FilePath) => selector.components.isPrefixOf path.components
  let purePaths ← defaultPurePaths.mapM (policyPath root)
  let deniedModules ← defaultDeniedImports.filterMapM fun (source, target) => do
    return if selected (← policyPath root source) then some target.toName else none
  return { pureModule := purePaths.any selected, deniedModules }

private def packageSearchPath (lake : Lake.LakeInstall) (root : FilePath) : IO (Option Lean.SearchPath) := do
  let cmd := (← IO.getEnv "LAKE").getD lake.lake.toString
  let env ← IO.Process.output { cmd, args := #["env"], cwd := root }
  if env.exitCode != 0 then
    IO.eprintln env.stderr
    return none
  let some paths := (env.stdout.splitOn "\n").findSome? (·.dropPrefix? "LEAN_PATH=") |
    IO.eprintln "Lake did not provide the package search path"
    return none
  return some (System.SearchPath.parse paths.trimAscii.toString)

private def initializeLean (packageRoot : Option FilePath) : IO Bool := do
  let sysroot ← findSysroot
  let lake := Lake.LakeInstall.ofLean { sysroot }
  let projectPath ← match packageRoot with
    | some root => packageSearchPath lake root
    | none => pure (some [])
  let some projectPath := projectPath | return false
  initSearchPath sysroot projectPath
  if ← lake.sharedLib.pathExists then
    loadDynlib lake.sharedLib
  return true

private def run (args : List String) : IO AuditOutcome := do
  if args.length > 1 then
    IO.eprintln "Usage: l4 [PATH]"
    return .failed
  let path := (← IO.currentDir) / FilePath.mk (args.headD ".")
  if !(← path.pathExists) then
    IO.eprintln s!"Path does not exist: {path}"
    return .failed
  if !(← path.isDir) then
    unless ← allowedSourceFile path do
      reportUnsupportedFile path
      return .violations
    if path.extension != some "lean" then return .passed
  let path ← realPathNormalized path
  if ← path.isDir then
    IO.eprintln "Analysis elaborates Lean: by_elab, macros/tactics and imported initializers may execute; not a sandbox."
    return ← scan path
  let packageRoot ← projectRoot? path
  let root ← match packageRoot with
    | some root => pure root
    | none => realPathNormalized (← IO.currentDir)
  let policy ← resolvePolicy path root
  unless ← initializeLean packageRoot do return .failed
  auditFile path policy

def main (args : List String) : IO UInt32 := do
  try
    return (← run args).exitCode
  catch error =>
    IO.eprintln s!"{args.headD "."}: Analysis Error: {error}"
    return 2
