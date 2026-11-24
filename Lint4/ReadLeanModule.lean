import Lean
import Lake.DSL
import Lake.Load.Workspace

namespace Lint4

open Lean System

structure ElaboratedFile where
  input : Parser.InputContext
  header : Syntax
  commands : Array Syntax
  env : Environment
  infoTrees : PersistentArray Elab.InfoTree

private partial def executesCode (stx : Syntax) : Bool :=
  [``Parser.Command.eval, ``Parser.Command.evalBang, ``Parser.Command.initialize,
    `Lean.runCmd, `Lean.runElab, `Lean.runMeta].contains stx.getKind ||
      stx.getArgs.any executesCode

open Elab.Frontend in
private partial def elaborateCommands : FrontendM Unit := do
  updateCmdPos
  let state ← get
  let input ← getInputContext
  let scope := state.commandState.scopes.head!
  let context := {
    env := state.commandState.env
    options := scope.opts
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls }
  let (cmd, parserState, messages) :=
    Parser.parseCommand input context state.parserState state.commandState.messages
  if cmd.getKind == ``Parser.Command.exit then
    throw <| IO.userError "#exit stops parsing before the end of the module"
  if executesCode cmd then
    let line := (input.fileMap.toPosition (cmd.getPos?.getD state.cmdPos)).line
    throw <| IO.userError s!"{input.fileName}:{line}: executable command is unsupported by static audit"
  modify fun s => { s with commands := s.commands.push cmd }
  setParserState parserState
  elabCommandAtFrontend cmd
  modify fun s =>
    let infoState := s.commandState.infoState.substituteLazy.get
    let trees := state.commandState.infoState.trees.append infoState.trees
    let commandState := { s.commandState with
      messages := messages ++ s.commandState.messages
      infoState := { infoState with trees } }
    { s with commandState }
  unless Parser.isTerminalCommand cmd do elaborateCommands

private def throwOnErrors (messages : MessageLog) (reason : String) : IO Unit := do
  unless messages.hasErrors do return
  for message in messages.toList do
    if message.severity == .error then
      IO.eprintln (← message.toString)
  throw (IO.userError reason)

def elaborateSource (path : FilePath) (source : String) (mainModule : Name) : IO ElaboratedFile := do
  let input := Parser.mkInputContext source path.toString
  let (header, parserState, headerMessages) ← Parser.parseHeader input
  unsafe enableInitializersExecution
  let (importEnv, messages) ← Elab.processHeader header {} headerMessages input (mainModule := mainModule)
  throwOnErrors messages "Unable to load Lean imports"
  let (_, elaboration) ← (elaborateCommands.run { inputCtx := input }).run
    { commandState := Elab.Command.mkState importEnv {} {}
      parserState
      cmdPos := parserState.pos }
  let state := elaboration.commandState
  throwOnErrors state.messages "Lean reported source errors"
  return {
    input
    header := header.raw
    commands := elaboration.commands
    env := state.env
    infoTrees := state.infoState.substituteLazy.get.trees }

def projectRoot? (target : FilePath) : IO (Option FilePath) := do
  let mut dir := if ← target.isDir then some target else target.parent
  while let some path := dir do
    if ← ["lakefile.lean", "lakefile.toml"].anyM (fun (name : String) => do
      let marker := path / name
      return (← marker.pathExists) && !(← marker.isDir)) then
      return some path
    dir := path.parent
  return none

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

def initializeLean (path : FilePath) (packageRoot : Option FilePath) : IO Name := do
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

end Lint4
