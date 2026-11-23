import Lean
import Support.Assertions

open Lean

def observe (cmd : IO.Process.SpawnArgs) : IO Unit := do
  let output ← IO.Process.output cmd
  let _observed := output.exitCode
  match (Json.parse output.stdout).toOption with
  | some reply => IO.ofExcept (Spec.requireThat "ready" (reply == Json.mkObj [("ready", .bool true)]))
  | none => pure ()

abbrev App := IO

def discardRead : App Unit := do
  let _ ← IO.FS.readFile "response"
