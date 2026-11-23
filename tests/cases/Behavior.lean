import Lean

def silent (r : Except Unit Nat) := r.toOption.getD 0
def substringOracle (j : Lean.Json) := j.compress.contains "ready"

def optionalFailure (task : IO Unit) : IO Unit := do
  try task catch _ => pure ()

def ignored : IO Unit := do
  discard (IO.Process.output {cmd := "tool"})

def vacuous (observed : Nat) : IO Unit :=
  if observed == observed then pure () else throw (IO.userError "changed")

def alwaysFails : IO Unit :=
  if false then pure () else throw (IO.userError "failed")

def traced : Nat :=
  dbg_trace "fixture"
  1

def checkErrorText (e : IO.Error) := e.toString.contains "resource busy"

def stdoutOnly (args : IO.Process.SpawnArgs) : IO String := do
  let out ← IO.Process.output args
  return out.stdout

def assertTrue (b : Bool) : IO Unit :=
  if b then pure () else throw (IO.userError "expected true")

def reflexiveInequality (n : Nat) := assertTrue (n != n)
