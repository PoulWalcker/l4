import Lean

-- IO.sleep and sorry also appear in human-readable test descriptions.
def description := "panic! unsafe def catch _ => pure ()"

namespace Domain
def head! (n : Nat) := n + 1
end Domain

def total := Domain.head! 5
def lookup (xs : List Nat) := xs.head?
def defaultOption (x : Option Nat) := x.getD 0
def textContract (s : String) := s.contains "ready"
def checkEvent (j : Lean.Json) := j == .str "ready"
def readFixture (path : System.FilePath) := IO.FS.readFile path
def propagate (task : IO Unit) : IO Unit := do
  try task catch e => throw e

def compareObserved (observed expected : Nat) : IO Unit :=
  if observed == expected then pure () else throw (IO.userError "changed")

def handleAndReport (task : IO Unit) : IO Unit := do
  try task catch e => IO.println e.toString

structure Sample where
  reading : Nat

instance : BEq Sample where
  beq _ _ := false

def compareSample (sample : Sample) : IO Unit :=
  if sample == sample then pure () else throw (IO.userError "changed")

def searchMessage (s : String) (j : Lean.Json) := s.contains j.compress
def knownValue := (Except.ok 2 : Except Unit Nat).toOption.getD 0

def stdoutOnSuccess (args : IO.Process.SpawnArgs) : IO String := do
  let out ← IO.Process.output args
  if out.exitCode == 0 then return out.stdout
  throw (IO.userError out.stderr)

def expectFailure (task : IO Unit) : IO Unit := do
  try task catch _ => return ()
  throw (IO.userError "expected failure")
