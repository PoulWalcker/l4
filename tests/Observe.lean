import Lean

open Lean

def Spec.requireThat (label : String) (condition : Bool) : Except String Unit :=
  unless condition do throw label

def observe (cmd : IO.Process.SpawnArgs) : IO Unit := do
  let output ← IO.Process.output cmd
  let _observed := output.exitCode
  match (Json.parse output.stdout).toOption with
  | some reply => IO.ofExcept (Spec.requireThat "ready" (reply == Json.mkObj [("ready", .bool true)]))
  | none => pure ()

abbrev App := IO

def discardRead : App Unit := do
  let _ ← IO.FS.readFile "response"

inductive Phase | idle | active | done
abbrev Round := Int
structure Packet where
  round : Round

def fromRound (round : Round) : Phase := match round with
  | -1 => .idle | 2 => .active | _ => .done
def fromPacket (packet : Packet) : Phase := match packet with
  | ⟨-1⟩ => .idle | ⟨2⟩ => .active | _ => .done
def fromFlag (fast : Bool) : Phase := if fast then .active else .idle
def fromText (s : String) : Phase := match s with
  | "active" => .active | "done" => .done | _ => .idle

def isDone : Phase → Bool
  | .done => true | _ => false
def nextPhase (p : Phase) := if isDone p then Phase.idle else p
def firstPhase (n : Nat) := if n == 0 then Phase.idle else .active

def Check.ensure (condition : Bool) : Except String Unit :=
  if condition then .ok () else .error "check failed"

def inspectReply (reply : Option Json) : Except String Unit :=
  match reply with
  | some actual => Check.ensure (actual == Json.mkObj [("ready", true)])
  | none => .ok ()

def expectDifferent (actual : Json) : IO Unit := do
  if actual == Json.mkObj [] then throw (IO.userError "unexpected object")
  else pure ()

def checkFlags (flags : List (Except String Bool)) : IO Unit := do
  for result in flags do
    if let .ok passed := result then
      unless passed do throw (IO.userError "failed")
      IO.println "passed"

def requireFlag (flag : Option Bool) : IO Unit := do
  match flag with
  | some value => IO.ofExcept (Check.ensure value)
  | none => throw (IO.userError "missing")

def fromWire (s : String) : Phase := match s with
  | "ok" | r#"done"# => .done | _ => .idle

def discardCheck (j : Json) : IO Unit := do
  let _unused := Check.ensure (j == Json.mkObj [])
  pure ()

def twoChecks (j k : Json) : Except String Unit := do
  Check.ensure (j == Json.mkObj []); Check.ensure (k == Json.mkObj [])

set_option match.ignoreUnusedAlts true in
def sameLiteral (s : String) : Phase := match s with
  | "ok" | r#"ok"# => .done | _ => .idle

def droppedVerdicts (j : Json) : IO Unit := do
  let _ ← pure (Check.ensure (j == Json.mkObj []))
  discard (pure (Check.ensure (j == Json.mkObj [])) : IO (Except String Unit))
  IO.ofExcept (Check.ensure (j == Json.mkObj []))

abbrev GuardIO := ExceptT String IO
def guardIO (b : Bool) : GuardIO Unit := if b then pure () else throw "failed"
def passes : GuardIO Unit := guardIO true
def fails : GuardIO Unit := guardIO false

section
local instance : Pure IO where pure _ := throw (IO.userError "failed")
def customGuard (b : Bool) : IO Unit := if b then pure () else throw (IO.userError "failed")
def unknownVerdict : IO Unit := customGuard true
end

def discardAfterCheck (j : Json) : IO Unit := do
  discard (do
    IO.ofExcept (Check.ensure (j == Json.mkObj []))
    pure (.ok ()) : IO (Except String Unit))

def twoFallbacks (act : IO Nat) : IO (Nat × Nat) := do
  let a ← (do try act catch _ => pure 0); let b ← (do try act catch _ => pure 0)
  return (a, b)
