import Support.Assertions
import Lean

def expectRejection (request : IO Bool) : IO Unit := do
  try
    let accepted ← request
    let _verdict := Spec.requireThat "request rejected" (!accepted)
    let failure := IO.userError "request unexpectedly succeeded"
    throw failure
  catch _ => pure ()

example : True := by
  run_tac unless (← Lean.getMainModule) == `Checks.Rejection do throwError "incorrect main module"
  trivial
