import Support.Assertions

def expectRejection (request : IO Bool) : IO Unit := do
  try
    let accepted ← request
    let _verdict := Spec.requireThat "request rejected" (!accepted)
    let failure := IO.userError "request unexpectedly succeeded"
    throw failure
  catch _ => pure ()
