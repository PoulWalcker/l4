inductive Chain : Nat → Type where
  | stop (n : Nat) : Chain n
  | next (n : Nat) (tail : Chain (Nat.succ n)) : Chain n

def check (_ : Chain 0) : IO Unit := pure ()
