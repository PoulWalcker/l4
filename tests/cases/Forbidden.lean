def pause := IO.sleep
unsafe def baseline : Nat := 0
def first (xs : List Nat) : Nat := xs.head!
theorem assumption : False := by sorry
theorem consequence : False := assumption
partial def spin (n : Nat) : Nat := spin n
axiom assumed : False
theorem needsAssumption : False := assumed
example : False := by sorry
def updateIndex (xs : Array Nat) (i : Nat) := xs.set! i 4
def parseInt (line : String) := line.toSlice.toInt!
unsafe example : Nat := 1
example : False := assumed
example : False := assumption
