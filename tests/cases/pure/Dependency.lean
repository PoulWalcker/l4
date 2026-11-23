import Init

import io.TestDriver

def now : IO Nat := IO.monoMsNow
abbrev Effect := IO
abbrev NestedEffect := Effect
def readClock : NestedEffect Nat := IO.monoMsNow
example : IO Unit := pure ()
