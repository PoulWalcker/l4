def message := IO.userError "expected"

namespace IO
def normalize (n : Nat) := n + 1
end IO

def expectedCount := IO.normalize 5
example : IO.Error := IO.userError "data"
