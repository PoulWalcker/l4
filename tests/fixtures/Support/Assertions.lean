namespace Spec

def requireThat (label : String) (condition : Bool) : Except String Unit :=
  unless condition do throw label

end Spec
