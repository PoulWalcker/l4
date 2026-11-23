import Lean

namespace Lint4

structure AuditPolicy where
  pureRoot? : Option System.FilePath := none
  specModule : Bool := false

def forbiddenInPure (moduleName : Lean.Name) : Bool :=
  [`io, `jobs].any (·.isPrefixOf moduleName)

end Lint4
