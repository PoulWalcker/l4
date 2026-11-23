namespace Lint4

inductive Severity where
  | noGo | warning
  deriving BEq

instance : ToString Severity where
  toString
    | .noGo => "No-Go"
    | .warning => "Warning"

structure Finding where
  line : Nat
  level : Severity
  rule : String
  detail : String
  deriving BEq

end Lint4
