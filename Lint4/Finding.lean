namespace Lint4

inductive Severity where
  | noGo | warning | couldBeBetter
  deriving BEq

instance : ToString Severity where
  toString
    | .noGo => "No-Go"
    | .warning => "Warning"
    | .couldBeBetter => "Could Be Better"

inductive Rule where
  | comment | manualTimer | unsafeCode | partialOperation | unfinishedProof
  | unprotectedSignature | discardedVerdict | vacuousAssertion | caughtFailure | effectInPureModule | forbiddenDependency
  | errorFallback | serializedJsonSearch | emptyHandler | partialRecursion | axiomDependency | debugTrace
  | formattedErrorSearch | lostResult | constantSuccess | constantFailure | unconditionalRetry
  | nonLeanFile | skippedAssertion | wholeJsonEquality
  deriving BEq

private def Rule.metadata : Rule → String × Severity
  | .comment => ("N01", .noGo)
  | .manualTimer => ("N02", .noGo)
  | .unsafeCode => ("N03", .noGo)
  | .partialOperation => ("N04", .noGo)
  | .unfinishedProof => ("N05", .noGo)
  | .unprotectedSignature => ("N06", .noGo)
  | .discardedVerdict => ("N07", .noGo)
  | .vacuousAssertion => ("N08", .noGo)
  | .caughtFailure => ("N09", .noGo)
  | .effectInPureModule => ("I01", .noGo)
  | .forbiddenDependency => ("I02", .noGo)
  | .errorFallback => ("W02", .warning)
  | .serializedJsonSearch => ("W03", .warning)
  | .emptyHandler => ("W04", .warning)
  | .partialRecursion => ("W10", .warning)
  | .axiomDependency => ("W11", .warning)
  | .debugTrace => ("W12", .warning)
  | .formattedErrorSearch => ("W13", .warning)
  | .lostResult => ("W16", .warning)
  | .constantSuccess => ("W17", .warning)
  | .constantFailure => ("W19", .warning)
  | .unconditionalRetry => ("W20", .warning)
  | .nonLeanFile => ("B03", .warning)
  | .skippedAssertion => ("C03", .couldBeBetter)
  | .wholeJsonEquality => ("C05", .couldBeBetter)

def Rule.code (rule : Rule) : String := rule.metadata.1
def Rule.severity (rule : Rule) : Severity := rule.metadata.2

structure Finding where
  line : Nat
  rule : Rule
  detail : String
  deriving BEq

end Lint4
