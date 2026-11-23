# Auditing Sapiens4 tests

Lint4 reports source locations where a Lean test breaks a configured rule or deserves review. Run it on a trusted checkout. Lean elaboration can execute macros, tactics and import initializers. The target project's Lake configuration also runs when resolving imports.

Build the target's Lean dependencies first. From the Lint4 checkout, with the pinned Lean toolchain on PATH, run

```sh
lake -d /path/to/sapiens4/spec build Contracts
lake build l4
.lake/build/bin/l4 /path/to/sapiens4/spec
python3 tests/cli.py
```

An individual Lean file is also a valid target. Exit **0** means the audit completed with no blocking findings, **1** means at least one file broke a blocking rule, and **2** means the audit was incomplete. In a directory scan, analysis errors take precedence over violations. A directory with no Lean source gives 2. Lint4 skips Lake configuration, build directories and linked subdirectories. It rejects early `#exit` and explicit executable command syntax such as `#eval`, including quoted occurrences. Running the scenarios themselves is a separate step in Sapiens4 (`lake -d spec test`).

## Blocking rules

| Rule | Evidence required by Lint4 |
| --- | --- |
| N02 · Manual timer | A reference resolves to `IO.sleep`, `Std.Async.sleep` or `Std.Async.Selector.sleep`, directly or through a forwarding definition. This enforces the project's ban on manual timers, including polling intervals. |
| N03 · Unsafe code | Lean marks the declaration or a referenced constant unsafe, or the source uses an unsafe term. Includes anonymous examples. |
| N04 · Partial operation | Panic syntax, partial indexing such as `xs[i]!`, or a reference to a listed partial API. Examples include `List.head!`, `Option.get!`, `Array.set!` and `String.toInt!`. The finite list of qualified names lives in `partialOperations` in [Terms.lean](Lint4/Rules/Terms.lean). A user-defined `Domain.head!` is accepted. |
| N05 · Unfinished proof | A term contains `sorryAx` or Lean reports it among a declaration's axiom dependencies. This includes `admit`, proofs using an unfinished lemma, and anonymous examples. |
| I01 · Effect in a pure module | A declaration in package-root `pure/` references `IO`, `EIO` or `BaseIO` in its type, body, or the type of a directly used constant. Type abbreviations are followed. A pure function can construct an `IO.Error`. |
| I02 · Forbidden dependency | A file in `pure/` imports `io` or `jobs` (including submodules), or uses a constant or projection from those modules. Import diagnostics point to the import line. |

A blocking finding records a violation of the audit policy. For example, N02 establishes that a timer is referenced. Measuring whether the scenario is flaky requires running it.

## Warnings

| Rule | Why review the location |
| --- | --- |
| W02 · Error replaced by a default | `Except.toOption` followed by `Option.getD`, or `Json.getObjValD`, can turn an unexpected response into a usable value. Ordinary optional defaults are accepted. |
| W03 · Serialized JSON search | `String.contains` searches the result of `Json.compress` or `Json.pretty`. A marker may occur in an unrelated field. A privacy test may intentionally search the entire payload. |
| W04 · Empty exception handler | A catch immediately completes with unit. Inspect whether it neutralizes a test failure. A rethrow, a recovery action, or an early success in a test that expects an exception has different behavior. |
| W10 · Partial recursion | Lean generated a partial recursive implementation. Review how the test terminates. |
| W11 · Axiom dependency | A declaration relies on an axiom beyond `propext`, `Classical.choice` and `Quot.sound`. N05 covers `sorryAx`. |
| W12 · Debug trace | A debug-trace construct or an explicit `dbgTrace` call remains in the test. |
| W13 · Formatted error search | A substring of a formatted `IO.Error` controls behavior. Review whether the error has a stable structured discriminator. |
| W16 · Lost result | The code discards an `Except` or `IO.Process.Output`, leaves a binding of that type unused, or uses only stdout/stderr from a directly bound `IO.Process.output`. A command can print the expected text and still exit unsuccessfully. |
| W17 / W19 · Constant assertion outcome | A recognized unit-success/error guard always selects success (W17) or failure (W19). Includes literal conditions, reflexive equality and inequality, negation and one level of a simple assertion helper such as `requireThat`. Boolean equality needs a `LawfulBEq` instance. |
| B03 · Audit coverage | Directory scans report Haskell, PureScript, JavaScript, TypeScript and HTML files for separate review. A browser bridge can legitimately accompany Lean assertions. |

## Choosing the check

Use literal matching or a regexp for an explicitly specified text format. The CLI regressions use a regexp to read diagnostic lines. Lean imports and command modifiers have parsed source locations. Calls, overloads, local bindings, effects and proof dependencies have identities and types after elaboration. Searching for `sorry`, `sleep`, `get!` or `catch` in raw source would also match strings, comments and unrelated declarations.

Counts of comments, lines, string arguments or Boolean fields, `Except String` and JSON-to-JSON signatures say little about the behavior a test observes. Reading and writing JSON fixtures is part of Sapiens4's migration scenarios. These patterns have no automatic verdict.

During behavioral review, follow one executed scenario from the action to the observation. Check that the runner actually invokes it, that the observation comes from the system under test, and that changing the observed value or status would fail the assertion. W17/W19 catch a subset of constant guards. Coverage of arbitrary helper chains, dynamic branches and the running application requires other evidence.

## Calibration against Sapiens4

At revision `b7059c7889e06aac5dfe23426d553591f991ba97`, the scan covered 22 Lean files. Seven contained blocking findings. Three locations referenced timers and 21 lines used partial operations. The scan also reported 36 warnings, including three notices about files outside Lean coverage. All 22 files completed analysis.

| Location in `spec/` | Review decision |
| --- | --- |
| `io/Host.lean:22` | `untilSome` sleeps between observations. N02 applies even though the poll has a deadline. A clock comparison alone no longer triggers a second warning. |
| `jobs/system/Recovery.lean:18` | Two calls to `setObjVal!` on one line produce one N04. Writing the resulting JSON constructs a previous schema version for the migration test. The write itself warrants no finding. |
| `jobs/system/Access.lean:88` | W03 locates a search across the entire serialized state for a private marker. That breadth is appropriate when disclosure anywhere would violate the contract. |
| `io/Host.lean:61` | W04 locates an empty handler in cleanup. The outer handler rethrows the original host failure. A reviewer can accept suppression of the secondary cleanup error. |
