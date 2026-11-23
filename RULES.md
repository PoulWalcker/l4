# Lint4 rule reference

Lint4 reports 26 rules across three severity levels. On a completed audit, a **No-Go** finding produces exit code `1`. **Warning** and **Could Be Better** findings alone leave the exit code at `0`. An analysis error produces exit code `2`.

The Sapiens4 column links to one matching source location per rule. A dash means the verifier reported no match for that rule in this scan. The scan covered 22 Lean files under `spec/` using the default settings and completed with zero analysis errors. Lint4 skips `lakefile.lean`. [Sapiens4 source snapshot](https://github.com/aleski-green/sapiens4/tree/7ae482545bfe4454168d7af48a94e4063cc8188e/spec) · [Lint4 implementation](./Lint4.lean)

## No-Go

| Rule | What it checks | Example that triggers it | Sapiens4 |
| --- | --- | --- | --- |
| **N02** Manual timer or wait | Flags references to `IO.sleep`, `Std.Async.sleep`, and `Std.Async.Selector.sleep`, including simple wrappers. | `IO.sleep pollMs` | [io/Host.lean#L22](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Host.lean#L22) |
| **N03** Unsafe operation | Looks for the words `unsafe`, `unsafeCoerce`, `unsafePerformIO`, `unsafeCast`, or `unsafeRefEq` in source code. | `unsafe def castValue (a : α) : β := unsafeCast a` | — |
| **N04** Partial operation | Flags `xs[i]!`, `panic!`, and functions whose final name is `head!`, `getLast!`, `get!`, `setObjVal!`, or `panic!`. A user-defined function with the same name can also trigger it. | `lines.getLast!.toNat?` | [io/Host.lean#L72](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Host.lean#L72) |
| **N05** Unproven placeholder | Detects `sorryAx` in a term or among a declaration’s transitive axiom dependencies. This covers `sorry`, `admit`, and proofs that rely on an unfinished theorem. | `theorem unfinished : False := by sorry` | — |
| **I01** IO in a pure module | Checks the types and bodies of declarations in selected files for references to `IO`, `EIO`, or `BaseIO`, including references through `abbrev`. The default path is `pure/`. | `def now : IO Nat := IO.monoMsNow` in `pure/Clock.lean` | — |
| **I02** Forbidden import | Checks direct imports against path-specific module restrictions. By default, files under `pure/` may not import `io`, `jobs`, or their submodules. | `import io.Host` in `pure/Model.lean` | — |

## Warning

| Rule | What it checks | Example that triggers it | Sapiens4 |
| --- | --- | --- | --- |
| **N01** Comment | Comments are prohibited. Lint4 warns on line comments, block comments, declaration documentation, and module documentation. | `-- Explain the fixture setup` | [io/Desktop.lean#L133](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Desktop.lean#L133) |
| **W01** String-typed error | Looks for `Except String` in the source. The error is carried as free-form text. | `abbrev Verdict := Except String Unit` | [pure/Observations.lean#L6](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/pure/Observations.lean#L6) |
| **W02** Silent default or fallback | Flags patterns such as `getObjValD`, `.getD`, and `.toOption.getD`. Also follows a local `.toOption` binding used later with `.getD`. | `(stringField control "description").toOption.getD ""` | [io/Desktop.lean#L64](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Desktop.lean#L64) |
| **W03** Text search over serialized JSON | Looks for `.compress.contains`, which searches the serialized JSON text for a substring. | `before.compress.contains marker` | [jobs/system/Access.lean#L12](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/jobs/system/Access.lean#L12) |
| **W04** Discarded exception | Flags a `catch` handler whose body is `pure ()` or `return ()` on the same or next line. | `catch _ => pure ()` | [io/Host.lean#L61](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Host.lean#L61) |
| **W06** JSON on both sides of an API | Checks definition signatures and function-type abbreviations for `Lean.Json` in both an input and the result. Container and effect types count. | `abbrev CryptoWindow := Json → IO Json` | [io/CryptoWindow.lean#L6](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/CryptoWindow.lean#L6) |
| **W09** Clock-based wait limit | Flags an async race with a timer on one side, or a clock-derived comparison inside a loop where one branch exits or throws. | `if (← IO.monoMsNow) ≥ deadline then throw err` inside `repeat` | [io/Host.lean#L21](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Host.lean#L21) |
| **W10** Partial definition | Looks for a definition declared `partial`. | `partial def spin (n : Nat) : Nat := spin n` | — |
| **W11** Dependency on a nonstandard axiom | Follows axiom dependencies. Axioms from `Init`, `Lean`, `Std`, and `Lake` are exempt. N05 handles `sorryAx`. | `axiom assumed : False` followed by `theorem claim : False := assumed` | — |
| **W12** Debug trace | Looks for `dbg_trace` in source code. | `dbg_trace "entered retry branch"` | — |
| **W13** Text search over a formatted value | Looks for `.toString.contains` or a `.toString` result saved in a local variable and later searched with `.contains`. | `let message := error.toString` followed by `message.contains "0x80040201"` | [io/Desktop.lean#L48](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Desktop.lean#L48) |
| **W16** Discarded IO result | Flags `discard` or `let _ ←` for selected IO actions, including file reads, process spawning, process-pipe operations, and actions returning `IO.Process.Output` or `Except`. | `discard child.stdout.getLine` | [io/Relay.lean#L24](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Relay.lean#L24) |
| **I03** Direct JSON file read | Flags a definition containing both `IO.FS.readFile` or `readBinFile` and `Json.parse`. The check uses their presence in the same definition. | `Json.parse (← IO.FS.readFile scriptPath)` | [io/Provider.lean#L22](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Provider.lean#L22) |
| **I04** Direct JSON file write | Flags a definition containing a file write and a JSON marker such as `.compress`, `toJson`, `setObjVal`, `Json.parse`, or `Json.mkObj`. The write and marker may occur on different lines. | `IO.FS.writeFile file previous` after constructing `previous` with `.compress` | [jobs/system/Recovery.lean#L19](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/jobs/system/Recovery.lean#L19) |
| **B03** Non-Lean source encountered | Reports a `.purs`, `.hs`, `.js`, or `.ts` file encountered during a Lean source scan. This finding describes audit coverage. | `BrowserBuild.hs` in the scanned directory | [BrowserBuild.hs](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/BrowserBuild.hs) |

## Could Be Better

| Rule | What it checks | Example that triggers it | Sapiens4 |
| --- | --- | --- | --- |
| **W05** Multiple string arguments | Flags a definition with two or more named `String` arguments in its signature. | `(url method path : String)` | [io/Host.lean#L64](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/io/Host.lean#L64) |
| **W07** Multiple string fields | Flags a structure with at least three field lines containing `: String`. | `Mailbox` declares `relay`, `path`, `deviceToken`, and `hostToken` as `String`. | [jobs/founder/DeviceConsent.lean#L107](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/jobs/founder/DeviceConsent.lean#L107) |
| **W08** Multiple Boolean fields | Flags a structure with at least three field lines containing `: Bool`. | `LocalWrite` declares `localHost`, `localIntent`, and `jsonBody` as `Bool`. | [pure/Privacy.lean#L33](https://github.com/aleski-green/sapiens4/blob/7ae482545bfe4454168d7af48a94e4063cc8188e/spec/pure/Privacy.lean#L33) |
| **C01** Long source line | Flags a raw source line longer than 160 characters. Whitespace counts. | A `def` signature occupying 161 characters on one line. | — |
| **C02** Long definition | Flags a `def` spanning more than 60 lines up to the next recognized declaration boundary or end of file. Blank lines count. | A `def` spanning 61 lines before the next declaration. | — |
