import Lint4.Finding
import Lint4.Frontend

namespace Lint4.SourceChecks

open Lean

private def blockComments (ctx : Parser.InputContext) (start stop : String.Pos.Raw) : Array Nat := Id.run do
  let mut pos := start
  let mut lines := #[]
  while pos < stop do
    let next := ctx.next pos
    if ctx.get pos == '/' && ctx.get next == '-' then
      lines := lines.push (ctx.fileMap.toPosition pos).line
      pos := ctx.next next
    else if ctx.get pos == '-' && ctx.get next == '/' then
      pos := ctx.next next
    else
      pos := next
  return lines

private def triviaComments (ctx : Parser.InputContext) (env : Environment)
    (part : Substring.Raw) : Array Nat := Id.run do
  let mut lines := #[]
  let mut pos := part.startPos
  while pos < part.stopPos do
    if (ctx.get pos).isWhitespace then
      pos := ctx.next pos
    else
      let next := ctx.next pos
      let parser? :=
        if ctx.get pos == '-' && ctx.get next == '-' then
          some (Parser.takeUntilFn (· == '\n'))
        else if ctx.get pos == '/' && ctx.get next == '-' then
          some (Parser.finishCommentBlock (pushMissingOnError := false) 1)
        else none
      let some parser := parser? | break
      let start := pos
      pos := (parser.run ctx { env, options := {} } (Parser.getTokenTable env)
        { pos := ctx.next next, cache := Parser.initCacheForInput ctx.inputString }).pos
      if ctx.get start == '/' then
        lines := lines ++ blockComments ctx start pos
      else
        lines := lines.push (ctx.fileMap.toPosition start).line
  return lines

private partial def commentLines (ctx : Parser.InputContext) (env : Environment)
    (stx : Syntax) : Array Nat := Id.run do
  let mut lines := #[]
  if [``Parser.Command.docComment, ``Parser.Command.moduleDoc].contains stx.getKind then
    if let some range := stx.getRange? then
      lines := lines ++ blockComments ctx range.start range.stop
  if let some (.original leading _ trailing _) := stx.getInfo? then
    for part in #[leading, trailing] do
      lines := lines ++ triviaComments ctx env part
  return lines ++ stx.getArgs.flatMap (commentLines ctx env)

def check (file : ElaboratedFile) : Array Finding :=
  let lines := (#[file.header] ++ file.commands).flatMap (commentLines file.input file.env)
  lines.map fun line => ⟨line, .comment, "Comment"⟩

end Lint4.SourceChecks
