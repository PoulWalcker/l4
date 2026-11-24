import Lint4.Finding
import Lint4.ReadLeanModule

namespace Lint4.Comments

open Lean

private def scanComments (ctx : Parser.InputContext) (start stop : String.Pos.Raw) : Array Nat := Id.run do
  let mut lines := #[]
  let mut depth := 0
  let mut pos := start
  while pos < stop do
    let next := ctx.next pos
    let pair := (ctx.get pos, ctx.get next)
    if pair == ('/', '-') then
      lines := lines.push (ctx.fileMap.toPosition pos).line
      depth := depth + 1
      pos := ctx.next next
    else if depth > 0 && pair == ('-', '/') then
      depth := depth - 1
      pos := ctx.next next
    else if depth == 0 && pair == ('-', '-') then
      lines := lines.push (ctx.fileMap.toPosition pos).line
      while pos < stop && ctx.get pos != '\n' do pos := ctx.next pos
    else
      pos := next
  return lines

private partial def commentLines (ctx : Parser.InputContext)
    (stx : Syntax) : Array Nat := Id.run do
  let mut lines := #[]
  if [``Parser.Command.docComment, ``Parser.Command.moduleDoc].contains stx.getKind then
    if let some range := stx.getRange? then
      lines := lines ++ scanComments ctx range.start range.stop
  if let some (.original leading _ trailing _) := stx.getInfo? then
    for part in #[leading, trailing] do
      lines := lines ++ scanComments ctx part.startPos part.stopPos
  return lines ++ stx.getArgs.flatMap (commentLines ctx)

def check (file : ElaboratedFile) : Array Finding :=
  let lines := (#[file.header] ++ file.commands).flatMap (commentLines file.input)
  lines.map fun line => ⟨line, .comment, "Comment"⟩

end Lint4.Comments
