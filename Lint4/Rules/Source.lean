import Lint4.Finding
import Lint4.Frontend

namespace Lint4.SourceChecks

open Lean

private def checkLineLengths (source : String) : Array Finding :=
  (source.splitOn "\n").toArray.zipIdx.filterMap fun (line, index) =>
    if line.length > 160 then
      some ⟨index + 1, .couldBeBetter, "C01", "Long source line"⟩
    else none

private partial def syntaxNodes (kind : SyntaxNodeKind) (stx : Syntax) : Array Syntax :=
  if stx.getKind == kind then #[stx] else stx.getArgs.flatMap (syntaxNodes kind)

private def checkDefinition (fileMap : FileMap) (stx : Syntax) : Array Finding := Id.run do
  let some pos := stx.getPos? | return #[]
  unless stx.getKind == ``Parser.Command.declaration do return #[]
  let decl := stx[1]
  unless decl.getKind == ``Parser.Command.definition do return #[]
  let line := (fileMap.toPosition (decl.getPos?.getD pos)).line
  let endLine := (fileMap.toPosition (decl.getTailPos?.getD pos)).line
  let mut findings := #[]
  if !(syntaxNodes ``Parser.Command.partial stx[0]).isEmpty then
    findings := findings.push ⟨line, .warning, "W10", "Partial definition"⟩
  if endLine - line + 1 > 60 then
    findings := findings.push ⟨line, .couldBeBetter, "C02", "Function longer than 60 lines"⟩
  return findings

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
      lines := lines.push (ctx.fileMap.toPosition pos).line
      pos := (parser.run ctx { env, options := {} } (Parser.getTokenTable env)
        { pos := ctx.next next, cache := Parser.initCacheForInput ctx.inputString }).pos
  return lines

private partial def commentLines (ctx : Parser.InputContext) (env : Environment)
    (stx : Syntax) : Array Nat := Id.run do
  let mut lines := #[]
  if [``Parser.Command.docComment, ``Parser.Command.moduleDoc].contains stx.getKind then
    if let some pos := stx.getPos? then
      lines := lines.push (ctx.fileMap.toPosition pos).line
  if let some (.original leading _ trailing _) := stx.getInfo? then
    for part in #[leading, trailing] do
      lines := lines ++ triviaComments ctx env part
  return lines ++ stx.getArgs.flatMap (commentLines ctx env)

def declarationBlocks (commands : Array Syntax) : Array Syntax :=
  commands.flatMap fun cmd =>
    let declarations := syntaxNodes ``Parser.Command.declaration cmd
    if declarations.isEmpty then #[cmd] else declarations

def check (rawSource : String) (file : ElaboratedFile) (blocks : Array Syntax) : Array Finding :=
  let comments := (#[file.header] ++ file.commands).flatMap (commentLines file.input file.importEnv)
  checkLineLengths rawSource ++
    comments.map (fun line => ⟨line, .warning, "W18", "Comment"⟩) ++
    blocks.flatMap (checkDefinition file.input.fileMap)

end Lint4.SourceChecks
