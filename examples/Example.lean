/-!
A small piece of plain data describing one worked example, for the
`shex_lean` executable's `list`/`run` commands to display.
-/

namespace Examples

/-- A worked schema/graph/typing example, described as plain text for
display by the `shex_lean` executable. -/
structure Example where
  /-- The name used to select this example on the command line. -/
  name : String
  /-- A one-line description shown by `list`. -/
  summary : String
  /-- The shapes schema, as paper/ShEx-like syntax. -/
  schemaText : String
  /-- The RDF graph, as Turtle-like syntax. -/
  graphText : String
  /-- The typing established (and, in the corresponding `.lean` proof file,
  proved correct per Definition 2). -/
  typingText : String

/-- The full text `run <name>` prints for an example. -/
def Example.render (e : Example) : String :=
  s!"{e.name} — {e.summary}\n\n" ++
  s!"Schema:\n{e.schemaText}\n\n" ++
  s!"Graph:\n{e.graphText}\n\n" ++
  s!"Typing:\n{e.typingText}\n"

end Examples
