/-!
Plain data that describes one worked example.
The `list` and `run` commands of the `shex_lean` executable show this data.
-/

namespace Examples

/-- A worked example with a schema, a graph and a typing.
Each part is plain text that the `shex_lean` executable shows. -/
structure Example where
  /-- The name that selects this example on the command line. -/
  name : String
  /-- A one-line description that `list` shows. -/
  summary : String
  /-- The shapes schema, in a syntax similar to the paper and to ShEx. -/
  schemaText : String
  /-- The RDF graph, in a syntax similar to Turtle. -/
  graphText : String
  /-- The typing of the example.
  The related `.lean` proof file proves that this typing is correct (Definition 2). -/
  typingText : String

/-- The full text that `run <name>` prints for an example. -/
def Example.render (e : Example) : String :=
  s!"{e.name} — {e.summary}\n\n" ++
  s!"Schema:\n{e.schemaText}\n\n" ++
  s!"Graph:\n{e.graphText}\n\n" ++
  s!"Typing:\n{e.typingText}\n"

end Examples
