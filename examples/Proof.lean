/-!
A small piece of plain data describing one proved theorem, for the
`shex_lean` executable's `list`/`run` commands to display alongside the
worked schema/graph/typing examples (`Examples.Example`).

Unlike `Example` (whose schema/graph/typing text is a hand-written summary
in paper notation), a `ProofItem` is shown by reading its Lean source
straight from `path` at runtime: the displayed proof can never drift from
the one `lake build` actually checks.
-/

namespace Examples

/-- A theorem the executable can show the Lean source of. -/
structure ProofItem where
  /-- The name used to select this proof on the command line. -/
  name : String
  /-- A one-line description shown by `list`. -/
  summary : String
  /-- Path (relative to the project root) of the `.lean` file containing
  the theorem's statement and proof. -/
  path : String

end Examples
