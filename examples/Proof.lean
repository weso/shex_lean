/-!
Plain data that describes one proved theorem.
The `list` and `run` commands of the `shex_lean` executable show
this data, together with the worked examples (`Examples.Example`).

The two kinds of data are different:

* An `Example` contains a summary of the schema, the graph and the typing.
  This summary is text in paper notation that a person wrote by hand.
* A `ProofItem` contains only a path.
  At runtime, the executable reads the Lean source from `path`.
  Thus, the proof that the executable shows is always
  the same as the proof that `lake build` checks.
-/

namespace Examples

/-- A theorem.
The executable can show the Lean source of this theorem. -/
structure ProofItem where
  /-- The name that selects this proof on the command line. -/
  name : String
  /-- A one-line description that `list` shows. -/
  summary : String
  /-- The path of the `.lean` file that contains the statement and the proof of the theorem.
  The path is relative to the project root. -/
  path : String

end Examples
