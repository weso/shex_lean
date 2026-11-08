import ShexLean.Common.RDF
import Mathlib.Data.Finset.Basic

/-!
Typings. They follow §3.1 ("Typing and Correct Typing") of Boneva, Labra
Gayo, Prud'hommeaux (2017).

> Definition 1 (node-type association, typing). A node-type association is a
> couple (n, L) in Nodes(G) × L. A typing of G by S is a set of node-type
> associations.
-/

namespace ShexLean

/-- The set `L` of shape labels. A schema uses shape labels as names for
its shapes. -/
abbrev Label := String

/-- A node-type association `(n, L)`. -/
abbrev Assoc := RDFNode × Label

/-- A typing is a finite set of node-type associations. -/
abbrev Typing := Finset Assoc

/-- `(n, L) ∈ typing`: the typing `typing` gives the shape `L` to the node
`n`. This definition is an `abbrev` (reducible). Thus, `decide` can see
the `Finset` membership below it, which is decidable. -/
abbrev Typing.has (typing : Typing) (n : RDFNode) (L : Label) : Prop :=
  (n, L) ∈ typing

end ShexLean
