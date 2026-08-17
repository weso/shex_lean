import ShexLean.Common.RDF
import Mathlib.Data.Finset.Basic

/-!
Typings, following §3.1 ("Typing and Correct Typing") of Boneva, Labra Gayo,
Prud'hommeaux (2017).

> Definition 1 (node-type association, typing). A node-type association is a
> couple (n, L) in Nodes(G) × L. A typing of G by S is a set of node-type
> associations.
-/

namespace ShexLean

/-- The set `L` of shape labels used to name shapes in a schema. -/
abbrev ShapeLabel := String

/-- A node-type association `(n, L)`. -/
abbrev NodeTypeAssoc := RDFNode × ShapeLabel

/-- A typing is a (finite) set of node-type associations. -/
abbrev Typing := Finset NodeTypeAssoc

/-- `(n, L) ∈ typing`, i.e. `n` is asserted to have shape `L` by `typing`.
An `abbrev` (reducible) so that `decide` can see through it to the underlying
(decidable) `Finset` membership. -/
abbrev Typing.has (typing : Typing) (n : RDFNode) (L : ShapeLabel) : Prop :=
  (n, L) ∈ typing

end ShexLean
