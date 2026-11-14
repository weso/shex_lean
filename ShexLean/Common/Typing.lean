import ShexLean.Common.RDF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter

/-!
> Definition 1 (node-type association, typing). A node-type association is a
> couple (n, L) in Nodes(G) × L.
> A typing of G by S is a set of node-type associations.
-/

namespace ShexLean

/-- The set `L` of shape labels. -/
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

/-- `τ_{|Z}`: the restriction of `τ` to the node-type associations that
have their label in `Z`. It is a plain function, not a definition with dot
notation, because dot notation on `τ : Typing` resolves to `Finset`. -/
def restrictTyping (τ : Typing) (Z : Finset Label) : Typing := τ.filter (fun p => p.2 ∈ Z)

theorem mem_restrictTyping {τ : Typing} {Z : Finset Label} {n : RDFNode} {z : Label} :
    (n, z) ∈ restrictTyping τ Z ↔ (n, z) ∈ τ ∧ z ∈ Z := by simp [restrictTyping]

/-- `τ` and `τ'` agree on `Z`: they give the same labels of `Z` to each
node. The agreement and monotonicity lemmas of the papers use this
hypothesis. -/
def AgreeOn (τ τ' : Typing) (Z : Finset Label) : Prop :=
  ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')

/-- If two typings have the same restriction to `Z`, they agree on `Z`. -/
theorem restrictTyping_agree {τ τ' : Typing} {Z : Finset Label}
    (h : restrictTyping τ Z = restrictTyping τ' Z) : AgreeOn τ τ' Z := by
  intro n z hz
  have := congrArg (fun t => (n, z) ∈ t) h
  simp only [mem_restrictTyping, hz, and_true] at this
  exact Iff.of_eq this

end ShexLean
