import ShexLean.Shex2025Inheritance.Termination

/-!
Definition 4 (§4.1) of the 2025 "Shape Expressions with Inheritance"
paper — correct typing.

> Definition 4 (correct typing). Let `G` be a graph and `S` be a schema. A
> typing `τ` of `G` by `S` is correct if for every `(n,z) ∈ τ`:
> – if `z ∉ A`, then `G,n,τ ⊨_S def(z)`,
> – if `z ∈ A`, then there exists `x ∈ desc(z) \ A` such that
>   `G,n,τ ⊨_S def(x)`.
>
> We denote `C(G,S)` the set of correct typings of `G` by `S`.

This is stated directly in terms of `Satisfies` (`ShexLean/Shex2025Inheritance/
Termination.lean`'s fuel-free, canonical relation — well-defined, i.e.
agreeing with the paper's real `⊨_S`, for schemas satisfying
`Schema.WellFormedX`/`Schema.WellFormedExtends`, by `lemma1`). The abstract
case reuses `Schema.desc` (`ShexLean/Shex2025Inheritance/Syntax.lean`, Definition
3's descendants) exactly as stated.
-/

namespace ShexLean.Inheritance

/-- Definition 4 (correct typing). -/
def Schema.CorrectTyping (S : Schema) (G : Graph) (τ : Typing) : Prop :=
  ∀ n z, τ.has n z →
    (z ∉ S.A → Satisfies S G τ n (S.shapeDef z)) ∧
    (z ∈ S.A → ∃ x ∈ S.desc z \ S.A, Satisfies S G τ n (S.shapeDef x))

/-- The empty typing is always correct (vacuously — it has no `(n,z)`
pairs to check), exactly as in the 2017 formalization
(`ShexLean/Shex2017Schemas/MaximalTyping.lean`'s analogous remark on `typing₄`). -/
theorem Schema.correctTyping_empty (S : Schema) (G : Graph) : S.CorrectTyping G ∅ := by
  intro n z hz
  simp [Typing.has] at hz

end ShexLean.Inheritance
