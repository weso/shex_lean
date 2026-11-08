import ShexLean.Shex2026InheritanceDisjunction.Termination

/-!
Definition 4 (§4.1) of the 2025 paper "Shape Expressions with
Inheritance": correct typing.

> Definition 4 (correct typing). Let `G` be a graph and `S` be a schema. A
> typing `τ` of `G` by `S` is correct if for every `(n,z) ∈ τ`:
> – if `z ∉ A`, then `G,n,τ ⊨_S def(z)`,
> – if `z ∈ A`, then there exists `x ∈ desc(z) \ A` such that
>   `G,n,τ ⊨_S def(x)`.
>
> We denote `C(G,S)` the set of correct typings of `G` by `S`.

The definition uses `Satisfies` directly. `Satisfies` is the canonical
relation with no fuel, from
`ShexLean/Shex2026InheritanceDisjunction/Termination.lean`. By `lemma1`,
it is well-defined (it agrees with the real `⊨_S` of the paper) for each
schema that satisfies `Schema.WellFormedX` and `Schema.WellFormedExtends`.
The abstract case uses `Schema.desc`
(`ShexLean/Shex2026InheritanceDisjunction/Syntax.lean`, the descendants of
Definition 3) exactly as stated.
-/

namespace ShexLean.InheritanceDisjunction

/-- Definition 4 (correct typing). -/
def Schema.CorrectTyping (S : Schema) (G : Graph) (τ : Typing) : Prop :=
  ∀ n z, τ.has n z →
    (z ∉ S.A → Satisfies S G τ n (S.shapeDef z)) ∧
    (z ∈ S.A → ∃ x ∈ S.desc z \ S.A, Satisfies S G τ n (S.shapeDef x))

/-- The empty typing is always correct. This is vacuously true, because it
has no `(n,z)` pairs to check. The 2017 formalization has the same
property (`typing4_correct` in
`ShexLean/Shex2017Schemas/examples/Example3_typings.lean`). -/
theorem Schema.correctTyping_empty (S : Schema) (G : Graph) : S.CorrectTyping G ∅ := by
  intro n z hz
  simp [Typing.has] at hz

end ShexLean.InheritanceDisjunction
