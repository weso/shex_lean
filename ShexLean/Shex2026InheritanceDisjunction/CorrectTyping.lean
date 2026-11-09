import ShexLean.Shex2026InheritanceDisjunction.Termination

/-!
This file is a copy of the same file in `ShexLean/Shex2025Inheritance/`,
for the relaxed rule 18 with disjunctive `extends`. It does not use the
payload of `.extends`. Thus, its proofs do not change.

Definition 4 (§4.1) of the 2025 paper "Shape Expressions with
Inheritance": correct typing.

> Definition 4 (correct typing). Let `G` be a graph and `S` be a schema. A
> typing `τ` of `G` by `S` is correct if for every `(n,z) ∈ τ`:
> – if `z ∉ A`, then `G,n,τ ⊨_S def(z)`,
> – if `z ∈ A`, then there exists `x ∈ desc(z) \ A` such that
>   `G,n,τ ⊨_S def(x)`.
>
> We denote `C(G,S)` the set of correct typings of `G` by `S`.

-/

namespace ShexLean.InheritanceDisjunction

open ShexLean.InheritanceCore

/-- Definition 4 (correct typing). -/
def Schema.CorrectTyping (S : Schema) (G : Graph) (τ : Typing) : Prop :=
  ∀ n z, τ.has n z →
    (z ∉ S.A → Satisfies S G τ n (S.shapeDef z)) ∧
    (z ∈ S.A → ∃ x ∈ S.desc z \ S.A, Satisfies S G τ n (S.shapeDef x))

/-- The empty typing is trivially correct. It has no `(n,z)` pairs to
check. -/
theorem Schema.correctTyping_empty (S : Schema) (G : Graph) : S.CorrectTyping G ∅ := by
  intro n z hz
  simp [Typing.has] at hz

end ShexLean.InheritanceDisjunction
