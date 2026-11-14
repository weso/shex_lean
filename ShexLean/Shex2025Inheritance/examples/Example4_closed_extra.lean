import ShexLean.Shex2025Inheritance.examples.Example3_triple_match
import Example

/-!
Example 4 from the 2025 paper "Shape Expressions with Inheritance" (§4.1,
rule 17 of Table 3): the modifiers `closed` and `extra`.

It uses again `M24`, `M246`, `M2a`, `M24a` and `τ_ex3` of Example 3
(`Example3_triple_match.lean`), but with a different triple expression:
`e = p @T_even ; p @T_lt5`. This is a plain sequence of two elements, with
no `|` and no `*`. Different from `e_ex3`, it needs `M` to have exactly
two triples after the `closed`/`extra` bookkeeping of the shape removes
all that is not "consumed".

The plain triple expression of Example 3 had no `closed` or `extra`. Thus,
this is the first file that tests that bookkeeping.
-/

namespace ShexLean.Inheritance

open ShexLean.InheritanceCore hiding Schema

/-- The triple expression of Example 4, `e = p @T_even ; p @T_lt5`. -/
def e_ex4 : TripleExpr := .seq (.tc "p" "T_even") (.tc "p" "T_lt5")

/-- Each `M` that satisfies a plain sequence `e1;e2` of two triple
constraints has exactly two elements. The semantics of `.tc` forces each
side of the split to be a singleton. The negative claims of Example 4 use
this lemma: the matching part of `M2a` is too small, and `M246` is too
large. -/
theorem seq_tc_tc_card_two {τ : Typing} {M : Finset Triple}
    {p1 : IRI} {z1 : Label} {p2 : IRI} {z2 : Label}
    (hSat : SatisfiesE τ M (.seq (.tc p1 z1) (.tc p2 z2))) : M.card = 2 := by
  obtain ⟨M1, M2, ⟨hdisj, hunion⟩, ⟨n1, o1, hM1, _⟩, ⟨n2, o2, hM2, _⟩⟩ := hSat
  subst hM1; subst hM2
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton, Finset.card_singleton]

/-- `M24, τ ⊨ ⟨e⟩` (Example 4). `e_ex4` "consumes" the two triples of `M24`
(`2` matches `p @T_even`, and `4` matches `p @T_lt5`). Thus, `Me = M24`,
and `Mnotin` is automatically empty. -/
theorem M24_satisfies_ofShape_e4 :
    SatisfiesMFuel bigFuel S_ex5 τ_ex3 M24 (.ofShape ⟨false, none, e_ex4⟩) := by
  apply ofShape_of_Me_eq_self (e := e_ex4)
  · apply Finset.Subset.antisymm
    · intro t ht; rw [mem_Me] at ht; exact ht.1
    · intro t ht
      have ht2 : t = tp "p" (.lit (.int 2)) ∨ t = tp "p" (.lit (.int 4)) := by
        unfold M24 at ht; simpa using ht
      rw [mem_Me]
      refine ⟨ht, "T_even", ?_, ?_⟩
      all_goals rcases ht2 with rfl | rfl <;> decide
  · refine ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.int 4))}, ⟨by decide, by decide⟩, ?_, ?_⟩
    · exact ⟨n_ex3, .lit (.int 2), rfl, by decide⟩
    · exact ⟨n_ex3, .lit (.int 4), rfl, by decide⟩

/-- `M2a, τ ¬⊨ ⟨e⟩` (Example 4). Only `2` (not `"a"`) matches a triple
constraint of `e_ex4`. Thus, `Me τ M2a e_ex4` has one element, but `e_ex4`
needs exactly two (`seq_tc_tc_card_two`). -/
theorem M2a_not_satisfies_ofShape_e4 :
    ¬ SatisfiesMFuel bigFuel S_ex5 τ_ex3 M2a (.ofShape ⟨false, none, e_ex4⟩) := by
  rintro ⟨hE, -, -⟩
  have hcard : (Me τ_ex3 M2a e_ex4).card = 2 := seq_tc_tc_card_two hE
  have hMe_sub : Me τ_ex3 M2a e_ex4 ⊆ {tp "p" (.lit (.int 2))} := by
    intro t ht
    rw [mem_Me] at ht
    obtain ⟨htM, z, hz, hty⟩ := ht
    unfold M2a at htM
    simp only [Finset.mem_insert, Finset.mem_singleton] at htM
    rcases htM with rfl | rfl
    · exact Finset.mem_singleton_self _
    · simp only [tp, e_ex4, TripleExpr.tcs, Finset.mem_union, Finset.mem_singleton,
        Prod.mk.injEq] at hz
      rcases hz with ⟨-, hz⟩ | ⟨-, hz⟩ <;> subst hz <;> exact absurd hty (by decide)
  have : (Me τ_ex3 M2a e_ex4).card ≤ 1 := Finset.card_le_card hMe_sub |>.trans (by decide)
  omega

/-- `M246, τ ¬⊨ ⟨e⟩` (Example 4). `M246` already has three elements. This
is too many for `e_ex4`, which needs exactly two, for all possible
matches. -/
theorem M246_not_satisfies_ofShape_e4 :
    ¬ SatisfiesMFuel bigFuel S_ex5 τ_ex3 M246 (.ofShape ⟨false, none, e_ex4⟩) := by
  rintro ⟨hE, hMnotin, -⟩
  have hcard := seq_tc_tc_card_two hE
  have hMnotin_empty : Mnotin τ_ex3 M246 e_ex4 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have := hMnotin (Finset.mem_image_of_mem Triple.pred ht)
    simp at this
  have hMe_eq : Me τ_ex3 M246 e_ex4 = M246 := by
    apply Finset.Subset.antisymm
    · intro t ht; rw [mem_Me] at ht; exact ht.1
    · intro t ht
      by_contra hnotMe
      have : t ∈ Mnotin τ_ex3 M246 e_ex4 := by
        rw [mem_Mnotin]
        refine ⟨⟨ht, ?_⟩, hnotMe⟩
        unfold M246 at ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl <;> simp [tp, e_ex4, TripleExpr.props, TripleExpr.tcs]
      rw [hMnotin_empty] at this
      exact absurd this (Finset.notMem_empty t)
  rw [hMe_eq] at hcard
  have : M246.card = 3 := by unfold M246; decide
  omega

/-- `M24a, τ ⊨ extra {p} ⟨e⟩` (Example 4). The leftover triple with `"a"`
is permitted, because its property `p` is in `extra`. -/
theorem M24a_satisfies_extra :
    SatisfiesMFuel bigFuel S_ex5 τ_ex3 M24a (.ofShape ⟨false, some {"p"}, e_ex4⟩) := by
  have hMe_eq : Me τ_ex3 M24a e_ex4 = M24 := by
    apply Finset.Subset.antisymm
    · intro t ht
      rw [mem_Me] at ht
      obtain ⟨htM, z, hz, hty⟩ := ht
      unfold M24a at htM; unfold M24
      simp only [Finset.mem_insert, Finset.mem_singleton] at htM ⊢
      rcases htM with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp only [tp, e_ex4, TripleExpr.tcs, Finset.mem_union, Finset.mem_singleton,
          Prod.mk.injEq] at hz
        rcases hz with ⟨-, hz⟩ | ⟨-, hz⟩ <;> subst hz <;> exact absurd hty (by decide)
    · intro t ht
      rw [mem_Me]
      unfold M24 at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      unfold M24a
      refine ⟨?_, "T_even", ?_, ?_⟩ <;> rcases ht with rfl | rfl <;> decide
  refine ⟨by rw [hMe_eq]; exact ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.int 4))},
    ⟨by decide, by decide⟩, ⟨n_ex3, .lit (.int 2), rfl, by decide⟩,
    ⟨n_ex3, .lit (.int 4), rfl, by decide⟩⟩, ?_, by simp⟩
  intro t ht
  unfold props at ht
  obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
  rw [mem_Mnotin, hMe_eq] at ht'
  obtain ⟨⟨htM, hpred⟩, htnotMe⟩ := ht'
  unfold M24a at htM
  simp only [Finset.mem_insert, Finset.mem_singleton] at htM
  rcases htM with rfl | rfl | rfl
  · exact absurd (by unfold M24; decide) htnotMe
  · exact absurd (by unfold M24; decide) htnotMe
  · decide

/-- `M24a ∪ {(n,q,2)}, τ ⊨ extra {p} ⟨e⟩` (Example 4). A shape that is not
closed does not see the extra triple with the predicate `q`, because
`q ∉ props(e_ex4) = {p}`. The `closed`/`extra` bookkeeping of rule 17 of
Table 3 looks only at `M^{e'}`, and its filter already removes the
predicates outside `props(e)`. Compare with
`M24a_q_not_satisfies_closed_extra` below: there, with `closed`, the same
set fails. -/
theorem M24a_q_satisfies_extra :
    SatisfiesMFuel bigFuel S_ex5 τ_ex3 (M24a ∪ {tp "q" (.lit (.int 2))})
      (.ofShape ⟨false, some {"p"}, e_ex4⟩) := by
  have hMe_eq : Me τ_ex3 (M24a ∪ {tp "q" (.lit (.int 2))}) e_ex4 = M24 := by
    apply Finset.Subset.antisymm
    · intro t ht
      rw [mem_Me] at ht
      obtain ⟨htM, z, hz, hty⟩ := ht
      simp only [M24a, M24, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at htM ⊢
      simp only [e_ex4, TripleExpr.tcs, Finset.mem_union, Finset.mem_singleton,
        Prod.mk.injEq] at hz
      rcases htM with (rfl | rfl | rfl) | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rcases hz with ⟨-, hz⟩ | ⟨-, hz⟩ <;> subst hz <;> exact absurd hty (by decide)
      · rcases hz with ⟨hz, -⟩ | ⟨hz, -⟩ <;> exact absurd hz (by decide)
    · intro t ht
      rw [mem_Me]
      unfold M24 at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      refine ⟨?_, "T_even", ?_, ?_⟩ <;> rcases ht with rfl | rfl <;>
        first | (unfold M24a; decide) | decide
  refine ⟨by rw [hMe_eq]; exact ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.int 4))},
    ⟨by decide, by decide⟩, ⟨n_ex3, .lit (.int 2), rfl, by decide⟩,
    ⟨n_ex3, .lit (.int 4), rfl, by decide⟩⟩, ?_, by simp⟩
  intro t ht
  unfold props at ht
  obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
  rw [mem_Mnotin, hMe_eq] at ht'
  obtain ⟨⟨htM, hpred⟩, htnotMe⟩ := ht'
  simp only [M24a, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at htM
  rcases htM with (rfl | rfl | rfl) | rfl
  · exact absurd (by unfold M24; decide) htnotMe
  · exact absurd (by unfold M24; decide) htnotMe
  · decide
  · exact absurd hpred (by decide)

/-- `M24a ∪ {(n,q,2)}, τ ¬⊨ closed extra {p} ⟨e⟩` (Example 4). Now `closed`
forbids the extra triple with the predicate `q`, because
`q ∉ props(e_ex4) ∪ {p} = {p}`. -/
theorem M24a_q_not_satisfies_closed_extra :
    ¬ SatisfiesMFuel bigFuel S_ex5 τ_ex3 (M24a ∪ {tp "q" (.lit (.int 2))})
      (.ofShape ⟨true, some {"p"}, e_ex4⟩) := by
  rintro ⟨-, -, hclosed⟩
  have hpq : "q" ∈ props (M24a ∪ {tp "q" (.lit (.int 2))}) :=
    Finset.mem_image_of_mem Triple.pred (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have := hclosed rfl hpq
  simp only [Finset.mem_union] at this
  rcases this with h | h
  · simp [e_ex4, TripleExpr.props, TripleExpr.tcs] at h
  · simp at h

end ShexLean.Inheritance

namespace Examples

open ShexLean.InheritanceCore (Shape)
open ShexLean.Inheritance (e_ex4 M24 M246 M2a M24a S_ex5 τ_ex3 bigFuel n_ex3 tp
  S_ex5_XClosed S_ex5_RestrOk satisfiesMFuel_decidable)
open ShexLean (Triple Graph.render renderDecide)

/-- The result of `renderDecide` for
`M ⊨ shape` with `S_ex5` and `τ_ex3`. Each `.ofShape` argument below
trivially satisfies `MOk` (`.ofShape _ => True`). Thus, only the
schema-level witnesses `S_ex5_XClosed` and `S_ex5_RestrOk` are
necessary. -/
def satEx4 (M : Finset Triple) (h : Shape) : String :=
  renderDecide (satisfiesMFuel_decidable S_ex5 τ_ex3 S_ex5_XClosed S_ex5_RestrOk
    bigFuel M (.ofShape h) trivial)

/-- `M24a ∪ {(n,q,2)}`: the set with the extra `q` triple. Both
`M24a_q_satisfies_extra` and `M24a_q_not_satisfies_closed_extra` use
it. -/
def M24a_q : Finset Triple := M24a ∪ {tp "q" (.lit (.int 2))}

/-- The `closed`/`extra` semantics of Example 4, on `M24`, `M246`, `M2a`
and `M24a` of Example 3.

* `graphText` is rendered from the real `Finset Triple` values.
* Each claim `M ⊨ shape` in `typingText` is a `renderDecide` computation
  with `satisfiesMFuel_decidable`. -/
def inheritance2025ClosedExtra : Example where
  name := "inheritance2025-example4-closed-extra"
  summary := "closed and extra modifiers (Table 3, rule 17) on M24, M246, M2a and M24a."
  schemaText := s!"e = {e_ex4.render}"
  graphText :=
    s!"M24    = {Graph.render M24}\n" ++
    s!"M246   = {Graph.render M246}\n" ++
    s!"M2a    = {Graph.render M2a}\n" ++
    s!"M24a   = {Graph.render M24a}\n" ++
    "M24a ∪ {(n,q,2)} = " ++ Graph.render M24a_q
  typingText :=
    s!"M24,  τ ⊨ ⟨e⟩ = {satEx4 M24 ⟨false, none, e_ex4⟩} (both triples consumed exactly)\n" ++
    s!"M2a,  τ ⊨ ⟨e⟩ = {satEx4 M2a ⟨false, none, e_ex4⟩} " ++
      "(only one triple matches e's constraints)\n" ++
    s!"M246, τ ⊨ ⟨e⟩ = {satEx4 M246 ⟨false, none, e_ex4⟩} (three triples, e needs exactly two)\n" ++
    s!"M24a, τ ⊨ extra " ++ "{p} " ++ s!"⟨e⟩ = {satEx4 M24a ⟨false, some {"p"}, e_ex4⟩} " ++
      "(leftover (n,p,\"a\") allowed by extra {p})\n" ++
    "M24a ∪ {(n,q,2)}, τ ⊨ extra {p} ⟨e⟩ = " ++
      s!"{satEx4 M24a_q ⟨false, some {"p"}, e_ex4⟩} " ++
      "(the extra q-triple is unconstrained)\n" ++
    "M24a ∪ {(n,q,2)}, τ ⊨ closed extra {p} ⟨e⟩ = " ++
      s!"{satEx4 M24a_q ⟨true, some {"p"}, e_ex4⟩}\n" ++
    "  — closed forbids the (n,q,2) triple: extra {p} only excuses leftover\n" ++
    "    p-triples, not triples with other predicates."

end Examples
