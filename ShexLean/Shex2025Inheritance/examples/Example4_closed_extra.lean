import ShexLean.Shex2025Inheritance.examples.Example3_triple_match
import Example

/-!
Example 4 from the 2025 "Shape Expressions with Inheritance" paper (§4.1,
Table 3 rule 17): the `closed`/`extra` modifiers, reusing Example 3's
`M24`/`M246`/`M2a`/`M24a`/`τ_ex3` (`Example3_triple_match.lean`), but a
*different* triple expression: `e = p @T_even ; p @T_lt5` (a bare
two-element sequence, no `|`/`*` — unlike `e_ex3`, this one needs `M` to
consist of *exactly* two triples once the shape's own `closed`/`extra`
bookkeeping strips away anything not "consumed", which is exactly what
this file exercises and Example 3 never did (a bare, unwrapped triple
expression has no `closed`/`extra` to speak of at all).
-/

namespace ShexLean.Inheritance

/-- Example 4's triple expression `e = p @T_even ; p @T_lt5`. -/
def e_ex4 : TripleExpr := .seq (.tc "p" "T_even") (.tc "p" "T_lt5")

/-- Any `M` satisfying a bare `e1;e2` sequence of two triple constraints
has exactly two elements — each side of the split is forced to a singleton
by `.tc`'s own semantics. The cardinality fact behind Example 4's negative
claims (`M2a`/`M246` can't satisfy `e_ex4`, for unrelated reasons: `M2a`'s
matching part is too small, `M246` itself is too big). -/
theorem seq_tc_tc_card_two {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ} {M : Finset Triple}
    {p1 : IRI} {z1 : Label} {p2 : IRI} {z2 : Label}
    (hSat : SatisfiesEFuel (fuel + 2) S G τ M (.seq (.tc p1 z1) (.tc p2 z2))) : M.card = 2 := by
  obtain ⟨M1, M2, ⟨hdisj, hunion⟩, ⟨n1, o1, hM1, _⟩, ⟨n2, o2, hM2, _⟩⟩ := hSat
  subst hM1; subst hM2
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton, Finset.card_singleton]

/-- `M24, τ ⊨ ⟨e⟩` (Example 4): both of `M24`'s triples are "consumed" by
`e_ex4` (`2` matches `p @T_even`, `4` matches `p @T_lt5`), so `Me = M24`
and `Mnotin` is automatically empty. -/
theorem M24_satisfies_ofShape_e4 :
    SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M24 (.ofShape ⟨false, none, e_ex4⟩) := by
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

/-- `M2a, τ ¬⊨ ⟨e⟩` (Example 4): only `2` (not `"a"`) matches any triple
constraint of `e_ex4`, so `Me τ M2a e_ex4` has one element, but `e_ex4`
needs exactly two (`seq_tc_tc_card_two`). -/
theorem M2a_not_satisfies_ofShape_e4 :
    ¬ SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M2a (.ofShape ⟨false, none, e_ex4⟩) := by
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

/-- `M246, τ ¬⊨ ⟨e⟩` (Example 4): `M246` already has three elements, too
many for `e_ex4`'s exactly-two requirement, regardless of which match. -/
theorem M246_not_satisfies_ofShape_e4 :
    ¬ SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M246 (.ofShape ⟨false, none, e_ex4⟩) := by
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

/-- `M24a, τ ⊨ extra {p} ⟨e⟩` (Example 4): the leftover `"a"`-triple is
allowed since its property `p` is listed in `extra`. -/
theorem M24a_satisfies_extra :
    SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M24a (.ofShape ⟨false, some {"p"}, e_ex4⟩) := by
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

/-- `M24a ∪ {(n,q,2)}, τ ⊨ extra {p} ⟨e⟩` (Example 4): the extra
`q`-predicated triple is invisible to a non-closed shape (`q ∉
props(e_ex4) = {p}`, so it is captured by neither `M^e` nor `M^{e'}` at
all — Table 3 rule 17's `closed`/`extra` bookkeeping only ever inspects
`M^{e'}`, whose own filter already excludes predicates outside
`props(e)`). Contrasts with `M24a_q_not_satisfies_closed_extra` right
below: adding `closed` is exactly what makes this same set fail. -/
theorem M24a_q_satisfies_extra :
    SatisfiesMFuel bigFuel S_ex5 default τ_ex3 (M24a ∪ {tp "q" (.lit (.int 2))})
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

/-- `M24a ∪ {(n,q,2)}, τ ¬⊨ closed extra {p} ⟨e⟩` (Example 4): `closed`
now forbids the extra `q`-predicated triple entirely, since `q ∉
props(e_ex4) ∪ {p} = {p}`. -/
theorem M24a_q_not_satisfies_closed_extra :
    ¬ SatisfiesMFuel bigFuel S_ex5 default τ_ex3 (M24a ∪ {tp "q" (.lit (.int 2))})
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

open ShexLean.Inheritance (Shape e_ex4 M24 M246 M2a M24a S_ex5 τ_ex3 bigFuel n_ex3 tp
  S_ex5_XClosed S_ex5_RestrOk satisfiesMFuel_decidable)
open ShexLean (Triple Graph.render renderDecide)

/-- `renderDecide`'s `native_decide`-computed verdict for `M ⊨ shape` under
`S_ex5`/`τ_ex3` — every `.ofShape` argument below trivially satisfies `MOk`
(`.ofShape _ => True`), so no `XClosed`/`RestrOk` beyond the schema-level
`S_ex5_XClosed`/`S_ex5_RestrOk` witnesses is ever needed. -/
def satEx4 (M : Finset Triple) (h : Shape) : String :=
  renderDecide (satisfiesMFuel_decidable S_ex5 default τ_ex3 S_ex5_XClosed S_ex5_RestrOk
    bigFuel M (.ofShape h) trivial)

/-- `M24a ∪ {(n,q,2)}`, the extra-`q`-triple set both `M24a_q_satisfies_extra`
and `M24a_q_not_satisfies_closed_extra` reason about. -/
def M24a_q : Finset Triple := M24a ∪ {tp "q" (.lit (.int 2))}

/-- Example 4's `closed`/`extra` semantics, on Example 3's `M24`/`M246`/
`M2a`/`M24a`. `graphText` is rendered from the real `Finset Triple` values;
every `M ⊨ shape` claim in `typingText` is a `native_decide` computation via
`satisfiesMFuel_decidable`, not prose. -/
def inheritance2025ClosedExtra : Example where
  name := "inheritance2025-example4-closed-extra"
  summary := "closed/extra modifiers (Table 3, rule 17) on M24/M246/M2a/M24a."
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
