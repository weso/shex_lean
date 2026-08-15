import ShexLean.Shex2017Schemas.Proposition1
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Max

/-!
Lemma 2 (§3.3): `Typing(G, S, strat)` (Definition 4) does not depend on
which stratification `strat` of `S` is chosen.

The paper's own proof of this is only a sketch ("Proof. (Idea)..."): it
asserts a canonical "most refined" stratification exists and that every
stratification agrees with it, without spelling out why. This file gives a
full, independent proof, built from the ground up:

- `maxTypingAgreeing_fusion` ("Fusion"): revealing a schema's labels in one
  batch vs. two nested batches gives the same `maxTypingAgreeing` result.
- `combineStrat` + `Typing4_combineStrat`: a concrete "lex-combine"
  stratification and *refinement invariance* along it — not needed by the
  final proof below, but a genuine, independently useful fact, and the
  route originally attempted before it became clear that exact
  checkpoint-alignment with an *arbitrary* second stratification is
  mathematically impossible (two mutually-independent labels can be
  ordered differently by different valid stratifications).
- `maxTypingAgreeing_swap` ("Swap"): two batches that *each individually*
  only depend on a common base (not on each other) can be revealed in
  either order with the same result — two applications of Fusion.
- `remainingMin`/`cont1`: a canonical process that, starting from `∅`,
  repeatedly reveals the least-`strat`-valued remaining batch (for some
  arbitrarily fixed valid stratification, used only to make each step
  well-defined) until every label is settled.
- `cont1_indep` ("Independence"): `cont1`'s final answer does not change if
  the *first* step instead reveals any other valid batch — proved by
  strong induction on the number of remaining labels, using Swap to
  reconcile `cont1`'s own next step against the alternative one. This is
  the mathematical heart of the proof: it is what "reordering independent
  material doesn't change the final typing" actually means, made precise
  enough to prove.
- `cont1_chain`/`cont1_eq_Typing4`: chaining Independence along *any* valid
  stratification's own checkpoints shows `cont1 S _ G ∅ ∅ = Typing4 G S
  strat'` for that stratification — so, applied to `strat1` and `strat2`
  separately, both equal the same `cont1` value, giving `lemma2`.
-/

namespace ShexLean

/-- For *any* valid stratification, a stratum-checkpoint is self-contained:
every label in `S.stratum strat i` has *both* its positive and negative
dependencies confined within that same checkpoint. (Negative dependencies
even land strictly inside `S.stratum strat (i-1)`, but the weaker
`⊆ S.stratum strat i` bound is what later lemmas need.) This is what makes
`i ↦ S.stratum strat i` a well-behaved increasing sequence of self-
consistent sub-schemas. -/
theorem Schema.stratum_self_contained (S : Schema) (strat : Stratification S)
    (hClosed : S.Closed) (i : ℕ) :
    ∀ L ∈ S.stratum strat.strat i,
      (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ S.stratum strat.strat i := by
  intro L hL L2 hL2
  simp only [Schema.stratum, Finset.mem_filter] at hL ⊢
  obtain ⟨hLlabels, hLstrat⟩ := hL
  have hL2labels : L2 ∈ S.labels := hClosed L hLlabels hL2
  rcases Finset.mem_union.mp hL2 with hpos | hneg
  · exact ⟨hL2labels, (strat.pos_le L hLlabels L2 hpos).trans hLstrat⟩
  · exact ⟨hL2labels, (le_of_lt (strat.neg_strict L hLlabels L2 hneg)).trans hLstrat⟩

/-- `S` restricted to an arbitrary label set `Ls` (not necessarily a
stratum-checkpoint of any particular stratification), keeping the same
definitions. Generalizes `Schema.stratRestrict`. -/
def Schema.restrictLabels (S : Schema) (Ls : Finset ShapeLabel) : Schema where
  labels := Ls
  shapeDef := S.shapeDef

theorem Typing.restrictTo_mono {t t' : Typing} {Lo : Finset ShapeLabel} (h : t ⊆ t') :
    t.restrictTo Lo ⊆ t'.restrictTo Lo := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := Typing.mem_restrictTo.mp hp
  exact Typing.mem_restrictTo.mpr ⟨h hp1, hp2⟩

/-- Restricting to `Lo₂ ⊆ Lo₁` and then to `Lo₂` again is the same as
restricting to `Lo₂` directly. -/
theorem Typing.restrictTo_restrictTo {t : Typing} {Lo₁ Lo₂ : Finset ShapeLabel}
    (h : Lo₂ ⊆ Lo₁) : (t.restrictTo Lo₁).restrictTo Lo₂ = t.restrictTo Lo₂ := by
  apply Finset.ext
  rintro ⟨n, L⟩
  simp only [Typing.mem_restrictTo]
  constructor
  · rintro ⟨⟨htmem, _⟩, hL⟩
    exact ⟨htmem, hL⟩
  · rintro ⟨htmem, hL⟩
    exact ⟨⟨htmem, h hL⟩, hL⟩

theorem Schema.univTyping_mono {S : Schema} {G : Graph} {Ls Ls' : Finset ShapeLabel}
    (h : Ls ⊆ Ls') : (S.restrictLabels Ls).univTyping G ⊆ (S.restrictLabels Ls').univTyping G := by
  intro p hp
  simp only [Schema.univTyping, Schema.restrictLabels] at hp ⊢
  exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).1, h (Finset.mem_product.mp hp).2⟩

/-- A typing correct for a schema stays correct when restricted to a
self-contained (both `posDeps` and `negDeps` confined within it) sub-set of
labels — `Satisfies.agree` applies because such a label's whole dependency
footprint is already inside the restriction. -/
theorem restrictLabels_correct_restrictTo {S : Schema} {G : Graph} {Ls1 Ls2 : Finset ShapeLabel}
    {t : Typing}
    (hself : ∀ L ∈ Ls1, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Ls1)
    (ht : (S.restrictLabels Ls2).CorrectTyping G t) :
    (S.restrictLabels Ls1).CorrectTyping G (t.restrictTo Ls1) := by
  intro n L hmem
  obtain ⟨hmemT, hL1⟩ := Typing.mem_restrictTo.mp hmem
  have hSat : Satisfies G t n (S.shapeDef L) := ht n L hmemT
  have hagree : ∀ n' L', L' ∈ (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps →
      ((n', L') ∈ t ↔ (n', L') ∈ t.restrictTo Ls1) := by
    intro n' L' hL'
    have hL'1 : L' ∈ Ls1 := hself L hL1 hL'
    constructor
    · intro h; exact Typing.mem_restrictTo.mpr ⟨h, hL'1⟩
    · intro h; exact (Typing.mem_restrictTo.mp h).1
  exact (Satisfies.agree (G := G) (S.shapeDef L) hagree n).mp hSat

/-- **Fusion**: revealing `Ls₂` in one shot (`Lo = Ls`) agrees with
revealing it in two stages through the intermediate checkpoint `Ls₁`
(`Lo = Ls` then `Lo = Ls₁`) — batching more or less finely doesn't change
`maxTypingAgreeing`'s outcome, provided everything new in `Ls₂` only
negatively depends on the original `Ls`, and `Ls₁` is self-contained under
positive dependencies (both hold automatically when `Ls ⊆ Ls₁ ⊆ Ls₂` are
stratum-checkpoints of the same stratification, `Schema.stratum_self_contained`).

The proof shows each side is, as a *whole object* (not by decomposing into
individual candidate typings — an individual correct typing of `Ls₁` need
not be *maximal* there, so a per-candidate argument does not go through),
a valid candidate for the other's `maxTypingAgreeing` construction. -/
theorem maxTypingAgreeing_fusion {S : Schema} {G : Graph} {Ls Ls1 Ls2 : Finset ShapeLabel}
    {T : Typing} (hLsLs1 : Ls ⊆ Ls1) (hLs1Ls2 : Ls1 ⊆ Ls2)
    (hneg2 : ∀ L ∈ Ls2, (S.shapeDef L).negDeps ⊆ Ls)
    (hpos1 : ∀ L ∈ Ls1, (S.shapeDef L).posDeps ⊆ Ls1)
    (hTsub : T ⊆ (S.restrictLabels Ls).univTyping G)
    (hTcorrect : (S.restrictLabels Ls).CorrectTyping G T) :
    maxTypingAgreeing (S.restrictLabels Ls2) G Ls1
        (maxTypingAgreeing (S.restrictLabels Ls1) G Ls T) =
      maxTypingAgreeing (S.restrictLabels Ls2) G Ls T := by
  set A := maxTypingAgreeing (S.restrictLabels Ls1) G Ls T with hA_def
  set B := maxTypingAgreeing (S.restrictLabels Ls2) G Ls1 A with hB_def
  set C := maxTypingAgreeing (S.restrictLabels Ls2) G Ls T with hC_def
  have hTsub1 : T ⊆ (S.restrictLabels Ls1).univTyping G :=
    hTsub.trans (Schema.univTyping_mono hLsLs1)
  have hTcorrect1 : (S.restrictLabels Ls1).CorrectTyping G T := hTcorrect
  have hTsub2 : T ⊆ (S.restrictLabels Ls2).univTyping G :=
    hTsub.trans (Schema.univTyping_mono (hLsLs1.trans hLs1Ls2))
  have hTcorrect2 : (S.restrictLabels Ls2).CorrectTyping G T := hTcorrect
  have hAsub1 : A ⊆ (S.restrictLabels Ls1).univTyping G := maxTypingAgreeing_subset _ G _ _
  have hAcorrect1 : (S.restrictLabels Ls1).CorrectTyping G A :=
    maxTypingAgreeing_correct hTsub1 hTcorrect1 (fun L hL => hneg2 L (hLs1Ls2 hL))
  have hArestrict : A.restrictTo Ls = T.restrictTo Ls :=
    maxTypingAgreeing_restrictTo hTsub1 hTcorrect1
  have hAsub2 : A ⊆ (S.restrictLabels Ls2).univTyping G := hAsub1.trans (Schema.univTyping_mono hLs1Ls2)
  have hAcorrect2 : (S.restrictLabels Ls2).CorrectTyping G A := hAcorrect1
  -- `A` is itself a valid `C`-candidate.
  have hAC : A ⊆ C := subset_maxTypingAgreeing hAsub2 hAcorrect2 hArestrict
  have hBsub2 : B ⊆ (S.restrictLabels Ls2).univTyping G := maxTypingAgreeing_subset _ G _ _
  have hBcorrect2 : (S.restrictLabels Ls2).CorrectTyping G B :=
    maxTypingAgreeing_correct hAsub2 hAcorrect2 (fun L hL => (hneg2 L hL).trans hLsLs1)
  have hBrestrict1 : B.restrictTo Ls1 = A.restrictTo Ls1 :=
    maxTypingAgreeing_restrictTo hAsub2 hAcorrect2
  -- `B ⊆ C`.
  have hBC : B ⊆ C := by
    apply subset_maxTypingAgreeing hBsub2 hBcorrect2
    rw [← Typing.restrictTo_restrictTo (t := B) hLsLs1, hBrestrict1,
      Typing.restrictTo_restrictTo (t := A) hLsLs1, hArestrict]
  -- `C ⊆ B`.
  have hCB : C ⊆ B := by
    have hCsub2 : C ⊆ (S.restrictLabels Ls2).univTyping G := maxTypingAgreeing_subset _ G _ _
    have hCcorrect2 : (S.restrictLabels Ls2).CorrectTyping G C :=
      maxTypingAgreeing_correct hTsub2 hTcorrect2 hneg2
    have hCrestrict : C.restrictTo Ls = T.restrictTo Ls := maxTypingAgreeing_restrictTo hTsub2 hTcorrect2
    have hself1 : ∀ L ∈ Ls1, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Ls1 := by
      intro L hL
      apply Finset.union_subset (hpos1 L hL)
      exact (hneg2 L (hLs1Ls2 hL)).trans hLsLs1
    have hCL1correct : (S.restrictLabels Ls1).CorrectTyping G (C.restrictTo Ls1) :=
      restrictLabels_correct_restrictTo hself1 hCcorrect2
    have hCL1sub : C.restrictTo Ls1 ⊆ (S.restrictLabels Ls1).univTyping G := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Typing.mem_restrictTo.mp hp
      simp only [Schema.univTyping, Schema.restrictLabels] at hCsub2 ⊢
      exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp (hCsub2 hp1)).1, hp2⟩
    have hCL1restrict : (C.restrictTo Ls1).restrictTo Ls = T.restrictTo Ls := by
      rw [Typing.restrictTo_restrictTo hLsLs1, hCrestrict]
    have hCL1A : C.restrictTo Ls1 ⊆ A := subset_maxTypingAgreeing hCL1sub hCL1correct hCL1restrict
    have hCL1eqA : C.restrictTo Ls1 = A.restrictTo Ls1 := by
      apply Finset.Subset.antisymm
      · intro p hp
        obtain ⟨hp1, hp2⟩ := Typing.mem_restrictTo.mp hp
        exact Typing.mem_restrictTo.mpr ⟨hCL1A (Typing.mem_restrictTo.mpr ⟨hp1, hp2⟩), hp2⟩
      · exact Typing.restrictTo_mono hAC
    exact subset_maxTypingAgreeing hCsub2 hCcorrect2 hCL1eqA
  exact Finset.Subset.antisymm hBC hCB

/-- Sharper than `Schema.stratum_self_contained` on the negative side: a
label's negative dependencies land strictly *inside the previous*
checkpoint, not just inside its own. -/
theorem Schema.stratum_neg_confined (S : Schema) (strat : Stratification S)
    (hClosed : S.Closed) (i : ℕ) :
    ∀ L ∈ S.stratum strat.strat i, (S.shapeDef L).negDeps ⊆ S.stratum strat.strat (i - 1) := by
  intro L hL L2 hL2
  simp only [Schema.stratum, Finset.mem_filter] at hL ⊢
  obtain ⟨hLlabels, hLstrat⟩ := hL
  have hL2labels : L2 ∈ S.labels := hClosed L hLlabels (Finset.mem_union_right _ hL2)
  have := strat.neg_strict L hLlabels L2 hL2
  exact ⟨hL2labels, by omega⟩

theorem Schema.stratum_zero (S : Schema) (strat : Stratification S) :
    S.stratum strat.strat 0 = ∅ := by
  unfold Schema.stratum
  rw [Finset.filter_eq_empty_iff]
  intro L hL hle
  have := (strat.mem_range L hL).1
  omega

/-- `maxTypingAgreeing` is a no-op when asked to reveal exactly the schema
`fixed` is already correct+bounded for: the only self-agreeing candidate is
`fixed` itself. -/
theorem maxTypingAgreeing_self {S' : Schema} {G : Graph} {T : Typing}
    (hTsub : T ⊆ S'.univTyping G) (hTcorrect : S'.CorrectTyping G T) :
    maxTypingAgreeing S' G S'.labels T = T := by
  apply Finset.Subset.antisymm
  · have := Classical.decPred (fun t => S'.CorrectTyping G t ∧ t.restrictTo S'.labels = T.restrictTo S'.labels)
    apply Finset.sup_le
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    obtain ⟨htsub, -, htrestrict⟩ := ht
    have ht_eq : t.restrictTo S'.labels = t := by
      apply Finset.ext; rintro ⟨n, L⟩
      simp only [Typing.mem_restrictTo, Schema.univTyping] at htsub ⊢
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, (Finset.mem_product.mp (htsub h)).2⟩
    have hT_eq : T.restrictTo S'.labels = T := by
      apply Finset.ext; rintro ⟨n, L⟩
      simp only [Typing.mem_restrictTo, Schema.univTyping] at hTsub ⊢
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, (Finset.mem_product.mp (hTsub h)).2⟩
    rw [ht_eq, hT_eq] at htrestrict
    exact htrestrict.le
  · exact subset_maxTypingAgreeing hTsub hTcorrect rfl

/-!
The combined ("lex-refined") stratification: `strat1` as the primary key,
`strat2` as a tiebreak. It refines `strat1` exactly — its checkpoints at
multiples of `strat2.k + 1` recover `strat1`'s own checkpoints — which is
what makes it usable to relate `Typing4 strat1` to `Typing4` of a
stratification built from *both* `strat1` and `strat2`.
-/

private theorem lex_strict_mono {a1 a2 b1 b2 k2 : ℕ} (ha1 : 1 ≤ a1) (ha2 : 1 ≤ a2)
    (_hb1 : b1 ≤ k2) (hb2 : b2 ≤ k2) (ha : a2 < a1) :
    (a2 - 1) * (k2 + 1) + b2 < (a1 - 1) * (k2 + 1) + b1 := by
  obtain ⟨a1', rfl⟩ := Nat.exists_eq_add_of_le ha1
  obtain ⟨a2', rfl⟩ := Nat.exists_eq_add_of_le ha2
  have he1 : 1 + a1' - 1 = a1' := by omega
  have he2 : 1 + a2' - 1 = a2' := by omega
  rw [he1, he2]
  have hlt : a2' < a1' := by omega
  have hmul : (a2' + 1) * (k2 + 1) ≤ a1' * (k2 + 1) := Nat.mul_le_mul (by omega) (le_refl _)
  calc a2' * (k2 + 1) + b2 ≤ a2' * (k2 + 1) + k2 := by omega
    _ < a2' * (k2 + 1) + (k2 + 1) := by omega
    _ = (a2' + 1) * (k2 + 1) := by ring
    _ ≤ a1' * (k2 + 1) := hmul
    _ ≤ a1' * (k2 + 1) + b1 := by omega

private theorem lex_le {a1 a2 b1 b2 k2 : ℕ} (ha1 : 1 ≤ a1) (ha2 : 1 ≤ a2)
    (hb1 : b1 ≤ k2) (hb2 : b2 ≤ k2) (ha : a2 ≤ a1) (hab : a1 = a2 → b2 ≤ b1) :
    (a2 - 1) * (k2 + 1) + b2 ≤ (a1 - 1) * (k2 + 1) + b1 := by
  rcases eq_or_lt_of_le ha with heq | hlt
  · have hb : b2 ≤ b1 := hab heq.symm
    rw [show a2 = a1 from heq]
    omega
  · exact le_of_lt (lex_strict_mono ha1 ha2 hb1 hb2 hlt)

private theorem lex_upper {a k1 b k2 : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ k1) (hb : b ≤ k2) :
    (a - 1) * (k2 + 1) + b ≤ k1 * (k2 + 1) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha1
  have he : 1 + a' - 1 = a' := by omega
  rw [he]
  have hle : a' + 1 ≤ k1 := by omega
  have hmul : (a' + 1) * (k2 + 1) ≤ k1 * (k2 + 1) := Nat.mul_le_mul hle (le_refl _)
  have : a' * (k2 + 1) + b < (a' + 1) * (k2 + 1) := by
    calc a' * (k2 + 1) + b ≤ a' * (k2 + 1) + k2 := by omega
      _ < a' * (k2 + 1) + (k2 + 1) := by omega
      _ = (a' + 1) * (k2 + 1) := by ring
  omega

/-- `strat1` as primary key, `strat2` as tiebreak. -/
noncomputable def combineStrat {S : Schema} (hClosed : S.Closed) (strat1 strat2 : Stratification S) :
    Stratification S where
  k := strat1.k * (strat2.k + 1)
  strat := fun L => (strat1.strat L - 1) * (strat2.k + 1) + strat2.strat L
  mem_range := by
    intro L hL
    obtain ⟨h1lo, h1hi⟩ := strat1.mem_range L hL
    obtain ⟨h2lo, h2hi⟩ := strat2.mem_range L hL
    exact ⟨by omega, lex_upper h1lo h1hi h2hi⟩
  neg_strict := by
    intro L1 hL1 L2 hdep
    have h1 := strat1.neg_strict L1 hL1 L2 hdep
    have hL2 : L2 ∈ S.labels := hClosed L1 hL1 (Finset.mem_union_right _ hdep)
    obtain ⟨h1lo, -⟩ := strat1.mem_range L1 hL1
    obtain ⟨h1lo', -⟩ := strat1.mem_range L2 hL2
    obtain ⟨-, h2hi⟩ := strat2.mem_range L1 hL1
    obtain ⟨-, h2hi'⟩ := strat2.mem_range L2 hL2
    exact lex_strict_mono h1lo h1lo' h2hi h2hi' h1
  pos_le := by
    intro L1 hL1 L2 hdep
    have h1 := strat1.pos_le L1 hL1 L2 hdep
    have hL2 : L2 ∈ S.labels := hClosed L1 hL1 (Finset.mem_union_left _ hdep)
    obtain ⟨h1lo, -⟩ := strat1.mem_range L1 hL1
    obtain ⟨h1lo', -⟩ := strat1.mem_range L2 hL2
    obtain ⟨-, h2hi⟩ := strat2.mem_range L1 hL1
    obtain ⟨-, h2hi'⟩ := strat2.mem_range L2 hL2
    refine lex_le h1lo h1lo' h2hi h2hi' h1 (fun heq => ?_)
    have h2 := strat2.pos_le L1 hL1 L2 hdep
    exact h2

theorem stratum_combineStrat_align {S : Schema} (hClosed : S.Closed)
    (strat1 strat2 : Stratification S) (i : ℕ) :
    S.stratum strat1.strat i = S.stratum (combineStrat hClosed strat1 strat2).strat (i * (strat2.k + 1)) := by
  apply Finset.ext
  intro L
  simp only [Schema.stratum, Finset.mem_filter]
  constructor
  · rintro ⟨hL, hle⟩
    refine ⟨hL, ?_⟩
    show (strat1.strat L - 1) * (strat2.k + 1) + strat2.strat L ≤ i * (strat2.k + 1)
    obtain ⟨-, h2hi⟩ := strat2.mem_range L hL
    obtain ⟨h1lo, -⟩ := strat1.mem_range L hL
    obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le h1lo
    have he : strat1.strat L - 1 = a' := by omega
    rw [he]
    have : a' + 1 ≤ i := by omega
    have hmul : (a' + 1) * (strat2.k + 1) ≤ i * (strat2.k + 1) := Nat.mul_le_mul this (le_refl _)
    have : a' * (strat2.k + 1) + strat2.strat L < (a' + 1) * (strat2.k + 1) := by
      calc a' * (strat2.k + 1) + strat2.strat L ≤ a' * (strat2.k + 1) + strat2.k := by omega
        _ < a' * (strat2.k + 1) + (strat2.k + 1) := by omega
        _ = (a' + 1) * (strat2.k + 1) := by ring
    omega
  · rintro ⟨hL, hle⟩
    refine ⟨hL, ?_⟩
    show strat1.strat L ≤ i
    obtain ⟨h1lo, -⟩ := strat1.mem_range L hL
    obtain ⟨h2lo, h2hi⟩ := strat2.mem_range L hL
    obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le h1lo
    have he : strat1.strat L - 1 = a' := by omega
    change (strat1.strat L - 1) * (strat2.k + 1) + strat2.strat L ≤ i * (strat2.k + 1) at hle
    rw [he] at hle
    by_contra hcon
    push Not at hcon
    have : i + 1 ≤ a' + 1 := by omega
    have hmul : i * (strat2.k + 1) + (strat2.k + 1) ≤ (a' + 1) * (strat2.k + 1) :=
      calc i * (strat2.k + 1) + (strat2.k + 1) = (i + 1) * (strat2.k + 1) := by ring
        _ ≤ (a' + 1) * (strat2.k + 1) := Nat.mul_le_mul this (le_refl _)
    have hexpand : (a' + 1) * (strat2.k + 1) = a' * (strat2.k + 1) + (strat2.k + 1) := by ring
    omega

/-- **Refinement invariance**: `Typing4` under `strat1` agrees with
`Typing4` under `combineStrat hClosed strat1 strat2` (which refines
`strat1` exactly, at multiples of `strat2.k + 1`). Proved by induction on
`strat1`'s own strata, with an inner induction (bridging via repeated
`maxTypingAgreeing_fusion`) over the `strat2.k + 1` finer steps
`combineStrat` takes within each `strat1`-layer. -/
theorem stratTypingSeq_combineStrat_align {S : Schema} (hClosed : S.Closed)
    (strat1 strat2 : Stratification S) (G : Graph) :
    ∀ i ≤ strat1.k,
      stratTypingSeq S (combineStrat hClosed strat1 strat2).strat G (i * (strat2.k + 1)) =
        stratTypingSeq S strat1.strat G i
  | 0, _ => by simp [stratTypingSeq]
  | (i + 1), hi1 => by
      have hi : i ≤ strat1.k := by omega
      have houter := stratTypingSeq_combineStrat_align hClosed strat1 strat2 G i hi
      have hT1 := stratTypingSeq_correct S strat1 hClosed G i
      have halign : ∀ i' : ℕ, S.stratum strat1.strat i' =
          S.stratum (combineStrat hClosed strat1 strat2).strat (i' * (strat2.k + 1)) :=
        stratum_combineStrat_align hClosed strat1 strat2
      set combined := combineStrat hClosed strat1 strat2 with hcombined_def
      set Ls := S.stratum strat1.strat i with hLs_def
      set T := stratTypingSeq S strat1.strat G i with hT_def
      have hTsub : T ⊆ (S.restrictLabels Ls).univTyping G := hT1.1
      have hTcorrect : (S.restrictLabels Ls).CorrectTyping G T := hT1.2
      have inner : ∀ j, j ≤ strat2.k →
          stratTypingSeq S combined.strat G (i * (strat2.k + 1) + j) =
            maxTypingAgreeing (S.restrictLabels (S.stratum combined.strat (i * (strat2.k + 1) + j)))
              G Ls T := by
        intro j
        induction j with
        | zero =>
            intro _
            rw [Nat.add_zero, ← halign i, houter]
            exact (maxTypingAgreeing_self hTsub hTcorrect).symm
        | succ j ihj =>
            intro hj1
            have hj : j ≤ strat2.k := by omega
            have hj' := ihj hj
            set Ls1 := S.stratum combined.strat (i * (strat2.k + 1) + j) with hLs1_def
            set Ls2 := S.stratum combined.strat (i * (strat2.k + 1) + (j + 1)) with hLs2_def
            have hLs1Ls2 : Ls1 ⊆ Ls2 := by
              rw [hLs1_def, hLs2_def]; apply Schema.stratum_mono; omega
            have hLsLs1 : Ls ⊆ Ls1 := by
              rw [hLs_def, halign i, hLs1_def]; apply Schema.stratum_mono; omega
            have hLs2sub1 : Ls2 ⊆ S.stratum strat1.strat (i + 1) := by
              rw [hLs2_def, halign (i + 1)]
              apply Schema.stratum_mono
              have : i * (strat2.k + 1) + (j + 1) ≤ i * (strat2.k + 1) + (strat2.k + 1) := by omega
              have heq : i * (strat2.k + 1) + (strat2.k + 1) = (i + 1) * (strat2.k + 1) := by ring
              omega
            have hneg2 : ∀ L ∈ Ls2, (S.shapeDef L).negDeps ⊆ Ls := by
              intro L hL
              have := Schema.stratum_neg_confined S strat1 hClosed (i + 1) L (hLs2sub1 hL)
              simpa using this
            have hpos1 : ∀ L ∈ Ls1, (S.shapeDef L).posDeps ⊆ Ls1 := by
              intro L hL
              exact Finset.subset_union_left.trans
                (Schema.stratum_self_contained S combined hClosed
                  (i * (strat2.k + 1) + j) L hL)
            have hfusion := maxTypingAgreeing_fusion (S := S) (G := G) hLsLs1 hLs1Ls2
              hneg2 hpos1 hTsub hTcorrect
            have hstep : stratTypingSeq S combined.strat G (i * (strat2.k + 1) + (j + 1)) =
                maxTypingAgreeing (S.restrictLabels Ls2) G Ls1
                  (stratTypingSeq S combined.strat G (i * (strat2.k + 1) + j)) := by
              have heq : i * (strat2.k + 1) + (j + 1) = (i * (strat2.k + 1) + j) + 1 := by omega
              rw [heq]; rfl
            calc stratTypingSeq S combined.strat G (i * (strat2.k + 1) + (j + 1))
                = maxTypingAgreeing (S.restrictLabels Ls2) G Ls1
                    (stratTypingSeq S combined.strat G (i * (strat2.k + 1) + j)) := hstep
              _ = maxTypingAgreeing (S.restrictLabels Ls2) G Ls1
                    (maxTypingAgreeing (S.restrictLabels Ls1) G Ls T) := by rw [hj']
              _ = maxTypingAgreeing (S.restrictLabels Ls2) G Ls T := hfusion
      have hk2 := inner strat2.k (le_refl _)
      have hLs1last : S.stratum combined.strat (i * (strat2.k + 1) + strat2.k) ⊆
          S.stratum strat1.strat (i + 1) := by
        rw [halign (i + 1)]
        apply Schema.stratum_mono
        have heq : i * (strat2.k + 1) + (strat2.k + 1) = (i + 1) * (strat2.k + 1) := by ring
        omega
      have hLsLs1last : Ls ⊆ S.stratum combined.strat (i * (strat2.k + 1) + strat2.k) := by
        rw [hLs_def, halign i]
        apply Schema.stratum_mono
        omega
      have hneg2last : ∀ L ∈ S.stratum strat1.strat (i + 1), (S.shapeDef L).negDeps ⊆ Ls := by
        intro L hL
        have := Schema.stratum_neg_confined S strat1 hClosed (i + 1) L hL
        simpa using this
      have hpos1last : ∀ L ∈ S.stratum combined.strat (i * (strat2.k + 1) + strat2.k),
          (S.shapeDef L).posDeps ⊆ S.stratum combined.strat (i * (strat2.k + 1) + strat2.k) := by
        intro L hL
        exact Finset.subset_union_left.trans
          (Schema.stratum_self_contained S combined hClosed (i * (strat2.k + 1) + strat2.k) L hL)
      have hfusionlast := maxTypingAgreeing_fusion (S := S) (G := G) hLsLs1last
        (halign (i + 1) ▸ hLs1last) (halign (i + 1) ▸ hneg2last) hpos1last hTsub hTcorrect
      have hstep : stratTypingSeq S combined.strat G ((i + 1) * (strat2.k + 1)) =
          maxTypingAgreeing (S.restrictLabels (S.stratum combined.strat ((i + 1) * (strat2.k + 1)))) G
            (S.stratum combined.strat (i * (strat2.k + 1) + strat2.k))
            (stratTypingSeq S combined.strat G (i * (strat2.k + 1) + strat2.k)) := by
        have heq : (i + 1) * (strat2.k + 1) = (i * (strat2.k + 1) + strat2.k) + 1 := by ring
        rw [heq]; rfl
      calc stratTypingSeq S combined.strat G ((i + 1) * (strat2.k + 1))
          = maxTypingAgreeing (S.restrictLabels (S.stratum combined.strat ((i + 1) * (strat2.k + 1)))) G
              (S.stratum combined.strat (i * (strat2.k + 1) + strat2.k))
              (stratTypingSeq S combined.strat G (i * (strat2.k + 1) + strat2.k)) := hstep
        _ = maxTypingAgreeing (S.restrictLabels (S.stratum combined.strat ((i + 1) * (strat2.k + 1)))) G
              (S.stratum combined.strat (i * (strat2.k + 1) + strat2.k))
              (maxTypingAgreeing (S.restrictLabels (S.stratum combined.strat
                (i * (strat2.k + 1) + strat2.k))) G Ls T) := by rw [hk2]
        _ = maxTypingAgreeing (S.restrictLabels (S.stratum combined.strat ((i + 1) * (strat2.k + 1)))) G
              Ls T := hfusionlast
        _ = maxTypingAgreeing (S.restrictLabels (S.stratum strat1.strat (i + 1))) G Ls T := by
              rw [halign (i + 1)]
        _ = stratTypingSeq S strat1.strat G (i + 1) := rfl

/-- `combineStrat hClosed strat1 strat2` reduces to `Typing4 G S strat1` — the
`i = strat1.k` instance of `stratTypingSeq_combineStrat_align`, phrased via
`Typing4`. -/
theorem Typing4_combineStrat (S : Schema) (hClosed : S.Closed)
    (strat1 strat2 : Stratification S) (G : Graph) :
    Typing4 G S (combineStrat hClosed strat1 strat2) = Typing4 G S strat1 := by
  show stratTypingSeq S (combineStrat hClosed strat1 strat2).strat G
      (strat1.k * (strat2.k + 1)) = stratTypingSeq S strat1.strat G strat1.k
  exact stratTypingSeq_combineStrat_align hClosed strat1 strat2 G strat1.k (le_refl _)

/-!
**Lemma 2, general statement.**

`combineStrat hClosed strat1 strat2` aligns with `strat1`'s checkpoints but
not `strat2`'s in general: two mutually-independent labels (no dependency
edge either way) can be freely ordered differently by different valid
stratifications, so no single fixed combination aligns with an *arbitrary*
second stratification. The fix is to stop trying to align with a
*specific* schedule at all: define one canonical process that, at each
step, reveals *some* valid next batch (not tied to either `strat1` or
`strat2`), and show its final result doesn't depend on which valid batch
was chosen at each step (`indep` below, via `maxTypingAgreeing_swap`).
Then that process's final value can be shown to equal `Typing4 strat1` by
walking it through `strat1`'s own checkpoints one at a time (each such step
*is* a valid batch choice), and likewise for `strat2` — giving `Typing4
strat1 = Typing4 strat2` without ever needing `strat1` and `strat2` to
agree on any intermediate checkpoint.
-/

/-- The labels of least `strat`-value among those not yet in `Fixed` — a
canonical (but not the only valid) choice of "next batch": nonempty
whenever there is anything left, and (shown below) confined the way
`maxTypingAgreeing`'s construction needs. -/
def remainingMin (S : Schema) (strat : ShapeLabel → ℕ) (Fixed : Finset ShapeLabel) :
    Finset ShapeLabel :=
  (S.labels \ Fixed).filter (fun L => ∀ L' ∈ S.labels \ Fixed, strat L ≤ strat L')

theorem remainingMin_subset {S : Schema} {strat : ShapeLabel → ℕ} {Fixed : Finset ShapeLabel} :
    remainingMin S strat Fixed ⊆ S.labels \ Fixed := Finset.filter_subset _ _

theorem remainingMin_nonempty {S : Schema} {strat : ShapeLabel → ℕ} {Fixed : Finset ShapeLabel}
    (h : (S.labels \ Fixed).Nonempty) : (remainingMin S strat Fixed).Nonempty := by
  obtain ⟨L₀, hL₀, hmin⟩ := Finset.exists_min_image (S.labels \ Fixed) strat h
  exact ⟨L₀, Finset.mem_filter.mpr ⟨hL₀, hmin⟩⟩

/-- `remainingMin`'s batch (for any valid stratification `strat`) only
negatively depends on `Fixed`. -/
theorem remainingMin_neg {S : Schema} (strat : Stratification S) (hClosed : S.Closed)
    (Fixed : Finset ShapeLabel) :
    ∀ L ∈ remainingMin S strat.strat Fixed, (S.shapeDef L).negDeps ⊆ Fixed := by
  intro L hL L2 hL2
  obtain ⟨hLrem, hLmin⟩ := Finset.mem_filter.mp hL
  obtain ⟨hLlabels, hLnotFixed⟩ := Finset.mem_sdiff.mp hLrem
  have hL2labels : L2 ∈ S.labels := hClosed L hLlabels (Finset.mem_union_right _ hL2)
  by_contra hL2notFixed
  have hL2rem : L2 ∈ S.labels \ Fixed := Finset.mem_sdiff.mpr ⟨hL2labels, hL2notFixed⟩
  have h1 := strat.neg_strict L hLlabels L2 hL2
  have h2 := hLmin L2 hL2rem
  omega

/-- `Fixed ∪ remainingMin strat Fixed` is self-contained under positive
dependencies. -/
theorem remainingMin_pos {S : Schema} (strat : Stratification S) (hClosed : S.Closed)
    (Fixed : Finset ShapeLabel) :
    ∀ L ∈ remainingMin S strat.strat Fixed,
      (S.shapeDef L).posDeps ⊆ Fixed ∪ remainingMin S strat.strat Fixed := by
  intro L hL L2 hL2
  obtain ⟨hLrem, hLmin⟩ := Finset.mem_filter.mp hL
  obtain ⟨hLlabels, hLnotFixed⟩ := Finset.mem_sdiff.mp hLrem
  have hL2labels : L2 ∈ S.labels := hClosed L hLlabels (Finset.mem_union_left _ hL2)
  by_cases hL2Fixed : L2 ∈ Fixed
  · exact Finset.mem_union_left _ hL2Fixed
  · refine Finset.mem_union_right _ ?_
    have hL2rem : L2 ∈ S.labels \ Fixed := Finset.mem_sdiff.mpr ⟨hL2labels, hL2Fixed⟩
    have h1 := strat.pos_le L hLlabels L2 hL2
    have h2 := hLmin L2 hL2rem
    refine Finset.mem_filter.mpr ⟨hL2rem, fun L' hL' => ?_⟩
    have h3 := hLmin L' hL'
    omega

/-- Repeatedly reveal `strat`'s `remainingMin` batch, `n` times (or until
nothing is left — `n` is fuel, not meant to be tight). -/
noncomputable def cont1Fuel (S : Schema) (strat : Stratification S) (G : Graph) :
    ℕ → Finset ShapeLabel → Typing → Typing
  | 0, _, T => T
  | (n + 1), Fixed, T =>
      if (S.labels \ Fixed).Nonempty then
        cont1Fuel S strat G n (Fixed ∪ remainingMin S strat.strat Fixed)
          (maxTypingAgreeing (S.restrictLabels (Fixed ∪ remainingMin S strat.strat Fixed)) G
            Fixed T)
      else T

/-- `S.labels \ (Fixed ∪ remainingMin ...)` is strictly smaller than
`S.labels \ Fixed`. -/
private theorem remainingMin_card_lt (S : Schema) (strat : ShapeLabel → ℕ)
    {Fixed : Finset ShapeLabel} (h : (S.labels \ Fixed).Nonempty) :
    (S.labels \ (Fixed ∪ remainingMin S strat Fixed)).card < (S.labels \ Fixed).card := by
  have hBnonempty := remainingMin_nonempty (S := S) (strat := strat) h
  apply Finset.card_lt_card
  constructor
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    tauto
  · intro hsub
    obtain ⟨L₀, hL₀⟩ := hBnonempty
    have hL₀rem := remainingMin_subset (S := S) (strat := strat) hL₀
    have := hsub hL₀rem
    simp only [Finset.mem_sdiff, Finset.mem_union] at this
    exact this.2 (Or.inr hL₀)

private theorem cont1Fuel_of_not_nonempty (S : Schema) (strat : Stratification S) (G : Graph)
    {Fixed : Finset ShapeLabel} (h : ¬ (S.labels \ Fixed).Nonempty) (T : Typing) :
    ∀ n, cont1Fuel S strat G n Fixed T = T
  | 0 => rfl
  | (n + 1) => by simp only [cont1Fuel, ite_eq_right h]

/-- Once fuel is enough to exhaust the remaining labels, more fuel doesn't
change the result. -/
theorem cont1Fuel_stable (S : Schema) (strat : Stratification S) (G : Graph) :
    ∀ Fixed : Finset ShapeLabel, ∀ T : Typing, ∀ n n' : ℕ, (S.labels \ Fixed).card ≤ n →
      (S.labels \ Fixed).card ≤ n' → cont1Fuel S strat G n Fixed T = cont1Fuel S strat G n' Fixed T := by
  intro Fixed
  induction hcard : (S.labels \ Fixed).card using Nat.strong_induction_on generalizing Fixed with
  | _ card ih =>
    intro T n n' hn hn'
    by_cases hne : (S.labels \ Fixed).Nonempty
    · have hcardpos : 0 < card := hcard ▸ Finset.card_pos.mpr hne
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
      simp only [cont1Fuel, ite_eq_left hne]
      have hcard' : (S.labels \ (Fixed ∪ remainingMin S strat.strat Fixed)).card < card :=
        hcard ▸ remainingMin_card_lt S strat.strat hne
      exact ih _ hcard' _ rfl
        (maxTypingAgreeing (S.restrictLabels (Fixed ∪ remainingMin S strat.strat Fixed)) G Fixed T)
        m m' (by omega) (by omega)
    · rw [cont1Fuel_of_not_nonempty S strat G hne T n, cont1Fuel_of_not_nonempty S strat G hne T n']

/-- `cont1 S strat G Fixed T`: continue the `remainingMin` process from
`(Fixed, T)` all the way to `S.labels`, using `strat` throughout to choose
each batch (a fixed, concrete choice — but `indep` below shows *any* valid
first step gives the same final answer, so this concrete choice is not
actually load-bearing). -/
noncomputable def cont1 (S : Schema) (strat : Stratification S) (G : Graph)
    (Fixed : Finset ShapeLabel) (T : Typing) : Typing :=
  cont1Fuel S strat G S.labels.card Fixed T

theorem cont1_eq_fuel (S : Schema) (strat : Stratification S) (G : Graph)
    (Fixed : Finset ShapeLabel) (T : Typing) (n : ℕ) (hn : (S.labels \ Fixed).card ≤ n) :
    cont1 S strat G Fixed T = cont1Fuel S strat G n Fixed T :=
  cont1Fuel_stable S strat G Fixed T S.labels.card n (Finset.card_le_card (Finset.sdiff_subset)) hn

theorem cont1_done (S : Schema) (strat : Stratification S) (G : Graph)
    {Fixed : Finset ShapeLabel} (h : ¬ (S.labels \ Fixed).Nonempty) (T : Typing) :
    cont1 S strat G Fixed T = T := by
  have hcardzero : (S.labels \ Fixed).card = 0 := by
    rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]; exact h
  rw [cont1_eq_fuel S strat G Fixed T 1 (by omega)]
  simp only [cont1Fuel, ite_eq_right h]

theorem cont1_step (S : Schema) (strat : Stratification S) (G : Graph)
    {Fixed : Finset ShapeLabel} (h : (S.labels \ Fixed).Nonempty) (T : Typing) :
    cont1 S strat G Fixed T = cont1 S strat G (Fixed ∪ remainingMin S strat.strat Fixed)
      (maxTypingAgreeing (S.restrictLabels (Fixed ∪ remainingMin S strat.strat Fixed)) G Fixed T) := by
  obtain ⟨m, hm⟩ : ∃ m, (S.labels \ Fixed).card = m + 1 :=
    ⟨(S.labels \ Fixed).card - 1, by have := Finset.card_pos.mpr h; omega⟩
  rw [cont1_eq_fuel S strat G Fixed T (m + 1) (le_of_eq hm)]
  simp only [cont1Fuel, ite_eq_left h]
  refine (cont1_eq_fuel S strat G _ _ m ?_).symm
  have := remainingMin_card_lt S strat.strat h
  omega

/-- **Swap**: two disjoint batches `A`, `B` that *each individually* only
depend (negatively) on the common base `Ls0` and (positively) on `Ls0`
plus themselves — i.e. neither needs the other at all — can be revealed in
either order with the same result. Both sides reduce, via
`maxTypingAgreeing_fusion`, to the one-shot construction over `Ls0 ∪ A ∪
B`; this is the formal content of "reordering independent material doesn't
change the final typing", used below (`indep`) to show `cont1`'s first
step doesn't matter. -/
theorem maxTypingAgreeing_swap {S : Schema} {G : Graph} {Ls0 A B : Finset ShapeLabel}
    {T : Typing}
    (hLs0self : ∀ L ∈ Ls0, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Ls0)
    (hAneg : ∀ L ∈ A, (S.shapeDef L).negDeps ⊆ Ls0)
    (hApos : ∀ L ∈ A, (S.shapeDef L).posDeps ⊆ Ls0 ∪ A)
    (hBneg : ∀ L ∈ B, (S.shapeDef L).negDeps ⊆ Ls0)
    (hBpos : ∀ L ∈ B, (S.shapeDef L).posDeps ⊆ Ls0 ∪ B)
    (hTsub : T ⊆ (S.restrictLabels Ls0).univTyping G)
    (hTcorrect : (S.restrictLabels Ls0).CorrectTyping G T) :
    maxTypingAgreeing (S.restrictLabels (Ls0 ∪ A ∪ B)) G (Ls0 ∪ A)
        (maxTypingAgreeing (S.restrictLabels (Ls0 ∪ A)) G Ls0 T) =
      maxTypingAgreeing (S.restrictLabels (Ls0 ∪ A ∪ B)) G (Ls0 ∪ B)
        (maxTypingAgreeing (S.restrictLabels (Ls0 ∪ B)) G Ls0 T) := by
  have hLs0negA : ∀ L ∈ Ls0, (S.shapeDef L).negDeps ⊆ Ls0 := fun L hL =>
    (Finset.subset_union_right (s₁ := (S.shapeDef L).posDeps)).trans (hLs0self L hL)
  have hLs0posA : ∀ L ∈ Ls0, (S.shapeDef L).posDeps ⊆ Ls0 :=
    fun L hL => (Finset.subset_union_left).trans (hLs0self L hL)
  have hneg2' : ∀ L ∈ Ls0 ∪ A ∪ B, (S.shapeDef L).negDeps ⊆ Ls0 := by
    intro L hL
    simp only [Finset.mem_union] at hL
    rcases hL with (hL | hL) | hL
    · exact hLs0negA L hL
    · exact hAneg L hL
    · exact hBneg L hL
  have hpos1 : ∀ L ∈ Ls0 ∪ A, (S.shapeDef L).posDeps ⊆ Ls0 ∪ A := by
    intro L hL
    simp only [Finset.mem_union] at hL
    rcases hL with hL | hL
    · exact (hLs0posA L hL).trans Finset.subset_union_left
    · exact hApos L hL
  have hpos1' : ∀ L ∈ Ls0 ∪ B, (S.shapeDef L).posDeps ⊆ Ls0 ∪ B := by
    intro L hL
    simp only [Finset.mem_union] at hL
    rcases hL with hL | hL
    · exact (hLs0posA L hL).trans Finset.subset_union_left
    · exact hBpos L hL
  have hLs0LsA : Ls0 ⊆ Ls0 ∪ A := Finset.subset_union_left
  have hLs0LsB : Ls0 ⊆ Ls0 ∪ B := Finset.subset_union_left
  have hLsA2 : Ls0 ∪ A ⊆ Ls0 ∪ A ∪ B := Finset.subset_union_left
  have hLsB2 : Ls0 ∪ B ⊆ Ls0 ∪ A ∪ B := by
    intro x hx
    simp only [Finset.mem_union] at hx ⊢
    tauto
  have hLHS := maxTypingAgreeing_fusion (S := S) (G := G) hLs0LsA hLsA2 hneg2' hpos1
    hTsub hTcorrect
  have hRHS := maxTypingAgreeing_fusion (S := S) (G := G) hLs0LsB hLsB2 hneg2' hpos1'
    hTsub hTcorrect
  rw [hLHS, hRHS]

/-- **Independence**: `cont1`'s final answer, starting from a self-contained
`(Fixed, T)`, doesn't change if we first jump ahead by revealing *any*
other valid batch `C` (not necessarily `remainingMin`'s own choice, and not
necessarily disjoint from `Fixed`) — i.e. `cont1` doesn't actually care
which valid batch its underlying `strat` happens to pick at each step. -/
theorem cont1_indep (S : Schema) (strat : Stratification S) (hClosed : S.Closed) (G : Graph) :
    ∀ Fixed : Finset ShapeLabel, ∀ T : Typing,
      (∀ L ∈ Fixed, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Fixed) →
      T ⊆ (S.restrictLabels Fixed).univTyping G →
      (S.restrictLabels Fixed).CorrectTyping G T →
      ∀ C : Finset ShapeLabel, C ⊆ S.labels →
        (∀ L ∈ C, (S.shapeDef L).negDeps ⊆ Fixed) →
        (∀ L ∈ C, (S.shapeDef L).posDeps ⊆ Fixed ∪ C) →
        cont1 S strat G Fixed T =
          cont1 S strat G (Fixed ∪ C) (maxTypingAgreeing (S.restrictLabels (Fixed ∪ C)) G Fixed T) := by
  intro Fixed
  induction hcard : (S.labels \ Fixed).card using Nat.strong_induction_on generalizing Fixed with
  | _ card ih =>
    intro T hFixedSelf hTsub hTcorrect C hCsub hCneg hCpos
    rcases (C \ Fixed).eq_empty_or_nonempty with hCempty | hCnew
    · have hFixedC : Fixed ∪ C = Fixed := by
        apply Finset.union_eq_left.mpr
        intro x hx
        by_contra hxFixed
        have hxCF : x ∈ C \ Fixed := Finset.mem_sdiff.mpr ⟨hx, hxFixed⟩
        rw [hCempty] at hxCF
        exact absurd hxCF (Finset.notMem_empty x)
      have hMTA : maxTypingAgreeing (S.restrictLabels Fixed) G Fixed T = T :=
        maxTypingAgreeing_self (S' := S.restrictLabels Fixed) hTsub hTcorrect
      rw [hFixedC, hMTA]
    · by_cases hne : (S.labels \ Fixed).Nonempty
      · have hA₁neg := remainingMin_neg strat hClosed Fixed
        have hA₁pos := remainingMin_pos strat hClosed Fixed
        have hA₁ne := remainingMin_nonempty (S := S) (strat := strat.strat) hne
        have hA₁sub : remainingMin S strat.strat Fixed ⊆ S.labels :=
          remainingMin_subset.trans Finset.sdiff_subset
        have hcardA₁ : (S.labels \ (Fixed ∪ remainingMin S strat.strat Fixed)).card < card :=
          hcard ▸ remainingMin_card_lt S strat.strat hne
        set A₁ := remainingMin S strat.strat Fixed with hA₁_def
        -- `Fixed ∪ A₁` is self-contained, and `T_{A₁}` is correct+bounded for it.
        have hFA₁self : ∀ L ∈ Fixed ∪ A₁, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Fixed ∪ A₁ := by
          intro L hL
          simp only [Finset.mem_union] at hL
          rcases hL with hL | hL
          · exact (hFixedSelf L hL).trans Finset.subset_union_left
          · exact Finset.union_subset (hA₁pos L hL) ((hA₁neg L hL).trans Finset.subset_union_left)
        have hFA₁neg : ∀ L ∈ Fixed ∪ A₁, (S.shapeDef L).negDeps ⊆ Fixed := by
          intro L hL
          simp only [Finset.mem_union] at hL
          rcases hL with hL | hL
          · exact (Finset.subset_union_right (s₁ := (S.shapeDef L).posDeps)).trans (hFixedSelf L hL)
          · exact hA₁neg L hL
        have hTsubA₁ : T ⊆ (S.restrictLabels (Fixed ∪ A₁)).univTyping G :=
          hTsub.trans (Schema.univTyping_mono Finset.subset_union_left)
        have hTA₁sub : maxTypingAgreeing (S.restrictLabels (Fixed ∪ A₁)) G Fixed T ⊆
            (S.restrictLabels (Fixed ∪ A₁)).univTyping G := maxTypingAgreeing_subset _ G _ _
        have hTA₁correct : (S.restrictLabels (Fixed ∪ A₁)).CorrectTyping G
            (maxTypingAgreeing (S.restrictLabels (Fixed ∪ A₁)) G Fixed T) :=
          maxTypingAgreeing_correct hTsubA₁ hTcorrect hFA₁neg
        -- First `ih` application: base `Fixed ∪ A₁`, jump `C`.
        have hstep1 := ih _ hcardA₁ (Fixed ∪ A₁) rfl
          (maxTypingAgreeing (S.restrictLabels (Fixed ∪ A₁)) G Fixed T) hFA₁self hTA₁sub hTA₁correct
          C hCsub (fun L hL => (hCneg L hL).trans Finset.subset_union_left)
          (fun L hL => (hCpos L hL).trans (Finset.union_subset_union_left Finset.subset_union_left))
        -- `Fixed ∪ C` is self-contained, and `T''` is correct+bounded for it.
        have hFCself : ∀ L ∈ Fixed ∪ C, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Fixed ∪ C := by
          intro L hL
          simp only [Finset.mem_union] at hL
          rcases hL with hL | hL
          · exact (hFixedSelf L hL).trans Finset.subset_union_left
          · exact Finset.union_subset (hCpos L hL) ((hCneg L hL).trans Finset.subset_union_left)
        have hFCneg : ∀ L ∈ Fixed ∪ C, (S.shapeDef L).negDeps ⊆ Fixed := by
          intro L hL
          simp only [Finset.mem_union] at hL
          rcases hL with hL | hL
          · exact (Finset.subset_union_right (s₁ := (S.shapeDef L).posDeps)).trans (hFixedSelf L hL)
          · exact hCneg L hL
        have hTsubC : T ⊆ (S.restrictLabels (Fixed ∪ C)).univTyping G :=
          hTsub.trans (Schema.univTyping_mono Finset.subset_union_left)
        set T'' := maxTypingAgreeing (S.restrictLabels (Fixed ∪ C)) G Fixed T with hT''_def
        have hT''sub : T'' ⊆ (S.restrictLabels (Fixed ∪ C)).univTyping G := maxTypingAgreeing_subset _ G _ _
        have hT''correct : (S.restrictLabels (Fixed ∪ C)).CorrectTyping G T'' :=
          maxTypingAgreeing_correct hTsubC hTcorrect hFCneg
        have hcardC : (S.labels \ (Fixed ∪ C)).card < card := by
          rw [← hcard]
          apply Finset.card_lt_card
          constructor
          · intro x hx
            simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
            tauto
          · intro hsub
            obtain ⟨L₀, hL₀⟩ := hCnew
            obtain ⟨hL₀C, hL₀nFixed⟩ := Finset.mem_sdiff.mp hL₀
            have hL₀rem : L₀ ∈ S.labels \ Fixed := Finset.mem_sdiff.mpr ⟨hCsub hL₀C, hL₀nFixed⟩
            have hcontra := hsub hL₀rem
            simp only [Finset.mem_sdiff, Finset.mem_union] at hcontra
            exact hcontra.2 (Or.inr hL₀C)
        -- Second `ih` application: base `Fixed ∪ C`, jump `A₁`.
        have hstep2 := ih _ hcardC (Fixed ∪ C) rfl T'' hFCself hT''sub hT''correct
          A₁ hA₁sub (fun L hL => (hA₁neg L hL).trans Finset.subset_union_left)
          (fun L hL => (hA₁pos L hL).trans (Finset.union_subset_union_left Finset.subset_union_left))
        -- Combine via `cont1_step` and `maxTypingAgreeing_swap`.
        have hswap := maxTypingAgreeing_swap (S := S) (G := G) (Ls0 := Fixed) (A := A₁) (B := C)
          hFixedSelf hA₁neg hA₁pos hCneg hCpos hTsub hTcorrect
        have hcomm : Fixed ∪ A₁ ∪ C = Fixed ∪ C ∪ A₁ := by
          apply Finset.ext; intro x; simp only [Finset.mem_union]; tauto
        rw [cont1_step S strat G hne T]
        calc cont1 S strat G (Fixed ∪ A₁) (maxTypingAgreeing (S.restrictLabels (Fixed ∪ A₁)) G Fixed T)
            = cont1 S strat G ((Fixed ∪ A₁) ∪ C)
                (maxTypingAgreeing (S.restrictLabels ((Fixed ∪ A₁) ∪ C)) G (Fixed ∪ A₁)
                  (maxTypingAgreeing (S.restrictLabels (Fixed ∪ A₁)) G Fixed T)) := hstep1
          _ = cont1 S strat G ((Fixed ∪ A₁) ∪ C)
                (maxTypingAgreeing (S.restrictLabels ((Fixed ∪ A₁) ∪ C)) G (Fixed ∪ C) T'') := by
                rw [hswap]
          _ = cont1 S strat G (Fixed ∪ C) T'' := hcomm ▸ hstep2.symm
      · -- Nothing left at all: `Fixed ⊇ S.labels`, so `C ⊆ Fixed` too, contradicting `hCnew`.
        exfalso
        obtain ⟨L₀, hL₀⟩ := hCnew
        obtain ⟨hL₀C, hL₀nFixed⟩ := Finset.mem_sdiff.mp hL₀
        exact hne ⟨L₀, Finset.mem_sdiff.mpr ⟨hCsub hL₀C, hL₀nFixed⟩⟩

/-- Chain `cont1_indep` along `strat'`'s own checkpoints: `cont1`, built
using *any* fixed `strat0` internally, agrees with `strat'` at every one of
`strat'`'s own checkpoints — regardless of `strat0`. -/
theorem cont1_chain (S : Schema) (strat0 : Stratification S) (hClosed : S.Closed) (G : Graph)
    (strat' : Stratification S) :
    ∀ i ≤ strat'.k,
      cont1 S strat0 G ∅ ∅ = cont1 S strat0 G (S.stratum strat'.strat i)
        (stratTypingSeq S strat'.strat G i)
  | 0, _ => by simp [Schema.stratum_zero, stratTypingSeq]
  | (i + 1), hi1 => by
      have hi : i ≤ strat'.k := by omega
      have hIH := cont1_chain S strat0 hClosed G strat' i hi
      have hT' := stratTypingSeq_correct S strat' hClosed G i
      have hself : ∀ L ∈ S.stratum strat'.strat i,
          (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ S.stratum strat'.strat i :=
        Schema.stratum_self_contained S strat' hClosed i
      set C := S.stratum strat'.strat (i + 1) \ S.stratum strat'.strat i with hC_def
      have hCsub : C ⊆ S.labels := (Finset.sdiff_subset).trans (fun L hL =>
        (Finset.mem_filter.mp hL).1)
      have hUnion : S.stratum strat'.strat i ∪ C = S.stratum strat'.strat (i + 1) := by
        rw [hC_def, Finset.union_sdiff_of_subset (Schema.stratum_mono (by omega))]
      have hCneg : ∀ L ∈ C, (S.shapeDef L).negDeps ⊆ S.stratum strat'.strat i := by
        intro L hL
        have hL' : L ∈ S.stratum strat'.strat (i + 1) := hUnion ▸ Finset.mem_union_right _ hL
        exact Schema.stratum_neg_confined S strat' hClosed (i + 1) L hL' |>.trans
          (by rw [show i + 1 - 1 = i by omega])
      have hCpos : ∀ L ∈ C, (S.shapeDef L).posDeps ⊆ S.stratum strat'.strat i ∪ C := by
        intro L hL
        rw [hUnion]
        have hL' : L ∈ S.stratum strat'.strat (i + 1) := hUnion ▸ Finset.mem_union_right _ hL
        exact Finset.subset_union_left.trans
          (Schema.stratum_self_contained S strat' hClosed (i + 1) L hL')
      have hindep := cont1_indep S strat0 hClosed G (S.stratum strat'.strat i)
        (stratTypingSeq S strat'.strat G i) hself hT'.1 hT'.2 C hCsub hCneg hCpos
      rw [hIH, hindep, hUnion]
      congr 1

/-- `cont1 S strat0 G ∅ ∅` equals `Typing4` for *any* valid stratification —
so, in particular, for both `strat1` and `strat2`. -/
theorem cont1_eq_Typing4 (S : Schema) (strat0 : Stratification S) (hClosed : S.Closed) (G : Graph)
    (strat' : Stratification S) : cont1 S strat0 G ∅ ∅ = Typing4 G S strat' := by
  have h := cont1_chain S strat0 hClosed G strat' strat'.k (le_refl _)
  rw [h]
  apply cont1_done
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset]
  intro L hL
  simp only [Schema.stratum, Finset.mem_filter]
  exact ⟨hL, (strat'.mem_range L hL).2⟩

/-- Lemma 2. `Typing(G, S, strat)` (Definition 4) does not depend on which
stratification of `S` is chosen: both sides equal `cont1 S strat1 G ∅ ∅`,
a canonical process built by always revealing every "ready" label
(`remainingMin`) — independent of which valid stratification is used to
justify each step (`cont1_indep`). -/
theorem lemma2 (S : Schema) (hClosed : S.Closed) (strat1 strat2 : Stratification S) (G : Graph) :
    Typing4 G S strat1 = Typing4 G S strat2 := by
  rw [← cont1_eq_Typing4 S strat1 hClosed G strat1, ← cont1_eq_Typing4 S strat1 hClosed G strat2]

end ShexLean
