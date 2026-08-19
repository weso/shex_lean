import ShexLean.Shex2017Schemas.Proposition1
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Max

/-!
Lemma 2 (§3.3): `Typing(G, S, str)` (Definition 4) does not depend on
which stratification `str` of `S` is chosen.

The paper only sketches this proof ("Proof. (Idea)..."): it asserts a
canonical "most refined" stratification exists and that every
stratification agrees with it, without justifying why. This file gives a
full independent proof:

- `maxAgree_fusion`: revealing a schema's labels in one batch or in two
  nested batches gives the same `maxAgree` result.
- `combStrat` / `MTyping_combStrat`: a "lex-combine" stratification and
  refinement invariance along it. Not needed by the final proof, but kept
  as an independently useful fact. Exact checkpoint alignment with an
  arbitrary second stratification is not possible in general (two
  mutually independent labels can be ordered differently by different
  valid stratifications), which is why the general proof takes a
  different route below.
- `maxAgree_swap`: two batches that each individually depend only on a
  common base (not on each other) can be revealed in either order with
  the same result, by two applications of Fusion.
- `remMin` / `cont1`: a canonical process that, starting from `∅`,
  repeatedly reveals the least-`str`-valued remaining batch (for some
  arbitrarily fixed valid stratification, used only to make each step
  well-defined) until every label is settled.
- `cont1_indep`: `cont1`'s final answer does not change if the first step
  instead reveals any other valid batch. Proved by strong induction on
  the number of remaining labels, using Swap to reconcile `cont1`'s own
  next step against the alternative one.
- `cont1_chain` / `cont1_eq_MTyping`: chaining `cont1_indep` along any
  valid stratification's own checkpoints shows `cont1 S _ G ∅ ∅ =
  MTyping G S str'` for that stratification, so `str1` and `str2` both
  equal the same `cont1` value, giving `lemma2`.
-/

namespace ShexLean

/-- For any valid stratification, a stratum-checkpoint is self-contained:
every label in `S.stratum str i` has both its positive and negative
dependencies confined within that same checkpoint. (Negative dependencies
land strictly inside `S.stratum str (i-1)`, but later lemmas only need
the weaker `⊆ S.stratum str i` bound.) -/
theorem Schema.stratum_self_contained (S : Schema) (str : Strat S)
    (hClosed : S.Closed) (i : ℕ) :
    ∀ L ∈ S.stratum str.str i,
      (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ S.stratum str.str i := by
  intro L hL L2 hL2
  simp only [Schema.stratum, Finset.mem_filter] at hL ⊢
  obtain ⟨hLlabels, hLstrat⟩ := hL
  have hL2labels : L2 ∈ S.labels := hClosed L hLlabels hL2
  rcases Finset.mem_union.mp hL2 with hpos | hneg
  · exact ⟨hL2labels, (str.pos_le L hLlabels L2 hpos).trans hLstrat⟩
  · exact ⟨hL2labels, (le_of_lt (str.neg_strict L hLlabels L2 hneg)).trans hLstrat⟩

/-- `S` restricted to an arbitrary label set `Ls` (not necessarily a
stratum-checkpoint of any particular stratification), keeping the same
definitions. Generalizes `Schema.stratRestrict`. -/
def Schema.restrictLabels (S : Schema) (Ls : Finset Label) : Schema where
  labels := Ls
  shapeDef := S.shapeDef

theorem Typing.restrictTo_mono {t t' : Typing} {Lo : Finset Label} (h : t ⊆ t') :
    t.restrictTo Lo ⊆ t'.restrictTo Lo := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := Typing.mem_restrictTo.mp hp
  exact Typing.mem_restrictTo.mpr ⟨h hp1, hp2⟩

/-- Restricting to `Lo₂ ⊆ Lo₁` and then to `Lo₂` again is the same as
restricting to `Lo₂` directly. -/
theorem Typing.restrictTo_restrictTo {t : Typing} {Lo₁ Lo₂ : Finset Label}
    (h : Lo₂ ⊆ Lo₁) : (t.restrictTo Lo₁).restrictTo Lo₂ = t.restrictTo Lo₂ := by
  apply Finset.ext
  rintro ⟨n, L⟩
  simp only [Typing.mem_restrictTo]
  constructor
  · rintro ⟨⟨htmem, _⟩, hL⟩
    exact ⟨htmem, hL⟩
  · rintro ⟨htmem, hL⟩
    exact ⟨⟨htmem, h hL⟩, hL⟩

theorem Schema.univTyping_mono {S : Schema} {G : Graph} {Ls Ls' : Finset Label}
    (h : Ls ⊆ Ls') : (S.restrictLabels Ls).univTyping G ⊆ (S.restrictLabels Ls').univTyping G := by
  intro p hp
  simp only [Schema.univTyping, Schema.restrictLabels] at hp ⊢
  exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).1, h (Finset.mem_product.mp hp).2⟩

/-- A typing correct for a schema stays correct when restricted to a
self-contained (both `posDeps` and `negDeps` confined within it) subset of
labels, via `Satisfies.agree`. -/
theorem restrictLabels_correct_restrictTo {S : Schema} {G : Graph} {Ls1 Ls2 : Finset Label}
    {t : Typing}
    (hself : ∀ L ∈ Ls1, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Ls1)
    (ht : (S.restrictLabels Ls2).CorrTyping G t) :
    (S.restrictLabels Ls1).CorrTyping G (t.restrictTo Ls1) := by
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

/-- Fusion: revealing `Ls₂` in one shot (`Lo = Ls`) agrees with revealing
it in two stages through the intermediate checkpoint `Ls₁` (`Lo = Ls` then
`Lo = Ls₁`), provided everything new in `Ls₂` only negatively depends on
`Ls`, and `Ls₁` is self-contained under positive dependencies. Both hold
automatically when `Ls ⊆ Ls₁ ⊆ Ls₂` are stratum-checkpoints of the same
stratification (`Schema.stratum_self_contained`).

The proof shows each side, as a whole object, is a valid candidate for
the other's `maxAgree` construction; a per-candidate argument does not
work since an individual correct typing of `Ls₁` need not be maximal
there. -/
theorem maxAgree_fusion {S : Schema} {G : Graph} {Ls Ls1 Ls2 : Finset Label}
    {T : Typing} (hLsLs1 : Ls ⊆ Ls1) (hLs1Ls2 : Ls1 ⊆ Ls2)
    (hneg2 : ∀ L ∈ Ls2, (S.shapeDef L).negDeps ⊆ Ls)
    (hpos1 : ∀ L ∈ Ls1, (S.shapeDef L).posDeps ⊆ Ls1)
    (hTsub : T ⊆ (S.restrictLabels Ls).univTyping G)
    (hTcorrect : (S.restrictLabels Ls).CorrTyping G T) :
    maxAgree (S.restrictLabels Ls2) G Ls1
        (maxAgree (S.restrictLabels Ls1) G Ls T) =
      maxAgree (S.restrictLabels Ls2) G Ls T := by
  set A := maxAgree (S.restrictLabels Ls1) G Ls T with hA_def
  set B := maxAgree (S.restrictLabels Ls2) G Ls1 A with hB_def
  set C := maxAgree (S.restrictLabels Ls2) G Ls T with hC_def
  have hTsub1 : T ⊆ (S.restrictLabels Ls1).univTyping G :=
    hTsub.trans (Schema.univTyping_mono hLsLs1)
  have hTcorrect1 : (S.restrictLabels Ls1).CorrTyping G T := hTcorrect
  have hTsub2 : T ⊆ (S.restrictLabels Ls2).univTyping G :=
    hTsub.trans (Schema.univTyping_mono (hLsLs1.trans hLs1Ls2))
  have hTcorrect2 : (S.restrictLabels Ls2).CorrTyping G T := hTcorrect
  have hAsub1 : A ⊆ (S.restrictLabels Ls1).univTyping G := maxAgree_subset _ G _ _
  have hAcorrect1 : (S.restrictLabels Ls1).CorrTyping G A :=
    maxAgree_correct hTsub1 hTcorrect1 (fun L hL => hneg2 L (hLs1Ls2 hL))
  have hArestrict : A.restrictTo Ls = T.restrictTo Ls :=
    maxAgree_restrictTo hTsub1 hTcorrect1
  have hAsub2 : A ⊆ (S.restrictLabels Ls2).univTyping G := hAsub1.trans (Schema.univTyping_mono hLs1Ls2)
  have hAcorrect2 : (S.restrictLabels Ls2).CorrTyping G A := hAcorrect1
  -- `A` is itself a valid `C`-candidate.
  have hAC : A ⊆ C := subset_maxAgree hAsub2 hAcorrect2 hArestrict
  have hBsub2 : B ⊆ (S.restrictLabels Ls2).univTyping G := maxAgree_subset _ G _ _
  have hBcorrect2 : (S.restrictLabels Ls2).CorrTyping G B :=
    maxAgree_correct hAsub2 hAcorrect2 (fun L hL => (hneg2 L hL).trans hLsLs1)
  have hBrestrict1 : B.restrictTo Ls1 = A.restrictTo Ls1 :=
    maxAgree_restrictTo hAsub2 hAcorrect2
  -- `B ⊆ C`.
  have hBC : B ⊆ C := by
    apply subset_maxAgree hBsub2 hBcorrect2
    rw [← Typing.restrictTo_restrictTo (t := B) hLsLs1, hBrestrict1,
      Typing.restrictTo_restrictTo (t := A) hLsLs1, hArestrict]
  -- `C ⊆ B`.
  have hCB : C ⊆ B := by
    have hCsub2 : C ⊆ (S.restrictLabels Ls2).univTyping G := maxAgree_subset _ G _ _
    have hCcorrect2 : (S.restrictLabels Ls2).CorrTyping G C :=
      maxAgree_correct hTsub2 hTcorrect2 hneg2
    have hCrestrict : C.restrictTo Ls = T.restrictTo Ls := maxAgree_restrictTo hTsub2 hTcorrect2
    have hself1 : ∀ L ∈ Ls1, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Ls1 := by
      intro L hL
      apply Finset.union_subset (hpos1 L hL)
      exact (hneg2 L (hLs1Ls2 hL)).trans hLsLs1
    have hCL1correct : (S.restrictLabels Ls1).CorrTyping G (C.restrictTo Ls1) :=
      restrictLabels_correct_restrictTo hself1 hCcorrect2
    have hCL1sub : C.restrictTo Ls1 ⊆ (S.restrictLabels Ls1).univTyping G := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Typing.mem_restrictTo.mp hp
      simp only [Schema.univTyping, Schema.restrictLabels] at hCsub2 ⊢
      exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp (hCsub2 hp1)).1, hp2⟩
    have hCL1restrict : (C.restrictTo Ls1).restrictTo Ls = T.restrictTo Ls := by
      rw [Typing.restrictTo_restrictTo hLsLs1, hCrestrict]
    have hCL1A : C.restrictTo Ls1 ⊆ A := subset_maxAgree hCL1sub hCL1correct hCL1restrict
    have hCL1eqA : C.restrictTo Ls1 = A.restrictTo Ls1 := by
      apply Finset.Subset.antisymm
      · intro p hp
        obtain ⟨hp1, hp2⟩ := Typing.mem_restrictTo.mp hp
        exact Typing.mem_restrictTo.mpr ⟨hCL1A (Typing.mem_restrictTo.mpr ⟨hp1, hp2⟩), hp2⟩
      · exact Typing.restrictTo_mono hAC
    exact subset_maxAgree hCsub2 hCcorrect2 hCL1eqA
  exact Finset.Subset.antisymm hBC hCB

/-- Sharper than `Schema.stratum_self_contained` on the negative side: a
label's negative dependencies land strictly *inside the previous*
checkpoint, not just inside its own. -/
theorem Schema.stratum_neg_confined (S : Schema) (str : Strat S)
    (hClosed : S.Closed) (i : ℕ) :
    ∀ L ∈ S.stratum str.str i, (S.shapeDef L).negDeps ⊆ S.stratum str.str (i - 1) := by
  intro L hL L2 hL2
  simp only [Schema.stratum, Finset.mem_filter] at hL ⊢
  obtain ⟨hLlabels, hLstrat⟩ := hL
  have hL2labels : L2 ∈ S.labels := hClosed L hLlabels (Finset.mem_union_right _ hL2)
  have := str.neg_strict L hLlabels L2 hL2
  exact ⟨hL2labels, by omega⟩

theorem Schema.stratum_zero (S : Schema) (str : Strat S) :
    S.stratum str.str 0 = ∅ := by
  unfold Schema.stratum
  rw [Finset.filter_eq_empty_iff]
  intro L hL hle
  have := (str.mem_range L hL).1
  omega

/-- `maxAgree` is a no-op when asked to reveal exactly the schema
`fixed` is already correct+bounded for: the only self-agreeing candidate is
`fixed` itself. -/
theorem maxAgree_self {S' : Schema} {G : Graph} {T : Typing}
    (hTsub : T ⊆ S'.univTyping G) (hTcorrect : S'.CorrTyping G T) :
    maxAgree S' G S'.labels T = T := by
  apply Finset.Subset.antisymm
  · have := Classical.decPred (fun t => S'.CorrTyping G t ∧ t.restrictTo S'.labels = T.restrictTo S'.labels)
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
  · exact subset_maxAgree hTsub hTcorrect rfl

/-!
The combined ("lex-refined") stratification: `str1` as the primary key,
`str2` as a tiebreak. Its checkpoints at multiples of `str2.k + 1`
recover `str1`'s own checkpoints, which lets it relate `MTyping str1` to
`MTyping` of a stratification built from both `str1` and `str2`.
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

/-- `str1` as primary key, `str2` as tiebreak. -/
noncomputable def combStrat {S : Schema} (hClosed : S.Closed) (str1 str2 : Strat S) :
    Strat S where
  k := str1.k * (str2.k + 1)
  str := fun L => (str1.str L - 1) * (str2.k + 1) + str2.str L
  mem_range := by
    intro L hL
    obtain ⟨h1lo, h1hi⟩ := str1.mem_range L hL
    obtain ⟨h2lo, h2hi⟩ := str2.mem_range L hL
    exact ⟨by omega, lex_upper h1lo h1hi h2hi⟩
  neg_strict := by
    intro L1 hL1 L2 hdep
    have h1 := str1.neg_strict L1 hL1 L2 hdep
    have hL2 : L2 ∈ S.labels := hClosed L1 hL1 (Finset.mem_union_right _ hdep)
    obtain ⟨h1lo, -⟩ := str1.mem_range L1 hL1
    obtain ⟨h1lo', -⟩ := str1.mem_range L2 hL2
    obtain ⟨-, h2hi⟩ := str2.mem_range L1 hL1
    obtain ⟨-, h2hi'⟩ := str2.mem_range L2 hL2
    exact lex_strict_mono h1lo h1lo' h2hi h2hi' h1
  pos_le := by
    intro L1 hL1 L2 hdep
    have h1 := str1.pos_le L1 hL1 L2 hdep
    have hL2 : L2 ∈ S.labels := hClosed L1 hL1 (Finset.mem_union_left _ hdep)
    obtain ⟨h1lo, -⟩ := str1.mem_range L1 hL1
    obtain ⟨h1lo', -⟩ := str1.mem_range L2 hL2
    obtain ⟨-, h2hi⟩ := str2.mem_range L1 hL1
    obtain ⟨-, h2hi'⟩ := str2.mem_range L2 hL2
    refine lex_le h1lo h1lo' h2hi h2hi' h1 (fun heq => ?_)
    have h2 := str2.pos_le L1 hL1 L2 hdep
    exact h2

theorem stratum_combStrat_align {S : Schema} (hClosed : S.Closed)
    (str1 str2 : Strat S) (i : ℕ) :
    S.stratum str1.str i = S.stratum (combStrat hClosed str1 str2).str (i * (str2.k + 1)) := by
  apply Finset.ext
  intro L
  simp only [Schema.stratum, Finset.mem_filter]
  constructor
  · rintro ⟨hL, hle⟩
    refine ⟨hL, ?_⟩
    show (str1.str L - 1) * (str2.k + 1) + str2.str L ≤ i * (str2.k + 1)
    obtain ⟨-, h2hi⟩ := str2.mem_range L hL
    obtain ⟨h1lo, -⟩ := str1.mem_range L hL
    obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le h1lo
    have he : str1.str L - 1 = a' := by omega
    rw [he]
    have : a' + 1 ≤ i := by omega
    have hmul : (a' + 1) * (str2.k + 1) ≤ i * (str2.k + 1) := Nat.mul_le_mul this (le_refl _)
    have : a' * (str2.k + 1) + str2.str L < (a' + 1) * (str2.k + 1) := by
      calc a' * (str2.k + 1) + str2.str L ≤ a' * (str2.k + 1) + str2.k := by omega
        _ < a' * (str2.k + 1) + (str2.k + 1) := by omega
        _ = (a' + 1) * (str2.k + 1) := by ring
    omega
  · rintro ⟨hL, hle⟩
    refine ⟨hL, ?_⟩
    show str1.str L ≤ i
    obtain ⟨h1lo, -⟩ := str1.mem_range L hL
    obtain ⟨h2lo, h2hi⟩ := str2.mem_range L hL
    obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le h1lo
    have he : str1.str L - 1 = a' := by omega
    change (str1.str L - 1) * (str2.k + 1) + str2.str L ≤ i * (str2.k + 1) at hle
    rw [he] at hle
    by_contra hcon
    push Not at hcon
    have : i + 1 ≤ a' + 1 := by omega
    have hmul : i * (str2.k + 1) + (str2.k + 1) ≤ (a' + 1) * (str2.k + 1) :=
      calc i * (str2.k + 1) + (str2.k + 1) = (i + 1) * (str2.k + 1) := by ring
        _ ≤ (a' + 1) * (str2.k + 1) := Nat.mul_le_mul this (le_refl _)
    have hexpand : (a' + 1) * (str2.k + 1) = a' * (str2.k + 1) + (str2.k + 1) := by ring
    omega

/-- Refinement invariance: `MTyping` under `str1` agrees with `MTyping`
under `combStrat hClosed str1 str2` (which refines `str1` exactly, at
multiples of `str2.k + 1`). Proved by induction on `str1`'s strata, with
an inner induction (via repeated `maxAgree_fusion`) over the `str2.k + 1`
finer steps `combStrat` takes within each `str1`-layer. -/
theorem typ_combStrat_align {S : Schema} (hClosed : S.Closed)
    (str1 str2 : Strat S) (G : Graph) :
    ∀ i ≤ str1.k,
      typ S (combStrat hClosed str1 str2).str G (i * (str2.k + 1)) =
        typ S str1.str G i
  | 0, _ => by simp [typ]
  | (i + 1), hi1 => by
      have hi : i ≤ str1.k := by omega
      have houter := typ_combStrat_align hClosed str1 str2 G i hi
      have hT1 := typ_correct S str1 hClosed G i
      have halign : ∀ i' : ℕ, S.stratum str1.str i' =
          S.stratum (combStrat hClosed str1 str2).str (i' * (str2.k + 1)) :=
        stratum_combStrat_align hClosed str1 str2
      set combined := combStrat hClosed str1 str2 with hcombined_def
      set Ls := S.stratum str1.str i with hLs_def
      set T := typ S str1.str G i with hT_def
      have hTsub : T ⊆ (S.restrictLabels Ls).univTyping G := hT1.1
      have hTcorrect : (S.restrictLabels Ls).CorrTyping G T := hT1.2
      have inner : ∀ j, j ≤ str2.k →
          typ S combined.str G (i * (str2.k + 1) + j) =
            maxAgree (S.restrictLabels (S.stratum combined.str (i * (str2.k + 1) + j)))
              G Ls T := by
        intro j
        induction j with
        | zero =>
            intro _
            rw [Nat.add_zero, ← halign i, houter]
            exact (maxAgree_self hTsub hTcorrect).symm
        | succ j ihj =>
            intro hj1
            have hj : j ≤ str2.k := by omega
            have hj' := ihj hj
            set Ls1 := S.stratum combined.str (i * (str2.k + 1) + j) with hLs1_def
            set Ls2 := S.stratum combined.str (i * (str2.k + 1) + (j + 1)) with hLs2_def
            have hLs1Ls2 : Ls1 ⊆ Ls2 := by
              rw [hLs1_def, hLs2_def]; apply Schema.stratum_mono; omega
            have hLsLs1 : Ls ⊆ Ls1 := by
              rw [hLs_def, halign i, hLs1_def]; apply Schema.stratum_mono; omega
            have hLs2sub1 : Ls2 ⊆ S.stratum str1.str (i + 1) := by
              rw [hLs2_def, halign (i + 1)]
              apply Schema.stratum_mono
              have : i * (str2.k + 1) + (j + 1) ≤ i * (str2.k + 1) + (str2.k + 1) := by omega
              have heq : i * (str2.k + 1) + (str2.k + 1) = (i + 1) * (str2.k + 1) := by ring
              omega
            have hneg2 : ∀ L ∈ Ls2, (S.shapeDef L).negDeps ⊆ Ls := by
              intro L hL
              have := Schema.stratum_neg_confined S str1 hClosed (i + 1) L (hLs2sub1 hL)
              simpa using this
            have hpos1 : ∀ L ∈ Ls1, (S.shapeDef L).posDeps ⊆ Ls1 := by
              intro L hL
              exact Finset.subset_union_left.trans
                (Schema.stratum_self_contained S combined hClosed
                  (i * (str2.k + 1) + j) L hL)
            have hfusion := maxAgree_fusion (S := S) (G := G) hLsLs1 hLs1Ls2
              hneg2 hpos1 hTsub hTcorrect
            have hstep : typ S combined.str G (i * (str2.k + 1) + (j + 1)) =
                maxAgree (S.restrictLabels Ls2) G Ls1
                  (typ S combined.str G (i * (str2.k + 1) + j)) := by
              have heq : i * (str2.k + 1) + (j + 1) = (i * (str2.k + 1) + j) + 1 := by omega
              rw [heq]; rfl
            calc typ S combined.str G (i * (str2.k + 1) + (j + 1))
                = maxAgree (S.restrictLabels Ls2) G Ls1
                    (typ S combined.str G (i * (str2.k + 1) + j)) := hstep
              _ = maxAgree (S.restrictLabels Ls2) G Ls1
                    (maxAgree (S.restrictLabels Ls1) G Ls T) := by rw [hj']
              _ = maxAgree (S.restrictLabels Ls2) G Ls T := hfusion
      have hk2 := inner str2.k (le_refl _)
      have hLs1last : S.stratum combined.str (i * (str2.k + 1) + str2.k) ⊆
          S.stratum str1.str (i + 1) := by
        rw [halign (i + 1)]
        apply Schema.stratum_mono
        have heq : i * (str2.k + 1) + (str2.k + 1) = (i + 1) * (str2.k + 1) := by ring
        omega
      have hLsLs1last : Ls ⊆ S.stratum combined.str (i * (str2.k + 1) + str2.k) := by
        rw [hLs_def, halign i]
        apply Schema.stratum_mono
        omega
      have hneg2last : ∀ L ∈ S.stratum str1.str (i + 1), (S.shapeDef L).negDeps ⊆ Ls := by
        intro L hL
        have := Schema.stratum_neg_confined S str1 hClosed (i + 1) L hL
        simpa using this
      have hpos1last : ∀ L ∈ S.stratum combined.str (i * (str2.k + 1) + str2.k),
          (S.shapeDef L).posDeps ⊆ S.stratum combined.str (i * (str2.k + 1) + str2.k) := by
        intro L hL
        exact Finset.subset_union_left.trans
          (Schema.stratum_self_contained S combined hClosed (i * (str2.k + 1) + str2.k) L hL)
      have hfusionlast := maxAgree_fusion (S := S) (G := G) hLsLs1last
        (halign (i + 1) ▸ hLs1last) (halign (i + 1) ▸ hneg2last) hpos1last hTsub hTcorrect
      have hstep : typ S combined.str G ((i + 1) * (str2.k + 1)) =
          maxAgree (S.restrictLabels (S.stratum combined.str ((i + 1) * (str2.k + 1)))) G
            (S.stratum combined.str (i * (str2.k + 1) + str2.k))
            (typ S combined.str G (i * (str2.k + 1) + str2.k)) := by
        have heq : (i + 1) * (str2.k + 1) = (i * (str2.k + 1) + str2.k) + 1 := by ring
        rw [heq]; rfl
      calc typ S combined.str G ((i + 1) * (str2.k + 1))
          = maxAgree (S.restrictLabels (S.stratum combined.str ((i + 1) * (str2.k + 1)))) G
              (S.stratum combined.str (i * (str2.k + 1) + str2.k))
              (typ S combined.str G (i * (str2.k + 1) + str2.k)) := hstep
        _ = maxAgree (S.restrictLabels (S.stratum combined.str ((i + 1) * (str2.k + 1)))) G
              (S.stratum combined.str (i * (str2.k + 1) + str2.k))
              (maxAgree (S.restrictLabels (S.stratum combined.str
                (i * (str2.k + 1) + str2.k))) G Ls T) := by rw [hk2]
        _ = maxAgree (S.restrictLabels (S.stratum combined.str ((i + 1) * (str2.k + 1)))) G
              Ls T := hfusionlast
        _ = maxAgree (S.restrictLabels (S.stratum str1.str (i + 1))) G Ls T := by
              rw [halign (i + 1)]
        _ = typ S str1.str G (i + 1) := rfl

/-- `combStrat hClosed str1 str2` reduces to `MTyping G S str1`: the
`i = str1.k` instance of `typ_combStrat_align`, phrased via `MTyping`. -/
theorem MTyping_combStrat (S : Schema) (hClosed : S.Closed)
    (str1 str2 : Strat S) (G : Graph) :
    MTyping G S (combStrat hClosed str1 str2) = MTyping G S str1 := by
  show typ S (combStrat hClosed str1 str2).str G
      (str1.k * (str2.k + 1)) = typ S str1.str G str1.k
  exact typ_combStrat_align hClosed str1 str2 G str1.k (le_refl _)

/-!
Lemma 2, general statement.

`combStrat hClosed str1 str2` aligns with `str1`'s checkpoints but not
`str2`'s in general: two mutually independent labels (no dependency edge
either way) can be ordered differently by different valid
stratifications, so no single fixed combination aligns with an arbitrary
second stratification. Instead, we define one canonical process that at
each step reveals some valid next batch (not tied to `str1` or `str2`),
and show its final result doesn't depend on which valid batch was chosen
at each step (`cont1_indep` below, via `maxAgree_swap`). That process's
final value equals `MTyping str1` by walking it through `str1`'s own
checkpoints (each such step is a valid batch choice), and likewise for
`str2`, giving `MTyping str1 = MTyping str2` without needing `str1` and
`str2` to agree on any intermediate checkpoint.
-/

/-- The labels of least `str`-value among those not yet in `Fixed`: a
canonical (but not the only valid) choice of "next batch". Nonempty
whenever labels remain, and confined the way `maxAgree`'s construction
needs (shown below). -/
def remMin (S : Schema) (str : Label → ℕ) (Fixed : Finset Label) :
    Finset Label :=
  (S.labels \ Fixed).filter (fun L => ∀ L' ∈ S.labels \ Fixed, str L ≤ str L')

theorem remMin_subset {S : Schema} {str : Label → ℕ} {Fixed : Finset Label} :
    remMin S str Fixed ⊆ S.labels \ Fixed := Finset.filter_subset _ _

theorem remMin_nonempty {S : Schema} {str : Label → ℕ} {Fixed : Finset Label}
    (h : (S.labels \ Fixed).Nonempty) : (remMin S str Fixed).Nonempty := by
  obtain ⟨L₀, hL₀, hmin⟩ := Finset.exists_min_image (S.labels \ Fixed) str h
  exact ⟨L₀, Finset.mem_filter.mpr ⟨hL₀, hmin⟩⟩

/-- `remMin`'s batch (for any valid stratification `str`) only
negatively depends on `Fixed`. -/
theorem remMin_neg {S : Schema} (str : Strat S) (hClosed : S.Closed)
    (Fixed : Finset Label) :
    ∀ L ∈ remMin S str.str Fixed, (S.shapeDef L).negDeps ⊆ Fixed := by
  intro L hL L2 hL2
  obtain ⟨hLrem, hLmin⟩ := Finset.mem_filter.mp hL
  obtain ⟨hLlabels, hLnotFixed⟩ := Finset.mem_sdiff.mp hLrem
  have hL2labels : L2 ∈ S.labels := hClosed L hLlabels (Finset.mem_union_right _ hL2)
  by_contra hL2notFixed
  have hL2rem : L2 ∈ S.labels \ Fixed := Finset.mem_sdiff.mpr ⟨hL2labels, hL2notFixed⟩
  have h1 := str.neg_strict L hLlabels L2 hL2
  have h2 := hLmin L2 hL2rem
  omega

/-- `Fixed ∪ remMin str Fixed` is self-contained under positive
dependencies. -/
theorem remMin_pos {S : Schema} (str : Strat S) (hClosed : S.Closed)
    (Fixed : Finset Label) :
    ∀ L ∈ remMin S str.str Fixed,
      (S.shapeDef L).posDeps ⊆ Fixed ∪ remMin S str.str Fixed := by
  intro L hL L2 hL2
  obtain ⟨hLrem, hLmin⟩ := Finset.mem_filter.mp hL
  obtain ⟨hLlabels, hLnotFixed⟩ := Finset.mem_sdiff.mp hLrem
  have hL2labels : L2 ∈ S.labels := hClosed L hLlabels (Finset.mem_union_left _ hL2)
  by_cases hL2Fixed : L2 ∈ Fixed
  · exact Finset.mem_union_left _ hL2Fixed
  · refine Finset.mem_union_right _ ?_
    have hL2rem : L2 ∈ S.labels \ Fixed := Finset.mem_sdiff.mpr ⟨hL2labels, hL2Fixed⟩
    have h1 := str.pos_le L hLlabels L2 hL2
    have h2 := hLmin L2 hL2rem
    refine Finset.mem_filter.mpr ⟨hL2rem, fun L' hL' => ?_⟩
    have h3 := hLmin L' hL'
    omega

/-- Repeatedly reveal `str`'s `remMin` batch, `n` times (or until
nothing is left — `n` is fuel, not meant to be tight). -/
noncomputable def cont1Fuel (S : Schema) (str : Strat S) (G : Graph) :
    ℕ → Finset Label → Typing → Typing
  | 0, _, T => T
  | (n + 1), Fixed, T =>
      if (S.labels \ Fixed).Nonempty then
        cont1Fuel S str G n (Fixed ∪ remMin S str.str Fixed)
          (maxAgree (S.restrictLabels (Fixed ∪ remMin S str.str Fixed)) G
            Fixed T)
      else T

/-- `S.labels \ (Fixed ∪ remMin ...)` is strictly smaller than
`S.labels \ Fixed`. -/
private theorem remMin_card_lt (S : Schema) (str : Label → ℕ)
    {Fixed : Finset Label} (h : (S.labels \ Fixed).Nonempty) :
    (S.labels \ (Fixed ∪ remMin S str Fixed)).card < (S.labels \ Fixed).card := by
  have hBnonempty := remMin_nonempty (S := S) (str := str) h
  apply Finset.card_lt_card
  constructor
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    tauto
  · intro hsub
    obtain ⟨L₀, hL₀⟩ := hBnonempty
    have hL₀rem := remMin_subset (S := S) (str := str) hL₀
    have := hsub hL₀rem
    simp only [Finset.mem_sdiff, Finset.mem_union] at this
    exact this.2 (Or.inr hL₀)

private theorem cont1Fuel_of_not_nonempty (S : Schema) (str : Strat S) (G : Graph)
    {Fixed : Finset Label} (h : ¬ (S.labels \ Fixed).Nonempty) (T : Typing) :
    ∀ n, cont1Fuel S str G n Fixed T = T
  | 0 => rfl
  | (n + 1) => by simp only [cont1Fuel, ite_eq_right h]

/-- Once fuel is enough to exhaust the remaining labels, more fuel doesn't
change the result. -/
theorem cont1Fuel_stable (S : Schema) (str : Strat S) (G : Graph) :
    ∀ Fixed : Finset Label, ∀ T : Typing, ∀ n n' : ℕ, (S.labels \ Fixed).card ≤ n →
      (S.labels \ Fixed).card ≤ n' → cont1Fuel S str G n Fixed T = cont1Fuel S str G n' Fixed T := by
  intro Fixed
  induction hcard : (S.labels \ Fixed).card using Nat.strong_induction_on generalizing Fixed with
  | _ card ih =>
    intro T n n' hn hn'
    by_cases hne : (S.labels \ Fixed).Nonempty
    · have hcardpos : 0 < card := hcard ▸ Finset.card_pos.mpr hne
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
      simp only [cont1Fuel, ite_eq_left hne]
      have hcard' : (S.labels \ (Fixed ∪ remMin S str.str Fixed)).card < card :=
        hcard ▸ remMin_card_lt S str.str hne
      exact ih _ hcard' _ rfl
        (maxAgree (S.restrictLabels (Fixed ∪ remMin S str.str Fixed)) G Fixed T)
        m m' (by omega) (by omega)
    · rw [cont1Fuel_of_not_nonempty S str G hne T n, cont1Fuel_of_not_nonempty S str G hne T n']

/-- `cont1 S str G Fixed T`: continue the `remMin` process from
`(Fixed, T)` all the way to `S.labels`, using `str` throughout to choose
each batch. `cont1_indep` below shows any valid first step gives the same
final answer, so this concrete choice of `str` is not load-bearing. -/
noncomputable def cont1 (S : Schema) (str : Strat S) (G : Graph)
    (Fixed : Finset Label) (T : Typing) : Typing :=
  cont1Fuel S str G S.labels.card Fixed T

theorem cont1_eq_fuel (S : Schema) (str : Strat S) (G : Graph)
    (Fixed : Finset Label) (T : Typing) (n : ℕ) (hn : (S.labels \ Fixed).card ≤ n) :
    cont1 S str G Fixed T = cont1Fuel S str G n Fixed T :=
  cont1Fuel_stable S str G Fixed T S.labels.card n (Finset.card_le_card (Finset.sdiff_subset)) hn

theorem cont1_done (S : Schema) (str : Strat S) (G : Graph)
    {Fixed : Finset Label} (h : ¬ (S.labels \ Fixed).Nonempty) (T : Typing) :
    cont1 S str G Fixed T = T := by
  have hcardzero : (S.labels \ Fixed).card = 0 := by
    rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]; exact h
  rw [cont1_eq_fuel S str G Fixed T 1 (by omega)]
  simp only [cont1Fuel, ite_eq_right h]

theorem cont1_step (S : Schema) (str : Strat S) (G : Graph)
    {Fixed : Finset Label} (h : (S.labels \ Fixed).Nonempty) (T : Typing) :
    cont1 S str G Fixed T = cont1 S str G (Fixed ∪ remMin S str.str Fixed)
      (maxAgree (S.restrictLabels (Fixed ∪ remMin S str.str Fixed)) G Fixed T) := by
  obtain ⟨m, hm⟩ : ∃ m, (S.labels \ Fixed).card = m + 1 :=
    ⟨(S.labels \ Fixed).card - 1, by have := Finset.card_pos.mpr h; omega⟩
  rw [cont1_eq_fuel S str G Fixed T (m + 1) (le_of_eq hm)]
  simp only [cont1Fuel, ite_eq_left h]
  refine (cont1_eq_fuel S str G _ _ m ?_).symm
  have := remMin_card_lt S str.str h
  omega

/-- Swap: two disjoint batches `A`, `B` that each individually depend
(negatively) only on the common base `Ls0` and (positively) on `Ls0` plus
themselves — neither needs the other — can be revealed in either order
with the same result. Both sides reduce, via `maxAgree_fusion`, to the
one-shot construction over `Ls0 ∪ A ∪ B`. Used below (`cont1_indep`) to
show `cont1`'s first step doesn't matter. -/
theorem maxAgree_swap {S : Schema} {G : Graph} {Ls0 A B : Finset Label}
    {T : Typing}
    (hLs0self : ∀ L ∈ Ls0, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Ls0)
    (hAneg : ∀ L ∈ A, (S.shapeDef L).negDeps ⊆ Ls0)
    (hApos : ∀ L ∈ A, (S.shapeDef L).posDeps ⊆ Ls0 ∪ A)
    (hBneg : ∀ L ∈ B, (S.shapeDef L).negDeps ⊆ Ls0)
    (hBpos : ∀ L ∈ B, (S.shapeDef L).posDeps ⊆ Ls0 ∪ B)
    (hTsub : T ⊆ (S.restrictLabels Ls0).univTyping G)
    (hTcorrect : (S.restrictLabels Ls0).CorrTyping G T) :
    maxAgree (S.restrictLabels (Ls0 ∪ A ∪ B)) G (Ls0 ∪ A)
        (maxAgree (S.restrictLabels (Ls0 ∪ A)) G Ls0 T) =
      maxAgree (S.restrictLabels (Ls0 ∪ A ∪ B)) G (Ls0 ∪ B)
        (maxAgree (S.restrictLabels (Ls0 ∪ B)) G Ls0 T) := by
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
  have hLHS := maxAgree_fusion (S := S) (G := G) hLs0LsA hLsA2 hneg2' hpos1
    hTsub hTcorrect
  have hRHS := maxAgree_fusion (S := S) (G := G) hLs0LsB hLsB2 hneg2' hpos1'
    hTsub hTcorrect
  rw [hLHS, hRHS]

/-- `cont1`'s final answer, starting from a self-contained `(Fixed, T)`,
doesn't change if we first jump ahead by revealing any other valid batch
`C` (not necessarily `remMin`'s own choice, nor disjoint from `Fixed`).
So `cont1` doesn't depend on which valid batch its underlying `str`
picks at each step. -/
theorem cont1_indep (S : Schema) (str : Strat S) (hClosed : S.Closed) (G : Graph) :
    ∀ Fixed : Finset Label, ∀ T : Typing,
      (∀ L ∈ Fixed, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Fixed) →
      T ⊆ (S.restrictLabels Fixed).univTyping G →
      (S.restrictLabels Fixed).CorrTyping G T →
      ∀ C : Finset Label, C ⊆ S.labels →
        (∀ L ∈ C, (S.shapeDef L).negDeps ⊆ Fixed) →
        (∀ L ∈ C, (S.shapeDef L).posDeps ⊆ Fixed ∪ C) →
        cont1 S str G Fixed T =
          cont1 S str G (Fixed ∪ C) (maxAgree (S.restrictLabels (Fixed ∪ C)) G Fixed T) := by
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
      have hMTA : maxAgree (S.restrictLabels Fixed) G Fixed T = T :=
        maxAgree_self (S' := S.restrictLabels Fixed) hTsub hTcorrect
      rw [hFixedC, hMTA]
    · by_cases hne : (S.labels \ Fixed).Nonempty
      · have hA₁neg := remMin_neg str hClosed Fixed
        have hA₁pos := remMin_pos str hClosed Fixed
        have hA₁ne := remMin_nonempty (S := S) (str := str.str) hne
        have hA₁sub : remMin S str.str Fixed ⊆ S.labels :=
          remMin_subset.trans Finset.sdiff_subset
        have hcardA₁ : (S.labels \ (Fixed ∪ remMin S str.str Fixed)).card < card :=
          hcard ▸ remMin_card_lt S str.str hne
        set A₁ := remMin S str.str Fixed with hA₁_def
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
        have hTA₁sub : maxAgree (S.restrictLabels (Fixed ∪ A₁)) G Fixed T ⊆
            (S.restrictLabels (Fixed ∪ A₁)).univTyping G := maxAgree_subset _ G _ _
        have hTA₁correct : (S.restrictLabels (Fixed ∪ A₁)).CorrTyping G
            (maxAgree (S.restrictLabels (Fixed ∪ A₁)) G Fixed T) :=
          maxAgree_correct hTsubA₁ hTcorrect hFA₁neg
        -- First `ih` application: base `Fixed ∪ A₁`, jump `C`.
        have hstep1 := ih _ hcardA₁ (Fixed ∪ A₁) rfl
          (maxAgree (S.restrictLabels (Fixed ∪ A₁)) G Fixed T) hFA₁self hTA₁sub hTA₁correct
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
        set T'' := maxAgree (S.restrictLabels (Fixed ∪ C)) G Fixed T with hT''_def
        have hT''sub : T'' ⊆ (S.restrictLabels (Fixed ∪ C)).univTyping G := maxAgree_subset _ G _ _
        have hT''correct : (S.restrictLabels (Fixed ∪ C)).CorrTyping G T'' :=
          maxAgree_correct hTsubC hTcorrect hFCneg
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
        -- Combine via `cont1_step` and `maxAgree_swap`.
        have hswap := maxAgree_swap (S := S) (G := G) (Ls0 := Fixed) (A := A₁) (B := C)
          hFixedSelf hA₁neg hA₁pos hCneg hCpos hTsub hTcorrect
        have hcomm : Fixed ∪ A₁ ∪ C = Fixed ∪ C ∪ A₁ := by
          apply Finset.ext; intro x; simp only [Finset.mem_union]; tauto
        rw [cont1_step S str G hne T]
        calc cont1 S str G (Fixed ∪ A₁) (maxAgree (S.restrictLabels (Fixed ∪ A₁)) G Fixed T)
            = cont1 S str G ((Fixed ∪ A₁) ∪ C)
                (maxAgree (S.restrictLabels ((Fixed ∪ A₁) ∪ C)) G (Fixed ∪ A₁)
                  (maxAgree (S.restrictLabels (Fixed ∪ A₁)) G Fixed T)) := hstep1
          _ = cont1 S str G ((Fixed ∪ A₁) ∪ C)
                (maxAgree (S.restrictLabels ((Fixed ∪ A₁) ∪ C)) G (Fixed ∪ C) T'') := by
                rw [hswap]
          _ = cont1 S str G (Fixed ∪ C) T'' := hcomm ▸ hstep2.symm
      · -- Nothing left at all: `Fixed ⊇ S.labels`, so `C ⊆ Fixed` too, contradicting `hCnew`.
        exfalso
        obtain ⟨L₀, hL₀⟩ := hCnew
        obtain ⟨hL₀C, hL₀nFixed⟩ := Finset.mem_sdiff.mp hL₀
        exact hne ⟨L₀, Finset.mem_sdiff.mpr ⟨hCsub hL₀C, hL₀nFixed⟩⟩

/-- Chain `cont1_indep` along `str'`'s own checkpoints: `cont1`, built
using any fixed `str0` internally, agrees with `str'` at every one of
`str'`'s own checkpoints, regardless of `str0`. -/
theorem cont1_chain (S : Schema) (str0 : Strat S) (hClosed : S.Closed) (G : Graph)
    (str' : Strat S) :
    ∀ i ≤ str'.k,
      cont1 S str0 G ∅ ∅ = cont1 S str0 G (S.stratum str'.str i)
        (typ S str'.str G i)
  | 0, _ => by simp [Schema.stratum_zero, typ]
  | (i + 1), hi1 => by
      have hi : i ≤ str'.k := by omega
      have hIH := cont1_chain S str0 hClosed G str' i hi
      have hT' := typ_correct S str' hClosed G i
      have hself : ∀ L ∈ S.stratum str'.str i,
          (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ S.stratum str'.str i :=
        Schema.stratum_self_contained S str' hClosed i
      set C := S.stratum str'.str (i + 1) \ S.stratum str'.str i with hC_def
      have hCsub : C ⊆ S.labels := (Finset.sdiff_subset).trans (fun L hL =>
        (Finset.mem_filter.mp hL).1)
      have hUnion : S.stratum str'.str i ∪ C = S.stratum str'.str (i + 1) := by
        rw [hC_def, Finset.union_sdiff_of_subset (Schema.stratum_mono (by omega))]
      have hCneg : ∀ L ∈ C, (S.shapeDef L).negDeps ⊆ S.stratum str'.str i := by
        intro L hL
        have hL' : L ∈ S.stratum str'.str (i + 1) := hUnion ▸ Finset.mem_union_right _ hL
        exact Schema.stratum_neg_confined S str' hClosed (i + 1) L hL' |>.trans
          (by rw [show i + 1 - 1 = i by omega])
      have hCpos : ∀ L ∈ C, (S.shapeDef L).posDeps ⊆ S.stratum str'.str i ∪ C := by
        intro L hL
        rw [hUnion]
        have hL' : L ∈ S.stratum str'.str (i + 1) := hUnion ▸ Finset.mem_union_right _ hL
        exact Finset.subset_union_left.trans
          (Schema.stratum_self_contained S str' hClosed (i + 1) L hL')
      have hindep := cont1_indep S str0 hClosed G (S.stratum str'.str i)
        (typ S str'.str G i) hself hT'.1 hT'.2 C hCsub hCneg hCpos
      rw [hIH, hindep, hUnion]
      congr 1

/-- `cont1 S str0 G ∅ ∅` equals `MTyping` for any valid stratification,
in particular for both `str1` and `str2`. -/
theorem cont1_eq_MTyping (S : Schema) (str0 : Strat S) (hClosed : S.Closed) (G : Graph)
    (str' : Strat S) : cont1 S str0 G ∅ ∅ = MTyping G S str' := by
  have h := cont1_chain S str0 hClosed G str' str'.k (le_refl _)
  rw [h]
  apply cont1_done
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset]
  intro L hL
  simp only [Schema.stratum, Finset.mem_filter]
  exact ⟨hL, (str'.mem_range L hL).2⟩

/-- Lemma 2. `Typing(G, S, str)` (Definition 4) does not depend on which
stratification of `S` is chosen: both sides equal `cont1 S str1 G ∅ ∅`,
a canonical process built by always revealing every "ready" label
(`remMin`), independent of which valid stratification justifies each
step (`cont1_indep`). -/
theorem lemma2 (S : Schema) (hClosed : S.Closed) (str1 str2 : Strat S) (G : Graph) :
    MTyping G S str1 = MTyping G S str2 := by
  rw [← cont1_eq_MTyping S str1 hClosed G str1, ← cont1_eq_MTyping S str1 hClosed G str2]

end ShexLean
