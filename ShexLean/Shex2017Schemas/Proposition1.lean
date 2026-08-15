import ShexLean.Shex2017Schemas.Semantics
import ShexLean.Shex2017Schemas.Stratification
import ShexLean.Shex2017Schemas.MaximalTyping
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
Building blocks for §3.3's Proposition 1 (soundness of `Typing(G,S,strat)`
for stratified schemas), beyond what Lemma 1 (`ShexLean/Shex2017Schemas/MaximalTyping.lean`)
covers for the negation-free case.

This first part is a fully general "agreement" lemma: `⊢`/`⊨` depend on
`typing` only through its restriction to the labels actually referenced by
the shape/triple expression at hand — unconditionally, for *any* use of
`NOT`, not just negation-free expressions. It underlies the "stratified"
monotonicity lemma built on top of it further down this file.
-/

namespace ShexLean

mutual

/-- If `typing` and `typing'` agree (as an `Iff`) on every label appearing
in `S` (`S.posDeps ∪ S.negDeps`), then `⊢` agrees on `S` too. -/
theorem Satisfies.agree {G : Graph} {typing typing' : Typing} :
    ∀ (S : ShapeExpr),
      (∀ n L, L ∈ S.posDeps ∪ S.negDeps → ((n, L) ∈ typing ↔ (n, L) ∈ typing')) →
      ∀ (n : RDFNode), Satisfies G typing n S ↔ Satisfies G typing' n S
  | .valueDescr _, _, _ => Iff.rfl
  | .neigDescr E, hagree, n => Matches.agree (G := G) E hagree (neigh G n)
  | .and S1 S2, hagree, n => by
      have h1 := Satisfies.agree (G := G) S1 (fun n L hL => hagree n L (by
        simp only [ShapeExpr.posDeps, ShapeExpr.negDeps,
          Finset.mem_union] at hL ⊢
        tauto)) n
      have h2 := Satisfies.agree (G := G) S2 (fun n L hL => hagree n L (by
        simp only [ShapeExpr.posDeps, ShapeExpr.negDeps,
          Finset.mem_union] at hL ⊢
        tauto)) n
      exact and_congr h1 h2
  | .or S1 S2, hagree, n => by
      have h1 := Satisfies.agree (G := G) S1 (fun n L hL => hagree n L (by
        simp only [ShapeExpr.posDeps, ShapeExpr.negDeps,
          Finset.mem_union] at hL ⊢
        tauto)) n
      have h2 := Satisfies.agree (G := G) S2 (fun n L hL => hagree n L (by
        simp only [ShapeExpr.posDeps, ShapeExpr.negDeps,
          Finset.mem_union] at hL ⊢
        tauto)) n
      exact or_congr h1 h2
  | .not S, hagree, n => by
      have h := Satisfies.agree (G := G) S (fun n L hL => hagree n L (by
        rw [ShapeExpr.not_posDeps, ShapeExpr.not_negDeps]
        simpa using hL)) n
      exact not_congr h

/-- Same as `Satisfies.agree`, for `⊨`. -/
theorem Matches.agree {G : Graph} {typing typing' : Typing} :
    ∀ (E : TripleExpr),
      (∀ n L, L ∈ E.posDeps ∪ E.negDeps → ((n, L) ∈ typing ↔ (n, L) ∈ typing')) →
      ∀ (N : Finset Triple), Matches G typing N E ↔ Matches G typing' N E
  | .tPattern P L, hagree, N => by
      have hL : L ∈ (TripleExpr.tPattern P L).posDeps ∪ (TripleExpr.tPattern P L).negDeps := by
        simp [TripleExpr.posDeps, TripleExpr.negDeps, TripleExpr.depsAux]
      constructor
      · rintro ⟨subj, pred, obj, hN, hP, htyp⟩
        exact ⟨subj, pred, obj, hN, hP, (hagree obj L hL).mp htyp⟩
      · rintro ⟨subj, pred, obj, hN, hP, htyp⟩
        exact ⟨subj, pred, obj, hN, hP, (hagree obj L hL).mpr htyp⟩
  | .empty, _, _ => Iff.rfl
  | .someOf E1 E2, hagree, N => by
      have h1 := Matches.agree (G := G) E1 (fun n L hL => hagree n L (by
        simp only [TripleExpr.posDeps, TripleExpr.negDeps,
          Finset.mem_union] at hL ⊢
        tauto)) N
      have h2 := Matches.agree (G := G) E2 (fun n L hL => hagree n L (by
        simp only [TripleExpr.posDeps, TripleExpr.negDeps,
          Finset.mem_union] at hL ⊢
        tauto)) N
      exact or_congr h1 h2
  | .eachOf E1 E2, hagree, N => by
      constructor
      · rintro ⟨N1, N2, hdu, h1, h2⟩
        have a1 := Matches.agree (G := G) E1 (fun n L hL => hagree n L (by
          simp only [TripleExpr.posDeps, TripleExpr.negDeps,
            Finset.mem_union] at hL ⊢
          tauto)) N1
        have a2 := Matches.agree (G := G) E2 (fun n L hL => hagree n L (by
          simp only [TripleExpr.posDeps, TripleExpr.negDeps,
            Finset.mem_union] at hL ⊢
          tauto)) N2
        exact ⟨N1, N2, hdu, a1.mp h1, a2.mp h2⟩
      · rintro ⟨N1, N2, hdu, h1, h2⟩
        have a1 := Matches.agree (G := G) E1 (fun n L hL => hagree n L (by
          simp only [TripleExpr.posDeps, TripleExpr.negDeps,
            Finset.mem_union] at hL ⊢
          tauto)) N1
        have a2 := Matches.agree (G := G) E2 (fun n L hL => hagree n L (by
          simp only [TripleExpr.posDeps, TripleExpr.negDeps,
            Finset.mem_union] at hL ⊢
          tauto)) N2
        exact ⟨N1, N2, hdu, a1.mpr h1, a2.mpr h2⟩
  | .rep E _ _, hagree, N => by
      constructor
      · rintro ⟨Ns, hdu, hmin, hmax, hall⟩
        exact ⟨Ns, hdu, hmin, hmax, fun Ni hNi => (Matches.agree (G := G) E hagree Ni).mp (hall Ni hNi)⟩
      · rintro ⟨Ns, hdu, hmin, hmax, hall⟩
        exact ⟨Ns, hdu, hmin, hmax, fun Ni hNi => (Matches.agree (G := G) E hagree Ni).mpr (hall Ni hNi)⟩

end

/-!
"Stratified" (mixed) monotonicity: growing `typing ⊆ typing'` is enough for
the positively-occurring part of `S`, but whatever sits under a `NOT` needs
*exact* agreement between `typing`/`typing'` on a label set `Lo` — this is
what `S.negDeps ⊆ Lo` buys us, via `Satisfies.agree` above. Taking `Lo = ∅`
recovers plain monotonicity for negation-free `S` (`ShexLean.Satisfies.mono`
in `MaximalTyping.lean`); Proposition 1 uses the general form with
`Lo = ` a lower stratum.
-/

mutual

/-- If `typing ⊆ typing'` and they agree exactly on `Lo`, then `⊢` for `S`
transports from `typing` to `typing'`, provided `S`'s negative dependencies
are confined to `Lo`. -/
theorem Satisfies.stratMono {G : Graph} {typing typing' : Typing} {Lo : Finset ShapeLabel}
    (hsub : typing ⊆ typing')
    (hagree : ∀ n L, L ∈ Lo → ((n, L) ∈ typing ↔ (n, L) ∈ typing')) :
    ∀ (S : ShapeExpr), S.negDeps ⊆ Lo → ∀ (n : RDFNode),
      Satisfies G typing n S → Satisfies G typing' n S
  | .valueDescr _, _, _, h => h
  | .neigDescr E, hle, n, h => Matches.stratMono (G := G) hsub hagree E hle (neigh G n) h
  | .and S1 S2, hle, n, ⟨h1, h2⟩ => by
      have le1 : S1.negDeps ⊆ Lo := by
        simp only [ShapeExpr.negDeps, Finset.union_subset_iff] at hle
        exact hle.1
      have le2 : S2.negDeps ⊆ Lo := by
        simp only [ShapeExpr.negDeps, Finset.union_subset_iff] at hle
        exact hle.2
      exact ⟨Satisfies.stratMono (G := G) hsub hagree S1 le1 n h1,
        Satisfies.stratMono (G := G) hsub hagree S2 le2 n h2⟩
  | .or S1 S2, hle, n, Or.inl h => by
      have le1 : S1.negDeps ⊆ Lo := by
        simp only [ShapeExpr.negDeps, Finset.union_subset_iff] at hle
        exact hle.1
      exact Or.inl (Satisfies.stratMono (G := G) hsub hagree S1 le1 n h)
  | .or S1 S2, hle, n, Or.inr h => by
      have le2 : S2.negDeps ⊆ Lo := by
        simp only [ShapeExpr.negDeps, Finset.union_subset_iff] at hle
        exact hle.2
      exact Or.inr (Satisfies.stratMono (G := G) hsub hagree S2 le2 n h)
  | .not S, hle, n, h => by
      have hle' : S.posDeps ∪ S.negDeps ⊆ Lo := by
        rw [← ShapeExpr.not_negDeps]; exact hle
      intro hc
      exact h ((Satisfies.agree (G := G) S (fun n L hL => hagree n L (hle' hL)) n).mpr hc)

/-- Same as `Satisfies.stratMono`, for `⊨`. -/
theorem Matches.stratMono {G : Graph} {typing typing' : Typing} {Lo : Finset ShapeLabel}
    (hsub : typing ⊆ typing')
    (hagree : ∀ n L, L ∈ Lo → ((n, L) ∈ typing ↔ (n, L) ∈ typing')) :
    ∀ (E : TripleExpr), E.negDeps ⊆ Lo → ∀ (N : Finset Triple),
      Matches G typing N E → Matches G typing' N E
  | .tPattern _ _, _, _, ⟨subj, pred, obj, hN, hP, htyp⟩ =>
      ⟨subj, pred, obj, hN, hP, hsub htyp⟩
  | .empty, _, _, h => h
  | .someOf E1 E2, hle, N, Or.inl h => by
      have le1 : E1.negDeps ⊆ Lo := by
        simp only [TripleExpr.negDeps, Finset.union_subset_iff] at hle
        exact hle.1
      exact Or.inl (Matches.stratMono (G := G) hsub hagree E1 le1 N h)
  | .someOf E1 E2, hle, N, Or.inr h => by
      have le2 : E2.negDeps ⊆ Lo := by
        simp only [TripleExpr.negDeps, Finset.union_subset_iff] at hle
        exact hle.2
      exact Or.inr (Matches.stratMono (G := G) hsub hagree E2 le2 N h)
  | .eachOf E1 E2, hle, N, ⟨N1, N2, hdu, h1, h2⟩ => by
      have le1 : E1.negDeps ⊆ Lo := by
        simp only [TripleExpr.negDeps, Finset.union_subset_iff] at hle
        exact hle.1
      have le2 : E2.negDeps ⊆ Lo := by
        simp only [TripleExpr.negDeps, Finset.union_subset_iff] at hle
        exact hle.2
      exact ⟨N1, N2, hdu, Matches.stratMono (G := G) hsub hagree E1 le1 N1 h1,
        Matches.stratMono (G := G) hsub hagree E2 le2 N2 h2⟩
  | .rep E _ _, hle, N, ⟨Ns, hdu, hmin, hmax, hall⟩ =>
      ⟨Ns, hdu, hmin, hmax,
        fun Ni hNi => Matches.stratMono (G := G) hsub hagree E hle Ni (hall Ni hNi)⟩

end

/-!
§3.3's Definition 4 ("stratification-maximal correct typing") and
Proposition 1.

Our `Schema.shapeDef : ShapeLabel → ShapeExpr` is, unlike the paper's
`def : L → ShExpr`, total on *all* shape labels (a Lean function must be):
nothing stops a schema from mentioning, inside some `def(L)`, a label that
is not itself in `S.labels`. The paper's schemas are implicitly closed
under label reference (`ShapeRef` is grammatically confined to `L`); we
make that assumption explicit as `Schema.Closed`, since Proposition 1 (via
the stratification's `neg_strict`) needs referenced labels to actually
carry a stratum.
-/

/-- Well-formedness: every label referenced (positively or negatively) by
some declared label's definition is itself declared. The paper's schemas
are always like this (`def : L → ShExpr`, and `ShapeRef` is grammatically
confined to `L`); our `shapeDef` is total on all of `ShapeLabel` so this
isn't automatic, but it is needed for `neg_strict`/`pos_le` (stated for
*all* label pairs) to actually constrain every label a stratified schema's
definitions can reach. -/
def Schema.Closed (S : Schema) : Prop :=
  ∀ L ∈ S.labels, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ S.labels

/-- `typing_{|Lo}`: the restriction of `typing` to the node-type
associations whose label is in `Lo`. -/
def Typing.restrictTo (typing : Typing) (Lo : Finset ShapeLabel) : Typing :=
  typing.filter (fun p => p.2 ∈ Lo)

theorem Typing.mem_restrictTo {typing : Typing} {Lo : Finset ShapeLabel} {n : RDFNode}
    {L : ShapeLabel} : (n, L) ∈ typing.restrictTo Lo ↔ (n, L) ∈ typing ∧ L ∈ Lo := by
  simp [Typing.restrictTo]

/-- Two typings with the same restriction to `Lo` agree (as an `Iff`) on
every label in `Lo`. -/
theorem Typing.restrictTo_agree {typing typing' : Typing} {Lo : Finset ShapeLabel}
    (h : typing.restrictTo Lo = typing'.restrictTo Lo) :
    ∀ n L, L ∈ Lo → ((n, L) ∈ typing ↔ (n, L) ∈ typing') := by
  intro n L hL
  constructor
  · intro hmem
    have hin : (n, L) ∈ typing.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨hmem, hL⟩
    rw [h] at hin
    exact (Typing.mem_restrictTo.mp hin).1
  · intro hmem
    have hin : (n, L) ∈ typing'.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨hmem, hL⟩
    rw [← h] at hin
    exact (Typing.mem_restrictTo.mp hin).1

/-- `L_i = {L ∈ L | strat(L) ≤ i}`. -/
def Schema.stratum (S : Schema) (strat : ShapeLabel → ℕ) (i : ℕ) : Finset ShapeLabel :=
  S.labels.filter (fun L => strat L ≤ i)

theorem Schema.stratum_mono {S : Schema} {strat : ShapeLabel → ℕ} {i j : ℕ} (h : i ≤ j) :
    S.stratum strat i ⊆ S.stratum strat j := by
  intro L hL
  simp only [Schema.stratum, Finset.mem_filter] at hL ⊢
  exact ⟨hL.1, hL.2.trans h⟩

/-- `S_i = (L_i, def_i)` with `def_i(L) = def(L)`: the restriction of `S`
to the shape labels of stratum `≤ i`, keeping the same definitions. -/
def Schema.stratRestrict (S : Schema) (strat : ShapeLabel → ℕ) (i : ℕ) : Schema where
  labels := S.stratum strat i
  shapeDef := S.shapeDef

/-- `maxTypingAgreeing S' G Lo fixed`: the union of all correct typings of
`G` by `S'` that agree with `fixed` on `Lo` (i.e. whose restriction to `Lo`
is `fixed.restrictTo Lo`). Generalizes `Schema.maximalTyping`
(`ShexLean/Shex2017Schemas/MaximalTyping.lean`) — which is the case `Lo = ∅` — with the
extra agreement constraint that Definition 4 needs to glue strata
together. Uses classical choice to decide `CorrectTyping`, as
`Schema.maximalTyping` does. -/
noncomputable def maxTypingAgreeing (S' : Schema) (G : Graph) (Lo : Finset ShapeLabel)
    (fixed : Typing) : Typing :=
  haveI := Classical.decPred (fun t => S'.CorrectTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  ((S'.univTyping G).powerset.filter
    (fun t => S'.CorrectTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)).sup id

theorem subset_maxTypingAgreeing {S' : Schema} {G : Graph} {Lo : Finset ShapeLabel}
    {fixed t : Typing} (hsub : t ⊆ S'.univTyping G) (hcorrect : S'.CorrectTyping G t)
    (hagree : t.restrictTo Lo = fixed.restrictTo Lo) : t ⊆ maxTypingAgreeing S' G Lo fixed := by
  have := Classical.decPred (fun t => S'.CorrectTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  apply Finset.le_sup (f := id)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hcorrect, hagree⟩

theorem maxTypingAgreeing_subset (S' : Schema) (G : Graph) (Lo : Finset ShapeLabel)
    (fixed : Typing) : maxTypingAgreeing S' G Lo fixed ⊆ S'.univTyping G := by
  have := Classical.decPred (fun t => S'.CorrectTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  apply Finset.sup_le
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_powerset] at ht
  exact ht.1

/-- `maxTypingAgreeing` really does agree with `fixed` on `Lo`: every
candidate does by construction, and `fixed` itself is always a candidate
(it agrees with itself trivially, and is a correct typing of `S'` given
`hfixed_correct`), so the union's restriction to `Lo` is neither more nor
less than `fixed`'s. -/
theorem maxTypingAgreeing_restrictTo {S' : Schema} {G : Graph} {Lo : Finset ShapeLabel}
    {fixed : Typing} (hfixed_sub : fixed ⊆ S'.univTyping G)
    (hfixed_correct : S'.CorrectTyping G fixed) :
    (maxTypingAgreeing S' G Lo fixed).restrictTo Lo = fixed.restrictTo Lo := by
  have := Classical.decPred (fun t => S'.CorrectTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  apply Finset.ext
  rintro ⟨n, L⟩
  rw [Typing.mem_restrictTo, Typing.mem_restrictTo]
  constructor
  · rintro ⟨hmem, hL⟩
    simp only [maxTypingAgreeing, Finset.mem_sup, Finset.mem_filter, Finset.mem_powerset,
      id] at hmem
    obtain ⟨t, ⟨_, _, htagree⟩, htmem⟩ := hmem
    have hin : (n, L) ∈ t.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨htmem, hL⟩
    rw [htagree] at hin
    exact ⟨(Typing.mem_restrictTo.mp hin).1, hL⟩
  · rintro ⟨hmem, hL⟩
    refine ⟨?_, hL⟩
    exact subset_maxTypingAgreeing hfixed_sub hfixed_correct rfl hmem

/-- `maxTypingAgreeing` is itself a correct typing of `G` by `S'`, provided
`S'`'s negative dependencies are all confined to `Lo` — exactly what a
stratification guarantees of `S_{i+1}` relative to `L_i`. -/
theorem maxTypingAgreeing_correct {S' : Schema} {G : Graph} {Lo : Finset ShapeLabel}
    {fixed : Typing} (hfixed_sub : fixed ⊆ S'.univTyping G)
    (hfixed_correct : S'.CorrectTyping G fixed)
    (hLo : ∀ L ∈ S'.labels, (S'.shapeDef L).negDeps ⊆ Lo) :
    S'.CorrectTyping G (maxTypingAgreeing S' G Lo fixed) := by
  have := Classical.decPred (fun t => S'.CorrectTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  intro n L hmem
  simp only [maxTypingAgreeing, Finset.mem_sup, Finset.mem_filter, Finset.mem_powerset,
    id] at hmem
  obtain ⟨t, ⟨htsub, htcorrect, htagree⟩, htmem⟩ := hmem
  have hL : L ∈ S'.labels := (Finset.mem_product.mp (htsub htmem)).2
  have hsub_t : t ⊆ maxTypingAgreeing S' G Lo fixed :=
    subset_maxTypingAgreeing htsub htcorrect htagree
  have hagree_t : ∀ n L, L ∈ Lo → ((n, L) ∈ t ↔ (n, L) ∈ maxTypingAgreeing S' G Lo fixed) := by
    apply Typing.restrictTo_agree
    rw [htagree, maxTypingAgreeing_restrictTo hfixed_sub hfixed_correct]
  exact Satisfies.stratMono (G := G) hsub_t hagree_t (S'.shapeDef L) (hLo L hL) n
    (htcorrect n L htmem)

/-- The `typing_i` sequence of Definition 4, unified into a single
`ℕ`-recursion: `typing_0 := ∅` (vacuously correct for `S_0`, the empty
schema — `L_0 = ∅` since every label has `strat ≥ 1`) and `typing_{i+1}` is
the union of all correct typings of `G` by `S_{i+1}` agreeing with
`typing_i` on `L_i`. This is exactly the paper's recursion once `typing_1`
(defined there directly as Lemma 1's negation-free maximal typing) is seen
as the special case `Lo = L_0 = ∅` of the general step — Lemma 1 itself is
`maxTypingAgreeing`'s correctness with a vacuous agreement condition. -/
noncomputable def stratTypingSeq (S : Schema) (strat : ShapeLabel → ℕ) (G : Graph) : ℕ → Typing
  | 0 => ∅
  | i + 1 => maxTypingAgreeing (S.stratRestrict strat (i + 1)) G (S.stratum strat i)
      (stratTypingSeq S strat G i)

/-- Definition 4: the stratification-maximal correct typing of `G` by `S`
with stratification `strat`. -/
noncomputable def Typing4 (G : Graph) (S : Schema) (strat : Stratification S) : Typing :=
  stratTypingSeq S strat.strat G strat.k

/-- The two invariants `stratTypingSeq` maintains at every stratum `i`: it
is a subset of `S_i`'s universe of typings, and it is a correct typing of
`G` by `S_i`. Proved together by induction on `i`, mirroring the paper's
Proposition 1 proof: the base case (`i = 0`, standing for the paper's "base
case is Lemma 1" — `L_0 = ∅` since every label has `strat ≥ 1`, exactly
Lemma 1's `Lo = ∅`) is vacuous; the inductive step is
`maxTypingAgreeing_correct` with `Lo = L_i`, using `Schema.Closed` together
with the stratification's `neg_strict` to show `S_{i+1}`'s negative
dependencies stay within `L_i`. -/
theorem stratTypingSeq_correct (S : Schema) (strat : Stratification S) (hClosed : S.Closed)
    (G : Graph) : ∀ i : ℕ,
      stratTypingSeq S strat.strat G i ⊆ (S.stratRestrict strat.strat i).univTyping G ∧
      (S.stratRestrict strat.strat i).CorrectTyping G (stratTypingSeq S strat.strat G i)
  | 0 => by
      refine ⟨by simp [stratTypingSeq], ?_⟩
      intro n L hmem
      simp [stratTypingSeq] at hmem
  | i + 1 => by
      obtain ⟨hsub_i, hcorrect_i⟩ := stratTypingSeq_correct S strat hClosed G i
      have hsub_i' : stratTypingSeq S strat.strat G i ⊆
          (S.stratRestrict strat.strat (i + 1)).univTyping G := by
        intro p hp
        have hp' := hsub_i hp
        simp only [Schema.univTyping, Schema.stratRestrict] at hp' ⊢
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp hp').1,
            Schema.stratum_mono (Nat.le_succ i) (Finset.mem_product.mp hp').2⟩
      have hcorrect_i' : (S.stratRestrict strat.strat (i + 1)).CorrectTyping G
          (stratTypingSeq S strat.strat G i) := hcorrect_i
      have hLo : ∀ L ∈ (S.stratRestrict strat.strat (i + 1)).labels,
          (S.shapeDef L).negDeps ⊆ S.stratum strat.strat i := by
        intro L hL L2 hL2
        simp only [Schema.stratRestrict, Schema.stratum, Finset.mem_filter] at hL
        obtain ⟨hLlabels, hLstrat⟩ := hL
        have hL2labels : L2 ∈ S.labels := hClosed L hLlabels (Finset.mem_union_right _ hL2)
        have hstratlt := strat.neg_strict L hLlabels L2 hL2
        simp only [Schema.stratum, Finset.mem_filter]
        exact ⟨hL2labels, by omega⟩
      refine ⟨maxTypingAgreeing_subset _ G _ _, ?_⟩
      show (S.stratRestrict strat.strat (i + 1)).CorrectTyping G
        (maxTypingAgreeing (S.stratRestrict strat.strat (i + 1)) G (S.stratum strat.strat i)
          (stratTypingSeq S strat.strat G i))
      exact maxTypingAgreeing_correct hsub_i' hcorrect_i' hLo

/-- Proposition 1. For any schema `S` that is well-formed (`Schema.Closed`)
and admits a stratification `strat`, and any graph `G`, `Typing(G, S,
strat)` (Definition 4) is a correct typing of `G` by `S`. -/
theorem proposition1 (S : Schema) (strat : Stratification S) (hClosed : S.Closed) (G : Graph) :
    S.CorrectTyping G (Typing4 G S strat) :=
  (stratTypingSeq_correct S strat hClosed G strat.k).2

end ShexLean
