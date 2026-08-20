import ShexLean.Shex2017Schemas.Semantics
import ShexLean.Shex2017Schemas.Stratification
import ShexLean.Shex2017Schemas.MaximalTyping
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
Building blocks for §3.3's Proposition 1 (soundness of `Typing(G,S,str)`
for stratified schemas), beyond what Lemma 1 (`ShexLean/Shex2017Schemas/MaximalTyping.lean`)
covers for the negation-free case.

First, an agreement lemma: `⊢`/`⊨` depend on `t` only through its
restriction to the labels referenced by the shape/triple expression,
for any expression (including those with `NOT`). Used below to prove
the stratified monotonicity lemma.
-/

namespace ShexLean

mutual

/-- If `t` and `t'` agree (as an `Iff`) on every label appearing
in `S` (`S.posDeps ∪ S.negDeps`), then `⊢` agrees on `S` too. -/
theorem Satisfies.agree {G : Graph} {t t' : Typing} :
    ∀ (S : ShExpr),
      (∀ n L, L ∈ S.posDeps ∪ S.negDeps → ((n, L) ∈ t ↔ (n, L) ∈ t')) →
      ∀ (n : RDFNode), Satisfies G t n S ↔ Satisfies G t' n S
  | .valueDescr _, _, _ => Iff.rfl
  | .neigDescr E, hagree, n => Matches.agree (G := G) E hagree (neigh G n)
  | .and S1 S2, hagree, n => by
      have h1 := Satisfies.agree (G := G) S1
        (fun n L hL => hagree n L (ShExpr.and_deps_subset_left S1 S2 hL)) n
      have h2 := Satisfies.agree (G := G) S2
        (fun n L hL => hagree n L (ShExpr.and_deps_subset_right S1 S2 hL)) n
      exact and_congr h1 h2
  | .or S1 S2, hagree, n => by
      have h1 := Satisfies.agree (G := G) S1
        (fun n L hL => hagree n L (ShExpr.or_deps_subset_left S1 S2 hL)) n
      have h2 := Satisfies.agree (G := G) S2
        (fun n L hL => hagree n L (ShExpr.or_deps_subset_right S1 S2 hL)) n
      exact or_congr h1 h2
  | .not S, hagree, n => by
      have h := Satisfies.agree (G := G) S (fun n L hL => hagree n L (by
        rw [ShExpr.not_posDeps, ShExpr.not_negDeps]
        simpa using hL)) n
      exact not_congr h

/-- Same as `Satisfies.agree`, for `⊨`. -/
theorem Matches.agree {G : Graph} {t t' : Typing} :
    ∀ (E : TExpr),
      (∀ n L, L ∈ E.posDeps ∪ E.negDeps → ((n, L) ∈ t ↔ (n, L) ∈ t')) →
      ∀ (N : Finset Triple), Matches G t N E ↔ Matches G t' N E
  | .tPattern P L, hagree, N => by
      have hL : L ∈ (TExpr.tPattern P L).posDeps ∪ (TExpr.tPattern P L).negDeps := by
        simp [TExpr.posDeps, TExpr.negDeps, TExpr.depsAux]
      constructor
      · rintro ⟨subj, pred, obj, hN, hP, htyp⟩
        exact ⟨subj, pred, obj, hN, hP, (hagree obj L hL).mp htyp⟩
      · rintro ⟨subj, pred, obj, hN, hP, htyp⟩
        exact ⟨subj, pred, obj, hN, hP, (hagree obj L hL).mpr htyp⟩
  | .empty, _, _ => Iff.rfl
  | .someOf E1 E2, hagree, N => by
      have h1 := Matches.agree (G := G) E1
        (fun n L hL => hagree n L (TExpr.someOf_deps_subset_left E1 E2 hL)) N
      have h2 := Matches.agree (G := G) E2
        (fun n L hL => hagree n L (TExpr.someOf_deps_subset_right E1 E2 hL)) N
      exact or_congr h1 h2
  | .eachOf E1 E2, hagree, N => by
      constructor
      · rintro ⟨N1, N2, hdu, h1, h2⟩
        exact ⟨N1, N2, hdu, (Matches.agree (G := G) E1
          (fun n L hL => hagree n L (TExpr.eachOf_deps_subset_left E1 E2 hL)) N1).mp h1,
          (Matches.agree (G := G) E2
          (fun n L hL => hagree n L (TExpr.eachOf_deps_subset_right E1 E2 hL)) N2).mp h2⟩
      · rintro ⟨N1, N2, hdu, h1, h2⟩
        exact ⟨N1, N2, hdu, (Matches.agree (G := G) E1
          (fun n L hL => hagree n L (TExpr.eachOf_deps_subset_left E1 E2 hL)) N1).mpr h1,
          (Matches.agree (G := G) E2
          (fun n L hL => hagree n L (TExpr.eachOf_deps_subset_right E1 E2 hL)) N2).mpr h2⟩
  | .rep E _ _, hagree, N => by
      constructor
      · rintro ⟨Ns, hdu, hmin, hmax, hall⟩
        exact ⟨Ns, hdu, hmin, hmax, fun Ni hNi => (Matches.agree (G := G) E hagree Ni).mp (hall Ni hNi)⟩
      · rintro ⟨Ns, hdu, hmin, hmax, hall⟩
        exact ⟨Ns, hdu, hmin, hmax, fun Ni hNi => (Matches.agree (G := G) E hagree Ni).mpr (hall Ni hNi)⟩

end

/-!
Stratified monotonicity: `t ⊆ t'` suffices for the positive part of `S`,
but anything under a `NOT` needs exact agreement between `t` and `t'` on a
label set `Lo`, which is what `S.negDeps ⊆ Lo` provides (via
`Satisfies.agree` above). `Lo = ∅` recovers plain monotonicity for
negation-free `S` (`ShexLean.Satisfies.mono` in `MaximalTyping.lean`);
Proposition 1 uses the general form with `Lo` a lower stratum.
-/

mutual

/-- If `t ⊆ t'` and they agree exactly on `Lo`, then `⊢` for `S`
transports from `t` to `t'`, provided `S`'s negative dependencies
are confined to `Lo`. -/
theorem Satisfies.stratMono {G : Graph} {t t' : Typing} {Lo : Finset Label}
    (hsub : t ⊆ t')
    (hagree : ∀ n L, L ∈ Lo → ((n, L) ∈ t ↔ (n, L) ∈ t')) :
    ∀ (S : ShExpr), S.negDeps ⊆ Lo → ∀ (n : RDFNode),
      Satisfies G t n S → Satisfies G t' n S
  | .valueDescr _, _, _, h => h
  | .neigDescr E, hle, n, h => Matches.stratMono (G := G) hsub hagree E hle (neigh G n) h
  | .and S1 S2, hle, n, ⟨h1, h2⟩ =>
      ⟨Satisfies.stratMono (G := G) hsub hagree S1 ((ShExpr.and_negDeps_subset_left S1 S2).trans hle) n h1,
        Satisfies.stratMono (G := G) hsub hagree S2 ((ShExpr.and_negDeps_subset_right S1 S2).trans hle) n h2⟩
  | .or S1 S2, hle, n, Or.inl h =>
      Or.inl (Satisfies.stratMono (G := G) hsub hagree S1
        ((ShExpr.or_negDeps_subset_left S1 S2).trans hle) n h)
  | .or S1 S2, hle, n, Or.inr h =>
      Or.inr (Satisfies.stratMono (G := G) hsub hagree S2
        ((ShExpr.or_negDeps_subset_right S1 S2).trans hle) n h)
  | .not S, hle, n, h => by
      have hle' : S.posDeps ∪ S.negDeps ⊆ Lo := by
        rw [← ShExpr.not_negDeps]; exact hle
      intro hc
      exact h ((Satisfies.agree (G := G) S (fun n L hL => hagree n L (hle' hL)) n).mpr hc)

/-- Same as `Satisfies.stratMono`, for `⊨`. -/
theorem Matches.stratMono {G : Graph} {t t' : Typing} {Lo : Finset Label}
    (hsub : t ⊆ t')
    (hagree : ∀ n L, L ∈ Lo → ((n, L) ∈ t ↔ (n, L) ∈ t')) :
    ∀ (E : TExpr), E.negDeps ⊆ Lo → ∀ (N : Finset Triple),
      Matches G t N E → Matches G t' N E
  | .tPattern _ _, _, _, ⟨subj, pred, obj, hN, hP, htyp⟩ =>
      ⟨subj, pred, obj, hN, hP, hsub htyp⟩
  | .empty, _, _, h => h
  | .someOf E1 E2, hle, N, Or.inl h =>
      Or.inl (Matches.stratMono (G := G) hsub hagree E1
        ((TExpr.someOf_negDeps_subset_left E1 E2).trans hle) N h)
  | .someOf E1 E2, hle, N, Or.inr h =>
      Or.inr (Matches.stratMono (G := G) hsub hagree E2
        ((TExpr.someOf_negDeps_subset_right E1 E2).trans hle) N h)
  | .eachOf E1 E2, hle, _N, ⟨N1, N2, hdu, h1, h2⟩ =>
      ⟨N1, N2, hdu,
        Matches.stratMono (G := G) hsub hagree E1
          ((TExpr.eachOf_negDeps_subset_left E1 E2).trans hle) N1 h1,
        Matches.stratMono (G := G) hsub hagree E2
          ((TExpr.eachOf_negDeps_subset_right E1 E2).trans hle) N2 h2⟩
  | .rep E _ _, hle, _N, ⟨Ns, hdu, hmin, hmax, hall⟩ =>
      ⟨Ns, hdu, hmin, hmax,
        fun Ni hNi => Matches.stratMono (G := G) hsub hagree E hle Ni (hall Ni hNi)⟩

end

/-!
§3.3's Definition 4 ("stratification-maximal correct typing") and
Proposition 1.

Unlike the paper's `def : L → ShExpr`, `Schema.shapeDef : Label → ShExpr`
is total (a Lean function must be), so nothing stops a schema from
referencing inside some `def(L)` a label not in `S.labels`. The paper's
schemas are implicitly closed under label reference; `Schema.Closed` makes
that assumption explicit, since Proposition 1 needs referenced labels to
carry a stratum (via `neg_strict`).
-/

/-- Well-formedness: every label referenced (positively or negatively) by
some declared label's definition is itself declared. This holds
automatically in the paper's grammar but not for our total `shapeDef`, and
is needed for `neg_strict`/`pos_le` to constrain every label a stratified
schema's definitions can reach. -/
def Schema.Closed (S : Schema) : Prop :=
  ∀ L ∈ S.labels, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ S.labels

/-- `typing_{|Lo}`: the restriction of `t` to the node-type
associations whose label is in `Lo`. -/
def Typing.restrictTo (t : Typing) (Lo : Finset Label) : Typing :=
  t.filter (fun p => p.2 ∈ Lo)

theorem Typing.mem_restrictTo {t : Typing} {Lo : Finset Label} {n : RDFNode}
    {L : Label} : (n, L) ∈ t.restrictTo Lo ↔ (n, L) ∈ t ∧ L ∈ Lo := by
  simp [Typing.restrictTo]

/-- Two typings with the same restriction to `Lo` agree (as an `Iff`) on
every label in `Lo`. -/
theorem Typing.restrictTo_agree {t t' : Typing} {Lo : Finset Label}
    (h : t.restrictTo Lo = t'.restrictTo Lo) :
    ∀ n L, L ∈ Lo → ((n, L) ∈ t ↔ (n, L) ∈ t') := by
  intro n L hL
  constructor
  · intro hmem
    have hin : (n, L) ∈ t.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨hmem, hL⟩
    rw [h] at hin
    exact (Typing.mem_restrictTo.mp hin).1
  · intro hmem
    have hin : (n, L) ∈ t'.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨hmem, hL⟩
    rw [← h] at hin
    exact (Typing.mem_restrictTo.mp hin).1

/-- `L_i = {L ∈ L | str(L) ≤ i}`. -/
def Schema.stratum (S : Schema) (str : Label → ℕ) (i : ℕ) : Finset Label :=
  S.labels.filter (fun L => str L ≤ i)

theorem Schema.stratum_mono {S : Schema} {str : Label → ℕ} {i j : ℕ} (h : i ≤ j) :
    S.stratum str i ⊆ S.stratum str j := by
  intro L hL
  simp only [Schema.stratum, Finset.mem_filter] at hL ⊢
  exact ⟨hL.1, hL.2.trans h⟩

/-- `S_i = (L_i, def_i)` with `def_i(L) = def(L)`: the restriction of `S`
to the shape labels of stratum `≤ i`, keeping the same definitions. -/
def Schema.stratRestrict (S : Schema) (str : Label → ℕ) (i : ℕ) : Schema where
  labels := S.stratum str i
  shapeDef := S.shapeDef

/-- `maxAgree S' G Lo fixed`: the union of all correct typings of
`G` by `S'` that agree with `fixed` on `Lo` (i.e. whose restriction to `Lo`
is `fixed.restrictTo Lo`). Generalizes `Schema.maximalTyping`
(`ShexLean/Shex2017Schemas/MaximalTyping.lean`, the case `Lo = ∅`) with the
agreement constraint Definition 4 needs to glue strata together. Uses
classical choice to decide `CorrTyping`, as `Schema.maximalTyping` does. -/
noncomputable def maxAgree (S' : Schema) (G : Graph) (Lo : Finset Label)
    (fixed : Typing) : Typing :=
  haveI := Classical.decPred (fun t => S'.CorrTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  ((S'.univTyping G).powerset.filter
    (fun t => S'.CorrTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)).sup id

theorem subset_maxAgree {S' : Schema} {G : Graph} {Lo : Finset Label}
    {fixed t : Typing} (hsub : t ⊆ S'.univTyping G) (hcorrect : S'.CorrTyping G t)
    (hagree : t.restrictTo Lo = fixed.restrictTo Lo) : t ⊆ maxAgree S' G Lo fixed := by
  have := Classical.decPred (fun t => S'.CorrTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  apply Finset.le_sup (f := id)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hcorrect, hagree⟩

theorem maxAgree_subset (S' : Schema) (G : Graph) (Lo : Finset Label)
    (fixed : Typing) : maxAgree S' G Lo fixed ⊆ S'.univTyping G := by
  have := Classical.decPred (fun t => S'.CorrTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  apply Finset.sup_le
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_powerset] at ht
  exact ht.1

/-- `maxAgree` agrees with `fixed` on `Lo`: every candidate does by
construction, and `fixed` is itself always a candidate. -/
theorem maxAgree_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label}
    {fixed : Typing} (hfixed_sub : fixed ⊆ S'.univTyping G)
    (hfixed_correct : S'.CorrTyping G fixed) :
    (maxAgree S' G Lo fixed).restrictTo Lo = fixed.restrictTo Lo := by
  have := Classical.decPred (fun t => S'.CorrTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  apply Finset.ext
  rintro ⟨n, L⟩
  rw [Typing.mem_restrictTo, Typing.mem_restrictTo]
  constructor
  · rintro ⟨hmem, hL⟩
    simp only [maxAgree, Finset.mem_sup, Finset.mem_filter, Finset.mem_powerset,
      id] at hmem
    obtain ⟨t, ⟨_, _, htagree⟩, htmem⟩ := hmem
    have hin : (n, L) ∈ t.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨htmem, hL⟩
    rw [htagree] at hin
    exact ⟨(Typing.mem_restrictTo.mp hin).1, hL⟩
  · rintro ⟨hmem, hL⟩
    refine ⟨?_, hL⟩
    exact subset_maxAgree hfixed_sub hfixed_correct rfl hmem

/-- `maxAgree` is itself a correct typing of `G` by `S'`, provided
`S'`'s negative dependencies are all confined to `Lo`. A stratification
guarantees this of `S_{i+1}` relative to `L_i`. -/
theorem maxAgree_correct {S' : Schema} {G : Graph} {Lo : Finset Label}
    {fixed : Typing} (hfixed_sub : fixed ⊆ S'.univTyping G)
    (hfixed_correct : S'.CorrTyping G fixed)
    (hLo : ∀ L ∈ S'.labels, (S'.shapeDef L).negDeps ⊆ Lo) :
    S'.CorrTyping G (maxAgree S' G Lo fixed) := by
  have := Classical.decPred (fun t => S'.CorrTyping G t ∧ t.restrictTo Lo = fixed.restrictTo Lo)
  intro n L hmem
  simp only [maxAgree, Finset.mem_sup, Finset.mem_filter, Finset.mem_powerset,
    id] at hmem
  obtain ⟨t, ⟨htsub, htcorrect, htagree⟩, htmem⟩ := hmem
  have hL : L ∈ S'.labels := (Finset.mem_product.mp (htsub htmem)).2
  have hsub_t : t ⊆ maxAgree S' G Lo fixed :=
    subset_maxAgree htsub htcorrect htagree
  have hagree_t : ∀ n L, L ∈ Lo → ((n, L) ∈ t ↔ (n, L) ∈ maxAgree S' G Lo fixed) := by
    apply Typing.restrictTo_agree
    rw [htagree, maxAgree_restrictTo hfixed_sub hfixed_correct]
  exact Satisfies.stratMono (G := G) hsub_t hagree_t (S'.shapeDef L) (hLo L hL) n
    (htcorrect n L htmem)

/-- The `typing_i` sequence of Definition 4, as a single `ℕ`-recursion:
`typing_0 := ∅` (`L_0 = ∅` since every label has `str ≥ 1`) and
`typing_{i+1}` is the union of all correct typings of `G` by `S_{i+1}`
agreeing with `typing_i` on `L_i`. `typing_1` (Lemma 1's negation-free
maximal typing in the paper) is the special case `Lo = L_0 = ∅`. -/
noncomputable def typ (S : Schema) (str : Label → ℕ) (G : Graph) : ℕ → Typing
  | 0 => ∅
  | i + 1 => maxAgree (S.stratRestrict str (i + 1)) G (S.stratum str i)
      (typ S str G i)

/-- Definition 4: the stratification-maximal correct typing of `G` by `S`
with stratification `str`. -/
noncomputable def MTyping (G : Graph) (S : Schema) (str : Strat S) : Typing :=
  typ S str.str G str.k

/-- The two invariants `typ` maintains at every stratum `i`: it is a
subset of `S_i`'s universe of typings, and it is a correct typing of `G`
by `S_i`. Proved by induction on `i`, following the paper's Proposition 1
proof: the base case (`i = 0`, `L_0 = ∅`) is vacuous; the inductive step
is `maxAgree_correct` with `Lo = L_i`, using `Schema.Closed` and the
stratification's `neg_strict` to show `S_{i+1}`'s negative dependencies
stay within `L_i`. -/
theorem typ_correct (S : Schema) (str : Strat S) (hClosed : S.Closed)
    (G : Graph) : ∀ i : ℕ,
      typ S str.str G i ⊆ (S.stratRestrict str.str i).univTyping G ∧
      (S.stratRestrict str.str i).CorrTyping G (typ S str.str G i)
  | 0 => by
      refine ⟨by simp [typ], ?_⟩
      intro n L hmem
      simp [typ] at hmem
  | i + 1 => by
      obtain ⟨hsub_i, hcorrect_i⟩ := typ_correct S str hClosed G i
      have hsub_i' : typ S str.str G i ⊆
          (S.stratRestrict str.str (i + 1)).univTyping G := by
        intro p hp
        have hp' := hsub_i hp
        simp only [Schema.univTyping, Schema.stratRestrict] at hp' ⊢
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp hp').1,
            Schema.stratum_mono (Nat.le_succ i) (Finset.mem_product.mp hp').2⟩
      have hcorrect_i' : (S.stratRestrict str.str (i + 1)).CorrTyping G
          (typ S str.str G i) := hcorrect_i
      have hLo : ∀ L ∈ (S.stratRestrict str.str (i + 1)).labels,
          (S.shapeDef L).negDeps ⊆ S.stratum str.str i := by
        intro L hL L2 hL2
        simp only [Schema.stratRestrict, Schema.stratum, Finset.mem_filter] at hL
        obtain ⟨hLlabels, hLstrat⟩ := hL
        have hL2labels : L2 ∈ S.labels := hClosed L hLlabels (Finset.mem_union_right _ hL2)
        have hstratlt := str.neg_strict L hLlabels L2 hL2
        simp only [Schema.stratum, Finset.mem_filter]
        exact ⟨hL2labels, by omega⟩
      refine ⟨maxAgree_subset _ G _ _, ?_⟩
      show (S.stratRestrict str.str (i + 1)).CorrTyping G
        (maxAgree (S.stratRestrict str.str (i + 1)) G (S.stratum str.str i)
          (typ S str.str G i))
      exact maxAgree_correct hsub_i' hcorrect_i' hLo

/-- Proposition 1. For any schema `S` that is well-formed (`Schema.Closed`)
and admits a stratification `str`, and any graph `G`, `Typing(G, S,
str)` (Definition 4) is a correct typing of `G` by `S`. -/
theorem proposition1 (S : Schema) (str : Strat S) (hClosed : S.Closed) (G : Graph) :
    S.CorrTyping G (MTyping G S str) :=
  (typ_correct S str hClosed G str.k).2

end ShexLean
