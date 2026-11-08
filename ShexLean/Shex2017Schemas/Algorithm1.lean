import ShexLean.Common.FixedPoint
import ShexLean.Shex2017Schemas.Lemma2

/-!
§4.1: Algorithm 1 (`refine`), and the proof that it is correct. The
algorithm computes `Typing(G, S, str)` (Definition 4).

```
Input: G: a graph, S = (L, def): a schema, str a stratification for S
       with k strata
Output: Typing(G, S, str)
1  t ← ∅;
2  for i from 1 to k do
     // Add all node-type associations for stratum i
3    foreach n in Nodes(G) do
4      foreach L in L_i do
5        add (n, L) to t;
     // Refine w.r.t. the types on stratum i
6    changing ← true;
7    while changing do
8      changing ← false;
9      foreach (n, L) in t s.t. L ∈ L_i do
10       if not t, n ⊢ def(L) then
11         remove (n, L) from t;
12         changing ← true;
13   return t
```

Each iteration `i` of the outer loop computes a greatest fixed point:

1. Start from the largest possible typing for `S_i`. This typing contains
   all the pairs that are already fixed for `S_{i-1}`, and all the
   possible pairs for the new labels.
2. Remove each pair that does not satisfy `⊢` at that time.
3. Do step 2 again until no more pairs go out.

This file does these steps:

* It formalizes the computation of one stratum (`refineStep` and
  `refine1`).
* It proves that this computation is equal to `maxAgree`. (`maxAgree` is
  the construction of one stratum in Definition 4.)
* It connects the result for all `k` strata. The final result is
  `Algorithm1 G S str = MTyping G S str`.
-/

namespace ShexLean

/-- The initial guess for the stratum `S'`, relative to the result
`(Lo, T)` of the previous stratum. On `Lo`, it keeps the pairs of `T`
exactly. For the other labels of `S'`, it adds all the possible node-type
associations. These are lines 3–5 of `refine`. -/
def bigStart (S' : Schema) (G : Graph) (Lo : Finset Label) (T : Typing) : Typing :=
  (S'.univTyping G).filter (fun p => p.2 ∈ Lo → p ∈ T)

theorem mem_bigStart {S' : Schema} {G : Graph} {Lo : Finset Label} {T : Typing}
    {p : Assoc} : p ∈ bigStart S' G Lo T ↔ p ∈ S'.univTyping G ∧ (p.2 ∈ Lo → p ∈ T) :=
  Finset.mem_filter

theorem bigStart_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label} {T : Typing}
    (hTsub : T ⊆ S'.univTyping G) : (bigStart S' G Lo T).restrictTo Lo = T.restrictTo Lo := by
  apply Finset.ext
  rintro ⟨n, L⟩
  simp only [Typing.mem_restrictTo, mem_bigStart]
  constructor
  · rintro ⟨⟨-, h⟩, hL⟩; exact ⟨h hL, hL⟩
  · rintro ⟨h, hL⟩; exact ⟨⟨hTsub h, fun _ => h⟩, hL⟩

/-- One refinement pass: remove each node-type association that has a
label outside `Lo` and does not satisfy `⊢` at that time. These are lines
9–12 of `refine` (one full pass of the loop body). The `while changing` of
the paper does this pass again until nothing changes. Thus, it iterates
the pass to a fixed point. -/
noncomputable def refineStep (S' : Schema) (G : Graph) (Lo : Finset Label)
    (current : Typing) : Typing :=
  haveI := Classical.decPred (fun p : Assoc => p.2 ∈ Lo ∨ Satisfies G current p.1 (S'.shapeDef p.2))
  current.filter (fun p => p.2 ∈ Lo ∨ Satisfies G current p.1 (S'.shapeDef p.2))

theorem mem_refineStep {S' : Schema} {G : Graph} {Lo : Finset Label} {current : Typing}
    {p : Assoc} :
    p ∈ refineStep S' G Lo current ↔
      p ∈ current ∧ (p.2 ∈ Lo ∨ Satisfies G current p.1 (S'.shapeDef p.2)) := by
  unfold refineStep
  simp only [Finset.mem_filter]

theorem refineStep_subset (S' : Schema) (G : Graph) (Lo : Finset Label) (current : Typing) :
    refineStep S' G Lo current ⊆ current := by
  intro p hp; exact (mem_refineStep.mp hp).1

/-- `refineStep` never adds or removes a pair with a label in `Lo`. -/
theorem refineStep_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label} {current : Typing} :
    (refineStep S' G Lo current).restrictTo Lo = current.restrictTo Lo := by
  apply Finset.ext
  rintro ⟨n, L⟩
  simp only [Typing.mem_restrictTo, mem_refineStep]
  constructor
  · rintro ⟨⟨hmem, -⟩, hL⟩; exact ⟨hmem, hL⟩
  · rintro ⟨hmem, hL⟩; exact ⟨⟨hmem, Or.inl hL⟩, hL⟩

/-- The computation of one stratum in `refine`. Start from `bigStart`, and
iterate `refineStep` to a fixed point. `Finset.card` iterations are always
sufficient (`Finset.decreasing_iterate_fixed`). -/
noncomputable def refine1 (S' : Schema) (G : Graph) (Lo : Finset Label) (T : Typing) : Typing :=
  (refineStep S' G Lo)^[(bigStart S' G Lo T).card] (bigStart S' G Lo T)

theorem refine1_fixed (S' : Schema) (G : Graph) (Lo : Finset Label) (T : Typing) :
    refineStep S' G Lo (refine1 S' G Lo T) = refine1 S' G Lo T :=
  Finset.decreasing_iterate_fixed (refineStep S' G Lo) (refineStep_subset S' G Lo) (bigStart S' G Lo T)

theorem refine1_subset (S' : Schema) (G : Graph) (Lo : Finset Label) (T : Typing) :
    refine1 S' G Lo T ⊆ bigStart S' G Lo T := by
  suffices h : ∀ n, (refineStep S' G Lo)^[n] (bigStart S' G Lo T) ⊆ bigStart S' G Lo T by
    exact h _
  intro n
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ihn =>
      rw [Function.iterate_succ_apply']
      exact (refineStep_subset S' G Lo _).trans ihn

theorem iterate_refineStep_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label} {T : Typing}
    (hTsub : T ⊆ S'.univTyping G) :
    ∀ n, ((refineStep S' G Lo)^[n] (bigStart S' G Lo T)).restrictTo Lo = T.restrictTo Lo := by
  intro n
  induction n with
  | zero => exact bigStart_restrictTo hTsub
  | succ n ihn =>
      rw [Function.iterate_succ_apply', refineStep_restrictTo, ihn]

theorem refine1_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label} {T : Typing}
    (hTsub : T ⊆ S'.univTyping G) : (refine1 S' G Lo T).restrictTo Lo = T.restrictTo Lo :=
  iterate_refineStep_restrictTo hTsub _

/-!
The core lemma: `refine1` computes the same result as `maxAgree`.
(`Proposition1.lean` and `Lemma2.lean` make the same object with
`maxAgree`, as the union of all correct typings, not with iterative
refinement.)
-/

/-- `refine1 S' G Lo T` is correct for `S'`:

* On `Lo`, it gets the correctness of `T` (with `Satisfies.agree`), because
  `Lo` is self-contained.
* Outside `Lo`, the correctness follows directly, because `refine1` is a
  fixed point of `refineStep`. -/
theorem refine1_correct {S : Schema} {G : Graph} {Ls' Lo : Finset Label} {T : Typing}
    (hLoLs' : Lo ⊆ Ls') (hLoself : ∀ L ∈ Lo, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Lo)
    (hTsub : T ⊆ (S.restrictLabels Lo).univTyping G)
    (hTcorrect : (S.restrictLabels Lo).CorrTyping G T) :
    (S.restrictLabels Ls').CorrTyping G (refine1 (S.restrictLabels Ls') G Lo T) := by
  intro n L hmem
  by_cases hL : L ∈ Lo
  · have hTsub' : T ⊆ (S.restrictLabels Ls').univTyping G := hTsub.trans (Schema.univTyping_mono hLoLs')
    have hrestr := refine1_restrictTo (S' := S.restrictLabels Ls') (Lo := Lo) hTsub'
    have hagree : ∀ n' L', L' ∈ Lo → ((n', L') ∈ T ↔ (n', L') ∈ refine1 (S.restrictLabels Ls') G Lo T) :=
      Typing.restrictTo_agree hrestr.symm
    have hmemT : (n, L) ∈ T := by
      have hmem' := hmem
      rw [← hagree n L hL] at hmem'
      exact hmem'
    have hSat : Satisfies G T n (S.shapeDef L) := hTcorrect n L hmemT
    have hagreeL : ∀ n' L', L' ∈ (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps →
        ((n', L') ∈ T ↔ (n', L') ∈ refine1 (S.restrictLabels Ls') G Lo T) :=
      fun n' L' hL' => hagree n' L' (hLoself L hL hL')
    exact (Satisfies.agree (G := G) (S.shapeDef L) hagreeL n).mp hSat
  · have hfixed := refine1_fixed (S.restrictLabels Ls') G Lo T
    rw [← hfixed] at hmem
    rcases mem_refineStep.mp hmem with ⟨-, hcase⟩
    exact hcase.resolve_left hL

/-- `maxAgree` is also a fixed point of `refineStep`. Its correctness gives
the "keep" side of the filter directly. Also, `maxAgree` starts below
`bigStart`. Thus, it stays below each iterate, and also below
`refine1`. -/
theorem maxAgree_subset_refine1 {S : Schema} {G : Graph} {Ls' Lo : Finset Label}
    {T : Typing} (hLoLs' : Lo ⊆ Ls')
    (hTsub : T ⊆ (S.restrictLabels Lo).univTyping G)
    (hTcorrect : (S.restrictLabels Lo).CorrTyping G T)
    (hLsneg : ∀ L ∈ Ls', (S.shapeDef L).negDeps ⊆ Lo) :
    maxAgree (S.restrictLabels Ls') G Lo T ⊆ refine1 (S.restrictLabels Ls') G Lo T := by
  set M := maxAgree (S.restrictLabels Ls') G Lo T with hM_def
  have hTsub' : T ⊆ (S.restrictLabels Ls').univTyping G := hTsub.trans (Schema.univTyping_mono hLoLs')
  have hMcorrect : (S.restrictLabels Ls').CorrTyping G M :=
    maxAgree_correct hTsub' hTcorrect hLsneg
  have hMsub : M ⊆ (S.restrictLabels Ls').univTyping G := maxAgree_subset _ G _ _
  have hMrestrict : M.restrictTo Lo = T.restrictTo Lo := maxAgree_restrictTo hTsub' hTcorrect
  have hMfixed : refineStep (S.restrictLabels Ls') G Lo M = M := by
    apply Finset.Subset.antisymm (refineStep_subset _ G Lo M)
    intro p hp
    exact mem_refineStep.mpr ⟨hp, Or.inr (hMcorrect p.1 p.2 hp)⟩
  have hMbigStart : M ⊆ bigStart (S.restrictLabels Ls') G Lo T := by
    intro p hp
    refine mem_bigStart.mpr ⟨hMsub hp, fun hpLo => ?_⟩
    have : p ∈ M.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨hp, hpLo⟩
    rw [hMrestrict] at this
    exact (Typing.mem_restrictTo.mp this).1
  have hind : ∀ n, M ⊆ (refineStep (S.restrictLabels Ls') G Lo)^[n] (bigStart (S.restrictLabels Ls') G Lo T) := by
    intro n
    induction n with
    | zero => exact hMbigStart
    | succ n ihn =>
        rw [Function.iterate_succ_apply']
        set curn := (refineStep (S.restrictLabels Ls') G Lo)^[n] (bigStart (S.restrictLabels Ls') G Lo T)
          with hcurn_def
        have hcurn_restrict : curn.restrictTo Lo = T.restrictTo Lo := iterate_refineStep_restrictTo hTsub' n
        have hagree : ∀ n' L', L' ∈ Lo → ((n', L') ∈ M ↔ (n', L') ∈ curn) := by
          intro n' L' hL'
          have h1 : ((n', L') ∈ M ↔ (n', L') ∈ T) := by
            constructor
            · intro hmem
              have : (n', L') ∈ M.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨hmem, hL'⟩
              rw [hMrestrict] at this
              exact (Typing.mem_restrictTo.mp this).1
            · intro hmem
              have : (n', L') ∈ T.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨hmem, hL'⟩
              rw [← hMrestrict] at this
              exact (Typing.mem_restrictTo.mp this).1
          have h2 : ((n', L') ∈ curn ↔ (n', L') ∈ T) := by
            constructor
            · intro hmem
              have : (n', L') ∈ curn.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨hmem, hL'⟩
              rw [hcurn_restrict] at this
              exact (Typing.mem_restrictTo.mp this).1
            · intro hmem
              have : (n', L') ∈ T.restrictTo Lo := Typing.mem_restrictTo.mpr ⟨hmem, hL'⟩
              rw [← hcurn_restrict] at this
              exact (Typing.mem_restrictTo.mp this).1
          exact h1.trans h2.symm
        intro p hp
        apply mem_refineStep.mpr
        refine ⟨ihn hp, ?_⟩
        by_cases hpLo : p.2 ∈ Lo
        · exact Or.inl hpLo
        · refine Or.inr (Satisfies.stratMono (G := G) (ihn) hagree (S.shapeDef p.2)
            (hLsneg p.2 (Finset.mem_product.mp (hMsub hp)).2) p.1 ?_)
          exact hMcorrect p.1 p.2 hp
  exact hind (bigStart (S.restrictLabels Ls') G Lo T).card

/-- The core lemma for one stratum: `refine1` computes exactly
`maxAgree`. -/
theorem refine1_eq_maxAgree {S : Schema} {G : Graph} {Ls' Lo : Finset Label}
    {T : Typing} (hLoLs' : Lo ⊆ Ls')
    (hLoself : ∀ L ∈ Lo, (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps ⊆ Lo)
    (hTsub : T ⊆ (S.restrictLabels Lo).univTyping G)
    (hTcorrect : (S.restrictLabels Lo).CorrTyping G T)
    (hLsneg : ∀ L ∈ Ls', (S.shapeDef L).negDeps ⊆ Lo) :
    refine1 (S.restrictLabels Ls') G Lo T = maxAgree (S.restrictLabels Ls') G Lo T := by
  apply Finset.Subset.antisymm
  · have hTsub' : T ⊆ (S.restrictLabels Ls').univTyping G := hTsub.trans (Schema.univTyping_mono hLoLs')
    exact subset_maxAgree (refine1_subset _ G Lo T |>.trans
      (fun p hp => (mem_bigStart.mp hp).1)) (refine1_correct hLoLs' hLoself hTsub hTcorrect)
      (refine1_restrictTo hTsub')
  · exact maxAgree_subset_refine1 hLoLs' hTsub hTcorrect hLsneg

/-!
Connection across the strata. `refineAlg` follows the recursion of `typ`
exactly. It uses `refine1` (the real procedure) in place of `maxAgree`
(the declarative description "union of correct typings"). The core lemma
above shows that the two are equal at each step. Thus, they are equal at
all steps, and also at `str.k`.
-/

/-- The recursion over the strata that Algorithm 1 does:

* `refineAlg S str G 0 := ∅`.
* Each next stratum starts from `bigStart` (lines 3–5 of `refine`) and
  refines down to a fixed point (lines 6–12). The result of the previous
  stratum is the "frozen" part of the initial guess. -/
noncomputable def refineAlg (S : Schema) (str : Label → ℕ) (G : Graph) : ℕ → Typing
  | 0 => ∅
  | i + 1 => refine1 (S.stratRestrict str (i + 1)) G (S.stratum str i) (refineAlg S str G i)

/-- Algorithm 1 (`refine`), run for all the `str.k` strata of `S`. -/
noncomputable def Algorithm1 (G : Graph) (S : Schema) (str : Strat S) : Typing :=
  refineAlg S str.str G str.k

/-- `S.stratRestrict str i` and `S.restrictLabels (S.stratum str i)` make
the same schema (the same `labels` and the same `shapeDef`). Thus, the
core lemma `refine1_eq_maxAgree` applies directly to `stratRestrict`,
although its statement uses the more general `restrictLabels`. -/
theorem Schema.stratRestrict_eq_restrictLabels (S : Schema) (str : Label → ℕ) (i : ℕ) :
    S.stratRestrict str i = S.restrictLabels (S.stratum str i) := rfl

/-- The recursion of Algorithm 1 over the strata computes exactly the same
result as `typ` (the declarative construction of Definition 4), at each
stratum.

The proof applies the core lemma (`refine1_eq_maxAgree`) to each stratum of
`S`. The hypotheses for each step come from these results:

* `Schema.stratum_mono` (`Lo ⊆ Ls'`).
* `Schema.stratum_self_contained` (`hLoself`).
* `typ_correct` (`hTsub` and `hTcorrect`).
* `neg_strict` of the stratification (`hLsneg`, as in the inductive step
  of `typ_correct`). -/
theorem refineAlg_eq_typ (S : Schema) (str : Strat S) (hClosed : S.Closed)
    (G : Graph) : ∀ i : ℕ, refineAlg S str.str G i = typ S str.str G i
  | 0 => rfl
  | i + 1 => by
      have ih := refineAlg_eq_typ S str hClosed G i
      obtain ⟨hsub_i, hcorrect_i⟩ := typ_correct S str hClosed G i
      have hLoLs' : S.stratum str.str i ⊆ S.stratum str.str (i + 1) :=
        Schema.stratum_mono (Nat.le_succ i)
      have hLoself := S.stratum_self_contained str hClosed i
      have hTsub : typ S str.str G i ⊆
          (S.restrictLabels (S.stratum str.str i)).univTyping G := by
        rw [← Schema.stratRestrict_eq_restrictLabels]; exact hsub_i
      have hTcorrect : (S.restrictLabels (S.stratum str.str i)).CorrTyping G
          (typ S str.str G i) := by
        rw [← Schema.stratRestrict_eq_restrictLabels]; exact hcorrect_i
      have hLsneg : ∀ L ∈ S.stratum str.str (i + 1),
          (S.shapeDef L).negDeps ⊆ S.stratum str.str i := by
        intro L hL L2 hL2
        simp only [Schema.stratum, Finset.mem_filter] at hL
        obtain ⟨hLlabels, hLstrat⟩ := hL
        have hL2labels : L2 ∈ S.labels := hClosed L hLlabels (Finset.mem_union_right _ hL2)
        have hstratlt := str.neg_strict L hLlabels L2 hL2
        simp only [Schema.stratum, Finset.mem_filter]
        exact ⟨hL2labels, by omega⟩
      show refine1 (S.stratRestrict str.str (i + 1)) G (S.stratum str.str i)
          (refineAlg S str.str G i) =
        maxAgree (S.stratRestrict str.str (i + 1)) G (S.stratum str.str i)
          (typ S str.str G i)
      rw [ih, Schema.stratRestrict_eq_restrictLabels]
      exact refine1_eq_maxAgree hLoLs' hLoself hTsub hTcorrect hLsneg

/-- Algorithm 1 is correct. The refinement procedure, run for all the
`str.k` strata, computes exactly `Typing(G, S, str)` (Definition 4). §4.1
of the paper says this. -/
theorem algorithm1_correct (G : Graph) (S : Schema) (str : Strat S)
    (hClosed : S.Closed) : Algorithm1 G S str = MTyping G S str :=
  refineAlg_eq_typ S str hClosed G str.k

end ShexLean
