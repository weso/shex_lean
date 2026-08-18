import ShexLean.Common.FixedPoint
import ShexLean.Shex2017Schemas.Lemma2

/-!
§4.1: Algorithm 1 (`refine`), and its correctness — it computes
`Typing(G, S, str)` (Definition 4).

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

Each outer iteration `i` is a *greatest fixed point* computation: start from
the largest plausible typing for `S_i` (everything already fixed for
`S_{i-1}`, plus every possible guess for the new labels), then repeatedly
strip out anything that currently fails `⊢`, until nothing more can be
removed. This file formalizes that per-stratum computation
(`refineStep`/`refine1`), proves it equals `maxAgree` (hence
`Definition 4`'s own per-stratum construction), and chains that across all
`k` strata to get `Algorithm1 G S str = MTyping G S str`.
-/

namespace ShexLean

/-- The initial guess for stratum `S'` relative to the previous stratum's
`(Lo, T)`: keep `T`'s contribution on `Lo` exactly, and guess every
possible node-type association for the rest of `S'`'s labels. Lines 3–5 of
`refine`. -/
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

/-- One refinement pass: drop any node-type association for a label
outside `Lo` that doesn't currently satisfy `⊢`. Lines 9–12 of `refine`
(one full pass over the loop body — the paper's `while changing` repeats
this until nothing more changes, i.e. iterates this to a fixed point). -/
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

/-- `refineStep` never touches (adds or removes) a `Lo`-labeled pair. -/
theorem refineStep_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label} {current : Typing} :
    (refineStep S' G Lo current).restrictTo Lo = current.restrictTo Lo := by
  apply Finset.ext
  rintro ⟨n, L⟩
  simp only [Typing.mem_restrictTo, mem_refineStep]
  constructor
  · rintro ⟨⟨hmem, -⟩, hL⟩; exact ⟨hmem, hL⟩
  · rintro ⟨hmem, hL⟩; exact ⟨⟨hmem, Or.inl hL⟩, hL⟩

/-- The per-stratum computation `refine` performs: start from `bigStart`
and iterate `refineStep` to a fixed point (`Finset.card`-many iterations
always suffice, by `Finset.decreasing_iterate_fixed`). -/
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
**Core lemma**: `refine1` computes the same thing as `maxAgree`
(Proposition1.lean/Lemma2.lean's own construction of the same object,
via the union of all correct typings, rather than iterative refinement).
-/

/-- `refine1 S' G Lo T` is correct for `S'`: on `Lo` it inherits `T`'s
correctness (via `Satisfies.agree`, since `Lo` is self-contained), and
outside `Lo` it holds directly from `refine1` being a fixed point of
`refineStep`. -/
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

/-- `maxAgree` is itself a fixed point of `refineStep` (its own
correctness gives the "keep" side of the filter for free), and starts
below `bigStart`, so it stays below every iterate — in particular below
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

/-- The per-stratum core lemma: `refine1` computes exactly `maxAgree`. -/
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
**Chaining across strata.** `refineAlg` mirrors `typ`'s
recursion exactly, replacing `maxAgree` (the declarative "union of
correct typings" description) with `refine1` (the actual procedure); the
per-stratum core lemma above shows the two agree at every step, so the two
recursions agree everywhere, and in particular at `str.k`.
-/

/-- The per-stratum recursion Algorithm 1 performs: `refineAlg S str G 0
:= ∅`, and each successor stratum refines from `bigStart` (lines 3–5 of
`refine`) down to a fixed point (lines 6–12), reusing the previous
stratum's result as the "frozen" part of the initial guess. -/
noncomputable def refineAlg (S : Schema) (str : Label → ℕ) (G : Graph) : ℕ → Typing
  | 0 => ∅
  | i + 1 => refine1 (S.stratRestrict str (i + 1)) G (S.stratum str i) (refineAlg S str G i)

/-- Algorithm 1 (`refine`), run for all `str.k` strata of `S`. -/
noncomputable def Algorithm1 (G : Graph) (S : Schema) (str : Strat S) : Typing :=
  refineAlg S str.str G str.k

/-- `S.stratRestrict str i` and `S.restrictLabels (S.stratum str i)`
build the identical schema (same `labels`, same `shapeDef`) — this lets the
per-stratum core lemma `refine1_eq_maxAgree` (stated in terms of
the more general `restrictLabels`) apply directly to `stratRestrict`. -/
theorem Schema.stratRestrict_eq_restrictLabels (S : Schema) (str : Label → ℕ) (i : ℕ) :
    S.stratRestrict str i = S.restrictLabels (S.stratum str i) := rfl

/-- Algorithm 1's per-stratum recursion computes exactly what
`typ` (Definition 4's declarative construction) computes, at
every stratum. Chains the per-stratum core lemma
(`refine1_eq_maxAgree`) across all of `S`'s strata: the hypotheses
it needs at each step come from `Schema.stratum_mono` (for `Lo ⊆ Ls'`),
`Schema.stratum_self_contained` (for `hLoself`), `typ_correct`
(for `hTsub`/`hTcorrect`), and the stratification's `neg_strict` (for
`hLsneg`, exactly as in `typ_correct`'s own inductive step). -/
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

/-- **Algorithm 1's correctness.** The per-stratum refinement procedure,
run for all `str.k` strata, computes exactly `Typing(G, S, str)`
(Definition 4) — Algorithm 1 as described in §4.1 of the paper really does
compute the semantics it claims to. -/
theorem algorithm1_correct (G : Graph) (S : Schema) (str : Strat S)
    (hClosed : S.Closed) : Algorithm1 G S str = MTyping G S str :=
  refineAlg_eq_typ S str hClosed G str.k

end ShexLean
