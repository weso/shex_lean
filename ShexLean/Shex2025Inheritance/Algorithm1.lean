import ShexLean.Shex2025Inheritance.Lemma2

/-!
§5: the validation/refinement algorithm (`refine`), and its correctness for
ShEx with inheritance — it computes `Typing8 G S strat` (Definition 8,
`τ_max(S,σ,G)`), for a well-formed schema `S` (`WellFormedX`/
`ExtAcyclic`/`WellFormedExtra`/`NotIsExtendsFree`/`DClosed`) and
stratification `strat`.

```
Input: G: a graph, S = (Y,X,def,A): a schema, strat a stratification for S
       with k strata
Output: τ_max(S,strat,G)
1  typing ← ∅;
2  for i from 1 to k do
     // Add all node-type associations for stratum i
3    foreach n in Nodes(G) do
4      foreach L in (Y∪X)_i do
5        add (n, L) to typing;
     // Refine w.r.t. the types on stratum i
6    changing ← true;
7    while changing do
8      changing ← false;
9      foreach (n, L) in typing s.t. L ∈ (Y∪X)_i do
10       if not typing, n ⊨_S def(L) then
11         remove (n, L) from typing;
12         changing ← true;
13   return typing
```

Per stratum, this is a greatest-fixed-point computation: start from every
possible node-type guess for the new stratum, frozen agreement with the
previous stratum, then repeatedly strip out anything currently failing
`⊨_S` (Definition 4) until nothing more can be removed. `Satisfies`
depends on the schema (via `.anc`/`.ancSet`), so crossing between
differently-restricted schemas (`S.restrictLabels Lo` vs
`S.restrictLabels Ls'`) needs the schema-invariance machinery `ShexLean/
Shex2025Inheritance/Lemma2.lean` provides
(`Satisfies_restrictLabels_agree`, `Schema.correctTyping_stratRestrict_mono`). -/

namespace ShexLean.Inheritance

/-- A purely order-theoretic fact used to show the per-stratum refinement
loop actually reaches a fixed point: iterating any *decreasing* self-map of
a finite type stabilizes within `x.card` steps (pure `Finset`/
`Function.iterate` reasoning, no schema content). -/
theorem Finset.decreasing_iterate_fixed {α : Type*} [DecidableEq α] (f : Finset α → Finset α)
    (hf : ∀ t, f t ⊆ t) (x : Finset α) : f (f^[x.card] x) = f^[x.card] x := by
  have hfix : ∀ (y : Finset α), f y = y → ∀ n, f^[n] y = y := by
    intro y hy n
    induction n with
    | zero => rfl
    | succ n ihn => rw [Function.iterate_succ_apply', ihn, hy]
  induction hcard : x.card using Nat.strong_induction_on generalizing x with
  | _ card ih =>
    by_cases heq : f x = x
    · rw [hfix x heq card]
      exact heq
    · have hsub := hf x
      have hlt : (f x).card < x.card := Finset.card_lt_card (hsub.ssubset_of_ne heq)
      have hcard' : (f x).card < card := hcard ▸ hlt
      have hxne : x ≠ ∅ := by rintro rfl; exact heq (by simpa using hf (∅ : Finset α))
      have hcardpos : 0 < card := by
        rw [← hcard]; exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hxne)
      have hih := ih (f x).card hcard' (f x) rfl
      have hpad : ∀ n, (f x).card ≤ n → f^[n] (f x) = f^[(f x).card] (f x) := by
        intro n hn
        obtain ⟨k, rfl⟩ : ∃ k, n = k + (f x).card := ⟨n - (f x).card, by omega⟩
        rw [Function.iterate_add_apply]
        exact hfix (f^[(f x).card] (f x)) hih k
      have hstep : f^[card] x = f^[card - 1] (f x) := by
        conv_lhs => rw [show card = (card - 1) + 1 by omega]
        rw [Function.iterate_succ_apply]
      rw [hstep, hpad (card - 1) (by omega)]
      exact hih

/-- The initial guess for stratum `S'` relative to the previous stratum's
`(Lo, T)`: keep `T`'s contribution on `Lo` exactly, and guess every possible
node-type association for the rest of `S'`'s labels. Lines 3-5 of `refine`. -/
def bigStart (S' : Schema) (G : Graph) (Lo : Finset Label) (T : Typing) : Typing :=
  (S'.univTyping G).filter (fun p => p.2 ∈ Lo → p ∈ T)

theorem mem_bigStart {S' : Schema} {G : Graph} {Lo : Finset Label} {T : Typing}
    {p : Assoc} : p ∈ bigStart S' G Lo T ↔ p ∈ S'.univTyping G ∧ (p.2 ∈ Lo → p ∈ T) :=
  Finset.mem_filter

theorem bigStart_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label} {T : Typing}
    (hTsub : T ⊆ S'.univTyping G) :
    restrictTyping (bigStart S' G Lo T) Lo = restrictTyping T Lo := by
  apply Finset.ext
  rintro ⟨n, L⟩
  simp only [mem_restrictTyping, mem_bigStart]
  constructor
  · rintro ⟨⟨-, h⟩, hL⟩; exact ⟨h hL, hL⟩
  · rintro ⟨h, hL⟩; exact ⟨⟨hTsub h, fun _ => h⟩, hL⟩

/-- One refinement pass: drop any node-type association for a label
outside `Lo` that doesn't currently satisfy `⊨_S`. Lines 9-12 of `refine`
(one full pass over the loop body — the paper's `while changing` repeats
this until nothing more changes, i.e. iterates this to a fixed point). The
per-pair keep-condition mirrors `Schema.CorrectTyping`'s own two-bullet
shape exactly — line 10's "not `typing, n ⊨_S def(L)`" really means "not
locally correct at `(n,L)`", not just "not `Satisfies ... def(L)`" (an
abstract `L` is never itself directly `Satisfies`-checked; Definition 4
instead requires some *descendant* to be). -/
def Schema.locallyCorrect (S' : Schema) (G : Graph) (τ : Typing) (p : Assoc) : Prop :=
  (p.2 ∉ S'.A → Satisfies S' G τ p.1 (S'.shapeDef p.2)) ∧
  (p.2 ∈ S'.A → ∃ x ∈ S'.desc p.2 \ S'.A, Satisfies S' G τ p.1 (S'.shapeDef x))

noncomputable def refineStep (S' : Schema) (G : Graph) (Lo : Finset Label)
    (current : Typing) : Typing :=
  haveI := Classical.decPred (fun p : Assoc => p.2 ∈ Lo ∨ S'.locallyCorrect G current p)
  current.filter (fun p => p.2 ∈ Lo ∨ S'.locallyCorrect G current p)

theorem mem_refineStep {S' : Schema} {G : Graph} {Lo : Finset Label} {current : Typing}
    {p : Assoc} :
    p ∈ refineStep S' G Lo current ↔
      p ∈ current ∧ (p.2 ∈ Lo ∨ S'.locallyCorrect G current p) := by
  unfold refineStep
  simp only [Finset.mem_filter]

theorem refineStep_subset (S' : Schema) (G : Graph) (Lo : Finset Label) (current : Typing) :
    refineStep S' G Lo current ⊆ current := by
  intro p hp; exact (mem_refineStep.mp hp).1

/-- `refineStep` never touches (adds or removes) a `Lo`-labeled pair. -/
theorem refineStep_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label} {current : Typing} :
    restrictTyping (refineStep S' G Lo current) Lo = restrictTyping current Lo := by
  apply Finset.ext
  rintro ⟨n, L⟩
  simp only [mem_restrictTyping, mem_refineStep]
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
  Finset.decreasing_iterate_fixed (refineStep S' G Lo) (refineStep_subset S' G Lo)
    (bigStart S' G Lo T)

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
    ∀ n, restrictTyping ((refineStep S' G Lo)^[n] (bigStart S' G Lo T)) Lo = restrictTyping T Lo := by
  intro n
  induction n with
  | zero => exact bigStart_restrictTo hTsub
  | succ n ihn =>
      rw [Function.iterate_succ_apply', refineStep_restrictTo, ihn]

theorem refine1_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label} {T : Typing}
    (hTsub : T ⊆ S'.univTyping G) : restrictTyping (refine1 S' G Lo T) Lo = restrictTyping T Lo :=
  iterate_refineStep_restrictTo hTsub _

/-!
**Core lemma**: `refine1` computes the same thing as `maxTypingAgreeing`
(`ShexLean/Shex2025Inheritance/Proposition1.lean`'s own construction of the
same object, via the union of all correct typings, rather than iterative
refinement).
-/

/-- A typing correct at `Lo`'s schema level, and confined to `Lo`-labelled
pairs, is automatically correct at any bigger `D_S`-closed schema level
`Ls' ⊇ Lo` too — no *new* pairs to check, and the schema-invariance facts
(`Satisfies_restrictLabels_agree`, `Schema.restrictLabels_desc_eq`) show
the checks for the *existing* pairs transport unchanged. -/
theorem correctTyping_restrictLabels_lift {S : Schema} (hWFX : S.WellFormedX)
    (hAcyclic : S.ExtAcyclic) {G : Graph} {Lo Ls' : Finset Label} {T : Typing}
    (hLoLs' : Lo ⊆ Ls') (hLoClosed : S.DClosedOn Lo) (hLs'Closed : S.DClosedOn Ls')
    (hTsub : T ⊆ (S.restrictLabels Lo).univTyping G)
    (hTcorrect : (S.restrictLabels Lo).CorrectTyping G T) :
    (S.restrictLabels Ls').CorrectTyping G T := by
  intro n L hmem
  have hLLo : L ∈ Lo := Schema.restrictLabels_mem_YX_subset S Lo (Finset.mem_product.mp (hTsub hmem)).2
  obtain ⟨hSatPlain, hSatAbs⟩ := hTcorrect n L hmem
  have htransport : ∀ x, x ∈ Lo → Satisfies (S.restrictLabels Lo) G T n (S.shapeDef x) →
      Satisfies (S.restrictLabels Ls') G T n (S.shapeDef x) := by
    intro x hx hSat
    exact (Satisfies_restrictLabels_agree hWFX hAcyclic hLoLs' hLoClosed hLs'Closed hx).mp hSat
  have hALoLs' : L ∈ (S.restrictLabels Lo).A ↔ L ∈ (S.restrictLabels Ls').A := by
    simp only [Schema.restrictLabels, Finset.mem_inter]
    constructor
    · rintro ⟨h, -⟩; exact ⟨h, hLoLs' hLLo⟩
    · rintro ⟨h, -⟩; exact ⟨h, hLLo⟩
  refine ⟨fun hLnA => htransport L hLLo (hSatPlain (fun h => hLnA (hALoLs'.mp h))), fun hLA => ?_⟩
  obtain ⟨x, hxmem, hSatx⟩ := hSatAbs (hALoLs'.mpr hLA)
  rw [Finset.mem_sdiff] at hxmem
  have hxdescLo : x ∈ (S.restrictLabels Lo).desc L := hxmem.1
  rw [Schema.restrictLabels_desc_eq hLoClosed hLLo] at hxdescLo
  have hxLo : x ∈ Lo := Schema.desc_subset_of_DClosedOn hLoClosed hLLo hxdescLo
  have hxnA : x ∉ S.A := by
    simp only [Schema.restrictLabels, Finset.mem_inter] at hxmem
    exact fun h => hxmem.2 ⟨h, hxLo⟩
  refine ⟨x, ?_, htransport x hxLo hSatx⟩
  rw [Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · rw [Schema.restrictLabels_desc_eq hLs'Closed (hLoLs' hLLo)]; exact hxdescLo
  · simp only [Schema.restrictLabels, Finset.mem_inter]
    exact fun h => hxnA h.1

/-- `refine1 S' G Lo T` is correct: on `Lo` it inherits `T`'s correctness
(via `Satisfies.agree` — a *typing*-agreement step — chained with
`Satisfies_restrictLabels_agree` — a *schema*-restriction-level step,
needed since `T`'s own correctness is witnessed at `Lo`'s schema level but
`Satisfies.agree` alone only ever compares two typings against a *single*
fixed schema); outside `Lo` it holds directly from `refine1` being a fixed
point of `refineStep`. -/
theorem refine1_correct {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic)
    {G : Graph} {Ls' Lo : Finset Label} {T : Typing}
    (hLoLs' : Lo ⊆ Ls') (hLoClosed : S.DClosedOn Lo) (hLs'Closed : S.DClosedOn Ls')
    (hTsub : T ⊆ (S.restrictLabels Lo).univTyping G)
    (hTcorrect : (S.restrictLabels Lo).CorrectTyping G T) :
    (S.restrictLabels Ls').CorrectTyping G (refine1 (S.restrictLabels Ls') G Lo T) := by
  have hWFX' : (S.restrictLabels Ls').WellFormedX := Schema.restrictLabels_WellFormedX hWFX Ls'
  have hWFXLo : (S.restrictLabels Lo).WellFormedX := Schema.restrictLabels_WellFormedX hWFX Lo
  intro n L hmem
  by_cases hL : L ∈ Lo
  · have hTsub' : T ⊆ (S.restrictLabels Ls').univTyping G :=
      hTsub.trans (Schema.univTyping_mono hLoLs')
    have hrestr := refine1_restrictTo (S' := S.restrictLabels Ls') (Lo := Lo) hTsub'
    have hagree : ∀ n' L', L' ∈ Lo → ((n', L') ∈ T ↔ (n', L') ∈ refine1 (S.restrictLabels Ls') G Lo T) :=
      restrictTyping_agree hrestr.symm
    have hmemT : (n, L) ∈ T := (hagree n L hL).mpr hmem
    obtain ⟨hSatPlain, hSatAbs⟩ := hTcorrect n L hmemT
    have hdepsL : (S.shapeDef L).depsIn Lo := Schema.shapeDef_depsIn hLoClosed hL
    -- A single "transport correctness of a `Lo`-confined label from `T` to
    -- `refine1 ... Lo T`, at schema level `Ls'`" step, reused by both the
    -- plain and abstract cases below.
    have htransport : ∀ x, x ∈ Lo → Satisfies (S.restrictLabels Lo) G T n (S.shapeDef x) →
        Satisfies (S.restrictLabels Ls') G (refine1 (S.restrictLabels Ls') G Lo T) n
          (S.shapeDef x) := by
      intro x hx hSat
      have hdepsx : (S.shapeDef x).depsIn Lo := Schema.shapeDef_depsIn hLoClosed hx
      have hstep1 : Satisfies (S.restrictLabels Lo) G T n (S.shapeDef x) ↔
          Satisfies (S.restrictLabels Lo) G (refine1 (S.restrictLabels Ls') G Lo T) n
            (S.shapeDef x) :=
        Satisfies.agree hWFXLo (Schema.restrictLabels_ExtAcyclic hAcyclic Lo) hLoClosed hagree hdepsx n
      have hstep2 : Satisfies (S.restrictLabels Lo) G (refine1 (S.restrictLabels Ls') G Lo T) n
            (S.shapeDef x) ↔
          Satisfies (S.restrictLabels Ls') G (refine1 (S.restrictLabels Ls') G Lo T) n
            (S.shapeDef x) :=
        Satisfies_restrictLabels_agree hWFX hAcyclic hLoLs' hLoClosed hLs'Closed hx
      exact (hstep1.trans hstep2).mp hSat
    have hALoLs' : L ∈ (S.restrictLabels Lo).A ↔ L ∈ (S.restrictLabels Ls').A := by
      simp only [Schema.restrictLabels, Finset.mem_inter]
      constructor
      · rintro ⟨h, -⟩; exact ⟨h, hLoLs' hL⟩
      · rintro ⟨h, -⟩; exact ⟨h, hL⟩
    refine ⟨fun hLnA => htransport L hL (hSatPlain (fun h => hLnA (hALoLs'.mp h))), fun hLA => ?_⟩
    obtain ⟨x, hxmem, hSatx⟩ := hSatAbs (hALoLs'.mpr hLA)
    rw [Finset.mem_sdiff] at hxmem
    have hxdescLo : x ∈ (S.restrictLabels Lo).desc L := hxmem.1
    have hxnALo : x ∉ (S.restrictLabels Lo).A := hxmem.2
    rw [Schema.restrictLabels_desc_eq hLoClosed hL] at hxdescLo
    have hxLo : x ∈ Lo := Schema.desc_subset_of_DClosedOn hLoClosed hL hxdescLo
    have hxnA : x ∉ S.A := by
      simp only [Schema.restrictLabels, Finset.mem_inter] at hxnALo
      exact fun h => hxnALo ⟨h, hxLo⟩
    refine ⟨x, ?_, htransport x hxLo hSatx⟩
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [Schema.restrictLabels_desc_eq hLs'Closed (hLoLs' hL)]; exact hxdescLo
    · simp only [Schema.restrictLabels, Finset.mem_inter]
      exact fun h => hxnA h.1
  · have hfixed := refine1_fixed (S.restrictLabels Ls') G Lo T
    rw [← hfixed] at hmem
    rcases mem_refineStep.mp hmem with ⟨-, hcase⟩
    exact hcase.resolve_left hL

/-- `maxTypingAgreeing` is itself a fixed point of `refineStep` (its own
correctness gives the "keep" side of the filter for free, via
`correctTyping_restrictLabels_lift` + `maxTypingAgreeing_correct`), and
starts below `bigStart`, so it stays below every iterate — in particular
below `refine1`. -/
theorem maxTypingAgreeing_subset_refine1 {S : Schema} (hWFX : S.WellFormedX)
    (hAcyclic : S.ExtAcyclic) (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree)
    {G : Graph} {Ls' Lo : Finset Label} {T : Typing} (hLoLs' : Lo ⊆ Ls')
    (hLoClosed : S.DClosedOn Lo) (hLs'Closed : S.DClosedOn Ls') (hLs'YX : Ls' ⊆ S.Y ∪ S.X)
    (hTsub : T ⊆ (S.restrictLabels Lo).univTyping G)
    (hTcorrect : (S.restrictLabels Lo).CorrectTyping G T)
    (hLsneg : ∀ z ∈ (S.restrictLabels Ls').Y ∪ (S.restrictLabels Ls').X,
      ((S.shapeDef z).depsAux false).negRefs ⊆ Lo) :
    maxTypingAgreeing (S.restrictLabels Ls') G Lo T ⊆ refine1 (S.restrictLabels Ls') G Lo T := by
  set M := maxTypingAgreeing (S.restrictLabels Ls') G Lo T with hM_def
  have hWFX' : (S.restrictLabels Ls').WellFormedX := Schema.restrictLabels_WellFormedX hWFX Ls'
  have hAcyclic' : (S.restrictLabels Ls').ExtAcyclic := Schema.restrictLabels_ExtAcyclic hAcyclic Ls'
  have hDClosed' : (S.restrictLabels Ls').DClosedOn ((S.restrictLabels Ls').Y ∪ (S.restrictLabels Ls').X) :=
    Schema.restrictLabels_DClosed hLs'Closed hLs'YX
  have hTsub' : T ⊆ (S.restrictLabels Ls').univTyping G := hTsub.trans (Schema.univTyping_mono hLoLs')
  have hTcorrect' : (S.restrictLabels Ls').CorrectTyping G T :=
    correctTyping_restrictLabels_lift hWFX hAcyclic hLoLs' hLoClosed hLs'Closed hTsub hTcorrect
  have hMcorrect : (S.restrictLabels Ls').CorrectTyping G M :=
    maxTypingAgreeing_correct hWFX' hAcyclic' hWFExtra hNEF hDClosed' hTsub' hTcorrect' hLsneg
  have hMsub : M ⊆ (S.restrictLabels Ls').univTyping G := maxTypingAgreeing_subset _ G _ _
  have hMrestrict : restrictTyping M Lo = restrictTyping T Lo :=
    maxTypingAgreeing_restrictTo hTsub' hTcorrect'
  have hMfixed : refineStep (S.restrictLabels Ls') G Lo M = M := by
    apply Finset.Subset.antisymm (refineStep_subset _ G Lo M)
    intro p hp
    exact mem_refineStep.mpr ⟨hp, Or.inr (hMcorrect p.1 p.2 hp)⟩
  have hMbigStart : M ⊆ bigStart (S.restrictLabels Ls') G Lo T := by
    intro p hp
    refine mem_bigStart.mpr ⟨hMsub hp, fun hpLo => ?_⟩
    have : p ∈ restrictTyping M Lo := mem_restrictTyping.mpr ⟨hp, hpLo⟩
    rw [hMrestrict] at this
    exact (mem_restrictTyping.mp this).1
  have hind : ∀ n, M ⊆ (refineStep (S.restrictLabels Ls') G Lo)^[n] (bigStart (S.restrictLabels Ls') G Lo T) := by
    intro n
    induction n with
    | zero => exact hMbigStart
    | succ n ihn =>
        rw [Function.iterate_succ_apply']
        set curn := (refineStep (S.restrictLabels Ls') G Lo)^[n]
          (bigStart (S.restrictLabels Ls') G Lo T) with hcurn_def
        have hcurn_restrict : restrictTyping curn Lo = restrictTyping T Lo :=
          iterate_refineStep_restrictTo hTsub' n
        have hagree : ∀ n' L', L' ∈ Lo → ((n', L') ∈ M ↔ (n', L') ∈ curn) := by
          intro n' L' hL'
          have h1 : ((n', L') ∈ M ↔ (n', L') ∈ T) := by
            constructor
            · intro hmem
              have : (n', L') ∈ restrictTyping M Lo := mem_restrictTyping.mpr ⟨hmem, hL'⟩
              rw [hMrestrict] at this
              exact (mem_restrictTyping.mp this).1
            · intro hmem
              have : (n', L') ∈ restrictTyping T Lo := mem_restrictTyping.mpr ⟨hmem, hL'⟩
              rw [← hMrestrict] at this
              exact (mem_restrictTyping.mp this).1
          have h2 : ((n', L') ∈ curn ↔ (n', L') ∈ T) := by
            constructor
            · intro hmem
              have : (n', L') ∈ restrictTyping curn Lo := mem_restrictTyping.mpr ⟨hmem, hL'⟩
              rw [hcurn_restrict] at this
              exact (mem_restrictTyping.mp this).1
            · intro hmem
              have : (n', L') ∈ restrictTyping T Lo := mem_restrictTyping.mpr ⟨hmem, hL'⟩
              rw [← hcurn_restrict] at this
              exact (mem_restrictTyping.mp this).1
          exact h1.trans h2.symm
        intro p hp
        apply mem_refineStep.mpr
        refine ⟨ihn hp, ?_⟩
        by_cases hpLo : p.2 ∈ Lo
        · exact Or.inl hpLo
        · have hp2mem : p.2 ∈ (S.restrictLabels Ls').Y ∪ (S.restrictLabels Ls').X :=
            (Finset.mem_product.mp (hMsub hp)).2
          have hdeps : (S.shapeDef p.2).depsIn ((S.restrictLabels Ls').Y ∪ (S.restrictLabels Ls').X) :=
            Schema.shapeDef_depsIn hDClosed' hp2mem
          have hMcp := hMcorrect p.1 p.2 hp
          refine Or.inr ⟨fun hpnA => ?_, fun hpA => ?_⟩
          · exact stratMonoFuel hWFX' hAcyclic' hWFExtra hNEF hDClosed' (ihn) hagree hLsneg
              (S.shapeDef p.2) hdeps (hWFExtra p.2) (hNEF p.2) (hLsneg p.2 hp2mem)
              _ p.1 (hMcp.1 hpnA)
          · obtain ⟨x, hxmem, hSatx⟩ := hMcp.2 hpA
            have hxY : x ∈ (S.restrictLabels Ls').Y ∪ (S.restrictLabels Ls').X := by
              have hxdesc : x ∈ (S.restrictLabels Ls').desc p.2 := (Finset.mem_sdiff.mp hxmem).1
              rw [Schema.mem_desc] at hxdesc
              exact Finset.mem_union_right _ hxdesc.1
            have hxdeps : (S.shapeDef x).depsIn ((S.restrictLabels Ls').Y ∪ (S.restrictLabels Ls').X) :=
              Schema.shapeDef_depsIn hDClosed' hxY
            exact ⟨x, hxmem, stratMonoFuel hWFX' hAcyclic' hWFExtra hNEF hDClosed' (ihn) hagree hLsneg
              (S.shapeDef x) hxdeps (hWFExtra x) (hNEF x) (hLsneg x hxY) _ p.1 hSatx⟩
  exact hind (bigStart (S.restrictLabels Ls') G Lo T).card

/-- The per-stratum core lemma: `refine1` computes exactly `maxTypingAgreeing`. -/
theorem refine1_eq_maxTypingAgreeing {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree)
    {G : Graph} {Ls' Lo : Finset Label} {T : Typing} (hLoLs' : Lo ⊆ Ls')
    (hLoClosed : S.DClosedOn Lo) (hLs'Closed : S.DClosedOn Ls') (hLs'YX : Ls' ⊆ S.Y ∪ S.X)
    (hTsub : T ⊆ (S.restrictLabels Lo).univTyping G)
    (hTcorrect : (S.restrictLabels Lo).CorrectTyping G T)
    (hLsneg : ∀ z ∈ (S.restrictLabels Ls').Y ∪ (S.restrictLabels Ls').X,
      ((S.shapeDef z).depsAux false).negRefs ⊆ Lo) :
    refine1 (S.restrictLabels Ls') G Lo T = maxTypingAgreeing (S.restrictLabels Ls') G Lo T := by
  apply Finset.Subset.antisymm
  · have hTsub' : T ⊆ (S.restrictLabels Ls').univTyping G := hTsub.trans (Schema.univTyping_mono hLoLs')
    exact subset_maxTypingAgreeing (refine1_subset _ G Lo T |>.trans
      (fun p hp => (mem_bigStart.mp hp).1)) (refine1_correct hWFX hAcyclic hLoLs' hLoClosed hLs'Closed
      hTsub hTcorrect) (refine1_restrictTo hTsub')
  · exact maxTypingAgreeing_subset_refine1 hWFX hAcyclic hWFExtra hNEF hLoLs' hLoClosed hLs'Closed
      hLs'YX hTsub hTcorrect hLsneg

/-!
**Chaining across strata.** `refineAlg` mirrors `stratTypingSeq`'s recursion
exactly, replacing `maxTypingAgreeing` (the declarative "union of correct
typings" description) with `refine1` (the actual procedure); the
per-stratum core lemma above shows the two agree at every step, so the two
recursions agree everywhere, and in particular at `strat.k`.
-/

/-- The per-stratum recursion Algorithm 1 performs: `refineAlg S strat G 0
:= ∅`, and each successor stratum refines from `bigStart` (lines 3-5 of
`refine`) down to a fixed point (lines 6-12), reusing the previous
stratum's result as the "frozen" part of the initial guess. -/
noncomputable def refineAlg (S : Schema) (strat : Label → ℕ) (G : Graph) : ℕ → Typing
  | 0 => ∅
  | i + 1 => refine1 (S.stratRestrict strat (i + 1)) G (S.stratum strat i) (refineAlg S strat G i)

/-- Algorithm 1 (`refine`), run for all `strat.k` strata of `S`. -/
noncomputable def Algorithm1 (G : Graph) (S : Schema) (strat : Stratification S) : Typing :=
  refineAlg S strat.strat G strat.k

/-- Algorithm 1's per-stratum recursion computes exactly what
`stratTypingSeq` (Definition 8's declarative construction) computes, at
every stratum. Chains the per-stratum core lemma
(`refine1_eq_maxTypingAgreeing`) across all of `S`'s strata: the
hypotheses it needs at each step come from `Schema.stratum_mono` (for
`Lo ⊆ Ls'`), `Schema.stratum_DClosedOn` (for `hLoClosed`/`hLs'Closed`),
`stratTypingSeq_correct` (for `hTsub`/`hTcorrect`), and the
stratification's `negDep_lt` (for `hLsneg`, exactly as in
`stratTypingSeq_correct`'s own inductive step). -/
theorem refineAlg_eq_stratTypingSeq (S : Schema) (strat : Stratification S) (hWFX : S.WellFormedX)
    (hAcyclic : S.ExtAcyclic) (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree)
    (hDClosed : S.DClosed) (G : Graph) :
    ∀ i : ℕ, refineAlg S strat.strat G i = stratTypingSeq S strat.strat G i
  | 0 => rfl
  | i + 1 => by
      have ih := refineAlg_eq_stratTypingSeq S strat hWFX hAcyclic hWFExtra hNEF hDClosed G i
      obtain ⟨hsub_i, hcorrect_i⟩ :=
        stratTypingSeq_correct hWFX hAcyclic hWFExtra hNEF hDClosed strat G i
      have hLoLs' : S.stratum strat.strat i ⊆ S.stratum strat.strat (i + 1) :=
        Schema.stratum_mono (Nat.le_succ i)
      have hLoClosed : S.DClosedOn (S.stratum strat.strat i) :=
        Schema.stratum_DClosedOn hDClosed strat i
      have hLs'Closed : S.DClosedOn (S.stratum strat.strat (i + 1)) :=
        Schema.stratum_DClosedOn hDClosed strat (i + 1)
      have hLs'YX : S.stratum strat.strat (i + 1) ⊆ S.Y ∪ S.X := by
        intro z hz; simp only [Schema.stratum, Finset.mem_filter] at hz; exact hz.1
      have hTsub : stratTypingSeq S strat.strat G i ⊆
          (S.restrictLabels (S.stratum strat.strat i)).univTyping G := by
        rw [← Schema.stratRestrict_eq_restrictLabels]; exact hsub_i
      have hTcorrect : (S.restrictLabels (S.stratum strat.strat i)).CorrectTyping G
          (stratTypingSeq S strat.strat G i) := by
        rw [← Schema.stratRestrict_eq_restrictLabels]; exact hcorrect_i
      have hLsneg : ∀ z ∈ (S.restrictLabels (S.stratum strat.strat (i + 1))).Y ∪
            (S.restrictLabels (S.stratum strat.strat (i + 1))).X,
          ((S.shapeDef z).depsAux false).negRefs ⊆ S.stratum strat.strat i := by
        rw [← Schema.stratRestrict_eq_restrictLabels]
        intro z hz z' hz'
        simp only [Schema.stratRestrict, Finset.mem_union, Finset.mem_filter] at hz
        have hzY : z ∈ S.Y ∪ S.X := by
          rcases hz with ⟨h, _⟩ | ⟨h, _⟩
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ h
        have hDNeg : S.DNegEdge z z' := Or.inl hz'
        have hz'Y : z' ∈ S.Y ∪ S.X := hDClosed z hzY z' (S.DEdge_of_DNegEdge hDNeg)
        have hlt : strat.strat z' < strat.strat z := strat.negDep_lt z hzY z' hDNeg
        simp only [Schema.stratum, Finset.mem_filter]
        refine ⟨hz'Y, ?_⟩
        rcases hz with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
      show refine1 (S.stratRestrict strat.strat (i + 1)) G (S.stratum strat.strat i)
          (refineAlg S strat.strat G i) =
        maxTypingAgreeing (S.stratRestrict strat.strat (i + 1)) G (S.stratum strat.strat i)
          (stratTypingSeq S strat.strat G i)
      rw [ih, Schema.stratRestrict_eq_restrictLabels]
      exact refine1_eq_maxTypingAgreeing hWFX hAcyclic hWFExtra hNEF hLoLs' hLoClosed hLs'Closed
        hLs'YX hTsub hTcorrect hLsneg

/-- **Algorithm 1's correctness.** The per-stratum refinement procedure, run
for all `strat.k` strata, computes exactly `Typing8 G S strat`
(`τ_max(S,σ,G)`, Definition 8) — the §5 refinement algorithm, adapted to
ShEx with inheritance, really does compute the semantics it claims to. -/
theorem algorithm1_correct (G : Graph) (S : Schema) (strat : Stratification S)
    (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic) (hWFExtra : S.WellFormedExtra)
    (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed) :
    Algorithm1 G S strat = Typing8 G S strat :=
  refineAlg_eq_stratTypingSeq S strat hWFX hAcyclic hWFExtra hNEF hDClosed G strat.k

/-- **Algorithm 1 computes a correct typing** (combining `algorithm1_correct`
with `proposition1`) — the validation algorithm's output is trustworthy on
its own terms, not just "equal to an abstractly-defined object". -/
theorem algorithm1_correctTyping (G : Graph) (S : Schema) (strat : Stratification S)
    (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic) (hWFExtra : S.WellFormedExtra)
    (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed) :
    S.CorrectTyping G (Algorithm1 G S strat) := by
  rw [algorithm1_correct G S strat hWFX hAcyclic hWFExtra hNEF hDClosed]
  exact proposition1 hWFX hAcyclic hWFExtra hNEF hDClosed strat G

end ShexLean.Inheritance
