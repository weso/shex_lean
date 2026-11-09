import ShexLean.InheritanceCore.Schema
import Mathlib.Data.Finset.Powerset

/-!
The semantics-level part of "Shape Expressions with Inheritance" (2025)
that does not depend on the rules of Table 3: correct typings
(Definition 4), the maximal typing (Definition 8) and Proposition 1.

The class `InheritanceSemantics` gives the satisfaction relation of a
development, and the two facts about it that these proofs use:

* `satisfies_transfer`: `Satisfies` depends only on the typing and the
  schema in the labels that the shape expression can reach.
* `satisfies_stratMono`: `Satisfies` is monotone in the typing, if the
  typing does not change on the negative dependencies.

`ShexLean/Shex2025Inheritance/Proposition1.lean` and
`ShexLean/Shex2026InheritanceDisjunction/Proposition1.lean` prove these
two facts and give the instances. All the results of this file, of
`ShexLean/InheritanceCore/Lemma2.lean` and of
`ShexLean/InheritanceCore/Algorithm1.lean` then apply to the two
developments.
-/

namespace ShexLean.InheritanceCore

/-- The satisfaction relation `n, τ ⊨_S s` of a development, two
well-formedness conditions on shape expressions, and the two facts that
the proofs of Proposition 1, Lemma 2 and Algorithm 1 use. -/
class InheritanceSemantics (E : Type) [ShapeSyntax E] where
  /-- `n, τ ⊨_S s`. -/
  Satisfies : Schema E → Graph → Typing → RDFNode → E → Prop
  /-- The invariant "(*)" of the appendix proof of Proposition 1 (refer to
  `Shape.WellFormedExtra`), for each shape in a shape expression. -/
  WellFormedExtra : E → Prop
  /-- No `extends` below a `not`. -/
  NotIsExtendsFree : E → Prop
  satisfies_transfer {S1 S2 : Schema E} {G : Graph} {τ1 τ2 : Typing} {Z : Finset Label} {s : E}
    (hAc1 : S1.ExtAcyclic) (hAc2 : S2.ExtAcyclic) (hdef : S1.shapeDef = S2.shapeDef)
    (hZ : S1.DClosedOn Z) (hagree : AgreeOn τ1 τ2 Z) (hanc : ∀ x ∈ Z, S1.anc x = S2.anc x)
    (hdeps : depsIn s Z) (n : RDFNode) :
    Satisfies S1 G τ1 n s ↔ Satisfies S2 G τ2 n s
  satisfies_stratMono {S : Schema E} {G : Graph} {τ τ' : Typing} {Z Lo : Finset Label} {s : E}
    (hAcyclic : S.ExtAcyclic) (hWFExtra : ∀ ℓ, WellFormedExtra (S.shapeDef ℓ))
    (hNEF : ∀ ℓ, NotIsExtendsFree (S.shapeDef ℓ)) (hZ : S.DClosedOn Z) (hsub : τ ⊆ τ')
    (hagree : AgreeOn τ τ' Lo) (hLo : ∀ z ∈ Z, (ShapeSyntax.deps (S.shapeDef z)).negRefs ⊆ Lo)
    (n : RDFNode) (hdeps : depsIn s Z) (hWF : WellFormedExtra s) (hNEF' : NotIsExtendsFree s)
    (hneg : (ShapeSyntax.deps s).negRefs ⊆ Lo) :
    Satisfies S G τ n s → Satisfies S G τ' n s

export InheritanceSemantics (Satisfies satisfies_transfer satisfies_stratMono)

variable {E : Type} [ShapeSyntax E] [InheritanceSemantics E]

/-- "(*)" for the full schema: the definition of each label. -/
def Schema.WellFormedExtra (S : Schema E) : Prop :=
  ∀ ℓ, InheritanceSemantics.WellFormedExtra (S.shapeDef ℓ)

/-- "No `extends` below `not`" for the full schema. -/
def Schema.NotIsExtendsFree (S : Schema E) : Prop :=
  ∀ ℓ, InheritanceSemantics.NotIsExtendsFree (S.shapeDef ℓ)

/-- `Satisfies` depends on `τ` only through its restriction to `Z`, if
`s` reaches only labels of `Z` and `Z` is `D_S`-closed. -/
theorem Satisfies.agree {S : Schema E} (hAcyclic : S.ExtAcyclic)
    {G : Graph} {τ τ' : Typing} {Z : Finset Label} (hZ : S.DClosedOn Z)
    (hagree : AgreeOn τ τ' Z) {s : E} (hdeps : depsIn s Z)
    (n : RDFNode) : Satisfies S G τ n s ↔ Satisfies S G τ' n s :=
  satisfies_transfer hAcyclic hAcyclic rfl hZ hagree (fun _ _ => rfl) hdeps n

/-- Definition 4 (correct typing). -/
def Schema.CorrectTyping (S : Schema E) (G : Graph) (τ : Typing) : Prop :=
  ∀ n z, τ.has n z →
    (z ∉ S.A → Satisfies S G τ n (S.shapeDef z)) ∧
    (z ∈ S.A → ∃ x ∈ S.desc z \ S.A, Satisfies S G τ n (S.shapeDef x))

/-- The empty typing is trivially correct. It has no `(n,z)` pairs to
check. -/
theorem Schema.correctTyping_empty (S : Schema E) (G : Graph) : S.CorrectTyping G ∅ := by
  intro n z hz
  simp [Typing.has] at hz

/-! ### Definition 8 and Proposition 1 -/

/-- `maxTypingAgreeing S' G Lo fixed`: the union of all the correct typings
of `G` by `S'` that agree with `fixed` on `Lo`. This is a general form of
the "maximal correct typing" of `S'` (the case `Lo = ∅`). It adds the
agreement constraint that Definition 8 needs to connect the strata. It
agrees with `maxAgree` of 2017
(`ShexLean/Shex2017Schemas/Proposition1.lean`), with
`Schema.CorrectTyping` and `restrictTyping` in place of the 2017
versions. -/
noncomputable def maxTypingAgreeing (S' : Schema E) (G : Graph) (Lo : Finset Label)
    (fixed : Typing) : Typing :=
  haveI := Classical.decPred
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)
  ((S'.univTyping G).powerset.filter
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)).sup id

theorem subset_maxTypingAgreeing {S' : Schema E} {G : Graph} {Lo : Finset Label}
    {fixed t : Typing} (hsub : t ⊆ S'.univTyping G) (hcorrect : S'.CorrectTyping G t)
    (hagree : restrictTyping t Lo = restrictTyping fixed Lo) :
    t ⊆ maxTypingAgreeing S' G Lo fixed := by
  have := Classical.decPred
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)
  apply Finset.le_sup (f := id)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hcorrect, hagree⟩

theorem maxTypingAgreeing_subset (S' : Schema E) (G : Graph) (Lo : Finset Label)
    (fixed : Typing) : maxTypingAgreeing S' G Lo fixed ⊆ S'.univTyping G := by
  have := Classical.decPred
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)
  apply Finset.sup_le
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_powerset] at ht
  exact ht.1

theorem maxTypingAgreeing_restrictTo {S' : Schema E} {G : Graph} {Lo : Finset Label}
    {fixed : Typing} (hfixed_sub : fixed ⊆ S'.univTyping G)
    (hfixed_correct : S'.CorrectTyping G fixed) :
    restrictTyping (maxTypingAgreeing S' G Lo fixed) Lo = restrictTyping fixed Lo := by
  have := Classical.decPred
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)
  apply Finset.ext
  rintro ⟨n, L⟩
  rw [mem_restrictTyping, mem_restrictTyping]
  constructor
  · rintro ⟨hmem, hL⟩
    simp only [maxTypingAgreeing, Finset.mem_sup, Finset.mem_filter, Finset.mem_powerset,
      id] at hmem
    obtain ⟨t, ⟨_, _, htagree⟩, htmem⟩ := hmem
    have hin : (n, L) ∈ restrictTyping t Lo := mem_restrictTyping.mpr ⟨htmem, hL⟩
    rw [htagree] at hin
    exact ⟨(mem_restrictTyping.mp hin).1, hL⟩
  · rintro ⟨hmem, hL⟩
    exact ⟨subset_maxTypingAgreeing hfixed_sub hfixed_correct rfl hmem, hL⟩

/-- `maxTypingAgreeing` is also a correct typing, if `Lo` contains the
negative dependencies of each label of `S'`. The abstract-label case (the
second bullet of `Schema.CorrectTyping`) goes from `τ` to `τ'` in the same
way as the plain case. It applies `stratMono` to `S'.shapeDef x` (the
descendant that is the witness), not to `S'.shapeDef L`. -/
theorem maxTypingAgreeing_correct {S' : Schema E} (hAcyclic : S'.ExtAcyclic)
    (hWFExtra : S'.WellFormedExtra)
    (hNEF : S'.NotIsExtendsFree) (hDClosed : S'.DClosedOn (S'.Y ∪ S'.X)) {G : Graph}
    {Lo : Finset Label} {fixed : Typing} (hfixed_sub : fixed ⊆ S'.univTyping G)
    (hfixed_correct : S'.CorrectTyping G fixed)
    (hLo : ∀ z ∈ S'.Y ∪ S'.X, (ShapeSyntax.deps (S'.shapeDef z)).negRefs ⊆ Lo) :
    S'.CorrectTyping G (maxTypingAgreeing S' G Lo fixed) := by
  have := Classical.decPred
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)
  intro n L hmem
  simp only [maxTypingAgreeing, Finset.mem_sup, Finset.mem_filter, Finset.mem_powerset,
    id] at hmem
  obtain ⟨t, ⟨htsub, htcorrect, htagree⟩, htmem⟩ := hmem
  have hL : L ∈ S'.Y ∪ S'.X := (Finset.mem_product.mp (htsub htmem)).2
  have hsub_t : t ⊆ maxTypingAgreeing S' G Lo fixed :=
    subset_maxTypingAgreeing htsub htcorrect htagree
  have hagree_t : AgreeOn t (maxTypingAgreeing S' G Lo fixed) Lo := by
    apply restrictTyping_agree
    rw [htagree, maxTypingAgreeing_restrictTo hfixed_sub hfixed_correct]
  have htcorrectL := htcorrect n L htmem
  refine ⟨fun hLA => ?_, fun hLA => ?_⟩
  · exact satisfies_stratMono hAcyclic hWFExtra hNEF hDClosed hsub_t hagree_t hLo n
      (S'.shapeDef_depsIn hDClosed hL) (hWFExtra L) (hNEF L) (hLo L hL)
      (htcorrectL.1 hLA)
  · obtain ⟨x, hxmem, hSatx⟩ := htcorrectL.2 hLA
    have hxY : x ∈ S'.Y ∪ S'.X := by
      have hxdesc : x ∈ S'.desc L := (Finset.mem_sdiff.mp hxmem).1
      exact Finset.mem_union_right _ (Schema.mem_desc.mp hxdesc).1
    exact ⟨x, hxmem, satisfies_stratMono hAcyclic hWFExtra hNEF hDClosed hsub_t
      hagree_t hLo n (S'.shapeDef_depsIn hDClosed hxY) (hWFExtra x) (hNEF x)
      (hLo x hxY) hSatx⟩

/-! ### Schema invariance of `Satisfies` across `stratRestrict`

This is the last part that Proposition 1 needs. `Satisfies` uses the
schema (in rule 18). Thus, `Satisfies (S.stratRestrict strat i) G τ n s`
and `Satisfies (S.stratRestrict strat j) G τ n s` are different
propositions. In 2017, `stratTypingSeq_correct` does not have this
problem, because `Satisfies` never uses the schema. Here,
`satisfies_transfer` solves it. -/

/-- **The key schema-invariance fact.** For a label `x` in a stratum
`≤ i`, `Satisfies` with `S.stratRestrict strat i` agrees with `Satisfies`
with each higher restriction `S.stratRestrict strat j` (`i ≤ j`). The
evaluation of `def(x)` never goes outside the strata `≤ i`
(`Schema.shapeDef_depsIn` and `Schema.stratum_DClosedOn`). In that region,
the `.anc` of the two schemas is the same (`Schema.stratRestrict_anc_eq`). -/
theorem Satisfies_stratRestrict_agree {S : Schema E}
    (hAcyclic : S.ExtAcyclic) (hDClosed : S.DClosed) (strat : Stratification S)
    {i j : ℕ} (hij : i ≤ j) {x : Label} (hxY : x ∈ S.Y ∪ S.X) (hxi : strat.strat x ≤ i)
    {G : Graph} {τ : Typing} {n : RDFNode} :
    Satisfies (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) ↔
    Satisfies (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) := by
  have hZ : S.DClosedOn (S.stratum strat.strat i) := Schema.stratum_DClosedOn hDClosed strat i
  have hxZ : x ∈ S.stratum strat.strat i := Schema.mem_stratum.mpr ⟨hxY, hxi⟩
  refine satisfies_transfer (Schema.stratRestrict_ExtAcyclic hAcyclic strat.strat i)
    (Schema.stratRestrict_ExtAcyclic hAcyclic strat.strat j) rfl hZ (fun _ _ _ => Iff.rfl)
    (fun y hy => ?_) (S.shapeDef_depsIn hZ hxZ) n
  obtain ⟨hyY, hyi⟩ := Schema.mem_stratum.mp hy
  rw [Schema.stratRestrict_anc_eq hDClosed strat hyY hyi,
    Schema.stratRestrict_anc_eq hDClosed strat hyY (hyi.trans hij)]

/-- A correct typing of `S.stratRestrict strat i` is also a correct typing
of `S.stratRestrict strat j`, for `i ≤ j`. The inductive step of
`stratTypingSeq_correct` needs this step: "go up one stratum level and keep
correctness".

Each part (`.A` membership, and the `.desc \ .A` witnesses) is monotone in
the restriction level, because `stratRestrict` only makes `Y`, `X` and `A`
larger when `i` becomes larger. The important step is to move the
`Satisfies` witnesses with `Satisfies_stratRestrict_agree`. -/
theorem Schema.correctTyping_stratRestrict_mono {S : Schema E}
    (hAcyclic : S.ExtAcyclic) (hDClosed : S.DClosed) (strat : Stratification S)
    {i j : ℕ} (hij : i ≤ j) {G : Graph} {t : Typing}
    (ht_sub : t ⊆ (S.stratRestrict strat.strat i).univTyping G)
    (ht_correct : (S.stratRestrict strat.strat i).CorrectTyping G t) :
    (S.stratRestrict strat.strat j).CorrectTyping G t := by
  intro n L hmem
  obtain ⟨hLY, hLi⟩ := Schema.mem_stratRestrict_YX.mp (Finset.mem_product.mp (ht_sub hmem)).2
  have hAiff : L ∈ (S.stratRestrict strat.strat i).A ↔ L ∈ (S.stratRestrict strat.strat j).A := by
    rw [Schema.mem_stratRestrict_A, Schema.mem_stratRestrict_A]
    constructor
    · rintro ⟨hLA, _⟩; exact ⟨hLA, hLi.trans hij⟩
    · rintro ⟨hLA, _⟩; exact ⟨hLA, hLi⟩
  obtain ⟨hcorrectPlain, hcorrectAbs⟩ := ht_correct n L hmem
  refine ⟨fun hLnotA => ?_, fun hLA => ?_⟩
  · exact (Satisfies_stratRestrict_agree hAcyclic hDClosed strat hij hLY hLi).mp
      (hcorrectPlain (fun h => hLnotA (hAiff.mp h)))
  · obtain ⟨x, hxmem, hSatx⟩ := hcorrectAbs (hAiff.mpr hLA)
    rw [Finset.mem_sdiff, Schema.mem_desc] at hxmem
    obtain ⟨⟨hxX', hxpath⟩, hxnA⟩ := hxmem
    rw [Schema.mem_stratRestrict_X] at hxX'
    rw [Schema.mem_stratRestrict_A] at hxnA
    obtain ⟨hxX, hxi⟩ := hxX'
    have hxY : x ∈ S.Y ∪ S.X := Finset.mem_union_right _ hxX
    have hxmem' : x ∈ (S.stratRestrict strat.strat j).desc L \ (S.stratRestrict strat.strat j).A := by
      rw [Finset.mem_sdiff, Schema.mem_desc, Schema.mem_stratRestrict_X, Schema.mem_stratRestrict_A]
      exact ⟨⟨⟨hxX, hxi.trans hij⟩, hxpath⟩, fun h => hxnA ⟨h.1, hxi⟩⟩
    exact ⟨x, hxmem',
      (Satisfies_stratRestrict_agree hAcyclic hDClosed strat hij hxY hxi).mp hSatx⟩

/-- The sequence `τ_i` of Definition 8, as one recursion on `ℕ`:

* `τ_0 := ∅`. This is vacuously correct for `S^σ_0`, because each label
  has `σ(z) ≥ 1`. Thus, stratum 0 is empty.
* `τ_{i+1}` is the union of all the correct typings of `G` by `S^σ_{i+1}`
  that agree with `τ_i` on `Y^σ_i ∪ X^σ_i`.

This agrees with the recursion of the paper. The base case `τ_1` of
Definition 8 ("the union of all correct typings of `G` by `S^σ_1`") is the
special case `Lo = ∅` of the general step. -/
noncomputable def stratTypingSeq (S : Schema E) (strat : Label → ℕ) (G : Graph) : ℕ → Typing
  | 0 => ∅
  | i + 1 => maxTypingAgreeing (S.stratRestrict strat (i + 1)) G (S.stratum strat i)
      (stratTypingSeq S strat G i)

/-- Definition 8: the maximal typing of `G` by `S` with `σ`,
`τ_max(S,σ,G)`. -/
noncomputable def Typing8 (G : Graph) (S : Schema E) (strat : Stratification S) : Typing :=
  stratTypingSeq S strat.strat G strat.k

/-- The two invariants of `stratTypingSeq` at each stratum `i`:

* It is a subset of the universe of typings of `S^σ_i`.
* It is a correct typing of `G` by `S^σ_i`.

The base case (`i = 0`) is vacuous. (`stratum strat 0 = ∅`, and
`Y^σ_0 ∪ X^σ_0 = ∅`, because each label has `σ ≥ 1`, `mem_range`.)

The inductive step combines two lemmas:

* `maxTypingAgreeing_correct`: the new correctness at stratum `i+1`.
* `Schema.correctTyping_stratRestrict_mono`: it moves the correctness of
  the previous typing at stratum `i` up to the schema of stratum `i+1`.

This solves the problem that a direct port in the 2017 style does not
solve. Refer to the docstring of `Satisfies_stratRestrict_agree`. -/
theorem stratTypingSeq_correct {S : Schema E} (hAcyclic : S.ExtAcyclic)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat : Stratification S) (G : Graph) (i : ℕ) :
      stratTypingSeq S strat.strat G i ⊆ (S.stratRestrict strat.strat i).univTyping G ∧
      (S.stratRestrict strat.strat i).CorrectTyping G (stratTypingSeq S strat.strat G i) := by
  induction i with
  | zero =>
      refine ⟨by simp [stratTypingSeq], ?_⟩
      intro n L hmem
      simp [stratTypingSeq] at hmem
  | succ i ih =>
      obtain ⟨hsub_i, hcorrect_i⟩ := ih
      have hsub_i' : stratTypingSeq S strat.strat G i ⊆
          (S.stratRestrict strat.strat (i + 1)).univTyping G := by
        intro p hp
        have hp' := Finset.mem_product.mp (hsub_i hp)
        refine Finset.mem_product.mpr ⟨hp'.1, ?_⟩
        obtain ⟨hpY, hpi⟩ := Schema.mem_stratRestrict_YX.mp hp'.2
        exact Schema.mem_stratRestrict_YX.mpr ⟨hpY, hpi.trans (Nat.le_succ i)⟩
      have hcorrect_i' : (S.stratRestrict strat.strat (i + 1)).CorrectTyping G
          (stratTypingSeq S strat.strat G i) :=
        Schema.correctTyping_stratRestrict_mono hAcyclic hDClosed strat (Nat.le_succ i)
          hsub_i hcorrect_i
      have hLo : ∀ z ∈ (S.stratRestrict strat.strat (i + 1)).Y ∪
            (S.stratRestrict strat.strat (i + 1)).X,
          (ShapeSyntax.deps ((S.stratRestrict strat.strat (i + 1)).shapeDef z)).negRefs ⊆
            S.stratum strat.strat i := by
        intro z hz z' hz'
        obtain ⟨hzY, hzi1⟩ := Schema.mem_stratRestrict_YX.mp hz
        have hDNeg : S.DNegEdge z z' := Or.inl hz'
        have hz'Y : z' ∈ S.Y ∪ S.X := hDClosed z hzY z' (S.DEdge_of_DNegEdge hDNeg)
        have hlt : strat.strat z' < strat.strat z := strat.negDep_lt z hzY z' hDNeg
        exact Schema.mem_stratum.mpr ⟨hz'Y, by omega⟩
      have hDClosed1 : (S.stratRestrict strat.strat (i + 1)).DClosed :=
        Schema.stratRestrict_DClosed hDClosed strat (i + 1)
      have hAcyclic1 : (S.stratRestrict strat.strat (i + 1)).ExtAcyclic :=
        Schema.stratRestrict_ExtAcyclic hAcyclic strat.strat (i + 1)
      refine ⟨maxTypingAgreeing_subset _ G _ _, ?_⟩
      show (S.stratRestrict strat.strat (i + 1)).CorrectTyping G
        (maxTypingAgreeing (S.stratRestrict strat.strat (i + 1)) G (S.stratum strat.strat i)
          (stratTypingSeq S strat.strat G i))
      exact maxTypingAgreeing_correct hAcyclic1 hWFExtra hNEF hDClosed1 hsub_i' hcorrect_i' hLo

/-- **Proposition 1.** For every schema `S`, stratification `σ` of `S`, and
graph `G`, the typing `τ_max(S,σ,G)` is a correct typing. -/
theorem proposition1 {S : Schema E} (hAcyclic : S.ExtAcyclic)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat : Stratification S) (G : Graph) :
    S.CorrectTyping G (Typing8 G S strat) := by
  have := (stratTypingSeq_correct hAcyclic hWFExtra hNEF hDClosed strat G strat.k).2
  rwa [Schema.stratRestrict_top] at this

end ShexLean.InheritanceCore
