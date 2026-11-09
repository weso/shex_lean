import ShexLean.InheritanceCore.Syntax
import ShexLean.Common.DisjointUnion
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Pairwise.Basic

/-!
Table 1 (`M,τ ⊨ e`, triple expressions) and rule 17 of Table 3
(`M,τ ⊨ [closed][extra P]⟨e⟩`, shapes) of "Shape Expressions with
Inheritance" (2025, §4.1). They do not depend on the payload of `extends`.
Thus, the 2025 paper (`ShexLean/Shex2025Inheritance/`) and the 2026
exploration (`ShexLean/Shex2026InheritanceDisjunction/`) share them.

This file also contains the facts about these relations that the proofs
of Proposition 1 use:

* Agreement: they depend on `τ` only through the labels that they refer to
  (`SatisfiesE_agree`, `SatisfiesShape_agree`).
* Monotonicity: Table 1 is monotone in `τ`, and rule 17 is monotone if the
  shape satisfies the invariant "(*)" (`monoE`, `SatisfiesShape_mono`).
-/

namespace ShexLean.InheritanceCore

/-- `subject(M)`: the common subject of a nonempty set of triples `M`. (If
`M` is a real neighbourhood set, this subject is unique.) It is selected
with classical choice. On `M = ∅`, the result is a junk value
(`.iri ""`). The notion of the paper is also not defined for this case.
(Rule 13 applies only when `M` is the neighbourhood of a node.) -/
noncomputable def subjectOf (M : Finset Triple) : RDFNode :=
  if h : M.Nonempty then (h.choose.subj : RDFNode) else RDFNode.iri ""

/-- `M^e` (Table 3, the discussion before rule 18): the triples of `M` that
satisfy a triple constraint of `e` with `τ`. Thus, their predicate matches
a triple constraint `p @z` of `e`, and their object has the type `z` in
`τ`. -/
noncomputable def Me (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  haveI := Classical.decPred (fun t : Triple => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)
  M.filter (fun t => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)

/-- `M^{e'}` (Table 3): the triples of `M` whose property occurs in `e`,
but that satisfy no triple constraint of `e`. -/
noncomputable def Mnotin (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  haveI := Classical.decPred (fun t : Triple => t.pred ∈ e.props)
  (M.filter (fun t => t.pred ∈ e.props)) \ Me τ M e

/-- `props(M)` (Table 3): the properties of the triples in `M`. -/
def props (M : Finset Triple) : Finset IRI := M.image Triple.pred

/-- The membership property of `Me`. This lemma fixes the
`Classical.decPred` instance of the filter one time, here. This prevents
instance mismatches at the call sites. (Refer to the notes about this
problem in `Proposition1.lean`.) -/
theorem mem_Me {τ : Typing} {M : Finset Triple} {e : TripleExpr} {t : Triple} :
    t ∈ Me τ M e ↔ t ∈ M ∧ ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z := by
  unfold Me; simp only [Finset.mem_filter]

/-- The membership property of `Mnotin`. The reason is the same as for
`mem_Me`. -/
theorem mem_Mnotin {τ : Typing} {M : Finset Triple} {e : TripleExpr} {t : Triple} :
    t ∈ Mnotin τ M e ↔ (t ∈ M ∧ t.pred ∈ e.props) ∧ t ∉ Me τ M e := by
  unfold Mnotin; simp only [Finset.mem_sdiff, Finset.mem_filter]

/-- `M = M' ⊎ (⊎_{x ∈ Idx} Mx)`: `M'` and the sets `Mx x` (for `x ∈ Idx`)
are pairwise disjoint, and their union is `M`. There is a finite number of
sets `Mx x`. Rule 18 of Table 3 uses this to divide a neighbourhood set
into one part that satisfies `h`, and one part for each ancestor that is
extended (transitively). -/
def DisjointUnionOn (M M' : Finset Triple) (Idx : Finset Label)
    (Mx : Label → Finset Triple) : Prop :=
  Disjoint M' (Idx.biUnion Mx) ∧ (Idx : Set Label).PairwiseDisjoint Mx ∧
    M = M' ∪ Idx.biUnion Mx

/-- `M,τ ⊨ e` (Table 1). It is structural on `e`. -/
def SatisfiesE (τ : Typing) : Finset Triple → TripleExpr → Prop
  -- Rule 1 (`ε`).
  | M, .empty => M = ∅
  -- Rule 2 (`p @z`). `o,τ ⊨ @z` is written inline as `τ.has o z` (rule 10 of
  -- Table 2 has no more recursion, refer to the module docstring).
  | M, .tc p z => ∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z
  -- Rule 3 (`e1|e2`).
  | M, .choice e1 e2 => SatisfiesE τ M e1 ∨ SatisfiesE τ M e2
  -- Rule 4 (`e1;e2`).
  | M, .seq e1 e2 =>
      ∃ M1 M2, DisjointUnion M M1 M2 ∧ SatisfiesE τ M1 e1 ∧ SatisfiesE τ M2 e2
  -- Rule 5 (`e1*`).
  | M, .star e =>
      ∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧ ∀ Ni ∈ Ns, SatisfiesE τ Ni e

/-- `M,τ ⊨ [closed][extra P]⟨e⟩` (rule 17 of Table 3). Rule 18 also uses it,
for the part `M'` that satisfies the shape `h` of `extends X h`. -/
def SatisfiesShape (τ : Typing) (M : Finset Triple) (h : Shape) : Prop :=
  SatisfiesE τ (Me τ M h.triples) h.triples ∧
  props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
  (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)

/-! General lemmas about `Me`, `Mnotin` and `SatisfiesShape`. Many worked
examples use them. -/

/-- Let `Me τ M e = M` (a triple constraint of `e` consumes each triple of
`M`). If `M` satisfies `e` (Table 1), then `M` also satisfies the trivial
shape `[closed:=false][extra:=none]⟨e⟩` (rule 17). `Mnotin` must be empty,
because it is always `⊆ M \ Me = M \ M = ∅`.

The `M'` part of an `extends X h` must satisfy this: `M', τ ⊨ h`
(rule 18). The check is against `h` as a shape, not directly against
`h.triples`. -/
theorem ofShape_of_Me_eq_self {τ : Typing} {M : Finset Triple} {e : TripleExpr}
    (hMe : Me τ M e = M) (hE : SatisfiesE τ M e) :
    SatisfiesShape τ M ⟨false, none, e⟩ := by
  refine ⟨?_, ?_, by simp⟩
  · show SatisfiesE τ (Me τ M e) e
    rw [hMe]; exact hE
  · show props (Mnotin τ M e) ⊆ (∅ : Finset IRI)
    rw [Finset.subset_empty, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    unfold props at ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    rw [mem_Mnotin] at ht'
    obtain ⟨⟨htM, _⟩, hnotMe⟩ := ht'
    exact hnotMe (by rw [hMe]; exact htM)

/-- Let a singleton `{(n,p,o)}` satisfy a plain triple constraint `p @z`
with `τ`. Then it also satisfies the trivial shape
`[closed:=false][extra:=none] ⟨p @z⟩` (rule 17). This is the special case
of `ofShape_of_Me_eq_self` that most `.extends` proofs need. -/
theorem singleton_tc_ofShape {τ : Typing} {p : IRI} {z : Label} {n : Subject} {o : RDFNode}
    (hty : τ.has o z) :
    SatisfiesShape τ {(⟨n, p, o⟩ : Triple)} ⟨false, none, .tc p z⟩ := by
  apply ofShape_of_Me_eq_self (e := .tc p z) (M := {(⟨n, p, o⟩ : Triple)})
  · apply Finset.Subset.antisymm
    · intro t ht; rw [mem_Me] at ht; exact ht.1
    · intro t ht
      simp only [Finset.mem_singleton] at ht
      subst ht
      rw [mem_Me]
      exact ⟨Finset.mem_singleton_self _, z, by simp [TripleExpr.tcs], hty⟩
  · exact ⟨n, o, rfl, hty⟩

/-- The converse of `ofShape_of_Me_eq_self`. Let each triple of `M` have a
predicate that is already in `e`. (Thus, no triple can go into the "extra"
set.) Then a witness of `M, τ ⊨ [extra:=none]⟨e⟩` (rule 17) forces
`Me τ M e = M`. Thus, `M` itself satisfies `e` (Table 1), not only a part
of `M`.

This lemma is necessary to change an obligation `M', τ ⊨ h` (the shape
part of rule 18) back into a `SatisfiesE` fact about `M'`. The reason is
that rule 18 checks `M'` against `h` as a shape, not directly against
`h.triples`. -/
theorem Me_eq_self_of_props_subset {τ : Typing} {M : Finset Triple} {e : TripleExpr}
    (hM : SatisfiesShape τ M ⟨false, none, e⟩) (hsub : props M ⊆ e.props) :
    Me τ M e = M := by
  obtain ⟨-, hMnotinSub, -⟩ := hM
  apply Finset.Subset.antisymm
  · intro t ht; rw [mem_Me] at ht; exact ht.1
  · intro t ht
    by_contra hnotMe
    have htin : t ∈ Mnotin τ M e := by
      rw [mem_Mnotin]
      exact ⟨⟨ht, hsub (Finset.mem_image_of_mem Triple.pred ht)⟩, hnotMe⟩
    have := hMnotinSub (Finset.mem_image_of_mem Triple.pred htin)
    simp at this

/-! ### Agreement and monotonicity -/

/-- `SatisfiesE` (Table 1) depends on `τ` only through its restriction to
`Z`, if the references of `e` are `⊆ Z`. Table 1 never does a schema
lookup. -/
theorem SatisfiesE_agree {τ τ' : Typing} {Z : Finset Label} (hagree : AgreeOn τ τ' Z) :
    ∀ (e : TripleExpr), e.refs ⊆ Z → ∀ M, SatisfiesE τ M e ↔ SatisfiesE τ' M e := by
  intro e
  induction e with
  | empty => intros; rfl
  | tc p z =>
      intro href M
      have hzZ : z ∈ Z := href (by simp [TripleExpr.refs, TripleExpr.tcs])
      simp only [SatisfiesE]
      exact exists₂_congr fun n o => and_congr_right fun _ => hagree o z hzZ
  | choice e1 e2 ih1 ih2 =>
      intro href M
      simp only [TripleExpr.refs, TripleExpr.tcs, Finset.image_union, Finset.union_subset_iff]
        at href
      exact or_congr (ih1 href.1 M) (ih2 href.2 M)
  | seq e1 e2 ih1 ih2 =>
      intro href M
      simp only [TripleExpr.refs, TripleExpr.tcs, Finset.image_union, Finset.union_subset_iff]
        at href
      simp only [SatisfiesE]
      exact exists₂_congr fun M1 M2 => and_congr_right fun _ =>
        and_congr (ih1 href.1 M1) (ih2 href.2 M2)
  | star e ih =>
      intro href M
      simp only [SatisfiesE]
      exact exists_congr fun Ns => and_congr_right fun _ =>
        forall₂_congr fun Ni _ => ih href Ni

/-- `M^e` (the `Me` of Table 3) is exactly equal for `τ` and `τ'`, if they
agree on the references of `e`. The membership test of each triple uses
`τ` only on a label in `e.refs ⊆ Z`. -/
theorem Me_eq {τ τ' : Typing} {Z : Finset Label} (hagree : AgreeOn τ τ' Z) {e : TripleExpr}
    (href : e.refs ⊆ Z) (M : Finset Triple) : Me τ M e = Me τ' M e := by
  ext t
  rw [mem_Me, mem_Me]
  refine and_congr_right fun _ => exists_congr fun z => and_congr_right fun hz => ?_
  exact hagree t.obj z (href (Finset.mem_image.mpr ⟨(t.pred, z), hz, rfl⟩))

/-- `M^{e'}` (the `Mnotin` of Table 3) is also exactly equal. It is made
from `Me` (equal by `Me_eq`) and from a filter on `props`, which does not
use `τ`. -/
theorem Mnotin_eq {τ τ' : Typing} {Z : Finset Label} (hagree : AgreeOn τ τ' Z) {e : TripleExpr}
    (href : e.refs ⊆ Z) (M : Finset Triple) : Mnotin τ M e = Mnotin τ' M e := by
  unfold Mnotin
  rw [Me_eq hagree href M]

/-- Rule 17 depends on `τ` only through its restriction to the references
of the shape. -/
theorem SatisfiesShape_agree {τ τ' : Typing} {Z : Finset Label} (hagree : AgreeOn τ τ' Z)
    {h : Shape} (href : h.triples.refs ⊆ Z) (M : Finset Triple) :
    SatisfiesShape τ M h ↔ SatisfiesShape τ' M h := by
  unfold SatisfiesShape
  rw [Me_eq hagree href M, Mnotin_eq hagree href M,
    SatisfiesE_agree hagree h.triples href (Me τ' M h.triples)]

/-- `SatisfiesE` (Table 1) is monotone in `τ` with no condition. When `τ`
becomes larger (for a fixed `M`), a match never fails. Table 1 has no
filtering of the `extra` type and no negation. -/
theorem monoE {τ τ' : Typing} (hsub : τ ⊆ τ') :
    ∀ (e : TripleExpr) (M : Finset Triple), SatisfiesE τ M e → SatisfiesE τ' M e := by
  intro e
  induction e with
  | empty => intro M h; exact h
  | tc p z =>
      intro M h
      obtain ⟨n, o, hM, htyp⟩ := h
      exact ⟨n, o, hM, hsub htyp⟩
  | choice e1 e2 ih1 ih2 => intro M h; exact h.imp (ih1 M) (ih2 M)
  | seq e1 e2 ih1 ih2 =>
      intro M h
      obtain ⟨M1, M2, hdu, h1, h2⟩ := h
      exact ⟨M1, M2, hdu, ih1 M1 h1, ih2 M2 h2⟩
  | star e ih =>
      intro M h
      obtain ⟨Ns, hdu, hall⟩ := h
      exact ⟨Ns, hdu, fun Ni hNi => ih Ni (hall Ni hNi)⟩

/-- Let `props(Mnotin τ M e) ⊆ P'` (the leftover-properties condition of
rule 17), and let `e` and `P'` satisfy "(*)" (`e.props ∩ P' = ∅`). Then
`Me τ M e` must be the full part of `M` that matches `props(e)`. This set
does not use `τ`. -/
theorem Me_eq_filter_of_success {τ : Typing} {e : TripleExpr} {P' : Finset IRI}
    (hWF : e.props ∩ P' = ∅) {M : Finset Triple}
    (hMnotin : props (Mnotin τ M e) ⊆ P') :
    Me τ M e = M.filter (fun t => t.pred ∈ e.props) := by
  have hsub1 : Me τ M e ⊆ M.filter (fun t => t.pred ∈ e.props) := by
    intro t ht
    rw [mem_Me] at ht
    simp only [Finset.mem_filter]
    refine ⟨ht.1, ?_⟩
    obtain ⟨z, hz, _⟩ := ht.2
    exact Finset.mem_image.mpr ⟨(t.pred, z), hz, rfl⟩
  refine Finset.Subset.antisymm hsub1 ?_
  intro t ht
  by_contra hnotin
  have htMnotin : t ∈ Mnotin τ M e := mem_Mnotin.mpr ⟨(Finset.mem_filter.mp ht), hnotin⟩
  have hpprops : t.pred ∈ e.props := (Finset.mem_filter.mp ht).2
  have hpP' : t.pred ∈ P' := hMnotin (Finset.mem_image_of_mem Triple.pred htMnotin)
  have : t.pred ∈ e.props ∩ P' := Finset.mem_inter.mpr ⟨hpprops, hpP'⟩
  rw [hWF] at this
  exact absurd this (by simp)

/-- When `Me` is at its maximum (`Me_eq_filter_of_success`, if there is
success at `τ`), it cannot become larger along `τ ⊆ τ'`. It is between
`Me τ M e` (below) and the same maximum, which does not depend on `τ`
(above). -/
theorem Me_stable {τ τ' : Typing} (hsub : τ ⊆ τ') {h : Shape} (hWF : h.WellFormedExtra)
    {M : Finset Triple} (hMnotin : props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅) :
    Me τ M h.triples = Me τ' M h.triples := by
  have hceil := Me_eq_filter_of_success hWF hMnotin
  have hmono : Me τ M h.triples ⊆ Me τ' M h.triples := by
    intro t ht
    rw [mem_Me] at ht ⊢
    exact ⟨ht.1, ht.2.imp fun z hz => ⟨hz.1, hsub hz.2⟩⟩
  have hbound : Me τ' M h.triples ⊆ M.filter (fun t => t.pred ∈ h.triples.props) := by
    intro t ht
    rw [mem_Me] at ht
    simp only [Finset.mem_filter]
    refine ⟨ht.1, ?_⟩
    obtain ⟨z, hz, _⟩ := ht.2
    exact Finset.mem_image.mpr ⟨(t.pred, z), hz, rfl⟩
  exact Finset.Subset.antisymm hmono (hceil ▸ hbound)

/-- Rule 17 is monotone in `τ`, if `h.WellFormedExtra` ("(*)") is true.
`Me` and `Mnotin` do not change (`Me_stable`). Thus, the inner `SatisfiesE`
check goes from `τ` to `τ'` with `monoE`. -/
theorem SatisfiesShape_mono {τ τ' : Typing} (hsub : τ ⊆ τ') {h : Shape}
    (hWF : h.WellFormedExtra) (M : Finset Triple) :
    SatisfiesShape τ M h → SatisfiesShape τ' M h := by
  rintro ⟨hE, hMnotin, hclosed⟩
  have hMeeq := Me_stable hsub hWF hMnotin
  have hMnotineq : Mnotin τ' M h.triples = Mnotin τ M h.triples := by
    unfold Mnotin; rw [hMeeq]
  exact ⟨hMeeq ▸ monoE hsub h.triples (Me τ M h.triples) hE, hMnotineq ▸ hMnotin, hclosed⟩

end ShexLean.InheritanceCore
