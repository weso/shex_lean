import ShexLean.Shex2026InheritanceDisjunction.Proposition1
import Mathlib.Data.Finset.Max

/-!
Lemma 2 (§4.3) of the 2025 paper "Shape Expressions with Inheritance":
`τ_max(S,σ,G)` (Definition 8) does not depend on the stratification `σ` of
`S` that you select.

This file is a port of `ShexLean/Shex2017Schemas/Lemma2.lean` of the 2017
formalization. The paper gives only a sketch of this proof ("Proof.
(Idea)..."). Thus, the 2017 file made a full, independent argument
(Fusion, Swap, a process `cont1` that does not depend on a schedule, and
Independence). This argument has almost the same structure here.

One part does **not** transfer directly. In 2017, `Satisfies` never uses
the schema. Thus, "restrict the schema to a self-contained label set" was
free (`Schema.restrictLabels`, with the same `shapeDef`, and no more
invariance lemma). Here, `Satisfies` really depends on the schema
(through `.anc` and `.ancSet`). For restrictions to a *stratum*,
`Satisfies_stratRestrict_agree` of
`ShexLean/Shex2026InheritanceDisjunction/Proposition1.lean` solves this
problem. Thus, this file first makes the full schema-invariance argument
more general:

* From `Schema.stratRestrict` (related to a stratification).
* To `Schema.restrictLabels` (any `D_S`-closed label set).

The batches of `cont1`, which do not depend on a schedule, need this
general form.
-/

namespace ShexLean.InheritanceDisjunction

/-! ### `Schema.restrictLabels`: restriction to any label set

This is a general form of `Schema.stratRestrict`
(`ShexLean/Shex2026InheritanceDisjunction/Proposition1.lean`) that is not
related to a stratification. Here, `Ls` is any label set. It is not
necessarily `S.stratum strat i` for a `strat` and an `i`. -/

/-- The restriction of `S` to a label set `Ls`. The definitions do not
change. This is the `Schema.restrictLabels` of 2017
(`ShexLean/Shex2017Schemas/Lemma2.lean`), and a general form of
`Schema.stratRestrict`. -/
def Schema.restrictLabels (S : Schema) (Ls : Finset Label) : Schema where
  Y := S.Y ∩ Ls
  X := S.X ∩ Ls
  A := S.A ∩ Ls
  disjointYX := S.disjointYX.mono Finset.inter_subset_left Finset.inter_subset_left
  A_subX := by
    intro z hz
    simp only [Finset.mem_inter] at hz ⊢
    exact ⟨S.A_subX hz.1, hz.2⟩
  shapeDef := S.shapeDef

/-- When `Ls ⊆ Y ∪ X`, the `Y ∪ X` of `restrictLabels Ls` is exactly `Ls`.
This is the general version of `Schema.stratRestrict_YX_eq_stratum`. -/
theorem Schema.restrictLabels_YX_eq {S : Schema} {Ls : Finset Label}
    (hLs : Ls ⊆ S.Y ∪ S.X) : (S.restrictLabels Ls).Y ∪ (S.restrictLabels Ls).X = Ls := by
  unfold Schema.restrictLabels
  rw [← Finset.union_inter_distrib_right]
  exact Finset.inter_eq_right.mpr hLs

/-- `WellFormedX` stays true for each `restrictLabels`. This is the general
version of `Schema.stratRestrict_WellFormedX`. -/
theorem Schema.restrictLabels_WellFormedX {S : Schema} (hWFX : S.WellFormedX)
    (Ls : Finset Label) : (S.restrictLabels Ls).WellFormedX := by
  intro x hx
  simp only [Schema.restrictLabels, Finset.mem_inter] at hx
  exact hWFX x hx.1

/-- `restrictLabels` does not change the edges of `D_S`. This is the
general version of `Schema.stratRestrict_DEdge_eq`. -/
theorem Schema.restrictLabels_DEdge_eq (S : Schema) (Ls : Finset Label) :
    (S.restrictLabels Ls).DEdge = S.DEdge := rfl

/-- `(restrictLabels Ls).Y ∪ (restrictLabels Ls).X ⊆ Ls` always (also when
`Ls ⊄ Y ∪ X`). The definition uses intersections, so it never adds labels
outside `Ls`. This changes a hypothesis `∀ z ∈ Ls, ...` into the form
`∀ z ∈ (restrictLabels Ls).Y ∪ (restrictLabels Ls).X, ...` that
`maxTypingAgreeing_correct` needs. -/
theorem Schema.restrictLabels_mem_YX_subset (S : Schema) (Ls : Finset Label) :
    (S.restrictLabels Ls).Y ∪ (S.restrictLabels Ls).X ⊆ Ls := by
  intro z hz
  simp only [Schema.restrictLabels, Finset.mem_union, Finset.mem_inter] at hz
  rcases hz with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h

/-- `restrictLabels Ls` is also `DClosed` (relative to its own `Y ∪ X`,
which is `Ls` when `Ls ⊆ Y ∪ X`), if `S` is `D_S`-closed on `Ls`.

This is the general version of `Schema.stratRestrict_DClosed`. It is made
in the same way, with the two simple bridge lemmas above (`rfl` and set
equality). If you give `hLsClosed` directly, `whnf` becomes too slow, in
the same way. (Refer to the docstring of `Schema.stratRestrict_DClosed`,
in `ShexLean/Shex2026InheritanceDisjunction/Proposition1.lean`.) -/
theorem Schema.restrictLabels_DClosed {S : Schema} {Ls : Finset Label}
    (hLsClosed : S.DClosedOn Ls) (hLsYX : Ls ⊆ S.Y ∪ S.X) :
    (S.restrictLabels Ls).DClosedOn ((S.restrictLabels Ls).Y ∪ (S.restrictLabels Ls).X) := by
  rw [Schema.restrictLabels_YX_eq hLsYX]
  intro z hz z' hedge
  rw [Schema.restrictLabels_DEdge_eq] at hedge
  exact hLsClosed z hz z' hedge

theorem Schema.univTyping_mono {S : Schema} {G : Graph} {Ls Ls' : Finset Label}
    (h : Ls ⊆ Ls') : (S.restrictLabels Ls).univTyping G ⊆ (S.restrictLabels Ls').univTyping G := by
  have hY : (S.restrictLabels Ls).Y ⊆ (S.restrictLabels Ls').Y := Finset.inter_subset_inter le_rfl h
  have hX : (S.restrictLabels Ls).X ⊆ (S.restrictLabels Ls').X := Finset.inter_subset_inter le_rfl h
  intro p hp
  simp only [Schema.univTyping] at hp ⊢
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  refine Finset.mem_product.mpr ⟨hp1, ?_⟩
  rcases Finset.mem_union.mp hp2 with h1 | h1
  · exact Finset.mem_union_left _ (hY h1)
  · exact Finset.mem_union_right _ (hX h1)

/-! ### A restriction to a `D_S`-closed set does not change `.anc` and `.desc`

This is the general version of `Schema.stratRestrict_anc_eq` (which uses
`Stratification.le_of_path`, specific to a stratum). It uses the more basic
fact below that result. If `Ls` is `D_S`-closed, then each label that
`H_S` reaches from a member of `Ls`, in *the two* directions, already stays
in `Ls`. The reason is that `dep-extends` is symmetric (Definition 5) and
is part of `D_S`. -/

/-- `S.anc x ⊆ Ls` if `x ∈ Ls` and `Ls` is `D_S`-closed. This follows
directly from `Schema.ancSet_subset` with `xs = {x}`. -/
theorem Schema.anc_subset_of_DClosedOn {S : Schema} {Ls : Finset Label} (hLs : S.DClosedOn Ls)
    {x : Label} (hx : x ∈ Ls) : S.anc x ⊆ Ls := by
  have h := S.ancSet_subset hLs (xs := {x}) (Finset.singleton_subset_iff.mpr hx)
  simpa [Schema.ancSet, Finset.singleton_biUnion] using h

/-- The reversal of a `ReflTransGen` path along a symmetric relation. -/
private theorem reflTransGen_reverse_of_symm {α : Type*} {r : α → α → Prop}
    (hsymm : ∀ a b, r a b → r b a) {x y : α} (h : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih => exact Relation.ReflTransGen.head (hsymm _ _ hstep) ih

/-- `S.desc L ⊆ Ls` if `L ∈ Ls` and `Ls` is `D_S`-closed. This is the dual
of `Schema.anc_subset_of_DClosedOn`, in the "descendant" direction. It
needs the reversal above, because the reachability of `Schema.desc` goes in
the opposite direction along `extEdge`. `dep-extends` (and thus `D_S`)
does not depend on the direction. -/
theorem Schema.desc_subset_of_DClosedOn {S : Schema} {Ls : Finset Label} (hLs : S.DClosedOn Ls)
    {L : Label} (hL : L ∈ Ls) : S.desc L ⊆ Ls := by
  intro x hx
  rw [Schema.mem_desc] at hx
  obtain ⟨_, hxpath⟩ := hx
  have hpath1 : Relation.ReflTransGen S.depExtends x L :=
    Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) x L hxpath
  have hpath2 : Relation.ReflTransGen S.depExtends L x :=
    reflTransGen_reverse_of_symm (fun a b h => h.symm) hpath1
  have hpath3 : Relation.ReflTransGen S.DEdge L x :=
    Relation.ReflTransGen.mono (fun _ _ h => Or.inr h) L x hpath2
  exact S.reach_mem hLs hL hpath3

/-- `(S.restrictLabels Ls).anc x = S.anc x` for `x` in a `D_S`-closed
`Ls`. This is the general version of `Schema.stratRestrict_anc_eq`. -/
theorem Schema.restrictLabels_anc_eq {S : Schema} {Ls : Finset Label} (hLsClosed : S.DClosedOn Ls)
    {x : Label} (hxLs : x ∈ Ls) : (S.restrictLabels Ls).anc x = S.anc x := by
  have hsub : S.anc x ⊆ Ls := S.anc_subset_of_DClosedOn hLsClosed hxLs
  apply Finset.ext
  intro y
  unfold Schema.anc Schema.restrictLabels Schema.extEdge
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hyX, _⟩, hpath⟩
    exact ⟨hyX, hpath⟩
  · rintro ⟨hyX, hpath⟩
    have hyanc : y ∈ S.anc x := by
      unfold Schema.anc; simp only [Finset.mem_filter]; exact ⟨hyX, hpath⟩
    exact ⟨⟨hyX, hsub hyanc⟩, hpath⟩

/-- `(S.restrictLabels Ls).desc L = S.desc L` for `L` in a `D_S`-closed
`Ls`. This is the dual of `Schema.restrictLabels_anc_eq`. -/
theorem Schema.restrictLabels_desc_eq {S : Schema} {Ls : Finset Label} (hLsClosed : S.DClosedOn Ls)
    {L : Label} (hLLs : L ∈ Ls) : (S.restrictLabels Ls).desc L = S.desc L := by
  have hsub : S.desc L ⊆ Ls := S.desc_subset_of_DClosedOn hLsClosed hLLs
  apply Finset.ext
  intro x
  rw [Schema.mem_desc, Schema.mem_desc]
  unfold Schema.restrictLabels
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨⟨hxX, _⟩, hpath⟩
    exact ⟨hxX, hpath⟩
  · rintro ⟨hxX, hpath⟩
    have hxdesc : x ∈ S.desc L := Schema.mem_desc.mpr ⟨hxX, hpath⟩
    exact ⟨⟨hxX, hsub hxdesc⟩, hpath⟩

/-! ### `Satisfies` across `restrictLabels`, and lifting `CorrectTyping` -/

/-- **The general schema-invariance fact** of this file. For a label in
`Ls1`, `Satisfies` with `restrictLabels Ls1` agrees with `Satisfies` with
each larger `D_S`-closed `restrictLabels Ls2 ⊇ Ls1`.

This is the general version (for any `D_S`-closed set) of
`Satisfies_stratRestrict_agree`. It is made in the same way (`stableFuel`
and `schemaAgreeFuel`), with `Schema.restrictLabels_anc_eq` in place of
`Schema.stratRestrict_anc_eq`, which is specific to a stratum. -/
theorem Satisfies_restrictLabels_agree {S : Schema} (hWFX : S.WellFormedX)
    (hWFExt : S.WellFormedExtends) {Ls1 Ls2 : Finset Label} (hLs1Ls2 : Ls1 ⊆ Ls2)
    (hLs1Closed : S.DClosedOn Ls1) (hLs2Closed : S.DClosedOn Ls2)
    {x : Label} (hxLs1 : x ∈ Ls1) {G : Graph} {τ : Typing} {n : RDFNode} :
    Satisfies (S.restrictLabels Ls1) G τ n (S.shapeDef x) ↔
    Satisfies (S.restrictLabels Ls2) G τ n (S.shapeDef x) := by
  have hdeps : (S.shapeDef x).depsIn Ls1 := S.shapeDef_depsIn hLs1Closed hxLs1
  have hAnc : ∀ y ∈ Ls1, (S.restrictLabels Ls1).anc y = (S.restrictLabels Ls2).anc y := by
    intro y hy
    rw [Schema.restrictLabels_anc_eq hLs1Closed hy,
      Schema.restrictLabels_anc_eq hLs2Closed (hLs1Ls2 hy)]
  have hWFX1 : (S.restrictLabels Ls1).WellFormedX := Schema.restrictLabels_WellFormedX hWFX Ls1
  have hWFX2 : (S.restrictLabels Ls2).WellFormedX := Schema.restrictLabels_WellFormedX hWFX Ls2
  set F := max (ShapeExpr.reqFuel (S.restrictLabels Ls1) (S.shapeDef x) + 1)
    (ShapeExpr.reqFuel (S.restrictLabels Ls2) (S.shapeDef x) + 1) with hFdef
  have hstep1 : Satisfies (S.restrictLabels Ls1) G τ n (S.shapeDef x) ↔
      SatisfiesFuel F (S.restrictLabels Ls1) G τ n (S.shapeDef x) :=
    stableFuel hWFX1 hWFExt (S.shapeDef x)
      (ShapeExpr.reqFuel (S.restrictLabels Ls1) (S.shapeDef x) + 1) F
      (le_refl _) (le_max_left _ _) G τ n
  have hstep2 : Satisfies (S.restrictLabels Ls2) G τ n (S.shapeDef x) ↔
      SatisfiesFuel F (S.restrictLabels Ls2) G τ n (S.shapeDef x) :=
    stableFuel hWFX2 hWFExt (S.shapeDef x)
      (ShapeExpr.reqFuel (S.restrictLabels Ls2) (S.shapeDef x) + 1) F
      (le_refl _) (le_max_right _ _) G τ n
  have hcross : SatisfiesFuel F (S.restrictLabels Ls1) G τ n (S.shapeDef x) ↔
      SatisfiesFuel F (S.restrictLabels Ls2) G τ n (S.shapeDef x) :=
    schemaAgreeFuel (S1 := S.restrictLabels Ls1) (S2 := S.restrictLabels Ls2)
      rfl hWFExt hLs1Closed hAnc (S.shapeDef x) hdeps F τ n
  rw [hstep1, hstep2, hcross]

/-- A correct typing of `restrictLabels Ls2` restricts to a correct typing
of `restrictLabels Ls1`, for each `D_S`-closed `Ls1 ⊆ Ls2`. This is the
version of `restrictLabels_correct_restrictTo` of 2017. It combines two
steps:

* A τ-restriction step (`Satisfies.agree`, which is already generic in
  the schema, in `Proposition1.lean`).
* A *schema*-restriction step (`Satisfies_restrictLabels_agree`, new in
  this file).

2017 needed only the first step, because there `Satisfies` never uses the
schema.

The abstract-label case also needs `Schema.desc_subset_of_DClosedOn`. The
descendant that is the witness is automatically also in `Ls1`, because the
`D_S`-closure of `Ls1` already contains each `H_S` neighbour of `L`
(`dep-extends` is symmetric), not only its ordinary `dep` references. -/
theorem restrictLabels_correct_restrictTo {S : Schema} (hWFX : S.WellFormedX)
    (hWFExt : S.WellFormedExtends) {G : Graph} {Ls1 Ls2 : Finset Label} {t : Typing}
    (hLs1Ls2 : Ls1 ⊆ Ls2) (hLs1Closed : S.DClosedOn Ls1) (hLs2Closed : S.DClosedOn Ls2)
    (ht : (S.restrictLabels Ls2).CorrectTyping G t) :
    (S.restrictLabels Ls1).CorrectTyping G (restrictTyping t Ls1) := by
  intro n L hmem
  obtain ⟨hmemT, hL1⟩ := mem_restrictTyping.mp hmem
  have hcorrectL := ht n L hmemT
  have hAiff : L ∈ (S.restrictLabels Ls1).A ↔ L ∈ (S.restrictLabels Ls2).A := by
    simp only [Schema.restrictLabels, Finset.mem_inter]
    exact ⟨fun ⟨hLA, _⟩ => ⟨hLA, hLs1Ls2 hL1⟩, fun ⟨hLA, _⟩ => ⟨hLA, hL1⟩⟩
  have hagree1 : AgreeOn t (restrictTyping t Ls1) Ls1 := by
    intro n' L' hL'
    exact ⟨fun h => mem_restrictTyping.mpr ⟨h, hL'⟩, fun h => (mem_restrictTyping.mp h).1⟩
  refine ⟨fun hLnotA => ?_, fun hLA => ?_⟩
  · have hSat2 : Satisfies (S.restrictLabels Ls2) G t n (S.shapeDef L) :=
      hcorrectL.1 (fun h => hLnotA (hAiff.mpr h))
    have hSat1 : Satisfies (S.restrictLabels Ls1) G t n (S.shapeDef L) :=
      (Satisfies_restrictLabels_agree hWFX hWFExt hLs1Ls2 hLs1Closed hLs2Closed hL1).mpr hSat2
    have hdeps : (S.shapeDef L).depsIn Ls1 := S.shapeDef_depsIn hLs1Closed hL1
    exact (Satisfies.agree (Schema.restrictLabels_WellFormedX hWFX Ls1) hWFExt hLs1Closed hagree1
      hdeps n).mp hSat1
  · obtain ⟨x, hxmem, hSatx⟩ := hcorrectL.2 (hAiff.mp hLA)
    rw [Finset.mem_sdiff, Schema.restrictLabels_desc_eq hLs2Closed (hLs1Ls2 hL1)] at hxmem
    obtain ⟨hxdesc, hxnA2⟩ := hxmem
    have hxLs1 : x ∈ Ls1 := Schema.desc_subset_of_DClosedOn hLs1Closed hL1 hxdesc
    have hxLs2 : x ∈ Ls2 := hLs1Ls2 hxLs1
    have hxnA : x ∉ S.A := by
      simp only [Schema.restrictLabels, Finset.mem_inter] at hxnA2
      exact fun h => hxnA2 ⟨h, hxLs2⟩
    have hxmem' : x ∈ (S.restrictLabels Ls1).desc L \ (S.restrictLabels Ls1).A := by
      rw [Finset.mem_sdiff, Schema.restrictLabels_desc_eq hLs1Closed hL1]
      refine ⟨hxdesc, ?_⟩
      simp only [Schema.restrictLabels, Finset.mem_inter]
      exact fun h => hxnA h.1
    have hSat1 : Satisfies (S.restrictLabels Ls1) G t n (S.shapeDef x) :=
      (Satisfies_restrictLabels_agree hWFX hWFExt hLs1Ls2 hLs1Closed hLs2Closed hxLs1).mpr hSatx
    have hdepsx : (S.shapeDef x).depsIn Ls1 := S.shapeDef_depsIn hLs1Closed hxLs1
    exact ⟨x, hxmem', (Satisfies.agree (Schema.restrictLabels_WellFormedX hWFX Ls1) hWFExt
      hLs1Closed hagree1 hdepsx n).mp hSat1⟩

/-- A restriction to `Lo2 ⊆ Lo1` and then to `Lo2` again is the same as a
restriction to `Lo2` directly. This is the version of
`Typing.restrictTo_restrictTo` of 2017. -/
theorem restrictTyping_restrictTyping {t : Typing} {Lo1 Lo2 : Finset Label}
    (h : Lo2 ⊆ Lo1) : restrictTyping (restrictTyping t Lo1) Lo2 = restrictTyping t Lo2 := by
  apply Finset.ext
  rintro ⟨n, L⟩
  simp only [mem_restrictTyping]
  constructor
  · rintro ⟨⟨htmem, _⟩, hL⟩
    exact ⟨htmem, hL⟩
  · rintro ⟨htmem, hL⟩
    exact ⟨⟨htmem, h hL⟩, hL⟩

/-- A correct typing of `restrictLabels Ls1` is also a correct typing of
`restrictLabels Ls2`, for each `Ls1 ⊆ Ls2` (both `D_S`-closed). This is
the general version (for any set) of
`Schema.correctTyping_stratRestrict_mono`.

`restrictLabels_correct_restrictTo` also makes the *typing* smaller, and
loses data. This lemma keeps `t` exactly as it is. Only the schema becomes
larger. (As in `correctTyping_stratRestrict_mono`.) Each `.A` or `.desc`
witness in `Ls1` trivially stays in the larger `Ls2`, because the
intersection-based `restrictLabels` is monotone. -/
theorem Schema.correctTyping_restrictLabels_mono {S : Schema} (hWFX : S.WellFormedX)
    (hWFExt : S.WellFormedExtends) {Ls1 Ls2 : Finset Label} (hLs1Ls2 : Ls1 ⊆ Ls2)
    (hLs1Closed : S.DClosedOn Ls1) (hLs2Closed : S.DClosedOn Ls2) {G : Graph} {t : Typing}
    (ht_sub : t ⊆ (S.restrictLabels Ls1).univTyping G)
    (ht_correct : (S.restrictLabels Ls1).CorrectTyping G t) :
    (S.restrictLabels Ls2).CorrectTyping G t := by
  intro n L hmem
  have hLmem : L ∈ (S.restrictLabels Ls1).Y ∪ (S.restrictLabels Ls1).X :=
    (Finset.mem_product.mp (ht_sub hmem)).2
  have hLLs1 : L ∈ Ls1 := S.restrictLabels_mem_YX_subset Ls1 hLmem
  have hLLs2 : L ∈ Ls2 := hLs1Ls2 hLLs1
  have hAiff : L ∈ (S.restrictLabels Ls1).A ↔ L ∈ (S.restrictLabels Ls2).A := by
    simp only [Schema.restrictLabels, Finset.mem_inter]
    exact ⟨fun ⟨hLA, _⟩ => ⟨hLA, hLLs2⟩, fun ⟨hLA, _⟩ => ⟨hLA, hLLs1⟩⟩
  obtain ⟨hcorrectPlain, hcorrectAbs⟩ := ht_correct n L hmem
  refine ⟨fun hLnotA => ?_, fun hLA => ?_⟩
  · exact (Satisfies_restrictLabels_agree hWFX hWFExt hLs1Ls2 hLs1Closed hLs2Closed hLLs1).mp
      (hcorrectPlain (fun h => hLnotA (hAiff.mp h)))
  · obtain ⟨x, hxmem, hSatx⟩ := hcorrectAbs (hAiff.mpr hLA)
    rw [Finset.mem_sdiff, Schema.mem_desc] at hxmem
    obtain ⟨⟨hxX', hxpath⟩, hxnA⟩ := hxmem
    simp only [Schema.restrictLabels, Finset.mem_inter] at hxX' hxnA
    obtain ⟨hxX, hxLs1⟩ := hxX'
    have hxLs2 : x ∈ Ls2 := hLs1Ls2 hxLs1
    have hxnA' : x ∉ S.A := fun h => hxnA ⟨h, hxLs1⟩
    have hxmem' : x ∈ (S.restrictLabels Ls2).desc L \ (S.restrictLabels Ls2).A := by
      rw [Finset.mem_sdiff, Schema.mem_desc]
      refine ⟨⟨Finset.mem_inter.mpr ⟨hxX, hxLs2⟩, hxpath⟩, ?_⟩
      simp only [Schema.restrictLabels, Finset.mem_inter]
      exact fun h => hxnA' h.1
    exact ⟨x, hxmem',
      (Satisfies_restrictLabels_agree hWFX hWFExt hLs1Ls2 hLs1Closed hLs2Closed hxLs1).mp hSatx⟩

/-! ### Fusion -/

/-- **Fusion.** These two methods give the same result:

* Reveal `Ls2` in one step (`Lo = Ls`).
* Reveal `Ls2` in two steps through an intermediate checkpoint `Ls1`
  (`Lo = Ls2`, and then `Lo = Ls1`).

Thus, finer or coarser batches do not change the result of
`maxTypingAgreeing`. The conditions are:

* Each new label in `Ls2` has `D_S`-negative dependencies only in the
  original `Ls`.
* `Ls1` is `D_S`-closed for its own positive dependencies.

This is the version of `maxAgree_fusion` of 2017
(`ShexLean/Shex2017Schemas/Lemma2.lean`). The proof is almost the same
argument by inclusion in the two directions: each side, as a *full
object*, is a valid candidate for the `maxTypingAgreeing` of the other
side. The differences are:

* It passes the four well-formedness hypotheses that
  `maxTypingAgreeing_correct` and `restrictLabels_correct_restrictTo`
  need.
* It uses membership in `S.DEdge` and `S.DNegEdge` in place of the set
  containment of `posDeps` and `negDeps` of 2017. -/
theorem maxTypingAgreeing_fusion {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree)
    {G : Graph} {Ls Ls1 Ls2 : Finset Label} {T : Typing}
    (hLsLs1 : Ls ⊆ Ls1) (hLs1Ls2 : Ls1 ⊆ Ls2)
    (hLsClosed : S.DClosedOn Ls) (hLs1Closed : S.DClosedOn Ls1) (hLs2Closed : S.DClosedOn Ls2)
    (hLs1YX : Ls1 ⊆ S.Y ∪ S.X) (hLs2YX : Ls2 ⊆ S.Y ∪ S.X)
    (hneg2 : ∀ z ∈ Ls2, ((S.shapeDef z).depsAux false).negRefs ⊆ Ls)
    (hTsub : T ⊆ (S.restrictLabels Ls).univTyping G)
    (hTcorrect : (S.restrictLabels Ls).CorrectTyping G T) :
    maxTypingAgreeing (S.restrictLabels Ls2) G Ls1
        (maxTypingAgreeing (S.restrictLabels Ls1) G Ls T) =
      maxTypingAgreeing (S.restrictLabels Ls2) G Ls T := by
  set A := maxTypingAgreeing (S.restrictLabels Ls1) G Ls T with hA_def
  set B := maxTypingAgreeing (S.restrictLabels Ls2) G Ls1 A with hB_def
  set C := maxTypingAgreeing (S.restrictLabels Ls2) G Ls T with hC_def
  have hWFX1 : (S.restrictLabels Ls1).WellFormedX := Schema.restrictLabels_WellFormedX hWFX Ls1
  have hWFX2 : (S.restrictLabels Ls2).WellFormedX := Schema.restrictLabels_WellFormedX hWFX Ls2
  have hLs1Closed' := Schema.restrictLabels_DClosed hLs1Closed hLs1YX
  have hLs2Closed' := Schema.restrictLabels_DClosed hLs2Closed hLs2YX
  have hTsub1 : T ⊆ (S.restrictLabels Ls1).univTyping G := hTsub.trans (Schema.univTyping_mono hLsLs1)
  have hTcorrect1 : (S.restrictLabels Ls1).CorrectTyping G T :=
    Schema.correctTyping_restrictLabels_mono hWFX hWFExt hLsLs1 hLsClosed hLs1Closed hTsub hTcorrect
  have hTsub2 : T ⊆ (S.restrictLabels Ls2).univTyping G :=
    hTsub.trans (Schema.univTyping_mono (hLsLs1.trans hLs1Ls2))
  have hTcorrect2 : (S.restrictLabels Ls2).CorrectTyping G T :=
    Schema.correctTyping_restrictLabels_mono hWFX hWFExt (hLsLs1.trans hLs1Ls2) hLsClosed hLs2Closed
      hTsub hTcorrect
  have hAsub1 : A ⊆ (S.restrictLabels Ls1).univTyping G := maxTypingAgreeing_subset _ G _ _
  have hAcorrect1 : (S.restrictLabels Ls1).CorrectTyping G A :=
    maxTypingAgreeing_correct hWFX1 hWFExt hWFExtra hNEF hLs1Closed' hTsub1 hTcorrect1
      (fun z hz => hneg2 z (hLs1Ls2 (S.restrictLabels_mem_YX_subset Ls1 hz)))
  have hArestrict : restrictTyping A Ls = restrictTyping T Ls :=
    maxTypingAgreeing_restrictTo hTsub1 hTcorrect1
  have hAsub2 : A ⊆ (S.restrictLabels Ls2).univTyping G := hAsub1.trans (Schema.univTyping_mono hLs1Ls2)
  have hAcorrect2 : (S.restrictLabels Ls2).CorrectTyping G A :=
    Schema.correctTyping_restrictLabels_mono hWFX hWFExt hLs1Ls2 hLs1Closed hLs2Closed hAsub1
      hAcorrect1
  have hAC : A ⊆ C := subset_maxTypingAgreeing hAsub2 hAcorrect2 hArestrict
  have hBsub2 : B ⊆ (S.restrictLabels Ls2).univTyping G := maxTypingAgreeing_subset _ G _ _
  have hBcorrect2 : (S.restrictLabels Ls2).CorrectTyping G B :=
    maxTypingAgreeing_correct hWFX2 hWFExt hWFExtra hNEF hLs2Closed' hAsub2 hAcorrect2
      (fun z hz => (hneg2 z (S.restrictLabels_mem_YX_subset Ls2 hz)).trans hLsLs1)
  have hBrestrict1 : restrictTyping B Ls1 = restrictTyping A Ls1 :=
    maxTypingAgreeing_restrictTo hAsub2 hAcorrect2
  have hBC : B ⊆ C := by
    apply subset_maxTypingAgreeing hBsub2 hBcorrect2
    rw [← restrictTyping_restrictTyping (t := B) hLsLs1, hBrestrict1,
      restrictTyping_restrictTyping (t := A) hLsLs1, hArestrict]
  have hCB : C ⊆ B := by
    have hCsub2 : C ⊆ (S.restrictLabels Ls2).univTyping G := maxTypingAgreeing_subset _ G _ _
    have hCcorrect2 : (S.restrictLabels Ls2).CorrectTyping G C :=
      maxTypingAgreeing_correct hWFX2 hWFExt hWFExtra hNEF hLs2Closed' hTsub2 hTcorrect2
        (fun z hz => hneg2 z (S.restrictLabels_mem_YX_subset Ls2 hz))
    have hCrestrict : restrictTyping C Ls = restrictTyping T Ls :=
      maxTypingAgreeing_restrictTo hTsub2 hTcorrect2
    have hself1 : S.DClosedOn Ls1 := hLs1Closed
    have hCL1correct : (S.restrictLabels Ls1).CorrectTyping G (restrictTyping C Ls1) :=
      restrictLabels_correct_restrictTo hWFX hWFExt hLs1Ls2 hself1 hLs2Closed hCcorrect2
    have hCL1sub : restrictTyping C Ls1 ⊆ (S.restrictLabels Ls1).univTyping G := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := mem_restrictTyping.mp hp
      simp only [Schema.univTyping, Schema.restrictLabels] at hCsub2 ⊢
      exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp (hCsub2 hp1)).1, by
        simp only [Finset.mem_union, Finset.mem_inter]
        rcases Finset.mem_union.mp (Finset.mem_product.mp (hCsub2 hp1)).2 with h | h
        · exact Or.inl ⟨(Finset.mem_inter.mp h).1, hp2⟩
        · exact Or.inr ⟨(Finset.mem_inter.mp h).1, hp2⟩⟩
    have hCL1restrict : restrictTyping (restrictTyping C Ls1) Ls = restrictTyping T Ls := by
      rw [restrictTyping_restrictTyping hLsLs1, hCrestrict]
    have hCL1A : restrictTyping C Ls1 ⊆ A := subset_maxTypingAgreeing hCL1sub hCL1correct hCL1restrict
    have hCL1eqA : restrictTyping C Ls1 = restrictTyping A Ls1 := by
      apply Finset.Subset.antisymm
      · intro p hp
        obtain ⟨hp1, hp2⟩ := mem_restrictTyping.mp hp
        exact mem_restrictTyping.mpr ⟨hCL1A (mem_restrictTyping.mpr ⟨hp1, hp2⟩), hp2⟩
      · intro p hp
        obtain ⟨hp1, hp2⟩ := mem_restrictTyping.mp hp
        exact mem_restrictTyping.mpr ⟨hAC hp1, hp2⟩
    exact subset_maxTypingAgreeing hCsub2 hCcorrect2 hCL1eqA
  exact Finset.Subset.antisymm hBC hCB

/-- `maxTypingAgreeing` does nothing if you ask it to reveal exactly the
schema for which `fixed` is already correct and bounded. The only
candidate that agrees with itself is `fixed`. -/
theorem maxTypingAgreeing_self {S' : Schema} {G : Graph} {T : Typing}
    (hTsub : T ⊆ S'.univTyping G) (hTcorrect : S'.CorrectTyping G T) :
    maxTypingAgreeing S' G (S'.Y ∪ S'.X) T = T := by
  apply Finset.Subset.antisymm
  · have := Classical.decPred (fun t => S'.CorrectTyping G t ∧
      restrictTyping t (S'.Y ∪ S'.X) = restrictTyping T (S'.Y ∪ S'.X))
    apply Finset.sup_le
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    obtain ⟨htsub, -, htrestrict⟩ := ht
    have ht_eq : restrictTyping t (S'.Y ∪ S'.X) = t := by
      apply Finset.ext; rintro ⟨n, L⟩
      simp only [mem_restrictTyping, Schema.univTyping] at htsub ⊢
      exact ⟨fun h => h.1, fun h => ⟨h, (Finset.mem_product.mp (htsub h)).2⟩⟩
    have hT_eq : restrictTyping T (S'.Y ∪ S'.X) = T := by
      apply Finset.ext; rintro ⟨n, L⟩
      simp only [mem_restrictTyping, Schema.univTyping] at hTsub ⊢
      exact ⟨fun h => h.1, fun h => ⟨h, (Finset.mem_product.mp (hTsub h)).2⟩⟩
    rw [ht_eq, hT_eq] at htrestrict
    exact htrestrict.le
  · exact subset_maxTypingAgreeing hTsub hTcorrect rfl

/-!
**Lemma 2, general statement.**

The method is the same as in `ShexLean/Shex2017Schemas/Lemma2.lean` of
2017. In general, it is not possible to align the checkpoints of a second
stratification of your choice with a fixed combination of the checkpoints
of the first one. Two labels that do not depend on each other in `D_S` can
have opposite orders in two valid stratifications.

In its place:

1. We define one canonical process (`cont1`) that does not depend on a
   schedule. It reveals *a* valid next batch at each step.
2. We show that its result does not depend on the valid batch that each
   step selects (`cont1_indep`, with `maxTypingAgreeing_swap`).
3. We follow the process through the checkpoints of each stratification
   separately. This shows that it is equal to `Typing8` for *the two*
   stratifications.
-/

/-- The labels, not yet in `Fixed`, with the smallest `strat` value. This
is a canonical choice of "next batch", but it is not the only valid
choice. -/
def remainingMin (S : Schema) (strat : Label → ℕ) (Fixed : Finset Label) :
    Finset Label :=
  ((S.Y ∪ S.X) \ Fixed).filter (fun L => ∀ L' ∈ (S.Y ∪ S.X) \ Fixed, strat L ≤ strat L')

theorem remainingMin_subset {S : Schema} {strat : Label → ℕ} {Fixed : Finset Label} :
    remainingMin S strat Fixed ⊆ (S.Y ∪ S.X) \ Fixed := Finset.filter_subset _ _

theorem remainingMin_nonempty {S : Schema} {strat : Label → ℕ} {Fixed : Finset Label}
    (h : ((S.Y ∪ S.X) \ Fixed).Nonempty) : (remainingMin S strat Fixed).Nonempty := by
  obtain ⟨L₀, hL₀, hmin⟩ := Finset.exists_min_image ((S.Y ∪ S.X) \ Fixed) strat h
  exact ⟨L₀, Finset.mem_filter.mpr ⟨hL₀, hmin⟩⟩

/-- The batch of `remainingMin` (for each valid stratification `strat`)
has `D_S`-negative dependencies only in `Fixed`. -/
theorem remainingMin_neg {S : Schema} (strat : Stratification S) (hDClosed : S.DClosed)
    (Fixed : Finset Label) :
    ∀ z ∈ remainingMin S strat.strat Fixed, ∀ z', S.DNegEdge z z' → z' ∈ Fixed := by
  intro z hz z' hz'
  obtain ⟨hzrem, hzmin⟩ := Finset.mem_filter.mp hz
  obtain ⟨hzYX, hznotFixed⟩ := Finset.mem_sdiff.mp hzrem
  have hz'YX : z' ∈ S.Y ∪ S.X := hDClosed z hzYX z' (S.DEdge_of_DNegEdge hz')
  by_contra hz'notFixed
  have hz'rem : z' ∈ (S.Y ∪ S.X) \ Fixed := Finset.mem_sdiff.mpr ⟨hz'YX, hz'notFixed⟩
  have h1 := strat.negDep_lt z hzYX z' hz'
  have h2 := hzmin z' hz'rem
  omega

/-- `Fixed ∪ remainingMin strat Fixed` is self-contained for `D_S`. -/
theorem remainingMin_pos {S : Schema} (strat : Stratification S) (hDClosed : S.DClosed)
    (Fixed : Finset Label) :
    ∀ z ∈ remainingMin S strat.strat Fixed, ∀ z', S.DEdge z z' →
      z' ∈ Fixed ∪ remainingMin S strat.strat Fixed := by
  intro z hz z' hz'
  obtain ⟨hzrem, hzmin⟩ := Finset.mem_filter.mp hz
  obtain ⟨hzYX, hznotFixed⟩ := Finset.mem_sdiff.mp hzrem
  have hz'YX : z' ∈ S.Y ∪ S.X := hDClosed z hzYX z' hz'
  by_cases hz'Fixed : z' ∈ Fixed
  · exact Finset.mem_union_left _ hz'Fixed
  · refine Finset.mem_union_right _ ?_
    have hz'rem : z' ∈ (S.Y ∪ S.X) \ Fixed := Finset.mem_sdiff.mpr ⟨hz'YX, hz'Fixed⟩
    have h1 := strat.dep_le z hzYX z' hz'
    have h2 := hzmin z' hz'rem
    refine Finset.mem_filter.mpr ⟨hz'rem, fun L' hL' => ?_⟩
    have h3 := hzmin L' hL'
    omega

/-- Reveal the `remainingMin` batch of `strat` `n` times, or until no
labels remain. `n` is fuel. It does not have to be a tight bound. -/
noncomputable def cont1Fuel (S : Schema) (strat : Stratification S) (G : Graph) :
    ℕ → Finset Label → Typing → Typing
  | 0, _, T => T
  | (n + 1), Fixed, T =>
      if ((S.Y ∪ S.X) \ Fixed).Nonempty then
        cont1Fuel S strat G n (Fixed ∪ remainingMin S strat.strat Fixed)
          (maxTypingAgreeing (S.restrictLabels (Fixed ∪ remainingMin S strat.strat Fixed)) G
            Fixed T)
      else T

private theorem remainingMin_card_lt (S : Schema) (strat : Label → ℕ)
    {Fixed : Finset Label} (h : ((S.Y ∪ S.X) \ Fixed).Nonempty) :
    ((S.Y ∪ S.X) \ (Fixed ∪ remainingMin S strat Fixed)).card < ((S.Y ∪ S.X) \ Fixed).card := by
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
    {Fixed : Finset Label} (h : ¬ ((S.Y ∪ S.X) \ Fixed).Nonempty) (T : Typing) :
    ∀ n, cont1Fuel S strat G n Fixed T = T
  | 0 => rfl
  | (n + 1) => by simp only [cont1Fuel, ite_eq_right h]

/-- When the fuel is sufficient to use all the remaining labels, more fuel
does not change the result. -/
theorem cont1Fuel_stable (S : Schema) (strat : Stratification S) (G : Graph) :
    ∀ Fixed : Finset Label, ∀ T : Typing, ∀ n n' : ℕ, ((S.Y ∪ S.X) \ Fixed).card ≤ n →
      ((S.Y ∪ S.X) \ Fixed).card ≤ n' →
        cont1Fuel S strat G n Fixed T = cont1Fuel S strat G n' Fixed T := by
  intro Fixed
  induction hcard : ((S.Y ∪ S.X) \ Fixed).card using Nat.strong_induction_on generalizing Fixed with
  | _ card ih =>
    intro T n n' hn hn'
    by_cases hne : ((S.Y ∪ S.X) \ Fixed).Nonempty
    · have hcardpos : 0 < card := hcard ▸ Finset.card_pos.mpr hne
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
      simp only [cont1Fuel, ite_eq_left hne]
      have hcard' : ((S.Y ∪ S.X) \ (Fixed ∪ remainingMin S strat.strat Fixed)).card < card :=
        hcard ▸ remainingMin_card_lt S strat.strat hne
      exact ih _ hcard' _ rfl
        (maxTypingAgreeing (S.restrictLabels (Fixed ∪ remainingMin S strat.strat Fixed)) G Fixed T)
        m m' (by omega) (by omega)
    · rw [cont1Fuel_of_not_nonempty S strat G hne T n, cont1Fuel_of_not_nonempty S strat G hne T n']

/-- `cont1 S strat G Fixed T`: continue the `remainingMin` process from
`(Fixed, T)` until it gets to `S.Y ∪ S.X`. At each step, `strat` selects
the batch. (This is a fixed, concrete choice. But `cont1_indep` below shows
that *each* valid first step gives the same final answer.) -/
noncomputable def cont1 (S : Schema) (strat : Stratification S) (G : Graph)
    (Fixed : Finset Label) (T : Typing) : Typing :=
  cont1Fuel S strat G (S.Y ∪ S.X).card Fixed T

theorem cont1_eq_fuel (S : Schema) (strat : Stratification S) (G : Graph)
    (Fixed : Finset Label) (T : Typing) (n : ℕ) (hn : ((S.Y ∪ S.X) \ Fixed).card ≤ n) :
    cont1 S strat G Fixed T = cont1Fuel S strat G n Fixed T :=
  cont1Fuel_stable S strat G Fixed T (S.Y ∪ S.X).card n (Finset.card_le_card Finset.sdiff_subset) hn

theorem cont1_done (S : Schema) (strat : Stratification S) (G : Graph)
    {Fixed : Finset Label} (h : ¬ ((S.Y ∪ S.X) \ Fixed).Nonempty) (T : Typing) :
    cont1 S strat G Fixed T = T := by
  have hcardzero : ((S.Y ∪ S.X) \ Fixed).card = 0 := by
    rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]; exact h
  rw [cont1_eq_fuel S strat G Fixed T 1 (by omega)]
  simp only [cont1Fuel, ite_eq_right h]

theorem cont1_step (S : Schema) (strat : Stratification S) (G : Graph)
    {Fixed : Finset Label} (h : ((S.Y ∪ S.X) \ Fixed).Nonempty) (T : Typing) :
    cont1 S strat G Fixed T = cont1 S strat G (Fixed ∪ remainingMin S strat.strat Fixed)
      (maxTypingAgreeing (S.restrictLabels (Fixed ∪ remainingMin S strat.strat Fixed)) G Fixed T) := by
  obtain ⟨m, hm⟩ : ∃ m, ((S.Y ∪ S.X) \ Fixed).card = m + 1 :=
    ⟨((S.Y ∪ S.X) \ Fixed).card - 1, by have := Finset.card_pos.mpr h; omega⟩
  rw [cont1_eq_fuel S strat G Fixed T (m + 1) (le_of_eq hm)]
  simp only [cont1Fuel, ite_eq_left h]
  refine (cont1_eq_fuel S strat G _ _ m ?_).symm
  have := remainingMin_card_lt S strat.strat h
  omega

/-- **Swap.** Let `A` and `B` be two batches. Let *each* batch depend
(negatively) only on the common base `Ls0`, and let each batch be
`D_S`-closed together with `Ls0`. Then you can reveal them in the two
orders and get the same result. With `maxTypingAgreeing_fusion`, the two
sides both become the one-step construction over `Ls0 ∪ A ∪ B`.

This is the formal content of "a different order of independent material
does not change the final typing". `cont1_indep` below uses it to show
that the first step of `cont1` has no effect on the result. -/
theorem maxTypingAgreeing_swap {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree)
    {G : Graph} {Ls0 A B : Finset Label} {T : Typing}
    (hLs0Closed : S.DClosedOn Ls0) (hLs0AClosed : S.DClosedOn (Ls0 ∪ A))
    (hLs0BClosed : S.DClosedOn (Ls0 ∪ B)) (hLs0ABClosed : S.DClosedOn (Ls0 ∪ A ∪ B))
    (hLs0AYX : Ls0 ∪ A ⊆ S.Y ∪ S.X) (hLs0BYX : Ls0 ∪ B ⊆ S.Y ∪ S.X)
    (hLs0ABYX : Ls0 ∪ A ∪ B ⊆ S.Y ∪ S.X)
    (hAneg : ∀ z ∈ A, ((S.shapeDef z).depsAux false).negRefs ⊆ Ls0)
    (hBneg : ∀ z ∈ B, ((S.shapeDef z).depsAux false).negRefs ⊆ Ls0)
    (hTsub : T ⊆ (S.restrictLabels Ls0).univTyping G)
    (hTcorrect : (S.restrictLabels Ls0).CorrectTyping G T) :
    maxTypingAgreeing (S.restrictLabels (Ls0 ∪ A ∪ B)) G (Ls0 ∪ A)
        (maxTypingAgreeing (S.restrictLabels (Ls0 ∪ A)) G Ls0 T) =
      maxTypingAgreeing (S.restrictLabels (Ls0 ∪ A ∪ B)) G (Ls0 ∪ B)
        (maxTypingAgreeing (S.restrictLabels (Ls0 ∪ B)) G Ls0 T) := by
  have hneg2' : ∀ z ∈ Ls0 ∪ A ∪ B, ((S.shapeDef z).depsAux false).negRefs ⊆ Ls0 := by
    intro z hz
    simp only [Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · intro z' hz'
      exact hLs0Closed z hz z' (Or.inl (S.dep_of_depShapeNeg hz'))
    · exact hAneg z hz
    · exact hBneg z hz
  have hLs0LsA : Ls0 ⊆ Ls0 ∪ A := Finset.subset_union_left
  have hLs0LsB : Ls0 ⊆ Ls0 ∪ B := Finset.subset_union_left
  have hLsA2 : Ls0 ∪ A ⊆ Ls0 ∪ A ∪ B := Finset.subset_union_left
  have hLsB2 : Ls0 ∪ B ⊆ Ls0 ∪ A ∪ B := by
    intro x hx
    simp only [Finset.mem_union] at hx ⊢
    tauto
  have hLHS := maxTypingAgreeing_fusion hWFX hWFExt hWFExtra hNEF hLs0LsA hLsA2
    hLs0Closed hLs0AClosed hLs0ABClosed hLs0AYX hLs0ABYX hneg2' hTsub hTcorrect
  have hRHS := maxTypingAgreeing_fusion hWFX hWFExt hWFExtra hNEF hLs0LsB hLsB2
    hLs0Closed hLs0BClosed hLs0ABClosed hLs0BYX hLs0ABYX hneg2' hTsub hTcorrect
  rw [hLHS, hRHS]

/-- **Independence.** Start `cont1` from a `D_S`-closed `(Fixed, T)`. Its
final answer does not change if we first reveal *a* different valid batch
`C`. (`C` is not necessarily the choice of `remainingMin`, and is not
necessarily disjoint from `Fixed`.) Thus, `cont1` does not depend on the
valid batch that its `strat` selects at each step. -/
theorem cont1_indep {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat : Stratification S) (G : Graph) :
    ∀ Fixed : Finset Label, ∀ T : Typing,
      Fixed ⊆ S.Y ∪ S.X → S.DClosedOn Fixed →
      T ⊆ (S.restrictLabels Fixed).univTyping G →
      (S.restrictLabels Fixed).CorrectTyping G T →
      ∀ C : Finset Label, C ⊆ S.Y ∪ S.X →
        (∀ z ∈ C, ((S.shapeDef z).depsAux false).negRefs ⊆ Fixed) →
        (∀ z ∈ C, ∀ z', S.DEdge z z' → z' ∈ Fixed ∪ C) →
        cont1 S strat G Fixed T =
          cont1 S strat G (Fixed ∪ C)
            (maxTypingAgreeing (S.restrictLabels (Fixed ∪ C)) G Fixed T) := by
  intro Fixed
  induction hcard : ((S.Y ∪ S.X) \ Fixed).card using Nat.strong_induction_on generalizing Fixed with
  | _ card ih =>
    intro T hFixedYX hFixedClosed hTsub hTcorrect C hCsub hCneg hCpos
    rcases (C \ Fixed).eq_empty_or_nonempty with hCempty | hCnew
    · have hFixedC : Fixed ∪ C = Fixed := by
        apply Finset.union_eq_left.mpr
        intro x hx
        by_contra hxFixed
        have hxCF : x ∈ C \ Fixed := Finset.mem_sdiff.mpr ⟨hx, hxFixed⟩
        rw [hCempty] at hxCF
        exact absurd hxCF (Finset.notMem_empty x)
      have hMTA : maxTypingAgreeing (S.restrictLabels Fixed) G Fixed T = T := by
        have h := maxTypingAgreeing_self (S' := S.restrictLabels Fixed) hTsub hTcorrect
        rwa [Schema.restrictLabels_YX_eq hFixedYX] at h
      rw [hFixedC, hMTA]
    · by_cases hne : ((S.Y ∪ S.X) \ Fixed).Nonempty
      · have hA₁neg := remainingMin_neg strat hDClosed Fixed
        have hA₁pos := remainingMin_pos strat hDClosed Fixed
        have hA₁ne := remainingMin_nonempty (S := S) (strat := strat.strat) hne
        have hA₁sub : remainingMin S strat.strat Fixed ⊆ S.Y ∪ S.X :=
          remainingMin_subset.trans Finset.sdiff_subset
        have hcardA₁ : ((S.Y ∪ S.X) \ (Fixed ∪ remainingMin S strat.strat Fixed)).card < card :=
          hcard ▸ remainingMin_card_lt S strat.strat hne
        set A₁ := remainingMin S strat.strat Fixed with hA₁_def
        have hA₁negRefs : ∀ z ∈ A₁, ((S.shapeDef z).depsAux false).negRefs ⊆ Fixed :=
          fun z hz z' hz' => hA₁neg z hz z' (Or.inl hz')
        have hFA₁YX : Fixed ∪ A₁ ⊆ S.Y ∪ S.X := Finset.union_subset hFixedYX hA₁sub
        have hFA₁Closed : S.DClosedOn (Fixed ∪ A₁) := by
          intro z hz z' hedge
          simp only [Finset.mem_union] at hz
          rcases hz with hz | hz
          · exact Finset.mem_union_left _ (hFixedClosed z hz z' hedge)
          · exact hA₁pos z hz z' hedge
        have hTsubA₁ : T ⊆ (S.restrictLabels (Fixed ∪ A₁)).univTyping G :=
          hTsub.trans (Schema.univTyping_mono Finset.subset_union_left)
        have hTcorrectA₁ : (S.restrictLabels (Fixed ∪ A₁)).CorrectTyping G T :=
          Schema.correctTyping_restrictLabels_mono hWFX hWFExt Finset.subset_union_left
            hFixedClosed hFA₁Closed hTsub hTcorrect
        have hTA₁sub : maxTypingAgreeing (S.restrictLabels (Fixed ∪ A₁)) G Fixed T ⊆
            (S.restrictLabels (Fixed ∪ A₁)).univTyping G := maxTypingAgreeing_subset _ G _ _
        have hFA₁negRefs : ∀ z ∈ Fixed ∪ A₁, ((S.shapeDef z).depsAux false).negRefs ⊆ Fixed := by
          intro z hz
          rcases Finset.mem_union.mp hz with hz | hz
          · exact fun z' hz' => hFixedClosed z hz z' (Or.inl (S.dep_of_depShapeNeg hz'))
          · exact hA₁negRefs z hz
        have hTA₁correct : (S.restrictLabels (Fixed ∪ A₁)).CorrectTyping G
            (maxTypingAgreeing (S.restrictLabels (Fixed ∪ A₁)) G Fixed T) :=
          maxTypingAgreeing_correct (Schema.restrictLabels_WellFormedX hWFX _) hWFExt hWFExtra hNEF
            (Schema.restrictLabels_DClosed hFA₁Closed hFA₁YX) hTsubA₁ hTcorrectA₁
            (fun z hz => hFA₁negRefs z (S.restrictLabels_mem_YX_subset (Fixed ∪ A₁) hz))
        -- First use of `ih`: base `Fixed ∪ A₁`, jump `C`.
        have hstep1 := ih _ hcardA₁ (Fixed ∪ A₁) rfl
          (maxTypingAgreeing (S.restrictLabels (Fixed ∪ A₁)) G Fixed T) hFA₁YX hFA₁Closed
          hTA₁sub hTA₁correct
          C hCsub (fun z hz => (hCneg z hz).trans Finset.subset_union_left)
          (fun z hz z' hz' => by
            rcases Finset.mem_union.mp (hCpos z hz z' hz') with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
            · exact Finset.mem_union_right _ h)
        -- `Fixed ∪ C` is `D_S`-closed and in `Y ∪ X`, and `T''` is
        -- correct and bounded for it.
        have hFCYX : Fixed ∪ C ⊆ S.Y ∪ S.X := Finset.union_subset hFixedYX hCsub
        have hFCClosed : S.DClosedOn (Fixed ∪ C) := by
          intro z hz z' hedge
          simp only [Finset.mem_union] at hz
          rcases hz with hz | hz
          · exact Finset.mem_union_left _ (hFixedClosed z hz z' hedge)
          · exact hCpos z hz z' hedge
        have hTsubC : T ⊆ (S.restrictLabels (Fixed ∪ C)).univTyping G :=
          hTsub.trans (Schema.univTyping_mono Finset.subset_union_left)
        have hTcorrectC : (S.restrictLabels (Fixed ∪ C)).CorrectTyping G T :=
          Schema.correctTyping_restrictLabels_mono hWFX hWFExt Finset.subset_union_left
            hFixedClosed hFCClosed hTsub hTcorrect
        set T'' := maxTypingAgreeing (S.restrictLabels (Fixed ∪ C)) G Fixed T with hT''_def
        have hT''sub : T'' ⊆ (S.restrictLabels (Fixed ∪ C)).univTyping G :=
          maxTypingAgreeing_subset _ G _ _
        have hFCnegRefs : ∀ z ∈ Fixed ∪ C, ((S.shapeDef z).depsAux false).negRefs ⊆ Fixed := by
          intro z hz
          rcases Finset.mem_union.mp hz with hz | hz
          · exact fun z' hz' => hFixedClosed z hz z' (Or.inl (S.dep_of_depShapeNeg hz'))
          · exact hCneg z hz
        have hT''correct : (S.restrictLabels (Fixed ∪ C)).CorrectTyping G T'' :=
          maxTypingAgreeing_correct (Schema.restrictLabels_WellFormedX hWFX _) hWFExt hWFExtra hNEF
            (Schema.restrictLabels_DClosed hFCClosed hFCYX) hTsubC hTcorrectC
            (fun z hz => hFCnegRefs z (S.restrictLabels_mem_YX_subset (Fixed ∪ C) hz))
        have hcardC : ((S.Y ∪ S.X) \ (Fixed ∪ C)).card < card := by
          rw [← hcard]
          apply Finset.card_lt_card
          constructor
          · intro x hx
            simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
            tauto
          · intro hsub
            obtain ⟨L₀, hL₀⟩ := hCnew
            obtain ⟨hL₀C, hL₀nFixed⟩ := Finset.mem_sdiff.mp hL₀
            have hL₀rem : L₀ ∈ (S.Y ∪ S.X) \ Fixed := Finset.mem_sdiff.mpr ⟨hCsub hL₀C, hL₀nFixed⟩
            have hcontra := hsub hL₀rem
            simp only [Finset.mem_sdiff, Finset.mem_union] at hcontra
            exact hcontra.2 (Or.inr hL₀C)
        -- Second use of `ih`: base `Fixed ∪ C`, jump `A₁`.
        have hstep2 := ih _ hcardC (Fixed ∪ C) rfl T'' hFCYX hFCClosed hT''sub hT''correct
          A₁ hA₁sub (fun z hz => (hA₁negRefs z hz).trans Finset.subset_union_left)
          (fun z hz z' hz' => by
            rcases Finset.mem_union.mp (hA₁pos z hz z' hz') with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
            · exact Finset.mem_union_right _ h)
        -- Combine with `cont1_step` and `maxTypingAgreeing_swap`.
        have hLs0ABClosed : S.DClosedOn (Fixed ∪ A₁ ∪ C) := by
          intro z hz z' hedge
          simp only [Finset.mem_union] at hz
          rcases hz with (hz | hz) | hz
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hFixedClosed z hz z' hedge))
          · rcases Finset.mem_union.mp (hA₁pos z hz z' hedge) with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
          · rcases Finset.mem_union.mp (hCpos z hz z' hedge) with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
            · exact Finset.mem_union_right _ h
        have hLs0ABYX : Fixed ∪ A₁ ∪ C ⊆ S.Y ∪ S.X := Finset.union_subset hFA₁YX hCsub
        have hswap := maxTypingAgreeing_swap hWFX hWFExt hWFExtra hNEF hFixedClosed hFA₁Closed
          hFCClosed hLs0ABClosed hFA₁YX hFCYX hLs0ABYX hA₁negRefs hCneg hTsub hTcorrect
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
      · exfalso
        obtain ⟨L₀, hL₀⟩ := hCnew
        obtain ⟨hL₀C, hL₀nFixed⟩ := Finset.mem_sdiff.mp hL₀
        exact hne ⟨L₀, Finset.mem_sdiff.mpr ⟨hCsub hL₀C, hL₀nFixed⟩⟩

/-! ### Applying `cont1_indep` along the checkpoints of a stratification -/

theorem Schema.stratum_zero (S : Schema) (strat : Stratification S) :
    S.stratum strat.strat 0 = ∅ := by
  unfold Schema.stratum
  rw [Finset.filter_eq_empty_iff]
  intro z hz hle
  have := (strat.mem_range z hz).1
  omega

/-- A stronger result than `Schema.stratum_DClosedOn` for the negative
side. The negative dependencies of a label are strictly *inside the
previous* checkpoint, not only inside its own checkpoint. This is the
version of `Schema.stratum_neg_confined` of 2017. -/
theorem Schema.stratum_negDep_confined {S : Schema} (strat : Stratification S) (hDClosed : S.DClosed)
    (i : ℕ) : ∀ z ∈ S.stratum strat.strat i,
      ((S.shapeDef z).depsAux false).negRefs ⊆ S.stratum strat.strat (i - 1) := by
  intro z hz z' hz'
  simp only [Schema.stratum, Finset.mem_filter] at hz ⊢
  obtain ⟨hzYX, hzi⟩ := hz
  have hDNeg : S.DNegEdge z z' := Or.inl hz'
  have hz'YX : z' ∈ S.Y ∪ S.X := hDClosed z hzYX z' (S.DEdge_of_DNegEdge hDNeg)
  have hlt := strat.negDep_lt z hzYX z' hDNeg
  exact ⟨hz'YX, by omega⟩

/-- `S.stratRestrict strat i` and `S.restrictLabels (S.stratum strat i)`
make the same schema. (This is almost `rfl`, but not exactly, because the
field filters of `stratRestrict` and the intersections of `restrictLabels`
are different `Finset` expressions.)

This lemma connects `stratTypingSeq_correct`
(`ShexLean/Shex2026InheritanceDisjunction/Proposition1.lean`, which uses
`stratRestrict`) with the `restrictLabels` vocabulary that the general
argument of this file needs. It has the same role as
`Schema.stratRestrict_eq_restrictLabels` of 2017
(`ShexLean/Shex2017Schemas/Algorithm1.lean`). -/
theorem Schema.stratRestrict_eq_restrictLabels (S : Schema) (strat : Label → ℕ) (i : ℕ) :
    S.stratRestrict strat i = S.restrictLabels (S.stratum strat i) := by
  unfold Schema.stratRestrict Schema.restrictLabels Schema.stratum
  congr 1
  · apply Finset.ext; intro x
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_union]
    tauto
  · apply Finset.ext; intro x
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_union]
    tauto
  · apply Finset.ext; intro x
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hxA, hxle⟩; exact ⟨hxA, Or.inr (S.A_subX hxA), hxle⟩
    · rintro ⟨hxA, _, hxle⟩; exact ⟨hxA, hxle⟩

/-- Apply `cont1_indep` along the checkpoints of `strat'`. `cont1` uses
*any* fixed `strat0` internally. It agrees with `strat'` at each checkpoint
of `strat'`, for each `strat0`. -/
theorem cont1_chain {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat0 : Stratification S) (G : Graph) (strat' : Stratification S) :
    ∀ i ≤ strat'.k,
      cont1 S strat0 G ∅ ∅ = cont1 S strat0 G (S.stratum strat'.strat i)
        (stratTypingSeq S strat'.strat G i)
  | 0, _ => by simp [Schema.stratum_zero, stratTypingSeq]
  | (i + 1), hi1 => by
      have hi : i ≤ strat'.k := by omega
      have hIH := cont1_chain hWFX hWFExt hWFExtra hNEF hDClosed strat0 G strat' i hi
      have hT' := stratTypingSeq_correct hWFX hWFExt hWFExtra hNEF hDClosed strat' G i
      rw [Schema.stratRestrict_eq_restrictLabels] at hT'
      have hself : S.DClosedOn (S.stratum strat'.strat i) := Schema.stratum_DClosedOn hDClosed strat' i
      set C := S.stratum strat'.strat (i + 1) \ S.stratum strat'.strat i with hC_def
      have hCsub : C ⊆ S.Y ∪ S.X :=
        Finset.sdiff_subset.trans (Finset.filter_subset _ _)
      have hUnion : S.stratum strat'.strat i ∪ C = S.stratum strat'.strat (i + 1) := by
        rw [hC_def, Finset.union_sdiff_of_subset (Schema.stratum_mono (by omega))]
      have hCneg : ∀ z ∈ C, ((S.shapeDef z).depsAux false).negRefs ⊆ S.stratum strat'.strat i := by
        intro z hz
        have hz' : z ∈ S.stratum strat'.strat (i + 1) := hUnion ▸ Finset.mem_union_right _ hz
        have := Schema.stratum_negDep_confined strat' hDClosed (i + 1) z hz'
        simpa using this
      have hCpos : ∀ z ∈ C, ∀ z', S.DEdge z z' → z' ∈ S.stratum strat'.strat i ∪ C := by
        intro z hz z' hedge
        rw [hUnion]
        have hz' : z ∈ S.stratum strat'.strat (i + 1) := hUnion ▸ Finset.mem_union_right _ hz
        exact Schema.stratum_DClosedOn hDClosed strat' (i + 1) z hz' z' hedge
      have hindep := cont1_indep hWFX hWFExt hWFExtra hNEF hDClosed strat0 G
        (S.stratum strat'.strat i) (stratTypingSeq S strat'.strat G i)
        (Finset.filter_subset _ _) hself hT'.1 hT'.2 C hCsub hCneg hCpos
      have hstep : maxTypingAgreeing (S.restrictLabels (S.stratum strat'.strat (i + 1))) G
          (S.stratum strat'.strat i) (stratTypingSeq S strat'.strat G i) =
          stratTypingSeq S strat'.strat G (i + 1) := by
        rw [← Schema.stratRestrict_eq_restrictLabels]; rfl
      rw [hIH, hindep, hUnion, hstep]

/-- `cont1 S strat0 G ∅ ∅` is equal to `Typing8` for *each* valid
stratification. Thus, it is equal for `strat1` and also for `strat2`. -/
theorem cont1_eq_Typing8 {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat0 : Stratification S) (G : Graph) (strat' : Stratification S) :
    cont1 S strat0 G ∅ ∅ = Typing8 G S strat' := by
  have h := cont1_chain hWFX hWFExt hWFExtra hNEF hDClosed strat0 G strat' strat'.k (le_refl _)
  rw [h]
  apply cont1_done
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset]
  intro z hz
  simp only [Schema.stratum, Finset.mem_filter]
  exact ⟨hz, (strat'.mem_range z hz).2⟩

/-- **Lemma 2.** `τ_max(S,σ,G)` (Definition 8) does not depend on the
stratification `σ` of `S` that you select. The two sides are equal to
`cont1 S strat1 G ∅ ∅`. This is a canonical process that always reveals
each "ready" label (`remainingMin`). It does not depend on the valid
stratification that justifies each step (`cont1_indep`). -/
theorem lemma2 {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat1 strat2 : Stratification S) (G : Graph) :
    Typing8 G S strat1 = Typing8 G S strat2 := by
  rw [← cont1_eq_Typing8 hWFX hWFExt hWFExtra hNEF hDClosed strat1 G strat1,
    ← cont1_eq_Typing8 hWFX hWFExt hWFExtra hNEF hDClosed strat1 G strat2]

end ShexLean.InheritanceDisjunction
