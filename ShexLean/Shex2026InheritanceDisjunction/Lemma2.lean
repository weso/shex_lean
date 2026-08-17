import ShexLean.Shex2026InheritanceDisjunction.Proposition1
import Mathlib.Data.Finset.Max

/-!
Lemma 2 (§4.3) of the 2025 "Shape Expressions with Inheritance" paper:
`τ_max(S,σ,G)` (Definition 8) does not depend on which stratification `σ`
of `S` is chosen.

This file ports the 2017 formalization's own `ShexLean/Shex2017Schemas/Lemma2.lean` — the
paper itself only sketches this proof ("Proof. (Idea)..."), so 2017's file
built a full, independent argument from the ground up (Fusion/Swap/a
schedule-agnostic `cont1` process/Independence), which transfers here
almost unchanged in *shape*. What does **not** transfer for free: 2017's
`Satisfies` never consults the schema at all, so "restrict the schema to a
self-contained label set" was free (`Schema.restrictLabels`, sharing
`shapeDef`, with no further invariance lemma needed). Here `Satisfies`
genuinely depends on the schema (via `.anc`/`.ancSet`, exactly the gap
`ShexLean/Shex2025Inheritance/Proposition1.lean`'s `Satisfies_stratRestrict_agree`
closed for *stratum*-shaped restrictions) — so this file first generalizes
that whole schema-invariance argument from `Schema.stratRestrict` (tied to
a stratification) to `Schema.restrictLabels` (an arbitrary `D_S`-closed
label set), which is what `cont1`'s schedule-agnostic batches actually need.
-/

namespace ShexLean.InheritanceDisjunction

/-! ### `Schema.restrictLabels`: restriction to an arbitrary label set

Generalizes `Schema.stratRestrict` (`ShexLean/Shex2025Inheritance/Proposition1.lean`)
away from being tied to a stratification — `Ls` here is any label set, not
necessarily `S.stratum strat i` for some `strat`/`i`. -/

/-- `S` restricted to an arbitrary label set `Ls`, keeping the same
definitions — 2017's `Schema.restrictLabels` (`ShexLean/Shex2017Schemas/Lemma2.lean`),
generalizing `Schema.stratRestrict`. -/
def Schema.restrictLabels (S : Schema) (Ls : Finset ShapeLabel) : Schema where
  Y := S.Y ∩ Ls
  X := S.X ∩ Ls
  A := S.A ∩ Ls
  disjointYX := S.disjointYX.mono Finset.inter_subset_left Finset.inter_subset_left
  A_subX := by
    intro z hz
    simp only [Finset.mem_inter] at hz ⊢
    exact ⟨S.A_subX hz.1, hz.2⟩
  shapeDef := S.shapeDef

/-- When `Ls ⊆ Y ∪ X`, `restrictLabels Ls`'s own `Y ∪ X` is exactly `Ls` —
the general analogue of `Schema.stratRestrict_YX_eq_stratum`. -/
theorem Schema.restrictLabels_YX_eq {S : Schema} {Ls : Finset ShapeLabel}
    (hLs : Ls ⊆ S.Y ∪ S.X) : (S.restrictLabels Ls).Y ∪ (S.restrictLabels Ls).X = Ls := by
  unfold Schema.restrictLabels
  rw [← Finset.union_inter_distrib_right]
  exact Finset.inter_eq_right.mpr hLs

/-- `WellFormedX` transfers to any `restrictLabels` — the general analogue
of `Schema.stratRestrict_WellFormedX`. -/
theorem Schema.restrictLabels_WellFormedX {S : Schema} (hWFX : S.WellFormedX)
    (Ls : Finset ShapeLabel) : (S.restrictLabels Ls).WellFormedX := by
  intro x hx
  simp only [Schema.restrictLabels, Finset.mem_inter] at hx
  exact hWFX x hx.1

/-- `restrictLabels` doesn't change `D_S`'s edges — the general analogue of
`Schema.stratRestrict_DEdge_eq`. -/
theorem Schema.restrictLabels_DEdge_eq (S : Schema) (Ls : Finset ShapeLabel) :
    (S.restrictLabels Ls).DEdge = S.DEdge := rfl

/-- `(restrictLabels Ls).Y ∪ (restrictLabels Ls).X ⊆ Ls` always (regardless
of whether `Ls ⊆ Y ∪ X`) — the intersection-based definition never adds
anything beyond `Ls` itself. Used to convert a `∀ z ∈ Ls, ...` hypothesis
into the `∀ z ∈ (restrictLabels Ls).Y ∪ (restrictLabels Ls).X, ...` form
`maxTypingAgreeing_correct` actually wants. -/
theorem Schema.restrictLabels_mem_YX_subset (S : Schema) (Ls : Finset ShapeLabel) :
    (S.restrictLabels Ls).Y ∪ (S.restrictLabels Ls).X ⊆ Ls := by
  intro z hz
  simp only [Schema.restrictLabels, Finset.mem_union, Finset.mem_inter] at hz
  rcases hz with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h

/-- `restrictLabels Ls` is itself `DClosed` (w.r.t. its own `Y ∪ X`, which
is `Ls` when `Ls ⊆ Y ∪ X`), given `S` is `D_S`-closed on `Ls` — the general
analogue of `Schema.stratRestrict_DClosed`, built the same way (via the two
cheap `rfl`/set-equality bridging lemmas above) to avoid the same `whnf`
blow-up passing `hLsClosed` directly would cause (see `Schema.stratRestrict_
DClosed`'s docstring, `ShexLean/Shex2025Inheritance/Proposition1.lean`). -/
theorem Schema.restrictLabels_DClosed {S : Schema} {Ls : Finset ShapeLabel}
    (hLsClosed : S.DClosedOn Ls) (hLsYX : Ls ⊆ S.Y ∪ S.X) :
    (S.restrictLabels Ls).DClosedOn ((S.restrictLabels Ls).Y ∪ (S.restrictLabels Ls).X) := by
  rw [Schema.restrictLabels_YX_eq hLsYX]
  intro z hz z' hedge
  rw [Schema.restrictLabels_DEdge_eq] at hedge
  exact hLsClosed z hz z' hedge

theorem Schema.univTyping_mono {S : Schema} {G : Graph} {Ls Ls' : Finset ShapeLabel}
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

/-! ### `.anc`/`.desc` are unaffected by restricting to a `D_S`-closed set

Generalizes `Schema.stratRestrict_anc_eq` (which used `Stratification.
le_of_path`, specific to a stratum) via the more fundamental fact
underlying it: `D_S`-closure of `Ls` already confines everything `H_S`
reaches from a member of `Ls`, in *both* directions (`dep-extends` is
symmetric, Definition 5), since it's folded into `D_S` at all. -/

/-- `S.anc x ⊆ Ls` whenever `x ∈ Ls` and `Ls` is `D_S`-closed — direct
corollary of `Schema.ancSet_subset` at `xs = {x}`. -/
theorem Schema.anc_subset_of_DClosedOn {S : Schema} {Ls : Finset ShapeLabel} (hLs : S.DClosedOn Ls)
    {x : ShapeLabel} (hx : x ∈ Ls) : S.anc x ⊆ Ls := by
  have h := S.ancSet_subset hLs (xs := {x}) (Finset.singleton_subset_iff.mpr hx)
  simpa [Schema.ancSet, Finset.singleton_biUnion] using h

/-- Reversing a `ReflTransGen` path along a symmetric relation. -/
private theorem reflTransGen_reverse_of_symm {α : Type*} {r : α → α → Prop}
    (hsymm : ∀ a b, r a b → r b a) {x y : α} (h : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih => exact Relation.ReflTransGen.head (hsymm _ _ hstep) ih

/-- `S.desc L ⊆ Ls` whenever `L ∈ Ls` and `Ls` is `D_S`-closed — the
"descendant" direction dual of `Schema.anc_subset_of_DClosedOn`, needing
the reversal above since `Schema.desc`'s own reachability runs the opposite
way along `extEdge`, but `dep-extends` (hence `D_S`) doesn't care about
direction. -/
theorem Schema.desc_subset_of_DClosedOn {S : Schema} {Ls : Finset ShapeLabel} (hLs : S.DClosedOn Ls)
    {L : ShapeLabel} (hL : L ∈ Ls) : S.desc L ⊆ Ls := by
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

/-- `(S.restrictLabels Ls).anc x = S.anc x` for `x` confined to a
`D_S`-closed `Ls` — the general analogue of `Schema.stratRestrict_anc_eq`. -/
theorem Schema.restrictLabels_anc_eq {S : Schema} {Ls : Finset ShapeLabel} (hLsClosed : S.DClosedOn Ls)
    {x : ShapeLabel} (hxLs : x ∈ Ls) : (S.restrictLabels Ls).anc x = S.anc x := by
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

/-- `(S.restrictLabels Ls).desc L = S.desc L` for `L` confined to a
`D_S`-closed `Ls` — the dual of `Schema.restrictLabels_anc_eq`. -/
theorem Schema.restrictLabels_desc_eq {S : Schema} {Ls : Finset ShapeLabel} (hLsClosed : S.DClosedOn Ls)
    {L : ShapeLabel} (hLLs : L ∈ Ls) : (S.restrictLabels Ls).desc L = S.desc L := by
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

/-- **The general schema-invariance fact** underlying this whole file:
`Satisfies` against `restrictLabels Ls1` agrees with `Satisfies` against
any bigger `D_S`-closed `restrictLabels Ls2 ⊇ Ls1`, for a label confined to
`Ls1` — the general (arbitrary-`D_S`-closed-set) analogue of
`Satisfies_stratRestrict_agree`, built the identical way (`stableFuel` +
`schemaAgreeFuel`), just with `Schema.restrictLabels_anc_eq` in place of
the stratum-specific `Schema.stratRestrict_anc_eq`. -/
theorem Satisfies_restrictLabels_agree {S : Schema} (hWFX : S.WellFormedX)
    (hWFExt : S.WellFormedExtends) {Ls1 Ls2 : Finset ShapeLabel} (hLs1Ls2 : Ls1 ⊆ Ls2)
    (hLs1Closed : S.DClosedOn Ls1) (hLs2Closed : S.DClosedOn Ls2)
    {x : ShapeLabel} (hxLs1 : x ∈ Ls1) {G : Graph} {τ : Typing} {n : RDFNode} :
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

/-- A correct typing of `restrictLabels Ls2` restricts down to a correct
typing of `restrictLabels Ls1`, for any `D_S`-closed `Ls1 ⊆ Ls2` — 2025's
analogue of 2017's `restrictLabels_correct_restrictTo`, combining a
τ-restriction step (`Satisfies.agree`, already schema-generic in
`Proposition1.lean`) with a *schema*-restriction step
(`Satisfies_restrictLabels_agree`, new to this file) — 2017 only ever
needed the former, since `Satisfies` there never consults the schema. The
abstract-label case additionally needs `Schema.desc_subset_of_DClosedOn`:
the witnessing descendant is automatically confined to `Ls1` too, since
`Ls1`'s `D_S`-closure already captures every `H_S`-neighbour of `L`
(`dep-extends` being symmetric), not just its ordinary `dep`-references. -/
theorem restrictLabels_correct_restrictTo {S : Schema} (hWFX : S.WellFormedX)
    (hWFExt : S.WellFormedExtends) {G : Graph} {Ls1 Ls2 : Finset ShapeLabel} {t : Typing}
    (hLs1Ls2 : Ls1 ⊆ Ls2) (hLs1Closed : S.DClosedOn Ls1) (hLs2Closed : S.DClosedOn Ls2)
    (ht : (S.restrictLabels Ls2).CorrectTyping G t) :
    (S.restrictLabels Ls1).CorrectTyping G (restrictTyping t Ls1) := by
  intro n L hmem
  obtain ⟨hmemT, hL1⟩ := mem_restrictTyping.mp hmem
  have hcorrectL := ht n L hmemT
  have hAiff : L ∈ (S.restrictLabels Ls1).A ↔ L ∈ (S.restrictLabels Ls2).A := by
    simp only [Schema.restrictLabels, Finset.mem_inter]
    exact ⟨fun ⟨hLA, _⟩ => ⟨hLA, hLs1Ls2 hL1⟩, fun ⟨hLA, _⟩ => ⟨hLA, hL1⟩⟩
  have hagree1 : ∀ n' L', L' ∈ Ls1 → ((n', L') ∈ t ↔ (n', L') ∈ restrictTyping t Ls1) := by
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

/-- Restricting to `Lo2 ⊆ Lo1` and then to `Lo2` again is the same as
restricting to `Lo2` directly — 2025's analogue of 2017's `Typing.
restrictTo_restrictTo`. -/
theorem restrictTyping_restrictTyping {t : Typing} {Lo1 Lo2 : Finset ShapeLabel}
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
`restrictLabels Ls2` for any `Ls1 ⊆ Ls2` (both `D_S`-closed) — the general
(arbitrary-set) analogue of `Schema.correctTyping_stratRestrict_mono`.
Unlike `restrictLabels_correct_restrictTo` (which also shrinks the
*typing*, dropping data), this keeps `t` exactly as given — only the
ambient schema grows, and (as in `correctTyping_stratRestrict_mono`) every
`.A`/`.desc` witness confined to `Ls1` trivially stays confined to the
bigger `Ls2` too, by plain monotonicity of the intersection-based
`restrictLabels`. -/
theorem Schema.correctTyping_restrictLabels_mono {S : Schema} (hWFX : S.WellFormedX)
    (hWFExt : S.WellFormedExtends) {Ls1 Ls2 : Finset ShapeLabel} (hLs1Ls2 : Ls1 ⊆ Ls2)
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

/-- **Fusion**: revealing `Ls2` in one shot (`Lo = Ls`) agrees with
revealing it in two stages through an intermediate checkpoint `Ls1`
(`Lo = Ls2` then `Lo = Ls1`) — batching more or less finely doesn't change
`maxTypingAgreeing`'s outcome, provided everything new in `Ls2` only
`D_S`-negatively-depends on the original `Ls`, and `Ls1` is `D_S`-closed on
its own positive dependencies. 2025 analogue of 2017's `maxTypingAgreeing_
fusion` (`ShexLean/Shex2017Schemas/Lemma2.lean`); the proof is essentially the same
mutual-inclusion argument (each side is, as a *whole object*, a valid
candidate for the other's `maxTypingAgreeing`), just threading the four
well-formedness hypotheses `maxTypingAgreeing_correct`/`restrictLabels_
correct_restrictTo` need throughout, and using `S.DEdge`/`S.DNegEdge`
membership in place of 2017's `posDeps`/`negDeps` set-containment. -/
theorem maxTypingAgreeing_fusion {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree)
    {G : Graph} {Ls Ls1 Ls2 : Finset ShapeLabel} {T : Typing}
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

/-- `maxTypingAgreeing` is a no-op when asked to reveal exactly the schema
`fixed` is already correct+bounded for: the only self-agreeing candidate is
`fixed` itself. -/
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

Same strategy as 2017's own `ShexLean/Shex2017Schemas/Lemma2.lean`: rather than trying to
align an *arbitrary* second stratification's checkpoints with a fixed
combination of the first (mathematically impossible in general — two
mutually `D_S`-independent labels can be ordered oppositely by different
valid stratifications), define one canonical, schedule-agnostic process
(`cont1`) that reveals *some* valid next batch at each step, show its
result doesn't depend on which valid batch was chosen (`cont1_indep`, via
`maxTypingAgreeing_swap`), then walk it through each stratification's own
checkpoints separately to show it equals `Typing8` for *both*.
-/

/-- The labels of least `strat`-value among those not yet in `Fixed` — a
canonical (but not the only valid) choice of "next batch". -/
def remainingMin (S : Schema) (strat : ShapeLabel → ℕ) (Fixed : Finset ShapeLabel) :
    Finset ShapeLabel :=
  ((S.Y ∪ S.X) \ Fixed).filter (fun L => ∀ L' ∈ (S.Y ∪ S.X) \ Fixed, strat L ≤ strat L')

theorem remainingMin_subset {S : Schema} {strat : ShapeLabel → ℕ} {Fixed : Finset ShapeLabel} :
    remainingMin S strat Fixed ⊆ (S.Y ∪ S.X) \ Fixed := Finset.filter_subset _ _

theorem remainingMin_nonempty {S : Schema} {strat : ShapeLabel → ℕ} {Fixed : Finset ShapeLabel}
    (h : ((S.Y ∪ S.X) \ Fixed).Nonempty) : (remainingMin S strat Fixed).Nonempty := by
  obtain ⟨L₀, hL₀, hmin⟩ := Finset.exists_min_image ((S.Y ∪ S.X) \ Fixed) strat h
  exact ⟨L₀, Finset.mem_filter.mpr ⟨hL₀, hmin⟩⟩

/-- `remainingMin`'s batch (for any valid stratification `strat`) only
`D_S`-negatively depends on `Fixed`. -/
theorem remainingMin_neg {S : Schema} (strat : Stratification S) (hDClosed : S.DClosed)
    (Fixed : Finset ShapeLabel) :
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

/-- `Fixed ∪ remainingMin strat Fixed` is self-contained under `D_S`. -/
theorem remainingMin_pos {S : Schema} (strat : Stratification S) (hDClosed : S.DClosed)
    (Fixed : Finset ShapeLabel) :
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

/-- Repeatedly reveal `strat`'s `remainingMin` batch, `n` times (or until
nothing is left — `n` is fuel, not meant to be tight). -/
noncomputable def cont1Fuel (S : Schema) (strat : Stratification S) (G : Graph) :
    ℕ → Finset ShapeLabel → Typing → Typing
  | 0, _, T => T
  | (n + 1), Fixed, T =>
      if ((S.Y ∪ S.X) \ Fixed).Nonempty then
        cont1Fuel S strat G n (Fixed ∪ remainingMin S strat.strat Fixed)
          (maxTypingAgreeing (S.restrictLabels (Fixed ∪ remainingMin S strat.strat Fixed)) G
            Fixed T)
      else T

private theorem remainingMin_card_lt (S : Schema) (strat : ShapeLabel → ℕ)
    {Fixed : Finset ShapeLabel} (h : ((S.Y ∪ S.X) \ Fixed).Nonempty) :
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
    {Fixed : Finset ShapeLabel} (h : ¬ ((S.Y ∪ S.X) \ Fixed).Nonempty) (T : Typing) :
    ∀ n, cont1Fuel S strat G n Fixed T = T
  | 0 => rfl
  | (n + 1) => by simp only [cont1Fuel, ite_eq_right h]

/-- Once fuel is enough to exhaust the remaining labels, more fuel doesn't
change the result. -/
theorem cont1Fuel_stable (S : Schema) (strat : Stratification S) (G : Graph) :
    ∀ Fixed : Finset ShapeLabel, ∀ T : Typing, ∀ n n' : ℕ, ((S.Y ∪ S.X) \ Fixed).card ≤ n →
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
`(Fixed, T)` all the way to `S.Y ∪ S.X`, using `strat` throughout to choose
each batch (a fixed, concrete choice — but `cont1_indep` below shows *any*
valid first step gives the same final answer). -/
noncomputable def cont1 (S : Schema) (strat : Stratification S) (G : Graph)
    (Fixed : Finset ShapeLabel) (T : Typing) : Typing :=
  cont1Fuel S strat G (S.Y ∪ S.X).card Fixed T

theorem cont1_eq_fuel (S : Schema) (strat : Stratification S) (G : Graph)
    (Fixed : Finset ShapeLabel) (T : Typing) (n : ℕ) (hn : ((S.Y ∪ S.X) \ Fixed).card ≤ n) :
    cont1 S strat G Fixed T = cont1Fuel S strat G n Fixed T :=
  cont1Fuel_stable S strat G Fixed T (S.Y ∪ S.X).card n (Finset.card_le_card Finset.sdiff_subset) hn

theorem cont1_done (S : Schema) (strat : Stratification S) (G : Graph)
    {Fixed : Finset ShapeLabel} (h : ¬ ((S.Y ∪ S.X) \ Fixed).Nonempty) (T : Typing) :
    cont1 S strat G Fixed T = T := by
  have hcardzero : ((S.Y ∪ S.X) \ Fixed).card = 0 := by
    rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]; exact h
  rw [cont1_eq_fuel S strat G Fixed T 1 (by omega)]
  simp only [cont1Fuel, ite_eq_right h]

theorem cont1_step (S : Schema) (strat : Stratification S) (G : Graph)
    {Fixed : Finset ShapeLabel} (h : ((S.Y ∪ S.X) \ Fixed).Nonempty) (T : Typing) :
    cont1 S strat G Fixed T = cont1 S strat G (Fixed ∪ remainingMin S strat.strat Fixed)
      (maxTypingAgreeing (S.restrictLabels (Fixed ∪ remainingMin S strat.strat Fixed)) G Fixed T) := by
  obtain ⟨m, hm⟩ : ∃ m, ((S.Y ∪ S.X) \ Fixed).card = m + 1 :=
    ⟨((S.Y ∪ S.X) \ Fixed).card - 1, by have := Finset.card_pos.mpr h; omega⟩
  rw [cont1_eq_fuel S strat G Fixed T (m + 1) (le_of_eq hm)]
  simp only [cont1Fuel, ite_eq_left h]
  refine (cont1_eq_fuel S strat G _ _ m ?_).symm
  have := remainingMin_card_lt S strat.strat h
  omega

/-- **Swap**: two batches `A`, `B` that *each individually* only depend
(negatively) on the common base `Ls0` and are themselves `D_S`-closed
together with it, can be revealed in either order with the same result —
both sides reduce, via `maxTypingAgreeing_fusion`, to the one-shot
construction over `Ls0 ∪ A ∪ B`. This is the formal content of "reordering
independent material doesn't change the final typing", used below
(`cont1_indep`) to show `cont1`'s first step doesn't matter. -/
theorem maxTypingAgreeing_swap {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree)
    {G : Graph} {Ls0 A B : Finset ShapeLabel} {T : Typing}
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

/-- **Independence**: `cont1`'s final answer, starting from a `D_S`-closed
`(Fixed, T)`, doesn't change if we first jump ahead by revealing *any*
other valid batch `C` (not necessarily `remainingMin`'s own choice, and not
necessarily disjoint from `Fixed`) — i.e. `cont1` doesn't actually care
which valid batch its underlying `strat` happens to pick at each step. -/
theorem cont1_indep {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat : Stratification S) (G : Graph) :
    ∀ Fixed : Finset ShapeLabel, ∀ T : Typing,
      Fixed ⊆ S.Y ∪ S.X → S.DClosedOn Fixed →
      T ⊆ (S.restrictLabels Fixed).univTyping G →
      (S.restrictLabels Fixed).CorrectTyping G T →
      ∀ C : Finset ShapeLabel, C ⊆ S.Y ∪ S.X →
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
        -- First `ih` application: base `Fixed ∪ A₁`, jump `C`.
        have hstep1 := ih _ hcardA₁ (Fixed ∪ A₁) rfl
          (maxTypingAgreeing (S.restrictLabels (Fixed ∪ A₁)) G Fixed T) hFA₁YX hFA₁Closed
          hTA₁sub hTA₁correct
          C hCsub (fun z hz => (hCneg z hz).trans Finset.subset_union_left)
          (fun z hz z' hz' => by
            rcases Finset.mem_union.mp (hCpos z hz z' hz') with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
            · exact Finset.mem_union_right _ h)
        -- `Fixed ∪ C` is `D_S`-closed and confined to `Y ∪ X`, and `T''` is
        -- correct+bounded for it.
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
        -- Second `ih` application: base `Fixed ∪ C`, jump `A₁`.
        have hstep2 := ih _ hcardC (Fixed ∪ C) rfl T'' hFCYX hFCClosed hT''sub hT''correct
          A₁ hA₁sub (fun z hz => (hA₁negRefs z hz).trans Finset.subset_union_left)
          (fun z hz z' hz' => by
            rcases Finset.mem_union.mp (hA₁pos z hz z' hz') with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
            · exact Finset.mem_union_right _ h)
        -- Combine via `cont1_step` and `maxTypingAgreeing_swap`.
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

/-! ### Chaining `cont1_indep` along a stratification's own checkpoints -/

theorem Schema.stratum_zero (S : Schema) (strat : Stratification S) :
    S.stratum strat.strat 0 = ∅ := by
  unfold Schema.stratum
  rw [Finset.filter_eq_empty_iff]
  intro z hz hle
  have := (strat.mem_range z hz).1
  omega

/-- Sharper than `Schema.stratum_DClosedOn` on the negative side: a label's
negative dependencies land strictly *inside the previous* checkpoint, not
just inside its own — 2025's analogue of 2017's `Schema.stratum_neg_confined`. -/
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
build the identical schema (`rfl`-close, but not literally `rfl` since
`stratRestrict`'s per-field filters and `restrictLabels`'s intersections
are different `Finset` expressions) — bridges `stratTypingSeq_correct`
(`ShexLean/Shex2025Inheritance/Proposition1.lean`, `stratRestrict`-based) into the
`restrictLabels`-based vocabulary this file's general machinery needs,
matching 2017's own `Schema.stratRestrict_eq_restrictLabels`
(`ShexLean/Shex2017Schemas/Algorithm1.lean`). -/
theorem Schema.stratRestrict_eq_restrictLabels (S : Schema) (strat : ShapeLabel → ℕ) (i : ℕ) :
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

/-- Chain `cont1_indep` along `strat'`'s own checkpoints: `cont1`, built
using *any* fixed `strat0` internally, agrees with `strat'` at every one of
`strat'`'s own checkpoints — regardless of `strat0`. -/
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

/-- `cont1 S strat0 G ∅ ∅` equals `Typing8` for *any* valid stratification —
so, in particular, for both `strat1` and `strat2`. -/
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

/-- **Lemma 2.** `τ_max(S,σ,G)` (Definition 8) does not depend on which
stratification `σ` of `S` is chosen: both sides equal `cont1 S strat1 G ∅
∅`, a canonical process built by always revealing every "ready" label
(`remainingMin`) — independent of which valid stratification is used to
justify each step (`cont1_indep`). -/
theorem lemma2 {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat1 strat2 : Stratification S) (G : Graph) :
    Typing8 G S strat1 = Typing8 G S strat2 := by
  rw [← cont1_eq_Typing8 hWFX hWFExt hWFExtra hNEF hDClosed strat1 G strat1,
    ← cont1_eq_Typing8 hWFX hWFExt hWFExtra hNEF hDClosed strat1 G strat2]

end ShexLean.InheritanceDisjunction
