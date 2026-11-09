import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2025Inheritance.Stratification
import ShexLean.Shex2025Inheritance.Render
import Mathlib.Tactic.FinCases
import Example

/-!
Example 1 from the 2025 paper "Shape Expressions with Inheritance" (§3,
Def. 2): the full motivating schema `S₁` of §2. This is the
multiple-inheritance chain of `ColouredCircle`: `Coord`, `Attribute`,
`Colour`, the abstract `Figure`, `Circle`, `Radius`, `ColouredFigure` and
`ColouredCircle` (Fig. 1). It is applied to the graph of Fig. 2 (nodes
`f1`, `f2`, `a1`, `a2`, `a3`, `c1` and `c2`).

This file proves the main claims of the paper:

* `c1` and `c2` satisfy `Coord`.
* `a1`, `a2` and `a3` satisfy `Attribute`.
* `a2` satisfies `Colour`.
* `a1` and `a3` satisfy `Radius`.
* `f2` is a `Circle`.
* The multiple-inheritance case: `f1` is a `ColouredCircle`. (The `H_S`
  of Fig. 3 gives `anc({Circle,ColouredFigure}) = {Circle, Figure,
  ColouredFigure}`. `Figure` is counted one time, although it comes
  through the two parents.)

This file proves the ancestor facts of the extension hierarchy `H_{S1}`
(`hancCircle`, `hancColouredFigure` and `hancSetCircleColouredFigure`;
the subject of Example 2, Fig. 3). They are not in `Example2_...lean`,
because `f1_satisfies_ColouredCircle` (the main claim of this file) needs
`hancSetCircleColouredFigure` to state its rule-18 partition.
`Example2_extension_hierarchy.lean` imports this file and only shows the
same facts again.
-/

namespace ShexLean.Inheritance

/-- A fuel bound that is sufficient for all the proofs in this file. -/
def bigFuel1 : ℕ := 10

/-- `T_float`, approximated as "any integer literal", because `Literal`
has no float constructor. -/
def cFloat : NodeConstraint
  | .lit (.int _) => True
  | _ => False

/-- `T_str` for Fig. 1: the node is a string literal. -/
def cStrFig1 : NodeConstraint
  | .lit (.str _) => True
  | _ => False

/-- `T_"colour"`: the literal string `"colour"`. -/
def cColourLit : NodeConstraint
  | .lit (.str s) => s = "colour"
  | _ => False

/-- `T_"radius"`: the literal string `"radius"`. -/
def cRadiusLit : NodeConstraint
  | .lit (.str s) => s = "radius"
  | _ => False

/-- The schema of Fig. 1:

* `Coord` is a `Y` label (a plain shape, with no `extends`).
* `Attribute`, `Colour`, `Figure`, `Circle`, `Radius`, `ColouredFigure`
  and `ColouredCircle` are `X` labels.
* `Figure` is `abstract` (`A = {Figure}`).

`A` has no role in the fuel-bounded `Satisfies*` relations. Only the
correct-typing definition (Definition 4, `Schema.CorrectTyping`) uses it.
This file does not use that definition. -/
def S_fig1 : Schema where
  Y := {"Coord", "T_str", "T_any", "T_float", "T_colour", "T_radius"}
  X := {"Attribute", "Colour", "Figure", "Circle", "Radius", "ColouredFigure", "ColouredCircle"}
  A := {"Figure"}
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "Coord" => .ofShape ⟨false, none, .seq (.tc "x" "T_float") (.tc "y" "T_float")⟩
    | "T_str" => .constraint cStrFig1
    | "T_any" => .constraint (fun _ => True)
    | "T_float" => .constraint cFloat
    | "T_colour" => .constraint cColourLit
    | "T_radius" => .constraint cRadiusLit
    | "Attribute" =>
        .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩
    | "Colour" =>
        .and (.extends {"Attribute"} ⟨false, none, .tc "scope" "T_str"⟩)
          (.ofShape ⟨false, none, .tc "name" "T_colour"⟩)
    | "Figure" => .extends ∅ ⟨false, none, .tc "coord" "Coord"⟩
    | "Circle" => .extends {"Figure"} ⟨false, none, .tc "attr" "Radius"⟩
    | "Radius" =>
        .and (.extends {"Attribute"} ⟨false, none, .empty⟩)
          (.ofShape ⟨false, none, .seq (.tc "name" "T_radius") (.tc "value" "T_float")⟩)
    | "ColouredFigure" => .extends {"Figure"} ⟨false, none, .tc "attr" "Colour"⟩
    | "ColouredCircle" => .extends {"Circle", "ColouredFigure"} ⟨false, none, .empty⟩
    | _ => .constraint (fun _ => False)

/-- The graph nodes of Fig. 2. -/
def a1 : Subject := .iri "a1"
def a2 : Subject := .iri "a2"
def a3 : Subject := .iri "a3"
def c1 : Subject := .iri "c1"
def c2 : Subject := .iri "c2"
def f1 : Subject := .iri "f1"
def f2 : Subject := .iri "f2"

/-- The graph of Fig. 2. The coordinates and the `value`s are approximated
as integer literals: `10.1` of `a1` ↦ `10`, `7.2` of `a3` ↦ `7`,
`(2.0, 4.0)` of `c1` ↦ `(2, 4)`, and `(0.2, -2.3)` of `c2` ↦ `(0, -2)`.

`f1` has two `attr` triples (to `a1`, the `Radius`, and to `a2`, the
`Colour`) and one `coord` triple. These are the three parts that the
rule-18 partition of `ColouredCircle` over
`{Circle, Figure, ColouredFigure}` needs. -/
def G_fig1 : Graph :=
  { ⟨a1, "name", .lit (.str "radius")⟩, ⟨a1, "value", .lit (.int 10)⟩,
    ⟨a2, "scope", .lit (.str "fill")⟩, ⟨a2, "name", .lit (.str "colour")⟩,
    ⟨a2, "value", .lit (.str "#ff0000")⟩,
    ⟨a3, "name", .lit (.str "radius")⟩, ⟨a3, "value", .lit (.int 7)⟩,
    ⟨c1, "x", .lit (.int 2)⟩, ⟨c1, "y", .lit (.int 4)⟩,
    ⟨c2, "x", .lit (.int 0)⟩, ⟨c2, "y", .lit (.int (-2))⟩,
    ⟨f1, "attr", a1⟩, ⟨f1, "attr", a2⟩, ⟨f1, "coord", c1⟩,
    ⟨f2, "attr", a3⟩, ⟨f2, "coord", c2⟩ }

/-- A typing that is the witness of each `p @z` lookup that the claims
below need. The `τ.has` lookups are given directly. This file does not
prove that `τ` is a correct typing (Definition 4, which connects `τ` to
the truth values of the node constraints).

It contains the literal triple-constraint types of the nodes (`T_str`,
`T_any`, `T_float`, `T_"colour"` and `T_"radius"`). It also contains, for
`a1`, `a2`, `a3`, `c1` and `c2`, the shape-reference types (`Radius`,
`Colour` and `Coord`) that the `attr` and `coord` triple constraints of
`f1` and `f2` look up. -/
def τ_fig1 : Typing :=
  { (RDFNode.lit (.str "radius"), "T_str"), (RDFNode.lit (.str "radius"), "T_radius"),
    (RDFNode.lit (.int 10), "T_any"), (RDFNode.lit (.int 10), "T_float"),
    (RDFNode.lit (.int 7), "T_any"), (RDFNode.lit (.int 7), "T_float"),
    (RDFNode.lit (.str "fill"), "T_str"),
    (RDFNode.lit (.str "colour"), "T_str"), (RDFNode.lit (.str "colour"), "T_colour"),
    (RDFNode.lit (.str "#ff0000"), "T_any"),
    (RDFNode.lit (.int 2), "T_float"), (RDFNode.lit (.int 4), "T_float"),
    (RDFNode.lit (.int 0), "T_float"), (RDFNode.lit (.int (-2)), "T_float"),
    ((a1 : RDFNode), "Radius"), ((a2 : RDFNode), "Colour"), ((c1 : RDFNode), "Coord"),
    ((a3 : RDFNode), "Radius"), ((c2 : RDFNode), "Coord") }

/-! Helpers for the claims below:

* Reachability in `H_S` for "root" extendable labels (with no outgoing
  edges) and for extendable labels with a "single parent".
* Satisfaction facts for rule 17 (`.ofShape`), for the small
  triple-expression shapes of Fig. 1 (`⟨ε⟩`, a plain `p @z`, and a plain
  `p1 @z1 ; p2 @z2`).

Each helper permits "junk" triples with a different predicate, because no
shape of Fig. 1 is `closed`. -/

theorem reach_root {S : Schema} {p : Label} (hparent : ∀ c, ¬ S.extEdge p c) :
    ∀ x', Relation.ReflTransGen S.extEdge p x' → x' = p := by
  intro x' h
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
  · exact heq.symm
  · exact absurd hc (hparent c)

theorem anc_root {S : Schema} {x : Label} (hx : x ∈ S.X)
    (hedge : ∀ c, ¬ S.extEdge x c) : S.anc x = {x} := by
  apply Finset.ext; intro x'
  unfold Schema.anc
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩; exact reach_root hedge x' h
  · rintro rfl; exact ⟨hx, Relation.ReflTransGen.refl⟩

theorem anc_one_parent {S : Schema} {x p : Label} (hx : x ∈ S.X) (hp : p ∈ S.X)
    (hedge : ∀ c, S.extEdge x c ↔ c = p) (hparent : ∀ c, ¬ S.extEdge p c) :
    S.anc x = {x, p} := by
  apply Finset.ext; intro x'
  unfold Schema.anc
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, hc'⟩
    · exact Or.inl heq.symm
    · have hceq : c = p := (hedge c).mp hc
      exact Or.inr (hceq ▸ reach_root hparent x' (hceq ▸ hc'))
  · rintro (heq | heq)
    · rw [heq]; exact ⟨hx, Relation.ReflTransGen.refl⟩
    · rw [heq]; exact ⟨hp, Relation.ReflTransGen.single ((hedge p).mpr rfl)⟩

/-- The empty set satisfies the trivial shape `[ε]`, which is not closed
and has no `extra` (rule 17 of Table 3). We use it at each location where
the `M'` part of an `extends X ⟨ε⟩` is empty (`Radius` and
`ColouredCircle`, which both use a plain `⟨ε⟩` as their shape). -/
theorem empty_satisfies_emptyShape {τ : Typing} :
    SatisfiesShape τ (∅ : Finset Triple)
      ⟨false, none, .empty⟩ := by
  have hMeEmpty : Me τ (∅ : Finset Triple) TripleExpr.empty = ∅ := by unfold Me; simp
  refine ⟨?_, ?_, fun h => absurd h (by decide)⟩
  · show SatisfiesE τ (Me τ (∅ : Finset Triple) TripleExpr.empty) TripleExpr.empty
    rw [hMeEmpty]; rfl
  · show props (Mnotin τ (∅ : Finset Triple) TripleExpr.empty) ⊆ (∅ : Finset IRI)
    unfold Mnotin
    simp [props, TripleExpr.props, TripleExpr.tcs]

/-- `insert t junk, τ ⊨ [false,none]⟨p @z⟩` (rule 17 of Table 3), if `t` is
the only triple with the predicate `p`, and all the predicates of `junk`
are different from `p`. We use it for the restriction `name @T_"colour"`
of `Colour`, applied to the full neighbourhood of `a2` (which also has
`scope` and `value` triples). -/
theorem single_tc_ofShape_junk {τ : Typing}
    {p : IRI} {z : Label} {t : Triple} {junk : Finset Triple}
    (hp : t.pred = p) (hjunk : ∀ t' ∈ junk, t'.pred ≠ p) (hty : τ.has t.obj z) :
    SatisfiesShape τ (insert t junk)
      ⟨false, none, .tc p z⟩ := by
  have hMe : Me τ (insert t junk) (.tc p z) = {t} := by
    apply Finset.Subset.antisymm
    · intro t' ht'
      rw [mem_Me] at ht'
      obtain ⟨htM, z', hz, -⟩ := ht'
      simp only [Finset.mem_insert] at htM
      simp only [TripleExpr.tcs, Finset.mem_singleton, Prod.mk.injEq] at hz
      rcases htM with rfl | htj
      · exact Finset.mem_singleton_self _
      · exact absurd hz.1 (hjunk t' htj)
    · intro t' ht'
      simp only [Finset.mem_singleton] at ht'
      subst ht'
      rw [mem_Me]
      exact ⟨Finset.mem_insert_self _ _, z, by simp [TripleExpr.tcs, hp], hty⟩
  refine ⟨?_, ?_, by simp⟩
  · rw [hMe]; exact ⟨t.subj, t.obj, by rw [← hp], hty⟩
  · show props (Mnotin τ (insert t junk) (.tc p z)) ⊆ (∅ : Finset IRI)
    rw [Finset.subset_empty, Finset.eq_empty_iff_forall_notMem]
    intro t' ht'
    unfold props at ht'
    obtain ⟨t'', ht'', rfl⟩ := Finset.mem_image.mp ht'
    rw [mem_Mnotin, hMe] at ht''
    obtain ⟨⟨htM, hpred⟩, hnotMe⟩ := ht''
    simp only [Finset.mem_insert] at htM
    simp only [TripleExpr.props, TripleExpr.tcs, Finset.image_singleton, Finset.mem_singleton]
      at hpred
    rcases htM with rfl | htj
    · exact hnotMe (Finset.mem_singleton_self _)
    · exact (hjunk t'' htj) hpred

/-- `{t1, t2}, τ ⊨ [false,none]⟨p1 @z1 ; p2 @z2⟩` (rule 17 of Table 3), for
exactly two triples and no junk. This is the version of
`singleton_tc_ofShape` for two triple constraints. We use it for `Coord`
of Fig. 1, for `Attribute` (on the nodes `a1` and `a3`, which have no
other triples), and for the restriction
`name @T_"radius" ; value @T_float` of `Radius`. -/
theorem pair_tc_tc_ofShape {τ : Typing}
    {p1 p2 : IRI} {z1 z2 : Label} {t1 t2 : Triple}
    (hp1 : t1.pred = p1) (hp2 : t2.pred = p2) (hne : t1 ≠ t2)
    (hty1 : τ.has t1.obj z1) (hty2 : τ.has t2.obj z2) :
    SatisfiesShape τ {t1, t2}
      ⟨false, none, .seq (.tc p1 z1) (.tc p2 z2)⟩ := by
  have hMe : Me τ ({t1, t2} : Finset Triple) (.seq (.tc p1 z1) (.tc p2 z2)) = {t1, t2} := by
    apply Finset.Subset.antisymm
    · intro t ht; rw [mem_Me] at ht; exact ht.1
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [mem_Me]
      rcases ht with rfl | rfl
      · exact ⟨Finset.mem_insert_self _ _, z1, by simp [TripleExpr.tcs, hp1], hty1⟩
      · exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), z2,
          by simp [TripleExpr.tcs, hp2], hty2⟩
  refine ofShape_of_Me_eq_self hMe ⟨{t1}, {t2}, ⟨?_, ?_⟩,
    ⟨t1.subj, t1.obj, by rw [← hp1], hty1⟩, ⟨t2.subj, t2.obj, by rw [← hp2], hty2⟩⟩
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_singleton] at hx1 hx2
    exact hne (hx1.symm.trans hx2)
  · ext x; simp

/-- `insert t1 (insert t2 junk), τ ⊨ [false,none]⟨p1 @z1 ; p2 @z2⟩` (rule 17
of Table 3). This is the version of `pair_tc_tc_ofShape` that permits
junk. We use it for `a2 ⊨ Attribute`. (The neighbourhood of `a2` also has
a `scope` triple, which is not related to the `name` and `value` of
`Attribute`.) -/
theorem pair_tc_tc_ofShape_junk {τ : Typing}
    {p1 p2 : IRI} {z1 z2 : Label} {t1 t2 : Triple} {junk : Finset Triple}
    (hp1 : t1.pred = p1) (hp2 : t2.pred = p2) (hne : t1 ≠ t2)
    (hjunk : ∀ t ∈ junk, t.pred ≠ p1 ∧ t.pred ≠ p2)
    (hty1 : τ.has t1.obj z1) (hty2 : τ.has t2.obj z2) :
    SatisfiesShape τ (insert t1 (insert t2 junk))
      ⟨false, none, .seq (.tc p1 z1) (.tc p2 z2)⟩ := by
  have hMe : Me τ (insert t1 (insert t2 junk)) (.seq (.tc p1 z1) (.tc p2 z2)) = {t1, t2} := by
    apply Finset.Subset.antisymm
    · intro t ht
      rw [mem_Me] at ht
      obtain ⟨htM, z, hz, -⟩ := ht
      simp only [Finset.mem_insert] at htM
      simp only [TripleExpr.tcs, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hz
      rcases htM with rfl | rfl | htj
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exfalso
        rcases hz with ⟨hzp, -⟩ | ⟨hzp, -⟩
        · exact (hjunk t htj).1 hzp
        · exact (hjunk t htj).2 hzp
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [mem_Me]
      rcases ht with rfl | rfl
      · exact ⟨Finset.mem_insert_self _ _, z1, by simp [TripleExpr.tcs, hp1], hty1⟩
      · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), z2,
          by simp [TripleExpr.tcs, hp2], hty2⟩
  refine ⟨?_, ?_, by simp⟩
  · rw [hMe]
    refine ⟨{t1}, {t2}, ⟨?_, ?_⟩, ⟨t1.subj, t1.obj, by rw [← hp1], hty1⟩,
      ⟨t2.subj, t2.obj, by rw [← hp2], hty2⟩⟩
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_singleton] at hx1 hx2
      exact hne (hx1.symm.trans hx2)
    · ext x; simp
  · show props (Mnotin τ (insert t1 (insert t2 junk)) (.seq (.tc p1 z1) (.tc p2 z2)))
      ⊆ (∅ : Finset IRI)
    rw [Finset.subset_empty, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    unfold props at ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    rw [mem_Mnotin, hMe] at ht'
    obtain ⟨⟨htM, hpred⟩, hnotMe⟩ := ht'
    simp only [Finset.mem_insert] at htM
    simp only [TripleExpr.props, TripleExpr.tcs, Finset.image_union, Finset.image_singleton,
      Finset.mem_union, Finset.mem_singleton] at hpred
    rcases htM with rfl | rfl | htj
    · exact hnotMe (Finset.mem_insert_self _ _)
    · exact hnotMe (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · rcases hpred with hp | hp
      · exact (hjunk t' htj).1 hp
      · exact (hjunk t' htj).2 hp

/-! The edges of `H_S` (Fig. 3) between the `X` labels below. This is the
subject of Example 2 (`Example2_extension_hierarchy.lean`), but the
rule-18 partition of `f1_satisfies_ColouredCircle` needs it here. -/

theorem hAttributeEdge : ∀ c, ¬ S_fig1.extEdge "Attribute" c := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  intro c hc; unfold Schema.extEdge at hc; rw [hshape] at hc
  simp [ShapeExpr.extendsTargets] at hc

theorem hFigureEdge : ∀ c, ¬ S_fig1.extEdge "Figure" c := by
  have hshape : S_fig1.shapeDef "Figure" = .extends ∅ ⟨false, none, .tc "coord" "Coord"⟩ := rfl
  intro c hc; unfold Schema.extEdge at hc; rw [hshape] at hc
  simp [ShapeExpr.extendsTargets] at hc

theorem hCircleEdge : ∀ c, S_fig1.extEdge "Circle" c ↔ c = "Figure" := by
  have hshape : S_fig1.shapeDef "Circle" =
      .extends {"Figure"} ⟨false, none, .tc "attr" "Radius"⟩ := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem hColouredFigureEdge : ∀ c, S_fig1.extEdge "ColouredFigure" c ↔ c = "Figure" := by
  have hshape : S_fig1.shapeDef "ColouredFigure" =
      .extends {"Figure"} ⟨false, none, .tc "attr" "Colour"⟩ := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem hColourEdge : ∀ c, S_fig1.extEdge "Colour" c ↔ c = "Attribute" := by
  have hshape : S_fig1.shapeDef "Colour" =
      .and (.extends {"Attribute"} ⟨false, none, .tc "scope" "T_str"⟩)
        (.ofShape ⟨false, none, .tc "name" "T_colour"⟩) := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem hRadiusEdge : ∀ c, S_fig1.extEdge "Radius" c ↔ c = "Attribute" := by
  have hshape : S_fig1.shapeDef "Radius" =
      .and (.extends {"Attribute"} ⟨false, none, .empty⟩)
        (.ofShape ⟨false, none, .seq (.tc "name" "T_radius") (.tc "value" "T_float")⟩) := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem hancAttribute : S_fig1.anc "Attribute" = {"Attribute"} := anc_root (by decide) hAttributeEdge
theorem hancFigure : S_fig1.anc "Figure" = {"Figure"} := anc_root (by decide) hFigureEdge
theorem hancCircle : S_fig1.anc "Circle" = {"Circle", "Figure"} :=
  anc_one_parent (by decide) (by decide) hCircleEdge hFigureEdge
theorem hancColouredFigure : S_fig1.anc "ColouredFigure" = {"ColouredFigure", "Figure"} :=
  anc_one_parent (by decide) (by decide) hColouredFigureEdge hFigureEdge
theorem hancColour : S_fig1.anc "Colour" = {"Colour", "Attribute"} :=
  anc_one_parent (by decide) (by decide) hColourEdge hAttributeEdge
theorem hancRadius : S_fig1.anc "Radius" = {"Radius", "Attribute"} :=
  anc_one_parent (by decide) (by decide) hRadiusEdge hAttributeEdge

theorem hancSetAttribute : S_fig1.ancSet {"Attribute"} = {"Attribute"} := by
  unfold Schema.ancSet; simp [hancAttribute]
theorem hancSetFigure : S_fig1.ancSet {"Figure"} = {"Figure"} := by
  unfold Schema.ancSet; simp [hancFigure]
theorem hancSetCircleColouredFigure :
    S_fig1.ancSet {"Circle", "ColouredFigure"} = {"Circle", "Figure", "ColouredFigure"} := by
  unfold Schema.ancSet
  rw [show ({"Circle", "ColouredFigure"} : Finset Label) = insert "Circle" {"ColouredFigure"}
      from rfl, Finset.biUnion_insert, Finset.singleton_biUnion, hancCircle, hancColouredFigure]
  decide

/-- `c1, τ ⊨ Coord` (the claim of Fig. 2 "node c1 satisfies Coord").
`Coord` is a `Y` label (a plain shape with no `extends`). Thus, this is a
rule-17 check on `neigh(c1)`. -/
theorem c1_satisfies_Coord :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 c1 (S_fig1.shapeDef "Coord") := by
  have hshape : S_fig1.shapeDef "Coord" =
      .ofShape ⟨false, none, .seq (.tc "x" "T_float") (.tc "y" "T_float")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 c1) _)
  have hneigh : neigh G_fig1 c1 =
      {(⟨c1, "x", .lit (.int 2)⟩ : Triple), ⟨c1, "y", .lit (.int 4)⟩} := by decide
  rw [hneigh]
  exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `c2, τ ⊨ Coord`. -/
theorem c2_satisfies_Coord :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 c2 (S_fig1.shapeDef "Coord") := by
  have hshape : S_fig1.shapeDef "Coord" =
      .ofShape ⟨false, none, .seq (.tc "x" "T_float") (.tc "y" "T_float")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 c2) _)
  have hneigh : neigh G_fig1 c2 =
      {(⟨c2, "x", .lit (.int 0)⟩ : Triple), ⟨c2, "y", .lit (.int (-2))⟩} := by decide
  rw [hneigh]
  exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `a1, τ ⊨ Attribute` (the claim of Fig. 2 "Nodes a1, a2, a3 satisfy
`Attribute`", for `a1`). `Attribute` has no `extends` targets. Thus, the
rule-18 partition is trivial: `M' = M`, and `Mx` is vacuous over
`anc(∅) = ∅`. -/
theorem a1_satisfies_Attribute :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 a1 (S_fig1.shapeDef "Attribute") := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 a1) _)
  have hneigh : neigh G_fig1 a1 =
      {(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩} := by decide
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset Label) = ∅ := by unfold Schema.ancSet; simp
  refine ⟨{(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩},
    fun _ => ∅, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hanc]; decide
  · rw [hanc]; intro a ha; simp at ha
  · rw [hanc]; decide
  · exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)
  · rw [hanc]; intro x hx; simp at hx
  · rw [hanc]; intro x hx; simp at hx

/-- `a3, τ ⊨ Attribute`. -/
theorem a3_satisfies_Attribute :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 a3 (S_fig1.shapeDef "Attribute") := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 a3) _)
  have hneigh : neigh G_fig1 a3 =
      {(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩} := by decide
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset Label) = ∅ := by unfold Schema.ancSet; simp
  refine ⟨{(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩},
    fun _ => ∅, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hanc]; decide
  · rw [hanc]; intro a ha; simp at ha
  · rw [hanc]; decide
  · exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)
  · rw [hanc]; intro x hx; simp at hx
  · rw [hanc]; intro x hx; simp at hx

/-- `a2, τ ⊨ Attribute`. The neighbourhood of `a2` also has a `scope`
triple (which `Colour` needs, refer to `a2_satisfies_Colour`).
`Attribute` is not `closed`, so it ignores this triple as junk. -/
theorem a2_satisfies_Attribute :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 a2 (S_fig1.shapeDef "Attribute") := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 a2) _)
  have hneigh : neigh G_fig1 a2 =
      insert (⟨a2, "name", .lit (.str "colour")⟩ : Triple)
        (insert (⟨a2, "value", .lit (.str "#ff0000")⟩ : Triple) {⟨a2, "scope", .lit (.str "fill")⟩}) := by
    decide
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset Label) = ∅ := by unfold Schema.ancSet; simp
  refine ⟨insert (⟨a2, "name", .lit (.str "colour")⟩ : Triple)
      (insert (⟨a2, "value", .lit (.str "#ff0000")⟩ : Triple) {⟨a2, "scope", .lit (.str "fill")⟩}),
    fun _ => ∅, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hanc]; decide
  · rw [hanc]; intro a ha; simp at ha
  · rw [hanc]; decide
  · refine pair_tc_tc_ofShape_junk rfl rfl (by decide) ?_ (by decide) (by decide)
    intro t ht; simp only [Finset.mem_singleton] at ht; subst ht; exact ⟨by decide, by decide⟩
  · rw [hanc]; intro x hx; simp at hx
  · rw [hanc]; intro x hx; simp at hx

/-- `a2, τ ⊨ Colour` (the claim of Fig. 2 "node a2 satisfies Colour").
`Colour = extends Attribute ⟨scope @T_str⟩ and ⟨name @T_"colour"⟩`.

* The first conjunct splits `neigh(a2)` into `M' = {scope-triple}` (which
  matches `scope @T_str`) and
  `Mx(Attribute) = {name-triple, value-triple}` (which matches
  `ext-te(Attribute) = name @T_str ; value @T_any`).
* The second conjunct checks `name @T_"colour"` directly against all of
  `neigh(a2)`. For it, the `scope` and `value` triples are junk. -/
theorem a2_satisfies_Colour :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 a2 (S_fig1.shapeDef "Colour") := by
  have hshape : S_fig1.shapeDef "Colour" =
      .and (.extends {"Attribute"} ⟨false, none, .tc "scope" "T_str"⟩)
        (.ofShape ⟨false, none, .tc "name" "T_colour"⟩) := rfl
  rw [hshape]
  have hneigh : neigh G_fig1 a2 =
      insert (⟨a2, "name", .lit (.str "colour")⟩ : Triple)
        (insert (⟨a2, "scope", .lit (.str "fill")⟩ : Triple)
          {⟨a2, "value", .lit (.str "#ff0000")⟩}) := by decide
  refine ⟨?_, ?_⟩
  · refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 a2) _)
    rw [hneigh]
    refine ⟨{(⟨a2, "scope", .lit (.str "fill")⟩ : Triple)}, fun _ =>
      {(⟨a2, "name", .lit (.str "colour")⟩ : Triple), ⟨a2, "value", .lit (.str "#ff0000")⟩},
      ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hancSetAttribute]; decide
    · rw [hancSetAttribute]; intro a ha b hb hab
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · rw [hancSetAttribute]; decide
    · exact singleton_tc_ofShape (by decide)
    · rw [hancSetAttribute]
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      exact ⟨{(⟨a2, "name", .lit (.str "colour")⟩ : Triple)},
        {(⟨a2, "value", .lit (.str "#ff0000")⟩ : Triple)}, ⟨by decide, by decide⟩,
        ⟨a2, .lit (.str "colour"), rfl, by decide⟩, ⟨a2, .lit (.str "#ff0000"), rfl, by decide⟩⟩
    · rw [hancSetAttribute]
      intro x hx u hu; simp only [Finset.mem_singleton] at hx; subst hx
      have hAshape : S_fig1.shapeDef "Attribute" =
          .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
      rw [hAshape] at hu; simp [ShapeExpr.restrOf] at hu
  · refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 a2) _)
    rw [hneigh]
    refine single_tc_ofShape_junk rfl ?_ (by decide)
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide

/-- `a1, τ ⊨ Radius` (the claim of Fig. 2 "a1, a3 satisfy Radius").
`Radius = extends Attribute ⟨ε⟩ and ⟨name @T_"radius" ; value @T_float⟩`.

* The first conjunct has `M' = ∅` (`⟨ε⟩` has no constraint when it is not
  closed) and `Mx(Attribute) = neigh(a1)` (all of it, which matches
  `ext-te(Attribute)`).
* The second conjunct checks `name @T_"radius" ; value @T_float` directly
  against `neigh(a1)`. There is no junk here, because `a1` has exactly
  these two triples. -/
theorem a1_satisfies_Radius :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 a1 (S_fig1.shapeDef "Radius") := by
  have hshape : S_fig1.shapeDef "Radius" =
      .and (.extends {"Attribute"} ⟨false, none, .empty⟩)
        (.ofShape ⟨false, none, .seq (.tc "name" "T_radius") (.tc "value" "T_float")⟩) := rfl
  rw [hshape]
  have hneigh : neigh G_fig1 a1 =
      {(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩} := by decide
  refine ⟨?_, ?_⟩
  · refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 a1) _)
    rw [hneigh]
    refine ⟨∅, fun _ =>
      {(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩},
      ⟨?_, ?_, ?_⟩, empty_satisfies_emptyShape, ?_, ?_⟩
    · rw [hancSetAttribute]; decide
    · rw [hancSetAttribute]; intro a ha b hb hab
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · rw [hancSetAttribute]; simp
    · rw [hancSetAttribute]
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      exact ⟨{(⟨a1, "name", .lit (.str "radius")⟩ : Triple)}, {⟨a1, "value", .lit (.int 10)⟩},
        ⟨by decide, by decide⟩, ⟨a1, .lit (.str "radius"), rfl, by decide⟩,
        ⟨a1, .lit (.int 10), rfl, by decide⟩⟩
    · rw [hancSetAttribute]
      intro x hx u hu; simp only [Finset.mem_singleton] at hx; subst hx
      have hAshape : S_fig1.shapeDef "Attribute" =
          .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
      rw [hAshape] at hu; simp [ShapeExpr.restrOf] at hu
  · refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 a1) _)
    rw [hneigh]
    exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `a3, τ ⊨ Radius`. -/
theorem a3_satisfies_Radius :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 a3 (S_fig1.shapeDef "Radius") := by
  have hshape : S_fig1.shapeDef "Radius" =
      .and (.extends {"Attribute"} ⟨false, none, .empty⟩)
        (.ofShape ⟨false, none, .seq (.tc "name" "T_radius") (.tc "value" "T_float")⟩) := rfl
  rw [hshape]
  have hneigh : neigh G_fig1 a3 =
      {(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩} := by decide
  refine ⟨?_, ?_⟩
  · refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 a3) _)
    rw [hneigh]
    refine ⟨∅, fun _ =>
      {(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩},
      ⟨?_, ?_, ?_⟩, empty_satisfies_emptyShape, ?_, ?_⟩
    · rw [hancSetAttribute]; decide
    · rw [hancSetAttribute]; intro a ha b hb hab
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · rw [hancSetAttribute]; simp
    · rw [hancSetAttribute]
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      exact ⟨{(⟨a3, "name", .lit (.str "radius")⟩ : Triple)}, {⟨a3, "value", .lit (.int 7)⟩},
        ⟨by decide, by decide⟩, ⟨a3, .lit (.str "radius"), rfl, by decide⟩,
        ⟨a3, .lit (.int 7), rfl, by decide⟩⟩
    · rw [hancSetAttribute]
      intro x hx u hu; simp only [Finset.mem_singleton] at hx; subst hx
      have hAshape : S_fig1.shapeDef "Attribute" =
          .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
      rw [hAshape] at hu; simp [ShapeExpr.restrOf] at hu
  · refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 a3) _)
    rw [hneigh]
    exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `f2, τ ⊨ Circle` (the claim of Fig. 2 "f2 is a Circle").
`Circle = extends Figure ⟨attr @Radius⟩`.

* `M' = {(f2,attr,a3)}` matches `attr @Radius`, through the assertion
  `(a3, Radius)` of `τ`.
* `Mx(Figure) = {(f2,coord,c2)}` matches `ext-te(Figure) = coord @Coord`,
  through `(c2, Coord)`. -/
theorem f2_satisfies_Circle :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 f2 (S_fig1.shapeDef "Circle") := by
  have hshape : S_fig1.shapeDef "Circle" =
      .extends {"Figure"} ⟨false, none, .tc "attr" "Radius"⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 f2) _)
  have hneigh : neigh G_fig1 f2 =
      {(⟨f2, "attr", a3⟩ : Triple), ⟨f2, "coord", c2⟩} := by decide
  rw [hneigh]
  refine ⟨{(⟨f2, "attr", a3⟩ : Triple)}, fun _ => {(⟨f2, "coord", c2⟩ : Triple)}, ⟨?_, ?_, ?_⟩,
    singleton_tc_ofShape (by decide), ?_, ?_⟩
  · rw [hancSetFigure]; decide
  · rw [hancSetFigure]; intro a ha b hb hab
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · rw [hancSetFigure]; decide
  · rw [hancSetFigure]
    intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
    exact ⟨f2, c2, rfl, by decide⟩
  · rw [hancSetFigure]
    intro x hx u hu; simp only [Finset.mem_singleton] at hx; subst hx
    have hFshape : S_fig1.shapeDef "Figure" = .extends ∅ ⟨false, none, .tc "coord" "Coord"⟩ := rfl
    rw [hFshape] at hu; simp [ShapeExpr.restrOf] at hu

/-- `f1, τ ⊨ ColouredCircle` (the main multiple-inheritance claim of
Fig. 2 and Fig. 3: "f1 is a ColouredCircle").
`ColouredCircle = extends Circle, ColouredFigure ⟨ε⟩`.

`M' = ∅` (`⟨ε⟩` has no constraint when it is not closed). The rule-18
partition is over `anc({Circle,ColouredFigure}) = {Circle, Figure,
ColouredFigure}`. (Fig. 3: `Figure` comes through the two parents, but
occurs only one time.) It splits the three triples of `neigh(f1)` one to
one:

* `Mx(Circle) = {(f1,attr,a1)}` (`ext-te(Circle) = attr @Radius`).
* `Mx(Figure) = {(f1,coord,c1)}` (`ext-te(Figure) = coord @Coord`).
* `Mx(ColouredFigure) = {(f1,attr,a2)}`
  (`ext-te(ColouredFigure) = attr @Colour`).

`coord` is used one time, although `Circle` and `ColouredFigure` both go
through `Figure`. -/
theorem f1_satisfies_ColouredCircle :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 f1 (S_fig1.shapeDef "ColouredCircle") := by
  have hshape : S_fig1.shapeDef "ColouredCircle" =
      .extends {"Circle", "ColouredFigure"} ⟨false, none, .empty⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 τ_fig1 (neigh G_fig1 f1) _)
  have hneigh : neigh G_fig1 f1 =
      {(⟨f1, "attr", a1⟩ : Triple), ⟨f1, "attr", a2⟩, ⟨f1, "coord", c1⟩} := by decide
  rw [hneigh]
  refine ⟨∅, fun x => if x = "Circle" then {(⟨f1, "attr", a1⟩ : Triple)}
      else if x = "Figure" then {(⟨f1, "coord", c1⟩ : Triple)} else {⟨f1, "attr", a2⟩},
    ⟨?_, ?_, ?_⟩, empty_satisfies_emptyShape, ?_, ?_⟩
  · rw [hancSetCircleColouredFigure]; simp
  · rw [hancSetCircleColouredFigure]
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    unfold Function.onFun
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp_all <;> decide
  · rw [hancSetCircleColouredFigure]; decide
  · rw [hancSetCircleColouredFigure]
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨f1, a1, by decide, by decide⟩
    · exact ⟨f1, c1, by decide, by decide⟩
    · exact ⟨f1, a2, by decide, by decide⟩
  · rw [hancSetCircleColouredFigure]
    intro x hx u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hCshape : S_fig1.shapeDef "Circle" =
        .extends {"Figure"} ⟨false, none, .tc "attr" "Radius"⟩ := rfl
    have hFshape : S_fig1.shapeDef "Figure" = .extends ∅ ⟨false, none, .tc "coord" "Coord"⟩ := rfl
    have hCFshape : S_fig1.shapeDef "ColouredFigure" =
        .extends {"Figure"} ⟨false, none, .tc "attr" "Colour"⟩ := rfl
    rcases hx with rfl | rfl | rfl
    · rw [hCshape] at hu; simp [ShapeExpr.restrOf] at hu
    · rw [hFshape] at hu; simp [ShapeExpr.restrOf] at hu
    · rw [hCFshape] at hu; simp [ShapeExpr.restrOf] at hu

/-! The prerequisites for the decidability of `S_fig1`: `XClosed` and
`RestrOk` (which `satisfiesFuel_decidable` needs), and an `FOk` witness
for each top-level shape that a claim below checks. The display text below
computes each claim with `native_decide`. It uses the schema, graph and
typing of the proofs above. -/

theorem S_fig1_XClosed : S_fig1.XClosed := by unfold Schema.XClosed; decide

theorem S_fig1_RestrOk : S_fig1.RestrOk := by
  intro x hx u hu
  fin_cases hx <;> simp_all [S_fig1, ShapeExpr.restrOf] <;> (try subst hu) <;> trivial

def coordFOk : (S_fig1.shapeDef "Coord").FOk S_fig1 := PUnit.unit
def attributeFOk : (S_fig1.shapeDef "Attribute").FOk S_fig1 := PLift.up (by decide)
def colourFOk : (S_fig1.shapeDef "Colour").FOk S_fig1 := ⟨PLift.up (by decide), PUnit.unit⟩
def radiusFOk : (S_fig1.shapeDef "Radius").FOk S_fig1 := ⟨PLift.up (by decide), PUnit.unit⟩
def circleFOk : (S_fig1.shapeDef "Circle").FOk S_fig1 := PLift.up (by decide)
def colouredCircleFOk : (S_fig1.shapeDef "ColouredCircle").FOk S_fig1 := PLift.up (by decide)

/-- The result of `renderDecide`, computed with `native_decide`, for
`n ⊨ S_fig1.shapeDef L`. There is one line for each main claim below. -/
def satFig1 (n : RDFNode) (L : Label) (hOk : (S_fig1.shapeDef L).FOk S_fig1) : String :=
  renderDecide (satisfiesFuel_decidable S_fig1 G_fig1 τ_fig1 S_fig1_XClosed S_fig1_RestrOk
    bigFuel1 n (S_fig1.shapeDef L) hOk)

end ShexLean.Inheritance

namespace Examples

open ShexLean.Inheritance (S_fig1 G_fig1 τ_fig1 satFig1 coordFOk attributeFOk colourFOk
  radiusFOk circleFOk colouredCircleFOk c1 c2 a1 a2 a3 f1 f2)
open ShexLean (Graph.render renderDecide)

/-- The full `ColouredCircle` schema and graph of Fig. 1 and Fig. 2.

* `schemaText` and `graphText` are generated from the real values `S_fig1`
  and `G_fig1` (floats are approximated as integer literals).
* Each claim in `typingText` is a `native_decide` computation of
  `SatisfiesFuel` on the same `S_fig1`, `G_fig1` and `τ_fig1`. -/
def inheritance2025Figures : Example where
  name := "inheritance2025-example1-figures"
  summary := "Fig. 1/2's full ColouredCircle schema: f1 is both a Circle and a ColouredFigure."
  schemaText := S_fig1.render
  graphText := Graph.render G_fig1
  typingText :=
    s!"c1 ⊨ Coord = {satFig1 c1 "Coord" coordFOk}, c2 ⊨ Coord = {satFig1 c2 "Coord" coordFOk}\n" ++
    s!"a1 ⊨ Attribute = {satFig1 a1 "Attribute" attributeFOk}, " ++
      s!"a2 ⊨ Attribute = {satFig1 a2 "Attribute" attributeFOk}, " ++
      s!"a3 ⊨ Attribute = {satFig1 a3 "Attribute" attributeFOk}\n" ++
    s!"a2 ⊨ Colour = {satFig1 a2 "Colour" colourFOk}\n" ++
    s!"a1 ⊨ Radius = {satFig1 a1 "Radius" radiusFOk}, a3 ⊨ Radius = {satFig1 a3 "Radius" radiusFOk}\n" ++
    s!"f2 ⊨ Circle = {satFig1 f2 "Circle" circleFOk}\n" ++
    s!"f1 ⊨ ColouredCircle = {satFig1 f1 "ColouredCircle" colouredCircleFOk} " ++
      "— the multiple-inheritance headline claim: f1 extends both Circle and\n" ++
    "ColouredFigure, which both extend Figure, but H_S1 (Fig. 3) counts Figure's\n" ++
    "one coord property only once (see Example 2)."

end Examples
