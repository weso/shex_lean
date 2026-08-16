import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2025Inheritance.Stratification
import ShexLean.Shex2025Inheritance.Render
import Mathlib.Tactic.FinCases
import Example

/-!
Example 1 from the 2025 "Shape Expressions with Inheritance" paper (§3,
Def. 2): the full §2 motivating schema `S₁` — the multiple-inheritance
`ColouredCircle` chain: `Coord`, `Attribute`, `Colour`, abstract `Figure`,
`Circle`, `Radius`, `ColouredFigure`, and `ColouredCircle` (Fig. 1),
instantiated over Fig. 2's graph (nodes `f1`, `f2`, `a1`, `a2`, `a3`, `c1`,
`c2`), proving the paper's own headline claims: `c1`/`c2 ⊨ Coord`,
`a1`/`a2`/`a3 ⊨ Attribute`, `a2 ⊨ Colour`, `a1`/`a3 ⊨ Radius`, `f2` is a
`Circle`, and — the multiple-inheritance punchline — `f1` is a
`ColouredCircle` (Fig. 3's `H_S` gives `anc({Circle,ColouredFigure}) =
{Circle, Figure, ColouredFigure}`, `Figure` counted once even though
inherited via both parents).

The extension hierarchy `H_{S1}`'s own ancestor facts (`hancCircle`/
`hancColouredFigure`/`hancSetCircleColouredFigure`, Example 2's own
subject, Fig. 3) are proved here rather than in `Example2_...lean`, since
`f1_satisfies_ColouredCircle` (this file's own headline claim) needs
`hancSetCircleColouredFigure` to state its own rule-18 partition;
`Example2_extension_hierarchy.lean` imports this file and just re-displays
the same facts.
-/

namespace ShexLean.Inheritance

/-- A fuel bound generous enough for every proof in this file. -/
def bigFuel1 : ℕ := 10

/-- `T_float` (approximated, per the module docstring, as "any integer
literal" since `Literal` has no float constructor). -/
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

/-- Fig. 1's schema: `Coord` is a `Y`-label (a plain shape, no `extends`);
`Attribute, Colour, Figure, Circle, Radius, ColouredFigure, ColouredCircle`
are `X`-labels; `Figure` is `abstract` (`A = {Figure}`, though `A` plays no
role in the fuel-bounded `Satisfies*` relations themselves — only in
well-definedness, not yet formalized). -/
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

/-- Fig. 2's graph nodes. -/
def a1 : Subject := .iri "a1"
def a2 : Subject := .iri "a2"
def a3 : Subject := .iri "a3"
def c1 : Subject := .iri "c1"
def c2 : Subject := .iri "c2"
def f1 : Subject := .iri "f1"
def f2 : Subject := .iri "f2"

/-- Fig. 2's graph. Coordinates/`value`s are approximated as integer
literals (see the module docstring): `a1`'s `10.1` ↦ `10`, `a3`'s `7.2` ↦
`7`, `c1`'s `(2.0, 4.0)` ↦ `(2, 4)`, `c2`'s `(0.2, -2.3)` ↦ `(0, -2)`. `f1`
has *two* `attr` triples (to `a1`, the `Radius`, and to `a2`, the
`Colour`) plus one `coord` triple — exactly the three pieces
`ColouredCircle`'s rule-18 partition over `{Circle, Figure, ColouredFigure}`
needs. -/
def G_fig1 : Graph :=
  { ⟨a1, "name", .lit (.str "radius")⟩, ⟨a1, "value", .lit (.int 10)⟩,
    ⟨a2, "scope", .lit (.str "fill")⟩, ⟨a2, "name", .lit (.str "colour")⟩,
    ⟨a2, "value", .lit (.str "#ff0000")⟩,
    ⟨a3, "name", .lit (.str "radius")⟩, ⟨a3, "value", .lit (.int 7)⟩,
    ⟨c1, "x", .lit (.int 2)⟩, ⟨c1, "y", .lit (.int 4)⟩,
    ⟨c2, "x", .lit (.int 0)⟩, ⟨c2, "y", .lit (.int (-2))⟩,
    ⟨f1, "attr", a1⟩, ⟨f1, "attr", a2⟩, ⟨f1, "coord", c1⟩,
    ⟨f2, "attr", a3⟩, ⟨f2, "coord", c2⟩ }

/-- A typing witnessing every `p @z` lookup the claims below need — `τ.has`
resolutions are given directly (Definition 4 "correct typing", connecting
`τ` back to the node constraints' own truth values, is not yet
formalized), including both a node's *literal* triple-constraint types
(`T_str`/`T_any`/`T_float`/`T_"colour"`/`T_"radius"`) and, for `a1`, `a2`,
`a3`, `c1`, `c2` themselves, the shape-reference types (`Radius`, `Colour`,
`Coord`) that `f1`/`f2`'s own `attr`/`coord` triple constraints look up. -/
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

/-! General-purpose helpers for the claims below: reachability in `H_S` for
"root" (no outgoing edges) and "single parent" extendable labels, and
rule-17 (`.ofShape`) satisfaction facts for the small triple-expression
shapes Fig. 1 actually uses (`⟨ε⟩`, a bare `p @z`, and a bare `p1 @z1 ; p2
@z2`), each allowing arbitrary "junk" triples with an unrelated predicate
since none of Fig. 1's own shapes are `closed`. -/

theorem reach_root {S : Schema} {p : ShapeLabel} (hparent : ∀ c, ¬ S.extEdge p c) :
    ∀ x', Relation.ReflTransGen S.extEdge p x' → x' = p := by
  intro x' h
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
  · exact heq.symm
  · exact absurd hc (hparent c)

theorem anc_root {S : Schema} {x : ShapeLabel} (hx : x ∈ S.X)
    (hedge : ∀ c, ¬ S.extEdge x c) : S.anc x = {x} := by
  apply Finset.ext; intro x'
  unfold Schema.anc
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩; exact reach_root hedge x' h
  · rintro rfl; exact ⟨hx, Relation.ReflTransGen.refl⟩

theorem anc_one_parent {S : Schema} {x p : ShapeLabel} (hx : x ∈ S.X) (hp : p ∈ S.X)
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

/-- The empty set trivially satisfies the (non-closed, no-`extra`) trivial
shape `[ε]` (Table 3 rule 17) — reused wherever an `extends X ⟨ε⟩`'s own
`M'` piece is chosen to be empty (`Radius`/`ColouredCircle`, both of which
use a bare `⟨ε⟩` as their own shape). -/
theorem empty_satisfies_emptyShape {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ} :
    SatisfiesMFuel (fuel + 2) S G τ (∅ : Finset Triple) (.ofShape ⟨false, none, .empty⟩) := by
  have hMeEmpty : Me τ (∅ : Finset Triple) TripleExpr.empty = ∅ := by unfold Me; simp
  refine ⟨?_, ?_, fun h => absurd h (by decide)⟩
  · show SatisfiesEFuel (fuel + 1) S G τ (Me τ (∅ : Finset Triple) TripleExpr.empty) TripleExpr.empty
    rw [hMeEmpty]; rfl
  · show props (Mnotin τ (∅ : Finset Triple) TripleExpr.empty) ⊆ (∅ : Finset IRI)
    unfold Mnotin
    simp [props, TripleExpr.props, TripleExpr.tcs]

/-- `insert t junk, τ ⊨ [false,none]⟨p @z⟩` (Table 3 rule 17) whenever `t`
is the unique triple with predicate `p`, and `junk`'s predicates are all
different from `p` (so, non-closed, entirely unconstrained). Reused for
`Colour`'s own `name @T_"colour"` restriction applied to `a2`'s full
neighbourhood (which also has `scope`/`value` triples). -/
theorem single_tc_ofShape_junk {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {p : IRI} {z : ShapeLabel} {t : Triple} {junk : Finset Triple}
    (hp : t.pred = p) (hjunk : ∀ t' ∈ junk, t'.pred ≠ p) (hty : τ.has t.obj z) :
    SatisfiesMFuel (fuel + 2) S G τ (insert t junk) (.ofShape ⟨false, none, .tc p z⟩) := by
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

/-- `{t1, t2}, τ ⊨ [false,none]⟨p1 @z1 ; p2 @z2⟩` (Table 3 rule 17) for
exactly two triples, no junk — the two-triple-constraint analogue of
`singleton_tc_ofShape`, reused for Fig. 1's `Coord`, `Attribute` (nodes
`a1`/`a3`, which have no other triples), and `Radius`'s own
`name @T_"radius" ; value @T_float` restriction. -/
theorem pair_tc_tc_ofShape {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {p1 p2 : IRI} {z1 z2 : ShapeLabel} {t1 t2 : Triple}
    (hp1 : t1.pred = p1) (hp2 : t2.pred = p2) (hne : t1 ≠ t2)
    (hty1 : τ.has t1.obj z1) (hty2 : τ.has t2.obj z2) :
    SatisfiesMFuel (fuel + 3) S G τ {t1, t2}
      (.ofShape ⟨false, none, .seq (.tc p1 z1) (.tc p2 z2)⟩) := by
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
  refine ofShape_of_Me_eq_self (fuel := fuel + 2) hMe ⟨{t1}, {t2}, ⟨?_, ?_⟩,
    ⟨t1.subj, t1.obj, by rw [← hp1], hty1⟩, ⟨t2.subj, t2.obj, by rw [← hp2], hty2⟩⟩
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_singleton] at hx1 hx2
    exact hne (hx1.symm.trans hx2)
  · ext x; simp

/-- `insert t1 (insert t2 junk), τ ⊨ [false,none]⟨p1 @z1 ; p2 @z2⟩` (Table
3 rule 17): the junk-tolerant analogue of `pair_tc_tc_ofShape`, reused for
`a2 ⊨ Attribute` (`a2`'s neighbourhood also has a `scope` triple, unrelated
to `Attribute`'s own `name`/`value`). -/
theorem pair_tc_tc_ofShape_junk {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {p1 p2 : IRI} {z1 z2 : ShapeLabel} {t1 t2 : Triple} {junk : Finset Triple}
    (hp1 : t1.pred = p1) (hp2 : t2.pred = p2) (hne : t1 ≠ t2)
    (hjunk : ∀ t ∈ junk, t.pred ≠ p1 ∧ t.pred ≠ p2)
    (hty1 : τ.has t1.obj z1) (hty2 : τ.has t2.obj z2) :
    SatisfiesMFuel (fuel + 3) S G τ (insert t1 (insert t2 junk))
      (.ofShape ⟨false, none, .seq (.tc p1 z1) (.tc p2 z2)⟩) := by
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

/-! `H_S`'s edges (Fig. 3) among the `X`-labels actually used below —
Example 2's own subject matter (`Example2_extension_hierarchy.lean`), but
needed here for `f1_satisfies_ColouredCircle`'s own rule-18 partition. -/

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
  rw [show ({"Circle", "ColouredFigure"} : Finset ShapeLabel) = insert "Circle" {"ColouredFigure"}
      from rfl, Finset.biUnion_insert, Finset.singleton_biUnion, hancCircle, hancColouredFigure]
  decide

/-- `c1, τ ⊨ Coord` (Fig. 2's claim "node c1 satisfies Coord"). `Coord` is
a `Y`-label (a bare, `extends`-free shape), so this reduces directly to a
rule-17 check on `neigh(c1)`. -/
theorem c1_satisfies_Coord :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 c1 (S_fig1.shapeDef "Coord") := by
  have hshape : S_fig1.shapeDef "Coord" =
      .ofShape ⟨false, none, .seq (.tc "x" "T_float") (.tc "y" "T_float")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 c1) _)
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
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 c2) _)
  have hneigh : neigh G_fig1 c2 =
      {(⟨c2, "x", .lit (.int 0)⟩ : Triple), ⟨c2, "y", .lit (.int (-2))⟩} := by decide
  rw [hneigh]
  exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `a1, τ ⊨ Attribute` (Fig. 2's claim "Nodes a1, a2, a3 satisfy
`Attribute`", restricted to `a1`). `Attribute` has no `extends` targets of
its own, so the rule-18 partition is trivial: `M' = M`, `Mx` vacuous over
`anc(∅) = ∅`. -/
theorem a1_satisfies_Attribute :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 a1 (S_fig1.shapeDef "Attribute") := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a1) _)
  have hneigh : neigh G_fig1 a1 =
      {(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩} := by decide
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset ShapeLabel) = ∅ := by unfold Schema.ancSet; simp
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
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a3) _)
  have hneigh : neigh G_fig1 a3 =
      {(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩} := by decide
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset ShapeLabel) = ∅ := by unfold Schema.ancSet; simp
  refine ⟨{(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩},
    fun _ => ∅, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hanc]; decide
  · rw [hanc]; intro a ha; simp at ha
  · rw [hanc]; decide
  · exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)
  · rw [hanc]; intro x hx; simp at hx
  · rw [hanc]; intro x hx; simp at hx

/-- `a2, τ ⊨ Attribute`: `a2`'s neighbourhood also has a `scope` triple
(needed for `Colour`, see `a2_satisfies_Colour`), which `Attribute` (not
`closed`) simply ignores as junk. -/
theorem a2_satisfies_Attribute :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 a2 (S_fig1.shapeDef "Attribute") := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a2) _)
  have hneigh : neigh G_fig1 a2 =
      insert (⟨a2, "name", .lit (.str "colour")⟩ : Triple)
        (insert (⟨a2, "value", .lit (.str "#ff0000")⟩ : Triple) {⟨a2, "scope", .lit (.str "fill")⟩}) := by
    decide
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset ShapeLabel) = ∅ := by unfold Schema.ancSet; simp
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

/-- `a2, τ ⊨ Colour` (Fig. 2's claim "node a2 satisfies Colour"). `Colour =
extends Attribute ⟨scope @T_str⟩ and ⟨name @T_"colour"⟩`: the first
conjunct splits `neigh(a2)` into `M' = {scope-triple}` (matching `scope
@T_str`) and `Mx(Attribute) = {name-triple, value-triple}` (matching
`ext-te(Attribute) = name @T_str ; value @T_any`); the second conjunct
checks `name @T_"colour"` directly against all of `neigh(a2)` (the
`scope`/`value` triples are junk to it). -/
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
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a2) _)
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
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a2) _)
    rw [hneigh]
    refine single_tc_ofShape_junk rfl ?_ (by decide)
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide

/-- `a1, τ ⊨ Radius` (Fig. 2's claim "a1, a3 satisfy Radius"). `Radius =
extends Attribute ⟨ε⟩ and ⟨name @T_"radius" ; value @T_float⟩`: the first
conjunct's own `M' = ∅` (trivially, `⟨ε⟩` is unconstrained when
non-closed) and `Mx(Attribute) = neigh(a1)` (all of it, matching
`ext-te(Attribute)`); the second conjunct checks `name @T_"radius" ; value
@T_float` directly against `neigh(a1)` (no junk here — `a1` has exactly
those two triples). -/
theorem a1_satisfies_Radius :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 a1 (S_fig1.shapeDef "Radius") := by
  have hshape : S_fig1.shapeDef "Radius" =
      .and (.extends {"Attribute"} ⟨false, none, .empty⟩)
        (.ofShape ⟨false, none, .seq (.tc "name" "T_radius") (.tc "value" "T_float")⟩) := rfl
  rw [hshape]
  have hneigh : neigh G_fig1 a1 =
      {(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩} := by decide
  refine ⟨?_, ?_⟩
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a1) _)
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
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a1) _)
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
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a3) _)
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
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a3) _)
    rw [hneigh]
    exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `f2, τ ⊨ Circle` (Fig. 2's claim "f2 is a Circle"). `Circle = extends
Figure ⟨attr @Radius⟩`: `M' = {(f2,attr,a3)}` (matching `attr @Radius`,
via `τ`'s `(a3, Radius)` assertion) and `Mx(Figure) = {(f2,coord,c2)}`
(matching `ext-te(Figure) = coord @Coord`, via `(c2, Coord)`). -/
theorem f2_satisfies_Circle :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 f2 (S_fig1.shapeDef "Circle") := by
  have hshape : S_fig1.shapeDef "Circle" =
      .extends {"Figure"} ⟨false, none, .tc "attr" "Radius"⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 f2) _)
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

/-- `f1, τ ⊨ ColouredCircle` (Fig. 2/3's headline multiple-inheritance
claim: "f1 is a ColouredCircle"). `ColouredCircle = extends Circle,
ColouredFigure ⟨ε⟩`: `M' = ∅` (`⟨ε⟩`, non-closed, unconstrained), and the
rule-18 partition over `anc({Circle,ColouredFigure}) = {Circle, Figure,
ColouredFigure}` (Fig. 3: `Figure`, inherited via *both* parents, appears
only once) splits `neigh(f1)`'s three triples one-to-one:
`Mx(Circle) = {(f1,attr,a1)}` (`ext-te(Circle) = attr @Radius`),
`Mx(Figure) = {(f1,coord,c1)}` (`ext-te(Figure) = coord @Coord`),
`Mx(ColouredFigure) = {(f1,attr,a2)}` (`ext-te(ColouredFigure) = attr
@Colour`) — `coord` used once even though both `Circle` and
`ColouredFigure` route through `Figure`. -/
theorem f1_satisfies_ColouredCircle :
    SatisfiesFuel bigFuel1 S_fig1 G_fig1 τ_fig1 f1 (S_fig1.shapeDef "ColouredCircle") := by
  have hshape : S_fig1.shapeDef "ColouredCircle" =
      .extends {"Circle", "ColouredFigure"} ⟨false, none, .empty⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 f1) _)
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

/-! `S_fig1`'s decidability prerequisites: `XClosed`/`RestrOk` (needed by
`satisfiesFuel_decidable`), and an `FOk` witness for each top-level shape
one of the claims below checks — `Example1_figures.lean`'s own display text
now computes every claim via `native_decide` rather than transcribing the
paper's prose, reusing the schema/graph/typing already proved correct
above. -/

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

/-- `renderDecide`'s `native_decide`-computed verdict for `n ⊨ S_fig1.shapeDef L`,
one line per headline claim below. -/
def satFig1 (n : RDFNode) (L : ShapeLabel) (hOk : (S_fig1.shapeDef L).FOk S_fig1) : String :=
  renderDecide (satisfiesFuel_decidable S_fig1 G_fig1 τ_fig1 S_fig1_XClosed S_fig1_RestrOk
    bigFuel1 n (S_fig1.shapeDef L) hOk)

end ShexLean.Inheritance

namespace Examples

open ShexLean.Inheritance (S_fig1 G_fig1 τ_fig1 satFig1 coordFOk attributeFOk colourFOk
  radiusFOk circleFOk colouredCircleFOk c1 c2 a1 a2 a3 f1 f2)
open ShexLean (Graph.render renderDecide)

/-- Fig. 1/2's full `ColouredCircle` schema and graph. `schemaText`/
`graphText` are generated from the real `S_fig1`/`G_fig1` values (integer
literals, per the module docstring's float approximation); every claim in
`typingText` is a `native_decide` computation of `SatisfiesFuel` on the same
`S_fig1`/`G_fig1`/`τ_fig1`, not prose. -/
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
