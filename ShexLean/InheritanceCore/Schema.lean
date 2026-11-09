import ShexLean.InheritanceCore.Syntax
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Relation

/-!
The schemas of "Shape Expressions with Inheritance" (2025, Definitions 2,
3, 5, 6 and 7), for any type `E` of shape expressions.

The 2025 paper (`ShexLean/Shex2025Inheritance/`) and the 2026 exploration
(`ShexLean/Shex2026InheritanceDisjunction/`) have different shape
expressions: the payload of `extends` is one shape or a list of shapes.
But the schema, the extension hierarchy `H_S`, the dependency graph `D_S`,
stratifications and the restrictions of a schema to a set of labels use a
shape expression only through two functions. The class `ShapeSyntax` gives
them:

* `extendsTargets s`: the labels after `extends`, at any location in `s`.
* `deps s`: the dependency information of `s` (the `depsAux false` walk of
  Definition 5).

Each development defines `Schema` as `ShexLean.InheritanceCore.Schema` at
its own `ShapeExpr`.
-/

namespace ShexLean.InheritanceCore

/-- The two functions of a shape expression that the schema-level
definitions use, and the two facts about them that Definition 5 states
("`dep` subsumes `dep-shape-neg` and `dep-extra-neg`"). -/
class ShapeSyntax (E : Type) where
  extendsTargets : E → Finset Label
  deps : E → DepInfo
  negRefs_subset_refs : ∀ s, (deps s).negRefs ⊆ (deps s).refs
  extraNegRefs_subset_refs : ∀ s, (deps s).extraNegRefs ⊆ (deps s).refs

/-- Definition 2 (ShEx schema). `S = (Y, X, def, A)`:

* `Y`: the simple labels.
* `X`: the extendable labels, disjoint from `Y`.
* `A ⊆ X`: the abstract labels.
* `shapeDef` (the `def` of the paper): gives a definition to each label of
  `Y ∪ X`.

`shapeDef` is total on all of `Label` (as in the 2017 formalization),
because Lean functions must be total. Because of this, we need the extra
hypothesis `Schema.WellFormedX` below. (It has the same role as
`Schema.Closed` in `ShexLean/Shex2017Schemas/Proposition1.lean`.) -/
structure Schema (E : Type) where
  Y : Finset Label
  X : Finset Label
  A : Finset Label
  disjointYX : Disjoint Y X
  A_subX : A ⊆ X
  shapeDef : Label → E

variable {E : Type} [ShapeSyntax E]

/-- The labels that a shape expression can reach:

* The `@z'` references at any location in it (`ShapeSyntax.deps`).
* The `extends` targets at any location in it
  (`ShapeSyntax.extendsTargets`). -/
def depsIn (s : E) (Z : Finset Label) : Prop :=
  (ShapeSyntax.deps s).refs ⊆ Z ∧ ShapeSyntax.extendsTargets s ⊆ Z

/-- The edge relation of `H_S` in Definition 3. There is an edge from `x`
to `x'` if and only if `x'` comes directly after `extends` at the top of
`def(x)`. -/
abbrev Schema.extEdge (S : Schema E) (x x' : Label) : Prop :=
  x' ∈ ShapeSyntax.extendsTargets (S.shapeDef x)

/-- Definition 3 (extension hierarchy). `x' ∈ S.anc x` if and only if
there is a path (possibly empty) from `x` to `x'` in `H_S`. Thus, `x'` is
an ancestor of `x`, and `x` is a descendant of `x'`.

The result is restricted to `S.X` (the vertex set of `H_S`). It has a
meaning only for `x ∈ S.X`. The definition uses `Classical.decPred`,
because `extEdge` is a `Prop` and, in general, reachability is not
decidable. The 2017 formalization does the same in other locations. -/
noncomputable def Schema.anc (S : Schema E) (x : Label) : Finset Label :=
  haveI := Classical.decPred (Relation.ReflTransGen S.extEdge x)
  S.X.filter (Relation.ReflTransGen S.extEdge x)

/-- `S.desc x`: the descendants of `x` (the dual of `S.anc`). -/
noncomputable def Schema.desc (S : Schema E) (x : Label) : Finset Label :=
  haveI := Classical.decPred (Relation.ReflTransGen S.extEdge · x)
  S.X.filter (Relation.ReflTransGen S.extEdge · x)

/-- `anc(X) = ⋃_{x ∈ X} anc(x)`. Table 3 extends `anc` to a set of labels
in this way. Rule 18 uses it. -/
noncomputable def Schema.ancSet (S : Schema E) (xs : Finset Label) : Finset Label :=
  xs.biUnion S.anc

/-! ### Membership lemmas

`anc` and `desc` are filters with a `Classical.decPred` instance. These
lemmas fix the instance one time, here. Thus, the proofs in the other
files use `rw` or `simp` with these lemmas, and never unfold the filters.
This prevents instance mismatches at the call sites. -/

theorem Schema.mem_anc {S : Schema E} {x y : Label} :
    y ∈ S.anc x ↔ y ∈ S.X ∧ Relation.ReflTransGen S.extEdge x y := by
  unfold Schema.anc; simp only [Finset.mem_filter]

theorem Schema.mem_desc {S : Schema E} {x y : Label} :
    y ∈ S.desc x ↔ y ∈ S.X ∧ Relation.ReflTransGen S.extEdge y x := by
  unfold Schema.desc; simp only [Finset.mem_filter]

theorem Schema.mem_ancSet {S : Schema E} {xs : Finset Label} {y : Label} :
    y ∈ S.ancSet xs ↔ ∃ x ∈ xs, y ∈ S.anc x := by
  unfold Schema.ancSet; exact Finset.mem_biUnion

/-- Each label of `X` is its own ancestor (the empty path of `H_S`). -/
theorem Schema.mem_anc_self {S : Schema E} {x : Label} (hx : x ∈ S.X) : x ∈ S.anc x :=
  Schema.mem_anc.mpr ⟨hx, Relation.ReflTransGen.refl⟩

theorem Schema.anc_subset_X {S : Schema E} {x : Label} : S.anc x ⊆ S.X :=
  fun _ hy => (Schema.mem_anc.mp hy).1

theorem Schema.ancSet_subset_X {S : Schema E} {xs : Finset Label} : S.ancSet xs ⊆ S.X := by
  intro y hy
  obtain ⟨_, _, hy⟩ := Schema.mem_ancSet.mp hy
  exact Schema.anc_subset_X hy

/-! ### Definition 5: the dependency graph `D_S` -/

/-- `dep-extends_S(z,z')`: `H_S` has an edge between `z` and `z'`, in one
of the two directions. -/
def Schema.depExtends (S : Schema E) (z z' : Label) : Prop := S.extEdge z z' ∨ S.extEdge z' z

/-- `dep_S(z,z')`: `z'` occurs as a reference (`@z'`) in `def(z)`. -/
def Schema.dep (S : Schema E) (z z' : Label) : Prop :=
  z' ∈ (ShapeSyntax.deps (S.shapeDef z)).refs

/-- `dep-shape-neg_S(z,z')`: `def(z)` has a reference to `z'` below a
`not`. (Refer to `ShapeExpr.depsAux`: this file counts "below any `not`",
not "below an odd number of `not`".) -/
def Schema.depShapeNeg (S : Schema E) (z z' : Label) : Prop :=
  z' ∈ (ShapeSyntax.deps (S.shapeDef z)).negRefs

/-- `dep-extra-neg_S(z,z')`: a sub-expression `[closed][extra P]⟨e⟩` of
`def(z)` has a triple constraint `p @z'` with `p ∈ P`. -/
def Schema.depExtraNeg (S : Schema E) (z z' : Label) : Prop :=
  z' ∈ (ShapeSyntax.deps (S.shapeDef z)).extraNegRefs

/-- "`dep` subsumes `dep-shape-neg`" (the remark after Definition 5). -/
theorem Schema.dep_of_depShapeNeg {S : Schema E} {z z' : Label} (h : S.depShapeNeg z z') :
    S.dep z z' :=
  ShapeSyntax.negRefs_subset_refs (S.shapeDef z) h

/-- "`dep` subsumes `dep-extra-neg`" (the remark after Definition 5). -/
theorem Schema.dep_of_depExtraNeg {S : Schema E} {z z' : Label} (h : S.depExtraNeg z z') :
    S.dep z z' :=
  ShapeSyntax.extraNegRefs_subset_refs (S.shapeDef z) h

/-! ### Definition 6: well-defined schema, stratified negation -/

/-- `H_S` is acyclic: no extendable label extends itself transitively.
This is the first of the two conditions of Definition 6. -/
def Schema.ExtAcyclic (S : Schema E) : Prop :=
  ∀ x ∈ S.X, ¬ Relation.TransGen S.extEdge x x

/-- An edge of `D_S` ("`z` depends on `z'`"). `dep` subsumes
`dep-shape-neg` and `dep-extra-neg` (the remark after Definition 5). Thus,
`dep` and `dep-extends` together already cover each edge that `D_S` can
have, for each of the four labels. -/
def Schema.DEdge (S : Schema E) (z z' : Label) : Prop := S.dep z z' ∨ S.depExtends z z'

/-- An edge of `D_S` with one of the two *negative* labels. -/
def Schema.DNegEdge (S : Schema E) (z z' : Label) : Prop :=
  S.depShapeNeg z z' ∨ S.depExtraNeg z z'

/-- `D_S` has a cycle through a negative dependency edge. There is a
negative edge `a → b`, and an ordinary `D_S` path from `b` back to `a`
closes the cycle. (The path can be empty if `a = b`. This is a negative
self-loop.) -/
def Schema.NegCycle (S : Schema E) : Prop :=
  ∃ a b, S.DNegEdge a b ∧ Relation.ReflTransGen S.DEdge b a

/-- Definition 6 (well-defined schema, stratified negation). -/
def Schema.WellDefined (S : Schema E) : Prop := S.ExtAcyclic ∧ ¬ S.NegCycle

/-! ### The rank of an extendable label -/

/-- `S.anc` becomes strictly smaller along each edge of `H_S`, if
`S.ExtAcyclic` is true (the acyclicity condition of Definition 6).

If `x` extends `y`, then `x` also extends each label that `y` extends
transitively. But `x ∈ S.anc x`, and `x ∈ S.anc y` closes a cycle through
the edge `x → y`. This is the usual argument with the number of ancestors
as a rank function on a DAG. Because of it, `ExtAcyclic` alone gives a
well-founded measure. -/
theorem Schema.anc_ssubset_of_extEdge {S : Schema E} (hAcyclic : S.ExtAcyclic)
    {x y : Label} (hxX : x ∈ S.X) (hxy : S.extEdge x y) :
    S.anc y ⊂ S.anc x := by
  have hsub : S.anc y ⊆ S.anc x := by
    intro z hz
    rw [Schema.mem_anc] at hz ⊢
    exact ⟨hz.1, Relation.ReflTransGen.head hxy hz.2⟩
  refine ⟨hsub, fun hsub' => ?_⟩
  have hxy' : Relation.ReflTransGen S.extEdge y x :=
    (Schema.mem_anc.mp (hsub' (Schema.mem_anc_self hxX))).2
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy' with heq | htrans
  · exact hAcyclic x hxX (Relation.TransGen.single (heq.symm ▸ hxy))
  · exact hAcyclic x hxX (Relation.TransGen.head hxy htrans)

/-- `S.extRank x := (S.anc x).card`: a rank in `ℕ` that is a witness of the
acyclicity of `H_S`. It decreases strictly along each edge
(`extRank_lt_of_extEdge` below). The termination argument in the rest of
this file uses this well-founded measure. -/
noncomputable def Schema.extRank (S : Schema E) (x : Label) : ℕ := (S.anc x).card

/-- The rank form of `anc_ssubset_of_extEdge`: `extRank` decreases
strictly along each edge of `H_S` that starts at a label of `S`. -/
theorem Schema.extRank_lt_of_extEdge {S : Schema E} (hAcyclic : S.ExtAcyclic)
    {x y : Label} (hxX : x ∈ S.X) (hxy : S.extEdge x y) :
    S.extRank y < S.extRank x :=
  Finset.card_lt_card (S.anc_ssubset_of_extEdge hAcyclic hxX hxy)

/-- `extRank` does not increase along an ancestor path. If `x' ∈ S.anc x`,
then `extRank x' ≤ extRank x`. (The inequality is not strict, because
`x ∈ S.anc x` reflexively.) This bounds the rank of each label that a
rule-18 partition reaches (`x' ∈ S.ancSet xs`), not only the direct
targets `xs`. -/
theorem Schema.extRank_le_of_mem_anc {S : Schema E} {x x' : Label} (hx' : x' ∈ S.anc x) :
    S.extRank x' ≤ S.extRank x := by
  apply Finset.card_le_card
  intro z hz
  rw [Schema.mem_anc] at hx' hz ⊢
  exact ⟨hz.1, hx'.2.trans hz.2⟩

/-- Each `x ∈ S.X` has `extRank x ≥ 1` (reflexively, `x ∈ S.anc x`). Thus,
you can always write `extRank x` as `m + 1`. -/
theorem Schema.extRank_succ {S : Schema E} {x : Label} (hx : x ∈ S.X) :
    ∃ m, S.extRank x = m + 1 := by
  have h1 : 1 ≤ S.extRank x := Finset.one_le_card.mpr ⟨x, Schema.mem_anc_self hx⟩
  exact ⟨S.extRank x - 1, by omega⟩

/-- The fuel that is always sufficient for `S` (refer to `rankOk_any`). -/
noncomputable def Schema.fuelBound (S : Schema E) : ℕ := S.X.sup S.extRank + 1

/-! ### Definition 7: stratification -/

/-- `Z` is closed under `D_S`: each label that a member of `Z` depends on
(`dep` or `depExtends`) is also in `Z`. `Schema.DClosed` is the case
`Z = Y ∪ X`. Proposition 1 below also needs it for `Z = ` a stratum. -/
def Schema.DClosedOn (S : Schema E) (Z : Finset Label) : Prop :=
  ∀ z ∈ Z, ∀ z', S.DEdge z z' → z' ∈ Z

/-- Membership in a `D_S`-closed `Z` continues along each `D_S` path. -/
theorem Schema.reach_mem {S : Schema E} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {z z' : Label} (hz : z ∈ Z) (h : Relation.ReflTransGen S.DEdge z z') : z' ∈ Z := by
  induction h with
  | refl => exact hz
  | tail _ hstep ih => exact hZ _ ih _ hstep

/-- Well-formedness in addition to `ExtAcyclic`: each
label that is `D_S`-reachable from a declared label (`z ∈ Y ∪ X`) is also
declared.

The reason is the same as for `Schema.Closed` of 2017 (refer to the module
docstring of `ShexLean/Shex2017Schemas/Proposition1.lean`). `shapeDef` is
total on `Label`. Thus, a schema can refer to a label that is not
declared. But the conditions of `Stratification` apply only when the
source of the edge is in `Y ∪ X`. -/
def Schema.DClosed (S : Schema E) : Prop := S.DClosedOn (S.Y ∪ S.X)

/-- Definition 7 (stratification). It uses the edges of `D_S` (`DEdge` and
`DNegEdge`), not the paths of the paper. The two forms are equivalent by
induction on the path length. (`Stratification.lt_of_negPath` below gets
the path form.) `maxTypingAgreeing_correct` (later in the file) needs the
edge form. This definition has the same role as `Stratification` of 2017
(`ShexLean/Shex2017Schemas/Stratification.lean`). -/
structure Stratification (S : Schema E) where
  k : ℕ
  strat : Label → ℕ
  mem_range : ∀ z ∈ S.Y ∪ S.X, 1 ≤ strat z ∧ strat z ≤ k
  dep_le : ∀ z ∈ S.Y ∪ S.X, ∀ z', S.DEdge z z' → strat z' ≤ strat z
  negDep_lt : ∀ z ∈ S.Y ∪ S.X, ∀ z', S.DNegEdge z z' → strat z' < strat z

/-- `S` has a stratification (the existence part of Definition 7). The
paper says, with no proof, that stratified negation makes sure that a
stratification exists ("well known that stratified negation ... guarantees
the existence of a stratification"). This file also does not prove it.
The 2017 formalization does the same: `Schema.StratifiedNegation` is only
`Nonempty (Stratification S)`, with no separate existence theorem. -/
def Schema.StratifiedNegation (S : Schema E) : Prop := Nonempty (Stratification S)

/-- "`dep` subsumes `dep-shape-neg`/`dep-extra-neg`", applied to `DEdge`.
Each negative edge is also an ordinary `D_S` edge. -/
theorem Schema.DEdge_of_DNegEdge {S : Schema E} {z z' : Label} (h : S.DNegEdge z z') :
    S.DEdge z z' := by
  rcases h with h | h
  · exact Or.inl (Schema.dep_of_depShapeNeg h)
  · exact Or.inl (Schema.dep_of_depExtraNeg h)

/-- `strat` never increases along a `D_S` path (the first bullet of
Definition 7, in path form). -/
theorem Stratification.le_of_path {S : Schema E} (hDClosed : S.DClosed) (strat : Stratification S)
    {z z' : Label} (hzY : z ∈ S.Y ∪ S.X) (h : Relation.ReflTransGen S.DEdge z z') :
    strat.strat z' ≤ strat.strat z := by
  induction h with
  | refl => exact le_refl _
  | tail hprev hstep ih => exact le_trans (strat.dep_le _ (S.reach_mem hDClosed hzY hprev) _ hstep) ih

/-- Take a `D_S` path from `z` to `z'` that goes through a negative edge
`a → b` (`z ↝ a`, `a → b` negative, `b ↝ z'`). Along this path, `strat`
decreases strictly in total (the second bullet of Definition 7, in path
form). The proof applies `le_of_path` on each side of the strict step
`negDep_lt` in the middle. -/
theorem Stratification.lt_of_negPath {S : Schema E} (hDClosed : S.DClosed)
    (strat : Stratification S) {z a b z' : Label} (hzY : z ∈ S.Y ∪ S.X)
    (hza : Relation.ReflTransGen S.DEdge z a) (hab : S.DNegEdge a b)
    (hbz' : Relation.ReflTransGen S.DEdge b z') :
    strat.strat z' < strat.strat z := by
  have haY : a ∈ S.Y ∪ S.X := S.reach_mem hDClosed hzY hza
  have hbY : b ∈ S.Y ∪ S.X := hDClosed a haY b (S.DEdge_of_DNegEdge hab)
  calc strat.strat z' ≤ strat.strat b := strat.le_of_path hDClosed hbY hbz'
    _ < strat.strat a := strat.negDep_lt a haY b hab
    _ ≤ strat.strat z := strat.le_of_path hDClosed hzY hza

/-! ### Label sets that are closed under `D_S` -/

/-- If `x ∈ Z` and `Z` is `D_S`-closed, then the definition of `x` reaches
only labels in `Z`. The closure of `Z` is what is necessary to do the
recursion one more `extends` step deep and stay in `Z`. -/
theorem Schema.shapeDef_depsIn {S : Schema E} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {x : Label} (hx : x ∈ Z) : depsIn (S.shapeDef x) Z :=
  ⟨fun _ hz' => hZ x hx _ (Or.inl hz'), fun _ hz' => hZ x hx _ (Or.inr (Or.inl hz'))⟩

/-- `S.ancSet xs ⊆ Z` if `xs ⊆ Z` and `Z` is `D_S`-closed. Each ancestor
that a rule-18 partition reaches also stays in `Z`. -/
theorem Schema.ancSet_subset {S : Schema E} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {xs : Finset Label} (hxs : xs ⊆ Z) : S.ancSet xs ⊆ Z := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Schema.mem_ancSet.mp hx
  rw [Schema.mem_anc] at hyx
  have hstep : Relation.ReflTransGen S.DEdge y x :=
    Relation.ReflTransGen.mono (fun _ _ hab => Or.inr (Or.inl hab)) y x hyx.2
  exact S.reach_mem hZ (hxs hy) hstep

/-! ### Strata and the restriction of a schema to a stratum -/

/-- `nodes(G) × (Y ∪ X)`: the universe of all the possible node-type
associations for `G` by `S`. -/
def Schema.univTyping (S : Schema E) (G : Graph) : Typing := G.nodes ×ˢ (S.Y ∪ S.X)

/-- `Y_i^σ ∪ X_i^σ = {z ∈ Y ∪ X | σ(z) ≤ i}`. -/
def Schema.stratum (S : Schema E) (strat : Label → ℕ) (i : ℕ) : Finset Label :=
  (S.Y ∪ S.X).filter (fun z => strat z ≤ i)

omit [ShapeSyntax E] in
theorem Schema.mem_stratum {S : Schema E} {strat : Label → ℕ} {i : ℕ} {z : Label} :
    z ∈ S.stratum strat i ↔ z ∈ S.Y ∪ S.X ∧ strat z ≤ i := by
  simp only [Schema.stratum, Finset.mem_filter]

omit [ShapeSyntax E] in
theorem Schema.stratum_mono {S : Schema E} {strat : Label → ℕ} {i j : ℕ} (h : i ≤ j) :
    S.stratum strat i ⊆ S.stratum strat j := by
  intro z hz
  simp only [Schema.stratum, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hz.2.trans h⟩

/-- `S_i^σ = (Y_i^σ, X_i^σ, def, A_i^σ)`: the restriction of `S` to the
labels with a stratum `≤ i`. The definitions do not change. -/
def Schema.stratRestrict (S : Schema E) (strat : Label → ℕ) (i : ℕ) : Schema E where
  Y := S.Y.filter (fun z => strat z ≤ i)
  X := S.X.filter (fun z => strat z ≤ i)
  A := S.A.filter (fun z => strat z ≤ i)
  disjointYX := Finset.disjoint_filter_filter S.disjointYX
  A_subX := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨S.A_subX hz.1, hz.2⟩
  shapeDef := S.shapeDef

/-- `ExtAcyclic` stays true for each `stratRestrict`. Its `X` only becomes
smaller, and `extEdge` uses only
`shapeDef` (`stratRestrict` never changes `shapeDef`). Thus, a cycle in
the restriction is also a cycle in `S`. -/
theorem Schema.stratRestrict_ExtAcyclic {S : Schema E} (hAcyclic : S.ExtAcyclic)
    (strat : Label → ℕ) (i : ℕ) : (S.stratRestrict strat i).ExtAcyclic := by
  intro x hx
  simp only [Schema.stratRestrict, Finset.mem_filter] at hx
  exact hAcyclic x hx.1

/-- Each stratum `S.stratum strat i` is `D_S`-closed. The edges of `D_S`
never increase `strat` (the first bullet of Definition 7), and
`Schema.DClosed` keeps the membership in `Y ∪ X` along the path. -/
theorem Schema.stratum_DClosedOn {S : Schema E} (hDClosed : S.DClosed) (strat : Stratification S)
    (i : ℕ) : S.DClosedOn (S.stratum strat.strat i) := by
  intro z hz z' hedge
  simp only [Schema.stratum, Finset.mem_filter] at hz ⊢
  have hzY : z ∈ S.Y ∪ S.X := hz.1
  have hz'Y : z' ∈ S.Y ∪ S.X := hDClosed z hzY z' hedge
  exact ⟨hz'Y, le_trans (strat.dep_le z hzY z' hedge) hz.2⟩

/-- `(S.stratRestrict strat i).anc x = S.anc x` if `x` is in a stratum
`≤ i`. Each element of the unrestricted `S.anc x` already has
`strat ≤ strat x ≤ i` (the first bullet of Definition 7, through
`extEdge ⊆ depExtends ⊆ DEdge`). Thus, if you filter `S.X` to
`strat ≤ i` before you compute `anc`, you remove nothing.

Because of this, `Satisfies` computed with two different `stratRestrict`
levels agrees for each label in the lower level. The `ancSet` and
`extends`-step data that the `.extends` case of `SatisfiesMFuel` uses do
not depend on the (sufficiently high) stratum level of the schema
restriction. -/
theorem Schema.stratRestrict_anc_eq {S : Schema E} (hDClosed : S.DClosed) (strat : Stratification S)
    {x : Label} (hxY : x ∈ S.Y ∪ S.X) {i : ℕ} (hxi : strat.strat x ≤ i) :
    (S.stratRestrict strat.strat i).anc x = S.anc x := by
  apply Finset.ext
  intro y
  unfold Schema.anc Schema.stratRestrict Schema.extEdge
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hyX, _⟩, hpath⟩
    exact ⟨hyX, hpath⟩
  · rintro ⟨hyX, hpath⟩
    have hDEdgePath : Relation.ReflTransGen S.DEdge x y :=
      Relation.ReflTransGen.mono (fun _ _ h => Or.inr (Or.inl h)) x y hpath
    have hstratY : strat.strat y ≤ strat.strat x := strat.le_of_path hDClosed hxY hDEdgePath
    exact ⟨⟨hyX, by omega⟩, hpath⟩

omit [ShapeSyntax E] in
/-- `(S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X` (a union of
two sets, each with its own filter) and `S.stratum strat i` (one filter
over the union) are the same `Finset`, made in different ways. This lemma
connects the `Y ∪ X` form of `Schema.univTyping` with the form of
`Schema.stratum_mono`. -/
theorem Schema.stratRestrict_YX_eq_stratum (S : Schema E) (strat : Label → ℕ) (i : ℕ) :
    (S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X = S.stratum strat i := by
  unfold Schema.stratRestrict Schema.stratum
  rw [Finset.filter_union]

omit [ShapeSyntax E] in
/-- The labels of `S.stratRestrict strat i` are the labels of `S` with a
stratum `≤ i`. -/
theorem Schema.mem_stratRestrict_YX {S : Schema E} {strat : Label → ℕ} {i : ℕ} {z : Label} :
    z ∈ (S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X ↔
      z ∈ S.Y ∪ S.X ∧ strat z ≤ i := by
  rw [Schema.stratRestrict_YX_eq_stratum, Schema.mem_stratum]

omit [ShapeSyntax E] in
theorem Schema.mem_stratRestrict_X {S : Schema E} {strat : Label → ℕ} {i : ℕ} {z : Label} :
    z ∈ (S.stratRestrict strat i).X ↔ z ∈ S.X ∧ strat z ≤ i := by
  simp only [Schema.stratRestrict, Finset.mem_filter]

omit [ShapeSyntax E] in
theorem Schema.mem_stratRestrict_A {S : Schema E} {strat : Label → ℕ} {i : ℕ} {z : Label} :
    z ∈ (S.stratRestrict strat i).A ↔ z ∈ S.A ∧ strat z ≤ i := by
  simp only [Schema.stratRestrict, Finset.mem_filter]

/-- At the top stratum `k`, the restriction removes nothing. -/
theorem Schema.stratRestrict_top {S : Schema E} (strat : Stratification S) :
    S.stratRestrict strat.strat strat.k = S := by
  unfold Schema.stratRestrict
  congr 1
  · exact Finset.filter_true_of_mem
      (fun z hz => (strat.mem_range z (Finset.mem_union_left _ hz)).2)
  · exact Finset.filter_true_of_mem
      (fun z hz => (strat.mem_range z (Finset.mem_union_right _ hz)).2)
  · exact Finset.filter_true_of_mem
      (fun z hz => (strat.mem_range z (Finset.mem_union_right _ (S.A_subX hz))).2)

/-- `stratRestrict` does not change the edge relation of `D_S`. (It changes
only `Y`, `X` and `A`, never `shapeDef`, and `DEdge` uses only
`shapeDef`.)

This fact is a separate `rfl` lemma, so that later proofs can use it
directly with `rw`. Do not let the elaborator find it again by
unification. `DEdge` unfolds through much `Schema` and `Finset` data, so
the unification is very slow. It causes a timeout in the `hDClosed`
argument of `maxTypingAgreeing_correct`. -/
theorem Schema.stratRestrict_DEdge_eq (S : Schema E) (strat : Label → ℕ) (i : ℕ) :
    (S.stratRestrict strat i).DEdge = S.DEdge := rfl

/-- `S.stratRestrict strat i` is also `DClosed`, if `S` is. This is the
`stratRestrict` form of `Schema.stratum_DClosedOn`. It is connected
explicitly with `Schema.stratRestrict_YX_eq_stratum` and
`Schema.stratRestrict_DEdge_eq` (not with `hDClosed` directly), for the
same performance reason as in `Schema.stratRestrict_DEdge_eq`. -/
theorem Schema.stratRestrict_DClosed {S : Schema E} (hDClosed : S.DClosed) (strat : Stratification S)
    (i : ℕ) : (S.stratRestrict strat.strat i).DClosed := by
  intro z hz z' hedge
  rw [Schema.stratRestrict_YX_eq_stratum] at hz ⊢
  rw [Schema.stratRestrict_DEdge_eq] at hedge
  exact Schema.stratum_DClosedOn hDClosed strat i z hz z' hedge

/-! ### `Schema.restrictLabels`: restriction to any label set

Here, `Ls` is any label set. It is not necessarily a stratum
`S.stratum strat i` for a `strat` and an `i` (`Schema.stratRestrict`,
`Proposition1.lean`). -/

/-- The restriction of `S` to a label set `Ls`. The definitions do not
change. -/
def Schema.restrictLabels (S : Schema E) (Ls : Finset Label) : Schema E where
  Y := S.Y ∩ Ls
  X := S.X ∩ Ls
  A := S.A ∩ Ls
  disjointYX := S.disjointYX.mono Finset.inter_subset_left Finset.inter_subset_left
  A_subX := by
    intro z hz
    simp only [Finset.mem_inter] at hz ⊢
    exact ⟨S.A_subX hz.1, hz.2⟩
  shapeDef := S.shapeDef

omit [ShapeSyntax E] in
/-- When `Ls ⊆ Y ∪ X`, the `Y ∪ X` of `restrictLabels Ls` is exactly `Ls`.
This is the general version of `Schema.stratRestrict_YX_eq_stratum`. -/
theorem Schema.restrictLabels_YX_eq {S : Schema E} {Ls : Finset Label}
    (hLs : Ls ⊆ S.Y ∪ S.X) : (S.restrictLabels Ls).Y ∪ (S.restrictLabels Ls).X = Ls := by
  unfold Schema.restrictLabels
  rw [← Finset.union_inter_distrib_right]
  exact Finset.inter_eq_right.mpr hLs

/-- `ExtAcyclic` stays true for each `restrictLabels`. This is the general
version of `Schema.stratRestrict_ExtAcyclic`. -/
theorem Schema.restrictLabels_ExtAcyclic {S : Schema E} (hAcyclic : S.ExtAcyclic)
    (Ls : Finset Label) : (S.restrictLabels Ls).ExtAcyclic := by
  intro x hx
  simp only [Schema.restrictLabels, Finset.mem_inter] at hx
  exact hAcyclic x hx.1

/-- `restrictLabels` does not change the edges of `D_S`. This is the
general version of `Schema.stratRestrict_DEdge_eq`. -/
theorem Schema.restrictLabels_DEdge_eq (S : Schema E) (Ls : Finset Label) :
    (S.restrictLabels Ls).DEdge = S.DEdge := rfl

omit [ShapeSyntax E] in
/-- `(restrictLabels Ls).Y ∪ (restrictLabels Ls).X ⊆ Ls` always. (The
definition uses intersections, so it never adds labels outside `Ls`.) This
changes a hypothesis `∀ z ∈ Ls, ...` into the form
`∀ z ∈ (restrictLabels Ls).Y ∪ (restrictLabels Ls).X, ...` that
`maxTypingAgreeing_correct` needs. -/
theorem Schema.restrictLabels_mem_YX_subset (S : Schema E) (Ls : Finset Label) :
    (S.restrictLabels Ls).Y ∪ (S.restrictLabels Ls).X ⊆ Ls := by
  intro z hz
  simp only [Schema.restrictLabels, Finset.mem_union, Finset.mem_inter] at hz
  rcases hz with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h

/-- `restrictLabels Ls` is also `DClosed` (relative to its own `Y ∪ X`,
which is `Ls` when `Ls ⊆ Y ∪ X`), if `S` is `D_S`-closed on `Ls`.

This is the general version of `Schema.stratRestrict_DClosed`. It is made
in the same way, with the two bridge lemmas above. If you give `hLsClosed`
directly, `whnf` becomes too slow. (Refer to the docstring of
`Schema.stratRestrict_DClosed` in `Proposition1.lean`.) -/
theorem Schema.restrictLabels_DClosed {S : Schema E} {Ls : Finset Label}
    (hLsClosed : S.DClosedOn Ls) (hLsYX : Ls ⊆ S.Y ∪ S.X) :
    (S.restrictLabels Ls).DClosedOn ((S.restrictLabels Ls).Y ∪ (S.restrictLabels Ls).X) := by
  rw [Schema.restrictLabels_YX_eq hLsYX]
  intro z hz z' hedge
  rw [Schema.restrictLabels_DEdge_eq] at hedge
  exact hLsClosed z hz z' hedge

omit [ShapeSyntax E] in
theorem Schema.univTyping_mono {S : Schema E} {G : Graph} {Ls Ls' : Finset Label}
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
`Stratification.le_of_path`, specific to a stratum). If `Ls` is
`D_S`-closed, then each label that `H_S` reaches from a member of `Ls`, in
the two directions, stays in `Ls`. The reason is that `dep-extends` is
symmetric (Definition 5) and is part of `D_S`. -/

/-- `S.anc x ⊆ Ls` if `x ∈ Ls` and `Ls` is `D_S`-closed. This follows
directly from `Schema.ancSet_subset` with `xs = {x}`. -/
theorem Schema.anc_subset_of_DClosedOn {S : Schema E} {Ls : Finset Label} (hLs : S.DClosedOn Ls)
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
of `Schema.anc_subset_of_DClosedOn`. It needs the reversal above, because
the reachability of `Schema.desc` goes in the opposite direction to
`extEdge`. `dep-extends` (and thus `D_S`) does not depend on the
direction. -/
theorem Schema.desc_subset_of_DClosedOn {S : Schema E} {Ls : Finset Label} (hLs : S.DClosedOn Ls)
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
theorem Schema.restrictLabels_anc_eq {S : Schema E} {Ls : Finset Label} (hLsClosed : S.DClosedOn Ls)
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
theorem Schema.restrictLabels_desc_eq {S : Schema E} {Ls : Finset Label} (hLsClosed : S.DClosedOn Ls)
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

end ShexLean.InheritanceCore
