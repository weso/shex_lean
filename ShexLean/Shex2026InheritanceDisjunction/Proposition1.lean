import ShexLean.Shex2026InheritanceDisjunction.CorrectTyping
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
Definitions 7-8 (§4.3) and Proposition 1 of the 2025 paper "Shape
Expressions with Inheritance": stratification, the maximal typing, and its
correctness.

> Definition 7 (stratification). Let `S` be a well-defined schema. A
> stratification of `S` is a function `σ : Y ∪ X → ℕ` such that:
> – if there exists a non-empty path from `z` to `z'` in `D_S`, then
>   `σ(z) ≥ σ(z')`;
> – if there exists in `D_S` a non-empty path from `z` to `z'` that
>   contains an edge corresponding to a negative dependency, then
>   `σ(z) > σ(z')`.
>
> [...] In order to define `τ_max`, we introduce a series of typings
> `τ_1,...,τ_k` such that for every `i ∈ 1..k`, the typing `τ_i` contains
> only shape labels on stratums `j` such that `j ≤ i`. [...]
>
> Definition 8 (maximal typing). [...] For every `1 ≤ i ≤ k`, let `τ_i`
> be the typing of `G` by `S^σ_i` defined inductively by:
> – `τ_1` is the union of all correct typings of `G` by `S^σ_1`;
> – for every `1 ≤ i < k`, `τ_{i+1}` is the union of all correct typings
>   `τ'` which restriction on `Y^σ_i ∪ X^σ_i` is `τ_i`.
>
> The typing `τ_k` is called the maximal typing of `G` by `S` with `σ`
> and is denoted `τ_max(S,σ,G)`.
>
> Proposition 1. For every schema `S`, stratification `σ` of `S`, and
> graph `G`, the typing `τ_max(S,σ,G)` is a correct typing.

The structure of this file is the structure of
`ShexLean/Shex2017Schemas/Proposition1.lean` of the 2017 formalism
(Definitions 3 and 4 there), changed for the new `Schema` and `Satisfies`.
The parts for schema restriction, `maxTypingAgreeing` and `stratTypingSeq`
transfer almost mechanically. They restrict `Y`, `X` and `A` with a stratum
filter, not `.labels`. The abstract-label case of `Schema.CorrectTyping`
goes through with no change.

**The part that does *not* transfer mechanically.** In 2017,
`Satisfies.agree` and `Satisfies.stratMono` are proved by plain structural
recursion on the syntax tree, because `⊢` and `⊨` never dereference `def`.
A shape reference only uses `typing`. Here, `.extends` really dereferences
the *definitions of other labels* (the `ext-te(x)` and `restr(x)` of the
ancestors). Thus, an agreement or monotonicity fact about `Satisfies` must
use the dependency structure of the *schema* (`Schema.dep` and
`depExtends`, through reachability in `D_S`), not only the syntax tree of
one shape expression.

Also, it must use the `Fuel`-indexed definitions on which `Satisfies` is
built (`ShexLean/Shex2026InheritanceDisjunction/Termination.lean`). The
proofs follow the same induction structure (`stableE`, `stableM`,
`stableFuel`), but they record the *agreement of typings on the
dependency closure*, not the sufficiency of fuel.
-/

namespace ShexLean.InheritanceDisjunction

/-- `τ_{|Z}`: the restriction of `τ` to the node-type associations that
have their label in `Z`. This is a local copy of `Typing.restrictTo` of
2017 (`ShexLean/Shex2017Schemas/Proposition1.lean`). Its content is
trivial. We keep it local, so that the `Inheritance` subtree does not have
to import the full 2017 proof chain. It is a plain function, not
`Typing.restrictTo` with dot notation, because `Typing` resolves to the
shared `ShexLean.Typing`, and dot notation looks there first. -/
def restrictTyping (τ : Typing) (Z : Finset Label) : Typing := τ.filter (fun p => p.2 ∈ Z)

theorem mem_restrictTyping {τ : Typing} {Z : Finset Label} {n : RDFNode} {z : Label} :
    (n, z) ∈ restrictTyping τ Z ↔ (n, z) ∈ τ ∧ z ∈ Z := by simp [restrictTyping]

/-- If two typings have the same restriction to `Z`, they agree (as an
`Iff`) on each label in `Z`. -/
theorem restrictTyping_agree {τ τ' : Typing} {Z : Finset Label}
    (h : restrictTyping τ Z = restrictTyping τ' Z) :
    ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ') := by
  intro n z hz
  constructor
  · intro hmem
    have hin : (n, z) ∈ restrictTyping τ Z := mem_restrictTyping.mpr ⟨hmem, hz⟩
    rw [h] at hin; exact (mem_restrictTyping.mp hin).1
  · intro hmem
    have hin : (n, z) ∈ restrictTyping τ' Z := mem_restrictTyping.mpr ⟨hmem, hz⟩
    rw [← h] at hin; exact (mem_restrictTyping.mp hin).1

/-! ### Definition 7: stratification -/

/-- Well-formedness in addition to `WellFormedX` and `WellFormedExtends`:
each label that is `D_S`-reachable from a declared label (`z ∈ Y ∪ X`) is
also declared.

The reason is the same as for `Schema.Closed` of 2017 (refer to the module
docstring of `ShexLean/Shex2017Schemas/Proposition1.lean`). `shapeDef` is
total on all of `Label`. Thus, a schema can refer to a label that is not
declared. But the conditions of `Stratification` must be true only when
the source of the edge is in `Y ∪ X`. -/
def Schema.DClosed (S : Schema) : Prop :=
  ∀ z ∈ S.Y ∪ S.X, ∀ z', S.DEdge z z' → z' ∈ S.Y ∪ S.X

/-- Definition 7 (stratification). It uses the *edges* of `D_S` (`DEdge`
and `DNegEdge`), not the *paths* of the paper. The two forms are
equivalent by induction on the path length.
(`Stratification.lt_of_negPath` below gets the path form.)
`maxTypingAgreeing_correct` (later in the file) needs the edge form. This
definition has exactly the same role as `Stratification` of 2017
(`ShexLean/Shex2017Schemas/Stratification.lean`). -/
structure Stratification (S : Schema) where
  k : ℕ
  strat : Label → ℕ
  mem_range : ∀ z ∈ S.Y ∪ S.X, 1 ≤ strat z ∧ strat z ≤ k
  dep_le : ∀ z ∈ S.Y ∪ S.X, ∀ z', S.DEdge z z' → strat z' ≤ strat z
  negDep_lt : ∀ z ∈ S.Y ∪ S.X, ∀ z', S.DNegEdge z z' → strat z' < strat z

/-- `S` has a stratification (the existence part of Definition 7). The
paper says "well known that stratified negation ... guarantees the
existence of a stratification". The paper says this, but does not prove
it. This file also does not prove it. The 2017 formalization does the
same: `Schema.StratifiedNegation` is only `Nonempty (Stratification S)`,
with no separate existence theorem. -/
def Schema.StratifiedNegation (S : Schema) : Prop := Nonempty (Stratification S)

/-- "`dep` subsumes `dep-shape-neg`/`dep-extra-neg`", applied to `DEdge`.
Each negative edge is also an ordinary `D_S` edge. -/
theorem Schema.DEdge_of_DNegEdge {S : Schema} {z z' : Label} (h : S.DNegEdge z z') :
    S.DEdge z z' := by
  rcases h with h | h
  · exact Or.inl (Schema.dep_of_depShapeNeg h)
  · exact Or.inl (Schema.dep_of_depExtraNeg h)

/-- Membership in `Y ∪ X` continues forward along each `D_S` path, if
`Schema.DClosed` is true. -/
theorem Schema.mem_of_reach {S : Schema} (hDClosed : S.DClosed) {z z' : Label}
    (hzY : z ∈ S.Y ∪ S.X) (h : Relation.ReflTransGen S.DEdge z z') : z' ∈ S.Y ∪ S.X := by
  induction h with
  | refl => exact hzY
  | tail _ hstep ih => exact hDClosed _ ih _ hstep

/-- `strat` never increases along a `D_S` path (the first bullet of
Definition 7, in path form). -/
theorem Stratification.le_of_path {S : Schema} (hDClosed : S.DClosed) (strat : Stratification S)
    {z z' : Label} (hzY : z ∈ S.Y ∪ S.X) (h : Relation.ReflTransGen S.DEdge z z') :
    strat.strat z' ≤ strat.strat z := by
  induction h with
  | refl => exact le_refl _
  | tail hprev hstep ih => exact le_trans (strat.dep_le _ (S.mem_of_reach hDClosed hzY hprev) _ hstep) ih

/-- Take a `D_S` path from `z` to `z'` that goes through a negative edge
`a → b` (`z ↝ a`, `a → b` negative, `b ↝ z'`). Along this path, `strat`
decreases strictly in total (the second bullet of Definition 7, in path
form). The proof applies `le_of_path` on each side of the strict step
`negDep_lt` in the middle. -/
theorem Stratification.lt_of_negPath {S : Schema} (hDClosed : S.DClosed)
    (strat : Stratification S) {z a b z' : Label} (hzY : z ∈ S.Y ∪ S.X)
    (hza : Relation.ReflTransGen S.DEdge z a) (hab : S.DNegEdge a b)
    (hbz' : Relation.ReflTransGen S.DEdge b z') :
    strat.strat z' < strat.strat z := by
  have haY : a ∈ S.Y ∪ S.X := S.mem_of_reach hDClosed hzY hza
  have hbY : b ∈ S.Y ∪ S.X := hDClosed a haY b (S.DEdge_of_DNegEdge hab)
  calc strat.strat z' ≤ strat.strat b := strat.le_of_path hDClosed hbY hbz'
    _ < strat.strat a := strat.negDep_lt a haY b hab
    _ ≤ strat.strat z := strat.le_of_path hDClosed hzY hza

/-! ### An agreement lemma for `Satisfies`

`⊢` and `⊨` depend on `τ` only through its restriction to a set of labels
`Z` with two properties:

* `Z` is *closed* under `D_S` (`Schema.DClosedOn` below).
* `Z` contains all that the shape expression can reach syntactically
  (`ShapeExpr.depsIn`).

This is the 2025 version of `Satisfies.agree` of 2017
(`ShexLean/Shex2017Schemas/Proposition1.lean`). Now it must use the
dependency structure of the *schema*, because `.extends` dereferences the
definitions of other labels. It uses the `Fuel`-indexed definitions on
which `Satisfies` is built. It follows exactly the same one-way chain
(`agreeE → agreeM_noExtends`/`agreeM → agreeFuel`) as
`stableE → stableM_noExtends/stableM → stableFuel` in
`ShexLean/Shex2026InheritanceDisjunction/Termination.lean`. -/

/-- The labels that a shape expression can reach:

* The `@z'` references at any location in it (`ShapeExpr.depsAux`).
* The `extends` targets at any location in it
  (`ShapeExpr.extendsTargets`, now a full recursive walk. Refer to the
  docstring of that definition to know why it must be one.) -/
def ShapeExpr.depsIn (s : ShapeExpr) (Z : Finset Label) : Prop :=
  (s.depsAux false).refs ⊆ Z ∧ s.extendsTargets ⊆ Z

/-- One more well-formedness condition that `stratMono` needs, in addition
to `WellFormedX`, `WellFormedExtends` and `WellFormedExtra`: a `not` never
contains an `extends`.

Without it, the `not` case of `stratMono` needs *exact* agreement between
`τ` and `τ'` on each ancestor that an `extends` inside the negated content
can reach. But these ancestors are not necessarily in `Lo`, because
`dep-extends` is intentionally never a *negative* dependency
(Definition 5). Thus, the hypotheses of `stratMono` do not bound them.

This agrees with the "Design choices" discussion of the paper. That
discussion already restricts `extends` to conjunctions, to prevent this
type of complexity (there with `or`, here with `not`). No example of the
paper uses this case. With this condition, the content of a `not` is
always `NoExtends`. Thus, the `not` case of `stratMono` can use
`stratMonoM_noExtends` directly. It does not need a fully general
`stratMonoM` below `not`. (This file did not find that such a general
result is clearly true.) -/
def ShapeExpr.NotIsExtendsFree : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends _ _ => True
  | .or s1 s2 => s1.NotIsExtendsFree ∧ s2.NotIsExtendsFree
  | .and s1 s2 => s1.NotIsExtendsFree ∧ s2.NotIsExtendsFree
  | .not s => s.NoExtends

/-- The same condition for the full schema: the full definition of each
label. -/
def Schema.NotIsExtendsFree (S : Schema) : Prop := ∀ ℓ, (S.shapeDef ℓ).NotIsExtendsFree

/-- A `NoExtends` shape has no `extends` targets at any location, by
construction. (`extendsTargets` gives a nonempty result only at an
`.extends` node, and `NoExtends` excludes all such nodes.) -/
theorem ShapeExpr.NoExtends.extendsTargets_empty {s : ShapeExpr} (hs : s.NoExtends) :
    s.extendsTargets = ∅ := by
  induction s with
  | constraint _ => rfl
  | ofShape _ => rfl
  | «extends» _ _ => simp only [ShapeExpr.NoExtends] at hs
  | or s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.NoExtends] at hs
      simp only [ShapeExpr.extendsTargets, ih1 hs.1, ih2 hs.2, Finset.empty_union]
  | and s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.NoExtends] at hs
      simp only [ShapeExpr.extendsTargets, ih1 hs.1, ih2 hs.2, Finset.empty_union]
  | not s ih => simp only [ShapeExpr.extendsTargets]; exact ih hs

/-- `.refs` never depends on `neg` (only `.negRefs` does). Thus, a fact
`refs ⊆ Z` stays true across the change of `neg` that `.not` does. -/
theorem ShapeExpr.depsAux_refs_indep (s : ShapeExpr) (neg1 neg2 : Bool) :
    (s.depsAux neg1).refs = (s.depsAux neg2).refs := by
  induction s generalizing neg1 neg2 with
  | constraint c => simp [ShapeExpr.depsAux]
  | ofShape h => simp [ShapeExpr.depsAux, Shape.depInfo]
  | «extends» xs hs => exact Shape.listDepInfo_refs_indep hs neg1 neg2
  | or s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_refs]; rw [ih1 neg1 neg2, ih2 neg1 neg2]
  | and s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_refs]; rw [ih1 neg1 neg2, ih2 neg1 neg2]
  | not s _ => simp only [ShapeExpr.depsAux]

/-- The labels that the triple constraints of a triple expression refer
to. -/
def TripleExpr.refs (e : TripleExpr) : Finset Label := e.tcs.image Prod.snd

/-- `Z` is closed under `D_S`: each label that a member of `Z` depends on
(`dep` or `depExtends`) is also in `Z`. This is a general form of
`Schema.DClosed` (the case `Z = Y ∪ X`) for any label set. Proposition 1
below needs it for `Z = ` a stratum, not only for the full schema. -/
def Schema.DClosedOn (S : Schema) (Z : Finset Label) : Prop :=
  ∀ z ∈ Z, ∀ z', S.DEdge z z' → z' ∈ Z

/-- Membership in a `D_S`-closed `Z` continues along each `D_S` path. This
is a general form of `Schema.mem_of_reach`, which is now the instance
`Z = Y ∪ X` of this lemma. -/
theorem Schema.reach_mem {S : Schema} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {z z' : Label} (hz : z ∈ Z) (h : Relation.ReflTransGen S.DEdge z z') : z' ∈ Z := by
  induction h with
  | refl => exact hz
  | tail _ hstep ih => exact hZ _ ih _ hstep

/-- If `x ∈ Z` and `Z` is `D_S`-closed, then the definition of `x` reaches
only labels in `Z`. Thus, the closure of `Z` is exactly what is necessary
to do the recursion one more `extends` step deep and stay in `Z`. -/
theorem Schema.shapeDef_depsIn {S : Schema} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {x : Label} (hx : x ∈ Z) : (S.shapeDef x).depsIn Z :=
  ⟨fun _ hz' => hZ x hx _ (Or.inl hz'), fun _ hz' => hZ x hx _ (Or.inr (Or.inl hz'))⟩

/-- `S.ancSet xs ⊆ Z` if `xs ⊆ Z` and `Z` is `D_S`-closed. Each ancestor
that a rule-18 partition reaches also stays in `Z`. -/
theorem Schema.ancSet_subset {S : Schema} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {xs : Finset Label} (hxs : xs ⊆ Z) : S.ancSet xs ⊆ Z := by
  intro x hx
  unfold Schema.ancSet at hx
  obtain ⟨y, hy, hyx⟩ := Finset.mem_biUnion.mp hx
  unfold Schema.anc at hyx
  simp only [Finset.mem_filter] at hyx
  have hstep : Relation.ReflTransGen S.DEdge y x :=
    Relation.ReflTransGen.mono (fun _ _ hab => Or.inr (Or.inl hab)) y x hyx.2
  exact S.reach_mem hZ (hxs hy) hstep

/-- Each label in `S.ancSet xs` is in `S.X`. (This follows directly from
the definition of `Schema.anc`, which filters over `S.X`.) -/
theorem Schema.mem_ancSet_mem_X {S : Schema} {xs : Finset Label} {x : Label}
    (hx : x ∈ S.ancSet xs) : x ∈ S.X := by
  unfold Schema.ancSet at hx
  obtain ⟨y, _, hyx⟩ := Finset.mem_biUnion.mp hx
  unfold Schema.anc at hyx
  simp only [Finset.mem_filter] at hyx
  exact hyx.1

/-- `SatisfiesEFuel` (Table 1) depends on `τ` only through its restriction
to `Z`, if the references of `e` are `⊆ Z`. No schema-closure hypothesis
is necessary, because Table 1 never does a schema lookup, exactly as in
`stableE`. -/
theorem agreeE {S : Schema} {G : Graph} {τ τ' : Typing} {Z : Finset Label}
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) :
    ∀ (e : TripleExpr), e.refs ⊆ Z →
      ∀ fuel (M : Finset Triple), SatisfiesEFuel fuel S G τ M e ↔ SatisfiesEFuel fuel S G τ' M e := by
  intro e
  induction e with
  | empty => intro _ fuel M; rcases fuel with _ | f <;> rfl
  | tc p z =>
      intro href fuel M
      rcases fuel with _ | f
      · rfl
      have hzZ : z ∈ Z := href (by simp [TripleExpr.refs, TripleExpr.tcs])
      show (∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z) ↔
        (∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ'.has o z)
      constructor
      · rintro ⟨n, o, hM, ht⟩; exact ⟨n, o, hM, (hagree o z hzZ).mp ht⟩
      · rintro ⟨n, o, hM, ht⟩; exact ⟨n, o, hM, (hagree o z hzZ).mpr ht⟩
  | choice e1 e2 ih1 ih2 =>
      intro href fuel M
      rcases fuel with _ | f
      · rfl
      simp only [TripleExpr.refs, TripleExpr.tcs, Finset.image_union, Finset.union_subset_iff]
        at href
      show SatisfiesEFuel f S G τ M e1 ∨ SatisfiesEFuel f S G τ M e2 ↔
        SatisfiesEFuel f S G τ' M e1 ∨ SatisfiesEFuel f S G τ' M e2
      rw [ih1 href.1 f M, ih2 href.2 f M]
  | seq e1 e2 ih1 ih2 =>
      intro href fuel M
      rcases fuel with _ | f
      · rfl
      simp only [TripleExpr.refs, TripleExpr.tcs, Finset.image_union, Finset.union_subset_iff]
        at href
      show (∃ M1 M2, DisjointUnion M M1 M2 ∧
            SatisfiesEFuel f S G τ M1 e1 ∧ SatisfiesEFuel f S G τ M2 e2) ↔
          (∃ M1 M2, DisjointUnion M M1 M2 ∧
            SatisfiesEFuel f S G τ' M1 e1 ∧ SatisfiesEFuel f S G τ' M2 e2)
      constructor
      · rintro ⟨M1, M2, hdu, h1, h2⟩
        exact ⟨M1, M2, hdu, (ih1 href.1 f M1).mp h1, (ih2 href.2 f M2).mp h2⟩
      · rintro ⟨M1, M2, hdu, h1, h2⟩
        exact ⟨M1, M2, hdu, (ih1 href.1 f M1).mpr h1, (ih2 href.2 f M2).mpr h2⟩
  | star e ih =>
      intro href fuel M
      rcases fuel with _ | f
      · rfl
      show (∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧
            ∀ Ni ∈ Ns, SatisfiesEFuel f S G τ Ni e) ↔
          (∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧
            ∀ Ni ∈ Ns, SatisfiesEFuel f S G τ' Ni e)
      constructor
      · rintro ⟨Ns, hdu, hall⟩
        exact ⟨Ns, hdu, fun Ni hNi => (ih href f Ni).mp (hall Ni hNi)⟩
      · rintro ⟨Ns, hdu, hall⟩
        exact ⟨Ns, hdu, fun Ni hNi => (ih href f Ni).mpr (hall Ni hNi)⟩

/-- `M^e` (the `Me` of Table 3) does not only agree for `τ` and `τ'`. It is
*exactly equal*, if they agree on the references of `e`. The membership
test of each triple uses `τ` only on a label in `e.refs ⊆ Z`. For this
reason, the agreement case of rule 17 (in `agreeM` below) can use `agreeE`
directly at a *shared* `M^e`, with no more congruence argument. -/
theorem Me_eq {τ τ' : Typing} {Z : Finset Label}
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) {e : TripleExpr} (href : e.refs ⊆ Z)
    (M : Finset Triple) : Me τ M e = Me τ' M e := by
  unfold Me
  have := Classical.decPred (fun t : Triple => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)
  have := Classical.decPred (fun t : Triple => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ'.has t.obj z)
  apply Finset.ext
  intro t
  simp only [Finset.mem_filter]
  have hzZ : ∀ z, (t.pred, z) ∈ e.tcs → z ∈ Z := fun z hz => href (by
    simp only [TripleExpr.refs]; exact Finset.mem_image.mpr ⟨(t.pred, z), hz, rfl⟩)
  constructor
  · rintro ⟨htM, z, hz, htyp⟩; exact ⟨htM, z, hz, (hagree t.obj z (hzZ z hz)).mp htyp⟩
  · rintro ⟨htM, z, hz, htyp⟩; exact ⟨htM, z, hz, (hagree t.obj z (hzZ z hz)).mpr htyp⟩

/-- `M^{e'}` (the `Mnotin` of Table 3) is also exactly equal. It is made
from `Me` (equal by `Me_eq`) and from a filter on `props`, which does not
use `τ`. -/
theorem Mnotin_eq {τ τ' : Typing} {Z : Finset Label}
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) {e : TripleExpr} (href : e.refs ⊆ Z)
    (M : Finset Triple) : Mnotin τ M e = Mnotin τ' M e := by
  unfold Mnotin
  rw [Me_eq hagree href M]

/-- `SatisfiesMFuel` (Table 3) depends on `τ` only through its restriction
to `Z`, on each `NoExtends` shape. The condition "the references of `u`
are `⊆ Z`" is sufficient. No schema-closure hypothesis is necessary,
because `u` never uses rule 18.

We prove it *before* the general case, for the same reason as
`stableM_noExtends`. The evaluation of `restr(x)` (in the `.extends` case
of `agreeM`) is not on a subterm of the shape of the induction. Thus, the
induction hypothesis cannot reach it, and the proof uses this lemma in
its place. -/
theorem agreeM_noExtends {S : Schema} {G : Graph} {τ τ' : Typing} {Z : Finset Label}
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) :
    ∀ (u : ShapeExpr), u.NoExtends → (u.depsAux false).refs ⊆ Z →
      ∀ fuel (M : Finset Triple), SatisfiesMFuel fuel S G τ M u ↔ SatisfiesMFuel fuel S G τ' M u := by
  intro u
  induction u with
  | constraint c => intro _ _ fuel M; rcases fuel with _ | f <;> rfl
  | ofShape h =>
      intro _ href fuel M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.depsAux, Shape.depInfo] at href
      have hTrefs : h.triples.refs ⊆ Z := by simpa [TripleExpr.refs] using href
      show (SatisfiesEFuel f S G τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)) ↔
          (SatisfiesEFuel f S G τ' (Me τ' M h.triples) h.triples ∧
            props (Mnotin τ' M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅))
      rw [Me_eq hagree hTrefs M, Mnotin_eq hagree hTrefs M,
        agreeE hagree h.triples hTrefs f (Me τ' M h.triples)]
  | «extends» xs h => intro hu; simp only [ShapeExpr.NoExtends] at hu
  | or s1 s2 ih1 ih2 =>
      intro hu href fuel M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.NoExtends] at hu
      simp only [ShapeExpr.depsAux, DepInfo.union_refs, Finset.union_subset_iff] at href
      show SatisfiesMFuel f S G τ M s1 ∨ SatisfiesMFuel f S G τ M s2 ↔
        SatisfiesMFuel f S G τ' M s1 ∨ SatisfiesMFuel f S G τ' M s2
      rw [ih1 hu.1 href.1 f M, ih2 hu.2 href.2 f M]
  | and s1 s2 ih1 ih2 =>
      intro hu href fuel M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.NoExtends] at hu
      simp only [ShapeExpr.depsAux, DepInfo.union_refs, Finset.union_subset_iff] at href
      show SatisfiesMFuel f S G τ M s1 ∧ SatisfiesMFuel f S G τ M s2 ↔
        SatisfiesMFuel f S G τ' M s1 ∧ SatisfiesMFuel f S G τ' M s2
      rw [ih1 hu.1 href.1 f M, ih2 hu.2 href.2 f M]
  | not s ih =>
      intro hu href fuel M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.NoExtends] at hu
      simp only [ShapeExpr.depsAux] at href
      rw [s.depsAux_refs_indep true false] at href
      show ¬ SatisfiesMFuel f S G τ M s ↔ ¬ SatisfiesMFuel f S G τ' M s
      rw [ih hu href f M]

/-- The references of `ext-te(x)`, at *each* selected disjunct index, are
in the references of `def(x)`. This is the `refs`-containment version of
`extTeAt_size_le` in `Termination.lean`. -/
theorem extTeAt_refs_subset {S : Schema} (hWFX : S.WellFormedX) {x : Label} (hx : x ∈ S.X)
    (i : ℕ) : ((S.shapeDef x).extTeAt i).refs ⊆ ((S.shapeDef x).depsAux false).refs := by
  obtain ⟨xs', hs', -, hcase⟩ := hWFX x hx
  rcases ShapeExpr.extTeAt_mem_or_empty (S.shapeDef x) i with hempty | ⟨e, hmem, heq⟩
  · rw [hempty]; simp [TripleExpr.refs, TripleExpr.tcs]
  · rw [heq]
    rcases hcase with heq' | ⟨u, heq'⟩ <;> rw [heq'] at hmem ⊢ <;>
      unfold ShapeExpr.extTeList at hmem <;> simp only [ShapeExpr.depsAux]
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hmem
      exact Shape.triples_refs_subset_listDepInfo_refs hh false
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hmem
      simp only [DepInfo.union_refs]
      exact Finset.Subset.trans (Shape.triples_refs_subset_listDepInfo_refs hh false)
        Finset.subset_union_left

/-- The references of `restr(x)` are in the references of `def(x)`. This is
the `refs`-containment version of `restrOf_noExtends_and_size_le` in
`Termination.lean`. -/
theorem restrOf_refs_subset {S : Schema} {x : Label} {u : ShapeExpr}
    (hu : (S.shapeDef x).restrOf = some u) :
    (u.depsAux false).refs ⊆ ((S.shapeDef x).depsAux false).refs := by
  generalize hg : S.shapeDef x = e at hu
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' hs' =>
          simp only [ShapeExpr.restrOf] at hu
          obtain rfl := Option.some.inj hu
          simp only [ShapeExpr.depsAux, DepInfo.union_refs]
          exact Finset.subset_union_right
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- The negative references of `restr(x)` are in the negative references
of `def(x)`. -/
theorem restrOf_negRefs_subset {S : Schema} {x : Label} {u : ShapeExpr}
    (hu : (S.shapeDef x).restrOf = some u) :
    (u.depsAux false).negRefs ⊆ ((S.shapeDef x).depsAux false).negRefs := by
  generalize hg : S.shapeDef x = e at hu
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' hs' =>
          simp only [ShapeExpr.restrOf] at hu
          obtain rfl := Option.some.inj hu
          simp only [ShapeExpr.depsAux, DepInfo.union_negRefs]
          exact Finset.subset_union_right
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- `SatisfiesMFuel` (Table 3) depends on `τ` only through its restriction
to `Z`, if `s.depsIn Z` and `Z` is `D_S`-closed.

Each case except `.extends` is a copy of `agreeM_noExtends`, with the two
components of `depsIn` in place of only `.refs`. The `.extends` case
combines `agreeE` (for `h.triples` and `ext-te(x)`) with
`agreeM_noExtends` (for `restr(x)`, with `restrOf_refs_subset` and
`WellFormedExtends`). This has exactly the same structure as the
`.extends` case of `stableM` in `Termination.lean`. -/
theorem agreeM {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    {G : Graph} {τ τ' : Typing} {Z : Finset Label} (hZ : S.DClosedOn Z)
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) :
    ∀ (s : ShapeExpr), s.depsIn Z →
      ∀ fuel (M : Finset Triple), SatisfiesMFuel fuel S G τ M s ↔ SatisfiesMFuel fuel S G τ' M s := by
  intro s
  induction s with
  | constraint c => intro _ fuel M; rcases fuel with _ | f <;> rfl
  | ofShape h =>
      intro hdeps fuel M
      rcases fuel with _ | f
      · rfl
      have hTrefs : h.triples.refs ⊆ Z := by
        simpa [ShapeExpr.depsIn, ShapeExpr.depsAux, Shape.depInfo, TripleExpr.refs] using hdeps.1
      show (SatisfiesEFuel f S G τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)) ↔
          (SatisfiesEFuel f S G τ' (Me τ' M h.triples) h.triples ∧
            props (Mnotin τ' M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅))
      rw [Me_eq hagree hTrefs M, Mnotin_eq hagree hTrefs M,
        agreeE hagree h.triples hTrefs f (Me τ' M h.triples)]
  | «extends» xs hs =>
      intro hdeps fuel M
      rcases fuel with _ | f
      · rfl
      obtain ⟨hrefsZ, hxsZ⟩ := hdeps
      simp only [ShapeExpr.extendsTargets] at hxsZ
      have hancZ : S.ancSet xs ⊆ Z := S.ancSet_subset hZ hxsZ
      show (∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
            (∃ h ∈ hs, SatisfiesMFuel f S G τ M' (.ofShape h)) ∧
            (∀ x ∈ S.ancSet xs,
              SatisfiesEFuel f S G τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ∧
            (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
              SatisfiesMFuel f S G τ ((S.anc x).biUnion Mx) u)) ↔
          (∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
            (∃ h ∈ hs, SatisfiesMFuel f S G τ' M' (.ofShape h)) ∧
            (∀ x ∈ S.ancSet xs,
              SatisfiesEFuel f S G τ' (Mx x) ((S.shapeDef x).extTeAt (pick x))) ∧
            (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
              SatisfiesMFuel f S G τ' ((S.anc x).biUnion Mx) u))
      refine exists_congr fun M' => exists_congr fun Mx => exists_congr fun pick =>
        and_congr_right fun _ => ?_
      have he : (∃ h ∈ hs, SatisfiesMFuel f S G τ M' (.ofShape h)) ↔
          (∃ h ∈ hs, SatisfiesMFuel f S G τ' M' (.ofShape h)) :=
        exists_congr fun h => and_congr_right fun hmem =>
          agreeM_noExtends hagree (.ofShape h) trivial
            (Finset.Subset.trans (Shape.triples_refs_subset_listDepInfo_refs hmem false) hrefsZ)
            f M'
      have hext : (∀ x ∈ S.ancSet xs,
            SatisfiesEFuel f S G τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ↔
          (∀ x ∈ S.ancSet xs,
            SatisfiesEFuel f S G τ' (Mx x) ((S.shapeDef x).extTeAt (pick x))) := by
        refine forall_congr' fun x => forall_congr' fun hx => ?_
        have hxX : x ∈ S.X := Schema.mem_ancSet_mem_X hx
        have hxZ : x ∈ Z := hancZ hx
        exact agreeE hagree ((S.shapeDef x).extTeAt (pick x))
          (Finset.Subset.trans (extTeAt_refs_subset hWFX hxX (pick x))
            (S.shapeDef_depsIn hZ hxZ).1) f (Mx x)
      have hrestr : (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
            SatisfiesMFuel f S G τ ((S.anc x).biUnion Mx) u) ↔
          (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
            SatisfiesMFuel f S G τ' ((S.anc x).biUnion Mx) u) := by
        refine forall_congr' fun x => forall_congr' fun hx => forall_congr' fun u => ?_
        refine imp_congr_right fun hru => ?_
        have hxZ : x ∈ Z := hancZ hx
        have hNoExt : u.NoExtends := (restrOf_noExtends_and_size_le hWFExt hru).1
        have hurefs : (u.depsAux false).refs ⊆ Z :=
          Finset.Subset.trans (restrOf_refs_subset hru) (S.shapeDef_depsIn hZ hxZ).1
        exact agreeM_noExtends hagree u hNoExt hurefs f _
      rw [he, hext, hrestr]
  | or s1 s2 ih1 ih2 =>
      intro hdeps fuel M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      show SatisfiesMFuel f S G τ M s1 ∨ SatisfiesMFuel f S G τ M s2 ↔
        SatisfiesMFuel f S G τ' M s1 ∨ SatisfiesMFuel f S G τ' M s2
      rw [ih1 ⟨hdeps.1.1, hdeps.2.1⟩ f M, ih2 ⟨hdeps.1.2, hdeps.2.2⟩ f M]
  | and s1 s2 ih1 ih2 =>
      intro hdeps fuel M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      show SatisfiesMFuel f S G τ M s1 ∧ SatisfiesMFuel f S G τ M s2 ↔
        SatisfiesMFuel f S G τ' M s1 ∧ SatisfiesMFuel f S G τ' M s2
      rw [ih1 ⟨hdeps.1.1, hdeps.2.1⟩ f M, ih2 ⟨hdeps.1.2, hdeps.2.2⟩ f M]
  | not s ih =>
      intro hdeps fuel M
      rcases fuel with _ | f
      · rfl
      have hdeps' : s.depsIn Z := by
        refine ⟨?_, ?_⟩
        · rw [s.depsAux_refs_indep false true]
          simpa [ShapeExpr.depsAux] using hdeps.1
        · simpa [ShapeExpr.extendsTargets] using hdeps.2
      show ¬ SatisfiesMFuel f S G τ M s ↔ ¬ SatisfiesMFuel f S G τ' M s
      rw [ih hdeps' f M]

/-- `SatisfiesFuel` (Table 2) on a `NoExtends` shape. No schema-closure
hypothesis is necessary. This is exactly the same as `agreeM_noExtends`,
which does the inner Table 3 check of `.ofShape`. (`.extends` is not
possible with `NoExtends`.)

The `.not` case of `stratMonoFuel` needs this lemma. (By
`ShapeExpr.NotIsExtendsFree`, the content of a `not` node is always
`NoExtends`.) Without this lemma, that case must use the much heavier
`agreeFuel` below, with its `DClosedOn` and schema-wide agreement
requirements. A `NoExtends` shape never needs these requirements. -/
theorem agreeFuel_noExtends {S : Schema} {G : Graph} {τ τ' : Typing} {Z : Finset Label}
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) :
    ∀ (s : ShapeExpr), s.NoExtends → (s.depsAux false).refs ⊆ Z →
      ∀ fuel (n : RDFNode), SatisfiesFuel fuel S G τ n s ↔ SatisfiesFuel fuel S G τ' n s := by
  intro s
  induction s with
  | constraint c =>
      intro _ _ fuel n
      rcases fuel with _ | f
      · rfl
      · rfl
  | ofShape h =>
      intro _ href fuel n
      rcases fuel with _ | f
      · rfl
      exact agreeM_noExtends hagree (.ofShape h) trivial href f (neigh G n)
  | «extends» xs h => intro hu; simp only [ShapeExpr.NoExtends] at hu
  | or s1 s2 ih1 ih2 =>
      intro hu href fuel n
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.NoExtends] at hu
      simp only [ShapeExpr.depsAux, DepInfo.union_refs, Finset.union_subset_iff] at href
      show SatisfiesFuel f S G τ n s1 ∨ SatisfiesFuel f S G τ n s2 ↔
        SatisfiesFuel f S G τ' n s1 ∨ SatisfiesFuel f S G τ' n s2
      rw [ih1 hu.1 href.1 f n, ih2 hu.2 href.2 f n]
  | and s1 s2 ih1 ih2 =>
      intro hu href fuel n
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.NoExtends] at hu
      simp only [ShapeExpr.depsAux, DepInfo.union_refs, Finset.union_subset_iff] at href
      show SatisfiesFuel f S G τ n s1 ∧ SatisfiesFuel f S G τ n s2 ↔
        SatisfiesFuel f S G τ' n s1 ∧ SatisfiesFuel f S G τ' n s2
      rw [ih1 hu.1 href.1 f n, ih2 hu.2 href.2 f n]
  | not s ih =>
      intro hu href fuel n
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.NoExtends] at hu
      simp only [ShapeExpr.depsAux] at href
      rw [s.depsAux_refs_indep true false] at href
      show ¬ SatisfiesFuel f S G τ n s ↔ ¬ SatisfiesFuel f S G τ' n s
      rw [ih hu href f n]

/-- `SatisfiesFuel` (Table 2) depends on `τ` only through its restriction
to `Z`, if `s.depsIn Z` and `Z` is `D_S`-closed. The `.ofShape` and
`.extends` cases follow directly from `agreeM`. Each other case is
self-recursion, with exactly the same structure as `stableFuel`. -/
theorem agreeFuel {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    {G : Graph} {τ τ' : Typing} {Z : Finset Label} (hZ : S.DClosedOn Z)
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) :
    ∀ (s : ShapeExpr), s.depsIn Z →
      ∀ fuel (n : RDFNode), SatisfiesFuel fuel S G τ n s ↔ SatisfiesFuel fuel S G τ' n s := by
  intro s
  induction s with
  | constraint c => intro _ fuel n; rcases fuel with _ | f <;> rfl
  | ofShape h =>
      intro hdeps fuel n
      rcases fuel with _ | f
      · rfl
      show SatisfiesMFuel f S G τ (neigh G n) (.ofShape h) ↔
        SatisfiesMFuel f S G τ' (neigh G n) (.ofShape h)
      exact agreeM hWFX hWFExt hZ hagree (.ofShape h) hdeps f (neigh G n)
  | «extends» xs h =>
      intro hdeps fuel n
      rcases fuel with _ | f
      · rfl
      show SatisfiesMFuel f S G τ (neigh G n) (.extends xs h) ↔
        SatisfiesMFuel f S G τ' (neigh G n) (.extends xs h)
      exact agreeM hWFX hWFExt hZ hagree (.extends xs h) hdeps f (neigh G n)
  | or s1 s2 ih1 ih2 =>
      intro hdeps fuel n
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      show SatisfiesFuel f S G τ n s1 ∨ SatisfiesFuel f S G τ n s2 ↔
        SatisfiesFuel f S G τ' n s1 ∨ SatisfiesFuel f S G τ' n s2
      rw [ih1 ⟨hdeps.1.1, hdeps.2.1⟩ f n, ih2 ⟨hdeps.1.2, hdeps.2.2⟩ f n]
  | and s1 s2 ih1 ih2 =>
      intro hdeps fuel n
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      show SatisfiesFuel f S G τ n s1 ∧ SatisfiesFuel f S G τ n s2 ↔
        SatisfiesFuel f S G τ' n s1 ∧ SatisfiesFuel f S G τ' n s2
      rw [ih1 ⟨hdeps.1.1, hdeps.2.1⟩ f n, ih2 ⟨hdeps.1.2, hdeps.2.2⟩ f n]
  | not s ih =>
      intro hdeps fuel n
      rcases fuel with _ | f
      · rfl
      have hdeps' : s.depsIn Z := by
        refine ⟨?_, ?_⟩
        · rw [s.depsAux_refs_indep false true]
          simpa [ShapeExpr.depsAux] using hdeps.1
        · simpa [ShapeExpr.extendsTargets] using hdeps.2
      show ¬ SatisfiesFuel f S G τ n s ↔ ¬ SatisfiesFuel f S G τ' n s
      rw [ih hdeps' f n]

/-- The version of `Satisfies.agree` for the real `Satisfies` (with no
fuel). `reqFuel S s` does not depend on `τ`. Thus, `Satisfies S G τ n s`
and `Satisfies S G τ' n s` use the *same* concrete fuel value, and this is
`agreeFuel` at that shared value. -/
theorem Satisfies.agree {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    {G : Graph} {τ τ' : Typing} {Z : Finset Label} (hZ : S.DClosedOn Z)
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) {s : ShapeExpr} (hdeps : s.depsIn Z)
    (n : RDFNode) : Satisfies S G τ n s ↔ Satisfies S G τ' n s :=
  agreeFuel hWFX hWFExt hZ hagree s hdeps (ShapeExpr.reqFuel S s + 1) n

/-! ### A problem that `stratMono` has here, and that it did not have in 2017

Rule 17 of Table 3 filters the neighbourhood through `Me` and `Mnotin`:
the part of `M` that is "already correctly typed", and the "leftover"
part. These parts are computed *from `τ`*. This makes `SatisfiesMFuel`
and `Satisfies` really **not monotone** in `τ`, also with no negation at
any location.

When `τ` becomes larger, a triple can go from `Mnotin` into `Me`. If `Me`
already matched a *plain* (not starred) triple constraint such as `p @z`
(which needs `M` to be *exactly* a singleton), then the match fails when
`Me` has more than one element.

We checked a concrete example of this directly in Lean before we wrote
this section. Take the shape
`⟨closed := false, extra := some {p}, triples := p @z⟩`:

* With `τ₁ = {(t1.obj, z)}`, `M = {t1, t2}` satisfies it. Here,
  `Me = {t1}`, which is a singleton.
* With `τ₂ = τ₁ ∪ {(t2.obj, z)} ⊇ τ₁`, `M` does not satisfy it. Here, `Me`
  becomes `{t1, t2}`, which is not a singleton.

The appendix proof of Proposition 1 in the paper needs, and gives, exactly
the fix for this. It is an auxiliary invariant that the paper calls "(*)":
*for each sub-expression `[closed][extra P]⟨e⟩`, and for each
`p @u ∈ tcs(e)`, `p ∉ P`*. Thus, the properties of the triple constraints
of a shape never overlap its `extra` set.

The main text of the paper never gives this invariant as a separate
definition. Only the proof of Proposition 1 uses it. Thus, as
`Schema.WellFormedExtends` in `Termination.lean`, this file adds it as an
explicit hypothesis, `Schema.WellFormedExtra`.

*Why it fixes the problem.* With `(*)`, when a shape succeeds, the success
condition of `Mnotin` (`props(Mnotin) ⊆ P`) forces each triple in `M` that
matches `props(e)` to be already in `Me`. (No such triple can be a
"leftover" through `extra`, because `(*)` says that `extra` never covers
the properties of `e`.) Thus, `Me` already has its *maximal possible*
value, `M.filter (pred ∈ props e)`, which does not use `τ`. When `Me` is at
this maximum, it cannot become larger, for all the additions to `τ`. This
is exactly what gives monotonicity again for the positive uses of `Me` in
Table 3 (the uses that do not misuse `extra`). -/

/-- The implicit invariant "(*)" of Definition 5: the triple constraints of
a shape never use a property that is also in its `extra` set. -/
def Shape.WellFormedExtra (h : Shape) : Prop := h.triples.props ∩ h.extra.getD ∅ = ∅

/-- "(*)" for each shape at any location in a `ShapeExpr`: each `.ofShape`,
and *each* disjunct of the `hs` of an `.extends` (because `pick` can select
any of them). This applies at all locations, also when they are nested in
`or`, `and`, `not` or a restriction. -/
def ShapeExpr.WellFormedExtra : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape h => h.WellFormedExtra
  | .extends _ hs => ∀ h ∈ hs, h.WellFormedExtra
  | .or s1 s2 => s1.WellFormedExtra ∧ s2.WellFormedExtra
  | .and s1 s2 => s1.WellFormedExtra ∧ s2.WellFormedExtra
  | .not s => s.WellFormedExtra

/-- "(*)" for the full schema: the full definition of each label. -/
def Schema.WellFormedExtra (S : Schema) : Prop := ∀ ℓ, (S.shapeDef ℓ).WellFormedExtra

/-- The invariant "(*)" of `restr(x)` comes from the invariant of
`def(x)`. -/
theorem restrOf_wellFormedExtra {S : Schema} (hWFExtra : S.WellFormedExtra) {x : Label}
    {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u) : u.WellFormedExtra := by
  have hWFx := hWFExtra x
  generalize hg : S.shapeDef x = e at hu hWFx
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' hs' =>
          simp only [ShapeExpr.restrOf] at hu
          simp only [ShapeExpr.WellFormedExtra] at hWFx
          obtain rfl := Option.some.inj hu
          exact hWFx.2
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- The invariant "no `extends` below `not`" of `restr(x)` comes from the
invariant of `def(x)`. -/
theorem restrOf_notIsExtendsFree {S : Schema} (hNEF : S.NotIsExtendsFree) {x : Label}
    {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u) : u.NotIsExtendsFree := by
  have hNx := hNEF x
  generalize hg : S.shapeDef x = e at hu hNx
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' hs' =>
          simp only [ShapeExpr.restrOf] at hu
          simp only [ShapeExpr.NotIsExtendsFree] at hNx
          obtain rfl := Option.some.inj hu
          exact hNx.2
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- `SatisfiesEFuel` (Table 1) is monotone in `τ` with no condition. When
`τ` becomes larger (for a *fixed* `M`), a match never fails. Table 1 has
no filtering of the `extra` type and no negation. Thus, this lemma needs
no bookkeeping for `Z`, `Lo` or `WellFormedExtra`, as all the lemmas after
this point do. -/
theorem monoE {S : Schema} {G : Graph} {τ τ' : Typing} (hsub : τ ⊆ τ') :
    ∀ (e : TripleExpr) fuel (M : Finset Triple),
      SatisfiesEFuel fuel S G τ M e → SatisfiesEFuel fuel S G τ' M e := by
  intro e
  induction e with
  | empty =>
      intro fuel M h
      rcases fuel with _ | f
      · exact h
      · exact h
  | tc p z =>
      intro fuel M h
      rcases fuel with _ | f
      · exact h
      obtain ⟨n, o, hM, htyp⟩ := h
      exact ⟨n, o, hM, hsub htyp⟩
  | choice e1 e2 ih1 ih2 =>
      intro fuel M h
      rcases fuel with _ | f
      · exact h
      rcases h with h | h
      · exact Or.inl (ih1 f M h)
      · exact Or.inr (ih2 f M h)
  | seq e1 e2 ih1 ih2 =>
      intro fuel M h
      rcases fuel with _ | f
      · exact h
      obtain ⟨M1, M2, hdu, h1, h2⟩ := h
      exact ⟨M1, M2, hdu, ih1 f M1 h1, ih2 f M2 h2⟩
  | star e ih =>
      intro fuel M h
      rcases fuel with _ | f
      · exact h
      obtain ⟨Ns, hdu, hall⟩ := h
      exact ⟨Ns, hdu, fun Ni hNi => ih f Ni (hall Ni hNi)⟩

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

/-- Rule 17 (`.ofShape h`) is monotone in `τ`, if `h.WellFormedExtra`
("(*)") is true. `Me` and `Mnotin` do not change (`Me_stable`). Thus, the
inner `SatisfiesEFuel` check goes from `τ` to `τ'` with `monoE`, and
`Mnotin` becomes empty (thus trivially `⊆` any set). -/
theorem monoM_ofShape {S : Schema} {G : Graph} {τ τ' : Typing} (hsub : τ ⊆ τ') {h : Shape}
    (hWF : h.WellFormedExtra) (fuel : ℕ) (M : Finset Triple) :
    SatisfiesMFuel (fuel + 1) S G τ M (.ofShape h) →
      SatisfiesMFuel (fuel + 1) S G τ' M (.ofShape h) := by
  rintro ⟨hE, hMnotin, hclosed⟩
  have hMeeq := Me_stable hsub hWF hMnotin
  have hMnotineq : Mnotin τ' M h.triples = Mnotin τ M h.triples := by
    unfold Mnotin; rw [hMeeq]
  exact ⟨hMeeq ▸ monoE hsub h.triples fuel (Me τ M h.triples) hE, hMnotineq ▸ hMnotin, hclosed⟩

/-! ### `stratMono`: a larger `τ` for positive positions, exact agreement
below `not` -/

/-- On a `NoExtends` shape, a larger `τ` (`hsub`) keeps satisfaction,
*if* these conditions are true:

* `h.WellFormedExtra` is true at each `.ofShape` that the proof reaches.
* The negative references of the shape (the `negRefs` of Definition 5,
  now with latching) are in `Lo`.
* `τ` and `τ'` agree exactly on `Lo`.

`.not` changes to `agreeM_noExtends` (exact agreement). It uses
`negRefs_true_eq_refs` to see that the `negRefs` of the outer call bound
the *full* content below a `not`, not only its references that are not
negated again. This is exactly the reason why `depsAux` must latch and
not toggle (refer to the docstring of that definition). -/
theorem stratMonoM_noExtends {S : Schema} {G : Graph} {τ τ' : Typing} {Lo : Finset Label}
    (hsub : τ ⊆ τ') (hagree : ∀ n z, z ∈ Lo → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) :
    ∀ (u : ShapeExpr), u.NoExtends → u.WellFormedExtra → ((u.depsAux false).negRefs ⊆ Lo) →
      ∀ fuel (M : Finset Triple), SatisfiesMFuel fuel S G τ M u → SatisfiesMFuel fuel S G τ' M u := by
  intro u
  induction u with
  | constraint c =>
      intro _ _ _ fuel M h
      rcases fuel with _ | f
      · exact h
      · exact h
  | ofShape h =>
      intro _ hWFh _ fuel M hSat
      rcases fuel with _ | f
      · exact hSat
      exact monoM_ofShape hsub hWFh f M hSat
  | «extends» xs h => intro hu; simp only [ShapeExpr.NoExtends] at hu
  | or s1 s2 ih1 ih2 =>
      intro hu hWF hneg fuel M hSat
      rcases fuel with _ | f
      · exact hSat
      simp only [ShapeExpr.NoExtends] at hu
      simp only [ShapeExpr.WellFormedExtra] at hWF
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      rcases hSat with h1 | h1
      · exact Or.inl (ih1 hu.1 hWF.1 hneg.1 f M h1)
      · exact Or.inr (ih2 hu.2 hWF.2 hneg.2 f M h1)
  | and s1 s2 ih1 ih2 =>
      intro hu hWF hneg fuel M hSat
      rcases fuel with _ | f
      · exact hSat
      simp only [ShapeExpr.NoExtends] at hu
      simp only [ShapeExpr.WellFormedExtra] at hWF
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      exact ⟨ih1 hu.1 hWF.1 hneg.1 f M hSat.1, ih2 hu.2 hWF.2 hneg.2 f M hSat.2⟩
  | not s _ =>
      intro hu _ hneg fuel M hSat
      rcases fuel with _ | f
      · exact hSat
      simp only [ShapeExpr.NoExtends] at hu
      simp only [ShapeExpr.depsAux] at hneg
      rw [s.negRefs_true_eq_refs, s.depsAux_refs_indep true false] at hneg
      show ¬ SatisfiesMFuel f S G τ' M s
      exact fun hc => hSat ((agreeM_noExtends hagree s hu hneg f M).mpr hc)

/-- The general `stratMono`. It combines a larger `τ` (positive positions,
with `monoM_ofShape` and `monoE`) with exact agreement (negated positions,
with `stratMonoM_noExtends`; `ShapeExpr.NotIsExtendsFree` makes sure that
this is sufficient).

The `.extends` case uses the same reuse of witnesses as `agreeM`. The
differences from `agreeM` are:

* For `M'` and `ext-te(x)`, it uses `monoE` in place of `agreeE`. (Table 1
  is monotone with no condition, so it needs no `WellFormedExtra` and no
  agreement there.)
* For `restr(x)`, it uses `stratMonoM_noExtends` in place of
  `agreeM_noExtends`. This needs only the bound on *its own* negative
  dependencies, through `restrOf_negRefs_subset` and the schema-wide
  `hLo`. -/
theorem stratMonoM {S : Schema} (_hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (_hNEF : S.NotIsExtendsFree)
    {G : Graph} {τ τ' : Typing} {Z Lo : Finset Label}
    (hZ : S.DClosedOn Z) (hsub : τ ⊆ τ') (hagree : ∀ n z, z ∈ Lo → ((n, z) ∈ τ ↔ (n, z) ∈ τ'))
    (hLo : ∀ z ∈ Z, ((S.shapeDef z).depsAux false).negRefs ⊆ Lo) :
    ∀ (s : ShapeExpr), s.depsIn Z → s.WellFormedExtra → s.NotIsExtendsFree →
      ((s.depsAux false).negRefs ⊆ Lo) →
      ∀ fuel (M : Finset Triple), SatisfiesMFuel fuel S G τ M s → SatisfiesMFuel fuel S G τ' M s := by
  intro s
  induction s with
  | constraint c =>
      intro _ _ _ _ fuel M h
      rcases fuel with _ | f
      · exact h
      · exact h
  | ofShape h =>
      intro _ hWFh _ _ fuel M hSat
      rcases fuel with _ | f
      · exact hSat
      exact monoM_ofShape hsub hWFh f M hSat
  | «extends» xs hs =>
      intro hdeps hWF _ _ fuel M hSat
      rcases fuel with _ | f
      · exact hSat
      obtain ⟨_, hxsZ⟩ := hdeps
      simp only [ShapeExpr.extendsTargets] at hxsZ
      have hancZ : S.ancSet xs ⊆ Z := S.ancSet_subset hZ hxsZ
      obtain ⟨M', Mx, pick, hdu, ⟨h, hmem, hE⟩, hExt, hRestr⟩ := hSat
      have hE' : SatisfiesMFuel f S G τ' M' (.ofShape h) := by
        rcases f with _ | f'
        · exact hE
        · exact monoM_ofShape hsub (hWF h hmem) f' M' hE
      refine ⟨M', Mx, pick, hdu, ⟨h, hmem, hE'⟩,
        fun x hx => monoE hsub _ f (Mx x) (hExt x hx), ?_⟩
      intro x hx u hru
      have hxX : x ∈ S.X := Schema.mem_ancSet_mem_X hx
      have hxZ : x ∈ Z := hancZ hx
      have hNoExt : u.NoExtends := (restrOf_noExtends_and_size_le hWFExt hru).1
      have hWFu : u.WellFormedExtra := restrOf_wellFormedExtra hWFExtra hru
      have hnegU : (u.depsAux false).negRefs ⊆ Lo :=
        Finset.Subset.trans (restrOf_negRefs_subset hru) (hLo x hxZ)
      exact stratMonoM_noExtends hsub hagree u hNoExt hWFu hnegU f _ (hRestr x hx u hru)
  | or s1 s2 ih1 ih2 =>
      intro hdeps hWF hNEF' hneg fuel M hSat
      rcases fuel with _ | f
      · exact hSat
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      simp only [ShapeExpr.WellFormedExtra] at hWF
      simp only [ShapeExpr.NotIsExtendsFree] at hNEF'
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      rcases hSat with h1 | h1
      · exact Or.inl (ih1 ⟨hdeps.1.1, hdeps.2.1⟩ hWF.1 hNEF'.1 hneg.1 f M h1)
      · exact Or.inr (ih2 ⟨hdeps.1.2, hdeps.2.2⟩ hWF.2 hNEF'.2 hneg.2 f M h1)
  | and s1 s2 ih1 ih2 =>
      intro hdeps hWF hNEF' hneg fuel M hSat
      rcases fuel with _ | f
      · exact hSat
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      simp only [ShapeExpr.WellFormedExtra] at hWF
      simp only [ShapeExpr.NotIsExtendsFree] at hNEF'
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      exact ⟨ih1 ⟨hdeps.1.1, hdeps.2.1⟩ hWF.1 hNEF'.1 hneg.1 f M hSat.1,
        ih2 ⟨hdeps.1.2, hdeps.2.2⟩ hWF.2 hNEF'.2 hneg.2 f M hSat.2⟩
  | not s _ =>
      intro _ hWF hNEF' hneg fuel M hSat
      rcases fuel with _ | f
      · exact hSat
      simp only [ShapeExpr.WellFormedExtra] at hWF
      simp only [ShapeExpr.NotIsExtendsFree] at hNEF'
      simp only [ShapeExpr.depsAux] at hneg
      rw [s.negRefs_true_eq_refs, s.depsAux_refs_indep true false] at hneg
      show ¬ SatisfiesMFuel f S G τ' M s
      exact fun hc => hSat ((agreeM_noExtends hagree s hNEF' hneg f M).mpr hc)

/-- `stratMono` for `SatisfiesFuel` (Table 2). The `.ofShape` and
`.extends` cases follow directly from `stratMonoM` (same shape,
`neigh G n`). Each other case is self-recursion, with exactly the same
structure as `stableFuel` and `agreeFuel`. -/
theorem stratMonoFuel {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree)
    {G : Graph} {τ τ' : Typing} {Z Lo : Finset Label}
    (hZ : S.DClosedOn Z) (hsub : τ ⊆ τ') (hagree : ∀ n z, z ∈ Lo → ((n, z) ∈ τ ↔ (n, z) ∈ τ'))
    (hLo : ∀ z ∈ Z, ((S.shapeDef z).depsAux false).negRefs ⊆ Lo) :
    ∀ (s : ShapeExpr), s.depsIn Z → s.WellFormedExtra → s.NotIsExtendsFree →
      ((s.depsAux false).negRefs ⊆ Lo) →
      ∀ fuel (n : RDFNode), SatisfiesFuel fuel S G τ n s → SatisfiesFuel fuel S G τ' n s := by
  intro s
  induction s with
  | constraint c =>
      intro _ _ _ _ fuel n h
      rcases fuel with _ | f
      · exact h
      · exact h
  | ofShape h =>
      intro hdeps hWFh hNEF' hneg fuel n hSat
      rcases fuel with _ | f
      · exact hSat
      exact stratMonoM hWFX hWFExt hWFExtra hNEF hZ hsub hagree hLo (.ofShape h) hdeps hWFh hNEF'
        hneg f (neigh G n) hSat
  | «extends» xs h =>
      intro hdeps hWFh hNEF' hneg fuel n hSat
      rcases fuel with _ | f
      · exact hSat
      exact stratMonoM hWFX hWFExt hWFExtra hNEF hZ hsub hagree hLo (.extends xs h) hdeps hWFh
        hNEF' hneg f (neigh G n) hSat
  | or s1 s2 ih1 ih2 =>
      intro hdeps hWF hNEF' hneg fuel n hSat
      rcases fuel with _ | f
      · exact hSat
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      simp only [ShapeExpr.WellFormedExtra] at hWF
      simp only [ShapeExpr.NotIsExtendsFree] at hNEF'
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      rcases hSat with h1 | h1
      · exact Or.inl (ih1 ⟨hdeps.1.1, hdeps.2.1⟩ hWF.1 hNEF'.1 hneg.1 f n h1)
      · exact Or.inr (ih2 ⟨hdeps.1.2, hdeps.2.2⟩ hWF.2 hNEF'.2 hneg.2 f n h1)
  | and s1 s2 ih1 ih2 =>
      intro hdeps hWF hNEF' hneg fuel n hSat
      rcases fuel with _ | f
      · exact hSat
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      simp only [ShapeExpr.WellFormedExtra] at hWF
      simp only [ShapeExpr.NotIsExtendsFree] at hNEF'
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      exact ⟨ih1 ⟨hdeps.1.1, hdeps.2.1⟩ hWF.1 hNEF'.1 hneg.1 f n hSat.1,
        ih2 ⟨hdeps.1.2, hdeps.2.2⟩ hWF.2 hNEF'.2 hneg.2 f n hSat.2⟩
  | not s _ =>
      intro _ hWF hNEF' hneg fuel n hSat
      rcases fuel with _ | f
      · exact hSat
      simp only [ShapeExpr.WellFormedExtra] at hWF
      simp only [ShapeExpr.NotIsExtendsFree] at hNEF'
      simp only [ShapeExpr.depsAux] at hneg
      rw [s.negRefs_true_eq_refs, s.depsAux_refs_indep true false] at hneg
      show ¬ SatisfiesFuel f S G τ' n s
      exact fun hc => hSat ((agreeFuel_noExtends hagree s hNEF' hneg f n).mpr hc)

/-! ### Definition 8 and Proposition 1 -/

/-- `nodes(G) × (Y ∪ X)`: the universe of all the possible node-type
associations for `G` by `S`. -/
def Schema.univTyping (S : Schema) (G : Graph) : Typing := G.nodes ×ˢ (S.Y ∪ S.X)

/-- `Y_i^σ ∪ X_i^σ = {z ∈ Y ∪ X | σ(z) ≤ i}`. -/
def Schema.stratum (S : Schema) (strat : Label → ℕ) (i : ℕ) : Finset Label :=
  (S.Y ∪ S.X).filter (fun z => strat z ≤ i)

theorem Schema.stratum_mono {S : Schema} {strat : Label → ℕ} {i j : ℕ} (h : i ≤ j) :
    S.stratum strat i ⊆ S.stratum strat j := by
  intro z hz
  simp only [Schema.stratum, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hz.2.trans h⟩

/-- `S_i^σ = (Y_i^σ, X_i^σ, def, A_i^σ)`: the restriction of `S` to the
labels with a stratum `≤ i`. The definitions do not change. -/
def Schema.stratRestrict (S : Schema) (strat : Label → ℕ) (i : ℕ) : Schema where
  Y := S.Y.filter (fun z => strat z ≤ i)
  X := S.X.filter (fun z => strat z ≤ i)
  A := S.A.filter (fun z => strat z ≤ i)
  disjointYX := Finset.disjoint_filter_filter S.disjointYX
  A_subX := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨S.A_subX hz.1, hz.2⟩
  shapeDef := S.shapeDef

/-- `maxTypingAgreeing S' G Lo fixed`: the union of all the correct typings
of `G` by `S'` that agree with `fixed` on `Lo`. This is a general form of
the "maximal correct typing" of `S'` (the case `Lo = ∅`). It adds the
agreement constraint that Definition 8 needs to connect the strata. It is
exactly `maxAgree` of 2017 (`ShexLean/Shex2017Schemas/Proposition1.lean`),
with `Schema.CorrectTyping` and `restrictTyping` in place of the 2017
versions. -/
noncomputable def maxTypingAgreeing (S' : Schema) (G : Graph) (Lo : Finset Label)
    (fixed : Typing) : Typing :=
  haveI := Classical.decPred
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)
  ((S'.univTyping G).powerset.filter
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)).sup id

theorem subset_maxTypingAgreeing {S' : Schema} {G : Graph} {Lo : Finset Label}
    {fixed t : Typing} (hsub : t ⊆ S'.univTyping G) (hcorrect : S'.CorrectTyping G t)
    (hagree : restrictTyping t Lo = restrictTyping fixed Lo) :
    t ⊆ maxTypingAgreeing S' G Lo fixed := by
  have := Classical.decPred
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)
  apply Finset.le_sup (f := id)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hcorrect, hagree⟩

theorem maxTypingAgreeing_subset (S' : Schema) (G : Graph) (Lo : Finset Label)
    (fixed : Typing) : maxTypingAgreeing S' G Lo fixed ⊆ S'.univTyping G := by
  have := Classical.decPred
    (fun t => S'.CorrectTyping G t ∧ restrictTyping t Lo = restrictTyping fixed Lo)
  apply Finset.sup_le
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_powerset] at ht
  exact ht.1

theorem maxTypingAgreeing_restrictTo {S' : Schema} {G : Graph} {Lo : Finset Label}
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
way as the plain case. It applies `stratMonoM` to `S'.shapeDef x` (the
descendant that is the witness), not to `S'.shapeDef L`. -/
theorem maxTypingAgreeing_correct {S' : Schema} (hWFX : S'.WellFormedX)
    (hWFExt : S'.WellFormedExtends) (hWFExtra : S'.WellFormedExtra)
    (hNEF : S'.NotIsExtendsFree) (hDClosed : S'.DClosedOn (S'.Y ∪ S'.X)) {G : Graph}
    {Lo : Finset Label} {fixed : Typing} (hfixed_sub : fixed ⊆ S'.univTyping G)
    (hfixed_correct : S'.CorrectTyping G fixed)
    (hLo : ∀ z ∈ S'.Y ∪ S'.X, ((S'.shapeDef z).depsAux false).negRefs ⊆ Lo) :
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
  have hagree_t : ∀ n L, L ∈ Lo → ((n, L) ∈ t ↔ (n, L) ∈ maxTypingAgreeing S' G Lo fixed) := by
    apply restrictTyping_agree
    rw [htagree, maxTypingAgreeing_restrictTo hfixed_sub hfixed_correct]
  have htcorrectL := htcorrect n L htmem
  refine ⟨fun hLA => ?_, fun hLA => ?_⟩
  · exact stratMonoFuel hWFX hWFExt hWFExtra hNEF hDClosed hsub_t hagree_t hLo (S'.shapeDef L)
      (S'.shapeDef_depsIn hDClosed hL) (hWFExtra L) (hNEF L) (hLo L hL) _ n (htcorrectL.1 hLA)
  · obtain ⟨x, hxmem, hSatx⟩ := htcorrectL.2 hLA
    have hxY : x ∈ S'.Y ∪ S'.X := by
      have hxdesc : x ∈ S'.desc L := (Finset.mem_sdiff.mp hxmem).1
      unfold Schema.desc at hxdesc
      simp only [Finset.mem_filter] at hxdesc
      exact Finset.mem_union_right _ hxdesc.1
    exact ⟨x, hxmem, stratMonoFuel hWFX hWFExt hWFExtra hNEF hDClosed hsub_t hagree_t hLo
      (S'.shapeDef x) (S'.shapeDef_depsIn hDClosed hxY) (hWFExtra x) (hNEF x) (hLo x hxY)
      _ n hSatx⟩

/-! ### Schema invariance of `Satisfies` across `stratRestrict`

This is the last part that Proposition 1 needs, in addition to all the
parts above. `Satisfies` is defined at a canonical fuel that *depends on
the schema* (`reqFuel S s + 1`,
`ShexLean/Shex2026InheritanceDisjunction/Termination.lean`). Thus,
`Satisfies (S.stratRestrict strat i) G τ n s` and
`Satisfies (S.stratRestrict strat j) G τ n s` are different propositions.
They use different concrete `SatisfiesFuel` fuel values, over different
schemas with a different `X`.

In 2017, `stratTypingSeq_correct` does not have this problem, because
`Satisfies` never uses the schema. There, the equivalent step was a
definitional equality. Here, a new schema-invariance argument is
necessary:

* `SatisfiesEFuel` (Table 1) never uses `S` or `G`.
* In `SatisfiesMFuel` and `SatisfiesFuel`, the only case that depends on
  the schema is `.extends`. It uses `S` only through `S.shapeDef`, `S.anc`
  and `S.ancSet`.

Thus, two schemas with the same `shapeDef`, that agree on `.anc` for each
label that the dependencies of a shape can reach, give the same
results. -/

/-- `SatisfiesEFuel` (Table 1) does not depend on the schema or graph
parameters. The proof applies to *each* pair of schemas or graphs at a
shared fuel, with no side hypotheses. (The equations of Table 1 never use
`S` or `G`. Refer to the module docstring of
`ShexLean/Shex2026InheritanceDisjunction/Semantics.lean`.) -/
theorem SatisfiesEFuel_schema_indep (S1 S2 : Schema) (G1 G2 : Graph) :
    ∀ (e : TripleExpr) (fuel : ℕ) (τ : Typing) (M : Finset Triple),
      SatisfiesEFuel fuel S1 G1 τ M e ↔ SatisfiesEFuel fuel S2 G2 τ M e := by
  intro e
  induction e with
  | empty => intro fuel τ M; rcases fuel with _ | f <;> rfl
  | tc p z => intro fuel τ M; rcases fuel with _ | f <;> rfl
  | choice e1 e2 ih1 ih2 =>
      intro fuel τ M
      rcases fuel with _ | f
      · rfl
      show SatisfiesEFuel f S1 G1 τ M e1 ∨ SatisfiesEFuel f S1 G1 τ M e2 ↔
        SatisfiesEFuel f S2 G2 τ M e1 ∨ SatisfiesEFuel f S2 G2 τ M e2
      rw [ih1 f τ M, ih2 f τ M]
  | seq e1 e2 ih1 ih2 =>
      intro fuel τ M
      rcases fuel with _ | f
      · rfl
      show (∃ M1 M2, DisjointUnion M M1 M2 ∧
            SatisfiesEFuel f S1 G1 τ M1 e1 ∧ SatisfiesEFuel f S1 G1 τ M2 e2) ↔
          (∃ M1 M2, DisjointUnion M M1 M2 ∧
            SatisfiesEFuel f S2 G2 τ M1 e1 ∧ SatisfiesEFuel f S2 G2 τ M2 e2)
      constructor
      · rintro ⟨M1, M2, hdu, h1, h2⟩
        exact ⟨M1, M2, hdu, (ih1 f τ M1).mp h1, (ih2 f τ M2).mp h2⟩
      · rintro ⟨M1, M2, hdu, h1, h2⟩
        exact ⟨M1, M2, hdu, (ih1 f τ M1).mpr h1, (ih2 f τ M2).mpr h2⟩
  | star e ih =>
      intro fuel τ M
      rcases fuel with _ | f
      · rfl
      show (∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧
            ∀ Ni ∈ Ns, SatisfiesEFuel f S1 G1 τ Ni e) ↔
          (∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧
            ∀ Ni ∈ Ns, SatisfiesEFuel f S2 G2 τ Ni e)
      constructor
      · rintro ⟨Ns, hdu, hall⟩; exact ⟨Ns, hdu, fun Ni hNi => (ih f τ Ni).mp (hall Ni hNi)⟩
      · rintro ⟨Ns, hdu, hall⟩; exact ⟨Ns, hdu, fun Ni hNi => (ih f τ Ni).mpr (hall Ni hNi)⟩

/-- `SatisfiesMFuel` (Table 3) on a `NoExtends` shape also does not depend
on the schema or the graph. The `.extends` case (the only case that
depends on the schema) is not possible, and `.ofShape` only uses
`SatisfiesEFuel_schema_indep`. -/
theorem schemaAgreeM_noExtends (S1 S2 : Schema) (G1 G2 : Graph) :
    ∀ (u : ShapeExpr), u.NoExtends →
      ∀ (fuel : ℕ) (τ : Typing) (M : Finset Triple),
        SatisfiesMFuel fuel S1 G1 τ M u ↔ SatisfiesMFuel fuel S2 G2 τ M u := by
  intro u
  induction u with
  | constraint c => intro _ fuel τ M; rcases fuel with _ | f <;> rfl
  | ofShape h =>
      intro _ fuel τ M
      rcases fuel with _ | f
      · rfl
      show (SatisfiesEFuel f S1 G1 τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)) ↔
          (SatisfiesEFuel f S2 G2 τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅))
      rw [SatisfiesEFuel_schema_indep S1 S2 G1 G2 h.triples f τ (Me τ M h.triples)]
  | «extends» xs h => intro hu; simp only [ShapeExpr.NoExtends] at hu
  | or s1 s2 ih1 ih2 =>
      intro hu fuel τ M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.NoExtends] at hu
      show SatisfiesMFuel f S1 G1 τ M s1 ∨ SatisfiesMFuel f S1 G1 τ M s2 ↔
        SatisfiesMFuel f S2 G2 τ M s1 ∨ SatisfiesMFuel f S2 G2 τ M s2
      rw [ih1 hu.1 f τ M, ih2 hu.2 f τ M]
  | and s1 s2 ih1 ih2 =>
      intro hu fuel τ M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.NoExtends] at hu
      show SatisfiesMFuel f S1 G1 τ M s1 ∧ SatisfiesMFuel f S1 G1 τ M s2 ↔
        SatisfiesMFuel f S2 G2 τ M s1 ∧ SatisfiesMFuel f S2 G2 τ M s2
      rw [ih1 hu.1 f τ M, ih2 hu.2 f τ M]
  | not s ih =>
      intro hu fuel τ M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.NoExtends] at hu
      show ¬ SatisfiesMFuel f S1 G1 τ M s ↔ ¬ SatisfiesMFuel f S2 G2 τ M s
      rw [ih hu f τ M]

/-- `SatisfiesMFuel` (Table 3) for a general shape agrees between two
schemas `S1` and `S2`, if these conditions are true:

* `S1` and `S2` have the same `shapeDef`.
* They agree on `.anc` for each label in a `D_S`-closed set `Z`.
* `Z` contains the dependencies of the shape (`depsIn Z`).

This is the schema version of `agreeM` (which changes `τ` over a *fixed*
schema).

`S1.WellFormedExtends` is necessary to know that `restr(x)` is
`NoExtends`. Thus, its recursive call can use `schemaAgreeM_noExtends`,
and does not need a schema-agreement fact about shapes that contain
`.extends`. (By `WellFormedExtends`, `restr(x)` never contains one.) -/
theorem schemaAgreeM {S1 S2 : Schema} (hSD : S1.shapeDef = S2.shapeDef)
    (hWFExt1 : S1.WellFormedExtends) {Z : Finset Label} (hZ : S1.DClosedOn Z)
    (hAnc : ∀ x ∈ Z, S1.anc x = S2.anc x) {G : Graph} :
    ∀ (s : ShapeExpr), s.depsIn Z →
      ∀ (fuel : ℕ) (τ : Typing) (M : Finset Triple),
        SatisfiesMFuel fuel S1 G τ M s ↔ SatisfiesMFuel fuel S2 G τ M s := by
  intro s
  induction s with
  | constraint c => intro _ fuel τ M; rcases fuel with _ | f <;> rfl
  | ofShape h =>
      intro _ fuel τ M
      rcases fuel with _ | f
      · rfl
      show (SatisfiesEFuel f S1 G τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)) ↔
          (SatisfiesEFuel f S2 G τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅))
      rw [SatisfiesEFuel_schema_indep S1 S2 G G h.triples f τ (Me τ M h.triples)]
  | «extends» xs hs =>
      intro hdeps fuel τ M
      rcases fuel with _ | f
      · rfl
      obtain ⟨_, hxsZ⟩ := hdeps
      simp only [ShapeExpr.extendsTargets] at hxsZ
      have hancSetEq : S1.ancSet xs = S2.ancSet xs := by
        unfold Schema.ancSet
        apply Finset.biUnion_congr rfl
        intro x hx
        exact hAnc x (hxsZ hx)
      have hancZ : S1.ancSet xs ⊆ Z := S1.ancSet_subset hZ hxsZ
      show (∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S1.ancSet xs) Mx ∧
            (∃ h ∈ hs, SatisfiesMFuel f S1 G τ M' (.ofShape h)) ∧
            (∀ x ∈ S1.ancSet xs,
              SatisfiesEFuel f S1 G τ (Mx x) ((S1.shapeDef x).extTeAt (pick x))) ∧
            (∀ x ∈ S1.ancSet xs, ∀ u, (S1.shapeDef x).restrOf = some u →
              SatisfiesMFuel f S1 G τ ((S1.anc x).biUnion Mx) u)) ↔
          (∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S2.ancSet xs) Mx ∧
            (∃ h ∈ hs, SatisfiesMFuel f S2 G τ M' (.ofShape h)) ∧
            (∀ x ∈ S2.ancSet xs,
              SatisfiesEFuel f S2 G τ (Mx x) ((S2.shapeDef x).extTeAt (pick x))) ∧
            (∀ x ∈ S2.ancSet xs, ∀ u, (S2.shapeDef x).restrOf = some u →
              SatisfiesMFuel f S2 G τ ((S2.anc x).biUnion Mx) u))
      rw [hancSetEq]
      refine exists_congr fun M' => exists_congr fun Mx => exists_congr fun pick =>
        and_congr_right fun _ => ?_
      have he : (∃ h ∈ hs, SatisfiesMFuel f S1 G τ M' (.ofShape h)) ↔
          (∃ h ∈ hs, SatisfiesMFuel f S2 G τ M' (.ofShape h)) :=
        exists_congr fun h => and_congr_right fun _ =>
          schemaAgreeM_noExtends S1 S2 G G (.ofShape h) trivial f τ M'
      have hext : (∀ x ∈ S2.ancSet xs,
            SatisfiesEFuel f S1 G τ (Mx x) ((S1.shapeDef x).extTeAt (pick x))) ↔
          (∀ x ∈ S2.ancSet xs,
            SatisfiesEFuel f S2 G τ (Mx x) ((S2.shapeDef x).extTeAt (pick x))) := by
        refine forall_congr' fun x => forall_congr' fun _ => ?_
        rw [hSD]; exact SatisfiesEFuel_schema_indep S1 S2 G G _ f τ (Mx x)
      have hrestr : (∀ x ∈ S2.ancSet xs, ∀ u, (S1.shapeDef x).restrOf = some u →
            SatisfiesMFuel f S1 G τ ((S1.anc x).biUnion Mx) u) ↔
          (∀ x ∈ S2.ancSet xs, ∀ u, (S2.shapeDef x).restrOf = some u →
            SatisfiesMFuel f S2 G τ ((S2.anc x).biUnion Mx) u) := by
        refine forall_congr' fun x => forall_congr' fun hx => forall_congr' fun u => ?_
        have hxZ : x ∈ Z := by rw [← hancSetEq] at hx; exact hancZ hx
        rw [hSD]
        refine imp_congr_right fun hru => ?_
        rw [← hSD] at hru
        have hNoExt : u.NoExtends := (restrOf_noExtends_and_size_le hWFExt1 hru).1
        rw [hAnc x hxZ]
        exact schemaAgreeM_noExtends S1 S2 G G u hNoExt f τ _
      rw [he, hext, hrestr]
  | or s1 s2 ih1 ih2 =>
      intro hdeps fuel τ M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      show SatisfiesMFuel f S1 G τ M s1 ∨ SatisfiesMFuel f S1 G τ M s2 ↔
        SatisfiesMFuel f S2 G τ M s1 ∨ SatisfiesMFuel f S2 G τ M s2
      rw [ih1 ⟨hdeps.1.1, hdeps.2.1⟩ f τ M, ih2 ⟨hdeps.1.2, hdeps.2.2⟩ f τ M]
  | and s1 s2 ih1 ih2 =>
      intro hdeps fuel τ M
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      show SatisfiesMFuel f S1 G τ M s1 ∧ SatisfiesMFuel f S1 G τ M s2 ↔
        SatisfiesMFuel f S2 G τ M s1 ∧ SatisfiesMFuel f S2 G τ M s2
      rw [ih1 ⟨hdeps.1.1, hdeps.2.1⟩ f τ M, ih2 ⟨hdeps.1.2, hdeps.2.2⟩ f τ M]
  | not s ih =>
      intro hdeps fuel τ M
      rcases fuel with _ | f
      · rfl
      have hdeps' : s.depsIn Z := by
        refine ⟨?_, ?_⟩
        · rw [s.depsAux_refs_indep false true]
          simpa [ShapeExpr.depsAux] using hdeps.1
        · simpa [ShapeExpr.extendsTargets] using hdeps.2
      show ¬ SatisfiesMFuel f S1 G τ M s ↔ ¬ SatisfiesMFuel f S2 G τ M s
      rw [ih hdeps' f τ M]

/-- `SatisfiesFuel` (Table 2): the same schema-agreement fact, one level
higher. `.ofShape` and `.extends` follow directly from `schemaAgreeM`.
Each other case is self-recursion. -/
theorem schemaAgreeFuel {S1 S2 : Schema} (hSD : S1.shapeDef = S2.shapeDef)
    (hWFExt1 : S1.WellFormedExtends) {Z : Finset Label} (hZ : S1.DClosedOn Z)
    (hAnc : ∀ x ∈ Z, S1.anc x = S2.anc x) {G : Graph} :
    ∀ (s : ShapeExpr), s.depsIn Z →
      ∀ (fuel : ℕ) (τ : Typing) (n : RDFNode),
        SatisfiesFuel fuel S1 G τ n s ↔ SatisfiesFuel fuel S2 G τ n s := by
  intro s
  induction s with
  | constraint c => intro _ fuel τ n; rcases fuel with _ | f <;> rfl
  | ofShape h =>
      intro hdeps fuel τ n
      rcases fuel with _ | f
      · rfl
      show SatisfiesMFuel f S1 G τ (neigh G n) (.ofShape h) ↔
        SatisfiesMFuel f S2 G τ (neigh G n) (.ofShape h)
      exact schemaAgreeM hSD hWFExt1 hZ hAnc (.ofShape h) hdeps f τ (neigh G n)
  | «extends» xs h =>
      intro hdeps fuel τ n
      rcases fuel with _ | f
      · rfl
      show SatisfiesMFuel f S1 G τ (neigh G n) (.extends xs h) ↔
        SatisfiesMFuel f S2 G τ (neigh G n) (.extends xs h)
      exact schemaAgreeM hSD hWFExt1 hZ hAnc (.extends xs h) hdeps f τ (neigh G n)
  | or s1 s2 ih1 ih2 =>
      intro hdeps fuel τ n
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      show SatisfiesFuel f S1 G τ n s1 ∨ SatisfiesFuel f S1 G τ n s2 ↔
        SatisfiesFuel f S2 G τ n s1 ∨ SatisfiesFuel f S2 G τ n s2
      rw [ih1 ⟨hdeps.1.1, hdeps.2.1⟩ f τ n, ih2 ⟨hdeps.1.2, hdeps.2.2⟩ f τ n]
  | and s1 s2 ih1 ih2 =>
      intro hdeps fuel τ n
      rcases fuel with _ | f
      · rfl
      simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
        ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
      show SatisfiesFuel f S1 G τ n s1 ∧ SatisfiesFuel f S1 G τ n s2 ↔
        SatisfiesFuel f S2 G τ n s1 ∧ SatisfiesFuel f S2 G τ n s2
      rw [ih1 ⟨hdeps.1.1, hdeps.2.1⟩ f τ n, ih2 ⟨hdeps.1.2, hdeps.2.2⟩ f τ n]
  | not s ih =>
      intro hdeps fuel τ n
      rcases fuel with _ | f
      · rfl
      have hdeps' : s.depsIn Z := by
        refine ⟨?_, ?_⟩
        · rw [s.depsAux_refs_indep false true]
          simpa [ShapeExpr.depsAux] using hdeps.1
        · simpa [ShapeExpr.extendsTargets] using hdeps.2
      show ¬ SatisfiesFuel f S1 G τ n s ↔ ¬ SatisfiesFuel f S2 G τ n s
      rw [ih hdeps' f τ n]

/-- `WellFormedX` stays true for each `stratRestrict`. Its `X` only
becomes smaller. The witness that `WellFormedX` gives for `x ∈ S.X` does
not depend on the restriction that `x` also satisfies (if any). -/
theorem Schema.stratRestrict_WellFormedX {S : Schema} (hWFX : S.WellFormedX)
    (strat : Label → ℕ) (i : ℕ) : (S.stratRestrict strat i).WellFormedX := by
  intro x hx
  simp only [Schema.stratRestrict, Finset.mem_filter] at hx
  exact hWFX x hx.1

/-- Each stratum `S.stratum strat i` is `D_S`-closed. The edges of `D_S`
never increase `strat` (the first bullet of Definition 7), and
`Schema.DClosed` keeps the membership in `Y ∪ X` along the path. -/
theorem Schema.stratum_DClosedOn {S : Schema} (hDClosed : S.DClosed) (strat : Stratification S)
    (i : ℕ) : S.DClosedOn (S.stratum strat.strat i) := by
  intro z hz z' hedge
  simp only [Schema.stratum, Finset.mem_filter] at hz ⊢
  have hzY : z ∈ S.Y ∪ S.X := hz.1
  have hz'Y : z' ∈ S.Y ∪ S.X := hDClosed z hzY z' hedge
  exact ⟨hz'Y, le_trans (strat.dep_le z hzY z' hedge) hz.2⟩

/-- `(S.stratRestrict strat i).anc x = S.anc x` if `x` is in a stratum
`≤ i`. Each element of the *unrestricted* `S.anc x` already has
`strat ≤ strat x ≤ i` (the first bullet of Definition 7, through
`extEdge ⊆ depExtends ⊆ DEdge`). Thus, if you filter `S.X` to
`strat ≤ i` before you compute `anc`, you remove nothing.

This is the fact that makes `Satisfies`, computed with two different
`stratRestrict` levels, agree for each label in the lower level. The
`ancSet` and `extends`-step data that the `.extends` case of
`SatisfiesMFuel` uses do not depend on the (sufficiently high) stratum
level of the schema restriction. -/
theorem Schema.stratRestrict_anc_eq {S : Schema} (hDClosed : S.DClosed) (strat : Stratification S)
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

/-- **The key schema-invariance fact.** For a label `x` in a stratum
`≤ i`, `Satisfies` with `S.stratRestrict strat i` agrees with `Satisfies`
with each higher restriction `S.stratRestrict strat j` (`i ≤ j`).

These are syntactically different schemas (a different `X`, and thus
different `reqFuel` and `ancSet` bookkeeping). But the evaluation of
`def(x)` never goes outside the strata `≤ i` (`Schema.shapeDef_depsIn`
and `Schema.stratum_DClosedOn`). In that region, the `.anc` of the two
schemas is the same (`Schema.stratRestrict_anc_eq`). Thus, all that
`SatisfiesFuel` and `SatisfiesMFuel` use is also the same.

The proof combines two lemmas:

* `stableFuel` (same schema): it connects the canonical fuel of each side
  to a shared sufficient value.
* `schemaAgreeFuel` (same fuel): it connects the two schemas.

This is exactly the problem that stopped a direct port, in the 2017
style, of the inductive step of `stratTypingSeq_correct`.
(`hcorrect_i := hcorrect_i` fails here, because `Satisfies` really depends
on the schema. In 2017, it does not.) -/
theorem Satisfies_stratRestrict_agree {S : Schema} (hWFX : S.WellFormedX)
    (hWFExt : S.WellFormedExtends) (hDClosed : S.DClosed) (strat : Stratification S)
    {i j : ℕ} (hij : i ≤ j) {x : Label} (hxY : x ∈ S.Y ∪ S.X) (hxi : strat.strat x ≤ i)
    {G : Graph} {τ : Typing} {n : RDFNode} :
    Satisfies (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) ↔
    Satisfies (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) := by
  have hZDCl : S.DClosedOn (S.stratum strat.strat i) := Schema.stratum_DClosedOn hDClosed strat i
  have hxZ : x ∈ S.stratum strat.strat i := by
    simp only [Schema.stratum, Finset.mem_filter]; exact ⟨hxY, hxi⟩
  have hdeps : (S.shapeDef x).depsIn (S.stratum strat.strat i) := S.shapeDef_depsIn hZDCl hxZ
  have hAnc : ∀ y ∈ S.stratum strat.strat i,
      (S.stratRestrict strat.strat i).anc y = (S.stratRestrict strat.strat j).anc y := by
    intro y hy
    simp only [Schema.stratum, Finset.mem_filter] at hy
    rw [Schema.stratRestrict_anc_eq hDClosed strat hy.1 hy.2,
      Schema.stratRestrict_anc_eq hDClosed strat hy.1 (hy.2.trans hij)]
  have hWFX1 : (S.stratRestrict strat.strat i).WellFormedX :=
    Schema.stratRestrict_WellFormedX hWFX strat.strat i
  have hWFX2 : (S.stratRestrict strat.strat j).WellFormedX :=
    Schema.stratRestrict_WellFormedX hWFX strat.strat j
  set F := max (ShapeExpr.reqFuel (S.stratRestrict strat.strat i) (S.shapeDef x) + 1)
    (ShapeExpr.reqFuel (S.stratRestrict strat.strat j) (S.shapeDef x) + 1) with hFdef
  have hstep1 : Satisfies (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) ↔
      SatisfiesFuel F (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) :=
    stableFuel hWFX1 hWFExt (S.shapeDef x)
      (ShapeExpr.reqFuel (S.stratRestrict strat.strat i) (S.shapeDef x) + 1) F
      (le_refl _) (le_max_left _ _) G τ n
  have hstep2 : Satisfies (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) ↔
      SatisfiesFuel F (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) :=
    stableFuel hWFX2 hWFExt (S.shapeDef x)
      (ShapeExpr.reqFuel (S.stratRestrict strat.strat j) (S.shapeDef x) + 1) F
      (le_refl _) (le_max_right _ _) G τ n
  have hcross : SatisfiesFuel F (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) ↔
      SatisfiesFuel F (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) :=
    schemaAgreeFuel (S1 := S.stratRestrict strat.strat i) (S2 := S.stratRestrict strat.strat j)
      rfl hWFExt hZDCl hAnc (S.shapeDef x) hdeps F τ n
  rw [hstep1, hstep2, hcross]

/-- The membership property of `Schema.desc`. This lemma fixes the
instance of the filter one time, here, and not at each call site. This
prevents a frequent problem: an instance mismatch between
`Classical.decPred` and `Finset.filter`. -/
theorem Schema.mem_desc {S : Schema} {x y : Label} :
    y ∈ S.desc x ↔ y ∈ S.X ∧ Relation.ReflTransGen S.extEdge y x := by
  unfold Schema.desc
  simp only [Finset.mem_filter]

/-- `(S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X` (a union of
two sets, each with its own filter) and `S.stratum strat i` (one filter
over the union) are the same `Finset`, made in different ways. This lemma
connects the `Y ∪ X` form of `Schema.univTyping` with the form of
`Schema.stratum_mono`. -/
theorem Schema.stratRestrict_YX_eq_stratum (S : Schema) (strat : Label → ℕ) (i : ℕ) :
    (S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X = S.stratum strat i := by
  unfold Schema.stratRestrict Schema.stratum
  rw [Finset.filter_union]

/-- `stratRestrict` does not change the edge relation of `D_S`. (It changes
only `Y`, `X` and `A`, never `shapeDef`, and `DEdge` uses only
`shapeDef`.)

This fact is a separate `rfl` lemma, so that later proofs can use it
directly with `rw`. Do not let the elaborator find it again by
unification inside a large application. `DEdge` unfolds through much
`Schema` and `Finset` data, so the unification is very slow. If this fact
stays implicit, it causes a timeout in the `hDClosed` argument of
`maxTypingAgreeing_correct`. -/
theorem Schema.stratRestrict_DEdge_eq (S : Schema) (strat : Label → ℕ) (i : ℕ) :
    (S.stratRestrict strat i).DEdge = S.DEdge := rfl

/-- `S.stratRestrict strat i` is also `DClosed`, if `S` is. This is the
`stratRestrict` form of `Schema.stratum_DClosedOn`. It is connected
explicitly with `Schema.stratRestrict_YX_eq_stratum` and
`Schema.stratRestrict_DEdge_eq` (not with `hDClosed` directly), for the
same performance reason as in `Schema.stratRestrict_DEdge_eq`. -/
theorem Schema.stratRestrict_DClosed {S : Schema} (hDClosed : S.DClosed) (strat : Stratification S)
    (i : ℕ) : (S.stratRestrict strat.strat i).DClosed := by
  intro z hz z' hedge
  rw [Schema.stratRestrict_YX_eq_stratum] at hz ⊢
  rw [Schema.stratRestrict_DEdge_eq] at hedge
  exact Schema.stratum_DClosedOn hDClosed strat i z hz z' hedge

/-- A correct typing of `S.stratRestrict strat i` is also a correct typing
of `S.stratRestrict strat j`, for `i ≤ j`. The inductive step of
`stratTypingSeq_correct` needs this step: "go up one stratum level and keep
correctness".

Each part (`.A` membership, and the `.desc \ .A` witnesses) is monotone in
the restriction level, because `stratRestrict` only makes `Y`, `X` and `A`
*larger* when `i` becomes larger. The one important step is to move the
`Satisfies` witnesses with `Satisfies_stratRestrict_agree`. -/
theorem Schema.correctTyping_stratRestrict_mono {S : Schema} (hWFX : S.WellFormedX)
    (hWFExt : S.WellFormedExtends) (hDClosed : S.DClosed) (strat : Stratification S)
    {i j : ℕ} (hij : i ≤ j) {G : Graph} {t : Typing}
    (ht_sub : t ⊆ (S.stratRestrict strat.strat i).univTyping G)
    (ht_correct : (S.stratRestrict strat.strat i).CorrectTyping G t) :
    (S.stratRestrict strat.strat j).CorrectTyping G t := by
  intro n L hmem
  have hLmem : L ∈ (S.stratRestrict strat.strat i).Y ∪ (S.stratRestrict strat.strat i).X :=
    (Finset.mem_product.mp (ht_sub hmem)).2
  simp only [Schema.stratRestrict, Finset.mem_union, Finset.mem_filter] at hLmem
  have hLY : L ∈ S.Y ∪ S.X := by
    rcases hLmem with ⟨h, _⟩ | ⟨h, _⟩
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  have hLi : strat.strat L ≤ i := by rcases hLmem with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
  have hAiff : L ∈ (S.stratRestrict strat.strat i).A ↔ L ∈ (S.stratRestrict strat.strat j).A := by
    simp only [Schema.stratRestrict, Finset.mem_filter]
    constructor
    · rintro ⟨hLA, _⟩; exact ⟨hLA, hLi.trans hij⟩
    · rintro ⟨hLA, _⟩; exact ⟨hLA, hLi⟩
  obtain ⟨hcorrectPlain, hcorrectAbs⟩ := ht_correct n L hmem
  refine ⟨fun hLnotA => ?_, fun hLA => ?_⟩
  · exact (Satisfies_stratRestrict_agree hWFX hWFExt hDClosed strat hij hLY hLi).mp
      (hcorrectPlain (fun h => hLnotA (hAiff.mp h)))
  · obtain ⟨x, hxmem, hSatx⟩ := hcorrectAbs (hAiff.mpr hLA)
    rw [Finset.mem_sdiff, Schema.mem_desc] at hxmem
    obtain ⟨⟨hxX', hxpath⟩, hxnA⟩ := hxmem
    simp only [Schema.stratRestrict, Finset.mem_filter] at hxX' hxnA
    obtain ⟨hxX, hxi⟩ := hxX'
    have hxY : x ∈ S.Y ∪ S.X := Finset.mem_union_right _ hxX
    have hxnA' : x ∉ S.A := fun h => hxnA ⟨h, hxi⟩
    have hxmem' : x ∈ (S.stratRestrict strat.strat j).desc L \ (S.stratRestrict strat.strat j).A := by
      rw [Finset.mem_sdiff, Schema.mem_desc]
      refine ⟨⟨?_, hxpath⟩, ?_⟩
      · simp only [Schema.stratRestrict, Finset.mem_filter]; exact ⟨hxX, hxi.trans hij⟩
      · simp only [Schema.stratRestrict, Finset.mem_filter]; exact fun h => hxnA' h.1
    exact ⟨x, hxmem',
      (Satisfies_stratRestrict_agree hWFX hWFExt hDClosed strat hij hxY hxi).mp hSatx⟩

/-- The sequence `τ_i` of Definition 8, as one recursion on `ℕ`:

* `τ_0 := ∅`. This is vacuously correct for `S^σ_0`, because each label
  has `σ(z) ≥ 1`. Thus, stratum 0 is empty.
* `τ_{i+1}` is the union of all the correct typings of `G` by `S^σ_{i+1}`
  that agree with `τ_i` on `Y^σ_i ∪ X^σ_i`.

This agrees with the recursion of the paper. The base case `τ_1` of
Definition 8 ("the union of all correct typings of `G` by `S^σ_1`") is the
special case `Lo = ∅` of the general step. -/
noncomputable def stratTypingSeq (S : Schema) (strat : Label → ℕ) (G : Graph) : ℕ → Typing
  | 0 => ∅
  | i + 1 => maxTypingAgreeing (S.stratRestrict strat (i + 1)) G (S.stratum strat i)
      (stratTypingSeq S strat G i)

/-- Definition 8: the maximal typing of `G` by `S` with `σ`,
`τ_max(S,σ,G)`. -/
noncomputable def Typing8 (G : Graph) (S : Schema) (strat : Stratification S) : Typing :=
  stratTypingSeq S strat.strat G strat.k

/-- The two invariants of `stratTypingSeq` at each stratum `i`:

* It is a subset of the universe of typings of `S^σ_i`.
* It is a correct typing of `G` by `S^σ_i`.

The base case (`i = 0`) is vacuous. (`stratum strat 0 = ∅`, and
`Y^σ_0 ∪ X^σ_0 = ∅`, because each label has `σ ≥ 1`, `mem_range`.)

The inductive step combines two lemmas:

* `maxTypingAgreeing_correct`: the new correctness at stratum `i+1`.
* `Schema.correctTyping_stratRestrict_mono`: it moves the correctness of
  the *previous* typing at stratum `i` up to the schema of stratum `i+1`.

This solves exactly the problem that a direct port in the 2017 style did
not solve. Refer to the docstring of `Satisfies_stratRestrict_agree`. -/
theorem stratTypingSeq_correct {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
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
        have hp' := hsub_i hp
        simp only [Schema.univTyping] at hp' ⊢
        rw [Schema.stratRestrict_YX_eq_stratum]
        refine Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp').1, ?_⟩
        have hp2 : p.2 ∈ (S.stratRestrict strat.strat i).Y ∪ (S.stratRestrict strat.strat i).X :=
          (Finset.mem_product.mp hp').2
        rw [Schema.stratRestrict_YX_eq_stratum] at hp2
        exact Schema.stratum_mono (Nat.le_succ i) hp2
      have hcorrect_i' : (S.stratRestrict strat.strat (i + 1)).CorrectTyping G
          (stratTypingSeq S strat.strat G i) :=
        Schema.correctTyping_stratRestrict_mono hWFX hWFExt hDClosed strat (Nat.le_succ i)
          hsub_i hcorrect_i
      have hLo : ∀ z ∈ (S.stratRestrict strat.strat (i + 1)).Y ∪
            (S.stratRestrict strat.strat (i + 1)).X,
          (((S.stratRestrict strat.strat (i + 1)).shapeDef z).depsAux false).negRefs ⊆
            S.stratum strat.strat i := by
        intro z hz z' hz'
        simp only [Schema.stratRestrict, Finset.mem_union, Finset.mem_filter] at hz
        have hzY : z ∈ S.Y ∪ S.X := by
          rcases hz with ⟨h, _⟩ | ⟨h, _⟩
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ h
        have hzi1 : strat.strat z ≤ i + 1 := by rcases hz with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
        have hDNeg : S.DNegEdge z z' := Or.inl hz'
        have hz'Y : z' ∈ S.Y ∪ S.X := hDClosed z hzY z' (S.DEdge_of_DNegEdge hDNeg)
        have hlt : strat.strat z' < strat.strat z := strat.negDep_lt z hzY z' hDNeg
        simp only [Schema.stratum, Finset.mem_filter]
        exact ⟨hz'Y, by omega⟩
      have hDClosed1 : (S.stratRestrict strat.strat (i + 1)).DClosed :=
        Schema.stratRestrict_DClosed hDClosed strat (i + 1)
      have hWFX1 : (S.stratRestrict strat.strat (i + 1)).WellFormedX :=
        Schema.stratRestrict_WellFormedX hWFX strat.strat (i + 1)
      refine ⟨maxTypingAgreeing_subset _ G _ _, ?_⟩
      show (S.stratRestrict strat.strat (i + 1)).CorrectTyping G
        (maxTypingAgreeing (S.stratRestrict strat.strat (i + 1)) G (S.stratum strat.strat i)
          (stratTypingSeq S strat.strat G i))
      exact maxTypingAgreeing_correct hWFX1 hWFExt hWFExtra hNEF hDClosed1 hsub_i' hcorrect_i' hLo

/-- **Proposition 1.** For every schema `S`, stratification `σ` of `S`, and
graph `G`, the typing `τ_max(S,σ,G)` is a correct typing. -/
theorem proposition1 {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat : Stratification S) (G : Graph) :
    S.CorrectTyping G (Typing8 G S strat) := by
  have hk : S.stratRestrict strat.strat strat.k = S := by
    unfold Schema.stratRestrict
    congr 1
    · exact Finset.filter_true_of_mem
        (fun z hz => (strat.mem_range z (Finset.mem_union_left _ hz)).2)
    · exact Finset.filter_true_of_mem
        (fun z hz => (strat.mem_range z (Finset.mem_union_right _ hz)).2)
    · exact Finset.filter_true_of_mem
        (fun z hz => (strat.mem_range z (Finset.mem_union_right _ (S.A_subX hz))).2)
  have := (stratTypingSeq_correct hWFX hWFExt hWFExtra hNEF hDClosed strat G strat.k).2
  rw [hk] at this
  exact this

end ShexLean.InheritanceDisjunction
