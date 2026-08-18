import ShexLean.Shex2025Inheritance.CorrectTyping
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
Definitions 7-8 (§4.3) and Proposition 1 of the 2025 "Shape Expressions
with Inheritance" paper — stratification, the maximal typing, and its
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

This whole file is structurally the 2017 formalism's `ShexLean/
Proposition1.lean` (Definition 3/4 there) ported to the new `Schema`/
`Satisfies`. The schema-restriction/`maxTypingAgreeing`/`stratTypingSeq`
scaffolding transfers over essentially mechanically — restricting `Y`, `X`,
`A` by a stratum filter instead of `.labels`, and `Schema.CorrectTyping`'s
abstract-label case threading through unchanged.

**What does *not* transfer mechanically**: 2017's `Satisfies.agree`/
`Satisfies.stratMono` are proved by plain structural recursion on the AST,
because `⊢`/`⊨` there never dereference `def` — a shape reference only
ever consults `typing`. Here, `.extends` genuinely dereferences *other
labels' own definitions* (ancestors' `ext-te(x)`/`restr(x)`), so an
agreement/monotonicity fact about `Satisfies` has to reason about the
*schema's* dependency structure (`Schema.dep`/`depExtends`, via `D_S`
reachability), not just a single shape expression's own syntax tree — and
has to go through the `Fuel`-indexed machinery `Satisfies` is built on
(`ShexLean/Shex2025Inheritance/Termination.lean`), following the same induction
skeleton `stableE`/`stableM`/`stableFuel` used there, but tracking typing
*agreement on the dependency closure* instead of fuel sufficiency.
-/

namespace ShexLean.Inheritance

/-- `τ_{|Z}`: the restriction of `τ` to the node-type associations whose
label is in `Z` (2017's `Typing.restrictTo`, `ShexLean/Shex2017Schemas/Proposition1.lean`,
duplicated here — trivial in content, but kept local so this `Inheritance`
subtree doesn't need to import the entire 2017 proof chain for it; a plain
function rather than `Typing.restrictTo` dot notation, since `Typing`
resolves to the shared `ShexLean.Typing` and dot notation would look there
first, not here). -/
def restrictTyping (τ : Typing) (Z : Finset Label) : Typing := τ.filter (fun p => p.2 ∈ Z)

theorem mem_restrictTyping {τ : Typing} {Z : Finset Label} {n : RDFNode} {z : Label} :
    (n, z) ∈ restrictTyping τ Z ↔ (n, z) ∈ τ ∧ z ∈ Z := by simp [restrictTyping]

/-- Two typings with the same restriction to `Z` agree (as an `Iff`) on
every label in `Z`. -/
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

/-- Well-formedness beyond `WellFormedX`/`ExtAcyclic`: every label
`D_S`-reachable from a declared label (`z ∈ Y ∪ X`) is itself declared.
Needed for the same reason 2017's `Schema.Closed` was (`ShexLean/
Proposition1.lean`'s module docstring) — `shapeDef` is total on all of
`Label`, so nothing stops a schema from referencing an undeclared
label, but `Stratification`'s conditions are only required to hold with
`z ∈ Y ∪ X` as the edge's source. -/
def Schema.DClosed (S : Schema) : Prop :=
  ∀ z ∈ S.Y ∪ S.X, ∀ z', S.DEdge z z' → z' ∈ S.Y ∪ S.X

/-- Definition 7 (stratification), stated via `D_S`'s *edges* (`DEdge`/
`DNegEdge`) rather than the paper's literal *paths* — equivalent by
induction on path length (`Stratification.lt_of_negPath` below derives the
path form), and the edge form is what `maxTypingAgreeing_correct`
(further down) actually needs, exactly mirroring 2017's `Stratification`
(`ShexLean/Shex2017Schemas/Stratification.lean`). -/
structure Stratification (S : Schema) where
  k : ℕ
  strat : Label → ℕ
  mem_range : ∀ z ∈ S.Y ∪ S.X, 1 ≤ strat z ∧ strat z ≤ k
  dep_le : ∀ z ∈ S.Y ∪ S.X, ∀ z', S.DEdge z z' → strat z' ≤ strat z
  negDep_lt : ∀ z ∈ S.Y ∪ S.X, ∀ z', S.DNegEdge z z' → strat z' < strat z

/-- `S` admits a stratification (Definition 7's existence, matching the
paper's own use of "well known that stratified negation ... guarantees the
existence of a stratification" — asserted, not proved, by the paper
itself; likewise not proved here, following the same precedent set by the
2017 formalization, where `Schema.StratifiedNegation` is also just
`Nonempty (Stratification S)` with no separate existence theorem). -/
def Schema.StratifiedNegation (S : Schema) : Prop := Nonempty (Stratification S)

/-- "`dep` subsumes `dep-shape-neg`/`dep-extra-neg`" lifted to `DEdge`: any
negative edge is in particular an ordinary `D_S` edge. -/
theorem Schema.DEdge_of_DNegEdge {S : Schema} {z z' : Label} (h : S.DNegEdge z z') :
    S.DEdge z z' := by
  rcases h with h | h
  · exact Or.inl (Schema.dep_of_depShapeNeg h)
  · exact Or.inl (Schema.dep_of_depExtraNeg h)

/-- `Y ∪ X` membership propagates forward along any `D_S`-path, given
`Schema.DClosed`. -/
theorem Schema.mem_of_reach {S : Schema} (hDClosed : S.DClosed) {z z' : Label}
    (hzY : z ∈ S.Y ∪ S.X) (h : Relation.ReflTransGen S.DEdge z z') : z' ∈ S.Y ∪ S.X := by
  induction h with
  | refl => exact hzY
  | tail _ hstep ih => exact hDClosed _ ih _ hstep

/-- `strat` never increases along a `D_S`-path (Definition 7's first
bullet, in path form). -/
theorem Stratification.le_of_path {S : Schema} (hDClosed : S.DClosed) (strat : Stratification S)
    {z z' : Label} (hzY : z ∈ S.Y ∪ S.X) (h : Relation.ReflTransGen S.DEdge z z') :
    strat.strat z' ≤ strat.strat z := by
  induction h with
  | refl => exact le_refl _
  | tail hprev hstep ih => exact le_trans (strat.dep_le _ (S.mem_of_reach hDClosed hzY hprev) _ hstep) ih

/-- Along any `D_S`-path from `z` to `z'` that goes through a negative
edge `a → b` (`z ↝ a`, `a → b` negative, `b ↝ z'`), `strat` strictly
decreases overall (Definition 7's second bullet, in path form) — the
composition of `le_of_path` on either side of the strict `negDep_lt` step
in the middle. -/
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

`⊢`/`⊨` only ever depend on `τ` through its restriction to a set of labels
`Z` that is *closed* under `D_S` (`Schema.DClosedOn` below) and contains
everything the shape expression at hand can syntactically reach
(`ShapeExpr.depsIn`) — the 2025 analogue of 2017's `Satisfies.agree`
(`ShexLean/Shex2017Schemas/Proposition1.lean`), but now needing to reason about the
*schema's* dependency structure (since `.extends` dereferences other
labels' own definitions), and going through the `Fuel`-indexed machinery
`Satisfies` is built on, following the exact same one-way chain
(`agreeE → agreeM_noExtends`/`agreeM → agreeFuel`) as `stableE →
stableM_noExtends/stableM → stableFuel` in `ShexLean/Shex2025Inheritance/
Termination.lean`. -/

/-- The labels a shape expression could reach: `@z'` references anywhere
in it (`ShapeExpr.depsAux`) and `extends` targets anywhere in it
(`ShapeExpr.extendsTargets`, a full recursive walk — see that
definition's docstring for why it has to be). -/
def ShapeExpr.depsIn (s : ShapeExpr) (Z : Finset Label) : Prop :=
  (s.depsAux false).refs ⊆ Z ∧ s.extendsTargets ⊆ Z

/-- A further well-formedness condition `stratMono` needs, beyond
`WellFormedX`/`ExtAcyclic`/`WellFormedExtra`: `not` never contains
`extends`. Without it, `stratMono`'s `not` case would need *exact*
agreement between `τ`/`τ'` on every ancestor an `extends` buried inside the
negated content could reach — but those ancestors need not be confined to
`Lo` (`dep-extends` is deliberately never a *negative* dependency,
Definition 5), so nothing in `stratMono`'s own hypotheses would bound them.
Matches the spirit of the paper's own "Design choices" discussion, which
already restricts `extends` to conjunctions specifically to avoid this
flavour of complexity (there, with `or`; here, with `not`) — not exercised
by anything in the paper's own examples. With it, `not`'s content is
always `NoExtends`, so `stratMono`'s `not` case reuses
`stratMonoM_noExtends` directly. -/
def ShapeExpr.NotIsExtendsFree : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends _ _ => True
  | .or s1 s2 => s1.NotIsExtendsFree ∧ s2.NotIsExtendsFree
  | .and s1 s2 => s1.NotIsExtendsFree ∧ s2.NotIsExtendsFree
  | .not s => s.NoExtends

/-- Schema-wide: every label's entire definition. -/
def Schema.NotIsExtendsFree (S : Schema) : Prop := ∀ ℓ, (S.shapeDef ℓ).NotIsExtendsFree

/-- A `NoExtends` shape has no `extends` targets anywhere, by construction
(`extendsTargets` only ever produces something nonempty at an `.extends`
node, which `NoExtends` rules out entirely). -/
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

/-- `.refs` never actually depends on `neg` (only `.negRefs` does) — so a
`refs ⊆ Z` fact transfers across the `neg`-flip `.not` performs. -/
theorem ShapeExpr.depsAux_refs_indep (s : ShapeExpr) (neg1 neg2 : Bool) :
    (s.depsAux neg1).refs = (s.depsAux neg2).refs := by
  induction s generalizing neg1 neg2 with
  | constraint c => simp [ShapeExpr.depsAux]
  | ofShape h => simp [ShapeExpr.depsAux, Shape.depInfo]
  | «extends» xs h => simp [ShapeExpr.depsAux, Shape.depInfo]
  | or s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_refs]; rw [ih1 neg1 neg2, ih2 neg1 neg2]
  | and s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_refs]; rw [ih1 neg1 neg2, ih2 neg1 neg2]
  | not s _ => simp only [ShapeExpr.depsAux]

/-- The labels a triple expression's own triple constraints reference. -/
def TripleExpr.refs (e : TripleExpr) : Finset Label := e.tcs.image Prod.snd

/-- `Z` is closed under `D_S`: everything a member of `Z` depends on
(`dep` or `depExtends`) is also in `Z`. Generalizes `Schema.DClosed`
(the `Z = Y ∪ X` case) to an arbitrary label set, since Proposition 1
below needs it for `Z = ` a stratum, not just the whole schema. -/
def Schema.DClosedOn (S : Schema) (Z : Finset Label) : Prop :=
  ∀ z ∈ Z, ∀ z', S.DEdge z z' → z' ∈ Z

/-- Membership in a `D_S`-closed `Z` propagates along any `D_S`-path
(generalizes `Schema.mem_of_reach`, whose `Z = Y ∪ X` instance this now
subsumes). -/
theorem Schema.reach_mem {S : Schema} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {z z' : Label} (hz : z ∈ Z) (h : Relation.ReflTransGen S.DEdge z z') : z' ∈ Z := by
  induction h with
  | refl => exact hz
  | tail _ hstep ih => exact hZ _ ih _ hstep

/-- If `x ∈ Z` and `Z` is `D_S`-closed, then `x`'s own definition only
reaches labels in `Z` too — i.e. `Z`-closure is exactly what's needed to
recurse one more `extends`-hop deep and stay inside `Z`. -/
theorem Schema.shapeDef_depsIn {S : Schema} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {x : Label} (hx : x ∈ Z) : (S.shapeDef x).depsIn Z :=
  ⟨fun _ hz' => hZ x hx _ (Or.inl hz'), fun _ hz' => hZ x hx _ (Or.inr (Or.inl hz'))⟩

/-- `S.ancSet xs ⊆ Z` whenever `xs ⊆ Z` and `Z` is `D_S`-closed: every
ancestor reached by a rule-18 partition stays inside `Z` too. -/
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

/-- Every label in `S.ancSet xs` is in `S.X` (immediate from `Schema.anc`'s
own definition, which filters over `S.X`). -/
theorem Schema.mem_ancSet_mem_X {S : Schema} {xs : Finset Label} {x : Label}
    (hx : x ∈ S.ancSet xs) : x ∈ S.X := by
  unfold Schema.ancSet at hx
  obtain ⟨y, _, hyx⟩ := Finset.mem_biUnion.mp hx
  unfold Schema.anc at hyx
  simp only [Finset.mem_filter] at hyx
  exact hyx.1

/-- `SatisfiesEFuel` (Table 1) only depends on `τ` through its restriction
to `Z`, given `e`'s own references are `⊆ Z`. No schema-closure hypothesis
needed at all — Table 1 never does a schema lookup, exactly as in
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

/-- `M^e` (Table 3's `Me`) doesn't just *agree with*, it is *literally
equal* regardless of `τ` vs `τ'`, given they agree on `e`'s references —
every triple's membership test only ever consults `τ` on a label in
`e.refs ⊆ Z`. This is why rule 17's own agreement case (inside `agreeM`
below) can reuse `agreeE` directly at a *shared* `M^e`, rather than needing
a further congruence argument. -/
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

/-- `M^{e'}` (Table 3's `Mnotin`) is likewise literally equal — it's built
from `Me` (equal by `Me_eq`) and a `props`-based filter that doesn't
mention `τ` at all. -/
theorem Mnotin_eq {τ τ' : Typing} {Z : Finset Label}
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) {e : TripleExpr} (href : e.refs ⊆ Z)
    (M : Finset Triple) : Mnotin τ M e = Mnotin τ' M e := by
  unfold Mnotin
  rw [Me_eq hagree href M]

/-- `SatisfiesMFuel` (Table 3) only depends on `τ` through its restriction
to `Z`, on any `NoExtends` shape (`u`'s own references `⊆ Z` is enough —
no schema-closure hypothesis needed, since `u` never triggers rule 18).
Proved *before* the general case for the same reason `stableM_noExtends`
was: `restr(x)`'s evaluation (inside `agreeM`'s `.extends` case) isn't on a
subterm of the shape that induction is on, so that induction's own IH
can't reach it — this lemma is what's invoked instead. -/
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

/-- `ext-te(x)`'s own references are among `def(x)`'s (it's a sub-part of
it) — the `refs`-containment analogue of `Termination.lean`'s
`extTe_size_le`. -/
theorem extTe_refs_subset {S : Schema} (hWFX : S.WellFormedX) {x : Label} (hx : x ∈ S.X) :
    (S.shapeDef x).extTe.refs ⊆ ((S.shapeDef x).depsAux false).refs := by
  obtain ⟨xs', h', hcase⟩ := hWFX x hx
  rcases hcase with heq | ⟨u, heq⟩ <;> rw [heq]
  · simp only [ShapeExpr.extTe, ShapeExpr.depsAux, Shape.depInfo, TripleExpr.refs]
    exact Finset.Subset.refl _
  · simp only [ShapeExpr.extTe, ShapeExpr.depsAux, Shape.depInfo, DepInfo.union_refs,
      TripleExpr.refs]
    exact Finset.subset_union_left

/-- `restr(x)`'s own references are among `def(x)`'s — the
`refs`-containment analogue of `Termination.lean`'s
`restrOf_noExtends_and_size_le`. -/
theorem restrOf_refs_subset {S : Schema} {x : Label} {u : ShapeExpr}
    (hu : (S.shapeDef x).restrOf = some u) :
    (u.depsAux false).refs ⊆ ((S.shapeDef x).depsAux false).refs := by
  generalize hg : S.shapeDef x = e at hu
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' h' =>
          simp only [ShapeExpr.restrOf] at hu
          obtain rfl := Option.some.inj hu
          simp only [ShapeExpr.depsAux, DepInfo.union_refs]
          exact Finset.subset_union_right
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- `restr(x)`'s own negative references are among `def(x)`'s. -/
theorem restrOf_negRefs_subset {S : Schema} {x : Label} {u : ShapeExpr}
    (hu : (S.shapeDef x).restrOf = some u) :
    (u.depsAux false).negRefs ⊆ ((S.shapeDef x).depsAux false).negRefs := by
  generalize hg : S.shapeDef x = e at hu
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' h' =>
          simp only [ShapeExpr.restrOf] at hu
          obtain rfl := Option.some.inj hu
          simp only [ShapeExpr.depsAux, DepInfo.union_negRefs]
          exact Finset.subset_union_right
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- The `extendsTargets`-containment analogue of `restrOf_refs_subset`/
`restrOf_negRefs_subset`: `restr(x)`'s own extends-targets are among
`def(x)`'s (immediate, since `extendsTargets` recurses through `and`). -/
theorem restrOf_extendsTargets_subset {S : Schema} {x : Label} {u : ShapeExpr}
    (hu : (S.shapeDef x).restrOf = some u) :
    u.extendsTargets ⊆ (S.shapeDef x).extendsTargets := by
  generalize hg : S.shapeDef x = e at hu
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' h' =>
          simp only [ShapeExpr.restrOf] at hu
          obtain rfl := Option.some.inj hu
          simp only [ShapeExpr.extendsTargets]
          exact Finset.subset_union_right
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- `SatisfiesMFuel` (Table 3) only depends on `τ` through its restriction
to `Z`, given `s.depsIn Z`, `Z` is `D_S`-closed, and a rank witness
(`Schema.RankOk`, `Termination.lean`) covering `s`'s cascading `.extends`
chains — only `WellFormedX` is needed, no further restriction on where
`extends` nodes occur. Everything except `.extends` is copy-paste from
`agreeM_noExtends` with `depsIn`'s two components threaded through instead
of just `.refs`; `.extends` combines `agreeE` (for `h.triples`/`ext-te(x)`)
with the rank-`r'` induction hypothesis `ihr` (for `restr(x)`, in place of
`agreeM_noExtends`), exactly mirroring `stableMGen`'s own `.extends` case
in `Termination.lean`. -/
theorem agreeM {S : Schema} (hWFX : S.WellFormedX)
    {G : Graph} {τ τ' : Typing} {Z : Finset Label} (hZ : S.DClosedOn Z)
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) :
    ∀ r s, Schema.RankOk S r s → s.depsIn Z →
      ∀ fuel (M : Finset Triple), SatisfiesMFuel fuel S G τ M s ↔ SatisfiesMFuel fuel S G τ' M s := by
  intro r
  induction r with
  | zero =>
      intro s hs hdeps fuel M
      exact agreeM_noExtends hagree s hs hdeps.1 fuel M
  | succ r' ihr =>
      intro s
      induction s with
      | constraint c => intro _ _ fuel M; rcases fuel with _ | f <;> rfl
      | ofShape h =>
          intro _ hdeps fuel M
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
      | «extends» xs h =>
          intro hRank hdeps fuel M
          rcases fuel with _ | f
          · rfl
          obtain ⟨hrefsZ, hxsZ⟩ := hdeps
          simp only [ShapeExpr.extendsTargets] at hxsZ
          have hancZ : S.ancSet xs ⊆ Z := S.ancSet_subset hZ hxsZ
          have hRankAt : ∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
              Schema.RankOk S r' u := hRank
          show (∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
                SatisfiesMFuel f S G τ M' (.ofShape h) ∧
                (∀ x ∈ S.ancSet xs, SatisfiesEFuel f S G τ (Mx x) (S.shapeDef x).extTe) ∧
                (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
                  SatisfiesMFuel f S G τ ((S.anc x).biUnion Mx) u)) ↔
              (∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
                SatisfiesMFuel f S G τ' M' (.ofShape h) ∧
                (∀ x ∈ S.ancSet xs, SatisfiesEFuel f S G τ' (Mx x) (S.shapeDef x).extTe) ∧
                (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
                  SatisfiesMFuel f S G τ' ((S.anc x).biUnion Mx) u))
          refine exists_congr fun M' => exists_congr fun Mx => and_congr_right fun _ => ?_
          have he : SatisfiesMFuel f S G τ M' (.ofShape h) ↔ SatisfiesMFuel f S G τ' M' (.ofShape h) :=
            agreeM_noExtends hagree (.ofShape h) trivial hrefsZ f M'
          have hext : (∀ x ∈ S.ancSet xs, SatisfiesEFuel f S G τ (Mx x) (S.shapeDef x).extTe) ↔
              (∀ x ∈ S.ancSet xs, SatisfiesEFuel f S G τ' (Mx x) (S.shapeDef x).extTe) := by
            refine forall_congr' fun x => forall_congr' fun hx => ?_
            have hxX : x ∈ S.X := Schema.mem_ancSet_mem_X hx
            have hxZ : x ∈ Z := hancZ hx
            exact agreeE hagree (S.shapeDef x).extTe
              (Finset.Subset.trans (extTe_refs_subset hWFX hxX) (S.shapeDef_depsIn hZ hxZ).1) f (Mx x)
          have hrestr : (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
                SatisfiesMFuel f S G τ ((S.anc x).biUnion Mx) u) ↔
              (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
                SatisfiesMFuel f S G τ' ((S.anc x).biUnion Mx) u) := by
            refine forall_congr' fun x => forall_congr' fun hx => forall_congr' fun u => ?_
            refine imp_congr_right fun hru => ?_
            have hxZ : x ∈ Z := hancZ hx
            have hurefs : (u.depsAux false).refs ⊆ Z :=
              Finset.Subset.trans (restrOf_refs_subset hru) (S.shapeDef_depsIn hZ hxZ).1
            have huext : u.extendsTargets ⊆ Z :=
              Finset.Subset.trans (restrOf_extendsTargets_subset hru) (S.shapeDef_depsIn hZ hxZ).2
            exact ihr u (hRankAt x hx u hru) ⟨hurefs, huext⟩ f _
          rw [he, hext, hrestr]
      | or s1 s2 ih1 ih2 =>
          intro hRank hdeps fuel M
          rcases fuel with _ | f
          · rfl
          simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
            ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
          show SatisfiesMFuel f S G τ M s1 ∨ SatisfiesMFuel f S G τ M s2 ↔
            SatisfiesMFuel f S G τ' M s1 ∨ SatisfiesMFuel f S G τ' M s2
          rw [ih1 hRank.1 ⟨hdeps.1.1, hdeps.2.1⟩ f M, ih2 hRank.2 ⟨hdeps.1.2, hdeps.2.2⟩ f M]
      | and s1 s2 ih1 ih2 =>
          intro hRank hdeps fuel M
          rcases fuel with _ | f
          · rfl
          simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
            ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
          show SatisfiesMFuel f S G τ M s1 ∧ SatisfiesMFuel f S G τ M s2 ↔
            SatisfiesMFuel f S G τ' M s1 ∧ SatisfiesMFuel f S G τ' M s2
          rw [ih1 hRank.1 ⟨hdeps.1.1, hdeps.2.1⟩ f M, ih2 hRank.2 ⟨hdeps.1.2, hdeps.2.2⟩ f M]
      | not s ih =>
          intro hRank hdeps fuel M
          rcases fuel with _ | f
          · rfl
          simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, ShapeExpr.extendsTargets] at hdeps
          rw [s.depsAux_refs_indep true false] at hdeps
          show ¬ SatisfiesMFuel f S G τ M s ↔ ¬ SatisfiesMFuel f S G τ' M s
          rw [ih hRank hdeps f M]

/-- `SatisfiesFuel` (Table 2) on a `NoExtends` shape: no schema-closure
hypothesis needed at all, exactly like `agreeM_noExtends`, which handles
`.ofShape`'s own inner Table 3 check (`.extends` is impossible under
`NoExtends`). Needed by `stratMonoFuel`'s own `.not` case (a `not` node's
content is always `NoExtends`, by `ShapeExpr.NotIsExtendsFree`), which
would otherwise have to reach for the much heavier `agreeFuel` below (and
its `DClosedOn`/schema-wide-agreement requirements that a `NoExtends`
shape never actually needs). -/
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

/-- `SatisfiesFuel` (Table 2) only depends on `τ` through its restriction
to `Z`, given `s.depsIn Z` and `Z` is `D_S`-closed — only `WellFormedX`/
`ExtAcyclic` needed (the latter to supply `agreeM`'s rank witness via
`Schema.rankOk_any`). The `.ofShape`/`.extends` cases are immediate from
`agreeM`; everything else is self-recursion — exactly mirroring
`stableFuel`'s own structure. -/
theorem agreeFuel {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic)
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
      exact agreeM hWFX hZ hagree (S.X.sup S.extRank + 1) (.ofShape h)
        (Schema.rankOk_any hAcyclic hWFX _) hdeps f (neigh G n)
  | «extends» xs h =>
      intro hdeps fuel n
      rcases fuel with _ | f
      · rfl
      show SatisfiesMFuel f S G τ (neigh G n) (.extends xs h) ↔
        SatisfiesMFuel f S G τ' (neigh G n) (.extends xs h)
      exact agreeM hWFX hZ hagree (S.X.sup S.extRank + 1) (.extends xs h)
        (Schema.rankOk_any hAcyclic hWFX _) hdeps f (neigh G n)
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

/-- `Satisfies` (the real, fuel-free relation) only depends on `τ` through
its restriction to `Z`, under the same conditions as `agreeFuel`: since
`reqFuelGen S s` doesn't depend on `τ` at all, `Satisfies S G τ n s` and
`Satisfies S G τ' n s` use the *same* concrete fuel value, so this is just
`agreeFuel` at that shared value. -/
theorem Satisfies.agree {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic)
    {G : Graph} {τ τ' : Typing} {Z : Finset Label} (hZ : S.DClosedOn Z)
    (hagree : ∀ n z, z ∈ Z → ((n, z) ∈ τ ↔ (n, z) ∈ τ')) {s : ShapeExpr} (hdeps : s.depsIn Z)
    (n : RDFNode) : Satisfies S G τ n s ↔ Satisfies S G τ' n s :=
  agreeFuel hWFX hAcyclic hZ hagree s hdeps (Schema.reqFuelGen S s + 1) n

/-! ### A subtlety this file's `stratMono` needs that 2017's never did

Table 3's rule 17 filters the neighbourhood through `Me`/`Mnotin` — the
"already correctly typed" and "leftover" parts of `M`, computed *from
`τ` itself* — which makes `SatisfiesMFuel`/`Satisfies` genuinely
**non-monotone** in `τ`, even with no negation anywhere: growing `τ` can
move a triple from `Mnotin` into `Me`, and if `Me` was already matching a
*bare* (non-starred) triple constraint like `p @z` (which needs `M` to be
*exactly* a singleton), growing it past size 1 breaks that match. A
concrete instance of this was checked directly in Lean before writing this
section: a shape `⟨closed := false, extra := some {p}, triples := p @z⟩`
satisfied by `M = {t1, t2}` under `τ₁ = {(t1.obj, z)}` (`Me = {t1}`, a
singleton) stops being satisfied under `τ₂ = τ₁ ∪ {(t2.obj, z)} ⊇ τ₁`
(`Me` grows to `{t1, t2}`, no longer a singleton).

The paper's own appendix proof of Proposition 1 needs, and states, exactly
the fix for this — an auxiliary invariant it calls "(*)": *for every
`[closed][extra P]⟨e⟩` sub-expression, for every `p @u ∈ tcs(e)`, `p ∉ P`*
— i.e. a shape's own triple-constraint properties never overlap its
`extra` set. It's never phrased as a standalone definition in the paper's
main text, only used inside the Proposition 1 proof itself, so — the same
way `Schema.ExtAcyclic` (`Termination.lean`) makes one of the paper's own
implicit well-definedness conditions explicit — this file adds it here as
an explicit hypothesis, `Schema.WellFormedExtra`.

*Why it fixes the problem*: given `(*)`, whenever a shape succeeds at all,
`Mnotin`'s own success condition (`props(Mnotin) ⊆ P`) forces every
`props(e)`-matching triple in `M` to already be in `Me` (none can be
"left over" via `extra`, since `(*)` means `extra` never covers `e`'s own
properties) — i.e. `Me` is already the *maximal possible* value,
`M.filter (pred ∈ props e)`, a set that doesn't mention `τ` at all. Once
`Me` is pinned at its ceiling, it cannot grow any further no matter how
much more of `τ` is added, which is exactly what restores monotonicity
for Table 3's positive (non-`extra`-abusing) uses of `Me`. -/

/-- Definition 5's implicit invariant "(*)": a shape's own triple
constraints never use a property also listed in its `extra` set. -/
def Shape.WellFormedExtra (h : Shape) : Prop := h.triples.props ∩ h.extra.getD ∅ = ∅

/-- "(*)" required of every shape anywhere in a `ShapeExpr` (`.ofShape`
or the `h` of an `.extends`, wherever either occurs, including nested via
`or`/`and`/`not`/a restriction). -/
def ShapeExpr.WellFormedExtra : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape h => h.WellFormedExtra
  | .extends _ h => h.WellFormedExtra
  | .or s1 s2 => s1.WellFormedExtra ∧ s2.WellFormedExtra
  | .and s1 s2 => s1.WellFormedExtra ∧ s2.WellFormedExtra
  | .not s => s.WellFormedExtra

/-- "(*)" required schema-wide: every label's entire definition. -/
def Schema.WellFormedExtra (S : Schema) : Prop := ∀ ℓ, (S.shapeDef ℓ).WellFormedExtra

/-- `restr(x)`'s "(*)" invariant is inherited from `def(x)`'s own. -/
theorem restrOf_wellFormedExtra {S : Schema} (hWFExtra : S.WellFormedExtra) {x : Label}
    {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u) : u.WellFormedExtra := by
  have hWFx := hWFExtra x
  generalize hg : S.shapeDef x = e at hu hWFx
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' h' =>
          simp only [ShapeExpr.restrOf] at hu
          simp only [ShapeExpr.WellFormedExtra] at hWFx
          obtain rfl := Option.some.inj hu
          exact hWFx.2
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- `restr(x)`'s "no `extends` under `not`" invariant is inherited from
`def(x)`'s own. -/
theorem restrOf_notIsExtendsFree {S : Schema} (hNEF : S.NotIsExtendsFree) {x : Label}
    {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u) : u.NotIsExtendsFree := by
  have hNx := hNEF x
  generalize hg : S.shapeDef x = e at hu hNx
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' h' =>
          simp only [ShapeExpr.restrOf] at hu
          simp only [ShapeExpr.NotIsExtendsFree] at hNx
          obtain rfl := Option.some.inj hu
          exact hNx.2
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- `SatisfiesEFuel` (Table 1) is unconditionally monotone in `τ`: growing
`τ` (for a *fixed* `M`) never breaks a match. Table 1 has no `extra`-style
filtering and no negation, so — unlike everything past this point — this
needs no `Z`/`Lo`/`WellFormedExtra` bookkeeping at all. -/
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

/-- If `props(Mnotin τ M e) ⊆ P'` (rule 17's own leftover-properties
condition) and `e`/`P'` satisfy "(*)" (`e.props ∩ P' = ∅`), then `Me τ M e`
is already forced to be `M`'s entire `props(e)`-matching part — a set that
doesn't mention `τ` at all. -/
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

/-- Once `Me` is forced to its ceiling (`Me_eq_filter_of_success`, given
success at `τ`), it cannot grow any further along `τ ⊆ τ'` — sandwiched
between `Me τ M e` (below) and the same `τ`-independent ceiling (above). -/
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

/-- Rule 17 (`.ofShape h`) is monotone in `τ`, given `h.WellFormedExtra`
("(*)"): `Me`/`Mnotin` don't actually change (`Me_stable`), so the
inner `SatisfiesEFuel` check transfers via `monoE`, and `Mnotin` becomes
literally empty (hence trivially `⊆` anything). -/
theorem monoM_ofShape {S : Schema} {G : Graph} {τ τ' : Typing} (hsub : τ ⊆ τ') {h : Shape}
    (hWF : h.WellFormedExtra) (fuel : ℕ) (M : Finset Triple) :
    SatisfiesMFuel (fuel + 1) S G τ M (.ofShape h) →
      SatisfiesMFuel (fuel + 1) S G τ' M (.ofShape h) := by
  rintro ⟨hE, hMnotin, hclosed⟩
  have hMeeq := Me_stable hsub hWF hMnotin
  have hMnotineq : Mnotin τ' M h.triples = Mnotin τ M h.triples := by
    unfold Mnotin; rw [hMeeq]
  exact ⟨hMeeq ▸ monoE hsub h.triples fuel (Me τ M h.triples) hE, hMnotineq ▸ hMnotin, hclosed⟩

/-! ### `stratMono`: growing `τ` for positive positions, exact agreement
under `not` -/

/-- On a `NoExtends` shape: growing `τ` (`hsub`) transports satisfaction,
*given* `h.WellFormedExtra` at every `.ofShape` reached and the shape's own
negative references (Definition 5's `negRefs`, now under latching
semantics) confined to `Lo`, on which `τ`/`τ'` agree exactly. `.not`
switches to `agreeM_noExtends` (exact agreement), using
`negRefs_true_eq_refs` to see that the *whole* content under a `not` is
bounded by the outer call's `negRefs` — not just its own not-yet-further-
negated references — which is exactly why `depsAux` had to latch rather
than toggle (see that definition's docstring). -/
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

/-- The general `stratMono`, combining growing `τ` (positive positions,
via `monoM_ofShape`/`monoE`) with exact agreement (negated positions, via
`stratMonoM_noExtends`, which `ShapeExpr.NotIsExtendsFree` guarantees is
enough) — the `.extends` case reuses `agreeM`'s rank-indexed
induction/witness-reuse pattern (only `WellFormedX`, no further
restriction on where `extends` nodes occur), but with `monoE` in place of
`agreeE` for `M'`/`ext-te(x)` (no `WellFormedExtra`/agreement needed there
at all, Table 1 is unconditionally monotone) and `stratMonoM_noExtends`
recursed into via the rank-`r'` induction hypothesis `ihr` in place of
`agreeM_noExtends` for `restr(x)` (which only ever needs *its own*
negative-dependency bound, via `restrOf_negRefs_subset` + the schema-wide
`hLo`). `WellFormedExtra` and `NotIsExtendsFree` are both independently
required, orthogonal to the rank machinery. -/
theorem stratMonoM {S : Schema} (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree)
    {G : Graph} {τ τ' : Typing} {Z Lo : Finset Label}
    (hZ : S.DClosedOn Z) (hsub : τ ⊆ τ') (hagree : ∀ n z, z ∈ Lo → ((n, z) ∈ τ ↔ (n, z) ∈ τ'))
    (hLo : ∀ z ∈ Z, ((S.shapeDef z).depsAux false).negRefs ⊆ Lo) :
    ∀ r (s : ShapeExpr), Schema.RankOk S r s → s.depsIn Z → s.WellFormedExtra → s.NotIsExtendsFree →
      ((s.depsAux false).negRefs ⊆ Lo) →
      ∀ fuel (M : Finset Triple), SatisfiesMFuel fuel S G τ M s → SatisfiesMFuel fuel S G τ' M s := by
  intro r
  induction r with
  | zero =>
      intro s hNoExt _ hWF _ hneg fuel M hSat
      exact stratMonoM_noExtends hsub hagree s hNoExt hWF hneg fuel M hSat
  | succ r' ihr =>
      intro s
      induction s with
      | constraint c =>
          intro _ _ _ _ _ fuel M h
          rcases fuel with _ | f
          · exact h
          · exact h
      | ofShape h =>
          intro _ _ hWFh _ _ fuel M hSat
          rcases fuel with _ | f
          · exact hSat
          exact monoM_ofShape hsub hWFh f M hSat
      | «extends» xs h =>
          intro hRank hdeps hWF _ _ fuel M hSat
          rcases fuel with _ | f
          · exact hSat
          obtain ⟨_, hxsZ⟩ := hdeps
          simp only [ShapeExpr.extendsTargets] at hxsZ
          have hancZ : S.ancSet xs ⊆ Z := S.ancSet_subset hZ hxsZ
          have hRankAt : ∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
              Schema.RankOk S r' u := hRank
          obtain ⟨M', Mx, hdu, hE, hExt, hRestr⟩ := hSat
          have hE' : SatisfiesMFuel f S G τ' M' (.ofShape h) := by
            rcases f with _ | f'
            · exact hE
            · exact monoM_ofShape hsub hWF f' M' hE
          refine ⟨M', Mx, hdu, hE',
            fun x hx => monoE hsub _ f (Mx x) (hExt x hx), ?_⟩
          intro x hx u hru
          have hxX : x ∈ S.X := Schema.mem_ancSet_mem_X hx
          have hxZ : x ∈ Z := hancZ hx
          have hWFu : u.WellFormedExtra := restrOf_wellFormedExtra hWFExtra hru
          have hNEFu : u.NotIsExtendsFree := restrOf_notIsExtendsFree hNEF hru
          have hnegU : (u.depsAux false).negRefs ⊆ Lo :=
            Finset.Subset.trans (restrOf_negRefs_subset hru) (hLo x hxZ)
          have hurefsZ : u.depsIn Z := by
            have hurefs : (u.depsAux false).refs ⊆ Z :=
              Finset.Subset.trans (restrOf_refs_subset hru) (S.shapeDef_depsIn hZ hxZ).1
            have huext : u.extendsTargets ⊆ Z :=
              Finset.Subset.trans (restrOf_extendsTargets_subset hru) (S.shapeDef_depsIn hZ hxZ).2
            exact ⟨hurefs, huext⟩
          exact ihr u (hRankAt x hx u hru) hurefsZ hWFu hNEFu hnegU f _ (hRestr x hx u hru)
      | or s1 s2 ih1 ih2 =>
          intro hRank hdeps hWF hNEF' hneg fuel M hSat
          rcases fuel with _ | f
          · exact hSat
          simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
            ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
          simp only [ShapeExpr.WellFormedExtra] at hWF
          simp only [ShapeExpr.NotIsExtendsFree] at hNEF'
          simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
          rcases hSat with h1 | h1
          · exact Or.inl (ih1 hRank.1 ⟨hdeps.1.1, hdeps.2.1⟩ hWF.1 hNEF'.1 hneg.1 f M h1)
          · exact Or.inr (ih2 hRank.2 ⟨hdeps.1.2, hdeps.2.2⟩ hWF.2 hNEF'.2 hneg.2 f M h1)
      | and s1 s2 ih1 ih2 =>
          intro hRank hdeps hWF hNEF' hneg fuel M hSat
          rcases fuel with _ | f
          · exact hSat
          simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
            ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
          simp only [ShapeExpr.WellFormedExtra] at hWF
          simp only [ShapeExpr.NotIsExtendsFree] at hNEF'
          simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
          exact ⟨ih1 hRank.1 ⟨hdeps.1.1, hdeps.2.1⟩ hWF.1 hNEF'.1 hneg.1 f M hSat.1,
            ih2 hRank.2 ⟨hdeps.1.2, hdeps.2.2⟩ hWF.2 hNEF'.2 hneg.2 f M hSat.2⟩
      | not s _ =>
          intro _ _ hWF hNEF' hneg fuel M hSat
          rcases fuel with _ | f
          · exact hSat
          simp only [ShapeExpr.WellFormedExtra] at hWF
          simp only [ShapeExpr.NotIsExtendsFree] at hNEF'
          simp only [ShapeExpr.depsAux] at hneg
          rw [s.negRefs_true_eq_refs, s.depsAux_refs_indep true false] at hneg
          show ¬ SatisfiesMFuel f S G τ' M s
          exact fun hc => hSat ((agreeM_noExtends hagree s hNEF' hneg f M).mpr hc)

/-- `stratMono` for `SatisfiesFuel` (Table 2): only `WellFormedX`/
`ExtAcyclic` needed (the latter supplying `stratMonoM`'s rank witness via
`Schema.rankOk_any`, exactly as `agreeFuel` does for `agreeM`). The
`.ofShape`/`.extends` cases are immediate from `stratMonoM`; everything
else is self-recursion — mirroring `stableFuel`/`agreeFuel`'s own
structure. -/
theorem stratMonoFuel {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic)
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
      exact stratMonoM hWFExtra hNEF hZ hsub hagree hLo (S.X.sup S.extRank + 1) (.ofShape h)
        (Schema.rankOk_any hAcyclic hWFX _) hdeps hWFh hNEF' hneg f (neigh G n) hSat
  | «extends» xs h =>
      intro hdeps hWFh hNEF' hneg fuel n hSat
      rcases fuel with _ | f
      · exact hSat
      exact stratMonoM hWFExtra hNEF hZ hsub hagree hLo (S.X.sup S.extRank + 1) (.extends xs h)
        (Schema.rankOk_any hAcyclic hWFX _) hdeps hWFh hNEF' hneg f (neigh G n) hSat
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

/-- `nodes(G) × (Y ∪ X)`: the universe of every possible node-type
association for `G` by `S`. -/
def Schema.univTyping (S : Schema) (G : Graph) : Typing := G.nodes ×ˢ (S.Y ∪ S.X)

/-- `Y_i^σ ∪ X_i^σ = {z ∈ Y ∪ X | σ(z) ≤ i}`. -/
def Schema.stratum (S : Schema) (strat : Label → ℕ) (i : ℕ) : Finset Label :=
  (S.Y ∪ S.X).filter (fun z => strat z ≤ i)

theorem Schema.stratum_mono {S : Schema} {strat : Label → ℕ} {i j : ℕ} (h : i ≤ j) :
    S.stratum strat i ⊆ S.stratum strat j := by
  intro z hz
  simp only [Schema.stratum, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hz.2.trans h⟩

/-- `S_i^σ = (Y_i^σ, X_i^σ, def, A_i^σ)`: the restriction of `S` to labels
of stratum `≤ i`, keeping the same definitions. -/
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

/-- `maxTypingAgreeing S' G Lo fixed`: the union of all correct typings of
`G` by `S'` that agree with `fixed` on `Lo`. Generalizes `S'`'s own
"maximal correct typing" (`Lo = ∅`) with the extra agreement constraint
Definition 8 needs to glue strata together — exactly 2017's
`maxTypingAgreeing` (`ShexLean/Shex2017Schemas/Proposition1.lean`), with `Schema.
CorrectTyping`/`restrictTyping` in place of the 2017 versions. -/
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

/-- `maxTypingAgreeing` is itself a correct typing, provided `Lo ⊇` every
`S'`-label's own negative dependencies. The abstract-label case
(`Schema.CorrectTyping`'s second bullet) transports exactly like the
plain case, applying `stratMonoM` to `S'.shapeDef x` (the witnessing
descendant) instead of `S'.shapeDef L`. -/
theorem maxTypingAgreeing_correct {S' : Schema} (hWFX : S'.WellFormedX)
    (hAcyclic : S'.ExtAcyclic) (hWFExtra : S'.WellFormedExtra)
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
  · exact stratMonoFuel hWFX hAcyclic hWFExtra hNEF hDClosed hsub_t hagree_t hLo (S'.shapeDef L)
      (S'.shapeDef_depsIn hDClosed hL) (hWFExtra L) (hNEF L) (hLo L hL) _ n (htcorrectL.1 hLA)
  · obtain ⟨x, hxmem, hSatx⟩ := htcorrectL.2 hLA
    have hxY : x ∈ S'.Y ∪ S'.X := by
      have hxdesc : x ∈ S'.desc L := (Finset.mem_sdiff.mp hxmem).1
      unfold Schema.desc at hxdesc
      simp only [Finset.mem_filter] at hxdesc
      exact Finset.mem_union_right _ hxdesc.1
    exact ⟨x, hxmem, stratMonoFuel hWFX hAcyclic hWFExtra hNEF hDClosed hsub_t hagree_t hLo
      (S'.shapeDef x) (S'.shapeDef_depsIn hDClosed hxY) (hWFExtra x) (hNEF x) (hLo x hxY)
      _ n hSatx⟩

/-! ### Schema-invariance of `Satisfies` across `stratRestrict`

The final piece Proposition 1 needs, beyond everything above: `Satisfies`
is defined at a *schema-relative* canonical fuel (`reqFuel S s + 1`,
`ShexLean/Shex2025Inheritance/Termination.lean`), so `Satisfies (S.stratRestrict
strat i) G τ n s` and `Satisfies (S.stratRestrict strat j) G τ n s` are
literally different propositions (different concrete `SatisfiesFuel` fuel
values, over different schemas whose `X` differs) — unlike 2017's own
`stratTypingSeq_correct`, where `Satisfies` never consults the schema at
all, so the analogous step was `rfl`-free defeq there. Bridging the two
needs a genuinely new "schema-invariance" argument: `SatisfiesEFuel` (Table
1) never touches `S`/`G` at all, and `SatisfiesMFuel`/`SatisfiesFuel`'s only
schema-dependent case (`.extends`) touches `S` purely through
`S.shapeDef`/`S.anc`/`S.ancSet` — so two schemas sharing `shapeDef` and
agreeing on `.anc` for every label a shape's dependencies can reach behave
identically. -/

/-- `SatisfiesEFuel` (Table 1) doesn't depend on the schema or graph
parameters at all — literally provable for *any* two schemas/graphs at a
shared fuel, no side hypotheses needed (the defining equations of Table 1
never mention `S`/`G`, see `ShexLean/Shex2025Inheritance/Semantics.lean`'s module
docstring). -/
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

/-- `SatisfiesMFuel` (Table 3) on a `NoExtends` shape doesn't depend on the
schema or graph either — the `.extends` case (the only schema-dependent
one) is impossible, and `.ofShape` only defers to `SatisfiesEFuel_schema_
indep`. -/
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

/-- `SatisfiesMFuel` (Table 3) for a general shape: agrees between two
schemas `S1`/`S2` sharing the same `shapeDef` and agreeing on `.anc` for
every label in a `D_S`-closed set `Z` the shape's dependencies stay inside
(`depsIn Z`) — the schema analogue of `agreeM` (which instead varies `τ`
over a *fixed* schema). A rank witness (`Schema.RankOk S1 r s`,
`Termination.lean`) is needed to know when to stop recursing into `restr(x)`
via `schemaAgreeM_noExtends` and defer instead to the rank-`r'` induction
hypothesis — no restriction on where `extends` nodes occur, only
`S1`'s own rank bookkeeping (via `hSD`, `restr(x)` is identical between the
two schemas, so threading `S1`'s `RankOk` throughout is enough). -/
theorem schemaAgreeM {S1 S2 : Schema} (hSD : S1.shapeDef = S2.shapeDef)
    {Z : Finset Label} (hZ : S1.DClosedOn Z)
    (hAnc : ∀ x ∈ Z, S1.anc x = S2.anc x) {G : Graph} :
    ∀ r (s : ShapeExpr), Schema.RankOk S1 r s → s.depsIn Z →
      ∀ (fuel : ℕ) (τ : Typing) (M : Finset Triple),
        SatisfiesMFuel fuel S1 G τ M s ↔ SatisfiesMFuel fuel S2 G τ M s := by
  intro r
  induction r with
  | zero =>
      intro s hs _ fuel τ M
      exact schemaAgreeM_noExtends S1 S2 G G s hs fuel τ M
  | succ r' ihr =>
      intro s
      induction s with
      | constraint c => intro _ _ fuel τ M; rcases fuel with _ | f <;> rfl
      | ofShape h =>
          intro _ _ fuel τ M
          rcases fuel with _ | f
          · rfl
          show (SatisfiesEFuel f S1 G τ (Me τ M h.triples) h.triples ∧
                props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
                (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)) ↔
              (SatisfiesEFuel f S2 G τ (Me τ M h.triples) h.triples ∧
                props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
                (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅))
          rw [SatisfiesEFuel_schema_indep S1 S2 G G h.triples f τ (Me τ M h.triples)]
      | «extends» xs h =>
          intro hRank hdeps fuel τ M
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
          have hRankAt : ∀ x ∈ S1.ancSet xs, ∀ u, (S1.shapeDef x).restrOf = some u →
              Schema.RankOk S1 r' u := hRank
          show (∃ M' Mx, DisjointUnionOn M M' (S1.ancSet xs) Mx ∧
                SatisfiesMFuel f S1 G τ M' (.ofShape h) ∧
                (∀ x ∈ S1.ancSet xs, SatisfiesEFuel f S1 G τ (Mx x) (S1.shapeDef x).extTe) ∧
                (∀ x ∈ S1.ancSet xs, ∀ u, (S1.shapeDef x).restrOf = some u →
                  SatisfiesMFuel f S1 G τ ((S1.anc x).biUnion Mx) u)) ↔
              (∃ M' Mx, DisjointUnionOn M M' (S2.ancSet xs) Mx ∧
                SatisfiesMFuel f S2 G τ M' (.ofShape h) ∧
                (∀ x ∈ S2.ancSet xs, SatisfiesEFuel f S2 G τ (Mx x) (S2.shapeDef x).extTe) ∧
                (∀ x ∈ S2.ancSet xs, ∀ u, (S2.shapeDef x).restrOf = some u →
                  SatisfiesMFuel f S2 G τ ((S2.anc x).biUnion Mx) u))
          rw [hancSetEq]
          refine exists_congr fun M' => exists_congr fun Mx => and_congr_right fun _ => ?_
          have he : SatisfiesMFuel f S1 G τ M' (.ofShape h) ↔ SatisfiesMFuel f S2 G τ M' (.ofShape h) :=
            schemaAgreeM_noExtends S1 S2 G G (.ofShape h) trivial f τ M'
          have hext : (∀ x ∈ S2.ancSet xs, SatisfiesEFuel f S1 G τ (Mx x) (S1.shapeDef x).extTe) ↔
              (∀ x ∈ S2.ancSet xs, SatisfiesEFuel f S2 G τ (Mx x) (S2.shapeDef x).extTe) := by
            refine forall_congr' fun x => forall_congr' fun _ => ?_
            rw [hSD]; exact SatisfiesEFuel_schema_indep S1 S2 G G _ f τ (Mx x)
          have hrestr : (∀ x ∈ S2.ancSet xs, ∀ u, (S1.shapeDef x).restrOf = some u →
                SatisfiesMFuel f S1 G τ ((S1.anc x).biUnion Mx) u) ↔
              (∀ x ∈ S2.ancSet xs, ∀ u, (S2.shapeDef x).restrOf = some u →
                SatisfiesMFuel f S2 G τ ((S2.anc x).biUnion Mx) u) := by
            refine forall_congr' fun x => forall_congr' fun hx => forall_congr' fun u => ?_
            have hx1 : x ∈ S1.ancSet xs := by rw [hancSetEq]; exact hx
            have hxZ : x ∈ Z := hancZ hx1
            rw [hSD]
            refine imp_congr_right fun hru => ?_
            rw [← hSD] at hru
            have hurefsZ : u.depsIn Z := by
              have hurefs : (u.depsAux false).refs ⊆ Z :=
                Finset.Subset.trans (restrOf_refs_subset hru) (S1.shapeDef_depsIn hZ hxZ).1
              have huext : u.extendsTargets ⊆ Z :=
                Finset.Subset.trans (restrOf_extendsTargets_subset hru) (S1.shapeDef_depsIn hZ hxZ).2
              exact ⟨hurefs, huext⟩
            rw [hAnc x hxZ]
            exact ihr u (hRankAt x hx1 u hru) hurefsZ f τ _
          rw [he, hext, hrestr]
      | or s1 s2 ih1 ih2 =>
          intro hRank hdeps fuel τ M
          rcases fuel with _ | f
          · rfl
          simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
            ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
          show SatisfiesMFuel f S1 G τ M s1 ∨ SatisfiesMFuel f S1 G τ M s2 ↔
            SatisfiesMFuel f S2 G τ M s1 ∨ SatisfiesMFuel f S2 G τ M s2
          rw [ih1 hRank.1 ⟨hdeps.1.1, hdeps.2.1⟩ f τ M, ih2 hRank.2 ⟨hdeps.1.2, hdeps.2.2⟩ f τ M]
      | and s1 s2 ih1 ih2 =>
          intro hRank hdeps fuel τ M
          rcases fuel with _ | f
          · rfl
          simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs,
            ShapeExpr.extendsTargets, Finset.union_subset_iff] at hdeps
          show SatisfiesMFuel f S1 G τ M s1 ∧ SatisfiesMFuel f S1 G τ M s2 ↔
            SatisfiesMFuel f S2 G τ M s1 ∧ SatisfiesMFuel f S2 G τ M s2
          rw [ih1 hRank.1 ⟨hdeps.1.1, hdeps.2.1⟩ f τ M, ih2 hRank.2 ⟨hdeps.1.2, hdeps.2.2⟩ f τ M]
      | not s ih =>
          intro hRank hdeps fuel τ M
          rcases fuel with _ | f
          · rfl
          have hdeps' : s.depsIn Z := by
            refine ⟨?_, ?_⟩
            · rw [s.depsAux_refs_indep false true]
              simpa [ShapeExpr.depsAux] using hdeps.1
            · simpa [ShapeExpr.extendsTargets] using hdeps.2
          show ¬ SatisfiesMFuel f S1 G τ M s ↔ ¬ SatisfiesMFuel f S2 G τ M s
          rw [ih hRank hdeps' f τ M]

/-- `SatisfiesFuel` (Table 2): the same schema-agreement fact, one level up
— `.ofShape`/`.extends` are immediate from `schemaAgreeM` (with a
`Schema.rankOk_any`-supplied rank witness), everything else is
self-recursion. -/
theorem schemaAgreeFuel {S1 S2 : Schema} (hSD : S1.shapeDef = S2.shapeDef)
    (hWFX1 : S1.WellFormedX) (hAcyclic1 : S1.ExtAcyclic)
    {Z : Finset Label} (hZ : S1.DClosedOn Z)
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
      exact schemaAgreeM hSD hZ hAnc (S1.X.sup S1.extRank + 1) (.ofShape h)
        (Schema.rankOk_any hAcyclic1 hWFX1 _) hdeps f τ (neigh G n)
  | «extends» xs h =>
      intro hdeps fuel τ n
      rcases fuel with _ | f
      · rfl
      show SatisfiesMFuel f S1 G τ (neigh G n) (.extends xs h) ↔
        SatisfiesMFuel f S2 G τ (neigh G n) (.extends xs h)
      exact schemaAgreeM hSD hZ hAnc (S1.X.sup S1.extRank + 1) (.extends xs h)
        (Schema.rankOk_any hAcyclic1 hWFX1 _) hdeps f τ (neigh G n)
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

/-- `WellFormedX` transfers to any `stratRestrict`: its `X` only shrinks,
and the witness `WellFormedX` supplies for `x ∈ S.X` doesn't care which
restriction (if any) `x` happens to also satisfy. -/
theorem Schema.stratRestrict_WellFormedX {S : Schema} (hWFX : S.WellFormedX)
    (strat : Label → ℕ) (i : ℕ) : (S.stratRestrict strat i).WellFormedX := by
  intro x hx
  simp only [Schema.stratRestrict, Finset.mem_filter] at hx
  exact hWFX x hx.1

/-- `ExtAcyclic` transfers to any `stratRestrict` the same way
`WellFormedX` does: its `X` only shrinks, `extEdge` is purely `shapeDef`-
based (`stratRestrict` never touches `shapeDef`), so a cycle in the
restriction would already be a cycle in `S`. -/
theorem Schema.stratRestrict_ExtAcyclic {S : Schema} (hAcyclic : S.ExtAcyclic)
    (strat : Label → ℕ) (i : ℕ) : (S.stratRestrict strat i).ExtAcyclic := by
  intro x hx
  simp only [Schema.stratRestrict, Finset.mem_filter] at hx
  exact hAcyclic x hx.1

/-- Every stratum `S.stratum strat i` is `D_S`-closed: `D_S` edges never
increase `strat` (Definition 7's first bullet), and `Schema.DClosed` keeps
membership in `Y ∪ X` along the way. -/
theorem Schema.stratum_DClosedOn {S : Schema} (hDClosed : S.DClosed) (strat : Stratification S)
    (i : ℕ) : S.DClosedOn (S.stratum strat.strat i) := by
  intro z hz z' hedge
  simp only [Schema.stratum, Finset.mem_filter] at hz ⊢
  have hzY : z ∈ S.Y ∪ S.X := hz.1
  have hz'Y : z' ∈ S.Y ∪ S.X := hDClosed z hzY z' hedge
  exact ⟨hz'Y, le_trans (strat.dep_le z hzY z' hedge) hz.2⟩

/-- `(S.stratRestrict strat i).anc x = S.anc x` whenever `x` is confined to
stratum `≤ i`: every element of the *unrestricted* `S.anc x` already has
`strat ≤ strat x ≤ i` (Definition 7's first bullet, via `extEdge ⊆
depExtends ⊆ DEdge`), so filtering `S.X` down to `strat ≤ i` before
computing `anc` drops nothing. This is the fact that lets `Satisfies`
computed against two different `stratRestrict` levels agree for any label
confined to the lower one — the whole `ancSet`/`extends`-hop machinery
`SatisfiesMFuel`'s `.extends` case consults is literally unaffected by
which (sufficiently high) stratum level the ambient schema was restricted
to. -/
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

/-- **The key schema-invariance fact.** For a label `x` confined to stratum
`≤ i`, `Satisfies` against `S.stratRestrict strat i` agrees with `Satisfies`
against any higher restriction `S.stratRestrict strat j` (`i ≤ j`) — even
though these are, syntactically, different schemas (different `X`, hence
different `reqFuel`/`ancSet` bookkeeping), evaluating `def(x)` never
actually reaches outside stratum `≤ i` (`Schema.shapeDef_depsIn` +
`Schema.stratum_DClosedOn`), and on that confined region the two schemas'
`.anc` (hence everything `SatisfiesFuel`/`SatisfiesMFuel` consult) coincide
(`Schema.stratRestrict_anc_eq`). Combines `stableFuel` (same schema,
bridging each side's own canonical fuel up to a shared sufficient value)
with `schemaAgreeFuel` (same fuel, bridging the two schemas) — this is
exactly the gap that blocked a direct 2017-style port of `stratTypingSeq_
correct`'s inductive step (`hcorrect_i := hcorrect_i` fails here because,
unlike 2017, `Satisfies` genuinely depends on the schema). -/
theorem Satisfies_stratRestrict_agree {S : Schema} (hWFX : S.WellFormedX)
    (hAcyclic : S.ExtAcyclic) (hDClosed : S.DClosed) (strat : Stratification S)
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
  have hAcyclic1 : (S.stratRestrict strat.strat i).ExtAcyclic :=
    Schema.stratRestrict_ExtAcyclic hAcyclic strat.strat i
  have hAcyclic2 : (S.stratRestrict strat.strat j).ExtAcyclic :=
    Schema.stratRestrict_ExtAcyclic hAcyclic strat.strat j
  set F := max (Schema.reqFuelGen (S.stratRestrict strat.strat i) (S.shapeDef x) + 1)
    (Schema.reqFuelGen (S.stratRestrict strat.strat j) (S.shapeDef x) + 1) with hFdef
  have hstep1 : Satisfies (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) ↔
      SatisfiesFuel F (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) :=
    stableFuel hWFX1 hAcyclic1 (S.shapeDef x)
      (Schema.reqFuelGen (S.stratRestrict strat.strat i) (S.shapeDef x) + 1) F
      (le_refl _) (le_max_left _ _) G τ n
  have hstep2 : Satisfies (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) ↔
      SatisfiesFuel F (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) :=
    stableFuel hWFX2 hAcyclic2 (S.shapeDef x)
      (Schema.reqFuelGen (S.stratRestrict strat.strat j) (S.shapeDef x) + 1) F
      (le_refl _) (le_max_right _ _) G τ n
  have hcross : SatisfiesFuel F (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) ↔
      SatisfiesFuel F (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) :=
    schemaAgreeFuel (S1 := S.stratRestrict strat.strat i) (S2 := S.stratRestrict strat.strat j)
      rfl hWFX1 hAcyclic1 hZDCl hAnc (S.shapeDef x) hdeps F τ n
  rw [hstep1, hstep2, hcross]

/-- `Schema.desc`'s membership characterization, avoiding the recurring
`Classical.decPred`/`Finset.filter` instance-mismatch trap (see this file's
module docstring/memory notes) by fixing the filter's instance once here
rather than at every call site. -/
theorem Schema.mem_desc {S : Schema} {x y : Label} :
    y ∈ S.desc x ↔ y ∈ S.X ∧ Relation.ReflTransGen S.extEdge y x := by
  unfold Schema.desc
  simp only [Finset.mem_filter]

/-- `(S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X` (a union of
two separately-filtered sets) and `S.stratum strat i` (one filter over the
union) are the same `Finset`, just built differently — needed to bridge
`Schema.univTyping`'s `Y ∪ X` form with `Schema.stratum_mono`'s. -/
theorem Schema.stratRestrict_YX_eq_stratum (S : Schema) (strat : Label → ℕ) (i : ℕ) :
    (S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X = S.stratum strat i := by
  unfold Schema.stratRestrict Schema.stratum
  rw [Finset.filter_union]

/-- `stratRestrict` doesn't change `D_S`'s edge relation at all (it only
ever touches `Y`/`X`/`A`, never `shapeDef`, and `DEdge` is purely
`shapeDef`-based) — recorded as its own `rfl` lemma so later proofs can
`rw` this fact directly instead of relying on the elaborator to rediscover
it by unification buried inside a large application (which is expensive
enough, given how much `Schema`/`Finset` machinery `DEdge` unfolds through,
to time out `maxTypingAgreeing_correct`'s own `hDClosed` argument if left
implicit). -/
theorem Schema.stratRestrict_DEdge_eq (S : Schema) (strat : Label → ℕ) (i : ℕ) :
    (S.stratRestrict strat i).DEdge = S.DEdge := rfl

/-- `S.stratRestrict strat i` is itself `DClosed`, given `S` is — the
`stratRestrict`-relative form of `Schema.stratum_DClosedOn`, bridged via
`Schema.stratRestrict_YX_eq_stratum`/`Schema.stratRestrict_DEdge_eq`
(explicitly, rather than via `hDClosed` directly, for the same performance
reason noted on `Schema.stratRestrict_DEdge_eq`). -/
theorem Schema.stratRestrict_DClosed {S : Schema} (hDClosed : S.DClosed) (strat : Stratification S)
    (i : ℕ) : (S.stratRestrict strat.strat i).DClosed := by
  intro z hz z' hedge
  rw [Schema.stratRestrict_YX_eq_stratum] at hz ⊢
  rw [Schema.stratRestrict_DEdge_eq] at hedge
  exact Schema.stratum_DClosedOn hDClosed strat i z hz z' hedge

/-- A correct typing of `S.stratRestrict strat i` is also a correct typing
of `S.stratRestrict strat j`, for `i ≤ j` — the "climb one stratum level
without losing correctness" step `stratTypingSeq_correct`'s inductive step
needs. Every ingredient (`.A` membership, `.desc \ .A` witnesses) is
monotone in the restriction level, since `stratRestrict` only ever *grows*
`Y`/`X`/`A` as `i` grows; the one substantive step is transporting the
`Satisfies` witnesses themselves via `Satisfies_stratRestrict_agree`. -/
theorem Schema.correctTyping_stratRestrict_mono {S : Schema} (hWFX : S.WellFormedX)
    (hAcyclic : S.ExtAcyclic) (hDClosed : S.DClosed) (strat : Stratification S)
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
  · exact (Satisfies_stratRestrict_agree hWFX hAcyclic hDClosed strat hij hLY hLi).mp
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
      (Satisfies_stratRestrict_agree hWFX hAcyclic hDClosed strat hij hxY hxi).mp hSatx⟩

/-- The `τ_i` sequence of Definition 8, unified into a single
`ℕ`-recursion: `τ_0 := ∅` (vacuously correct for `S^σ_0`, since every label
has `σ(z) ≥ 1`, so stratum 0 is empty) and `τ_{i+1}` is the union of all
correct typings of `G` by `S^σ_{i+1}` agreeing with `τ_i` on `Y^σ_i ∪
X^σ_i`. Matches the paper's own recursion once `τ_1` (Definition 8's base
case, defined there directly as "the union of all correct typings of `G`
by `S^σ_1`") is seen as the special case `Lo = ∅` of the general step. -/
noncomputable def stratTypingSeq (S : Schema) (strat : Label → ℕ) (G : Graph) : ℕ → Typing
  | 0 => ∅
  | i + 1 => maxTypingAgreeing (S.stratRestrict strat (i + 1)) G (S.stratum strat i)
      (stratTypingSeq S strat G i)

/-- Definition 8: the maximal typing of `G` by `S` with `σ`,
`τ_max(S,σ,G)`. -/
noncomputable def Typing8 (G : Graph) (S : Schema) (strat : Stratification S) : Typing :=
  stratTypingSeq S strat.strat G strat.k

/-- The two invariants `stratTypingSeq` maintains at every stratum `i`: it
is a subset of `S^σ_i`'s universe of typings, and it is a correct typing of
`G` by `S^σ_i`. The base case (`i = 0`) is vacuous (`stratum strat 0 = ∅`,
`Y^σ_0 ∪ X^σ_0 = ∅` since every label has `σ ≥ 1`, `mem_range`). The
inductive step combines `maxTypingAgreeing_correct` (to get correctness at
stratum `i+1` fresh) with `Schema.correctTyping_stratRestrict_mono` (to
lift the stratum-`i` correctness of the *previous* typing up to stratum
`i+1`'s schema, closing exactly the gap that a direct 2017-style port left
open — see `Satisfies_stratRestrict_agree`'s docstring). -/
theorem stratTypingSeq_correct {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic)
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
        Schema.correctTyping_stratRestrict_mono hWFX hAcyclic hDClosed strat (Nat.le_succ i)
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
      have hAcyclic1 : (S.stratRestrict strat.strat (i + 1)).ExtAcyclic :=
        Schema.stratRestrict_ExtAcyclic hAcyclic strat.strat (i + 1)
      refine ⟨maxTypingAgreeing_subset _ G _ _, ?_⟩
      show (S.stratRestrict strat.strat (i + 1)).CorrectTyping G
        (maxTypingAgreeing (S.stratRestrict strat.strat (i + 1)) G (S.stratum strat.strat i)
          (stratTypingSeq S strat.strat G i))
      exact maxTypingAgreeing_correct hWFX1 hAcyclic1 hWFExtra hNEF hDClosed1 hsub_i' hcorrect_i' hLo

/-- **Proposition 1.** For every schema `S`, stratification `σ` of `S`, and
graph `G`, the typing `τ_max(S,σ,G)` is a correct typing. -/
theorem proposition1 {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic)
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
  have := (stratTypingSeq_correct hWFX hAcyclic hWFExtra hNEF hDClosed strat G strat.k).2
  rw [hk] at this
  exact this

end ShexLean.Inheritance
