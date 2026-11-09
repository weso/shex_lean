import ShexLean.Shex2025Inheritance.CorrectTyping
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

The structure of this file follows
`ShexLean/Shex2017Schemas/Proposition1.lean` of the 2017 formalism
(Definitions 3 and 4 there), changed for the new `Schema` and `Satisfies`.
The parts for schema restriction, `maxTypingAgreeing` and `stratTypingSeq`
transfer mechanically. They restrict `Y`, `X` and `A` with a stratum
filter, not `.labels`. The abstract-label case of `Schema.CorrectTyping`
does not change.

**The part that does not transfer.** In 2017, `Satisfies.agree` and
`Satisfies.stratMono` are proved by structural recursion on the syntax
tree, because `⊢` and `⊨` never dereference `def`. Here, `.extends`
dereferences the definitions of other labels (the `ext-te(x)` and
`restr(x)` of the ancestors). Thus, an agreement or monotonicity fact about
`Satisfies` must use the dependency structure of the schema
(`Schema.dep` and `depExtends`, through reachability in `D_S`), not only
the syntax tree of one shape expression.

Also, it must use the `Fuel`-indexed definitions on which `Satisfies` is
built (`ShexLean/Shex2025Inheritance/Termination.lean`). Each fact is proved
in the same three steps as `stableM` and `stableFuel` there:

1. One structural induction for one layer of Table 3 (`SatisfiesMAt`).
2. An induction on the fuel (`SatisfiesMFuel`).
3. The structural lift to Table 2 (`SatisfiesAt`).
-/

namespace ShexLean.Inheritance

open ShexLean.InheritanceCore

/-! ### Definition 7: stratification -/

/-- `Z` is closed under `D_S`: each label that a member of `Z` depends on
(`dep` or `depExtends`) is also in `Z`. `Schema.DClosed` is the case
`Z = Y ∪ X`. Proposition 1 below also needs it for `Z = ` a stratum. -/
def Schema.DClosedOn (S : Schema) (Z : Finset Label) : Prop :=
  ∀ z ∈ Z, ∀ z', S.DEdge z z' → z' ∈ Z

/-- Membership in a `D_S`-closed `Z` continues along each `D_S` path. -/
theorem Schema.reach_mem {S : Schema} {Z : Finset Label} (hZ : S.DClosedOn Z)
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
def Schema.DClosed (S : Schema) : Prop := S.DClosedOn (S.Y ∪ S.X)

/-- Definition 7 (stratification). It uses the edges of `D_S` (`DEdge` and
`DNegEdge`), not the paths of the paper. The two forms are equivalent by
induction on the path length. (`Stratification.lt_of_negPath` below gets
the path form.) `maxTypingAgreeing_correct` (later in the file) needs the
edge form. This definition has the same role as `Stratification` of 2017
(`ShexLean/Shex2017Schemas/Stratification.lean`). -/
structure Stratification (S : Schema) where
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
def Schema.StratifiedNegation (S : Schema) : Prop := Nonempty (Stratification S)

/-- "`dep` subsumes `dep-shape-neg`/`dep-extra-neg`", applied to `DEdge`.
Each negative edge is also an ordinary `D_S` edge. -/
theorem Schema.DEdge_of_DNegEdge {S : Schema} {z z' : Label} (h : S.DNegEdge z z') :
    S.DEdge z z' := by
  rcases h with h | h
  · exact Or.inl (Schema.dep_of_depShapeNeg h)
  · exact Or.inl (Schema.dep_of_depExtraNeg h)

/-- `strat` never increases along a `D_S` path (the first bullet of
Definition 7, in path form). -/
theorem Stratification.le_of_path {S : Schema} (hDClosed : S.DClosed) (strat : Stratification S)
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
theorem Stratification.lt_of_negPath {S : Schema} (hDClosed : S.DClosed)
    (strat : Stratification S) {z a b z' : Label} (hzY : z ∈ S.Y ∪ S.X)
    (hza : Relation.ReflTransGen S.DEdge z a) (hab : S.DNegEdge a b)
    (hbz' : Relation.ReflTransGen S.DEdge b z') :
    strat.strat z' < strat.strat z := by
  have haY : a ∈ S.Y ∪ S.X := S.reach_mem hDClosed hzY hza
  have hbY : b ∈ S.Y ∪ S.X := hDClosed a haY b (S.DEdge_of_DNegEdge hab)
  calc strat.strat z' ≤ strat.strat b := strat.le_of_path hDClosed hbY hbz'
    _ < strat.strat a := strat.negDep_lt a haY b hab
    _ ≤ strat.strat z := strat.le_of_path hDClosed hzY hza

/-! ### An agreement lemma for `Satisfies`

`⊢` and `⊨` depend on `τ` only through its restriction to a set of labels
`Z` with two properties:

* `Z` is closed under `D_S` (`Schema.DClosedOn`).
* `Z` contains all that the shape expression can reach syntactically
  (`ShapeExpr.depsIn`).

This is the 2025 version of `Satisfies.agree` of 2017
(`ShexLean/Shex2017Schemas/Proposition1.lean`). Now it must use the
dependency structure of the schema, because `.extends` dereferences the
definitions of other labels.

One lemma covers three changes at the same time: the typing (`τ1` and
`τ2` agree on `Z`), the schema (`S1` and `S2` have the same definitions,
and agree on `anc` in `Z`), and the evaluator of `restr(x)`. Thus,
`SatisfiesMAt_transfer` gives both `Satisfies.agree` (a change of typing)
and `Satisfies_stratRestrict_agree` below (a change of schema). -/

/-- The labels that a shape expression can reach:

* The `@z'` references at any location in it (`ShapeExpr.depsAux`).
* The `extends` targets at any location in it
  (`ShapeExpr.extendsTargets`, a full recursive walk. Refer to the
  docstring of that definition to know why.) -/
def ShapeExpr.depsIn (s : ShapeExpr) (Z : Finset Label) : Prop :=
  (s.depsAux false).refs ⊆ Z ∧ s.extendsTargets ⊆ Z

/-- A well-formedness condition that `stratMono` needs, in addition to
`ExtAcyclic` and `WellFormedExtra`: a `not` never contains an `extends`.

Without it, the `not` case of `stratMono` needs exact agreement between
`τ` and `τ'` on each ancestor that an `extends` inside the negated content
can reach. But these ancestors are not necessarily in `Lo`, because
`dep-extends` is intentionally never a negative dependency
(Definition 5). Thus, the hypotheses of `stratMono` do not bound them.

The "Design choices" discussion of the paper has a similar restriction. It
allows `extends` only on conjunctions, to prevent the same problem with
`or`. No example of the paper uses the `not` case. With this condition, the
content of a `not` is always `NoExtends`. Thus, the `not` case of
`stratMono` uses `SatisfiesMAt_agree_noExtends` directly. -/
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

/-- `.refs` never depends on `neg` (only `.negRefs` does). Thus, a fact
`refs ⊆ Z` stays true across the change of `neg` that `.not` does. -/
theorem ShapeExpr.depsAux_refs_indep (s : ShapeExpr) (neg1 neg2 : Bool) :
    (s.depsAux neg1).refs = (s.depsAux neg2).refs := by
  induction s generalizing neg1 neg2 with
  | constraint c => simp [ShapeExpr.depsAux]
  | ofShape h => simp [ShapeExpr.depsAux, Shape.depInfo]
  | «extends» xs h => simp [ShapeExpr.depsAux, Shape.depInfo]
  | or s1 s2 ih1 ih2 | and s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_refs]; rw [ih1 neg1 neg2, ih2 neg1 neg2]
  | not s _ => simp only [ShapeExpr.depsAux]

/-! `depsIn` goes down through `or`, `and` and `not`. -/

theorem ShapeExpr.depsIn_or {a b : ShapeExpr} {Z : Finset Label} :
    (ShapeExpr.or a b).depsIn Z ↔ a.depsIn Z ∧ b.depsIn Z := by
  simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs, ShapeExpr.extendsTargets,
    Finset.union_subset_iff]
  tauto

theorem ShapeExpr.depsIn_and {a b : ShapeExpr} {Z : Finset Label} :
    (ShapeExpr.and a b).depsIn Z ↔ a.depsIn Z ∧ b.depsIn Z := by
  simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, DepInfo.union_refs, ShapeExpr.extendsTargets,
    Finset.union_subset_iff]
  tauto

theorem ShapeExpr.depsIn_not {a : ShapeExpr} {Z : Finset Label} :
    (ShapeExpr.not a).depsIn Z ↔ a.depsIn Z := by
  simp only [ShapeExpr.depsIn, ShapeExpr.depsAux, ShapeExpr.extendsTargets,
    a.depsAux_refs_indep true false]

/-- If `x ∈ Z` and `Z` is `D_S`-closed, then the definition of `x` reaches
only labels in `Z`. The closure of `Z` is what is necessary to do the
recursion one more `extends` step deep and stay in `Z`. -/
theorem Schema.shapeDef_depsIn {S : Schema} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {x : Label} (hx : x ∈ Z) : (S.shapeDef x).depsIn Z :=
  ⟨fun _ hz' => hZ x hx _ (Or.inl hz'), fun _ hz' => hZ x hx _ (Or.inr (Or.inl hz'))⟩

/-- `S.ancSet xs ⊆ Z` if `xs ⊆ Z` and `Z` is `D_S`-closed. Each ancestor
that a rule-18 partition reaches also stays in `Z`. -/
theorem Schema.ancSet_subset {S : Schema} {Z : Finset Label} (hZ : S.DClosedOn Z)
    {xs : Finset Label} (hxs : xs ⊆ Z) : S.ancSet xs ⊆ Z := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Schema.mem_ancSet.mp hx
  rw [Schema.mem_anc] at hyx
  have hstep : Relation.ReflTransGen S.DEdge y x :=
    Relation.ReflTransGen.mono (fun _ _ hab => Or.inr (Or.inl hab)) y x hyx.2
  exact S.reach_mem hZ (hxs hy) hstep

/-- The references of `ext-te(x)` are in the references of `def(x)` (it is
a part of `def(x)`). For a definition that does not have the form
`extends X h [and u]`, `ext-te(x)` is `.empty`, which has no references. -/
theorem extTe_refs_subset (s : ShapeExpr) : s.extTe.refs ⊆ (s.depsAux false).refs := by
  rcases s with _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _, _⟩ | _ <;>
    simp [ShapeExpr.extTe, ShapeExpr.depsAux, Shape.refs_eq, TripleExpr.refs, TripleExpr.tcs,
      DepInfo.union_refs]

/-- The references of `restr(x)` are in the references of `def(x)`. -/
theorem restrOf_refs_subset {S : Schema} {x : Label} {u : ShapeExpr}
    (hu : (S.shapeDef x).restrOf = some u) :
    (u.depsAux false).refs ⊆ ((S.shapeDef x).depsAux false).refs := by
  obtain ⟨xs, h, heq⟩ := ShapeExpr.restrOf_eq_some.mp hu
  rw [heq]
  simp only [ShapeExpr.depsAux, DepInfo.union_refs]
  exact Finset.subset_union_right

/-- The negative references of `restr(x)` are in the negative references
of `def(x)`. -/
theorem restrOf_negRefs_subset {S : Schema} {x : Label} {u : ShapeExpr}
    (hu : (S.shapeDef x).restrOf = some u) :
    (u.depsAux false).negRefs ⊆ ((S.shapeDef x).depsAux false).negRefs := by
  obtain ⟨xs, h, heq⟩ := ShapeExpr.restrOf_eq_some.mp hu
  rw [heq]
  simp only [ShapeExpr.depsAux, DepInfo.union_negRefs]
  exact Finset.subset_union_right

/-- The extends targets of `restr(x)` are in the extends targets of
`def(x)`. -/
theorem restrOf_extendsTargets_subset {S : Schema} {x : Label} {u : ShapeExpr}
    (hu : (S.shapeDef x).restrOf = some u) :
    u.extendsTargets ⊆ (S.shapeDef x).extendsTargets := by
  obtain ⟨xs, h, heq⟩ := ShapeExpr.restrOf_eq_some.mp hu
  rw [heq]
  exact Finset.subset_union_right

/-- If `x ∈ Z` and `Z` is `D_S`-closed, then `restr(x)` reaches only labels
in `Z`. -/
theorem restrOf_depsIn {S : Schema} {Z : Finset Label} (hZ : S.DClosedOn Z) {x : Label}
    (hx : x ∈ Z) {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u) : u.depsIn Z :=
  ⟨(restrOf_refs_subset hu).trans (S.shapeDef_depsIn hZ hx).1,
    (restrOf_extendsTargets_subset hu).trans (S.shapeDef_depsIn hZ hx).2⟩

/-- On a `NoExtends` shape, Table 3 depends on `τ` only through its
restriction to the references of the shape. It does not depend on the
schema or on `restr` at all, because rule 18 is not used. No closure
hypothesis on `Z` is necessary.

The `not` case of `stratMono` needs this lemma. (By
`ShapeExpr.NotIsExtendsFree`, the content of a `not` node is always
`NoExtends`.) -/
theorem SatisfiesMAt_agree_noExtends {S1 S2 : Schema} {τ1 τ2 : Typing}
    {restr1 restr2 : Finset Triple → ShapeExpr → Prop} {Z : Finset Label}
    (hagree : AgreeOn τ1 τ2 Z) :
    ∀ s, s.NoExtends → (s.depsAux false).refs ⊆ Z →
      ∀ M, SatisfiesMAt S1 τ1 restr1 M s ↔ SatisfiesMAt S2 τ2 restr2 M s := by
  intro s
  induction s with
  | constraint _ => intros; rfl
  | ofShape h =>
      intro _ href M
      exact SatisfiesShape_agree hagree (by rwa [ShapeExpr.depsAux, Shape.refs_eq] at href) M
  | «extends» _ _ => intro hs; exact hs.elim
  | or s1 s2 ih1 ih2 =>
      intro hs href M
      simp only [ShapeExpr.depsAux, DepInfo.union_refs, Finset.union_subset_iff] at href
      exact or_congr (ih1 hs.1 href.1 M) (ih2 hs.2 href.2 M)
  | and s1 s2 ih1 ih2 =>
      intro hs href M
      simp only [ShapeExpr.depsAux, DepInfo.union_refs, Finset.union_subset_iff] at href
      exact and_congr (ih1 hs.1 href.1 M) (ih2 hs.2 href.2 M)
  | not s ih =>
      intro hs href M
      simp only [ShapeExpr.depsAux] at href
      rw [s.depsAux_refs_indep true false] at href
      exact not_congr (ih hs href M)

/-- The general transfer lemma for one layer of Table 3. The result does
not change if these conditions are true:

* `τ1` and `τ2` agree on a `D_S`-closed `Z`.
* `S1` and `S2` have the same definitions, and agree on `anc` in `Z`.
* `restr1` and `restr2` agree on each restriction `u` that the rank
  witness `P` covers, if `u` reaches only labels in `Z`.
* The shape reaches only labels in `Z` (`depsIn`).

The only case that uses the schema is `.extends`. Each other case is a
plain structural step. -/
theorem SatisfiesMAt_transfer {S1 S2 : Schema} {τ1 τ2 : Typing}
    {restr1 restr2 : Finset Triple → ShapeExpr → Prop} {P : ShapeExpr → Prop}
    {Z : Finset Label} (hZ : S1.DClosedOn Z) (hagree : AgreeOn τ1 τ2 Z)
    (hdef : S1.shapeDef = S2.shapeDef) (hanc : ∀ x ∈ Z, S1.anc x = S2.anc x)
    (hr : ∀ u, P u → u.depsIn Z → ∀ M, restr1 M u ↔ restr2 M u) :
    ∀ s, S1.RankOkAt P s → s.depsIn Z →
      ∀ M, SatisfiesMAt S1 τ1 restr1 M s ↔ SatisfiesMAt S2 τ2 restr2 M s := by
  intro s
  induction s with
  | constraint _ => intros; rfl
  | ofShape h =>
      intro _ hdeps M
      exact SatisfiesShape_agree hagree (by rw [← Shape.refs_eq h false]; exact hdeps.1) M
  | «extends» xs h =>
      intro hRank hdeps M
      have hxsZ : xs ⊆ Z := hdeps.2
      have hancZ : S1.ancSet xs ⊆ Z := S1.ancSet_subset hZ hxsZ
      have hancSet : S1.ancSet xs = S2.ancSet xs :=
        Finset.biUnion_congr rfl fun x hx => hanc x (hxsZ hx)
      simp only [SatisfiesMAt]
      rw [← hancSet, ← hdef]
      refine exists₂_congr fun M' Mx => and_congr_right fun _ => ?_
      refine and_congr (SatisfiesShape_agree hagree ?_ M') (and_congr ?_ ?_)
      · rw [← Shape.refs_eq h false]; exact hdeps.1
      · refine forall₂_congr fun x hx => SatisfiesE_agree hagree _ ?_ _
        exact (extTe_refs_subset _).trans (S1.shapeDef_depsIn hZ (hancZ hx)).1
      · refine forall₂_congr fun x hx => forall₂_congr fun u hu => ?_
        rw [hanc x (hancZ hx)]
        exact hr u (hRank x hx u hu) (restrOf_depsIn hZ (hancZ hx) hu) _
  | or s1 s2 ih1 ih2 =>
      intro hRank hdeps M
      rw [ShapeExpr.depsIn_or] at hdeps
      exact or_congr (ih1 hRank.1 hdeps.1 M) (ih2 hRank.2 hdeps.2 M)
  | and s1 s2 ih1 ih2 =>
      intro hRank hdeps M
      rw [ShapeExpr.depsIn_and] at hdeps
      exact and_congr (ih1 hRank.1 hdeps.1 M) (ih2 hRank.2 hdeps.2 M)
  | not s ih =>
      intro hRank hdeps M
      exact not_congr (ih hRank (ShapeExpr.depsIn_not.mp hdeps) M)

/-- `SatisfiesMFuel` (Table 3) at the same fuel, across a change of typing
and schema. The proof is an induction on the fuel. Each step is
`SatisfiesMAt_transfer`. -/
theorem SatisfiesMFuel_transfer {S1 S2 : Schema} {τ1 τ2 : Typing} {Z : Finset Label}
    (hZ : S1.DClosedOn Z) (hagree : AgreeOn τ1 τ2 Z)
    (hdef : S1.shapeDef = S2.shapeDef) (hanc : ∀ x ∈ Z, S1.anc x = S2.anc x) :
    ∀ r s, S1.RankOk r s → s.depsIn Z →
      ∀ M, SatisfiesMFuel r S1 τ1 M s ↔ SatisfiesMFuel r S2 τ2 M s := by
  intro r
  induction r with
  | zero => exact SatisfiesMAt_transfer hZ hagree hdef hanc (fun _ h => h.elim)
  | succ r ih => exact SatisfiesMAt_transfer hZ hagree hdef hanc ih

/-- `SatisfiesFuel` (Table 2) at the same fuel, across a change of typing
and schema. The fuel must be sufficient for `S1` (`Schema.fuelBound`). -/
theorem SatisfiesFuel_transfer {S1 S2 : Schema} (hAcyclic : S1.ExtAcyclic) {r : ℕ}
    (hr : S1.fuelBound ≤ r) {G : Graph} {τ1 τ2 : Typing} {Z : Finset Label}
    (hZ : S1.DClosedOn Z) (hagree : AgreeOn τ1 τ2 Z)
    (hdef : S1.shapeDef = S2.shapeDef) (hanc : ∀ x ∈ Z, S1.anc x = S2.anc x)
    {s : ShapeExpr} (hdeps : s.depsIn Z) (n : RDFNode) :
    SatisfiesFuel r S1 G τ1 n s ↔ SatisfiesFuel r S2 G τ2 n s :=
  SatisfiesAt_congr (·.depsIn Z) ShapeExpr.depsIn_or.mp ShapeExpr.depsIn_and.mp
    ShapeExpr.depsIn_not.mp
    (fun t ht M => SatisfiesMFuel_transfer hZ hagree hdef hanc r t
      (Schema.rankOk_fuelBound hAcyclic hr t) ht M) s hdeps

/-- `Satisfies` depends on `τ` only through its restriction to `Z`, if
`s.depsIn Z` and `Z` is `D_S`-closed. -/
theorem Satisfies.agree {S : Schema} (hAcyclic : S.ExtAcyclic)
    {G : Graph} {τ τ' : Typing} {Z : Finset Label} (hZ : S.DClosedOn Z)
    (hagree : AgreeOn τ τ' Z) {s : ShapeExpr} (hdeps : s.depsIn Z)
    (n : RDFNode) : Satisfies S G τ n s ↔ Satisfies S G τ' n s :=
  SatisfiesFuel_transfer hAcyclic le_rfl hZ hagree rfl (fun _ _ => rfl) hdeps n

/-! ### A problem that `stratMono` has here, and that it did not have in 2017

Rule 17 of Table 3 filters the neighbourhood through `Me` and `Mnotin`:
the part of `M` that is "already correctly typed", and the "leftover"
part. These parts are computed from `τ`. This makes `SatisfiesMFuel` and
`Satisfies` not monotone in `τ`, also with no negation at any location.

When `τ` becomes larger, a triple can go from `Mnotin` into `Me`. If `Me`
already matched a plain (not starred) triple constraint such as `p @z`
(which needs `M` to be exactly a singleton), then the match fails when
`Me` has more than one element.

For example, take the shape
`⟨closed := false, extra := some {p}, triples := p @z⟩`:

* With `τ₁ = {(t1.obj, z)}`, `M = {t1, t2}` satisfies it. Here,
  `Me = {t1}`, which is a singleton.
* With `τ₂ = τ₁ ∪ {(t2.obj, z)} ⊇ τ₁`, `M` does not satisfy it. Here, `Me`
  becomes `{t1, t2}`, which is not a singleton.

The appendix proof of Proposition 1 in the paper gives the fix. It uses an
auxiliary invariant that it calls "(*)": for each sub-expression
`[closed][extra P]⟨e⟩`, and for each `p @u ∈ tcs(e)`, `p ∉ P`. Thus, the
properties of the triple constraints of a shape never overlap its `extra`
set.

The main text of the paper never gives this invariant as a separate
definition. Only the proof of Proposition 1 uses it. `Schema.ExtAcyclic`
(`Termination.lean`) makes explicit one of the implicit well-definedness
conditions of the paper. In the same way, this file adds this invariant
as an explicit hypothesis, `Schema.WellFormedExtra`.

Why it fixes the problem. With `(*)`, when a shape succeeds, the success
condition of `Mnotin` (`props(Mnotin) ⊆ P`) forces each triple in `M` that
matches `props(e)` to be already in `Me`. (No such triple can be a
leftover through `extra`, because `(*)` says that `extra` never covers the
properties of `e`.) Thus, `Me` already has its maximal possible value,
`M.filter (pred ∈ props e)`, which does not use `τ`. When `Me` is at this
maximum, it cannot become larger when `τ` becomes larger. This gives
monotonicity again for the positive uses of `Me` in Table 3 (the uses that
do not misuse `extra`). -/

/-- "(*)" for each shape at any location in a `ShapeExpr`. (This means
each `.ofShape`, and the `h` of each `.extends`, also when they are nested
in `or`, `and`, `not` or a restriction.) -/
def ShapeExpr.WellFormedExtra : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape h => h.WellFormedExtra
  | .extends _ h => h.WellFormedExtra
  | .or s1 s2 => s1.WellFormedExtra ∧ s2.WellFormedExtra
  | .and s1 s2 => s1.WellFormedExtra ∧ s2.WellFormedExtra
  | .not s => s.WellFormedExtra

/-- "(*)" for the full schema: the full definition of each label. -/
def Schema.WellFormedExtra (S : Schema) : Prop := ∀ ℓ, (S.shapeDef ℓ).WellFormedExtra

/-- The invariant "(*)" of `restr(x)` comes from the invariant of
`def(x)`. -/
theorem restrOf_wellFormedExtra {S : Schema} (hWFExtra : S.WellFormedExtra) {x : Label}
    {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u) : u.WellFormedExtra := by
  obtain ⟨xs, h, heq⟩ := ShapeExpr.restrOf_eq_some.mp hu
  have hWFx := hWFExtra x
  rw [heq] at hWFx
  exact hWFx.2

/-- The invariant "no `extends` below `not`" of `restr(x)` comes from the
invariant of `def(x)`. -/
theorem restrOf_notIsExtendsFree {S : Schema} (hNEF : S.NotIsExtendsFree) {x : Label}
    {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u) : u.NotIsExtendsFree := by
  obtain ⟨xs, h, heq⟩ := ShapeExpr.restrOf_eq_some.mp hu
  have hNx := hNEF x
  rw [heq] at hNx
  exact hNx.2

/-! ### `stratMono`: a larger `τ` for positive positions, exact agreement
below `not` -/

/-- The negative references of the content of a `not` bound all its
references. This is the reason why `depsAux` must latch and not toggle
(refer to the docstring of that definition). -/
theorem ShapeExpr.refs_subset_of_not_negRefs {s : ShapeExpr} {Lo : Finset Label}
    (hneg : ((ShapeExpr.not s).depsAux false).negRefs ⊆ Lo) : (s.depsAux false).refs ⊆ Lo := by
  simp only [ShapeExpr.depsAux] at hneg
  rwa [s.negRefs_true_eq_refs, s.depsAux_refs_indep true false] at hneg

/-- `stratMono` for one layer of Table 3. A larger `τ` (`hsub`) keeps
satisfaction, if these conditions are true:

* `τ` and `τ'` agree exactly on `Lo`.
* The shape reaches only labels of a `D_S`-closed `Z`, and the negative
  references of each definition in `Z` are in `Lo`.
* `WellFormedExtra` and `NotIsExtendsFree` are true for the shape.
* `restr1` implies `restr2` on each restriction that the rank witness `P`
  covers.

The positive positions use `SatisfiesShape_mono` and `monoE`. The content
of a `not` is `NoExtends`, and uses `SatisfiesMAt_agree_noExtends` (exact
agreement on `Lo`). -/
theorem SatisfiesMAt_stratMono {S : Schema} (hWFExtra : S.WellFormedExtra)
    (hNEF : S.NotIsExtendsFree) {τ τ' : Typing} {Z Lo : Finset Label}
    {restr1 restr2 : Finset Triple → ShapeExpr → Prop} {P : ShapeExpr → Prop}
    (hZ : S.DClosedOn Z) (hsub : τ ⊆ τ') (hagree : AgreeOn τ τ' Lo)
    (hLo : ∀ z ∈ Z, ((S.shapeDef z).depsAux false).negRefs ⊆ Lo)
    (hr : ∀ u, P u → u.depsIn Z → u.WellFormedExtra → u.NotIsExtendsFree →
      (u.depsAux false).negRefs ⊆ Lo → ∀ M, restr1 M u → restr2 M u) :
    ∀ s, S.RankOkAt P s → s.depsIn Z → s.WellFormedExtra → s.NotIsExtendsFree →
      (s.depsAux false).negRefs ⊆ Lo →
      ∀ M, SatisfiesMAt S τ restr1 M s → SatisfiesMAt S τ' restr2 M s := by
  intro s
  induction s with
  | constraint _ => intro _ _ _ _ _ M h; exact h
  | ofShape h => intro _ _ hWF _ _ M hSat; exact SatisfiesShape_mono hsub hWF M hSat
  | «extends» xs h =>
      intro hRank hdeps hWF _ _ M hSat
      have hancZ : S.ancSet xs ⊆ Z := S.ancSet_subset hZ hdeps.2
      obtain ⟨M', Mx, hdu, hE, hExt, hRestr⟩ := hSat
      refine ⟨M', Mx, hdu, SatisfiesShape_mono hsub hWF M' hE,
        fun x hx => monoE hsub _ (Mx x) (hExt x hx), fun x hx u hu => ?_⟩
      have hxZ : x ∈ Z := hancZ hx
      exact hr u (hRank x hx u hu) (restrOf_depsIn hZ hxZ hu) (restrOf_wellFormedExtra hWFExtra hu)
        (restrOf_notIsExtendsFree hNEF hu) ((restrOf_negRefs_subset hu).trans (hLo x hxZ)) _
        (hRestr x hx u hu)
  | or s1 s2 ih1 ih2 =>
      intro hRank hdeps hWF hNEF' hneg M hSat
      rw [ShapeExpr.depsIn_or] at hdeps
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      exact hSat.imp (ih1 hRank.1 hdeps.1 hWF.1 hNEF'.1 hneg.1 M)
        (ih2 hRank.2 hdeps.2 hWF.2 hNEF'.2 hneg.2 M)
  | and s1 s2 ih1 ih2 =>
      intro hRank hdeps hWF hNEF' hneg M hSat
      rw [ShapeExpr.depsIn_and] at hdeps
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      exact ⟨ih1 hRank.1 hdeps.1 hWF.1 hNEF'.1 hneg.1 M hSat.1,
        ih2 hRank.2 hdeps.2 hWF.2 hNEF'.2 hneg.2 M hSat.2⟩
  | not s _ =>
      intro _ _ _ hNEF' hneg M hSat hc
      exact hSat ((SatisfiesMAt_agree_noExtends hagree s hNEF'
        (ShapeExpr.refs_subset_of_not_negRefs hneg) M).mpr hc)

/-- `stratMono` for `SatisfiesMFuel` (Table 3). The proof is an induction
on the fuel. Each step is `SatisfiesMAt_stratMono`. -/
theorem SatisfiesMFuel_stratMono {S : Schema} (hWFExtra : S.WellFormedExtra)
    (hNEF : S.NotIsExtendsFree) {τ τ' : Typing} {Z Lo : Finset Label}
    (hZ : S.DClosedOn Z) (hsub : τ ⊆ τ') (hagree : AgreeOn τ τ' Lo)
    (hLo : ∀ z ∈ Z, ((S.shapeDef z).depsAux false).negRefs ⊆ Lo) :
    ∀ r s, S.RankOk r s → s.depsIn Z → s.WellFormedExtra → s.NotIsExtendsFree →
      (s.depsAux false).negRefs ⊆ Lo →
      ∀ M, SatisfiesMFuel r S τ M s → SatisfiesMFuel r S τ' M s := by
  intro r
  induction r with
  | zero =>
      exact SatisfiesMAt_stratMono hWFExtra hNEF hZ hsub hagree hLo (fun _ h => h.elim)
  | succ r ih => exact SatisfiesMAt_stratMono hWFExtra hNEF hZ hsub hagree hLo ih

/-- `stratMono` for `SatisfiesFuel` (Table 2), at a fuel that is sufficient
for `S`. The `.ofShape` and `.extends` leaves use
`SatisfiesMFuel_stratMono`. The content of a `not` is `NoExtends`, and uses
`SatisfiesMAt_agree_noExtends` at each leaf. -/
theorem SatisfiesFuel_stratMono {S : Schema} (hAcyclic : S.ExtAcyclic)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) {r : ℕ} (hr : S.fuelBound ≤ r)
    {G : Graph} {τ τ' : Typing} {Z Lo : Finset Label}
    (hZ : S.DClosedOn Z) (hsub : τ ⊆ τ') (hagree : AgreeOn τ τ' Lo)
    (hLo : ∀ z ∈ Z, ((S.shapeDef z).depsAux false).negRefs ⊆ Lo) (n : RDFNode) :
    ∀ s, s.depsIn Z → s.WellFormedExtra → s.NotIsExtendsFree →
      (s.depsAux false).negRefs ⊆ Lo → SatisfiesFuel r S G τ n s → SatisfiesFuel r S G τ' n s := by
  intro s
  induction s with
  | constraint _ => intro _ _ _ _ h; exact h
  | ofShape _ | «extends» _ _ =>
      intro hdeps hWF hNEF' hneg hSat
      exact SatisfiesMFuel_stratMono hWFExtra hNEF hZ hsub hagree hLo r _
        (Schema.rankOk_fuelBound hAcyclic hr _) hdeps hWF hNEF' hneg _ hSat
  | or s1 s2 ih1 ih2 =>
      intro hdeps hWF hNEF' hneg hSat
      rw [ShapeExpr.depsIn_or] at hdeps
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      exact hSat.imp (ih1 hdeps.1 hWF.1 hNEF'.1 hneg.1) (ih2 hdeps.2 hWF.2 hNEF'.2 hneg.2)
  | and s1 s2 ih1 ih2 =>
      intro hdeps hWF hNEF' hneg hSat
      rw [ShapeExpr.depsIn_and] at hdeps
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, Finset.union_subset_iff] at hneg
      exact ⟨ih1 hdeps.1 hWF.1 hNEF'.1 hneg.1 hSat.1, ih2 hdeps.2 hWF.2 hNEF'.2 hneg.2 hSat.2⟩
  | not s _ =>
      intro _ _ hNEF' hneg hSat hc
      have href := ShapeExpr.refs_subset_of_not_negRefs hneg
      refine hSat ((SatisfiesAt_congr (fun t => t.NoExtends ∧ (t.depsAux false).refs ⊆ Lo)
        ?_ ?_ ?_ ?_ s ⟨hNEF', href⟩).mpr hc)
      · rintro a b ⟨hn, hrf⟩
        simp only [ShapeExpr.depsAux, DepInfo.union_refs, Finset.union_subset_iff] at hrf
        exact ⟨⟨hn.1, hrf.1⟩, ⟨hn.2, hrf.2⟩⟩
      · rintro a b ⟨hn, hrf⟩
        simp only [ShapeExpr.depsAux, DepInfo.union_refs, Finset.union_subset_iff] at hrf
        exact ⟨⟨hn.1, hrf.1⟩, ⟨hn.2, hrf.2⟩⟩
      · rintro a ⟨hn, hrf⟩
        simp only [ShapeExpr.depsAux] at hrf
        exact ⟨hn, a.depsAux_refs_indep false true ▸ hrf⟩
      · rintro t ⟨hn, hrf⟩ M
        obtain ⟨_, h1⟩ := SatisfiesMFuel_eq r S τ
        obtain ⟨_, h2⟩ := SatisfiesMFuel_eq r S τ'
        rw [h1, h2]
        exact SatisfiesMAt_agree_noExtends hagree t hn hrf M

/-! ### Definition 8 and Proposition 1 -/

/-- `nodes(G) × (Y ∪ X)`: the universe of all the possible node-type
associations for `G` by `S`. -/
def Schema.univTyping (S : Schema) (G : Graph) : Typing := G.nodes ×ˢ (S.Y ∪ S.X)

/-- `Y_i^σ ∪ X_i^σ = {z ∈ Y ∪ X | σ(z) ≤ i}`. -/
def Schema.stratum (S : Schema) (strat : Label → ℕ) (i : ℕ) : Finset Label :=
  (S.Y ∪ S.X).filter (fun z => strat z ≤ i)

theorem Schema.mem_stratum {S : Schema} {strat : Label → ℕ} {i : ℕ} {z : Label} :
    z ∈ S.stratum strat i ↔ z ∈ S.Y ∪ S.X ∧ strat z ≤ i := by
  simp only [Schema.stratum, Finset.mem_filter]

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
agreement constraint that Definition 8 needs to connect the strata. It
agrees with `maxAgree` of 2017
(`ShexLean/Shex2017Schemas/Proposition1.lean`), with
`Schema.CorrectTyping` and `restrictTyping` in place of the 2017
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
way as the plain case. It applies `stratMono` to `S'.shapeDef x` (the
descendant that is the witness), not to `S'.shapeDef L`. -/
theorem maxTypingAgreeing_correct {S' : Schema} (hAcyclic : S'.ExtAcyclic) (hWFExtra : S'.WellFormedExtra)
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
  have hagree_t : AgreeOn t (maxTypingAgreeing S' G Lo fixed) Lo := by
    apply restrictTyping_agree
    rw [htagree, maxTypingAgreeing_restrictTo hfixed_sub hfixed_correct]
  have htcorrectL := htcorrect n L htmem
  refine ⟨fun hLA => ?_, fun hLA => ?_⟩
  · exact SatisfiesFuel_stratMono hAcyclic hWFExtra hNEF le_rfl hDClosed hsub_t hagree_t hLo n
      (S'.shapeDef L) (S'.shapeDef_depsIn hDClosed hL) (hWFExtra L) (hNEF L) (hLo L hL)
      (htcorrectL.1 hLA)
  · obtain ⟨x, hxmem, hSatx⟩ := htcorrectL.2 hLA
    have hxY : x ∈ S'.Y ∪ S'.X := by
      have hxdesc : x ∈ S'.desc L := (Finset.mem_sdiff.mp hxmem).1
      exact Finset.mem_union_right _ (Schema.mem_desc.mp hxdesc).1
    exact ⟨x, hxmem, SatisfiesFuel_stratMono hAcyclic hWFExtra hNEF le_rfl hDClosed hsub_t
      hagree_t hLo n (S'.shapeDef x) (S'.shapeDef_depsIn hDClosed hxY) (hWFExtra x) (hNEF x)
      (hLo x hxY) hSatx⟩

/-! ### Schema invariance of `Satisfies` across `stratRestrict`

This is the last part that Proposition 1 needs. `Satisfies` uses the
schema in rule 18 (`.ancSet`, `.anc` and `shapeDef`), and its fuel
`S.fuelBound` depends on the schema. Thus,
`Satisfies (S.stratRestrict strat i) G τ n s` and
`Satisfies (S.stratRestrict strat j) G τ n s` are different propositions.

In 2017, `stratTypingSeq_correct` does not have this problem, because
`Satisfies` never uses the schema. Here, `SatisfiesFuel_transfer` (a change
of schema at the same fuel) and `stableFuel` (a change of fuel) solve it. -/

/-- `ExtAcyclic` stays true for each `stratRestrict`. Its `X` only becomes
smaller, and `extEdge` uses only
`shapeDef` (`stratRestrict` never changes `shapeDef`). Thus, a cycle in
the restriction is also a cycle in `S`. -/
theorem Schema.stratRestrict_ExtAcyclic {S : Schema} (hAcyclic : S.ExtAcyclic)
    (strat : Label → ℕ) (i : ℕ) : (S.stratRestrict strat i).ExtAcyclic := by
  intro x hx
  simp only [Schema.stratRestrict, Finset.mem_filter] at hx
  exact hAcyclic x hx.1

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
`≤ i`. Each element of the unrestricted `S.anc x` already has
`strat ≤ strat x ≤ i` (the first bullet of Definition 7, through
`extEdge ⊆ depExtends ⊆ DEdge`). Thus, if you filter `S.X` to
`strat ≤ i` before you compute `anc`, you remove nothing.

Because of this, `Satisfies` computed with two different `stratRestrict`
levels agrees for each label in the lower level. The `ancSet` and
`extends`-step data that the `.extends` case of `SatisfiesMFuel` uses do
not depend on the (sufficiently high) stratum level of the schema
restriction. -/
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
different `fuelBound` and `ancSet` bookkeeping). But the evaluation of
`def(x)` never goes outside the strata `≤ i` (`Schema.shapeDef_depsIn`
and `Schema.stratum_DClosedOn`). In that region, the `.anc` of the two
schemas is the same (`Schema.stratRestrict_anc_eq`). Thus, all that
`SatisfiesFuel` and `SatisfiesMFuel` use also agrees.

The proof combines two lemmas:

* `stableFuel` (same schema): it connects the canonical fuel of each side
  to a shared sufficient value.
* `SatisfiesFuel_transfer` (same fuel): it connects the two schemas.

This solves the problem that stops a direct port, in the 2017 style, of
the inductive step of `stratTypingSeq_correct`. In 2017, `Satisfies` does
not depend on the schema. Here, it does. -/
theorem Satisfies_stratRestrict_agree {S : Schema}
    (hAcyclic : S.ExtAcyclic) (hDClosed : S.DClosed) (strat : Stratification S)
    {i j : ℕ} (hij : i ≤ j) {x : Label} (hxY : x ∈ S.Y ∪ S.X) (hxi : strat.strat x ≤ i)
    {G : Graph} {τ : Typing} {n : RDFNode} :
    Satisfies (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) ↔
    Satisfies (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) := by
  have hZ : S.DClosedOn (S.stratum strat.strat i) := Schema.stratum_DClosedOn hDClosed strat i
  have hxZ : x ∈ S.stratum strat.strat i := Schema.mem_stratum.mpr ⟨hxY, hxi⟩
  have hAnc : ∀ y ∈ S.stratum strat.strat i,
      (S.stratRestrict strat.strat i).anc y = (S.stratRestrict strat.strat j).anc y := by
    intro y hy
    obtain ⟨hyY, hyi⟩ := Schema.mem_stratum.mp hy
    rw [Schema.stratRestrict_anc_eq hDClosed strat hyY hyi,
      Schema.stratRestrict_anc_eq hDClosed strat hyY (hyi.trans hij)]
  have hAc1 := Schema.stratRestrict_ExtAcyclic hAcyclic strat.strat i
  have hAc2 := Schema.stratRestrict_ExtAcyclic hAcyclic strat.strat j
  have hF1 := le_max_left (S.stratRestrict strat.strat i).fuelBound
    (S.stratRestrict strat.strat j).fuelBound
  have hF2 := le_max_right (S.stratRestrict strat.strat i).fuelBound
    (S.stratRestrict strat.strat j).fuelBound
  calc Satisfies (S.stratRestrict strat.strat i) G τ n (S.shapeDef x)
      _ ↔ SatisfiesFuel _ (S.stratRestrict strat.strat i) G τ n (S.shapeDef x) :=
        stableFuel hAc1 le_rfl hF1 G τ n _
      _ ↔ SatisfiesFuel _ (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) :=
        SatisfiesFuel_transfer (S2 := S.stratRestrict strat.strat j) hAc1 hF1 hZ
          (fun _ _ _ => Iff.rfl) rfl hAnc
          (S.shapeDef_depsIn hZ hxZ) n
      _ ↔ Satisfies (S.stratRestrict strat.strat j) G τ n (S.shapeDef x) :=
        (stableFuel hAc2 le_rfl hF2 G τ n _).symm

/-- `(S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X` (a union of
two sets, each with its own filter) and `S.stratum strat i` (one filter
over the union) are the same `Finset`, made in different ways. This lemma
connects the `Y ∪ X` form of `Schema.univTyping` with the form of
`Schema.stratum_mono`. -/
theorem Schema.stratRestrict_YX_eq_stratum (S : Schema) (strat : Label → ℕ) (i : ℕ) :
    (S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X = S.stratum strat i := by
  unfold Schema.stratRestrict Schema.stratum
  rw [Finset.filter_union]

/-- The labels of `S.stratRestrict strat i` are the labels of `S` with a
stratum `≤ i`. -/
theorem Schema.mem_stratRestrict_YX {S : Schema} {strat : Label → ℕ} {i : ℕ} {z : Label} :
    z ∈ (S.stratRestrict strat i).Y ∪ (S.stratRestrict strat i).X ↔
      z ∈ S.Y ∪ S.X ∧ strat z ≤ i := by
  rw [Schema.stratRestrict_YX_eq_stratum, Schema.mem_stratum]

theorem Schema.mem_stratRestrict_X {S : Schema} {strat : Label → ℕ} {i : ℕ} {z : Label} :
    z ∈ (S.stratRestrict strat i).X ↔ z ∈ S.X ∧ strat z ≤ i := by
  simp only [Schema.stratRestrict, Finset.mem_filter]

theorem Schema.mem_stratRestrict_A {S : Schema} {strat : Label → ℕ} {i : ℕ} {z : Label} :
    z ∈ (S.stratRestrict strat i).A ↔ z ∈ S.A ∧ strat z ≤ i := by
  simp only [Schema.stratRestrict, Finset.mem_filter]

/-- At the top stratum `k`, the restriction removes nothing. -/
theorem Schema.stratRestrict_top {S : Schema} (strat : Stratification S) :
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
larger when `i` becomes larger. The important step is to move the
`Satisfies` witnesses with `Satisfies_stratRestrict_agree`. -/
theorem Schema.correctTyping_stratRestrict_mono {S : Schema}
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
  the previous typing at stratum `i` up to the schema of stratum `i+1`.

This solves the problem that a direct port in the 2017 style does not
solve. Refer to the docstring of `Satisfies_stratRestrict_agree`. -/
theorem stratTypingSeq_correct {S : Schema} (hAcyclic : S.ExtAcyclic)
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
          (((S.stratRestrict strat.strat (i + 1)).shapeDef z).depsAux false).negRefs ⊆
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
theorem proposition1 {S : Schema} (hAcyclic : S.ExtAcyclic)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat : Stratification S) (G : Graph) :
    S.CorrectTyping G (Typing8 G S strat) := by
  have := (stratTypingSeq_correct hAcyclic hWFExtra hNEF hDClosed strat G strat.k).2
  rwa [Schema.stratRestrict_top] at this

end ShexLean.Inheritance
