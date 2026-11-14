import ShexLean.Shex2025Inheritance.Termination
import ShexLean.InheritanceCore.MaxTyping
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

open ShexLean.InheritanceCore hiding Schema

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
abbrev ShapeExpr.depsIn (s : ShapeExpr) (Z : Finset Label) : Prop := InheritanceCore.depsIn s Z

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
  simp only [ShapeExpr.depsIn, InheritanceCore.depsIn, ShapeExpr.shapeSyntax_deps,
    ShapeExpr.shapeSyntax_extendsTargets, ShapeExpr.depsAux, DepInfo.union_refs, ShapeExpr.extendsTargets,
    Finset.union_subset_iff]
  tauto

theorem ShapeExpr.depsIn_and {a b : ShapeExpr} {Z : Finset Label} :
    (ShapeExpr.and a b).depsIn Z ↔ a.depsIn Z ∧ b.depsIn Z := by
  simp only [ShapeExpr.depsIn, InheritanceCore.depsIn, ShapeExpr.shapeSyntax_deps,
    ShapeExpr.shapeSyntax_extendsTargets, ShapeExpr.depsAux, DepInfo.union_refs, ShapeExpr.extendsTargets,
    Finset.union_subset_iff]
  tauto

theorem ShapeExpr.depsIn_not {a : ShapeExpr} {Z : Finset Label} :
    (ShapeExpr.not a).depsIn Z ↔ a.depsIn Z := by
  simp only [ShapeExpr.depsIn, InheritanceCore.depsIn, ShapeExpr.shapeSyntax_deps,
    ShapeExpr.shapeSyntax_extendsTargets, ShapeExpr.depsAux, ShapeExpr.extendsTargets,
    a.depsAux_refs_indep true false]

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
schema or on `evalRestr` at all, because rule 18 is not used. No closure
hypothesis on `Z` is necessary.

The `not` case of `stratMono` needs this lemma. (By
`ShapeExpr.NotIsExtendsFree`, the content of a `not` node is always
`NoExtends`.) -/
theorem SatisfiesMAt_agree_noExtends {S1 S2 : Schema} {τ1 τ2 : Typing}
    {evalRestr1 evalRestr2 : Finset Triple → ShapeExpr → Prop} {Z : Finset Label}
    (hagree : AgreeOn τ1 τ2 Z) :
    ∀ s, s.NoExtends → (s.depsAux false).refs ⊆ Z →
      ∀ M, SatisfiesMAt S1 τ1 evalRestr1 M s ↔ SatisfiesMAt S2 τ2 evalRestr2 M s := by
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
* `evalRestr1` and `evalRestr2` agree on each restriction `u` that the rank
  witness `P` covers, if `u` reaches only labels in `Z`.
* The shape reaches only labels in `Z` (`depsIn`).

The only case that uses the schema is `.extends`. Each other case is a
plain structural step. -/
theorem SatisfiesMAt_transfer {S1 S2 : Schema} {τ1 τ2 : Typing}
    {evalRestr1 evalRestr2 : Finset Triple → ShapeExpr → Prop} {P : ShapeExpr → Prop}
    {Z : Finset Label} (hZ : S1.DClosedOn Z) (hagree : AgreeOn τ1 τ2 Z)
    (hdef : S1.shapeDef = S2.shapeDef) (hanc : ∀ x ∈ Z, S1.anc x = S2.anc x)
    (hr : ∀ u, P u → u.depsIn Z → ∀ M, evalRestr1 M u ↔ evalRestr2 M u) :
    ∀ s, S1.RankOkAt P s → s.depsIn Z →
      ∀ M, SatisfiesMAt S1 τ1 evalRestr1 M s ↔ SatisfiesMAt S2 τ2 evalRestr2 M s := by
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
* `evalRestr1` implies `evalRestr2` on each restriction that the rank witness `P`
  covers.

The positive positions use `SatisfiesShape_mono` and `monoE`. The content
of a `not` is `NoExtends`, and uses `SatisfiesMAt_agree_noExtends` (exact
agreement on `Lo`). -/
theorem SatisfiesMAt_stratMono {S : Schema} (hWFExtra : S.WellFormedExtra)
    (hNEF : S.NotIsExtendsFree) {τ τ' : Typing} {Z Lo : Finset Label}
    {evalRestr1 evalRestr2 : Finset Triple → ShapeExpr → Prop} {P : ShapeExpr → Prop}
    (hZ : S.DClosedOn Z) (hsub : τ ⊆ τ') (hagree : AgreeOn τ τ' Lo)
    (hLo : ∀ z ∈ Z, ((S.shapeDef z).depsAux false).negRefs ⊆ Lo)
    (hr : ∀ u, P u → u.depsIn Z → u.WellFormedExtra → u.NotIsExtendsFree →
      (u.depsAux false).negRefs ⊆ Lo → ∀ M, evalRestr1 M u → evalRestr2 M u) :
    ∀ s, S.RankOkAt P s → s.depsIn Z → s.WellFormedExtra → s.NotIsExtendsFree →
      (s.depsAux false).negRefs ⊆ Lo →
      ∀ M, SatisfiesMAt S τ evalRestr1 M s → SatisfiesMAt S τ' evalRestr2 M s := by
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

/-! ### The instance for the generic results

`ShexLean/InheritanceCore/MaxTyping.lean`, `Lemma2.lean` and
`Algorithm1.lean` prove Definition 8, Proposition 1, Lemma 2 and the
correctness of Algorithm 1 for each instance of `InheritanceSemantics`.
This instance gives them `Satisfies` and the two facts above. -/

instance : InheritanceSemantics ShapeExpr where
  Satisfies := Satisfies
  WellFormedExtra := ShapeExpr.WellFormedExtra
  NotIsExtendsFree := ShapeExpr.NotIsExtendsFree
  satisfies_transfer {S1 S2 G τ1 τ2 _ s} hAc1 hAc2 hdef hZ hagree hanc hdeps n :=
    (stableFuel hAc1 le_rfl (le_max_left S1.fuelBound S2.fuelBound) G τ1 n s).trans
      ((SatisfiesFuel_transfer hAc1 (le_max_left _ _) hZ hagree hdef hanc hdeps n).trans
        (stableFuel hAc2 le_rfl (le_max_right S1.fuelBound S2.fuelBound) G τ2 n s).symm)
  satisfies_stratMono {_ _ _ _ _ _ s} hAcyclic hWFExtra hNEF hZ hsub hagree hLo n hdeps hWF
      hNEF' hneg :=
    SatisfiesFuel_stratMono hAcyclic hWFExtra hNEF le_rfl hZ hsub hagree hLo n s hdeps hWF hNEF' hneg

/-- **Proposition 1** (the 2025 paper). For every schema `S`, stratification `σ`
of `S`, and graph `G`, the typing `τ_max(S,σ,G)` is a correct typing. The
proof is `ShexLean.InheritanceCore.proposition1`. -/
theorem proposition1 {S : Schema} (hAcyclic : S.ExtAcyclic)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat : Stratification S) (G : Graph) :
    S.CorrectTyping G (Typing8 G S strat) :=
  InheritanceCore.proposition1 hAcyclic hWFExtra hNEF hDClosed strat G

end ShexLean.Inheritance
