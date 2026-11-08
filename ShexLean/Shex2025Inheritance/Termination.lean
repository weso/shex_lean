import ShexLean.Shex2025Inheritance.Stratification
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
Lemma 1 (§4.2) of the 2025 paper "Shape Expressions with Inheritance":

> Lemma 1. The evaluation of `G, n, τ ⊨_S def(z)` always terminates, for
> every schema `S = (Y, X, def, A)`, graph `G`, node `n` of `G`, typing `τ`
> of `G` by `S`, and label `z ∈ Y ∪ X`.

`Semantics.lean` avoids the termination problem with an explicit argument
`Fuel : ℕ` in `SatisfiesFuel`, `SatisfiesMFuel` and `SatisfiesEFuel`. Each
recursive call decreases `Fuel`, and the result is `False` when no fuel
remains. Thus, the Lean function is total by construction, but it is not
yet the real relation of the paper (which does not depend on fuel).

This file shows that, for a well-defined schema, the result stops
depending on `Fuel` when `Fuel` is sufficiently large. Thus, the
approximation bounded by fuel becomes equal to the real relation.

In the 2017 formalization, `typing` gives the shape of a reference. Thus,
termination is a free structural recursion on the syntax tree. Here, the
`extends` rule of Table 3 does a recursion into the definitions of other
labels (`(S.shapeDef x).extTe` and `.restrOf`, for each ancestor `x`). This
is a schema lookup. It is not a subterm of the current expression.

The termination argument of the paper (the proof sketch of Lemma 1) is one
sentence: the tree of recursive calls is finite "due to the acyclic nature
of the extension hierarchy". A precise proof needs two items:

* A rank function on labels that is a witness of the acyclicity of `H_S`
  (`Schema.extRank` below).
* A combined measure that decreases on each recursive call. This includes
  the `extends` steps (controlled by the rank) and the ordinary structural
  steps on the syntax tree (`Schema.reqFuelR` and `Schema.reqFuelGen`).

The proof has the same generality as Lemma 1 of the paper. It assumes only
`WellFormedX` (Definition 2) and `ExtAcyclic` (Definition 6). It puts no
restriction on the locations of `extends` nodes. An `extends` node can
also be inside a restriction `u` (`extends X h and u`).
-/

namespace ShexLean.Inheritance

/-! ### Extension-hierarchy acyclicity -/

/-- `S.anc` becomes strictly smaller along each edge of `H_S`, if
`S.ExtAcyclic` is true (the acyclicity condition of Definition 6).

If `x` extends `y`, then `x` also extends each label that `y` extends
transitively. But `x ∈ S.anc x`, and `x ∈ S.anc y` closes a cycle through
the edge `x → y`. This is the usual argument with the number of ancestors
as a rank function on a DAG. Because of it, `ExtAcyclic` alone gives a
well-founded measure. -/
theorem Schema.anc_ssubset_of_extEdge {S : Schema} (hAcyclic : S.ExtAcyclic)
    {x y : Label} (hxX : x ∈ S.X) (hxy : S.extEdge x y) :
    S.anc y ⊂ S.anc x := by
  have hsub : S.anc y ⊆ S.anc x := by
    intro z hz
    unfold Schema.anc at hz ⊢
    have := Classical.decPred (Relation.ReflTransGen S.extEdge y)
    have := Classical.decPred (Relation.ReflTransGen S.extEdge x)
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, Relation.ReflTransGen.head hxy hz.2⟩
  refine ⟨hsub, fun hsub' => ?_⟩
  have hxancx : x ∈ S.anc x := by
    unfold Schema.anc
    have := Classical.decPred (Relation.ReflTransGen S.extEdge x)
    simp only [Finset.mem_filter]
    exact ⟨hxX, Relation.ReflTransGen.refl⟩
  have hxancy : x ∈ S.anc y := hsub' hxancx
  have hxy' : Relation.ReflTransGen S.extEdge y x := by
    unfold Schema.anc at hxancy
    have := Classical.decPred (Relation.ReflTransGen S.extEdge y)
    simp only [Finset.mem_filter] at hxancy
    exact hxancy.2
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy' with heq | htrans
  · exact hAcyclic x hxX (Relation.TransGen.single (heq.symm ▸ hxy))
  · exact hAcyclic x hxX (Relation.TransGen.head hxy htrans)

/-- `S.extRank x := (S.anc x).card`: a rank in `ℕ` that is a witness of the
acyclicity of `H_S`. It decreases strictly along each edge
(`extRank_lt_of_extEdge` below). The termination argument in the rest of
this file uses this well-founded measure. -/
noncomputable def Schema.extRank (S : Schema) (x : Label) : ℕ := (S.anc x).card

/-- The rank form of `anc_ssubset_of_extEdge`: `extRank` decreases
strictly along each edge of `H_S` that starts at a label of `S`. -/
theorem Schema.extRank_lt_of_extEdge {S : Schema} (hAcyclic : S.ExtAcyclic)
    {x y : Label} (hxX : x ∈ S.X) (hxy : S.extEdge x y) :
    S.extRank y < S.extRank x :=
  Finset.card_lt_card (S.anc_ssubset_of_extEdge hAcyclic hxX hxy)

/-- `extRank` does not increase along an ancestor path. If `x' ∈ S.anc x`,
then `extRank x' ≤ extRank x`. (The inequality is not strict, because
`x ∈ S.anc x` reflexively.) This bounds the rank of each label that a
rule-18 partition reaches (`x' ∈ S.ancSet xs`), not only the direct
targets `xs`. -/
theorem Schema.extRank_le_of_mem_anc {S : Schema} {x x' : Label} (hx' : x' ∈ S.anc x) :
    S.extRank x' ≤ S.extRank x := by
  apply Finset.card_le_card
  intro z hz
  unfold Schema.anc at hx' hz ⊢
  have := Classical.decPred (Relation.ReflTransGen S.extEdge x)
  have := Classical.decPred (Relation.ReflTransGen S.extEdge x')
  simp only [Finset.mem_filter] at hx' hz ⊢
  exact ⟨hz.1, hx'.2.trans hz.2⟩

/-! ### The base case: `NoExtends` shapes need no schema lookups -/

/-- `s` contains no `.extends` node at any location (also not nested in
`or`, `and` or `not`). -/
def ShapeExpr.NoExtends : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends _ _ => False
  | .or s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .and s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .not s => s.NoExtends

/-! ### The stabilization argument

The argument follows the dependency chain of the definitions (refer to the
module docstring of `Semantics.lean`):

1. `SatisfiesEFuel` becomes stable alone (it does no schema lookups).
2. `SatisfiesMFuel` becomes stable with step 1 and a base case for
   `NoExtends` shapes.
3. `SatisfiesFuel` becomes stable with step 2. -/

/-- The structural size of a triple expression. This is a large (not
tight) bound that gives sufficient fuel. Each recursive call of
`SatisfiesEFuel` is on a strictly smaller sub-expression. Thus, the size
decreases by 1 or more at each step. -/
def TripleExpr.size : TripleExpr → ℕ
  | .empty => 1
  | .tc _ _ => 1
  | .choice e1 e2 => e1.size + e2.size + 1
  | .seq e1 e2 => e1.size + e2.size + 1
  | .star e => e.size + 1

/-- `SatisfiesEFuel` becomes stable when `Fuel ≥ e.size`. Table 1 never
does a schema lookup (`τ` gives the label of `.tc`, refer to the module
docstring of `Semantics.lean`). Thus, the proof needs no hypothesis on
`S`. It is a plain structural induction on `e`. -/
theorem stableE (e : TripleExpr) :
    ∀ fuel1 fuel2, e.size ≤ fuel1 → e.size ≤ fuel2 →
      ∀ (S : Schema) (G : Graph) (τ : Typing) (M : Finset Triple),
        SatisfiesEFuel fuel1 S G τ M e ↔ SatisfiesEFuel fuel2 S G τ M e := by
  induction e with
  | empty =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [TripleExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [TripleExpr.size] at h2
      rfl
  | tc p z =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [TripleExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [TripleExpr.size] at h2
      rfl
  | choice e1 e2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [TripleExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [TripleExpr.size] at h2
      simp only [TripleExpr.size] at h1 h2
      show SatisfiesEFuel f1 S G τ M e1 ∨ SatisfiesEFuel f1 S G τ M e2 ↔
        SatisfiesEFuel f2 S G τ M e1 ∨ SatisfiesEFuel f2 S G τ M e2
      rw [ih1 f1 f2 (by omega) (by omega) S G τ M, ih2 f1 f2 (by omega) (by omega) S G τ M]
  | seq e1 e2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [TripleExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [TripleExpr.size] at h2
      simp only [TripleExpr.size] at h1 h2
      show (∃ M1 M2, DisjointUnion M M1 M2 ∧
            SatisfiesEFuel f1 S G τ M1 e1 ∧ SatisfiesEFuel f1 S G τ M2 e2) ↔
          (∃ M1 M2, DisjointUnion M M1 M2 ∧
            SatisfiesEFuel f2 S G τ M1 e1 ∧ SatisfiesEFuel f2 S G τ M2 e2)
      constructor
      · rintro ⟨M1, M2, hdu, h1', h2'⟩
        exact ⟨M1, M2, hdu, (ih1 f1 f2 (by omega) (by omega) S G τ M1).mp h1',
          (ih2 f1 f2 (by omega) (by omega) S G τ M2).mp h2'⟩
      · rintro ⟨M1, M2, hdu, h1', h2'⟩
        exact ⟨M1, M2, hdu, (ih1 f1 f2 (by omega) (by omega) S G τ M1).mpr h1',
          (ih2 f1 f2 (by omega) (by omega) S G τ M2).mpr h2'⟩
  | star e ih =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [TripleExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [TripleExpr.size] at h2
      simp only [TripleExpr.size] at h1 h2
      show (∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧
            ∀ Ni ∈ Ns, SatisfiesEFuel f1 S G τ Ni e) ↔
          (∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧
            ∀ Ni ∈ Ns, SatisfiesEFuel f2 S G τ Ni e)
      constructor
      · rintro ⟨Ns, hdu, hall⟩
        exact ⟨Ns, hdu, fun Ni hNi => (ih f1 f2 (by omega) (by omega) S G τ Ni).mp (hall Ni hNi)⟩
      · rintro ⟨Ns, hdu, hall⟩
        exact ⟨Ns, hdu, fun Ni hNi => (ih f1 f2 (by omega) (by omega) S G τ Ni).mpr (hall Ni hNi)⟩

/-- The structural size of a shape expression. (It has the same role as
`TripleExpr.size`: a large bound.) -/
def ShapeExpr.size : ShapeExpr → ℕ
  | .constraint _ => 1
  | .ofShape h => h.triples.size + 1
  | .extends _ h => h.triples.size + 1
  | .or s1 s2 => s1.size + s2.size + 1
  | .and s1 s2 => s1.size + s2.size + 1
  | .not s => s.size + 1

/-- `SatisfiesMFuel` becomes stable on each `NoExtends` shape when
`Fuel ≥ s.size`. It needs no hypothesis on the schema, because such a
shape never uses rule 18. We prove it before the general `stableMGen`
below, because `restr(x)` also needs it. `restr(x)` is not a subterm of
the shape of the general induction. -/
theorem stableM_noExtends (u : ShapeExpr) (hu : u.NoExtends) :
    ∀ fuel1 fuel2, u.size ≤ fuel1 → u.size ≤ fuel2 →
      ∀ (S : Schema) (G : Graph) (τ : Typing) (M : Finset Triple),
        SatisfiesMFuel fuel1 S G τ M u ↔ SatisfiesMFuel fuel2 S G τ M u := by
  induction u with
  | constraint c =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.size] at h2
      rfl
  | ofShape h =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.size] at h2
      simp only [ShapeExpr.size] at h1 h2
      show (SatisfiesEFuel f1 S G τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)) ↔
          (SatisfiesEFuel f2 S G τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅))
      rw [stableE h.triples f1 f2 (by omega) (by omega) S G τ (Me τ M h.triples)]
  | «extends» xs h => simp only [ShapeExpr.NoExtends] at hu
  | or s1 s2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.size] at h2
      simp only [ShapeExpr.size] at h1 h2
      simp only [ShapeExpr.NoExtends] at hu
      show SatisfiesMFuel f1 S G τ M s1 ∨ SatisfiesMFuel f1 S G τ M s2 ↔
        SatisfiesMFuel f2 S G τ M s1 ∨ SatisfiesMFuel f2 S G τ M s2
      rw [ih1 hu.1 f1 f2 (by omega) (by omega) S G τ M, ih2 hu.2 f1 f2 (by omega) (by omega) S G τ M]
  | and s1 s2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.size] at h2
      simp only [ShapeExpr.size] at h1 h2
      simp only [ShapeExpr.NoExtends] at hu
      show SatisfiesMFuel f1 S G τ M s1 ∧ SatisfiesMFuel f1 S G τ M s2 ↔
        SatisfiesMFuel f2 S G τ M s1 ∧ SatisfiesMFuel f2 S G τ M s2
      rw [ih1 hu.1 f1 f2 (by omega) (by omega) S G τ M, ih2 hu.2 f1 f2 (by omega) (by omega) S G τ M]
  | not s ih =>
      intro fuel1 fuel2 h1 h2 S G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.size] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.size] at h2
      simp only [ShapeExpr.size] at h1 h2
      simp only [ShapeExpr.NoExtends] at hu
      show ¬ SatisfiesMFuel f1 S G τ M s ↔ ¬ SatisfiesMFuel f2 S G τ M s
      rw [ih hu f1 f2 (by omega) (by omega) S G τ M]

/-! ### The fuel bound indexed by rank, and why it is sufficient

* `ShapeExpr.reqFuelAt S lower s` computes a fuel bound for `s`. For each
  `.extends` node, it uses `lower` as the bound for the restrictions of
  the ancestors.
* `Schema.reqFuelR S r` gives `lower` recursively, indexed by a rank
  budget `r`:
  * `reqFuelR S 0 := ShapeExpr.size`. This is sound at rank 0, where each
    reachable shape is `NoExtends`.
  * `reqFuelR S (r+1) := reqFuelAt S (reqFuelR S r)`.

`Schema.RankOk S r s` is the side condition: rank `r` covers each extends
target that is reachable from `s`. It is made in the same way as
`reqFuelR`.

`Schema.rankOk_shapeDef` is the acyclicity argument. For `x ∈ S.X`,
`RankOk S (extRank x) (S.shapeDef x)` is true, by strong induction on
`extRank x`. The reason is that each extends target reachable from the
definition of `x` has a strictly smaller rank (`extRank_lt_of_extEdge`).

`Schema.rankOk_any` extends this result to each `ShapeExpr`, not only to
an `S.shapeDef x`. It uses one global rank bound,
`S.X.sup S.extRank + 1`. This also covers the top-level queries
`S.shapeDef z` for a simple label `z` that is not in `S.X`. -/

noncomputable def ShapeExpr.reqFuelAt (S : Schema) (lower : ShapeExpr → ℕ) : ShapeExpr → ℕ
  | .constraint _ => 1
  | .ofShape h => h.triples.size + 1
  | .extends xs h =>
      max (h.triples.size + 1)
        ((S.ancSet xs).sup (fun x =>
          max ((S.shapeDef x).extTe.size + 1)
            (match (S.shapeDef x).restrOf with
             | none => 0
             | some u => lower u))) + 1
  | .or s1 s2 => max (ShapeExpr.reqFuelAt S lower s1) (ShapeExpr.reqFuelAt S lower s2) + 1
  | .and s1 s2 => max (ShapeExpr.reqFuelAt S lower s1) (ShapeExpr.reqFuelAt S lower s2) + 1
  | .not s => ShapeExpr.reqFuelAt S lower s + 1

/-- The fuel bound indexed by rank. `reqFuelR S r` is `reqFuelAt` iterated
`r` times. It starts from plain `ShapeExpr.size`, which is sound at rank
`0`, where each reachable shape is `NoExtends`. -/
noncomputable def Schema.reqFuelR (S : Schema) : ℕ → ShapeExpr → ℕ
  | 0 => ShapeExpr.size
  | r + 1 => ShapeExpr.reqFuelAt S (Schema.reqFuelR S r)

/-- The rank-`r` version of `ShapeExpr.NoExtends`. For each `.extends`
node, the restrictions of the ancestors are covered, unfolded through `r`
more cascading `.extends` steps. `RankOk S 0` is the same as
`NoExtends`. -/
def Schema.RankOkAt (S : Schema) (lowerOk : ShapeExpr → Prop) : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends xs _ => ∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u → lowerOk u
  | .or s1 s2 => Schema.RankOkAt S lowerOk s1 ∧ Schema.RankOkAt S lowerOk s2
  | .and s1 s2 => Schema.RankOkAt S lowerOk s1 ∧ Schema.RankOkAt S lowerOk s2
  | .not s => Schema.RankOkAt S lowerOk s

noncomputable def Schema.RankOk (S : Schema) : ℕ → ShapeExpr → Prop
  | 0 => ShapeExpr.NoExtends
  | r + 1 => Schema.RankOkAt S (Schema.RankOk S r)

theorem Schema.RankOkAt.of_noExtends (S : Schema) (lowerOk : ShapeExpr → Prop) :
    ∀ s : ShapeExpr, s.NoExtends → Schema.RankOkAt S lowerOk s := by
  intro s
  induction s with
  | constraint c => intro _; trivial
  | ofShape h => intro _; trivial
  | «extends» xs h => intro hs; simp [ShapeExpr.NoExtends] at hs
  | or s1 s2 ih1 ih2 =>
      intro hs
      simp only [ShapeExpr.NoExtends] at hs
      exact ⟨ih1 hs.1, ih2 hs.2⟩
  | and s1 s2 ih1 ih2 =>
      intro hs
      simp only [ShapeExpr.NoExtends] at hs
      exact ⟨ih1 hs.1, ih2 hs.2⟩
  | not s ih =>
      intro hs
      simp only [ShapeExpr.NoExtends] at hs
      exact ih hs

theorem Schema.RankOkAt.mono_pred (S : Schema) {P Q : ShapeExpr → Prop} (hPQ : ∀ u, P u → Q u) :
    ∀ s, Schema.RankOkAt S P s → Schema.RankOkAt S Q s := by
  intro s
  induction s with
  | constraint c => intro _; trivial
  | ofShape h => intro _; trivial
  | «extends» xs h =>
      intro hs x hx u hu
      exact hPQ u (hs x hx u hu)
  | or s1 s2 ih1 ih2 => intro hs; exact ⟨ih1 hs.1, ih2 hs.2⟩
  | and s1 s2 ih1 ih2 => intro hs; exact ⟨ih1 hs.1, ih2 hs.2⟩
  | not s ih => intro hs; exact ih hs

/-- `RankOk` is monotone. If a rank is sufficient for `s`, each higher
rank is also sufficient. -/
theorem Schema.RankOk.mono {S : Schema} : ∀ r s, Schema.RankOk S r s → Schema.RankOk S (r + 1) s := by
  intro r
  induction r with
  | zero =>
      intro s hs
      show Schema.RankOkAt S (Schema.RankOk S 0) s
      exact Schema.RankOkAt.of_noExtends S _ s hs
  | succ r' ih =>
      intro s hs
      show Schema.RankOkAt S (Schema.RankOk S (r' + 1)) s
      exact Schema.RankOkAt.mono_pred S ih s hs

theorem Schema.RankOk.mono_le {S : Schema} {r r' : ℕ} (h : r ≤ r') :
    ∀ s, Schema.RankOk S r s → Schema.RankOk S r' s := by
  induction h with
  | refl => intro s hs; exact hs
  | step _ ih => intro s hs; exact Schema.RankOk.mono _ s (ih s hs)

/-- Each `x ∈ S.X` has `extRank x ≥ 1` (reflexively, `x ∈ S.anc x`). Thus,
you can always write `extRank x` as `m + 1`. -/
theorem Schema.extRank_succ {S : Schema} {x : Label} (hx : x ∈ S.X) :
    ∃ m, S.extRank x = m + 1 := by
  have hxax : x ∈ S.anc x := by
    unfold Schema.anc
    have := Classical.decPred (Relation.ReflTransGen S.extEdge x)
    simp only [Finset.mem_filter]
    exact ⟨hx, Relation.ReflTransGen.refl⟩
  have h1 : 1 ≤ S.extRank x := by
    unfold Schema.extRank
    exact Finset.one_le_card.mpr ⟨x, hxax⟩
  exact ⟨S.extRank x - 1, by omega⟩

theorem Schema.ancSet_subset_X {S : Schema} {xs : Finset Label} : S.ancSet xs ⊆ S.X := by
  intro x' hx'
  unfold Schema.ancSet at hx'
  obtain ⟨z, -, hx'z⟩ := Finset.mem_biUnion.mp hx'
  unfold Schema.anc at hx'z
  have := Classical.decPred (Relation.ReflTransGen S.extEdge z)
  simp only [Finset.mem_filter] at hx'z
  exact hx'z.1

/-- From the `RankOk` of the definition of `x` (`extends xs h [and u]`),
get the `RankOk` of its restriction `u`. -/
theorem Schema.RankOk_restrOf {S : Schema} (hWFX : S.WellFormedX) {x : Label} (hx : x ∈ S.X)
    {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u)
    (hRank : Schema.RankOk S (S.extRank x) (S.shapeDef x)) :
    Schema.RankOk S (S.extRank x) u := by
  obtain ⟨xs, h, hcase⟩ := hWFX x hx
  rcases hcase with heq | ⟨u', heq⟩
  · rw [heq] at hu; simp [ShapeExpr.restrOf] at hu
  · rw [heq] at hu
    simp only [ShapeExpr.restrOf] at hu
    obtain rfl := Option.some.inj hu
    rw [heq] at hRank
    obtain ⟨m, hm⟩ := Schema.extRank_succ hx
    rw [hm] at hRank ⊢
    have hRank' := hRank
    unfold Schema.RankOk at hRank'
    exact hRank'.2

/-- Let `e` be a `ShapeExpr` whose direct `.extends` targets are all real
edges of `H_S` out of `x`. Let each `x' ∈ S.X` with a strictly smaller
rank already have `RankOk` of its definition. Then `e` is `RankOkAt` at
rank `m := extRank x - 1`.

With `e := S.shapeDef x`, this closes the induction in
`rankOk_shapeDef`. The statement is for a general `e`, because the
restriction `u` of `x` needs the same fact. -/
theorem Schema.RankOkAt_of_edges {S : Schema} (hAcyclic : S.ExtAcyclic) (hWFX : S.WellFormedX)
    {x : Label} (hx : x ∈ S.X)
    (IH : ∀ x' ∈ S.X, S.extRank x' < S.extRank x → Schema.RankOk S (S.extRank x') (S.shapeDef x'))
    {m : ℕ} (hm : S.extRank x = m + 1) :
    ∀ e : ShapeExpr, (∀ z ∈ e.extendsTargets, S.extEdge x z) →
      Schema.RankOkAt S (Schema.RankOk S m) e := by
  intro e
  induction e with
  | constraint c => intro _; trivial
  | ofShape h => intro _; trivial
  | «extends» zs h =>
      intro hzs x' hx' u hu
      obtain ⟨z, hzzs, hx'z⟩ := Finset.mem_biUnion.mp hx'
      have hxz : S.extEdge x z := hzs z (by simpa [ShapeExpr.extendsTargets] using hzzs)
      have hrankz : S.extRank z < S.extRank x := Schema.extRank_lt_of_extEdge hAcyclic hx hxz
      have hx'X : x' ∈ S.X := by
        unfold Schema.anc at hx'z
        have := Classical.decPred (Relation.ReflTransGen S.extEdge z)
        simp only [Finset.mem_filter] at hx'z
        exact hx'z.1
      have hrankx' : S.extRank x' ≤ S.extRank z := Schema.extRank_le_of_mem_anc hx'z
      have hrankx'm : S.extRank x' ≤ m := by omega
      have hIHx' : Schema.RankOk S (S.extRank x') (S.shapeDef x') := IH x' hx'X (by omega)
      have hru := Schema.RankOk_restrOf hWFX hx'X hu hIHx'
      exact Schema.RankOk.mono_le hrankx'm u hru
  | or s1 s2 ih1 ih2 =>
      intro hst
      refine ⟨ih1 (fun z hz => hst z ?_), ih2 (fun z hz => hst z ?_)⟩
      · simp only [ShapeExpr.extendsTargets, Finset.mem_union]; exact Or.inl hz
      · simp only [ShapeExpr.extendsTargets, Finset.mem_union]; exact Or.inr hz
  | and s1 s2 ih1 ih2 =>
      intro hst
      refine ⟨ih1 (fun z hz => hst z ?_), ih2 (fun z hz => hst z ?_)⟩
      · simp only [ShapeExpr.extendsTargets, Finset.mem_union]; exact Or.inl hz
      · simp only [ShapeExpr.extendsTargets, Finset.mem_union]; exact Or.inr hz
  | not s ih =>
      intro hst
      exact ih (fun z hz => hst z (by simpa [ShapeExpr.extendsTargets] using hz))

/-- For `x ∈ S.X`, the definition of `x` is `RankOk` at exactly the rank
of `x`. The proof is by strong induction on `extRank x`, with
`RankOkAt_of_edges`. This is the precise form of the termination argument
of Lemma 1. `ExtAcyclic` alone is sufficient. There is no other
restriction on the locations of `extends` nodes. -/
theorem Schema.rankOk_shapeDef {S : Schema} (hAcyclic : S.ExtAcyclic) (hWFX : S.WellFormedX) :
    ∀ x ∈ S.X, Schema.RankOk S (S.extRank x) (S.shapeDef x) := by
  have key : ∀ n x, x ∈ S.X → S.extRank x = n → Schema.RankOk S (S.extRank x) (S.shapeDef x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro x hx hxn
      obtain ⟨m, hm⟩ := Schema.extRank_succ hx
      have hIH : ∀ x' ∈ S.X, S.extRank x' < S.extRank x →
          Schema.RankOk S (S.extRank x') (S.shapeDef x') := by
        intro x' hx' hlt
        exact IH (S.extRank x') (hxn ▸ hlt) x' hx' rfl
      have hedges : ∀ z ∈ (S.shapeDef x).extendsTargets, S.extEdge x z := fun z hz => hz
      have hres := Schema.RankOkAt_of_edges hAcyclic hWFX hx hIH hm (S.shapeDef x) hedges
      rw [hm]
      exact hres
  intro x hx
  exact key (S.extRank x) x hx rfl

/-- Extends `rankOk_shapeDef` from one `x ∈ S.X` to each `ShapeExpr`
(also to `S.shapeDef z` for a simple label `z` that is not in `S.X`). The
global bound `S.X.sup S.extRank + 1` is always sufficient. -/
theorem Schema.rankOk_any {S : Schema} (hAcyclic : S.ExtAcyclic) (hWFX : S.WellFormedX) :
    ∀ e : ShapeExpr, Schema.RankOk S (S.X.sup S.extRank + 1) e := by
  intro e
  induction e with
  | constraint c => trivial
  | ofShape h => trivial
  | «extends» xs h =>
      show Schema.RankOkAt S (Schema.RankOk S (S.X.sup S.extRank)) (.extends xs h)
      intro x' hx' u hu
      have hx'X : x' ∈ S.X := Schema.ancSet_subset_X hx'
      have hrank : S.extRank x' ≤ S.X.sup S.extRank := Finset.le_sup hx'X
      have hok := Schema.rankOk_shapeDef hAcyclic hWFX x' hx'X
      have hru := Schema.RankOk_restrOf hWFX hx'X hu hok
      exact Schema.RankOk.mono_le hrank u hru
  | or s1 s2 ih1 ih2 => exact ⟨ih1, ih2⟩
  | and s1 s2 ih1 ih2 => exact ⟨ih1, ih2⟩
  | not s ih => exact ih

/-- `SatisfiesMFuel` becomes stable at the rank-`r` fuel `reqFuelR S r s`,
if `RankOk S r s` is true. The proof is by induction on `r`:

* Rank 0 is `stableM_noExtends`.
* At each higher rank, the induction hypothesis of rank `r'` gives the
  stability of a restriction. -/
theorem stableMGen (S : Schema) (_hWFX : S.WellFormedX) :
    ∀ r s, Schema.RankOk S r s →
      ∀ fuel1 fuel2, Schema.reqFuelR S r s ≤ fuel1 → Schema.reqFuelR S r s ≤ fuel2 →
        ∀ (G : Graph) (τ : Typing) (M : Finset Triple),
          SatisfiesMFuel fuel1 S G τ M s ↔ SatisfiesMFuel fuel2 S G τ M s := by
  intro r
  induction r with
  | zero =>
      intro s hs fuel1 fuel2 h1 h2 G τ M
      exact stableM_noExtends s hs fuel1 fuel2 h1 h2 S G τ M
  | succ r' ihr =>
      intro s
      induction s with
      | constraint c =>
          intro _ fuel1 fuel2 h1 h2 G τ M
          rcases fuel1 with _ | f1
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1
          rcases fuel2 with _ | f2
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h2
          rfl
      | ofShape h =>
          intro _ fuel1 fuel2 h1 h2 G τ M
          rcases fuel1 with _ | f1
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1
          rcases fuel2 with _ | f2
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h2
          simp only [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1 h2
          show (SatisfiesEFuel f1 S G τ (Me τ M h.triples) h.triples ∧
                props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
                (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)) ↔
              (SatisfiesEFuel f2 S G τ (Me τ M h.triples) h.triples ∧
                props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
                (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅))
          rw [stableE h.triples f1 f2 (by omega) (by omega) S G τ (Me τ M h.triples)]
      | «extends» xs h =>
          intro hRank fuel1 fuel2 h1 h2 G τ M
          rcases fuel1 with _ | f1
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1
          rcases fuel2 with _ | f2
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h2
          simp only [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1 h2
          have hRankAt : ∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
              Schema.RankOk S r' u := hRank
          have hboundE : ∀ x ∈ S.ancSet xs, (S.shapeDef x).extTe.size + 1 ≤ f1 ∧
              (S.shapeDef x).extTe.size + 1 ≤ f2 := by
            intro x hx
            have hle : max ((S.shapeDef x).extTe.size + 1)
                (match (S.shapeDef x).restrOf with
                 | none => 0 | some u => Schema.reqFuelR S r' u) ≤
                  (S.ancSet xs).sup (fun x => max ((S.shapeDef x).extTe.size + 1)
                    (match (S.shapeDef x).restrOf with
                     | none => 0 | some u => Schema.reqFuelR S r' u)) :=
              Finset.le_sup (f := fun x => max ((S.shapeDef x).extTe.size + 1)
                (match (S.shapeDef x).restrOf with
                 | none => 0 | some u => Schema.reqFuelR S r' u)) hx
            omega
          have hboundR : ∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
              Schema.reqFuelR S r' u ≤ f1 ∧ Schema.reqFuelR S r' u ≤ f2 := by
            intro x hx u hu
            have hle : max ((S.shapeDef x).extTe.size + 1) (Schema.reqFuelR S r' u) ≤
                (S.ancSet xs).sup (fun x => max ((S.shapeDef x).extTe.size + 1)
                  (match (S.shapeDef x).restrOf with
                   | none => 0 | some u => Schema.reqFuelR S r' u)) := by
              have := Finset.le_sup (f := fun x => max ((S.shapeDef x).extTe.size + 1)
                (match (S.shapeDef x).restrOf with
                 | none => 0 | some u => Schema.reqFuelR S r' u)) hx
              rw [hu] at this
              exact this
            omega
          show (∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
                SatisfiesMFuel f1 S G τ M' (.ofShape h) ∧
                (∀ x ∈ S.ancSet xs, SatisfiesEFuel f1 S G τ (Mx x) (S.shapeDef x).extTe) ∧
                (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
                  SatisfiesMFuel f1 S G τ ((S.anc x).biUnion Mx) u)) ↔
              (∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
                SatisfiesMFuel f2 S G τ M' (.ofShape h) ∧
                (∀ x ∈ S.ancSet xs, SatisfiesEFuel f2 S G τ (Mx x) (S.shapeDef x).extTe) ∧
                (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
                  SatisfiesMFuel f2 S G τ ((S.anc x).biUnion Mx) u))
          refine exists_congr fun M' => exists_congr fun Mx => and_congr_right fun _ => ?_
          have hofshapesize : (ShapeExpr.ofShape h).size = h.triples.size + 1 := rfl
          have he : SatisfiesMFuel f1 S G τ M' (.ofShape h) ↔ SatisfiesMFuel f2 S G τ M' (.ofShape h) :=
            stableM_noExtends (.ofShape h) trivial f1 f2 (by rw [hofshapesize]; omega)
              (by rw [hofshapesize]; omega) S G τ M'
          have hext : (∀ x ∈ S.ancSet xs, SatisfiesEFuel f1 S G τ (Mx x) (S.shapeDef x).extTe) ↔
              (∀ x ∈ S.ancSet xs, SatisfiesEFuel f2 S G τ (Mx x) (S.shapeDef x).extTe) := by
            refine forall_congr' fun x => forall_congr' fun hx => ?_
            obtain ⟨hb1, hb2⟩ := hboundE x hx
            exact stableE (S.shapeDef x).extTe f1 f2 (by omega) (by omega) S G τ (Mx x)
          have hrestr : (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
                SatisfiesMFuel f1 S G τ ((S.anc x).biUnion Mx) u) ↔
              (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
                SatisfiesMFuel f2 S G τ ((S.anc x).biUnion Mx) u) := by
            refine forall_congr' fun x => forall_congr' fun hx => forall_congr' fun u => ?_
            refine imp_congr_right fun hru => ?_
            obtain ⟨hb1, hb2⟩ := hboundR x hx u hru
            exact ihr u (hRankAt x hx u hru) f1 f2 hb1 hb2 G τ _
          rw [he, hext, hrestr]
      | or s1 s2 ih1 ih2 =>
          intro hRank fuel1 fuel2 h1 h2 G τ M
          rcases fuel1 with _ | f1
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1
          rcases fuel2 with _ | f2
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h2
          have e1 : Schema.reqFuelR S (r' + 1) s1 = ShapeExpr.reqFuelAt S (Schema.reqFuelR S r') s1 := rfl
          have e2 : Schema.reqFuelR S (r' + 1) s2 = ShapeExpr.reqFuelAt S (Schema.reqFuelR S r') s2 := rfl
          simp only [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1 h2
          show SatisfiesMFuel f1 S G τ M s1 ∨ SatisfiesMFuel f1 S G τ M s2 ↔
            SatisfiesMFuel f2 S G τ M s1 ∨ SatisfiesMFuel f2 S G τ M s2
          rw [ih1 hRank.1 f1 f2 (by omega) (by omega) G τ M,
              ih2 hRank.2 f1 f2 (by omega) (by omega) G τ M]
      | and s1 s2 ih1 ih2 =>
          intro hRank fuel1 fuel2 h1 h2 G τ M
          rcases fuel1 with _ | f1
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1
          rcases fuel2 with _ | f2
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h2
          have e1 : Schema.reqFuelR S (r' + 1) s1 = ShapeExpr.reqFuelAt S (Schema.reqFuelR S r') s1 := rfl
          have e2 : Schema.reqFuelR S (r' + 1) s2 = ShapeExpr.reqFuelAt S (Schema.reqFuelR S r') s2 := rfl
          simp only [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1 h2
          show SatisfiesMFuel f1 S G τ M s1 ∧ SatisfiesMFuel f1 S G τ M s2 ↔
            SatisfiesMFuel f2 S G τ M s1 ∧ SatisfiesMFuel f2 S G τ M s2
          rw [ih1 hRank.1 f1 f2 (by omega) (by omega) G τ M,
              ih2 hRank.2 f1 f2 (by omega) (by omega) G τ M]
      | not s ih =>
          intro hRank fuel1 fuel2 h1 h2 G τ M
          rcases fuel1 with _ | f1
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1
          rcases fuel2 with _ | f2
          · simp [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h2
          have e1 : Schema.reqFuelR S (r' + 1) s = ShapeExpr.reqFuelAt S (Schema.reqFuelR S r') s := rfl
          simp only [Schema.reqFuelR, ShapeExpr.reqFuelAt] at h1 h2
          show ¬ SatisfiesMFuel f1 S G τ M s ↔ ¬ SatisfiesMFuel f2 S G τ M s
          rw [ih hRank f1 f2 (by omega) (by omega) G τ M]

/-- The fuel bound that does not depend on rank. It is `reqFuelR` at the
largest rank that the schema can need, `S.X.sup S.extRank + 1`.
`rankOk_any` shows that this rank is always sufficient for each shape. -/
noncomputable def Schema.reqFuelGen (S : Schema) (s : ShapeExpr) : ℕ :=
  Schema.reqFuelR S (S.X.sup S.extRank + 1) s

theorem stableMGenFinal {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic) (s : ShapeExpr) :
    ∀ fuel1 fuel2, Schema.reqFuelGen S s ≤ fuel1 → Schema.reqFuelGen S s ≤ fuel2 →
      ∀ (G : Graph) (τ : Typing) (M : Finset Triple),
        SatisfiesMFuel fuel1 S G τ M s ↔ SatisfiesMFuel fuel2 S G τ M s :=
  stableMGen S hWFX (S.X.sup S.extRank + 1) s (Schema.rankOk_any hAcyclic hWFX s)

/-- `SatisfiesFuel` (Table 2) becomes stable when
`Fuel ≥ reqFuelGen S s + 1`, for a schema that satisfies `WellFormedX` and
`ExtAcyclic`. -/
theorem stableFuel {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic) (s : ShapeExpr) :
    ∀ fuel1 fuel2, Schema.reqFuelGen S s + 1 ≤ fuel1 → Schema.reqFuelGen S s + 1 ≤ fuel2 →
      ∀ (G : Graph) (τ : Typing) (n : RDFNode),
        SatisfiesFuel fuel1 S G τ n s ↔ SatisfiesFuel fuel2 S G τ n s := by
  induction s with
  | constraint c =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      rfl
  | ofShape h =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      show SatisfiesMFuel f1 S G τ (neigh G n) (.ofShape h) ↔
        SatisfiesMFuel f2 S G τ (neigh G n) (.ofShape h)
      exact stableMGenFinal hWFX hAcyclic (.ofShape h) f1 f2 (by omega) (by omega) G τ (neigh G n)
  | «extends» xs h =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      show SatisfiesMFuel f1 S G τ (neigh G n) (.extends xs h) ↔
        SatisfiesMFuel f2 S G τ (neigh G n) (.extends xs h)
      exact stableMGenFinal hWFX hAcyclic (.extends xs h) f1 f2 (by omega) (by omega) G τ (neigh G n)
  | or s1 s2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      have e1 : Schema.reqFuelGen S (.or s1 s2) =
          max (Schema.reqFuelR S (S.X.sup S.extRank + 1) s1)
              (Schema.reqFuelR S (S.X.sup S.extRank + 1) s2) + 1 := rfl
      have ea : Schema.reqFuelGen S s1 = Schema.reqFuelR S (S.X.sup S.extRank + 1) s1 := rfl
      have eb : Schema.reqFuelGen S s2 = Schema.reqFuelR S (S.X.sup S.extRank + 1) s2 := rfl
      rw [e1] at h1 h2
      show SatisfiesFuel f1 S G τ n s1 ∨ SatisfiesFuel f1 S G τ n s2 ↔
        SatisfiesFuel f2 S G τ n s1 ∨ SatisfiesFuel f2 S G τ n s2
      rw [ih1 f1 f2 (by omega) (by omega) G τ n, ih2 f1 f2 (by omega) (by omega) G τ n]
  | and s1 s2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      have e1 : Schema.reqFuelGen S (.and s1 s2) =
          max (Schema.reqFuelR S (S.X.sup S.extRank + 1) s1)
              (Schema.reqFuelR S (S.X.sup S.extRank + 1) s2) + 1 := rfl
      have ea : Schema.reqFuelGen S s1 = Schema.reqFuelR S (S.X.sup S.extRank + 1) s1 := rfl
      have eb : Schema.reqFuelGen S s2 = Schema.reqFuelR S (S.X.sup S.extRank + 1) s2 := rfl
      rw [e1] at h1 h2
      show SatisfiesFuel f1 S G τ n s1 ∧ SatisfiesFuel f1 S G τ n s2 ↔
        SatisfiesFuel f2 S G τ n s1 ∧ SatisfiesFuel f2 S G τ n s2
      rw [ih1 f1 f2 (by omega) (by omega) G τ n, ih2 f1 f2 (by omega) (by omega) G τ n]
  | not s ih =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      have e1 : Schema.reqFuelGen S (.not s) = Schema.reqFuelR S (S.X.sup S.extRank + 1) s + 1 := rfl
      have ea : Schema.reqFuelGen S s = Schema.reqFuelR S (S.X.sup S.extRank + 1) s := rfl
      rw [e1] at h1 h2
      show ¬ SatisfiesFuel f1 S G τ n s ↔ ¬ SatisfiesFuel f2 S G τ n s
      rw [ih f1 f2 (by omega) (by omega) G τ n]

/-! ### Packaging: the real `Satisfies`, and Lemma 1 -/

/-- The real `n, τ ⊨_S def(z)` (with no `Fuel` parameter). It evaluates at
a canonical fuel amount that is concretely sufficient. By `stableFuel`,
the result does not depend on this choice. `lemma1` below records this. -/
noncomputable def Satisfies (S : Schema) (G : Graph) (τ : Typing) (n : RDFNode)
    (s : ShapeExpr) : Prop :=
  SatisfiesFuel (Schema.reqFuelGen S s + 1) S G τ n s

/-- Lemma 1. Let `S` be a schema that satisfies `WellFormedX` and
`ExtAcyclic`. (These are the hypotheses of the paper. There is no
restriction on the locations of `extends` nodes.) Then the evaluation of
`n, τ ⊨_S def(z)` terminates. Each sufficiently large `Fuel` gives the
same answer as `Satisfies` (defined above at one canonical fuel value),
for each node `n`, typing `τ` and label `z ∈ Y ∪ X`. -/
theorem lemma1 {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic)
    (G : Graph) (τ : Typing) (n : RDFNode) (z : Label) (fuel : ℕ)
    (hfuel : Schema.reqFuelGen S (S.shapeDef z) + 1 ≤ fuel) :
    SatisfiesFuel fuel S G τ n (S.shapeDef z) ↔ Satisfies S G τ n (S.shapeDef z) :=
  stableFuel hWFX hAcyclic (S.shapeDef z) fuel (Schema.reqFuelGen S (S.shapeDef z) + 1) hfuel
    (le_refl _) G τ n

end ShexLean.Inheritance
