import ShexLean.Shex2025Inheritance.Stratification
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
Lemma 1 (§4.2) of the 2025 "Shape Expressions with Inheritance" paper:

> Lemma 1. The evaluation of `G, n, τ ⊨_S def(z)` always terminates, for
> every schema `S = (Y, X, def, A)`, graph `G`, node `n` of `G`, typing `τ`
> of `G` by `S`, and label `z ∈ Y ∪ X`.

`Semantics.lean` sidesteps termination by threading an explicit
`Fuel : ℕ` through `SatisfiesFuel`/`SatisfiesMFuel`/`SatisfiesEFuel`,
decremented on every recursive call, returning `False` on exhaustion —
a total Lean function by construction, but not yet the paper's real
(fuel-independent) relation. This file shows that, for a well-defined
schema, a large-enough `Fuel` makes the answer stop depending on `Fuel`:
the fuel-bounded approximation eventually equals the real relation.

Unlike the 2017 formalization, where a shape reference is resolved purely
via `typing` so termination is free structural recursion on the AST, here
Table 3's `extends` rule recurses into other labels' own definitions
(`(S.shapeDef x).extTe`/`.restrOf`, `x` ranging over ancestors) — a schema
lookup, not a subterm of the current expression. The paper's own
termination argument (Lemma 1's proof sketch) is one sentence: the tree of
recursive calls is finite "due to the acyclic nature of the extension
hierarchy". Making this precise needs a rank function on labels witnessing
`H_S`'s acyclicity (`Schema.extRank` below) and a combined measure that
decreases on every recursive call, both `extends`-hops (governed by the
rank) and ordinary AST-structural ones (`Schema.reqFuelR`/
`Schema.reqFuelGen`).

This is proved at the generality the paper's Lemma 1 claims: only
`WellFormedX` (Definition 2) and `ExtAcyclic` (Definition 6) are assumed,
with no restriction on where `extends` nodes occur, including inside a
restriction `u` (`extends X h and u`).
-/

namespace ShexLean.Inheritance

/-! ### Extension-hierarchy acyclicity -/

/-- `S.anc` strictly shrinks along every `H_S` edge, given `S.ExtAcyclic`
(Definition 6's acyclicity clause): if `x` extends `y`, everything `y`
transitively extends is also extended by `x`, but `x ∈ S.anc x` while
`x ∈ S.anc y` would close a cycle through the edge `x → y`. The standard
ancestor-count-as-rank-function argument on a DAG; this is why
`ExtAcyclic` alone gives a well-founded measure. -/
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

/-- `S.extRank x := (S.anc x).card`: a `ℕ`-valued rank witnessing `H_S`'s
acyclicity, strictly decreasing along every edge (`extRank_lt_of_extEdge`
below). The well-founded measure the rest of this file's termination
argument uses. -/
noncomputable def Schema.extRank (S : Schema) (x : Label) : ℕ := (S.anc x).card

/-- The rank form of `anc_ssubset_of_extEdge`: `extRank` strictly decreases
along every `H_S` edge out of a label of `S`. -/
theorem Schema.extRank_lt_of_extEdge {S : Schema} (hAcyclic : S.ExtAcyclic)
    {x y : Label} (hxX : x ∈ S.X) (hxy : S.extEdge x y) :
    S.extRank y < S.extRank x :=
  Finset.card_lt_card (S.anc_ssubset_of_extEdge hAcyclic hxX hxy)

/-- `extRank` does not increase along an ancestor path: `x' ∈ S.anc x`
gives `extRank x' ≤ extRank x` (not strict, since `x ∈ S.anc x`
reflexively). Used to bound the rank of every label reached by a rule-18
partition (`x' ∈ S.ancSet xs`), not just the direct targets `xs`. -/
theorem Schema.extRank_le_of_mem_anc {S : Schema} {x x' : Label} (hx' : x' ∈ S.anc x) :
    S.extRank x' ≤ S.extRank x := by
  apply Finset.card_le_card
  intro z hz
  unfold Schema.anc at hx' hz ⊢
  have := Classical.decPred (Relation.ReflTransGen S.extEdge x)
  have := Classical.decPred (Relation.ReflTransGen S.extEdge x')
  simp only [Finset.mem_filter] at hx' hz ⊢
  exact ⟨hz.1, hx'.2.trans hz.2⟩

/-! ### The base case: `NoExtends` shapes need no schema lookups at all -/

/-- `s` contains no `.extends` node anywhere (not even nested inside
`or`/`and`/`not`). -/
def ShapeExpr.NoExtends : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends _ _ => False
  | .or s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .and s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .not s => s.NoExtends

/-! ### The stabilization argument

Follows the dependency chain of the definitions themselves
(`Semantics.lean`'s module docstring): `SatisfiesEFuel` stabilizes on its
own (no schema lookups); `SatisfiesMFuel` stabilizes using that, plus a
`NoExtends`-only base case; `SatisfiesFuel` stabilizes using
`SatisfiesMFuel`. -/

/-- Structural size of a triple expression: a generous, not tight,
sufficient-fuel bound. Every recursive call `SatisfiesEFuel` makes is on a
strictly smaller sub-expression, so this decreases by at least 1 at every
step. -/
def TripleExpr.size : TripleExpr → ℕ
  | .empty => 1
  | .tc _ _ => 1
  | .choice e1 e2 => e1.size + e2.size + 1
  | .seq e1 e2 => e1.size + e2.size + 1
  | .star e => e.size + 1

/-- `SatisfiesEFuel` stabilizes once `Fuel ≥ e.size`. Table 1 never
performs a schema lookup (`.tc`'s label is resolved via `τ`, see
`Semantics.lean`'s module docstring), so no hypothesis on `S` is needed —
plain structural induction on `e`. -/
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

/-- Structural size of a shape expression (same generous role as
`TripleExpr.size`). -/
def ShapeExpr.size : ShapeExpr → ℕ
  | .constraint _ => 1
  | .ofShape h => h.triples.size + 1
  | .extends _ h => h.triples.size + 1
  | .or s1 s2 => s1.size + s2.size + 1
  | .and s1 s2 => s1.size + s2.size + 1
  | .not s => s.size + 1

/-- `SatisfiesMFuel` stabilizes on any `NoExtends` shape once
`Fuel ≥ s.size`; no schema hypothesis needed, since such a shape never
triggers rule 18. Proved before the general `stableMGen` below because it
is also needed for `restr(x)`, which is not a subterm of the shape the
general induction runs on. -/
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

/-! ### The rank-indexed fuel bound and its sufficiency

`ShapeExpr.reqFuelAt S lower s` computes a fuel bound for `s`, taking an
`.extends` node's ancestors' restrictions as bounded by `lower`.
`Schema.reqFuelR S r` supplies `lower` recursively, indexed by a rank
budget `r`: `reqFuelR S 0 := ShapeExpr.size` (sound at rank 0, where every
reachable shape is `NoExtends`), and `reqFuelR S (r+1) := reqFuelAt S
(reqFuelR S r)`.

`Schema.RankOk S r s` is the side condition that rank `r` actually covers
every extends-target reachable from `s`, built the same way as `reqFuelR`.
`Schema.rankOk_shapeDef` is the acyclicity argument: for `x ∈ S.X`,
`RankOk S (extRank x) (S.shapeDef x)` holds by strong induction on
`extRank x`, since every extends-target reachable from `x`'s definition
has strictly smaller rank (`extRank_lt_of_extEdge`). `Schema.rankOk_any`
lifts this to any `ShapeExpr`, not just some `S.shapeDef x`, at the single
global rank bound `S.X.sup S.extRank + 1`, covering top-level queries
`S.shapeDef z` for a simple label `z` not in `S.X` too. -/

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

/-- Rank-indexed fuel bound: `reqFuelR S r` is `reqFuelAt` iterated `r`
times, starting from plain `ShapeExpr.size` (sound at rank `0`, where every
reachable shape is `NoExtends`). -/
noncomputable def Schema.reqFuelR (S : Schema) : ℕ → ShapeExpr → ℕ
  | 0 => ShapeExpr.size
  | r + 1 => ShapeExpr.reqFuelAt S (Schema.reqFuelR S r)

/-- The rank-`r` analogue of `ShapeExpr.NoExtends`: every `.extends` node's
ancestors' restrictions, unfolded through `r` further cascading `.extends`
hops, are accounted for. `RankOk S 0` coincides with `NoExtends`. -/
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

/-- `RankOk` is monotone: a rank sufficient for `s` remains sufficient at
any higher rank. -/
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

/-- Every `x ∈ S.X` has `extRank x ≥ 1` (reflexively, `x ∈ S.anc x`), so
`extRank x` can always be written as some `m + 1`. -/
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

/-- From `RankOk` of `x`'s own definition (`extends xs h [and u]`), extract
`RankOk` of its restriction `u`. -/
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

/-- Any `ShapeExpr` `e` whose direct `.extends` targets are all genuine
`H_S`-edges out of `x` is `RankOkAt` at rank `m := extRank x - 1`, given
that every `x' ∈ S.X` of strictly smaller rank already has `RankOk` of its
own definition. Applied to `e := S.shapeDef x`, this closes the induction
in `rankOk_shapeDef`; stated for general `e` since `x`'s own restriction
`u` needs the same fact. -/
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

/-- For `x ∈ S.X`, `x`'s own definition is `RankOk` at exactly `x`'s rank,
by strong induction on `extRank x` using `RankOkAt_of_edges`. This is
Lemma 1's termination argument made precise: `ExtAcyclic` alone suffices,
with no further restriction on where `extends` nodes may occur. -/
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

/-- Lifts `rankOk_shapeDef` from a specific `x ∈ S.X` to any `ShapeExpr`
(in particular `S.shapeDef z` for a simple label `z` not in `S.X`): the
global bound `S.X.sup S.extRank + 1` always suffices. -/
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

/-- `SatisfiesMFuel` stabilizes at rank-`r` fuel `reqFuelR S r s`, given
`RankOk S r s`. Proved by induction on `r`: rank 0 is `stableM_noExtends`;
each further rank discharges a restriction's stabilization via the
rank-`r'` induction hypothesis. -/
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

/-- The rank-independent fuel bound: `reqFuelR` at the largest rank the
schema can ever need, `S.X.sup S.extRank + 1`, which `rankOk_any` shows is
always enough for any shape. -/
noncomputable def Schema.reqFuelGen (S : Schema) (s : ShapeExpr) : ℕ :=
  Schema.reqFuelR S (S.X.sup S.extRank + 1) s

theorem stableMGenFinal {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic) (s : ShapeExpr) :
    ∀ fuel1 fuel2, Schema.reqFuelGen S s ≤ fuel1 → Schema.reqFuelGen S s ≤ fuel2 →
      ∀ (G : Graph) (τ : Typing) (M : Finset Triple),
        SatisfiesMFuel fuel1 S G τ M s ↔ SatisfiesMFuel fuel2 S G τ M s :=
  stableMGen S hWFX (S.X.sup S.extRank + 1) s (Schema.rankOk_any hAcyclic hWFX s)

/-- `SatisfiesFuel` (Table 2) stabilizes once `Fuel ≥ reqFuelGen S s + 1`,
for a schema satisfying `WellFormedX`/`ExtAcyclic`. -/
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

/-! ### Packaging: the real `Satisfies`, and Lemma 1 itself -/

/-- The real `n, τ ⊨_S def(z)` (no `Fuel` parameter): evaluate at a
canonical, concretely-sufficient fuel amount. Independent of that choice
by `stableFuel`, recorded as `lemma1` below. -/
noncomputable def Satisfies (S : Schema) (G : Graph) (τ : Typing) (n : RDFNode)
    (s : ShapeExpr) : Prop :=
  SatisfiesFuel (Schema.reqFuelGen S s + 1) S G τ n s

/-- Lemma 1. For a schema `S` satisfying `WellFormedX`/`ExtAcyclic` (the
paper's own hypotheses, with no restriction on where `extends` nodes may
occur), `n, τ ⊨_S def(z)`'s evaluation terminates: any sufficiently large
`Fuel` gives the same answer as `Satisfies` (defined above at one
canonical fuel value), for every node `n`, typing `τ`, and label
`z ∈ Y ∪ X`. -/
theorem lemma1 {S : Schema} (hWFX : S.WellFormedX) (hAcyclic : S.ExtAcyclic)
    (G : Graph) (τ : Typing) (n : RDFNode) (z : Label) (fuel : ℕ)
    (hfuel : Schema.reqFuelGen S (S.shapeDef z) + 1 ≤ fuel) :
    SatisfiesFuel fuel S G τ n (S.shapeDef z) ↔ Satisfies S G τ n (S.shapeDef z) :=
  stableFuel hWFX hAcyclic (S.shapeDef z) fuel (Schema.reqFuelGen S (S.shapeDef z) + 1) hfuel
    (le_refl _) G τ n

end ShexLean.Inheritance
