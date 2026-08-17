import ShexLean.Shex2025Inheritance.Stratification
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
Lemma 1 (§4.2) of the 2025 "Shape Expressions with Inheritance" paper:

> Lemma 1. The evaluation of `G, n, τ ⊨_S def(z)` always terminates, for
> every schema `S = (Y, X, def, A)`, graph `G`, node `n` of `G`, typing `τ`
> of `G` by `S`, and label `z ∈ Y ∪ X`.

`ShexLean/Shex2025Inheritance/Semantics.lean` sidesteps termination by threading an
explicit `Fuel : ℕ` through `SatisfiesFuel`/`SatisfiesMFuel`/
`SatisfiesEFuel`, decremented on *every* recursive call, returning `False`
on exhaustion — a total Lean function by construction, but not yet the
paper's real (fuel-independent) relation. This file's job is to show that,
for a well-defined schema, a large-enough `Fuel` makes the answer stop
depending on `Fuel` at all — i.e. that the fuel-bounded under-approximation
*is*, eventually, the real thing.

## Why this is genuinely harder than anything the 2017 formalization needed

In `ShexLean/Shex2017Schemas/Semantics.lean`, a shape reference is resolved purely by
consulting `typing` (no recursive call into `def(L)`), so termination is
free structural recursion on the AST. Here, Table 3's `extends` rule
recurses into *other labels' own definitions*
(`(S.shapeDef x).extTe`/`.restrOf`, `x` ranging over ancestors) — a schema
lookup, not a subterm of the current expression. The paper's own
termination argument (Lemma 1's proof sketch, appendix) is exactly one
sentence: the tree of recursive calls is finite "due to the acyclic nature
of the extension hierarchy". Turning that sentence into a Lean proof needs
an actual *rank function* on labels witnessing `H_S`'s acyclicity, and a
combined measure that decreases on every recursive call (both the
`extends`-hop ones — governed by the rank — and the ordinary
AST-structural ones).

## An extra hypothesis beyond the paper's literal text

Definition 3 builds `H_S`'s edges *only* from a label's own *outermost*
`extends X h [and u]` clause: "`H_S` has an edge from `x` to `x'` iff
`def(x) = extends X h [and u]` and `x' ∈ X`" — nothing about `u`
(`restr(x)`) is scanned for `H_S`-edge purposes. But `u` is only
constrained by Definition 2 to be *some* plain shape expression, which the
grammar allows to itself contain a further `extends` node (nested inside
an `or`/`and`/`not`) — and *that* nested `extends`, when the recursive
evaluator actually reaches it, is not "seen" by `H_S`'s acyclicity check at
all, since Definition 3 only ever looks at the outermost clause. Nothing
in the paper's one-sentence proof sketch addresses this case, and it isn't
exercised by any of the paper's own examples. Rather than guess at (or
silently assume away) how the paper intends this edge case to be handled,
this file adds an explicit, documented extra hypothesis ruling it out —
`ShapeExpr.NoExtends`/`Schema.WellFormedExtends` below — exactly the same
kind of Lean-forced strengthening as `Schema.Closed` was for the 2017
formalization's Proposition 1 (`ShexLean/Shex2017Schemas/Proposition1.lean`): a genuine
technical judgment call, not a shortcut, and worth flagging explicitly if
this file is ever checked against the paper's intent more closely.
-/

namespace ShexLean.Inheritance

/-! ### Extension-hierarchy acyclicity -/

/-- `S.anc` strictly shrinks along every `H_S` edge, for an acyclic `S`
(`Schema.ExtAcyclic`, the termination-relevant half of Definition 6's
well-definedness condition, `ShexLean/Shex2025Inheritance/Stratification.lean`):
if `x` (directly) extends `y`, then everything `y` (transitively) extends
is also something `x` (transitively) extends, but `x` itself witnesses the
converse failing (`x ∈ S.anc x` always; `x ∈ S.anc y` would — combined
with the edge `x → y` — close a cycle through `x`). This is the standard
"descendant/ancestor count as a rank function on a DAG" trick, and is the
whole reason `Schema.ExtAcyclic` is enough to guarantee termination: it
turns "no cycle" into a genuine well-founded measure. -/
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

/-- `S.extRank x := (S.anc x).card`: a concrete `ℕ`-valued rank witnessing
`H_S`'s acyclicity, strictly decreasing along every edge
(`extRank_lt_of_extEdge` below) — the well-founded measure the rest of
this file's termination argument is built on. -/
noncomputable def Schema.extRank (S : Schema) (x : Label) : ℕ := (S.anc x).card

/-- The rank form of `anc_ssubset_of_extEdge`: `extRank` strictly decreases
along every `H_S` edge out of a label of `S`. -/
theorem Schema.extRank_lt_of_extEdge {S : Schema} (hAcyclic : S.ExtAcyclic)
    {x y : Label} (hxX : x ∈ S.X) (hxy : S.extEdge x y) :
    S.extRank y < S.extRank x :=
  Finset.card_lt_card (S.anc_ssubset_of_extEdge hAcyclic hxX hxy)

/-- `extRank` doesn't increase along an ancestor path: every `x' ∈ S.anc x`
has `extRank x' ≤ extRank x` (not strict — `x ∈ S.anc x` reflexively, the
`= x'` case). Used to bound the rank of *every* label reached by a rule-18
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

/-! ### The extra well-formedness hypothesis (see the module docstring) -/

/-- `s` contains no `.extends` node anywhere (not even nested inside
`or`/`and`/`not`). -/
def ShapeExpr.NoExtends : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends _ _ => False
  | .or s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .and s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .not s => s.NoExtends

/-- `s` only ever uses `.extends` in the two forms Definition 2 actually
allows a label's *own* top-level definition to take (`extends X h` or
`extends X h and u`, `u` itself `NoExtends`) — but, unlike `WellFormedX`,
checked *everywhere* `s` structurally contains a sub-shape-expression (so
that a top-level query `S.shapeDef z` built from `or`/`and`/`not` around
an `extends` is covered too, not just `X`-labels). See the module
docstring for why this is needed at all. -/
def ShapeExpr.WellFormedExtends : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends _ _ => True
  | .or s1 s2 => s1.WellFormedExtends ∧ s2.WellFormedExtends
  | .and (.extends _ _) s2 => s2.NoExtends
  | .and s1 s2 => s1.WellFormedExtends ∧ s2.WellFormedExtends
  | .not s => s.WellFormedExtends

/-- Every label of `S` (not just `S.X`'s labels, since a top-level query
need not itself be an extendable label) has a well-formed `extends`
structure. -/
def Schema.WellFormedExtends (S : Schema) : Prop :=
  ∀ ℓ, (S.shapeDef ℓ).WellFormedExtends

/-! ### The stabilization argument

Given `Schema.WellFormedX` (`ShexLean/Shex2025Inheritance/Syntax.lean`) and
`Schema.WellFormedExtends`, every `.extends` node the evaluator ever
actually unfolds is, by construction, in one of the two shallow forms
Definition 2 allows a label's *own* definition to take — `ext-te(x)`
(`(S.shapeDef x).extTe`) is always a bare `TripleExpr` (never itself
containing a `ShapeExpr`, hence never a further schema lookup at all), and
`restr(x)` (`(S.shapeDef x).restrOf`), when present, is `NoExtends` (never
containing *another* `.extends` node). So the recursion never needs to
"chase" more than one `extends`-hop along any single path: past that one
hop, everything left to evaluate is either a `TripleExpr` or a
`NoExtends` `ShapeExpr`, both bounded by ordinary AST size with no further
schema lookups possible. This is *why* `Schema.ExtAcyclic`/`Schema.extRank`
above end up not being needed by the argument below — `WellFormedExtends`
is strictly stronger than acyclicity (it doesn't just forbid a *cycle*
through a nested `extends`, it forbids *any* nested `extends` at all), so
the paper's own acyclicity-based argument for the fully general case (where
`restr(x)` may itself use `extends`) is not what's reproduced here; see the
module docstring. `extRank` is kept as a correct, reusable fact for a future
attempt at the fully general Lemma 1 that drops `WellFormedExtends`.

The proof follows the same one-way dependency chain as the definitions
themselves (`ShexLean/Shex2025Inheritance/Semantics.lean`'s own docstring):
`SatisfiesEFuel` stabilizes on its own (no schema lookups at all); then
`SatisfiesMFuel` stabilizes using that fact (plus a `NoExtends`-only
version of itself, proved first, for `restr(x)`); then `SatisfiesFuel`
stabilizes using `SatisfiesMFuel`'s result for the `.ofShape`/`.extends`
same-shape judgment switch. -/

/-- Structural size of a triple expression — a generous (not tight)
sufficient-fuel bound: every recursive call `SatisfiesEFuel` makes is on a
strictly smaller sub-expression, so this decreases by at least 1 at every
step. -/
def TripleExpr.size : TripleExpr → ℕ
  | .empty => 1
  | .tc _ _ => 1
  | .choice e1 e2 => e1.size + e2.size + 1
  | .seq e1 e2 => e1.size + e2.size + 1
  | .star e => e.size + 1

/-- `SatisfiesEFuel` stabilizes once `Fuel ≥ e.size`: any two sufficiently
large fuel values agree. Table 1 never performs a schema lookup at all
(`.tc`'s label is resolved purely via `τ`, see `Semantics.lean`'s module
docstring), so this needs no hypothesis on `S` whatsoever — plain
structural induction on `e`. -/
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

/-- The largest `.size` of any of `S`'s own extendable labels' definitions
— a fixed, schema-wide bound on how much fuel `ext-te(x)`/`restr(x)` can
ever need, for *any* `x ∈ S.X` a rule-18 partition might reach. -/
noncomputable def Schema.maxDefSize (S : Schema) : ℕ := S.X.sup (fun x => (S.shapeDef x).size)

/-- `SatisfiesMFuel` stabilizes on any `NoExtends` shape once
`Fuel ≥ s.size` — no schema hypothesis needed, since a `NoExtends` shape
never triggers rule 18 (no schema lookup possible), only `stableE`. Proved
*before* the general `stableM` below because `restr(x)`'s evaluation
inside the general `.extends` case needs exactly this fact applied to a
shape (`restr(x)`) that is *not* a subterm of the shape the general
induction is on. -/
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

/-- `ext-te(x)` is always strictly smaller than `def(x)` itself (it's a
sub-part of it, per Definition 2's "`def(x) = extends X h [and u]`") — so
`Schema.maxDefSize` bounds it too. -/
theorem extTe_size_le {S : Schema} (hWFX : S.WellFormedX) {x : Label} (hx : x ∈ S.X) :
    (S.shapeDef x).extTe.size ≤ (S.shapeDef x).size := by
  obtain ⟨xs', h', hcase⟩ := hWFX x hx
  rcases hcase with heq | ⟨u, heq⟩ <;> rw [heq] <;>
    simp only [ShapeExpr.extTe, ShapeExpr.size] <;> omega

/-- `restr(x)`, whenever present, is `NoExtends` (Definition 2 + the extra
`Schema.WellFormedExtends` hypothesis) and strictly smaller than `def(x)`
itself, for the same reason as `extTe_size_le`. -/
theorem restrOf_noExtends_and_size_le {S : Schema} (hWFExt : S.WellFormedExtends)
    {x : Label} {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u) :
    u.NoExtends ∧ u.size ≤ (S.shapeDef x).size := by
  have hWFx := hWFExt x
  generalize hg : S.shapeDef x = e at hu hWFx
  cases e with
  | and s1 s2 =>
      cases s1 with
      | «extends» xs' h' =>
          simp only [ShapeExpr.restrOf] at hu
          simp only [ShapeExpr.WellFormedExtends] at hWFx
          have hequ := Option.some.inj hu
          subst hequ
          exact ⟨hWFx, by simp only [ShapeExpr.size]; omega⟩
      | _ => simp [ShapeExpr.restrOf] at hu
  | _ => simp [ShapeExpr.restrOf] at hu

/-- Sufficient fuel for `s`'s `SatisfiesMFuel`/`SatisfiesFuel` evaluation
to have stabilized. The only case that isn't just structural AST size is
`.extends`, which additionally needs enough fuel to cover *any* ancestor's
own `ext-te`/`restr` (`Schema.maxDefSize`), not just `s`'s own size. `M'`'s
own bound uses `(.ofShape h).size = h.triples.size + 1`, not bare
`h.triples.size`: since `M'` is now checked against `.ofShape h` (Table 3
rule 17, one recursive `SatisfiesMFuel` step) rather than directly against
`h.triples` (Table 1), it costs one extra fuel level compared to a direct
`SatisfiesEFuel` call at the same fuel — see the module docstring. -/
noncomputable def ShapeExpr.reqFuel (S : Schema) : ShapeExpr → ℕ
  | .constraint _ => 1
  | .ofShape h => h.triples.size + 1
  | .extends _ h => max (h.triples.size + 1) S.maxDefSize + 1
  | .or s1 s2 => max (ShapeExpr.reqFuel S s1) (ShapeExpr.reqFuel S s2) + 1
  | .and s1 s2 => max (ShapeExpr.reqFuel S s1) (ShapeExpr.reqFuel S s2) + 1
  | .not s => ShapeExpr.reqFuel S s + 1

/-- `SatisfiesMFuel` stabilizes on any `s` once `Fuel ≥ reqFuel S s`, for a
schema `S` satisfying `WellFormedX`/`WellFormedExtends`. The `.extends`
case is the only one that needs those hypotheses (and `extTe_size_le`/
`restrOf_noExtends_and_size_le` above); every other case is exactly
`stableM_noExtends`'s proof, just with `reqFuel` in place of `size`. -/
theorem stableM {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (s : ShapeExpr) :
    ∀ fuel1 fuel2, ShapeExpr.reqFuel S s ≤ fuel1 → ShapeExpr.reqFuel S s ≤ fuel2 →
      ∀ (G : Graph) (τ : Typing) (M : Finset Triple),
        SatisfiesMFuel fuel1 S G τ M s ↔ SatisfiesMFuel fuel2 S G τ M s := by
  induction s with
  | constraint c =>
      intro fuel1 fuel2 h1 h2 G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.reqFuel] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.reqFuel] at h2
      rfl
  | ofShape h =>
      intro fuel1 fuel2 h1 h2 G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.reqFuel] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.reqFuel] at h2
      simp only [ShapeExpr.reqFuel] at h1 h2
      show (SatisfiesEFuel f1 S G τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)) ↔
          (SatisfiesEFuel f2 S G τ (Me τ M h.triples) h.triples ∧
            props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
            (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅))
      rw [stableE h.triples f1 f2 (by omega) (by omega) S G τ (Me τ M h.triples)]
  | «extends» xs h =>
      intro fuel1 fuel2 h1 h2 G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.reqFuel] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.reqFuel] at h2
      simp only [ShapeExpr.reqFuel] at h1 h2
      have hancX : ∀ x ∈ S.ancSet xs, x ∈ S.X := by
        intro x hx
        unfold Schema.ancSet at hx
        obtain ⟨y, _, hyx⟩ := Finset.mem_biUnion.mp hx
        unfold Schema.anc at hyx
        simp only [Finset.mem_filter] at hyx
        exact hyx.1
      have hboundDef : ∀ x ∈ S.ancSet xs, (S.shapeDef x).size ≤ S.maxDefSize := by
        intro x hx
        unfold Schema.maxDefSize
        exact Finset.le_sup (f := fun x => (S.shapeDef x).size) (hancX x hx)
      have hbound1 : ∀ x ∈ S.ancSet xs, (S.shapeDef x).size ≤ f1 := by
        intro x hx; have := hboundDef x hx; omega
      have hbound2 : ∀ x ∈ S.ancSet xs, (S.shapeDef x).size ≤ f2 := by
        intro x hx; have := hboundDef x hx; omega
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
        have hle := extTe_size_le hWFX (hancX x hx)
        exact stableE (S.shapeDef x).extTe f1 f2
          (by have := hbound1 x hx; omega) (by have := hbound2 x hx; omega) S G τ (Mx x)
      have hrestr : (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
            SatisfiesMFuel f1 S G τ ((S.anc x).biUnion Mx) u) ↔
          (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
            SatisfiesMFuel f2 S G τ ((S.anc x).biUnion Mx) u) := by
        refine forall_congr' fun x => forall_congr' fun hx => forall_congr' fun u => ?_
        refine imp_congr_right fun hru => ?_
        obtain ⟨hNoExt, hSizeLe⟩ := restrOf_noExtends_and_size_le hWFExt hru
        exact stableM_noExtends u hNoExt f1 f2
          (by have := hbound1 x hx; omega) (by have := hbound2 x hx; omega) S G τ _
      rw [he, hext, hrestr]
  | or s1 s2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.reqFuel] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.reqFuel] at h2
      simp only [ShapeExpr.reqFuel] at h1 h2
      show SatisfiesMFuel f1 S G τ M s1 ∨ SatisfiesMFuel f1 S G τ M s2 ↔
        SatisfiesMFuel f2 S G τ M s1 ∨ SatisfiesMFuel f2 S G τ M s2
      rw [ih1 f1 f2 (by omega) (by omega) G τ M, ih2 f1 f2 (by omega) (by omega) G τ M]
  | and s1 s2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.reqFuel] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.reqFuel] at h2
      simp only [ShapeExpr.reqFuel] at h1 h2
      show SatisfiesMFuel f1 S G τ M s1 ∧ SatisfiesMFuel f1 S G τ M s2 ↔
        SatisfiesMFuel f2 S G τ M s1 ∧ SatisfiesMFuel f2 S G τ M s2
      rw [ih1 f1 f2 (by omega) (by omega) G τ M, ih2 f1 f2 (by omega) (by omega) G τ M]
  | not s ih =>
      intro fuel1 fuel2 h1 h2 G τ M
      rcases fuel1 with _ | f1
      · simp [ShapeExpr.reqFuel] at h1
      rcases fuel2 with _ | f2
      · simp [ShapeExpr.reqFuel] at h2
      simp only [ShapeExpr.reqFuel] at h1 h2
      show ¬ SatisfiesMFuel f1 S G τ M s ↔ ¬ SatisfiesMFuel f2 S G τ M s
      rw [ih f1 f2 (by omega) (by omega) G τ M]

/-- `SatisfiesFuel` (Table 2) stabilizes once `Fuel ≥ reqFuel S s + 1` (one
more than `SatisfiesMFuel` needs for the very same `s`, to cover the extra
Table-2-to-Table-3 judgment switch). The `.ofShape`/`.extends` cases are
immediate from `stableM`; every other case is self-recursion. -/
theorem stableFuel {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (s : ShapeExpr) :
    ∀ fuel1 fuel2, ShapeExpr.reqFuel S s + 1 ≤ fuel1 → ShapeExpr.reqFuel S s + 1 ≤ fuel2 →
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
      exact stableM hWFX hWFExt (.ofShape h) f1 f2 (by omega) (by omega) G τ (neigh G n)
  | «extends» xs h =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      show SatisfiesMFuel f1 S G τ (neigh G n) (.extends xs h) ↔
        SatisfiesMFuel f2 S G τ (neigh G n) (.extends xs h)
      exact stableM hWFX hWFExt (.extends xs h) f1 f2 (by omega) (by omega) G τ (neigh G n)
  | or s1 s2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      simp only [ShapeExpr.reqFuel] at h1 h2
      show SatisfiesFuel f1 S G τ n s1 ∨ SatisfiesFuel f1 S G τ n s2 ↔
        SatisfiesFuel f2 S G τ n s1 ∨ SatisfiesFuel f2 S G τ n s2
      rw [ih1 f1 f2 (by omega) (by omega) G τ n, ih2 f1 f2 (by omega) (by omega) G τ n]
  | and s1 s2 ih1 ih2 =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      simp only [ShapeExpr.reqFuel] at h1 h2
      show SatisfiesFuel f1 S G τ n s1 ∧ SatisfiesFuel f1 S G τ n s2 ↔
        SatisfiesFuel f2 S G τ n s1 ∧ SatisfiesFuel f2 S G τ n s2
      rw [ih1 f1 f2 (by omega) (by omega) G τ n, ih2 f1 f2 (by omega) (by omega) G τ n]
  | not s ih =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      simp only [ShapeExpr.reqFuel] at h1 h2
      show ¬ SatisfiesFuel f1 S G τ n s ↔ ¬ SatisfiesFuel f2 S G τ n s
      rw [ih f1 f2 (by omega) (by omega) G τ n]

/-! ### Packaging: the real `Satisfies`, and Lemma 1 itself -/

/-- The real `n, τ ⊨_S def(z)` (no `Fuel` in sight): evaluate at a
canonical, concretely-sufficient fuel amount. Well-defined (independent of
this particular choice) by `stableFuel`, recorded as `lemma1` below. -/
noncomputable def Satisfies (S : Schema) (G : Graph) (τ : Typing) (n : RDFNode)
    (s : ShapeExpr) : Prop :=
  SatisfiesFuel (ShapeExpr.reqFuel S s + 1) S G τ n s

/-- The real `M, τ ⊨_S s` (Table 3, no `Fuel`). -/
noncomputable def SatisfiesM (S : Schema) (G : Graph) (τ : Typing) (M : Finset Triple)
    (s : ShapeExpr) : Prop :=
  SatisfiesMFuel (ShapeExpr.reqFuel S s) S G τ M s

/-- The real `M, τ ⊨_S e` (Table 1, no `Fuel`). -/
noncomputable def SatisfiesE (S : Schema) (G : Graph) (τ : Typing) (M : Finset Triple)
    (e : TripleExpr) : Prop :=
  SatisfiesEFuel e.size S G τ M e

/-- **Lemma 1.** For a schema `S` satisfying `WellFormedX`/
`WellFormedExtends`, `n, τ ⊨_S def(z)`'s evaluation "always terminates": any
sufficiently large `Fuel` computes the same, `Fuel`-independent answer that
`Satisfies` (defined above at one canonical such `Fuel`) gives — i.e. the
`Fuel`-bounded relations of `Semantics.lean` really do converge to a
well-defined limit, for every node `n`, typing `τ`, and label
`z ∈ Y ∪ X` (`def(z) := S.shapeDef z`, any `ShapeExpr`). -/
theorem lemma1 {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (G : Graph) (τ : Typing) (n : RDFNode) (z : Label) (fuel : ℕ)
    (hfuel : ShapeExpr.reqFuel S (S.shapeDef z) + 1 ≤ fuel) :
    SatisfiesFuel fuel S G τ n (S.shapeDef z) ↔ Satisfies S G τ n (S.shapeDef z) :=
  stableFuel hWFX hWFExt (S.shapeDef z) fuel (ShapeExpr.reqFuel S (S.shapeDef z) + 1) hfuel
    (le_refl _) G τ n

end ShexLean.Inheritance
