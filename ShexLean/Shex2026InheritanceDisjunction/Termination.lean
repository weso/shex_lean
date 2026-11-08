import ShexLean.Shex2026InheritanceDisjunction.Stratification
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
Lemma 1 (§4.2) of the 2025 paper "Shape Expressions with Inheritance":

> Lemma 1. The evaluation of `G, n, τ ⊨_S def(z)` always terminates, for
> every schema `S = (Y, X, def, A)`, graph `G`, node `n` of `G`, typing `τ`
> of `G` by `S`, and label `z ∈ Y ∪ X`.

`ShexLean/Shex2026InheritanceDisjunction/Semantics.lean` avoids the
termination problem with an explicit argument `Fuel : ℕ` in
`SatisfiesFuel`, `SatisfiesMFuel` and `SatisfiesEFuel`. *Each* recursive
call decreases `Fuel`, and the result is `False` when no fuel remains.
Thus, the Lean function is total by construction, but it is not yet the
real relation of the paper (which does not depend on fuel).

This file shows that, for a well-defined schema, the result stops
depending on `Fuel` when `Fuel` is sufficiently large. Thus, the
under-approximation bounded by fuel becomes equal to the real relation.

## Why this is more difficult than all that the 2017 formalization needed

In `ShexLean/Shex2017Schemas/Semantics.lean`, `typing` gives the shape of a
reference (with no recursive call into `def(L)`). Thus, termination is a
free structural recursion on the syntax tree. Here, the `extends` rule of
Table 3 does a recursion into the *definitions of other labels*
(`(S.shapeDef x).extTe` and `.restrOf`, for each ancestor `x`). This is a
schema lookup. It is not a subterm of the current expression.

The termination argument of the paper (the proof sketch of Lemma 1, in
the appendix) is exactly one sentence: the tree of recursive calls is
finite "due to the acyclic nature of the extension hierarchy". A Lean
proof of this sentence needs two items:

* A real *rank function* on labels that is a witness of the acyclicity of
  `H_S`.
* A combined measure that decreases on each recursive call. This includes
  the `extends` steps (controlled by the rank) and the ordinary structural
  steps on the syntax tree.

## An extra hypothesis that the text of the paper does not have

Definition 3 makes the edges of `H_S` *only* from the *outermost*
`extends X h [and u]` clause of a label: "`H_S` has an edge from `x` to `x'`
iff `def(x) = extends X h [and u]` and `x' ∈ X`". It does not look into `u`
(`restr(x)`) for `H_S` edges.

But Definition 2 requires only that `u` is *a* plain shape expression. The
grammar lets it contain a nested `extends` node (inside an `or`, `and` or
`not`). When the recursive evaluator gets to *that* nested `extends`, the
acyclicity check of `H_S` does not "see" it, because Definition 3 looks
only at the outermost clause. The one-sentence proof sketch of the paper
does not discuss this case, and no example of the paper uses it.

We do not guess how the paper intends to handle this edge case, and we do
not silently assume that it cannot occur. In its place, this file adds an
explicit extra hypothesis that excludes it: `ShapeExpr.NoExtends` and
`Schema.WellFormedExtends` below. This is the same type of strengthening
that Lean forces as `Schema.Closed` for Proposition 1 of the 2017
formalization (`ShexLean/Shex2017Schemas/Proposition1.lean`). It is a
technical decision, not a shortcut. If somebody compares this file with
the intent of the paper, they must examine this decision.

(Note: `ShexLean/Shex2025Inheritance/Termination.lean` does not need this
extra hypothesis. It proves Lemma 1 with only `WellFormedX` and
`ExtAcyclic`.)
-/

namespace ShexLean.InheritanceDisjunction

/-! ### Extension-hierarchy acyclicity -/

/-- `S.anc` becomes strictly smaller along each edge of `H_S`, for an
acyclic `S`. (`Schema.ExtAcyclic` is the part of the well-definedness
condition of Definition 6 that is related to termination, in
`ShexLean/Shex2026InheritanceDisjunction/Stratification.lean`.)

If `x` extends `y` directly, then `x` extends (transitively) each label
that `y` extends transitively. But `x` shows that the converse is false:
`x ∈ S.anc x` always, and `x ∈ S.anc y`, together with the edge `x → y`,
closes a cycle through `x`. This is the usual method "the number of
descendants or ancestors is a rank function on a DAG". It is the only
reason why `Schema.ExtAcyclic` is sufficient for termination: it changes
"no cycle" into a real well-founded measure. -/
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

/-- `S.extRank x := (S.anc x).card`: a concrete rank in `ℕ` that is a
witness of the acyclicity of `H_S`. It decreases strictly along each edge
(`extRank_lt_of_extEdge` below). The termination argument in the rest of
this file uses this well-founded measure. -/
noncomputable def Schema.extRank (S : Schema) (x : Label) : ℕ := (S.anc x).card

/-- The rank form of `anc_ssubset_of_extEdge`: `extRank` decreases
strictly along each edge of `H_S` that starts at a label of `S`. -/
theorem Schema.extRank_lt_of_extEdge {S : Schema} (hAcyclic : S.ExtAcyclic)
    {x y : Label} (hxX : x ∈ S.X) (hxy : S.extEdge x y) :
    S.extRank y < S.extRank x :=
  Finset.card_lt_card (S.anc_ssubset_of_extEdge hAcyclic hxX hxy)

/-- `extRank` does not increase along an ancestor path. Each `x' ∈ S.anc x`
has `extRank x' ≤ extRank x`. (The inequality is not strict, because
`x ∈ S.anc x` reflexively. This is the case `= x'`.) This bounds the rank
of *each* label that a rule-18 partition reaches (`x' ∈ S.ancSet xs`), not
only the direct targets `xs`. -/
theorem Schema.extRank_le_of_mem_anc {S : Schema} {x x' : Label} (hx' : x' ∈ S.anc x) :
    S.extRank x' ≤ S.extRank x := by
  apply Finset.card_le_card
  intro z hz
  unfold Schema.anc at hx' hz ⊢
  have := Classical.decPred (Relation.ReflTransGen S.extEdge x)
  have := Classical.decPred (Relation.ReflTransGen S.extEdge x')
  simp only [Finset.mem_filter] at hx' hz ⊢
  exact ⟨hz.1, hx'.2.trans hz.2⟩

/-! ### The extra well-formedness hypothesis (refer to the module docstring) -/

/-- `s` contains no `.extends` node at any location (also not nested in
`or`, `and` or `not`). -/
def ShapeExpr.NoExtends : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends _ _ => False
  | .or s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .and s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .not s => s.NoExtends

/-- `s` uses `.extends` only in the two forms that Definition 2 allows for
the *top-level* definition of a label: `extends X h`, or
`extends X h and u` where `u` is `NoExtends`.

This is different from `WellFormedX`, because the check applies to *each*
sub-shape-expression of `s`. Thus, it also covers a top-level query
`S.shapeDef z` made with `or`, `and` or `not` around an `extends`, not
only `X` labels. Refer to the module docstring to know why this is
necessary. -/
def ShapeExpr.WellFormedExtends : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends _ _ => True
  | .or s1 s2 => s1.WellFormedExtends ∧ s2.WellFormedExtends
  | .and (.extends _ _) s2 => s2.NoExtends
  | .and s1 s2 => s1.WellFormedExtends ∧ s2.WellFormedExtends
  | .not s => s.WellFormedExtends

/-- Each label of `S` has a well-formed `extends` structure. This applies
to all labels, not only the labels of `S.X`, because a top-level query is
not necessarily an extendable label. -/
def Schema.WellFormedExtends (S : Schema) : Prop :=
  ∀ ℓ, (S.shapeDef ℓ).WellFormedExtends

/-! ### The stabilization argument

Let `Schema.WellFormedX`
(`ShexLean/Shex2026InheritanceDisjunction/Syntax.lean`) and
`Schema.WellFormedExtends` be true. Then each `.extends` node that the
evaluator unfolds has one of the two shallow forms that Definition 2
allows for the definition of a label:

* `ext-te(x)` (`(S.shapeDef x).extTe`) is always a plain `TripleExpr`. It
  never contains a `ShapeExpr`. Thus, it never causes another schema
  lookup.
* `restr(x)` (`(S.shapeDef x).restrOf`), when it is present, is
  `NoExtends`. It never contains *another* `.extends` node.

Thus, the recursion never needs to follow more than one `extends` step
along a path. After that step, all that remains to evaluate is a
`TripleExpr` or a `NoExtends` `ShapeExpr`. The ordinary syntax-tree size
bounds the two, and no more schema lookups are possible.

This is the reason why the argument below does not need
`Schema.ExtAcyclic` and `Schema.extRank` above. `WellFormedExtends` is
strictly stronger than acyclicity. It does not only forbid a *cycle*
through a nested `extends`. It forbids *all* nested `extends`. Thus, this
file does not reproduce the acyclicity argument of the paper for the
fully general case (where `restr(x)` can use `extends`). Refer to the
module docstring. We keep `extRank` because it is a correct fact that a
future proof of the fully general Lemma 1 (with no `WellFormedExtends`)
can use.

The proof follows the same one-way dependency chain as the definitions
(refer to the docstring of
`ShexLean/Shex2026InheritanceDisjunction/Semantics.lean`):

1. `SatisfiesEFuel` becomes stable alone (it does no schema lookups).
2. `SatisfiesMFuel` becomes stable with step 1. It also uses a version of
   itself for `NoExtends` shapes only, which we prove first, for
   `restr(x)`.
3. `SatisfiesFuel` becomes stable with the result of step 2, for the
   change of judgment in the `.ofShape` and `.extends` cases. -/

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

/-- A large bound on the `.triples.size` of *all* the disjuncts in `hs`
together. This is the `hs : List Shape` version of `h.triples.size` in the
original formalization (with one `Shape`). We use it at each location
where we must bound the size of `extTeAt`, for each disjunct that `pick`
selects. -/
def Shape.listSize (hs : List Shape) : ℕ := (hs.map (fun h => h.triples.size)).sum

theorem Shape.triples_size_le_listSize {hs : List Shape} {h : Shape} (hmem : h ∈ hs) :
    h.triples.size ≤ Shape.listSize hs := by
  unfold Shape.listSize
  induction hs with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hmem with heq | hmem'
      · subst heq; omega
      · have := ih hmem'; omega

/-- `SatisfiesEFuel` becomes stable when `Fuel ≥ e.size`: two sufficiently
large fuel values agree. Table 1 never does a schema lookup. (Only `τ`
gives the label of `.tc`. Refer to the module docstring of
`Semantics.lean`.) Thus, the proof needs no hypothesis on `S`. It is a
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

/-- The structural size of a shape expression. (It has the same role as
`TripleExpr.size`: a large bound.) -/
def ShapeExpr.size : ShapeExpr → ℕ
  | .constraint _ => 1
  | .ofShape h => h.triples.size + 1
  | .extends _ hs => Shape.listSize hs + 1
  | .or s1 s2 => s1.size + s2.size + 1
  | .and s1 s2 => s1.size + s2.size + 1
  | .not s => s.size + 1

/-- `hs.listSize` bounds the `.triples.size` of each element of
`(.extends xs hs).extTeList` (`= hs.map Shape.triples`). -/
theorem TripleExpr.size_le_listSize_of_mem_extends {xs : Finset Label} {hs : List Shape}
    {e : TripleExpr} (hmem : e ∈ (ShapeExpr.extends xs hs).extTeList) : e.size ≤ Shape.listSize hs := by
  unfold ShapeExpr.extTeList at hmem
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hmem
  exact Shape.triples_size_le_listSize hh

/-- The same as `TripleExpr.size_le_listSize_of_mem_extends`, for the form
`.and (.extends xs hs) u` (the form `extends X hs and u` of a well-formed
`X` label). -/
theorem TripleExpr.size_le_listSize_of_mem_and_extends {xs : Finset Label} {hs : List Shape}
    {u : ShapeExpr} {e : TripleExpr} (hmem : e ∈ (ShapeExpr.and (.extends xs hs) u).extTeList) :
    e.size ≤ Shape.listSize hs := by
  unfold ShapeExpr.extTeList at hmem
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hmem
  exact Shape.triples_size_le_listSize hh

/-- For `s` the well-formed definition of an `X` label, `s.size` always
bounds the size of `extTeAt`. `s.size` already includes `hs.listSize` (the
`.extends` case of `ShapeExpr.size` above), for each disjunct that `pick`
selects. -/
theorem extTeAt_size_le {S : Schema} (hWFX : S.WellFormedX) {x : Label} (hx : x ∈ S.X)
    (i : ℕ) : ((S.shapeDef x).extTeAt i).size ≤ (S.shapeDef x).size := by
  obtain ⟨xs', hs', -, hcase⟩ := hWFX x hx
  rcases ShapeExpr.extTeAt_mem_or_empty (S.shapeDef x) i with hempty | ⟨e, hmem, heq⟩
  · rw [hempty]
    simp only [TripleExpr.size]
    rcases hcase with heq' | ⟨u, heq'⟩ <;> rw [heq'] <;> simp only [ShapeExpr.size] <;> omega
  · rw [heq]
    rcases hcase with heq' | ⟨u, heq'⟩ <;> rw [heq'] at hmem ⊢ <;> simp only [ShapeExpr.size]
    · exact le_trans (TripleExpr.size_le_listSize_of_mem_extends hmem) (by omega)
    · exact le_trans (TripleExpr.size_le_listSize_of_mem_and_extends hmem) (by omega)

/-- The largest `.size` of the definitions of the extendable labels of
`S`. This is a fixed bound for the full schema. It bounds the fuel that
`ext-te(x)` and `restr(x)` can need, for *each* `x ∈ S.X` that a rule-18
partition can reach. -/
noncomputable def Schema.maxDefSize (S : Schema) : ℕ := S.X.sup (fun x => (S.shapeDef x).size)

/-- `SatisfiesMFuel` becomes stable on each `NoExtends` shape when
`Fuel ≥ s.size`. It needs no hypothesis on the schema, because a
`NoExtends` shape never uses rule 18 (no schema lookup is possible). It
uses only `stableE`.

We prove it *before* the general `stableM` below. The reason is that, in
the general `.extends` case, the evaluation of `restr(x)` needs exactly
this fact, applied to a shape (`restr(x)`) that is *not* a subterm of the
shape of the general induction. -/
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

/-- When `restr(x)` is present, it is `NoExtends` (Definition 2, and the
extra hypothesis `Schema.WellFormedExtends`). It is also strictly smaller
than `def(x)`, for the same reason that `extTeAt_size_le` bounds
`ext-te(x)`. -/
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

/-- Sufficient fuel for the evaluation of `SatisfiesMFuel` and
`SatisfiesFuel` on `s` to become stable. The only case that is not plain
syntax-tree size is `.extends`. It also needs sufficient fuel to cover the
`ext-te` and `restr` of *each* ancestor (`Schema.maxDefSize`), not only
the size of `s`.

The bound of `M'` uses `(.ofShape h).size = h.triples.size + 1`, not only
`h.triples.size`. Now, the check of `M'` is against `.ofShape h` (rule 17
of Table 3, one recursive step of `SatisfiesMFuel`), not directly against
`h.triples` (Table 1). Thus, it costs one more fuel level than a direct
`SatisfiesEFuel` call at the same fuel. Refer to the module docstring. -/
noncomputable def ShapeExpr.reqFuel (S : Schema) : ShapeExpr → ℕ
  | .constraint _ => 1
  | .ofShape h => h.triples.size + 1
  | .extends _ hs => max (Shape.listSize hs + 1) S.maxDefSize + 1
  | .or s1 s2 => max (ShapeExpr.reqFuel S s1) (ShapeExpr.reqFuel S s2) + 1
  | .and s1 s2 => max (ShapeExpr.reqFuel S s1) (ShapeExpr.reqFuel S s2) + 1
  | .not s => ShapeExpr.reqFuel S s + 1

/-- `SatisfiesMFuel` becomes stable on each `s` when
`Fuel ≥ reqFuel S s`, for a schema `S` that satisfies `WellFormedX` and
`WellFormedExtends`. Only the `.extends` case needs these hypotheses (and
`extTe_size_le` and `restrOf_noExtends_and_size_le` above). Each other
case is exactly the proof of `stableM_noExtends`, with `reqFuel` in place
of `size`. -/
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
  | «extends» xs hs =>
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
      show (∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
            (∃ h ∈ hs, SatisfiesMFuel f1 S G τ M' (.ofShape h)) ∧
            (∀ x ∈ S.ancSet xs, SatisfiesEFuel f1 S G τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ∧
            (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
              SatisfiesMFuel f1 S G τ ((S.anc x).biUnion Mx) u)) ↔
          (∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
            (∃ h ∈ hs, SatisfiesMFuel f2 S G τ M' (.ofShape h)) ∧
            (∀ x ∈ S.ancSet xs, SatisfiesEFuel f2 S G τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ∧
            (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
              SatisfiesMFuel f2 S G τ ((S.anc x).biUnion Mx) u))
      refine exists_congr fun M' => exists_congr fun Mx => exists_congr fun pick =>
        and_congr_right fun _ => ?_
      have he : (∃ h ∈ hs, SatisfiesMFuel f1 S G τ M' (.ofShape h)) ↔
          (∃ h ∈ hs, SatisfiesMFuel f2 S G τ M' (.ofShape h)) := by
        refine exists_congr fun h => and_congr_right fun hmem => ?_
        have hhle : h.triples.size ≤ Shape.listSize hs := Shape.triples_size_le_listSize hmem
        have hofshapesize : (ShapeExpr.ofShape h).size = h.triples.size + 1 := rfl
        exact stableM_noExtends (.ofShape h) trivial f1 f2 (by rw [hofshapesize]; omega)
          (by rw [hofshapesize]; omega) S G τ M'
      have hext : (∀ x ∈ S.ancSet xs, SatisfiesEFuel f1 S G τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ↔
          (∀ x ∈ S.ancSet xs, SatisfiesEFuel f2 S G τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) := by
        refine forall_congr' fun x => forall_congr' fun hx => ?_
        have hle := extTeAt_size_le hWFX (hancX x hx) (pick x)
        exact stableE ((S.shapeDef x).extTeAt (pick x)) f1 f2
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

/-- `SatisfiesFuel` (Table 2) becomes stable when
`Fuel ≥ reqFuel S s + 1`. This is one more than `SatisfiesMFuel` needs for
the same `s`, to cover the extra change of judgment from Table 2 to
Table 3. The `.ofShape` and `.extends` cases follow directly from
`stableM`. Each other case is self-recursion. -/
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
  | «extends» xs hs =>
      intro fuel1 fuel2 h1 h2 G τ n
      rcases fuel1 with _ | f1
      · omega
      rcases fuel2 with _ | f2
      · omega
      show SatisfiesMFuel f1 S G τ (neigh G n) (.extends xs hs) ↔
        SatisfiesMFuel f2 S G τ (neigh G n) (.extends xs hs)
      exact stableM hWFX hWFExt (.extends xs hs) f1 f2 (by omega) (by omega) G τ (neigh G n)
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

/-! ### Packaging: the real `Satisfies`, and Lemma 1 -/

/-- The real `n, τ ⊨_S def(z)` (with no `Fuel`). It evaluates at a
canonical fuel amount that is concretely sufficient. By `stableFuel`, the
result does not depend on this choice. `lemma1` below records this. -/
noncomputable def Satisfies (S : Schema) (G : Graph) (τ : Typing) (n : RDFNode)
    (s : ShapeExpr) : Prop :=
  SatisfiesFuel (ShapeExpr.reqFuel S s + 1) S G τ n s

/-- The real `M, τ ⊨_S s` (Table 3, with no `Fuel`). -/
noncomputable def SatisfiesM (S : Schema) (G : Graph) (τ : Typing) (M : Finset Triple)
    (s : ShapeExpr) : Prop :=
  SatisfiesMFuel (ShapeExpr.reqFuel S s) S G τ M s

/-- The real `M, τ ⊨_S e` (Table 1, with no `Fuel`). -/
noncomputable def SatisfiesE (S : Schema) (G : Graph) (τ : Typing) (M : Finset Triple)
    (e : TripleExpr) : Prop :=
  SatisfiesEFuel e.size S G τ M e

/-- **Lemma 1.** Let `S` be a schema that satisfies `WellFormedX` and
`WellFormedExtends`. Then the evaluation of `n, τ ⊨_S def(z)` "always
terminates". Each sufficiently large `Fuel` computes the same answer,
which does not depend on `Fuel`. This answer is the result of `Satisfies`
(defined above at one canonical `Fuel`). Thus, the relations of
`Semantics.lean` that are bounded by `Fuel` converge to a well-defined
limit, for each node `n`, typing `τ` and label `z ∈ Y ∪ X`
(`def(z) := S.shapeDef z`, any `ShapeExpr`). -/
theorem lemma1 {S : Schema} (hWFX : S.WellFormedX) (hWFExt : S.WellFormedExtends)
    (G : Graph) (τ : Typing) (n : RDFNode) (z : Label) (fuel : ℕ)
    (hfuel : ShapeExpr.reqFuel S (S.shapeDef z) + 1 ≤ fuel) :
    SatisfiesFuel fuel S G τ n (S.shapeDef z) ↔ Satisfies S G τ n (S.shapeDef z) :=
  stableFuel hWFX hWFExt (S.shapeDef z) fuel (ShapeExpr.reqFuel S (S.shapeDef z) + 1) hfuel
    (le_refl _) G τ n

end ShexLean.InheritanceDisjunction
