import ShexLean.Shex2025Inheritance.Semantics
import Mathlib.Logic.Relation

/-!
Definitions 5 and 6 (§4.2) of the 2025 "Shape Expressions with
Inheritance" paper — the dependency graph `D_S` and well-defined schemas
("stratified negation").

> For every shape expression or triple expression `s`, let `sub-expr(s)`
> be the set of its sub-expressions, viewed as syntactic objects.
> Additionally, `neg-sub-expr(s)` is the set of sub-expressions of `s`
> that appear in `s` under an odd number of occurrences of the negation
> operator `not`. Let `S = (Y, X, def, A)` be a schema. We define the
> following four binary relations for labels `z, z' ∈ X ∪ Y`:
>
> – `dep-extends_S(z,z')` iff `H_S` has an edge from `z` to `z'` or from
>   `z'` to `z`;
> – `dep_S(z,z')` iff `z'` appears as a reference in `def(z)`, i.e.
>   `@z' ∈ sub-expr(def(z))`;
> – `dep-shape-neg_S(z,z')` iff `[closed][extra P]⟨e⟩ ∈ neg-sub-expr(def(z))`
>   and `@z' ∈ sub-expr(e)`;
> – `dep-extra-neg_S(z,z')` iff `[closed][extra P]⟨e⟩ ∈ sub-expr(def(z))`,
>   and `p @z' ∈ tcs(e)`, and `p ∈ P`.
>
> The dependencies `dep-shape-neg` and `dep-extra-neg` are called negative
> dependencies. Obviously, `dep` subsumes `dep-shape-neg` and
> `dep-extra-neg`.
>
> Definition 6 (well-defined schema, stratified negation). A schema `S`
> is well-defined if it satisfies these conditions:
> – `H_S`, the extension hierarchy graph of `S`, is acyclic;
> – in `D_S`, no cycle contains a negative dependency edge labelled
>   `dep-shape-neg` or `dep-extra-neg`. We say in this case that `S` is
>   with stratified negation.

Definition 5's four relations only need reference-collecting (`dep`,
`dep-shape-neg`) or triple-constraint-property-collecting
(`dep-extra-neg`) inside a single label's own definition, not a
schema-wide reachability computation like `H_S`'s edges. So, mirroring
`ShexLean/Shex2017Schemas/Stratification.lean`'s `depsAux`, a single
recursive walk over `s = S.shapeDef z`, tracking whether the current
position is under `not`, computes all three relations' target sets at
once (`DepInfo` below). `[closed][extra P]⟨e⟩` matches either a bare
`.ofShape h` or the `h` inside an `.extends X h` (same `Shape` grammar
production, Definition 1); since `extends X h [and u]`'s `u` is itself a
sub-expression of `def(z)`, the walk recurses through `or`/`and`/`not`
uniformly to reach every `[closed][extra P]⟨e⟩`, whether inside an
`extends`'s `h`, a restriction `u`, or a plain shape.

`dep-extends_S` is not built from this walk: `H_S`'s edges
(`Schema.extEdge`, `Syntax.lean`) already capture `extends X h`'s targets,
and `dep-extends_S(z,z')` is just that relation made symmetric.
-/

namespace ShexLean.Inheritance

/-! ### Definition 5: the dependency graph `D_S` -/

/-- The three label-sets a single `depsAux` walk over a shape expression
collects at once: labels referenced anywhere (`refs`, for `dep_S`), labels
referenced under an odd number of `not` (`negRefs`, for `dep-shape-neg_S`),
and labels referenced by a triple constraint whose property is also in
that same shape's `extra` set (`extraNegRefs`, for `dep-extra-neg_S`). -/
structure DepInfo where
  refs : Finset Label
  negRefs : Finset Label
  extraNegRefs : Finset Label

instance : Union DepInfo :=
  ⟨fun a b => ⟨a.refs ∪ b.refs, a.negRefs ∪ b.negRefs, a.extraNegRefs ∪ b.extraNegRefs⟩⟩

instance : EmptyCollection DepInfo := ⟨⟨∅, ∅, ∅⟩⟩

@[simp] theorem DepInfo.union_refs (a b : DepInfo) : (a ∪ b).refs = a.refs ∪ b.refs := rfl
@[simp] theorem DepInfo.union_negRefs (a b : DepInfo) :
    (a ∪ b).negRefs = a.negRefs ∪ b.negRefs := rfl
@[simp] theorem DepInfo.union_extraNegRefs (a b : DepInfo) :
    (a ∪ b).extraNegRefs = a.extraNegRefs ∪ b.extraNegRefs := rfl
@[simp] theorem DepInfo.empty_refs : (∅ : DepInfo).refs = ∅ := rfl
@[simp] theorem DepInfo.empty_negRefs : (∅ : DepInfo).negRefs = ∅ := rfl
@[simp] theorem DepInfo.empty_extraNegRefs : (∅ : DepInfo).extraNegRefs = ∅ := rfl

/-- The dependency info contributed by a single `[closed][extra P]⟨e⟩`
shape (Definition 1's `h`), given whether it occurs under `not` (`neg`;
see `ShapeExpr.depsAux`'s docstring for why this means "under any `not`",
not literally "under an odd number of `not`" as Definition 5 states). -/
def Shape.depInfo (h : Shape) (neg : Bool) : DepInfo :=
  { refs := h.triples.tcs.image Prod.snd
    negRefs := if neg then h.triples.tcs.image Prod.snd else ∅
    extraNegRefs := (h.triples.tcs.filter (fun pz => pz.1 ∈ h.extra.getD ∅)).image Prod.snd }

/-- Definition 5's `sub-expr(def(z))`/`neg-sub-expr(def(z))` walk.
`.extends`'s own extends-targets contribute nothing here; they are
`dep-extends_S`'s concern, via `Schema.extEdge`.

Deliberate deviation from Definition 5: the paper defines `neg-sub-expr(s)`
by true parity of `not`-nesting, toggling on every `not`. Here `neg`
latches instead: once `true`, a further nested `not` leaves it `true`
(`.not s => s.depsAux true`, ignoring the incoming `neg` rather than
negating it). This is a more conservative notion of "negative dependency"
— it can only classify more things as negative, never fewer — so every
schema well-defined under the paper's literal parity reading stays
well-defined under this one; nothing already proved changes meaning, and
the two readings agree on both papers' own examples (which never nest
`not` under `not`).

This is needed for `Proposition1.lean`'s `stratMono` (mirroring 2017's
`not_negDeps`): its `not` case needs everything reachable from inside a
`not`, regardless of that content's own `not`-nesting, to already be
covered by the outer call's `negRefs`. Latching gives this for free: at
`neg = true`, `negRefs = refs` unconditionally, by structural induction,
since latching never un-sets `neg`. True-parity toggling does not have
this property. -/
def ShapeExpr.depsAux (neg : Bool) : ShapeExpr → DepInfo
  | .constraint _ => ∅
  | .ofShape h => h.depInfo neg
  | .extends _ h => h.depInfo neg
  | .or s1 s2 => s1.depsAux neg ∪ s2.depsAux neg
  | .and s1 s2 => s1.depsAux neg ∪ s2.depsAux neg
  | .not s => s.depsAux true

/-- `dep-extends_S(z,z')`: `H_S` has an edge between `z` and `z'`, in
either direction. -/
def Schema.depExtends (S : Schema) (z z' : Label) : Prop := S.extEdge z z' ∨ S.extEdge z' z

/-- `dep_S(z,z')`: `z'` appears as a reference (`@z'`) somewhere in
`def(z)`. -/
def Schema.dep (S : Schema) (z z' : Label) : Prop :=
  z' ∈ ((S.shapeDef z).depsAux false).refs

/-- `dep-shape-neg_S(z,z')`: `z'` is referenced under an odd number of
`not` in `def(z)`. -/
def Schema.depShapeNeg (S : Schema) (z z' : Label) : Prop :=
  z' ∈ ((S.shapeDef z).depsAux false).negRefs

/-- `dep-extra-neg_S(z,z')`: some `[closed][extra P]⟨e⟩` sub-expression of
`def(z)` has a triple constraint `p @z'` with `p ∈ P`. -/
def Schema.depExtraNeg (S : Schema) (z z' : Label) : Prop :=
  z' ∈ ((S.shapeDef z).depsAux false).extraNegRefs

/-- `negRefs ⊆ refs` for any shape expression, at any `neg` — the
structural fact behind "`dep` subsumes `dep-shape-neg`". -/
theorem ShapeExpr.negRefs_subset_refs (s : ShapeExpr) (neg : Bool) :
    (s.depsAux neg).negRefs ⊆ (s.depsAux neg).refs := by
  induction s generalizing neg with
  | constraint c => simp [ShapeExpr.depsAux]
  | ofShape h => rcases neg <;> simp [ShapeExpr.depsAux, Shape.depInfo]
  | «extends» xs h => rcases neg <;> simp [ShapeExpr.depsAux, Shape.depInfo]
  | or s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, DepInfo.union_refs]
      exact Finset.union_subset_union (ih1 neg) (ih2 neg)
  | and s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, DepInfo.union_refs]
      exact Finset.union_subset_union (ih1 neg) (ih2 neg)
  | not s ih => simpa only [ShapeExpr.depsAux] using ih true

/-- At `neg = true`, `negRefs` is not just `⊆ refs` (`negRefs_subset_refs`)
but equal to it, for any `s`, including one with further `not`s nested
inside, since latching never un-sets `neg`. This is what `stratMono`'s
`.not` case (`Proposition1.lean`) needs: the outer call's `negRefs` (at
`neg = false`, i.e. `(.not s).depsAux false = s.depsAux true`) must bound
all of `s`'s own references, not just the not-yet-further-negated ones. -/
theorem ShapeExpr.negRefs_true_eq_refs (s : ShapeExpr) :
    (s.depsAux true).negRefs = (s.depsAux true).refs := by
  induction s with
  | constraint c => simp [ShapeExpr.depsAux]
  | ofShape h => simp [ShapeExpr.depsAux, Shape.depInfo]
  | «extends» xs h => simp [ShapeExpr.depsAux, Shape.depInfo]
  | or s1 s2 ih1 ih2 => simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, DepInfo.union_refs,
      ih1, ih2]
  | and s1 s2 ih1 ih2 => simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, DepInfo.union_refs,
      ih1, ih2]
  | not s ih => simpa only [ShapeExpr.depsAux] using ih

/-- `extraNegRefs ⊆ refs` for any shape expression, at any `neg` — the
structural fact behind "`dep` subsumes `dep-extra-neg`". -/
theorem ShapeExpr.extraNegRefs_subset_refs (s : ShapeExpr) (neg : Bool) :
    (s.depsAux neg).extraNegRefs ⊆ (s.depsAux neg).refs := by
  induction s generalizing neg with
  | constraint c => simp [ShapeExpr.depsAux]
  | ofShape h =>
      simp only [ShapeExpr.depsAux, Shape.depInfo]
      exact Finset.image_subset_image (Finset.filter_subset _ _)
  | «extends» xs h =>
      simp only [ShapeExpr.depsAux, Shape.depInfo]
      exact Finset.image_subset_image (Finset.filter_subset _ _)
  | or s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_extraNegRefs, DepInfo.union_refs]
      exact Finset.union_subset_union (ih1 neg) (ih2 neg)
  | and s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_extraNegRefs, DepInfo.union_refs]
      exact Finset.union_subset_union (ih1 neg) (ih2 neg)
  | not s ih => simpa only [ShapeExpr.depsAux] using ih true

/-- "`dep` subsumes `dep-shape-neg`" (Definition 5's remark). -/
theorem Schema.dep_of_depShapeNeg {S : Schema} {z z' : Label} (h : S.depShapeNeg z z') :
    S.dep z z' :=
  ShapeExpr.negRefs_subset_refs (S.shapeDef z) false h

/-- "`dep` subsumes `dep-extra-neg`" (Definition 5's remark). -/
theorem Schema.dep_of_depExtraNeg {S : Schema} {z z' : Label} (h : S.depExtraNeg z z') :
    S.dep z z' :=
  ShapeExpr.extraNegRefs_subset_refs (S.shapeDef z) false h

/-! ### Definition 6: well-defined schema, stratified negation -/

/-- `H_S` is acyclic: no extendable label transitively extends itself.
The first of Definition 6's two conditions. -/
def Schema.ExtAcyclic (S : Schema) : Prop :=
  ∀ x ∈ S.X, ¬ Relation.TransGen S.extEdge x x

/-- Any `D_S` edge ("`z` depends on `z'`"). Since `dep` subsumes
`dep-shape-neg`/`dep-extra-neg` (Definition 5's remark), following either
`dep` or `dep-extends` already covers every edge `D_S` can have, regardless
of which of the four labels it carries. -/
def Schema.DEdge (S : Schema) (z z' : Label) : Prop := S.dep z z' ∨ S.depExtends z z'

/-- A `D_S` edge carrying one of the two *negative* labels. -/
def Schema.DNegEdge (S : Schema) (z z' : Label) : Prop :=
  S.depShapeNeg z z' ∨ S.depExtraNeg z z'

/-- `D_S` has a cycle through a negative dependency edge: some negative
edge `a → b`, closed back into a cycle by an ordinary `D_S` path from `b`
back to `a` (possibly the empty path, if `a = b`, a negative self-loop). -/
def Schema.NegCycle (S : Schema) : Prop :=
  ∃ a b, S.DNegEdge a b ∧ Relation.ReflTransGen S.DEdge b a

/-- Definition 6 (well-defined schema, stratified negation). -/
def Schema.WellDefined (S : Schema) : Prop := S.ExtAcyclic ∧ ¬ S.NegCycle

end ShexLean.Inheritance
