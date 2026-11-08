import ShexLean.Shex2025Inheritance.Semantics
import Mathlib.Logic.Relation

/-!
Definitions 5 and 6 (§4.2) of the 2025 paper "Shape Expressions with Inheritance":
the dependency graph `D_S`, and well-defined schemas ("stratified negation").

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

Three of the four relations of Definition 5 look only inside the
definition of one label:

* `dep` and `dep-shape-neg` collect references.
* `dep-extra-neg` collects the properties of triple constraints.

They do not need a reachability computation over the full schema, as the
edges of `H_S` do. Thus, one recursive walk over `s = S.shapeDef z`
computes the target sets of the three relations together (`DepInfo`
below). The walk records if the current position is below a `not`. This
is the same method as `depsAux` in
`ShexLean/Shex2017Schemas/Stratification.lean`.

`[closed][extra P]⟨e⟩` matches a plain `.ofShape h`, and also the `h`
inside an `.extends X h`. (The two use the same `Shape` production of
Definition 1.) In `extends X h [and u]`, `u` is also a sub-expression of
`def(z)`. Thus, the walk goes through `or`, `and` and `not` in the same
way, and finds each `[closed][extra P]⟨e⟩`: in the `h` of an `extends`, in
a restriction `u`, or in a plain shape.

The walk does not make `dep-extends_S`. The edges of `H_S`
(`Schema.extEdge`, `Syntax.lean`) already record the targets of
`extends X h`. `dep-extends_S(z,z')` is that relation, made symmetric.
-/

namespace ShexLean.Inheritance

/-! ### Definition 5: the dependency graph `D_S` -/

/-- The three label sets that one `depsAux` walk over a shape expression
collects together:

* `refs` (for `dep_S`): the labels with a reference at any location.
* `negRefs` (for `dep-shape-neg_S`): the labels with a reference below a
  `not`. (Refer to the docstring of `ShapeExpr.depsAux` for how this is
  different from "an odd number of `not`".)
* `extraNegRefs` (for `dep-extra-neg_S`): the labels with a reference in a
  triple constraint whose property is also in the `extra` set of the same
  shape. -/
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

/-- The dependency information of one shape `[closed][extra P]⟨e⟩` (the
`h` of Definition 1). `neg` tells if the shape occurs below a `not`. (Refer
to the docstring of `ShapeExpr.depsAux` to know why this means "below
*any* `not`", and not "below an odd number of `not`" as in Definition 5.) -/
def Shape.depInfo (h : Shape) (neg : Bool) : DepInfo :=
  { refs := h.triples.tcs.image Prod.snd
    negRefs := if neg then h.triples.tcs.image Prod.snd else ∅
    extraNegRefs := (h.triples.tcs.filter (fun pz => pz.1 ∈ h.extra.getD ∅)).image Prod.snd }

/-- The walk `sub-expr(def(z))` / `neg-sub-expr(def(z))` of Definition 5.
The extends targets of `.extends` add nothing here. They are for
`dep-extends_S`, through `Schema.extEdge`.

**This is an intentional difference from Definition 5.** The paper defines
`neg-sub-expr(s)` by the true parity of the `not` nesting: each `not`
toggles it. Here, `neg` *latches*: when it is `true`, a nested `not` keeps
it `true`. (`.not s => s.depsAux true` ignores the incoming `neg`. It does
not negate it.)

This notion of "negative dependency" is more conservative. It can only
classify more dependencies as negative, never fewer. Thus:

* Each schema that is well-defined with the parity reading of the paper is
  also well-defined with this reading.
* No proved result changes its meaning.
* The two readings agree on the examples of the two papers. These examples
  never put a `not` below a `not`.

The `stratMono` lemma of `Proposition1.lean` needs this. (It has the same
role as `not_negDeps` in 2017.) Its `not` case needs the `negRefs` of the
outer call to cover all that is reachable inside a `not`, at each nesting
depth of `not` in that content. Latching gives this directly. At
`neg = true`, `negRefs = refs` always, by structural induction, because
latching never sets `neg` back to `false`. The parity reading does not
have this property. -/
def ShapeExpr.depsAux (neg : Bool) : ShapeExpr → DepInfo
  | .constraint _ => ∅
  | .ofShape h => h.depInfo neg
  | .extends _ h => h.depInfo neg
  | .or s1 s2 => s1.depsAux neg ∪ s2.depsAux neg
  | .and s1 s2 => s1.depsAux neg ∪ s2.depsAux neg
  | .not s => s.depsAux true

/-- `dep-extends_S(z,z')`: `H_S` has an edge between `z` and `z'`, in one
of the two directions. -/
def Schema.depExtends (S : Schema) (z z' : Label) : Prop := S.extEdge z z' ∨ S.extEdge z' z

/-- `dep_S(z,z')`: `z'` occurs as a reference (`@z'`) in `def(z)`. -/
def Schema.dep (S : Schema) (z z' : Label) : Prop :=
  z' ∈ ((S.shapeDef z).depsAux false).refs

/-- `dep-shape-neg_S(z,z')`: `def(z)` has a reference to `z'` below a
`not`. (Refer to `ShapeExpr.depsAux`: this file counts "below any `not`",
not "below an odd number of `not`".) -/
def Schema.depShapeNeg (S : Schema) (z z' : Label) : Prop :=
  z' ∈ ((S.shapeDef z).depsAux false).negRefs

/-- `dep-extra-neg_S(z,z')`: a sub-expression `[closed][extra P]⟨e⟩` of
`def(z)` has a triple constraint `p @z'` with `p ∈ P`. -/
def Schema.depExtraNeg (S : Schema) (z z' : Label) : Prop :=
  z' ∈ ((S.shapeDef z).depsAux false).extraNegRefs

/-- `negRefs ⊆ refs` for each shape expression, at each `neg`. This is
the structural fact for "`dep` subsumes `dep-shape-neg`". -/
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

/-- At `neg = true`, `negRefs` is not only `⊆ refs`
(`negRefs_subset_refs`). It is equal to `refs`, for each `s`, also when
`s` has more nested `not`s, because latching never sets `neg` back to
`false`.

The `.not` case of `stratMono` (`Proposition1.lean`) needs this. The
`negRefs` of the outer call (at `neg = false`, thus
`(.not s).depsAux false = s.depsAux true`) must bound all the references
of `s`, not only the references that are not negated again. -/
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

/-- `extraNegRefs ⊆ refs` for each shape expression, at each `neg`. This
is the structural fact for "`dep` subsumes `dep-extra-neg`". -/
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

/-- "`dep` subsumes `dep-shape-neg`" (the remark after Definition 5). -/
theorem Schema.dep_of_depShapeNeg {S : Schema} {z z' : Label} (h : S.depShapeNeg z z') :
    S.dep z z' :=
  ShapeExpr.negRefs_subset_refs (S.shapeDef z) false h

/-- "`dep` subsumes `dep-extra-neg`" (the remark after Definition 5). -/
theorem Schema.dep_of_depExtraNeg {S : Schema} {z z' : Label} (h : S.depExtraNeg z z') :
    S.dep z z' :=
  ShapeExpr.extraNegRefs_subset_refs (S.shapeDef z) false h

/-! ### Definition 6: well-defined schema, stratified negation -/

/-- `H_S` is acyclic: no extendable label extends itself transitively.
This is the first of the two conditions of Definition 6. -/
def Schema.ExtAcyclic (S : Schema) : Prop :=
  ∀ x ∈ S.X, ¬ Relation.TransGen S.extEdge x x

/-- An edge of `D_S` ("`z` depends on `z'`"). `dep` subsumes
`dep-shape-neg` and `dep-extra-neg` (the remark after Definition 5). Thus,
`dep` and `dep-extends` together already cover each edge that `D_S` can
have, for each of the four labels. -/
def Schema.DEdge (S : Schema) (z z' : Label) : Prop := S.dep z z' ∨ S.depExtends z z'

/-- An edge of `D_S` with one of the two *negative* labels. -/
def Schema.DNegEdge (S : Schema) (z z' : Label) : Prop :=
  S.depShapeNeg z z' ∨ S.depExtraNeg z z'

/-- `D_S` has a cycle through a negative dependency edge. There is a
negative edge `a → b`, and an ordinary `D_S` path from `b` back to `a`
closes the cycle. (The path can be empty if `a = b`. This is a negative
self-loop.) -/
def Schema.NegCycle (S : Schema) : Prop :=
  ∃ a b, S.DNegEdge a b ∧ Relation.ReflTransGen S.DEdge b a

/-- Definition 6 (well-defined schema, stratified negation). -/
def Schema.WellDefined (S : Schema) : Prop := S.ExtAcyclic ∧ ¬ S.NegCycle

end ShexLean.Inheritance
