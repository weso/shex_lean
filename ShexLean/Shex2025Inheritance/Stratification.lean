import ShexLean.Shex2025Inheritance.Syntax
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

open ShexLean.InheritanceCore hiding Schema

/-! ### Definition 5: the dependency graph `D_S` -/

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

/-- The schema-level definitions of `ShexLean/InheritanceCore/Schema.lean`
(`H_S`, `D_S`, `dep`, `dep-shape-neg`, `dep-extra-neg`, `dep-extends`,
Definition 6 and Definition 7) use a shape expression through these
functions. -/
instance : ShapeSyntax ShapeExpr where
  extendsTargets := ShapeExpr.extendsTargets
  deps s := s.depsAux false
  negRefs_subset_refs s := s.negRefs_subset_refs false
  extraNegRefs_subset_refs s := s.extraNegRefs_subset_refs false

@[simp] theorem ShapeExpr.shapeSyntax_deps (s : ShapeExpr) : ShapeSyntax.deps s = s.depsAux false :=
  rfl

@[simp] theorem ShapeExpr.shapeSyntax_extendsTargets (s : ShapeExpr) :
    ShapeSyntax.extendsTargets s = s.extendsTargets := rfl

end ShexLean.Inheritance
