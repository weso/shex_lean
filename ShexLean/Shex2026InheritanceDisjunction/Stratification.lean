import ShexLean.Shex2026InheritanceDisjunction.Semantics
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

Definition 5's four relations only ever need `@z'`-reference-collecting
(`dep`, `dep-shape-neg`) or triple-constraint-property-collecting
(`dep-extra-neg`) *inside a single label's own definition* — never a
schema-wide reachability computation, unlike `H_S`'s edges. So (mirroring
`ShexLean/Shex2017Schemas/Stratification.lean`'s `depsAux` for the 2017 formalism) a single
recursive walk over `s = S.shapeDef z`, tracking whether the current
position is under an odd number of `not`, computes all three relations'
"target set" at once (`DepInfo` below) — `[closed][extra P]⟨e⟩` matches
*either* a bare `.ofShape h` or the `h` embedded in an `.extends X h`
(both are literally the same `Shape` grammar production, Definition 1),
and — since `extends X h [and u]`'s `u` is a genuine sub-expression of
`def(z)` too — the walk recurses through `or`/`and`/`not` uniformly,
picking up every `[closed][extra P]⟨e⟩` reachable that way, regardless of
whether it sits inside an `extends`'s own `h`, a restriction `u`, or a
plain shape.

Note `dep-extends_S` is *not* built from this walk at all — `H_S`'s edges
(`Schema.extEdge`, `ShexLean/Shex2025Inheritance/Syntax.lean`) already capture
exactly `extends X h`'s targets; `dep-extends_S(z,z')` is just that
relation made symmetric.
-/

namespace ShexLean.InheritanceDisjunction

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
see `ShapeExpr.depsAux`'s docstring for why this is "under *any* `not`",
not literally "under an *odd number of* `not`" as Definition 5's own
wording has it). -/
def Shape.depInfo (h : Shape) (neg : Bool) : DepInfo :=
  { refs := h.triples.tcs.image Prod.snd
    negRefs := if neg then h.triples.tcs.image Prod.snd else ∅
    extraNegRefs := (h.triples.tcs.filter (fun pz => pz.1 ∈ h.extra.getD ∅)).image Prod.snd }

/-- `hs`'s combined dependency info: the union of every disjunct's own
`depInfo` — since `pick` (`Semantics.lean`'s rule 18) could select *any*
`h ∈ hs` at evaluation time, a sound (conservative) stratification analysis
must count *all* of them as potential dependencies, exactly the same way
`.or`/`.and`'s own `depsAux` cases union both branches regardless of which
one a particular derivation actually uses. -/
def Shape.listDepInfo (hs : List Shape) (neg : Bool) : DepInfo :=
  hs.foldr (fun h acc => h.depInfo neg ∪ acc) ∅

theorem Shape.listDepInfo_negRefs_subset_refs (hs : List Shape) (neg : Bool) :
    (Shape.listDepInfo hs neg).negRefs ⊆ (Shape.listDepInfo hs neg).refs := by
  induction hs with
  | nil => simp [Shape.listDepInfo]
  | cons a rest ih =>
      simp only [Shape.listDepInfo, List.foldr_cons, DepInfo.union_negRefs, DepInfo.union_refs]
      exact Finset.union_subset_union (by rcases neg <;> simp [Shape.depInfo]) ih

theorem Shape.listDepInfo_negRefs_true_eq_refs (hs : List Shape) :
    (Shape.listDepInfo hs true).negRefs = (Shape.listDepInfo hs true).refs := by
  induction hs with
  | nil => simp [Shape.listDepInfo]
  | cons a rest ih =>
      show (a.depInfo true ∪ Shape.listDepInfo rest true).negRefs =
        (a.depInfo true ∪ Shape.listDepInfo rest true).refs
      simp [Shape.depInfo, ih]

theorem Shape.listDepInfo_extraNegRefs_subset_refs (hs : List Shape) (neg : Bool) :
    (Shape.listDepInfo hs neg).extraNegRefs ⊆ (Shape.listDepInfo hs neg).refs := by
  induction hs with
  | nil => simp [Shape.listDepInfo]
  | cons a rest ih =>
      simp only [Shape.listDepInfo, List.foldr_cons, DepInfo.union_extraNegRefs,
        DepInfo.union_refs]
      exact Finset.union_subset_union
        (by simp only [Shape.depInfo]; exact Finset.image_subset_image (Finset.filter_subset _ _))
        ih

/-- `.refs` never actually depends on `neg` at the `Shape.listDepInfo`
level either (only `.negRefs` does) — the list analogue of
`ShapeExpr.depsAux_refs_indep` (`Proposition1.lean`). -/
theorem Shape.listDepInfo_refs_indep (hs : List Shape) (neg1 neg2 : Bool) :
    (Shape.listDepInfo hs neg1).refs = (Shape.listDepInfo hs neg2).refs := by
  induction hs with
  | nil => simp [Shape.listDepInfo]
  | cons a rest ih =>
      show (a.depInfo neg1 ∪ Shape.listDepInfo rest neg1).refs =
        (a.depInfo neg2 ∪ Shape.listDepInfo rest neg2).refs
      simp [Shape.depInfo, ih]

/-- Every disjunct's own `.triples.refs` is contained in `hs`'s combined
`Shape.listDepInfo`'s `.refs` — the `refs`-containment analogue of
`Shape.triples_size_le_listSize`, used by `Proposition1.lean`'s
`extTeAt_refs_subset` the same way `Termination.lean`'s `extTeAt_size_le`
uses the `.size` version. -/
theorem Shape.triples_refs_subset_listDepInfo_refs {hs : List Shape} {h : Shape} (hmem : h ∈ hs)
    (neg : Bool) : h.triples.tcs.image Prod.snd ⊆ (Shape.listDepInfo hs neg).refs := by
  induction hs with
  | nil => exact absurd hmem List.not_mem_nil
  | cons a rest ih =>
      show h.triples.tcs.image Prod.snd ⊆ (a.depInfo neg ∪ Shape.listDepInfo rest neg).refs
      rcases List.mem_cons.mp hmem with heq | hmem'
      · subst heq
        simp only [DepInfo.union_refs, Shape.depInfo]
        exact Finset.subset_union_left
      · simp only [DepInfo.union_refs]
        exact Finset.Subset.trans (ih hmem') Finset.subset_union_right

/-- Definition 5's `sub-expr(def(z))`/`neg-sub-expr(def(z))` walk.
`.extends`'s own extends-targets contribute nothing here (they are
`dep-extends_S`'s concern, via `Schema.extEdge`, not this walk's).

**A deliberate deviation from Definition 5's literal wording**, worth
flagging explicitly: the paper defines `neg-sub-expr(s)` as "sub-expressions
that appear in `s` under an *odd number of occurrences* of `not`" — true
parity, toggling on every `not`. Below, `neg` instead *latches*: once
`true`, a further nested `not` leaves it `true` rather than flipping it
back (`.not s => s.depsAux true`, ignoring the incoming `neg` rather than
negating it). This is a strictly *more conservative* notion of "negative
dependency" (it only ever classifies more things as negative, never fewer,
since parity-`true` positions are a subset of latch-`true` positions) —
every schema `well-defined` under the paper's literal parity reading
remains so under this stricter one, so nothing already proved changes
meaning, and it costs nothing for the schemas either paper actually
exercises (their own examples never nest `not` under `not`, where the two
readings first diverge). It's needed for `ShexLean/Shex2025Inheritance/
Proposition1.lean`'s `stratMono`: mirroring 2017's own `not_negDeps`
(`ShexLean/Shex2017Schemas/Proposition1.lean`, `S.posDeps ∪ S.negDeps ⊆ (.not S).negDeps`),
`stratMono`'s `not` case needs *everything* reachable from inside a `not`
— regardless of that content's own internal `not`-nesting — to already be
accounted for by the outer call's `negRefs`, which is exactly what latching
(and not true parity) guarantees: at `neg = true`, `negRefs = refs`
*unconditionally*, by a clean structural induction, since latching never
un-sets `neg` for the rest of the recursion. True-parity toggling does not
have this property (two nested `not`s cancel back to positive, so the
*outer* call's `negRefs` at that point would need to be empty, an
insufficient bound for what the inner content, itself simply reused for a
different stratMono step, would actually require). -/
def ShapeExpr.depsAux (neg : Bool) : ShapeExpr → DepInfo
  | .constraint _ => ∅
  | .ofShape h => h.depInfo neg
  | .extends _ hs => Shape.listDepInfo hs neg
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
  | «extends» xs hs => exact Shape.listDepInfo_negRefs_subset_refs hs neg
  | or s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, DepInfo.union_refs]
      exact Finset.union_subset_union (ih1 neg) (ih2 neg)
  | and s1 s2 ih1 ih2 =>
      simp only [ShapeExpr.depsAux, DepInfo.union_negRefs, DepInfo.union_refs]
      exact Finset.union_subset_union (ih1 neg) (ih2 neg)
  | not s ih => simpa only [ShapeExpr.depsAux] using ih true

/-- The latching payoff: at `neg = true`, `negRefs` is not just `⊆ refs`
(`negRefs_subset_refs`) but *equal* to it, for *any* `s` — including one
with further `not`s nested inside, since latching never un-sets `neg` for
the rest of the recursion. This is what `stratMono`'s `.not` case
(`ShexLean/Shex2025Inheritance/Proposition1.lean`) actually needs: the outer call's
`negRefs` (at `neg = false`, i.e. `(.not s).depsAux false = s.depsAux
true`) must bound *all* of `s`'s own references, not just the
not-yet-further-negated ones. -/
theorem ShapeExpr.negRefs_true_eq_refs (s : ShapeExpr) :
    (s.depsAux true).negRefs = (s.depsAux true).refs := by
  induction s with
  | constraint c => simp [ShapeExpr.depsAux]
  | ofShape h => simp [ShapeExpr.depsAux, Shape.depInfo]
  | «extends» xs hs => exact Shape.listDepInfo_negRefs_true_eq_refs hs
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
  | «extends» xs hs => exact Shape.listDepInfo_extraNegRefs_subset_refs hs neg
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

/-- Any `D_S` edge ("`z` depends on `z'`", the paper's own phrase right
after Definition 5: "`dep` subsumes `dep-shape-neg`/`dep-extra-neg`", so
following either the `dep` or `dep-extends` relation already covers every
edge `D_S` can have, regardless of which of the four labels it carries). -/
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

end ShexLean.InheritanceDisjunction
