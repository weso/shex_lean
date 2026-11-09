import ShexLean.Common.RDF
import ShexLean.Common.Typing
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Relation

/-!
Definitions 1–3 (§3) of Boneva, Labra Gayo, Prud'hommeaux, Thornton,
Waagmeester (2025), "Shape Expressions with Inheritance"
(arXiv:2503.24299). These definitions give:

* The syntax of shape expressions with inheritance.
* ShEx schemas.
* The extension hierarchy.

This formalism is different from `ShexLean.Syntax` (the `ShapeExpr` and
`TripleExpr` of the 2017 paper). It is not a strict extension of it:

* A node constraint is a Boolean predicate, not a concrete `ValueDescr`.
* `closed` and `extra` are shape modifiers in the syntax. In 2017, they
  were an encoding.
* `extends` is new.

It is in its own namespace, `ShexLean.Inheritance`, so that its names do
not conflict with the 2017 definitions. It uses, with no change, the RDF
and typing vocabulary that does not depend on a paper:

* `ShexLean.RDF` (`IRI`, `RDFNode`, `Triple`, `Graph`, `neigh`).
* `ShexLean.Typing` (`Label`, `Assoc`, `Typing`, `Typing.has`).

A "typing of `G` by `S`" has the same meaning in the two papers.

> Definition 1 (shape expressions). Let Y be a finite set of simple labels
> and X be a finite set of extendable labels disjoint from Y. A shape
> expression over Y and X is either a reference of the form @z, or a plain
> shape expression derivable from the non-terminal u in the following
> grammar:
>
>   u ::= h | t | c | u or u | u and u | not u .   (plain shape expression)
>   h ::= [closed] [extra P] ⟨e⟩ .                  (shape)
>   t ::= extends X h .                              (shape with extends)
>   c ::= a boolean function over IRI ∪ Blank ∪ Literal .   (node constraint)
>   e ::= ε | p @z | e|e | e;e | e* .                (triple expression)
>
> where z ∈ Y ∪ X, X ⊆ X, p ∈ IRI, P ⊆ IRI, the symbol 'ε' is a constant,
> and the symbols '@', '|', '*' and ';' are operators.

A reference `@z` is not a `ShapeExpr` constructor. The grammar of `u` in
Definition 1 has no `@z` alternative. (A schema's `def` maps labels to
`u`.) A reference occurs only inside a triple constraint `p @z`
(`TripleExpr.tc`). There, rule 10 of Table 2 (`@z: (n,z) ∈ τ`) is a typing
lookup with no more recursion. This agrees with `typing.has obj L` of Rule
te-tpattern in the 2017 formalization
(`ShexLean/Shex2017Schemas/Semantics.lean`). `Semantics.lean` puts it
directly in the satisfaction rule of `TripleExpr.tc`.

The production `t ::= extends X h .` has no `[and u]` field. In the text
of Definition 2, a label can have an optional restriction:
`extends X h and u`. This is the general production `u and u`, where the
first operand is `t`. Thus, it is
`ShapeExpr.and (ShapeExpr.extends X h) u`. `ShapeExpr.extTe` and
`ShapeExpr.restrOf` below get the `ext-te(x)` and `restr(x)` of the paper
(Table 3, rule 18) from the two forms: `extends X h` and
`(extends X h) and u`.
-/

namespace ShexLean.Inheritance

/-- The node constraint `c` of Def 1: "a boolean function over
IRI ∪ Blank ∪ Literal". Thus, it is a function over `RDFNode`. It is fully
abstract, as in the paper. (The 2017 formalization uses a concrete
`ValueDescr`.) -/
abbrev NodeConstraint := RDFNode → Prop

/-- The grammar of triple expressions of Def 1:
`e ::= ε | p @z | e|e | e;e | e*`. `tc p z` is the triple constraint
`p @z`. `z` is a `Label` (from `ShexLean.Typing`). Thus, it is in `Y ∪ X`
for the schema of the expression. -/
inductive TripleExpr where
  | empty : TripleExpr
  | tc (p : IRI) (z : Label) : TripleExpr
  | choice (e1 e2 : TripleExpr) : TripleExpr
  | seq (e1 e2 : TripleExpr) : TripleExpr
  | star (e : TripleExpr) : TripleExpr
  deriving DecidableEq

/-- The triple-constraint sub-expressions of `e` (`tcs(e)` in the paper),
as pairs `(property, target label)`. -/
def TripleExpr.tcs : TripleExpr → Finset (IRI × Label)
  | .empty => ∅
  | .tc p z => {(p, z)}
  | .choice e1 e2 => e1.tcs ∪ e2.tcs
  | .seq e1 e2 => e1.tcs ∪ e2.tcs
  | .star e => e.tcs

/-- The properties of the triple constraints of `e` (`props(e)` in the
paper). -/
def TripleExpr.props (e : TripleExpr) : Finset IRI := e.tcs.image Prod.fst

/-- The shape `h ::= [closed] [extra P] ⟨e⟩` of Def 1. `extra := none` when
there is no `extra` (thus, `P' = ∅` in rule 17 of Table 3).
`extra := some P` when there is one. -/
structure Shape where
  closed : Bool
  extra  : Option (Finset IRI)
  triples : TripleExpr
  deriving DecidableEq

/-- The grammar of shape expressions of Def 1 (`u`, `t`, `c` and the
Boolean connectives). This is all that the `def` of a schema can map a
label to. Refer to the module docstring to know why `@z` is not a
constructor, and why `extends` has no `restr` field. -/
inductive ShapeExpr where
  | ofShape (h : Shape) : ShapeExpr
  | extends (xs : Finset Label) (h : Shape) : ShapeExpr
  | constraint (c : NodeConstraint) : ShapeExpr
  | or (s1 s2 : ShapeExpr) : ShapeExpr
  | and (s1 s2 : ShapeExpr) : ShapeExpr
  | not (s : ShapeExpr) : ShapeExpr

/-- The labels after `extends`, at any location in `s`. The recursion goes
through `or`, `and` and `not`, not only the top level. The extension
hierarchy `H_S` (Definition 3) uses this function.

The text of Definition 3 describes only the outermost
`extends X h [and u]` clause of a label. But the grammar does not keep
`extends` only at that location. `u` can contain a nested `extends`, and
rule 18 of Table 3 (`Semantics.lean`) applies to each `.extends` node that
it gets to. Thus, the function must go through the full tree, as
`ShapeExpr.depsAux` (`Stratification.lean`) already does for references.
Then `Schema.extEdge`, `H_S` and `D_S` record each `extends` that the
evaluator can dereference. This includes an `extends` nested in the
definition of a `Y` label. -/
def ShapeExpr.extendsTargets : ShapeExpr → Finset Label
  | .extends xs _ => xs
  | .constraint _ => ∅
  | .ofShape _ => ∅
  | .or s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .and s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .not s => s.extendsTargets

/-- `ext-te(x)`: if `def(x) = extends X h [and u]`, the triple expression
of `h` (Table 3, the discussion before rule 18). If `s` does not have this
form, the result is a junk value (`.empty`). The result has a meaning only
for `x` with `s = S.shapeDef x`, where `x` is a well-formed extendable
label (`Schema.WellFormedX` below). -/
def ShapeExpr.extTe : ShapeExpr → TripleExpr
  | .extends _ h => h.triples
  | .and (.extends _ h) _ => h.triples
  | _ => .empty

/-- `restr(x)`: if `def(x) = extends X h [and u]`, the optional `u`. The
result is `none` if there is no `and u` part. This agrees with "whenever
it exists" in the text of the paper. If `s` does not have this form, the
result is a junk value (`none`). -/
def ShapeExpr.restrOf : ShapeExpr → Option ShapeExpr
  | .and (.extends _ _) u => some u
  | _ => none

/-- Definition 2 (ShEx schema). `S = (Y, X, def, A)`:

* `Y`: the simple labels.
* `X`: the extendable labels, disjoint from `Y`.
* `A ⊆ X`: the abstract labels.
* `shapeDef` (the `def` of the paper): gives a definition to each label of
  `Y ∪ X`.

`shapeDef` is total on all of `Label` (as in the 2017 formalization),
because Lean functions must be total. Because of this, we need the extra
hypothesis `Schema.WellFormedX` below. (It has the same role as
`Schema.Closed` in `ShexLean/Shex2017Schemas/Proposition1.lean`.) -/
structure Schema where
  Y : Finset Label
  X : Finset Label
  A : Finset Label
  disjointYX : Disjoint Y X
  A_subX : A ⊆ X
  shapeDef : Label → ShapeExpr

/-- The second bullet of Definition 2: for `x ∈ X`, `def(x)` must have the
form `extends X h [and u]`. Thus, it is `.extends xs h` or
`.and (.extends xs h) u`.

The first bullet says "for `y ∈ Y`, `def(y)` is a plain shape
expression". This is automatically true here, because `ShapeExpr` has no
`@z` constructor. Thus, each `ShapeExpr` value is a plain shape
expression. -/
def Schema.WellFormedX (S : Schema) : Prop :=
  ∀ x ∈ S.X, ∃ xs h, S.shapeDef x = .extends xs h ∨ ∃ u, S.shapeDef x = .and (.extends xs h) u

/-- The edge relation of `H_S` in Definition 3. There is an edge from `x`
to `x'` if and only if `x'` comes directly after `extends` at the top of
`def(x)`. -/
abbrev Schema.extEdge (S : Schema) (x x' : Label) : Prop :=
  x' ∈ (S.shapeDef x).extendsTargets

/-- Definition 3 (extension hierarchy). `x' ∈ S.anc x` if and only if
there is a path (possibly empty) from `x` to `x'` in `H_S`. Thus, `x'` is
an ancestor of `x`, and `x` is a descendant of `x'`.

The result is restricted to `S.X` (the vertex set of `H_S`). It has a
meaning only for `x ∈ S.X`. The definition uses `Classical.decPred`,
because `extEdge` is a `Prop` and, in general, reachability is not
decidable. The 2017 formalization does the same in other locations. -/
noncomputable def Schema.anc (S : Schema) (x : Label) : Finset Label :=
  haveI := Classical.decPred (Relation.ReflTransGen S.extEdge x)
  S.X.filter (Relation.ReflTransGen S.extEdge x)

/-- `S.desc x`: the descendants of `x` (the dual of `S.anc`). -/
noncomputable def Schema.desc (S : Schema) (x : Label) : Finset Label :=
  haveI := Classical.decPred (Relation.ReflTransGen S.extEdge · x)
  S.X.filter (Relation.ReflTransGen S.extEdge · x)

/-- `anc(X) = ⋃_{x ∈ X} anc(x)`. Table 3 extends `anc` to a set of labels
in this way. Rule 18 uses it. -/
noncomputable def Schema.ancSet (S : Schema) (xs : Finset Label) : Finset Label :=
  xs.biUnion S.anc

/-! ### Membership lemmas

`anc` and `desc` are filters with a `Classical.decPred` instance. These
lemmas fix the instance one time, here. Thus, the proofs in the other
files use `rw` or `simp` with these lemmas, and never unfold the filters.
This prevents instance mismatches at the call sites. -/

theorem Schema.mem_anc {S : Schema} {x y : Label} :
    y ∈ S.anc x ↔ y ∈ S.X ∧ Relation.ReflTransGen S.extEdge x y := by
  unfold Schema.anc; simp only [Finset.mem_filter]

theorem Schema.mem_desc {S : Schema} {x y : Label} :
    y ∈ S.desc x ↔ y ∈ S.X ∧ Relation.ReflTransGen S.extEdge y x := by
  unfold Schema.desc; simp only [Finset.mem_filter]

theorem Schema.mem_ancSet {S : Schema} {xs : Finset Label} {y : Label} :
    y ∈ S.ancSet xs ↔ ∃ x ∈ xs, y ∈ S.anc x := by
  unfold Schema.ancSet; exact Finset.mem_biUnion

/-- Each label of `X` is its own ancestor (the empty path of `H_S`). -/
theorem Schema.mem_anc_self {S : Schema} {x : Label} (hx : x ∈ S.X) : x ∈ S.anc x :=
  Schema.mem_anc.mpr ⟨hx, Relation.ReflTransGen.refl⟩

theorem Schema.anc_subset_X {S : Schema} {x : Label} : S.anc x ⊆ S.X :=
  fun _ hy => (Schema.mem_anc.mp hy).1

theorem Schema.ancSet_subset_X {S : Schema} {xs : Finset Label} : S.ancSet xs ⊆ S.X := by
  intro y hy
  obtain ⟨_, _, hy⟩ := Schema.mem_ancSet.mp hy
  exact Schema.anc_subset_X hy

/-- `restr(x) = some u` exactly when `def(x)` has the form
`extends X h and u`. The proofs about `restr(x)` use this lemma, and do not
do a case analysis on `ShapeExpr` again. -/
theorem ShapeExpr.restrOf_eq_some {s u : ShapeExpr} :
    s.restrOf = some u ↔ ∃ xs h, s = .and (.extends xs h) u := by
  constructor
  · intro hs
    rcases s with _ | _ | _ | _ | ⟨s1, s2⟩ | _ <;> try simp [ShapeExpr.restrOf] at hs
    cases s1 <;> simp_all
  · rintro ⟨xs, h, rfl⟩; rfl

end ShexLean.Inheritance
