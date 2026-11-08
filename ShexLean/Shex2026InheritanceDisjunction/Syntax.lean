import ShexLean.Common.RDF
import ShexLean.Common.Typing
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Relation

/-!
An exploratory variant of `ShexLean.Shex2025Inheritance` (Definitions 1–3,
§3, of Boneva, Labra Gayo, Prud'hommeaux, Thornton, Waagmeester (2025),
"Shape Expressions with Inheritance", arXiv:2503.24299). It examines a
design choice that the paper explicitly does not accept in §6 ("Design
Choices"):

> We impose a syntactic restriction on extendable shape expressions. They
> must be conjunctions of a shape and a plain shape expression. [...] extending
> on disjunctions together with multiple inheritance complicates the
> definition of the satisfaction relation [...] this would require (1)
> recording which one of the disjuncts [...] has been satisfied by each
> subtype [...] and (2) checking whether all the subtypes satisfy the same
> disjunct. We decided to take a conservative approach and limit the shape
> expressions that can be extended.

Here, `extends X h` has a more general form. `h` is a *nonempty list* of
plain shapes (`hs : List Shape`, which is `s1 or s2 or ...` in the surface
syntax of the paper), not one `Shape`. This is exactly the relaxation that
§6 does not accept.

A singleton list (`hs = [h]`) gives exactly the grammar of the original
paper. Thus, the original formalism is the special case `hs.length = 1` of
this formalism. Some definitions below need only the *set of possible
triple expressions* of `hs`. In the singleton case, each of these
definitions becomes exactly the original definition.

The ambiguity of §6 occurs only when a `.extends` node is *resolved as
the ancestor of a different label* (`ext-te(x)`, Table 3). The fix that we
examine here (refer to rule 18 in `Semantics.lean`) applies to the same
case. A direct resolution
(`M', τ ⊨ h` of rule 17 through rule 18 of Table 3) has no ambiguity. The
reason is that `or` already has an ordinary satisfaction rule (rule 14).
With this rule, a *single* node selects one of the disjuncts, and there is
no question of consistency between nodes.

All other parts are the same as in `ShexLean.Shex2025Inheritance.Syntax`.
This file is in its own namespace, `ShexLean.InheritanceDisjunction`
(parallel to `ShexLean.Inheritance`). Thus, its `ShapeExpr`, `Schema` and
other names do not conflict with the 2017 formalization or with the
original 2025 formalization. It uses directly the RDF and typing
vocabulary that does not depend on a paper.

> Definition 1 (shape expressions, as modified here). u ::= h | t | c | u or
> u | u and u | not u . h ::= [closed] [extra P] ⟨e⟩ . t ::= extends X h or h
> or ... or h . (nonempty disjunction of shapes, generalizing the paper's
> `t ::= extends X h`) c ::= a boolean function over IRI ∪ Blank ∪ Literal .
> e ::= ε | p @z | e|e | e;e | e* .
-/

namespace ShexLean.InheritanceDisjunction

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
label to.

The second argument of `extends` is now a *nonempty list* of shapes (`hs`).
`Schema.WellFormedX` requires `hs ≠ []`. In the original paper, it is one
`Shape`. Refer to the module docstring.

The module docstring of `ShexLean.Shex2025Inheritance.Syntax` tells why
`@z` is not a constructor, and why `extends` has no `restr` field. The two
reasons also apply here. -/
inductive ShapeExpr where
  | ofShape (h : Shape) : ShapeExpr
  | extends (xs : Finset Label) (hs : List Shape) : ShapeExpr
  | constraint (c : NodeConstraint) : ShapeExpr
  | or (s1 s2 : ShapeExpr) : ShapeExpr
  | and (s1 s2 : ShapeExpr) : ShapeExpr
  | not (s : ShapeExpr) : ShapeExpr

/-- The set of labels directly after `extends`, at *any* location in `s`.
The recursion goes through `or`, `and` and `not`, not only the top level.
The extension hierarchy `H_S` (Definition 3) uses this function. The
docstring of `ShexLean.Shex2025Inheritance.Syntax.ShapeExpr.extendsTargets`
tells why the recursion must go to each nesting depth, and not only to
the top-level `extends` clause of a well-formed `X` label. -/
def ShapeExpr.extendsTargets : ShapeExpr → Finset Label
  | .extends xs _ => xs
  | .constraint _ => ∅
  | .ofShape _ => ∅
  | .or s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .and s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .not s => s.extendsTargets

/-- A general form of `ext-te(x)`. If `def(x) = extends X hs [and u]`, the
result is the list of the triple expressions of all the shapes in `hs`.
(This is the discussion before rule 18 of Table 3, with one value for each
disjunct, not one value in total.)

If `s` does not have this form, the result is a junk value (`[]`). The
result has a meaning only for `x` with `s = S.shapeDef x`, where `x` is a
well-formed extendable label (`Schema.WellFormedX` below).

`extTeAt` (which rule 18 in `Semantics.lean` uses) takes an element of this
list by its index. In the case `hs = [h]` of the original paper, this list
always has one element. Thus, `extTeAt` at each index agrees with the
original `extTe`. -/
def ShapeExpr.extTeList : ShapeExpr → List TripleExpr
  | .extends _ hs => hs.map Shape.triples
  | .and (.extends _ hs) _ => hs.map Shape.triples
  | _ => []

/-- `ext-te(x)` at a selected disjunct index `i`. The index is taken modulo
the number of disjuncts. Thus, the function is total. On a well-formed,
nonempty `hs`, it never gives the junk default.

Rule 18 in `Semantics.lean` selects `i`. There is one witness
`pick : Label → ℕ` for each `.extends` occurrence, and all the ancestors
that this occurrence reaches use the same witness. The module docstring of
`Semantics.lean` tells why one shared choice for each occurrence is
sufficient to prevent the ambiguity of §6. -/
def ShapeExpr.extTeAt (s : ShapeExpr) (i : ℕ) : TripleExpr :=
  match s.extTeList with
  | [] => .empty
  | a :: rest => (a :: rest).get ⟨i % (a :: rest).length, Nat.mod_lt i (Nat.succ_pos rest.length)⟩

/-- On a singleton `hs = [h0]` (the restriction of the original paper, not
the relaxation that we examine here), `extTeAt` agrees with the original
`extTe` at *each* index `i`. This is the property "the singleton case
gives the original formalism" of the module docstring. -/
theorem ShapeExpr.extTeAt_one {xs : Finset Label} {h0 : Shape} (i : ℕ) :
    (ShapeExpr.extends xs [h0]).extTeAt i = h0.triples := by
  unfold ShapeExpr.extTeAt ShapeExpr.extTeList
  simp

/-- On `hs = [h0, h1]`, with two disjuncts, `extTeAt` selects `h0` at an
even index and `h1` at an odd index. This is the simplest case of the
relaxation (`⟨h0⟩ or ⟨h1⟩` in the surface syntax). -/
theorem ShapeExpr.extTeAt_two {xs : Finset Label} {h0 h1 : Shape} (i : ℕ) :
    (ShapeExpr.extends xs [h0, h1]).extTeAt i = if i % 2 = 0 then h0.triples else h1.triples := by
  unfold ShapeExpr.extTeAt ShapeExpr.extTeList
  simp only [List.map_cons, List.map_nil]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

/-- For *each* `s` and `i`, `extTeAt` gives one of these two results:

* The junk value `.empty`. This occurs only when `s.extTeList = []`. Thus,
  `s` does not have the form `.extends` or `.and (.extends _ _) _`, or it
  has one of these forms with `hs = []`. For a real `x ∈ S.X`,
  `Schema.WellFormedX` prevents the two cases.
* An element of `s.extTeList`.

`Termination.lean` uses this lemma to bound the syntax-tree size of
`extTeAt`, for each disjunct that `pick` selects. The statement uses
`extTeList` directly. Thus, it covers the two forms, `.extends xs hs` and
`.and (.extends xs hs) u`, in the same way. -/
theorem ShapeExpr.extTeAt_mem_or_empty (s : ShapeExpr) (i : ℕ) :
    s.extTeAt i = .empty ∨ ∃ e ∈ s.extTeList, s.extTeAt i = e := by
  unfold ShapeExpr.extTeAt
  cases s.extTeList with
  | nil => exact Or.inl rfl
  | cons a rest =>
      exact Or.inr ⟨_, List.get_mem (l := a :: rest)
        ⟨i % (a :: rest).length, Nat.mod_lt i (Nat.succ_pos _)⟩, rfl⟩

/-- `extTeAt` depends only on its index modulo the number of disjuncts.
(The modulus is at least 1, so that an empty `extTeList` is also covered.)
Thus, you can replace each `i` with its representative
`i % max 1 s.extTeList.length`, and the result does not change.

Because of this lemma, the existential over `pick : Label → ℕ` in rule 18
of `Semantics.lean` has a bound. For each ancestor, `Decidable.lean`
searches only over `Finset.range (max 1 s.extTeList.length)`. It uses this
lemma to show that the search loses no result: at each `x`, each `pick`
is equivalent to a bounded representative. -/
theorem ShapeExpr.extTeAt_mod (s : ShapeExpr) (i : ℕ) :
    s.extTeAt i = s.extTeAt (i % max 1 s.extTeList.length) := by
  unfold ShapeExpr.extTeAt
  cases hl : s.extTeList with
  | nil => rfl
  | cons a rest =>
      have hLpos : 0 < (a :: rest).length := Nat.succ_pos _
      have hmax : max 1 (a :: rest).length = (a :: rest).length := by omega
      simp only [hmax]
      congr 1
      apply Fin.eq_of_val_eq
      simp only
      rw [Nat.mod_mod]

/-- `restr(x)`: if `def(x) = extends X hs [and u]`, the optional `u`. The
result is `none` if there is no `and u` part. This agrees with "whenever
it exists" in the text of the paper. If `s` does not have this form, the
result is a junk value (`none`).

This is the same as in `ShexLean.Shex2025Inheritance.Syntax`. The only
change is that the second argument of `extends` is now `hs`, not `h`.
`restrOf` never looks at this argument. -/
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

/-- The second bullet of Definition 2, in a general form. For `x ∈ X`,
`def(x)` must have the form `extends X hs [and u]` with a *nonempty* `hs`.
Thus, it is `.extends xs hs` or `.and (.extends xs hs) u`, with `hs ≠ []`.

* `hs = [h]` is exactly the restriction of the original paper.
* `hs.length ≥ 2` is the relaxation that §6 does not accept, and that this
  folder examines.

The first bullet says "for `y ∈ Y`, `def(y)` is a plain shape expression".
This is automatically true here, as in the original formalism. -/
def Schema.WellFormedX (S : Schema) : Prop :=
  ∀ x ∈ S.X, ∃ xs hs, hs ≠ [] ∧
    (S.shapeDef x = .extends xs hs ∨ ∃ u, S.shapeDef x = .and (.extends xs hs) u)

/-- The edge relation of `H_S` in Definition 3. There is an edge from `x`
to `x'` if and only if `x'` comes directly after `extends` at the top of
`def(x)`. -/
abbrev Schema.extEdge (S : Schema) (x x' : Label) : Prop :=
  x' ∈ (S.shapeDef x).extendsTargets

/-- Definition 3 (extension hierarchy). `x' ∈ S.anc x` if and only if
there is a path (possibly empty) from `x` to `x'` in `H_S`. Thus, `x'` is
an ancestor of `x`, and `x` is a descendant of `x'`.

The result is restricted to `S.X` (the vertex set of `H_S`, as in
Definition 3). It has a meaning only for `x ∈ S.X`, as in the paper.
Classical choice decides the reachability predicate. (For a general
`Prop`-valued `extEdge`, this predicate is not decidable.) The 2017
formalization also uses `Classical.decPred` for similar filters. -/
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

end ShexLean.InheritanceDisjunction
