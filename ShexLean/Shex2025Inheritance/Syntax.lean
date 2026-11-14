import ShexLean.Common.RDF
import ShexLean.Common.Typing
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Relation
import ShexLean.InheritanceCore.Schema

/-!
Definitions 1–3 (§3) of Boneva, Labra Gayo, Prud'hommeaux, Thornton,
Waagmeester (2025), "Shape Expressions with Inheritance" (arXiv:2503.24299).
These definitions give:

* The syntax of shape expressions with inheritance.
* ShEx schemas.
* The extension hierarchy.

This formalism is different from `ShexLean.Syntax`
(the `ShapeExpr` and `TripleExpr` of the 2017 paper).
It is not a strict extension of it:

* A node constraint is a Boolean predicate, not a concrete `ValueDescr`.
* `closed` and `extra` are shape modifiers in the syntax.
  In 2017, they were an encoding.
* `extends` is new.

It is in its own namespace, `ShexLean.Inheritance`, so
that its names do not conflict with the 2017 definitions.
It uses, with no change, the RDF and typing vocabulary that does not depend on a paper:

* `ShexLean.RDF` (`IRI`, `RDFNode`, `Triple`, `Graph`, `neigh`).
* `ShexLean.Typing` (`Label`, `Assoc`, `Typing`, `Typing.has`).

A "typing of `G` by `S`" has the same meaning in the two papers.

The node constraints, triple expressions and shapes do not depend on the payload of `extends`.
They are in `ShexLean/InheritanceCore/Syntax.lean` (namespace
`ShexLean.InheritanceCore`), which the 2026 exploration also uses.
This file defines `ShapeExpr` and `Schema` on top of them.

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

A reference `@z` is not a `ShapeExpr` constructor.
The grammar of `u` in Definition 1 has no `@z` alternative.
(A schema's `def` maps labels to `u`.)
A reference occurs only inside a triple constraint `p @z` (`TripleExpr.tc`).
There, rule 10 of Table 2 (`@z: (n,z) ∈ τ`) is a typing lookup with no more recursion.
This agrees with `typing.has obj L` of Rule te-tpattern in the
2017 formalization (`ShexLean/Shex2017Schemas/Semantics.lean`).
`Semantics.lean` puts it directly in the satisfaction rule of `TripleExpr.tc`.

The production `t ::= extends X h .` has no `[and u]` field.
In the text of Definition 2, a label can have an optional restriction: `extends X h and u`.
This is the general production `u and u`, where the first operand is `t`.
Thus, it is `ShapeExpr.and (ShapeExpr.extends X h) u`.
`ShapeExpr.extTe` and `ShapeExpr.restrOf` below get the
`ext-te(x)` and `restr(x)` of the paper (Table 3, rule 18)
from the two forms: `extends X h` and `(extends X h) and u`.
-/

namespace ShexLean.Inheritance

open ShexLean.InheritanceCore hiding Schema

/-- The grammar of shape expressions of Def 1 (`u`, `t`, `c` and the Boolean connectives).
This is all that the `def` of a schema can map a label to.
Refer to the module docstring to know why `@z` is not
a constructor, and why `extends` has no `restr` field. -/
inductive ShapeExpr where
  | ofShape (h : Shape) : ShapeExpr
  | extends (xs : Finset Label) (h : Shape) : ShapeExpr
  | constraint (c : NodeConstraint) : ShapeExpr
  | or (s1 s2 : ShapeExpr) : ShapeExpr
  | and (s1 s2 : ShapeExpr) : ShapeExpr
  | not (s : ShapeExpr) : ShapeExpr

/-- The labels after `extends`, at any location in `s`.
The recursion goes through `or`, `and` and `not`, not only the top level.
The extension hierarchy `H_S` (Definition 3) uses this function.

The text of Definition 3 describes only the outermost `extends X h [and u]` clause of a label.
But the grammar does not keep `extends` only at that location.
`u` can contain a nested `extends`, and rule 18 of Table 3
(`Semantics.lean`) applies to each `.extends` node that it gets to.
Thus, the function must go through the full tree, as `ShapeExpr.depsAux`
(`Stratification.lean`) already does for references.
Then `Schema.extEdge`, `H_S` and `D_S` record each `extends` that the evaluator can dereference.
This includes an `extends` nested in the definition of a `Y` label. -/
def ShapeExpr.extendsTargets : ShapeExpr → Finset Label
  | .extends xs _ => xs
  | .constraint _ => ∅
  | .ofShape _ => ∅
  | .or s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .and s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .not s => s.extendsTargets

/-- `ext-te(x)`: if `def(x) = extends X h [and u]`, the triple
expression of `h` (Table 3, the discussion before rule 18).
If `s` does not have this form, the result is a junk value (`.empty`).
The result has a meaning only for `x` with `s = S.shapeDef x`, where
`x` is a well-formed extendable label (`Schema.WellFormedX` below). -/
def ShapeExpr.extTe : ShapeExpr → TripleExpr
  | .extends _ h => h.triples
  | .and (.extends _ h) _ => h.triples
  | _ => .empty

/-- `restr(x)`: if `def(x) = extends X h [and u]`, the optional `u`.
The result is `none` if there is no `and u` part.
This agrees with "whenever it exists" in the text of the paper.
If `s` does not have this form, the result is a junk value (`none`). -/
def ShapeExpr.restrOf : ShapeExpr → Option ShapeExpr
  | .and (.extends _ _) u => some u
  | _ => none

/-- Definition 2 (ShEx schema) `S = (Y, X, def, A)`, with the shape expressions of this file.
`ShexLean.InheritanceCore.Schema` gives the fields, the extension
hierarchy `H_S` (Definition 3: `anc`, `desc`, `ancSet`) and the dependency
graph `D_S` (Definition 5), for each type of shape expressions. -/
abbrev Schema := InheritanceCore.Schema ShapeExpr

/-- The second bullet of Definition 2: for `x ∈ X`,
`def(x)` must have the form `extends X h [and u]`.
Thus, it is `.extends xs h` or `.and (.extends xs h) u`.

The first bullet says "for `y ∈ Y`, `def(y)` is a plain shape expression".
This is automatically true here, because `ShapeExpr` has no `@z` constructor.
Thus, each `ShapeExpr` value is a plain shape expression. -/
def Schema.WellFormedX (S : Schema) : Prop :=
  ∀ x ∈ S.X, ∃ xs h, S.shapeDef x = .extends xs h ∨ ∃ u, S.shapeDef x = .and (.extends xs h) u

/-- `restr(x) = some u` exactly when `def(x)` has the form `extends X h and u`.
The proofs about `restr(x)` use this lemma, and do not do a case analysis on `ShapeExpr` again. -/
theorem ShapeExpr.restrOf_eq_some {s u : ShapeExpr} :
    s.restrOf = some u ↔ ∃ xs h, s = .and (.extends xs h) u := by
  constructor
  · intro hs
    rcases s with _ | _ | _ | _ | ⟨s1, s2⟩ | _ <;> try simp [ShapeExpr.restrOf] at hs
    cases s1 <;> simp_all
  · rintro ⟨xs, h, rfl⟩; rfl

end ShexLean.Inheritance
