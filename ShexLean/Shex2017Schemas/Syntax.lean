import ShexLean.Common.RDF
import ShexLean.Common.Typing
import Mathlib.Data.Finset.Basic

/-!
The grammar of shape expressions and triple expressions, Fig. 1 of Boneva,
Labra Gayo, Prud'hommeaux (2017):

```
ShExpr  ::= ValueDescr | NeigDescr                 TExpr        ::= TriplePattern | 'EMPTY'
          | ShapeAnd | ShapeOr | ShapeNot                        | SomeOfExpr | EachOfExpr
ValueDescr ::= a subset of IRI ∪ Lit ∪ {_b}                      | RepetExpr
NeigDescr  ::= TExpr                               TriplePattern ::= PropSet '@'ShapeRef
ShapeAnd   ::= ShExpr 'AND' ShExpr                 SomeOfExpr    ::= TExpr '|' TExpr
ShapeOr    ::= ShExpr 'OR' ShExpr                  EachOfExpr    ::= TExpr ';' TExpr
ShapeNot   ::= 'NOT' ShExpr                        RepetExpr     ::= TExpr '[' min ';' max ']'
                                                    PropSet       ::= a subset of IRI
                                                    ShapeRef      ::= a shape label in L
```

A shapes schema `S` is a pair `(L, def)`, where `L` is a set of shape labels
and `def` associates a shape expression with every label.
-/

namespace ShexLean

/-- An element of a `ValueDescr`: an IRI, a literal, or the special constant
`_b` standing for "any blank node". -/
inductive ValueItem where
  | iri      : IRI → ValueItem
  | lit      : Literal → ValueItem
  | anyBlank : ValueItem
  deriving DecidableEq, Repr

/-- `ValueDescr`: an arbitrary (finite) subset of `IRI ∪ Lit ∪ {_b}`. -/
abbrev ValueDescr := Finset ValueItem

/-- `PropSet`: an arbitrary (finite) subset of `IRI`. -/
abbrev PropSet := Finset IRI

mutual
/-- A shape expression, i.e. a Boolean combination of a value description and
a neighbourhood description. -/
inductive ShExpr where
  /-- `ValueDescr`: constrains the value of the node itself. -/
  | valueDescr : ValueDescr → ShExpr
  /-- `NeigDescr`: constrains the neighbourhood of the node via a triple
  expression. -/
  | neigDescr  : TExpr → ShExpr
  /-- `ShapeAnd`. -/
  | and        : ShExpr → ShExpr → ShExpr
  /-- `ShapeOr`. -/
  | or         : ShExpr → ShExpr → ShExpr
  /-- `ShapeNot`. -/
  | not        : ShExpr → ShExpr

/-- A triple expression, describing the expected neighbourhood of a node. -/
inductive TExpr where
  /-- `TriplePattern P @L`: a set of properties `P` paired with a shape
  reference `L` that the matched object must satisfy. -/
  | tPattern : PropSet → Label → TExpr
  /-- `EMPTY`: matched only by the empty set of triples. -/
  | empty    : TExpr
  /-- `SomeOfExpr E1 | E2`. -/
  | someOf   : TExpr → TExpr → TExpr
  /-- `EachOfExpr E1 ; E2`. -/
  | eachOf   : TExpr → TExpr → TExpr
  /-- `RepetExpr E [min; max]`; `none` for `max` stands for `*`. -/
  | rep      : TExpr → Nat → Option Nat → TExpr
end

/-- A shapes schema `S = (L, def)`. -/
structure Schema where
  /-- `L`: the set of shape labels used as names of shapes. -/
  labels   : Finset Label
  /-- `def`: associates a shape expression with every shape label. -/
  shapeDef : Label → ShExpr

end ShexLean
