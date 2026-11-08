import ShexLean.Common.RDF
import ShexLean.Common.Typing
import Mathlib.Data.Finset.Basic

/-!
The grammar of shape expressions and triple expressions. This is Fig. 1 of
Boneva, Labra Gayo, Prud'hommeaux (2017):

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

A shapes schema `S` is a pair `(L, def)`. `L` is a set of shape labels.
`def` gives a shape expression to each label.
-/

namespace ShexLean

/-- An element of a `ValueDescr`: an IRI, a literal, or the special
constant `_b`. The constant `_b` means "any blank node". -/
inductive ValueItem where
  | iri      : IRI → ValueItem
  | lit      : Literal → ValueItem
  | anyBlank : ValueItem
  deriving DecidableEq, Repr

/-- `ValueDescr`: a finite subset of `IRI ∪ Lit ∪ {_b}`. -/
abbrev ValueDescr := Finset ValueItem

/-- `PropSet`: a finite subset of `IRI`. -/
abbrev PropSet := Finset IRI

mutual
/-- A shape expression: a Boolean combination of value descriptions and
neighbourhood descriptions. -/
inductive ShExpr where
  /-- `ValueDescr`: a constraint on the value of the node. -/
  | valueDescr : ValueDescr → ShExpr
  /-- `NeigDescr`: a constraint on the neighbourhood of the node, with a
  triple expression. -/
  | neigDescr  : TExpr → ShExpr
  /-- `ShapeAnd`. -/
  | and        : ShExpr → ShExpr → ShExpr
  /-- `ShapeOr`. -/
  | or         : ShExpr → ShExpr → ShExpr
  /-- `ShapeNot`. -/
  | not        : ShExpr → ShExpr

/-- A triple expression. It describes the expected neighbourhood of a
node. -/
inductive TExpr where
  /-- `TriplePattern P @L`: a set of properties `P` and a shape reference
  `L`. The object of each matched triple must satisfy `L`. -/
  | tPattern : PropSet → Label → TExpr
  /-- `EMPTY`: only the empty set of triples matches it. -/
  | empty    : TExpr
  /-- `SomeOfExpr E1 | E2`. -/
  | someOf   : TExpr → TExpr → TExpr
  /-- `EachOfExpr E1 ; E2`. -/
  | eachOf   : TExpr → TExpr → TExpr
  /-- `RepetExpr E [min; max]`. If `max` is `none`, it means `*`. -/
  | rep      : TExpr → Nat → Option Nat → TExpr
end

/-- A shapes schema `S = (L, def)`. -/
structure Schema where
  /-- `L`: the set of shape labels. The labels are the names of the
shapes. -/
  labels   : Finset Label
  /-- `def`: gives a shape expression to each shape label. -/
  shapeDef : Label → ShExpr

end ShexLean
