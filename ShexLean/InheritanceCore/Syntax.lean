import ShexLean.Common.RDF
import ShexLean.Common.Typing
import Mathlib.Data.Finset.Image

/-!
The parts of the syntax of "Shape Expressions with Inheritance" (Boneva,
Labra Gayo, Prud'hommeaux, Thornton, Waagmeester, 2025, Definition 1) that
do not depend on the payload of `extends`:

* Node constraints `c`.
* Triple expressions `e ::= ε | p @z | e|e | e;e | e*`.
* Shapes `h ::= [closed] [extra P] ⟨e⟩`.
* The dependency information of a shape (Definition 5).

Two developments use these definitions:

* `ShexLean/Shex2025Inheritance/` (the paper: `extends X h`).
* `ShexLean/Shex2026InheritanceDisjunction/` (the exploration:
  `extends X hs`, with a list of shapes).

Each development defines its own `ShapeExpr` and `Schema` on top of them.
-/

namespace ShexLean.InheritanceCore

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

/-! ### The dependency information of a shape (Definition 5) -/

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

/-- The labels that the triple constraints of a triple expression refer
to. -/
def TripleExpr.refs (e : TripleExpr) : Finset Label := e.tcs.image Prod.snd

theorem Shape.refs_eq (h : Shape) (neg : Bool) : (h.depInfo neg).refs = h.triples.refs := by
  simp [Shape.depInfo, TripleExpr.refs]

/-- The implicit invariant "(*)" of Definition 5: the triple constraints of
a shape never use a property that is also in its `extra` set. -/
def Shape.WellFormedExtra (h : Shape) : Prop := h.triples.props ∩ h.extra.getD ∅ = ∅

end ShexLean.InheritanceCore
