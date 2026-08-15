import ShexLean.RDF
import ShexLean.Typing
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Relation

/-!
Definitions 1–3 (§3) of Boneva, Labra Gayo, Prud'hommeaux, Thornton,
Waagmeester (2025), "Shape Expressions with Inheritance" (arXiv:2503.24299)
— the syntax of shape expressions with inheritance, ShEx schemas, and the
extension hierarchy.

This is a genuine second formalism, not a strict extension of
`ShexLean.Syntax` (the 2017 paper's `ShapeExpr`/`TripleExpr`): node
constraints are now an arbitrary boolean predicate rather than a concrete
`ValueDescr`, `closed`/`extra` are first-class shape modifiers rather than
the 2017 encoding trick, and `extends` is new. It lives in its own
`ShexLean.Inheritance` namespace so its `ShapeExpr`/`Schema`/etc. do not
clash with the 2017 ones, while reusing the paper-independent RDF/typing
vocabulary directly: `ShexLean.RDF` (`IRI`, `RDFNode`, `Triple`, `Graph`,
`neigh`) and `ShexLean.Typing` (`ShapeLabel`, `NodeTypeAssoc`, `Typing`,
`Typing.has`) are used completely unchanged — a "typing of `G` by `S`" is
literally the same notion in both papers (`Nodes(G) × (labels)`).

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

A reference `@z` is *not* modelled as its own `ShapeExpr` constructor here.
Definition 1's grammar for `u` (the set a schema's `def` actually maps
labels into) has no `@z` alternative — references only ever occur nested
inside a triple constraint `p @z` (`TripleExpr.tc`), where Table 2's own
rule 10 (`@z: (n,z) ∈ τ`) is a *typing lookup with zero further
recursion*, exactly like Rule te-tpattern's `typing.has obj L` in the 2017
formalization (`ShexLean/Semantics.lean`). So it is inlined directly at
`TripleExpr.tc`'s satisfaction rule in `Semantics.lean` instead of being
threaded through as a genuine recursive `ShapeExpr` case.

The `t ::= extends X h .` grammar production also has no `[and u]`: a
label's optional restriction after `extends X h and u` (Definition 2's
prose) is just the generic `u and u/` production instantiated with the
first operand being `t` — i.e. `ShapeExpr.and (ShapeExpr.extends X h) u`,
reusing the generic `and` constructor rather than a dedicated field on
`extends`. `ShapeExpr.extTe`/`ShapeExpr.restrOf` below extract the paper's
`ext-te(x)`/`restr(x)` notations (Table 3, rule 18) from either the bare
`extends X h` or the `(extends X h) and u` shape.
-/

namespace ShexLean.Inheritance

/-- Def 1's node constraint `c`: "a boolean function over
IRI ∪ Blank ∪ Literal", i.e. over `RDFNode`. Left fully abstract, matching
the paper (unlike the 2017 formalization's concrete `ValueDescr`). -/
abbrev NodeConstraint := RDFNode → Prop

/-- Def 1's triple expression grammar,
`e ::= ε | p @z | e|e | e;e | e*`. `tc p z` is the triple constraint
`p @z`; `z` ranges over `ShapeLabel` (reused from `ShexLean.Typing`), i.e.
over `Y ∪ X` for whichever schema the expression belongs to. -/
inductive TripleExpr where
  | empty : TripleExpr
  | tc (p : IRI) (z : ShapeLabel) : TripleExpr
  | choice (e1 e2 : TripleExpr) : TripleExpr
  | seq (e1 e2 : TripleExpr) : TripleExpr
  | star (e : TripleExpr) : TripleExpr
  deriving DecidableEq

/-- The triple-constraint sub-expressions of `e` (the paper's `tcs(e)`),
represented as `(property, target label)` pairs. -/
def TripleExpr.tcs : TripleExpr → Finset (IRI × ShapeLabel)
  | .empty => ∅
  | .tc p z => {(p, z)}
  | .choice e1 e2 => e1.tcs ∪ e2.tcs
  | .seq e1 e2 => e1.tcs ∪ e2.tcs
  | .star e => e.tcs

/-- The properties used in `e`'s triple constraints (the paper's
`props(e)`). -/
def TripleExpr.props (e : TripleExpr) : Finset IRI := e.tcs.image Prod.fst

/-- Def 1's shape `h ::= [closed] [extra P] ⟨e⟩`. `extra := none` when
absent (so `P' = ∅` in Table 3's rule 17), `extra := some P` when present. -/
structure Shape where
  closed : Bool
  extra  : Option (Finset IRI)
  triples : TripleExpr
  deriving DecidableEq

/-- Def 1's shape expression grammar (`u`/`t`/`c`/boolean connectives),
i.e. everything a schema's `def` can map a label to. See the module
docstring for why `@z` is not a constructor and why `extends` has no
`restr` field of its own. -/
inductive ShapeExpr where
  | ofShape (h : Shape) : ShapeExpr
  | extends (xs : Finset ShapeLabel) (h : Shape) : ShapeExpr
  | constraint (c : NodeConstraint) : ShapeExpr
  | or (s1 s2 : ShapeExpr) : ShapeExpr
  | and (s1 s2 : ShapeExpr) : ShapeExpr
  | not (s : ShapeExpr) : ShapeExpr

/-- The set of labels named right after `extends`, *anywhere* in `s`
(recursing through `or`/`and`/`not`, not just at the very top). Used to
build the extension hierarchy `H_S` (Definition 3).

Definition 3's own phrasing only mentions a label's *outermost*
`extends X h [and u]` clause, but the grammar doesn't actually confine
`extends` to that position — `u` (or, for that matter, a `Y`-label's
unrestricted definition) can syntactically contain a further, nested
`extends` under `or`/`and`/`not`, and Table 3's rule 18 (`ShexLean/
Inheritance/Semantics.lean`) fires on *any* `.extends` node it structurally
reaches, regardless of nesting. Recursing through the whole tree here — the
same way `ShapeExpr.depsAux` (`ShexLean/Inheritance/Stratification.lean`)
already has to for ordinary references — is what makes `Schema.extEdge`/
`H_S`/`D_S` actually track everything the evaluator can dereference; the
top-level-only version originally here undercounted edges out of any label
whose `extends` isn't literally at the top (in particular every `Y`-label,
since only `X`-labels are forced into the shallow top-level form by
`Schema.WellFormedX`), which is unsound for anything reasoning about the
*schema's* dependency structure (`ShexLean/Inheritance/Proposition1.lean`'s
agreement lemma) even though it happened not to matter for
`ShexLean/Inheritance/Termination.lean` (whose `Fuel` bookkeeping walks the
whole tree independently via `ShapeExpr.reqFuel`, not through this
function at all). -/
def ShapeExpr.extendsTargets : ShapeExpr → Finset ShapeLabel
  | .extends xs _ => xs
  | .constraint _ => ∅
  | .ofShape _ => ∅
  | .or s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .and s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .not s => s.extendsTargets

/-- `ext-te(x)`: assuming `def(x) = extends X h [and u]`, the triple
expression of `h` (Table 3's discussion before rule 18). Junk value
(`.empty`) when `s` is not of that form — only ever meaningful for `x`
with `s = S.shapeDef x` and `x` a well-formed extendable label
(`Schema.WellFormedX` below). -/
def ShapeExpr.extTe : ShapeExpr → TripleExpr
  | .extends _ h => h.triples
  | .and (.extends _ h) _ => h.triples
  | _ => .empty

/-- `restr(x)`: assuming `def(x) = extends X h [and u]`, the optional `u`
(`none` if the `and u` part is absent, matching "whenever it exists" in
the paper's prose). Junk value (`none`) when `s` is not of that form. -/
def ShapeExpr.restrOf : ShapeExpr → Option ShapeExpr
  | .and (.extends _ _) u => some u
  | _ => none

/-- Definition 2 (ShEx schema). `S = (Y, X, def, A)`: `Y` simple labels,
`X` extendable labels disjoint from `Y`, `A ⊆ X` abstract labels, and
`shapeDef` (the paper's `def`) associates every label of `Y ∪ X` with its
definition. `shapeDef` is total on all of `ShapeLabel` (as in the 2017
formalization) because Lean functions must be total; `Schema.WellFormedX`
below is the extra hypothesis this forces (mirroring `Schema.Closed` in
`ShexLean/Proposition1.lean`). -/
structure Schema where
  Y : Finset ShapeLabel
  X : Finset ShapeLabel
  A : Finset ShapeLabel
  disjointYX : Disjoint Y X
  A_subX : A ⊆ X
  shapeDef : ShapeLabel → ShapeExpr

/-- Definition 2's second bullet: for `x ∈ X`, `def(x)` must be of the
form `extends X h [and u]`, i.e. `.extends xs h` or
`.and (.extends xs h) u`. (The first bullet, "for `y ∈ Y`, `def(y)` is a
plain shape expression", is automatic here: since `ShapeExpr` has no `@z`
constructor, *every* `ShapeExpr` value already is one, per the module
docstring.) -/
def Schema.WellFormedX (S : Schema) : Prop :=
  ∀ x ∈ S.X, ∃ xs h, S.shapeDef x = .extends xs h ∨ ∃ u, S.shapeDef x = .and (.extends xs h) u

/-- Definition 3's edge relation of `H_S`: an edge from `x` to `x'` iff
`x'` is named right after `extends` at the top of `def(x)`. -/
def Schema.extEdge (S : Schema) (x x' : ShapeLabel) : Prop :=
  x' ∈ (S.shapeDef x).extendsTargets

/-- Definition 3 (extension hierarchy). `x' ∈ S.anc x` iff there is a
(possibly empty) path from `x` to `x'` in `H_S`, i.e. `x'` is an ancestor
of `x` (equivalently `x` is a descendant of `x'`). Restricted to `S.X`
(`H_S`'s vertex set, per Definition 3); only meaningful for `x ∈ S.X`,
matching the paper. Classical choice decides the (in general undecidable
for an arbitrary `Prop`-valued `extEdge`) reachability predicate, exactly
as `Classical.decPred` is used throughout the 2017 formalization for
similar non-obviously-decidable filters. -/
noncomputable def Schema.anc (S : Schema) (x : ShapeLabel) : Finset ShapeLabel :=
  haveI := Classical.decPred (Relation.ReflTransGen S.extEdge x)
  S.X.filter (Relation.ReflTransGen S.extEdge x)

/-- `S.desc x`: the descendants of `x` (dual of `S.anc`). -/
noncomputable def Schema.desc (S : Schema) (x : ShapeLabel) : Finset ShapeLabel :=
  haveI := Classical.decPred (Relation.ReflTransGen S.extEdge · x)
  S.X.filter (Relation.ReflTransGen S.extEdge · x)

/-- `anc(X) = ⋃_{x ∈ X} anc(x)` (Table 3's extension of `anc` to a set of
labels, used by rule 18). -/
noncomputable def Schema.ancSet (S : Schema) (xs : Finset ShapeLabel) : Finset ShapeLabel :=
  xs.biUnion S.anc

end ShexLean.Inheritance
