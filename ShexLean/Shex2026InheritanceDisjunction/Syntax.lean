import ShexLean.Common.RDF
import ShexLean.Common.Typing
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Relation

/-!
An exploratory variant of `ShexLean.Shex2025Inheritance` (Definitions 1–3, §3,
of Boneva, Labra Gayo, Prud'hommeaux, Thornton, Waagmeester (2025), "Shape
Expressions with Inheritance", arXiv:2503.24299), investigating the design
choice the paper explicitly declines in §6 ("Design Choices"):

> We impose a syntactic restriction on extendable shape expressions. They
> must be conjunctions of a shape and a plain shape expression. [...] extending
> on disjunctions together with multiple inheritance complicates the
> definition of the satisfaction relation [...] this would require (1)
> recording which one of the disjuncts [...] has been satisfied by each
> subtype [...] and (2) checking whether all the subtypes satisfy the same
> disjunct. We decided to take a conservative approach and limit the shape
> expressions that can be extended.

Here `extends X h` is generalized so `h` ranges over a *nonempty list* of
plain shapes (`hs : List Shape`, ` s1 or s2 or ...` in the paper's surface
syntax) rather than a single `Shape` — precisely the relaxation §6 declines.
A singleton list (`hs = [h]`) reproduces the original paper's grammar
exactly, so the unmodified formalism is the `hs.length = 1` special case of
this one; every definition below that only ever needs `hs`'s *set of
possible triple expressions* is written to specialize back to the original
one verbatim in that case.

The actual ambiguity §6 describes, and the fix explored here (see
`Semantics.lean`'s rule 18), only shows up once a `.extends` node is
*resolved as someone else's ancestor* (`ext-te(x)`, Table 3) — resolving it
directly (Table 3 rule 17-via-18's own `M', τ ⊨ h`) is unambiguous already,
since `or` already has an ordinary satisfaction rule (rule 14) that lets a
*single* node pick either disjunct with no cross-node consistency question.

Otherwise unchanged from `ShexLean.Shex2025Inheritance.Syntax`: lives in its
own `ShexLean.InheritanceDisjunction` namespace (parallel to
`ShexLean.Inheritance`) so its `ShapeExpr`/`Schema`/etc. do not clash with
either the 2017 or the (unmodified) 2025 formalization, while reusing the
paper-independent RDF/typing vocabulary directly.

> Definition 1 (shape expressions, as modified here). u ::= h | t | c | u or
> u | u and u | not u . h ::= [closed] [extra P] ⟨e⟩ . t ::= extends X h or h
> or ... or h . (nonempty disjunction of shapes, generalizing the paper's
> `t ::= extends X h`) c ::= a boolean function over IRI ∪ Blank ∪ Literal .
> e ::= ε | p @z | e|e | e;e | e* .
-/

namespace ShexLean.InheritanceDisjunction

/-- Def 1's node constraint `c`: "a boolean function over
IRI ∪ Blank ∪ Literal", i.e. over `RDFNode`. Left fully abstract, matching
the paper (unlike the 2017 formalization's concrete `ValueDescr`). -/
abbrev NodeConstraint := RDFNode → Prop

/-- Def 1's triple expression grammar,
`e ::= ε | p @z | e|e | e;e | e*`. `tc p z` is the triple constraint
`p @z`; `z` ranges over `Label` (reused from `ShexLean.Typing`), i.e.
over `Y ∪ X` for whichever schema the expression belongs to. -/
inductive TripleExpr where
  | empty : TripleExpr
  | tc (p : IRI) (z : Label) : TripleExpr
  | choice (e1 e2 : TripleExpr) : TripleExpr
  | seq (e1 e2 : TripleExpr) : TripleExpr
  | star (e : TripleExpr) : TripleExpr
  deriving DecidableEq

/-- The triple-constraint sub-expressions of `e` (the paper's `tcs(e)`),
represented as `(property, target label)` pairs. -/
def TripleExpr.tcs : TripleExpr → Finset (IRI × Label)
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

/-- Def 1's shape expression grammar (`u`/`t`/`c`/boolean connectives), i.e.
everything a schema's `def` can map a label to. `extends`'s second argument
is now a *nonempty list* of shapes (`hs`, `Schema.WellFormedX` requires
`hs ≠ []`) instead of the original paper's single `Shape` — see the module
docstring. See `ShexLean.Shex2025Inheritance.Syntax`'s module docstring for
why `@z` is not a constructor and why `extends` has no `restr` field of its
own; both carry over unchanged here. -/
inductive ShapeExpr where
  | ofShape (h : Shape) : ShapeExpr
  | extends (xs : Finset Label) (hs : List Shape) : ShapeExpr
  | constraint (c : NodeConstraint) : ShapeExpr
  | or (s1 s2 : ShapeExpr) : ShapeExpr
  | and (s1 s2 : ShapeExpr) : ShapeExpr
  | not (s : ShapeExpr) : ShapeExpr

/-- The set of labels named right after `extends`, *anywhere* in `s`
(recursing through `or`/`and`/`not`, not just at the very top). Used to
build the extension hierarchy `H_S` (Definition 3). See
`ShexLean.Shex2025Inheritance.Syntax.ShapeExpr.extendsTargets`'s docstring
for why the recursion has to reach every nesting depth, not just the
top-level `extends` clause a well-formed `X`-label is confined to. -/
def ShapeExpr.extendsTargets : ShapeExpr → Finset Label
  | .extends xs _ => xs
  | .constraint _ => ∅
  | .ofShape _ => ∅
  | .or s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .and s1 s2 => s1.extendsTargets ∪ s2.extendsTargets
  | .not s => s.extendsTargets

/-- `ext-te(x)` generalized: assuming `def(x) = extends X hs [and u]`, the
list of triple expressions of every shape in `hs` (Table 3's discussion
before rule 18, generalized from a single value to one-per-disjunct). Junk
value (`[]`) when `s` is not of that form — only ever meaningful for `x`
with `s = S.shapeDef x` and `x` a well-formed extendable label
(`Schema.WellFormedX` below). `extTeAt`, used by `Semantics.lean`'s rule 18,
indexes into this list; on the original paper's `hs = [h]` case this list is
always a singleton, so `extTeAt` at any index agrees with the original
`extTe`. -/
def ShapeExpr.extTeList : ShapeExpr → List TripleExpr
  | .extends _ hs => hs.map Shape.triples
  | .and (.extends _ hs) _ => hs.map Shape.triples
  | _ => []

/-- `ext-te(x)` at a chosen disjunct index `i` (mod the number of
disjuncts, so it's total and — on a well-formed, nonempty `hs` — never hits
the junk default). See `Semantics.lean`'s rule 18 for how `i` is chosen
(one `pick : Label → ℕ` witness per `.extends` occurrence, shared
across every ancestor that occurrence reaches) and the module docstring
there for why a single shared choice per occurrence is enough to rule out
the §6 ambiguity. -/
def ShapeExpr.extTeAt (s : ShapeExpr) (i : ℕ) : TripleExpr :=
  match s.extTeList with
  | [] => .empty
  | a :: rest => (a :: rest).get ⟨i % (a :: rest).length, Nat.mod_lt i (Nat.succ_pos rest.length)⟩

/-- On a singleton `hs = [h0]` (the original paper's own restriction, not
the relaxation explored here), `extTeAt` agrees with the original `extTe`
at *every* index `i` — this is the "singleton case reduces to the
unmodified formalism" property promised in the module docstring. -/
theorem ShapeExpr.extTeAt_one {xs : Finset Label} {h0 : Shape} (i : ℕ) :
    (ShapeExpr.extends xs [h0]).extTeAt i = h0.triples := by
  unfold ShapeExpr.extTeAt ShapeExpr.extTeList
  simp

/-- On a two-disjunct `hs = [h0, h1]` (the simplest genuinely-relaxed case,
`⟨h0⟩ or ⟨h1⟩` in the surface syntax), `extTeAt` picks `h0` on an even index
and `h1` on an odd one. -/
theorem ShapeExpr.extTeAt_two {xs : Finset Label} {h0 h1 : Shape} (i : ℕ) :
    (ShapeExpr.extends xs [h0, h1]).extTeAt i = if i % 2 = 0 then h0.triples else h1.triples := by
  unfold ShapeExpr.extTeAt ShapeExpr.extTeList
  simp only [List.map_cons, List.map_nil]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

/-- For *any* `s`/`i`, `extTeAt` either falls back to the junk `.empty`
(only when `s.extTeList = []`, i.e. `s` isn't of the `.extends`/`.and
(.extends _ _) _` form at all, or is one of those with `hs = []` — both
ruled out for a genuine `x ∈ S.X` by `Schema.WellFormedX`) or is literally
an element of `s.extTeList` — used by `Termination.lean` to bound
`extTeAt`'s AST size regardless of which disjunct `pick` selects. Stated
directly in terms of `extTeList` so it covers both the bare `.extends xs
hs` and the `.and (.extends xs hs) u` shape uniformly. -/
theorem ShapeExpr.extTeAt_mem_or_empty (s : ShapeExpr) (i : ℕ) :
    s.extTeAt i = .empty ∨ ∃ e ∈ s.extTeList, s.extTeAt i = e := by
  unfold ShapeExpr.extTeAt
  cases s.extTeList with
  | nil => exact Or.inl rfl
  | cons a rest =>
      exact Or.inr ⟨_, List.get_mem (l := a :: rest)
        ⟨i % (a :: rest).length, Nat.mod_lt i (Nat.succ_pos _)⟩, rfl⟩

/-- `extTeAt` only ever depends on its index mod (at least 1, to survive an
empty `extTeList`) the disjunct count — so any `i` can be replaced by its
representative `i % max 1 s.extTeList.length` without changing the result.
This is exactly what makes the `pick : Label → ℕ` existential in
`Semantics.lean`'s rule 18 *boundable*: `Decidable.lean` searches only over
`Finset.range (max 1 s.extTeList.length)` for each ancestor, using this
lemma to show that's lossless (every `pick` is equivalent, at each `x`, to
some bounded representative). -/
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

/-- `restr(x)`: assuming `def(x) = extends X hs [and u]`, the optional `u`
(`none` if the `and u` part is absent, matching "whenever it exists" in the
paper's prose). Junk value (`none`) when `s` is not of that form. Unchanged
from `ShexLean.Shex2025Inheritance.Syntax` other than `extends`'s second
argument now being `hs` instead of `h`, which `restrOf` never inspects. -/
def ShapeExpr.restrOf : ShapeExpr → Option ShapeExpr
  | .and (.extends _ _) u => some u
  | _ => none

/-- Definition 2 (ShEx schema). `S = (Y, X, def, A)`: `Y` simple labels,
`X` extendable labels disjoint from `Y`, `A ⊆ X` abstract labels, and
`shapeDef` (the paper's `def`) associates every label of `Y ∪ X` with its
definition. `shapeDef` is total on all of `Label` (as in the 2017
formalization) because Lean functions must be total; `Schema.WellFormedX`
below is the extra hypothesis this forces (mirroring `Schema.Closed` in
`ShexLean/Shex2017Schemas/Proposition1.lean`). -/
structure Schema where
  Y : Finset Label
  X : Finset Label
  A : Finset Label
  disjointYX : Disjoint Y X
  A_subX : A ⊆ X
  shapeDef : Label → ShapeExpr

/-- Definition 2's second bullet, generalized: for `x ∈ X`, `def(x)` must be
of the form `extends X hs [and u]` with `hs` *nonempty* — i.e. `.extends xs
hs` or `.and (.extends xs hs) u`, `hs ≠ []`. (`hs = [h]` is exactly the
original paper's restriction; `hs.length ≥ 2` is the §6-declined relaxation
this folder explores.) The first bullet, "for `y ∈ Y`, `def(y)` is a plain
shape expression", is automatic here exactly as in the unmodified
formalism. -/
def Schema.WellFormedX (S : Schema) : Prop :=
  ∀ x ∈ S.X, ∃ xs hs, hs ≠ [] ∧
    (S.shapeDef x = .extends xs hs ∨ ∃ u, S.shapeDef x = .and (.extends xs hs) u)

/-- Definition 3's edge relation of `H_S`: an edge from `x` to `x'` iff
`x'` is named right after `extends` at the top of `def(x)`. -/
abbrev Schema.extEdge (S : Schema) (x x' : Label) : Prop :=
  x' ∈ (S.shapeDef x).extendsTargets

/-- Definition 3 (extension hierarchy). `x' ∈ S.anc x` iff there is a
(possibly empty) path from `x` to `x'` in `H_S`, i.e. `x'` is an ancestor
of `x` (equivalently `x` is a descendant of `x'`). Restricted to `S.X`
(`H_S`'s vertex set, per Definition 3); only meaningful for `x ∈ S.X`,
matching the paper. Classical choice decides the (in general undecidable
for an arbitrary `Prop`-valued `extEdge`) reachability predicate, exactly
as `Classical.decPred` is used throughout the 2017 formalization for
similar non-obviously-decidable filters. -/
noncomputable def Schema.anc (S : Schema) (x : Label) : Finset Label :=
  haveI := Classical.decPred (Relation.ReflTransGen S.extEdge x)
  S.X.filter (Relation.ReflTransGen S.extEdge x)

/-- `S.desc x`: the descendants of `x` (dual of `S.anc`). -/
noncomputable def Schema.desc (S : Schema) (x : Label) : Finset Label :=
  haveI := Classical.decPred (Relation.ReflTransGen S.extEdge · x)
  S.X.filter (Relation.ReflTransGen S.extEdge · x)

/-- `anc(X) = ⋃_{x ∈ X} anc(x)` (Table 3's extension of `anc` to a set of
labels, used by rule 18). -/
noncomputable def Schema.ancSet (S : Schema) (xs : Finset Label) : Finset Label :=
  xs.biUnion S.anc

end ShexLean.InheritanceDisjunction
