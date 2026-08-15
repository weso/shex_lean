import ShexLean.Common.RDF
import ShexLean.Common.Typing
import ShexLean.Common.DisjointUnion
import ShexLean.Shex2017Schemas.Syntax
import Mathlib.Data.Finset.Basic

/-!
The `⊢` and `⊨` relations of Fig. 2 in Boneva, Labra Gayo, Prud'hommeaux
(2017): "node satisfies a shape expression" and "set of triples matches a
triple expression".

Both relations are parameterized by a `typing`, exactly as `typing, n ⊢ S`
and `typing, N ⊨ E` in the paper. The paper stresses that `typing, n ⊢ S` "is
by recursion on the structure of `S`" (§3.1, Discussion on `⊢`) — the only
place a *shape label* gets resolved is by consulting `typing` in Rule
te-tpattern, not by a recursive call into `⊢` on `def(L)`. So for a fixed
`typing` the relation is a well-founded recursion on the finite AST of `S`
(resp. `E`), not a fixpoint over `⊢` itself. This is exactly why it can be
defined as ordinary mutually recursive `Prop`-valued functions below, rather
than as a mutual `inductive`: Rule se-shape-not's premise `¬ (typing, n ⊢ S)`
is a negative occurrence of `⊢`, which Lean's strict-positivity check would
reject for an `inductive` family but which is entirely fine for a recursive
function, since `S` is a strictly smaller subterm than `NOT S`.

Where the paper lists several rules with the same conclusion shape (the two
`se-value-descr` rules, and the two `te-some-of` rules), the corresponding
function equation below is their disjunction: the relation holds iff *some*
rule instance applies, matching "there exists a derivation".

Definition 2 ("correct typing") is stated directly in terms of `Satisfies`:
`typing` is correct if for every `(n, L) ∈ typing`, `Satisfies G typing n
(S.shapeDef L)` holds. The later machinery of §3.2–3.3 (stratification,
maximal correct typing) that turns `⊢`/`⊨` into a well-defined `SHAPES_SEM`
is left for a follow-up step.
-/

namespace ShexLean

/-- `n ∈ V` (Rule se-value-descr1): whether the RDF node `n` belongs to the
value description `V`, i.e. `n` is an IRI or a literal explicitly listed in
`V`. Blank nodes are never members of `V` this way — they can only satisfy
`V` via the separate `_b` constant, Rule se-value-descr2. -/
@[reducible] def NodeInValueDescr (n : RDFNode) (V : ValueDescr) : Prop :=
  match n with
  | .iri i => ValueItem.iri i ∈ V
  | .lit l => ValueItem.lit l ∈ V
  | .bnode _ => False

/-- `_b ∈ V` and `n` is a blank node (Rule se-value-descr2). Marked
`@[reducible]`, like `NodeInValueDescr`, for `decide`. -/
@[reducible] def NodeIsAnyBlankInValueDescr (n : RDFNode) (V : ValueDescr) : Prop :=
  match n with
  | .bnode _ => ValueItem.anyBlank ∈ V
  | _ => False

mutual

/-- `typing, n ⊢ S` (Fig. 2a): node `n` (of graph `G`) satisfies shape
expression `S` under `typing`. -/
def Satisfies (G : Graph) (typing : Typing) (n : RDFNode) : ShapeExpr → Prop
  -- se-value-descr1 ∨ se-value-descr2.
  | .valueDescr V => NodeInValueDescr n V ∨ NodeIsAnyBlankInValueDescr n V
  -- se-neig-descr.
  | .neigDescr E => Matches G typing (neigh G n) E
  -- se-shape-and.
  | .and S1 S2 => Satisfies G typing n S1 ∧ Satisfies G typing n S2
  -- se-shape-or1 ∨ se-shape-or2.
  | .or S1 S2 => Satisfies G typing n S1 ∨ Satisfies G typing n S2
  -- se-shape-not: `n` satisfies `NOT S` iff it does *not* satisfy `S`.
  | .not S => ¬ Satisfies G typing n S

/-- `typing, N ⊨ E` (Fig. 2b): the set of triples `N` matches triple
expression `E` under `typing`. -/
def Matches (G : Graph) (typing : Typing) (N : Finset Triple) : TripleExpr → Prop
  -- te-tpattern: `N` is the singleton `{(subj, pred, obj)}` for some triple
  -- whose predicate is in `P` and whose object has type `L` in `typing`.
  | .tPattern P L =>
      ∃ subj pred obj, N = {(⟨subj, pred, obj⟩ : Triple)} ∧ pred ∈ P ∧ typing.has obj L
  -- te-empty.
  | .empty => N = ∅
  -- te-some-of1 ∨ te-some-of2.
  | .someOf E1 E2 => Matches G typing N E1 ∨ Matches G typing N E2
  -- te-each-of.
  | .eachOf E1 E2 =>
      ∃ N1 N2, DisjointUnion N N1 N2 ∧ Matches G typing N1 E1 ∧ Matches G typing N2 E2
  -- te-repet: `N` splits into some `k`-tuple of disjoint sets `Ns`, each
  -- matching `E`, with `min ≤ k` and (when `max = some m`) `k ≤ m`.
  | .rep E min max =>
      ∃ Ns : List (Finset Triple), DisjointUnionList N Ns ∧
        min ≤ Ns.length ∧ (∀ m', max = some m' → Ns.length ≤ m') ∧
        ∀ Ni ∈ Ns, Matches G typing Ni E

end

end ShexLean
