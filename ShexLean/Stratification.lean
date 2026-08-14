import ShexLean.Syntax
import Mathlib.Data.Finset.Basic

/-!
The dependency graph and Definition 3 ("schema with stratified negation") of
§3.2 in Boneva, Labra Gayo, Prud'hommeaux (2017).

> We now define ... stratified negation. The dependency graph of `S` is a
> graph whose set of nodes is `L`, and that has two kinds of edges labelled
> `dep⁻` and `dep⁺` defined by (recall that shape expressions in disjunctive
> normal form):
> - There is a negative dependency edge `dep⁻(L1, L2)` from `L1` to `L2` iff
>   the shape label `L2` appears in `def(L1)` under an occurrence of the NOT
>   operator;
> - There is a positive dependency edge `dep⁺(L1, L2)` from `L1` to `L2` iff
>   the shape label `L2` appears in `def(L1)` but never under an occurrence
>   of NOT.

> Definition 3 (schema with stratified negation). A schema `S = (L, def)` is
> with stratified negation if there exists a natural number `k` and a
> mapping `strat` from `L` to the interval `[1; k]` such that for all shape
> labels `L1, L2`:
> - if `dep⁻(L1, L2)`, then `strat(L1) > strat(L2)`;
> - if `dep⁺(L1, L2)`, then `strat(L1) ≥ strat(L2)`.
-/

namespace ShexLean

mutual

/-- The shape labels reachable from `S` through some `TriplePattern`,
split into those reached with no `NOT` on the path from `S` down to that
`TriplePattern` (`.1`, the positive dependencies) and those reached under at
least one `NOT` (`.2`, the negative dependencies). `underNot` records whether
the recursion has already passed under a `NOT` on the way down to `S`. -/
@[reducible] def ShapeExpr.depsAux (underNot : Bool) : ShapeExpr → Finset ShapeLabel × Finset ShapeLabel
  | .valueDescr _ => (∅, ∅)
  | .neigDescr E  => TripleExpr.depsAux underNot E
  | .and S1 S2    =>
      let d1 := ShapeExpr.depsAux underNot S1
      let d2 := ShapeExpr.depsAux underNot S2
      (d1.1 ∪ d2.1, d1.2 ∪ d2.2)
  | .or S1 S2     =>
      let d1 := ShapeExpr.depsAux underNot S1
      let d2 := ShapeExpr.depsAux underNot S2
      (d1.1 ∪ d2.1, d1.2 ∪ d2.2)
  -- Once under a `NOT`, every reference further down stays under it, hence
  -- `underNot` is forced to `true` rather than toggled.
  | .not S        => ShapeExpr.depsAux true S

/-- Same as `ShapeExpr.depsAux`, for a triple expression. -/
@[reducible] def TripleExpr.depsAux (underNot : Bool) : TripleExpr → Finset ShapeLabel × Finset ShapeLabel
  | .tPattern _ L => if underNot then (∅, {L}) else ({L}, ∅)
  | .empty        => (∅, ∅)
  | .someOf E1 E2 =>
      let d1 := TripleExpr.depsAux underNot E1
      let d2 := TripleExpr.depsAux underNot E2
      (d1.1 ∪ d2.1, d1.2 ∪ d2.2)
  | .eachOf E1 E2 =>
      let d1 := TripleExpr.depsAux underNot E1
      let d2 := TripleExpr.depsAux underNot E2
      (d1.1 ∪ d2.1, d1.2 ∪ d2.2)
  | .rep E _ _    => TripleExpr.depsAux underNot E

end

/-- Shape labels appearing in `S` via some `TriplePattern`, never under a
`NOT` on the path from `S`. -/
@[reducible] def ShapeExpr.posDeps (S : ShapeExpr) : Finset ShapeLabel := (ShapeExpr.depsAux false S).1

/-- Shape labels appearing in `S` via some `TriplePattern`, under at least
one `NOT` on the path from `S`. -/
@[reducible] def ShapeExpr.negDeps (S : ShapeExpr) : Finset ShapeLabel := (ShapeExpr.depsAux false S).2

/-- `dep⁺(L1, L2)`: `L2` appears in `def(L1)` but never under an occurrence
of `NOT`. -/
@[reducible] def DepPos (S : Schema) (L1 L2 : ShapeLabel) : Prop := L2 ∈ (S.shapeDef L1).posDeps

/-- `dep⁻(L1, L2)`: `L2` appears in `def(L1)` under an occurrence of `NOT`. -/
@[reducible] def DepNeg (S : Schema) (L1 L2 : ShapeLabel) : Prop := L2 ∈ (S.shapeDef L1).negDeps

/-- Definition 3 (schema with stratified negation): a stratification of `S`
into `[1; k]` such that negative dependencies strictly decrease the stratum
and positive dependencies never increase it. -/
structure Stratification (S : Schema) where
  /-- The number of strata. -/
  k : ℕ
  /-- The mapping from shape labels to their stratum. -/
  strat : ShapeLabel → ℕ
  /-- `strat` maps every label of `S` into `[1; k]`. -/
  mem_range : ∀ L ∈ S.labels, 1 ≤ strat L ∧ strat L ≤ k
  /-- If `dep⁻(L1, L2)`, then `strat(L1) > strat(L2)`. -/
  neg_strict : ∀ L1 L2, DepNeg S L1 L2 → strat L2 < strat L1
  /-- If `dep⁺(L1, L2)`, then `strat(L1) ≥ strat(L2)`. -/
  pos_le : ∀ L1 L2, DepPos S L1 L2 → strat L2 ≤ strat L1

/-- `S` is a schema with stratified negation if it admits a stratification
(Definition 3). -/
def Schema.StratifiedNegation (S : Schema) : Prop := Nonempty (Stratification S)

end ShexLean
