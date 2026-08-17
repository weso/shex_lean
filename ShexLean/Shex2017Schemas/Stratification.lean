import ShexLean.Shex2017Schemas.Syntax
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
@[reducible] def ShExpr.depsAux (underNot : Bool) : ShExpr → Finset Label × Finset Label
  | .valueDescr _ => (∅, ∅)
  | .neigDescr E  => TExpr.depsAux underNot E
  | .and S1 S2    =>
      let d1 := ShExpr.depsAux underNot S1
      let d2 := ShExpr.depsAux underNot S2
      (d1.1 ∪ d2.1, d1.2 ∪ d2.2)
  | .or S1 S2     =>
      let d1 := ShExpr.depsAux underNot S1
      let d2 := ShExpr.depsAux underNot S2
      (d1.1 ∪ d2.1, d1.2 ∪ d2.2)
  -- Once under a `NOT`, every reference further down stays under it, hence
  -- `underNot` is forced to `true` rather than toggled.
  | .not S        => ShExpr.depsAux true S

/-- Same as `ShExpr.depsAux`, for a triple expression. -/
@[reducible] def TExpr.depsAux (underNot : Bool) : TExpr → Finset Label × Finset Label
  | .tPattern _ L => if underNot then (∅, {L}) else ({L}, ∅)
  | .empty        => (∅, ∅)
  | .someOf E1 E2 =>
      let d1 := TExpr.depsAux underNot E1
      let d2 := TExpr.depsAux underNot E2
      (d1.1 ∪ d2.1, d1.2 ∪ d2.2)
  | .eachOf E1 E2 =>
      let d1 := TExpr.depsAux underNot E1
      let d2 := TExpr.depsAux underNot E2
      (d1.1 ∪ d2.1, d1.2 ∪ d2.2)
  | .rep E _ _    => TExpr.depsAux underNot E

end

/-- Shape labels appearing in `S` via some `TriplePattern`, never under a
`NOT` on the path from `S`. -/
abbrev ShExpr.posDeps (S : ShExpr) : Finset Label := (ShExpr.depsAux false S).1

/-- Shape labels appearing in `S` via some `TriplePattern`, under at least
one `NOT` on the path from `S`. -/
abbrev ShExpr.negDeps (S : ShExpr) : Finset Label := (ShExpr.depsAux false S).2

/-- Shape labels appearing in `E` via some `TriplePattern`, never under a
`NOT` on the path from `E`. -/
abbrev TExpr.posDeps (E : TExpr) : Finset Label := (TExpr.depsAux false E).1

/-- Shape labels appearing in `E` via some `TriplePattern`, under at least
one `NOT` on the path from `E`. -/
abbrev TExpr.negDeps (E : TExpr) : Finset Label := (TExpr.depsAux false E).2

/-- `dep⁺(L1, L2)`: `L2` appears in `def(L1)` but never under an occurrence
of `NOT`. -/
abbrev DepPos (S : Schema) (L1 L2 : Label) : Prop := L2 ∈ (S.shapeDef L1).posDeps

/-- `dep⁻(L1, L2)`: `L2` appears in `def(L1)` under an occurrence of `NOT`. -/
abbrev DepNeg (S : Schema) (L1 L2 : Label) : Prop := L2 ∈ (S.shapeDef L1).negDeps

/-- Definition 3 (schema with stratified negation): a stratification of `S`
into `[1; k]` such that negative dependencies strictly decrease the stratum
and positive dependencies never increase it. -/
structure Stratification (S : Schema) where
  /-- The number of strata. -/
  k : ℕ
  /-- The mapping from shape labels to their stratum. -/
  strat : Label → ℕ
  /-- `strat` maps every label of `S` into `[1; k]`. -/
  mem_range : ∀ L ∈ S.labels, 1 ≤ strat L ∧ strat L ≤ k
  /-- If `dep⁻(L1, L2)`, then `strat(L1) > strat(L2)`. Scoped to `L1 ∈
  S.labels`, matching the paper: "the dependency graph of `S` is a graph
  whose set of nodes is `L`" (§3.2) — `dep⁻`/`dep⁺` edges are only ever
  considered between declared labels. -/
  neg_strict : ∀ L1 ∈ S.labels, ∀ L2, DepNeg S L1 L2 → strat L2 < strat L1
  /-- If `dep⁺(L1, L2)`, then `strat(L1) ≥ strat(L2)`. Scoped to `L1 ∈
  S.labels`, as for `neg_strict`. -/
  pos_le : ∀ L1 ∈ S.labels, ∀ L2, DepPos S L1 L2 → strat L2 ≤ strat L1

/-- `S` is a schema with stratified negation if it admits a stratification
(Definition 3). -/
def Schema.StratNeg (S : Schema) : Prop := Nonempty (Stratification S)

/-!
Two facts connecting `depsAux true` (used internally, right under a `NOT`)
back to `posDeps`/`negDeps` (`depsAux false`, the top-level view): entering
a `NOT` merges what would have been positive and negative dependencies into
one negative bucket. These are needed (in `ShexLean/Shex2017Schemas/Proposition1.lean`) to
recurse under arbitrarily nested `NOT`s without re-deriving this each time.
-/

mutual

theorem ShExpr.depsAux_true : ∀ (S : ShExpr),
    ShExpr.depsAux true S = (∅, S.posDeps ∪ S.negDeps)
  | .valueDescr _ => rfl
  | .neigDescr E => by
      simp only [ShExpr.depsAux, ShExpr.posDeps, ShExpr.negDeps]
      exact TExpr.depsAux_true E
  | .and S1 S2 => by
      simp only [ShExpr.depsAux, ShExpr.posDeps, ShExpr.negDeps,
        ShExpr.depsAux_true S1, ShExpr.depsAux_true S2, Prod.mk.injEq, Finset.empty_union,
        true_and]
      ext x; simp only [Finset.mem_union]; tauto
  | .or S1 S2 => by
      simp only [ShExpr.depsAux, ShExpr.posDeps, ShExpr.negDeps,
        ShExpr.depsAux_true S1, ShExpr.depsAux_true S2, Prod.mk.injEq, Finset.empty_union,
        true_and]
      ext x; simp only [Finset.mem_union]; tauto
  | .not S => by
      simp only [ShExpr.depsAux, ShExpr.posDeps, ShExpr.negDeps,
        ShExpr.depsAux_true S, Finset.empty_union]

theorem TExpr.depsAux_true : ∀ (E : TExpr),
    TExpr.depsAux true E = (∅, (TExpr.depsAux false E).1 ∪ (TExpr.depsAux false E).2)
  | .tPattern _ _ => by simp [TExpr.depsAux]
  | .empty => by simp [TExpr.depsAux]
  | .someOf E1 E2 => by
      simp only [TExpr.depsAux, TExpr.depsAux_true E1, TExpr.depsAux_true E2,
        Prod.mk.injEq, Finset.empty_union, true_and]
      ext x; simp only [Finset.mem_union]; tauto
  | .eachOf E1 E2 => by
      simp only [TExpr.depsAux, TExpr.depsAux_true E1, TExpr.depsAux_true E2,
        Prod.mk.injEq, Finset.empty_union, true_and]
      ext x; simp only [Finset.mem_union]; tauto
  | .rep E _ _ => TExpr.depsAux_true E

end

/-- Entering a `NOT` sends everything to `negDeps`: nothing under `.not S`
counts as a positive dependency. -/
theorem ShExpr.not_posDeps (S : ShExpr) : (ShExpr.not S).posDeps = ∅ := by
  simp only [ShExpr.posDeps, ShExpr.depsAux, ShExpr.depsAux_true S]

/-- Entering a `NOT` merges what would have been `S`'s positive and negative
dependencies into `.not S`'s negative dependencies. -/
theorem ShExpr.not_negDeps (S : ShExpr) :
    (ShExpr.not S).negDeps = S.posDeps ∪ S.negDeps := by
  simp only [ShExpr.negDeps, ShExpr.depsAux, ShExpr.depsAux_true S]

end ShexLean
