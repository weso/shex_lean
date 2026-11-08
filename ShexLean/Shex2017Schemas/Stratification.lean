import ShexLean.Shex2017Schemas.Syntax
import Mathlib.Data.Finset.Basic

/-!
The dependency graph and Definition 3 ("schema with stratified negation")
of §3.2 in Boneva, Labra Gayo, Prud'hommeaux (2017).

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
> mapping `str` from `L` to the interval `[1; k]` such that for all shape
> labels `L1, L2`:
> - if `dep⁻(L1, L2)`, then `str(L1) > str(L2)`;
> - if `dep⁺(L1, L2)`, then `str(L1) ≥ str(L2)`.
-/

namespace ShexLean

mutual

/-- The shape labels that `S` refers to through a `TriplePattern`. The
result has two parts:

* `.1`, the positive dependencies: the labels with no `NOT` on the path
  from `S` to the `TriplePattern`.
* `.2`, the negative dependencies: the labels with one or more `NOT` on
  that path.

`underNot` tells if the recursion already went below a `NOT` before it
got to `S`. -/
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
  -- Below a `NOT`, each reference further down is also below a `NOT`. Thus,
  -- `underNot` is always set to `true`. It does not change between values.
  | .not S        => ShExpr.depsAux true S

/-- The same as `ShExpr.depsAux`, for a triple expression. -/
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

/-- The shape labels that `S` refers to through a `TriplePattern`, with no
`NOT` on the path from `S`. -/
abbrev ShExpr.posDeps (S : ShExpr) : Finset Label := (ShExpr.depsAux false S).1

/-- The shape labels that `S` refers to through a `TriplePattern`, with one
or more `NOT` on the path from `S`. -/
abbrev ShExpr.negDeps (S : ShExpr) : Finset Label := (ShExpr.depsAux false S).2

/-- The shape labels that `E` refers to through a `TriplePattern`, with no
`NOT` on the path from `E`. -/
abbrev TExpr.posDeps (E : TExpr) : Finset Label := (TExpr.depsAux false E).1

/-- The shape labels that `E` refers to through a `TriplePattern`, with one
or more `NOT` on the path from `E`. -/
abbrev TExpr.negDeps (E : TExpr) : Finset Label := (TExpr.depsAux false E).2

/-- `dep⁺(L1, L2)`: `L2` occurs in `def(L1)`, but never below a `NOT`. -/
abbrev DepPos (S : Schema) (L1 L2 : Label) : Prop := L2 ∈ (S.shapeDef L1).posDeps

/-- `dep⁻(L1, L2)`: `L2` occurs in `def(L1)` below a `NOT`. -/
abbrev DepNeg (S : Schema) (L1 L2 : Label) : Prop := L2 ∈ (S.shapeDef L1).negDeps

/-- Definition 3 (schema with stratified negation): a stratification of
`S` into `[1; k]`. A negative dependency makes the stratum strictly
smaller. A positive dependency never makes the stratum larger. -/
structure Strat (S : Schema) where
  /-- The number of strata. -/
  k : ℕ
  /-- The map from each shape label to its stratum. -/
  str : Label → ℕ
  /-- `str` maps each label of `S` into `[1; k]`. -/
  mem_range : ∀ L ∈ S.labels, 1 ≤ str L ∧ str L ≤ k
  /-- If `dep⁻(L1, L2)`, then `str(L1) > str(L2)`. This applies only when
  `L1 ∈ S.labels`, as in the paper: "the dependency graph of `S` is a
  graph whose set of nodes is `L`" (§3.2). The `dep⁻` and `dep⁺` edges
  are only between declared labels. -/
  neg_strict : ∀ L1 ∈ S.labels, ∀ L2, DepNeg S L1 L2 → str L2 < str L1
  /-- If `dep⁺(L1, L2)`, then `str(L1) ≥ str(L2)`. This applies only when
  `L1 ∈ S.labels`, as for `neg_strict`. -/
  pos_le : ∀ L1 ∈ S.labels, ∀ L2, DepPos S L1 L2 → str L2 ≤ str L1

/-- `S` is a schema with stratified negation if it has a stratification
(Definition 3). -/
def Schema.StratNeg (S : Schema) : Prop := Nonempty (Strat S)

/-!
Two facts that connect `depsAux true` to `posDeps` and `negDeps`
(`depsAux false`). The proofs use `depsAux true` directly below a `NOT`.
`posDeps` and `negDeps` are the top-level view.

When the recursion goes below a `NOT`, the positive and the negative
dependencies go into one negative set.
`ShexLean/Shex2017Schemas/Proposition1.lean` needs these facts. With
them, it can do recursion below many nested `NOT`s, and it does not have
to prove this fact again each time.
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

/-- Below a `NOT`, all dependencies go to `negDeps`. Nothing below
`.not S` is a positive dependency. -/
theorem ShExpr.not_posDeps (S : ShExpr) : (ShExpr.not S).posDeps = ∅ := by
  simp only [ShExpr.posDeps, ShExpr.depsAux, ShExpr.depsAux_true S]

/-- Below a `NOT`, the positive and the negative dependencies of `S` go
together into the negative dependencies of `.not S`. -/
theorem ShExpr.not_negDeps (S : ShExpr) :
    (ShExpr.not S).negDeps = S.posDeps ∪ S.negDeps := by
  simp only [ShExpr.negDeps, ShExpr.depsAux, ShExpr.depsAux_true S]

/-! For `AND` and `OR` (and also `SomeOfExpr` and `EachOfExpr`), the
dependencies are the union of the dependencies of the two operands.
`depsAux` processes these four constructors in the same way.

These lemmas have names, so that the `agree` and `stratMono` proofs of
`Proposition1.lean` can restrict `hagree` or `hle` to a sub-expression with
`rw` or `Finset.subset_union_left`. Without these lemmas, each call site
must unfold `depsAux` again. -/

theorem ShExpr.and_posDeps (S1 S2 : ShExpr) : (S1.and S2).posDeps = S1.posDeps ∪ S2.posDeps := rfl
theorem ShExpr.and_negDeps (S1 S2 : ShExpr) : (S1.and S2).negDeps = S1.negDeps ∪ S2.negDeps := rfl
theorem ShExpr.or_posDeps (S1 S2 : ShExpr) : (S1.or S2).posDeps = S1.posDeps ∪ S2.posDeps := rfl
theorem ShExpr.or_negDeps (S1 S2 : ShExpr) : (S1.or S2).negDeps = S1.negDeps ∪ S2.negDeps := rfl
theorem TExpr.someOf_posDeps (E1 E2 : TExpr) :
    (E1.someOf E2).posDeps = E1.posDeps ∪ E2.posDeps := rfl
theorem TExpr.someOf_negDeps (E1 E2 : TExpr) :
    (E1.someOf E2).negDeps = E1.negDeps ∪ E2.negDeps := rfl
theorem TExpr.eachOf_posDeps (E1 E2 : TExpr) :
    (E1.eachOf E2).posDeps = E1.posDeps ∪ E2.posDeps := rfl
theorem TExpr.eachOf_negDeps (E1 E2 : TExpr) :
    (E1.eachOf E2).negDeps = E1.negDeps ∪ E2.negDeps := rfl

/-! Two forms derived from the lemmas above. `Proposition1.lean` needs
exactly these forms at each binary constructor:

* `agree` restricts `hagree` from a full set `posDeps ∪ negDeps` to the
  set of one operand.
* `stratMono` restricts `hle : _.negDeps ⊆ Lo` in the same way. -/

theorem ShExpr.and_deps_subset_left (S1 S2 : ShExpr) :
    S1.posDeps ∪ S1.negDeps ⊆ (S1.and S2).posDeps ∪ (S1.and S2).negDeps := by
  rw [ShExpr.and_posDeps, ShExpr.and_negDeps]
  exact Finset.union_subset_union Finset.subset_union_left Finset.subset_union_left
theorem ShExpr.and_deps_subset_right (S1 S2 : ShExpr) :
    S2.posDeps ∪ S2.negDeps ⊆ (S1.and S2).posDeps ∪ (S1.and S2).negDeps := by
  rw [ShExpr.and_posDeps, ShExpr.and_negDeps]
  exact Finset.union_subset_union Finset.subset_union_right Finset.subset_union_right
theorem ShExpr.or_deps_subset_left (S1 S2 : ShExpr) :
    S1.posDeps ∪ S1.negDeps ⊆ (S1.or S2).posDeps ∪ (S1.or S2).negDeps := by
  rw [ShExpr.or_posDeps, ShExpr.or_negDeps]
  exact Finset.union_subset_union Finset.subset_union_left Finset.subset_union_left
theorem ShExpr.or_deps_subset_right (S1 S2 : ShExpr) :
    S2.posDeps ∪ S2.negDeps ⊆ (S1.or S2).posDeps ∪ (S1.or S2).negDeps := by
  rw [ShExpr.or_posDeps, ShExpr.or_negDeps]
  exact Finset.union_subset_union Finset.subset_union_right Finset.subset_union_right
theorem TExpr.someOf_deps_subset_left (E1 E2 : TExpr) :
    E1.posDeps ∪ E1.negDeps ⊆ (E1.someOf E2).posDeps ∪ (E1.someOf E2).negDeps := by
  rw [TExpr.someOf_posDeps, TExpr.someOf_negDeps]
  exact Finset.union_subset_union Finset.subset_union_left Finset.subset_union_left
theorem TExpr.someOf_deps_subset_right (E1 E2 : TExpr) :
    E2.posDeps ∪ E2.negDeps ⊆ (E1.someOf E2).posDeps ∪ (E1.someOf E2).negDeps := by
  rw [TExpr.someOf_posDeps, TExpr.someOf_negDeps]
  exact Finset.union_subset_union Finset.subset_union_right Finset.subset_union_right
theorem TExpr.eachOf_deps_subset_left (E1 E2 : TExpr) :
    E1.posDeps ∪ E1.negDeps ⊆ (E1.eachOf E2).posDeps ∪ (E1.eachOf E2).negDeps := by
  rw [TExpr.eachOf_posDeps, TExpr.eachOf_negDeps]
  exact Finset.union_subset_union Finset.subset_union_left Finset.subset_union_left
theorem TExpr.eachOf_deps_subset_right (E1 E2 : TExpr) :
    E2.posDeps ∪ E2.negDeps ⊆ (E1.eachOf E2).posDeps ∪ (E1.eachOf E2).negDeps := by
  rw [TExpr.eachOf_posDeps, TExpr.eachOf_negDeps]
  exact Finset.union_subset_union Finset.subset_union_right Finset.subset_union_right

theorem ShExpr.and_negDeps_subset_left (S1 S2 : ShExpr) :
    S1.negDeps ⊆ (S1.and S2).negDeps := ShExpr.and_negDeps S1 S2 ▸ Finset.subset_union_left
theorem ShExpr.and_negDeps_subset_right (S1 S2 : ShExpr) :
    S2.negDeps ⊆ (S1.and S2).negDeps := ShExpr.and_negDeps S1 S2 ▸ Finset.subset_union_right
theorem ShExpr.or_negDeps_subset_left (S1 S2 : ShExpr) :
    S1.negDeps ⊆ (S1.or S2).negDeps := ShExpr.or_negDeps S1 S2 ▸ Finset.subset_union_left
theorem ShExpr.or_negDeps_subset_right (S1 S2 : ShExpr) :
    S2.negDeps ⊆ (S1.or S2).negDeps := ShExpr.or_negDeps S1 S2 ▸ Finset.subset_union_right
theorem TExpr.someOf_negDeps_subset_left (E1 E2 : TExpr) :
    E1.negDeps ⊆ (E1.someOf E2).negDeps := TExpr.someOf_negDeps E1 E2 ▸ Finset.subset_union_left
theorem TExpr.someOf_negDeps_subset_right (E1 E2 : TExpr) :
    E2.negDeps ⊆ (E1.someOf E2).negDeps := TExpr.someOf_negDeps E1 E2 ▸ Finset.subset_union_right
theorem TExpr.eachOf_negDeps_subset_left (E1 E2 : TExpr) :
    E1.negDeps ⊆ (E1.eachOf E2).negDeps := TExpr.eachOf_negDeps E1 E2 ▸ Finset.subset_union_left
theorem TExpr.eachOf_negDeps_subset_right (E1 E2 : TExpr) :
    E2.negDeps ⊆ (E1.eachOf E2).negDeps := TExpr.eachOf_negDeps E1 E2 ▸ Finset.subset_union_right

end ShexLean
