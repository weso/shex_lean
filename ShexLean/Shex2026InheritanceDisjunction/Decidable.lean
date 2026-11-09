import ShexLean.Common.FixedPoint
import ShexLean.Shex2026InheritanceDisjunction.Semantics
import ShexLean.Shex2017Schemas.RepBound
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Pi
import ShexLean.InheritanceCore.Decidable

/-!
This file makes the semantics of the 2025 paper "Shape Expressions with
Inheritance" decidable, in the variant with disjunctive `extends`. It is
the equivalent of `ShexLean.Shex2017Schemas.Decidable`. The full work
(each case of `SatisfiesE`, `SatisfiesMAt` and `SatisfiesAt`) is
much larger than in 2017, for two reasons. This file solves the two
problems directly. It does not go around them.

1. **`Schema.anc` and `Schema.ancSet` (the ancestor sets of rule 18 of
   Table 3, in `Syntax.lean`) are `noncomputable`.** They use
   `Classical.decPred (Relation.ReflTransGen S.extEdge x)`, because
   Mathlib has no general `Decidable` instance for the
   reflexive-transitive closure. (Reachability over a general relation,
   possibly infinite, is not decidable.)

   This file proves that the *same* declarative proposition as in the
   paper ("there is a path in `H_S`") *is* decidable. It needs one
   hypothesis that Definition 3 already assumes, but that this Lean port
   did not name before: the edges of `H_S` out of each `x ∈ X` stay in
   `X` (`Schema.XClosed` below). This is not a new restriction.
   Definition 3 says directly that the vertex set of `H_S` *is* `X`.
   `XClosed` only makes this fact explicit, so that we can compute with it.

   This file does not change `Schema.anc` and `ancSet`. They are still
   `noncomputable`, as before, so there is no risk to an existing proof.
   `ancReach` and `ancSetReach` below are *separate*, computable
   definitions, and the file proves that they are equal to `anc` and
   `ancSet`.
2. **`NodeConstraint := RDFNode → Prop`** (rule 13 of Table 3,
   `.constraint c`) is a general predicate with no canonical decision
   procedure. (The concrete `ValueDescr` of 2017 has one.) Thus, you can
   decide `SatisfiesMFuel` and `SatisfiesFuel` only *if* you give a
   `DecidablePred c` for each `c` that a schema uses. These instances go
   explicitly through the definitions below. The `.rep` case of
   `matches_decidable` does the same with a decidability witness for the
   repeated sub-expression of `repExact`.
-/

namespace ShexLean.InheritanceDisjunction

open ShexLean.InheritanceCore

open ShexLean

/-! ### `Schema.anc` and `ancSet`, made computable -/

/-- The assumption of the paper for Definition 3: the edges of `H_S` never
go out of `X`. Thus, `H_S` is a graph on the vertex set `X`. It is not a
larger graph that is filtered after. -/
def Schema.XClosed (S : Schema) : Prop :=
  ∀ x ∈ S.X, (S.shapeDef x).extendsTargets ⊆ S.X

/-- One step of the closure of the ancestor set: add each `X` vertex that
is not yet in the current set and that one more `extEdge` step can
reach. -/
private def ancStep (S : Schema) (t : Finset Label) : Finset Label :=
  t ∪ S.X.filter (fun y' => ∃ y ∈ t, S.extEdge y y')

private theorem mem_ancStep_iff {S : Schema} {t : Finset Label} {x' : Label} :
    x' ∈ ancStep S t ↔ x' ∈ t ∨ (x' ∈ S.X ∧ ∃ y ∈ t, S.extEdge y x') := by
  unfold ancStep
  rw [Finset.mem_union, Finset.mem_filter]

private theorem ancStep_subset_X {S : Schema} : ∀ t ⊆ S.X, ancStep S t ⊆ S.X := by
  intro t ht
  unfold ancStep
  exact Finset.union_subset ht (Finset.filter_subset _ _)

private theorem subset_ancStep {S : Schema} : ∀ t ⊆ S.X, t ⊆ ancStep S t :=
  fun _ _ => Finset.subset_union_left

private theorem iterate_subset_X {S : Schema} {x : Label} (hx : x ∈ S.X) :
    ∀ n, (ancStep S)^[n] {x} ⊆ S.X := by
  intro n
  induction n with
  | zero => simpa using Finset.singleton_subset_iff.mpr hx
  | succ n ih => rw [Function.iterate_succ_apply']; exact ancStep_subset_X _ ih

private theorem start_subset_iterate {S : Schema} {x : Label}
    (hx : x ∈ S.X) : ∀ n, ({x} : Finset Label) ⊆ (ancStep S)^[n] {x} := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (subset_ancStep _ (iterate_subset_X hx n))

/-- The computable ancestor set: iterate `ancStep` from `{x}` until it is
stable. This occurs in `(S.X \ {x}).card` steps or fewer
(`Finset.increasing_iterate_fixed`). -/
def ancReach (S : Schema) (x : Label) : Finset Label :=
  (ancStep S)^[(S.X \ {x}).card] {x}

/-- Each `extEdge` step out of a point of `S.X` that is reachable from `x`
stays in `S.X`. (This is the result of `XClosed`, applied along a path.) -/
private theorem reflTransGen_mem_X {S : Schema} (hXC : S.XClosed) {x : Label} (hx : x ∈ S.X)
    {x' : Label} (h : Relation.ReflTransGen S.extEdge x x') : x' ∈ S.X := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact hXC _ ih hbc

/-- The forward direction: each point that the iteration reaches is really
reachable with `extEdge`. -/
private theorem reflTransGen_of_mem_iterate {S : Schema} {x : Label} :
    ∀ n (x' : Label), x' ∈ (ancStep S)^[n] {x} → Relation.ReflTransGen S.extEdge x x' := by
  intro n
  induction n with
  | zero =>
      intro x' hx'
      simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at hx'
      subst hx'; exact Relation.ReflTransGen.refl
  | succ n ih =>
      intro x' hx'
      rw [Function.iterate_succ_apply'] at hx'
      rcases mem_ancStep_iff.mp hx' with hx' | ⟨-, y, hy, hedge⟩
      · exact ih x' hx'
      · exact Relation.ReflTransGen.tail (ih y hy) hedge

/-- The reverse direction: with `XClosed`, each point that is reachable
with `extEdge` is in `ancReach`. (`ancReach` is exactly the fixed point of
`ancStep` from `{x}`, by `Finset.increasing_iterate_fixed`.) -/
private theorem mem_ancReach_of_reflTransGen {S : Schema} (hXC : S.XClosed) {x : Label}
    (hx : x ∈ S.X) {x' : Label} (h : Relation.ReflTransGen S.extEdge x x') :
    x' ∈ ancReach S x := by
  have hFPfix : ancStep S (ancReach S x) = ancReach S x :=
    Finset.increasing_iterate_fixed (ancStep S) S.X subset_ancStep ancStep_subset_X
      {x} (Finset.singleton_subset_iff.mpr hx)
  have hxFP : x ∈ ancReach S x := start_subset_iterate hx _ (Finset.mem_singleton_self x)
  induction h with
  | refl => exact hxFP
  | tail hab hbc ih =>
      rename_i b c
      have hbX : b ∈ S.X := reflTransGen_mem_X hXC hx hab
      rw [← hFPfix]
      exact mem_ancStep_iff.mpr (Or.inr ⟨hXC b hbX hbc, b, ih, hbc⟩)

/-- `ancReach` is exactly `Schema.anc`, with the natural closure
hypothesis that Definition 3 already assumes. -/
theorem ancReach_eq_anc {S : Schema} (hXC : S.XClosed) {x : Label} (hx : x ∈ S.X) :
    ancReach S x = S.anc x := by
  ext x'
  unfold Schema.anc
  simp only [Finset.mem_filter]
  constructor
  · intro hx'
    exact ⟨iterate_subset_X hx _ hx', reflTransGen_of_mem_iterate _ x' hx'⟩
  · rintro ⟨-, hrtg⟩
    exact mem_ancReach_of_reflTransGen hXC hx hrtg

/-- The computable `ancSet`. -/
def ancSetReach (S : Schema) (xs : Finset Label) : Finset Label :=
  xs.biUnion (ancReach S)

theorem ancSetReach_eq_ancSet {S : Schema} (hXC : S.XClosed) {xs : Finset Label}
    (hxs : xs ⊆ S.X) : ancSetReach S xs = S.ancSet xs := by
  unfold ancSetReach Schema.ancSet
  apply Finset.biUnion_congr rfl
  intro x hx
  exact ancReach_eq_anc hXC (hxs hx)

/-! ### `SatisfiesMFuel` and `SatisfiesFuel` (Tables 3 and 2) are decidable, on a
restricted fragment

There are two more problems, in addition to `anc`, `ancSet`, `Me`,
`Mnotin` and `.star` above:

1. `subjectOf` (the `c (subjectOf M)` of rule 13) is also `noncomputable`.
   It uses `Classical.choice`, because the paper only says that its value
   is "the subject of a triple". There is no computable replacement that
   agrees with it in general. There is one only with an invariant "all the
   triples in `M` have the same subject", which the definitions do not
   record. We do not want to risk a different answer. Thus, we exclude
   `.constraint` from evaluation at the triple-set level
   (`ShapeExpr.MOk` below).
   * It is still decidable at the node level (rule 6, `c n`, with no
     `subjectOf`). This is the usual location where the check of the `Y`
     labels of a well-formed schema uses it.
   * It gets to the triple-set level only if a schema puts a plain
     `.constraint` in the `restr(x)` of an `extends`. No worked example
     does this.
2. `NodeConstraint := RDFNode → Prop` is a general predicate. (Def 1 keeps
   it fully abstract. The concrete `ValueDescr` of 2017 is not abstract.)
   Thus, no single `Decidable` instance covers each `.constraint c` that a
   schema can use. The caller must give a `DecidablePred c` for each
   occurrence (`ShapeExpr.AllConstraintsDecidable`, which follows the
   recursion of `MOk`).
-/

/-- The fragment of `ShapeExpr` where this file proves that
`SatisfiesMFuel` is decidable:

* It has no plain `.constraint` (problem 1 above).
* For each nested `.extends xs _`, `xs` stays in `S.X`. Thus,
  `ancSetReach` and `ancReach` apply. (They are equal to `S.ancSet` and
  `S.anc` only with this condition.) -/
def ShapeExpr.MOk (S : Schema) : ShapeExpr → Prop
  | .constraint _ => False
  | .ofShape _ => True
  | .extends xs _ => xs ⊆ S.X
  | .or s1 s2 => s1.MOk S ∧ s2.MOk S
  | .and s1 s2 => s1.MOk S ∧ s2.MOk S
  | .not s => s.MOk S

/-- The extra schema-level well-formedness that the decidability of
`SatisfiesMFuel` needs at rule 18. Each `restr(x)` that is present (for
`x ∈ X`) must also be in the `MOk` fragment, because rule 18 also evaluates
it at the triple-set level. -/
def Schema.RestrOk (S : Schema) : Prop :=
  ∀ x ∈ S.X, ∀ u, (S.shapeDef x).restrOf = some u → u.MOk S

/-- The recursive hypothesis "each `.constraint` that is reachable through
`or`, `and` and `not` has a `Decidable` predicate". The decidability of
`SatisfiesFuel` needs it for rule 6 (problem 2 above). `.ofShape` and
`.extends` give `True`. The `.constraint`s that are reachable through
`restr(x)` are a separate schema-level lookup, which `MOk` covers. -/
def ShapeExpr.AllConstraintsDecidable : ShapeExpr → Prop
  | .constraint c => Nonempty (DecidablePred c)
  | .ofShape _ => True
  | .extends _ _ => True
  | .or s1 s2 => s1.AllConstraintsDecidable ∧ s2.AllConstraintsDecidable
  | .and s1 s2 => s1.AllConstraintsDecidable ∧ s2.AllConstraintsDecidable
  | .not s => s.AllConstraintsDecidable

/-- The finite search space for `pick x` (the new disjunct-choice witness
of rule 18, in `Semantics.lean`). An index below
`(S.shapeDef x).extTeList.length` already gives each different result of
`extTeAt` at `x` (`ShapeExpr.extTeAt_mod`, `Syntax.lean`). The guard
`max 1 _` makes sure that the search space is never empty, also when the
`extTeList` of `x` is empty (the junk `.empty` case). -/
def ShapeExpr.pickBound (S : Schema) (x : Label) : Finset ℕ :=
  Finset.range (max 1 (S.shapeDef x).extTeList.length)

/-- The version of `extendMx` for `pick`. It extends a dependent witness
`p : ∀ a ∈ Idx, ℕ` (as in `Finset.pi`) to an ordinary `Label → ℕ`. Outside
`Idx`, the result is a junk value (`0`). -/
def extendPick (Idx : Finset Label) (p : ∀ a ∈ Idx, ℕ) : Label → ℕ :=
  fun x => if h : x ∈ Idx then p x h else 0

theorem extendPick_eq {Idx : Finset Label} {p : ∀ a ∈ Idx, ℕ} {x : Label}
    (hx : x ∈ Idx) : extendPick Idx p x = p x hx := by
  unfold extendPick; simp [hx]

/-- Each `pick : Label → ℕ` agrees, at each `x ∈ Idx`, with *a* bounded
representative in `ShapeExpr.pickBound S x`, as far as `extTeAt` can see
(`ShapeExpr.extTeAt_mod`). Because of this, it is sound for the bounded
search below to try only `extendPick Idx p` for
`p ∈ Finset.pi Idx (ShapeExpr.pickBound S)`, and not a general `pick`. -/
theorem exists_pickBound_eq_extTeAt {S : Schema} {Idx : Finset Label} (pick : Label → ℕ) :
    ∃ p ∈ Finset.pi Idx (ShapeExpr.pickBound S),
      ∀ x ∈ Idx, (S.shapeDef x).extTeAt (extendPick Idx p x) = (S.shapeDef x).extTeAt (pick x) := by
  refine ⟨fun x _ => pick x % max 1 (S.shapeDef x).extTeList.length, ?_, ?_⟩
  · rw [Finset.mem_pi]
    intro x hx
    unfold ShapeExpr.pickBound
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  · intro x hx
    rw [extendPick_eq hx]
    exact ((S.shapeDef x).extTeAt_mod (pick x)).symm

/-- The ancestors of a point in `ancSetReach S xs` stay in this set.
Because of this, it is sound to use `Mx` only at points of
`ancSetReach S xs` in the `restr(x)` clause of rule 18
(`(S.anc x).biUnion Mx`, where `x` is in the same set). -/
theorem ancReach_subset_ancSetReach {S : Schema} (hXC : S.XClosed) {xs : Finset Label}
    (hxs : xs ⊆ S.X) {x : Label} (hx : x ∈ ancSetReach S xs) :
    ancReach S x ⊆ ancSetReach S xs := by
  rw [ancSetReach_eq_ancSet hXC hxs] at hx ⊢
  unfold Schema.ancSet at hx ⊢
  obtain ⟨x0, hx0, hxx0⟩ := Finset.mem_biUnion.mp hx
  simp only [Schema.anc, Finset.mem_filter] at hxx0
  have hx0X : x0 ∈ S.X := hxs hx0
  have hxX : x ∈ S.X := hxx0.1
  rw [ancReach_eq_anc hXC hxX]
  have hrtg0 : Relation.ReflTransGen S.extEdge x0 x := hxx0.2
  intro x' hx'
  simp only [Schema.anc, Finset.mem_filter] at hx'
  have hxX' : x' ∈ S.X := hx'.1
  have hrtg1 : Relation.ReflTransGen S.extEdge x x' := hx'.2
  refine Finset.mem_biUnion.mpr ⟨x0, hx0, ?_⟩
  simp only [Schema.anc, Finset.mem_filter]
  exact ⟨hxX', hrtg0.trans hrtg1⟩

/-- Each point of `ancSetReach S xs` is also in `S.X`. (It is a union of
images of `S.anc`, and `S.anc _ ⊆ S.X` always, by construction.) -/
theorem ancSetReach_subset_X {S : Schema} (hXC : S.XClosed) {xs : Finset Label}
    (hxs : xs ⊆ S.X) : ancSetReach S xs ⊆ S.X := by
  intro x hx
  rw [ancSetReach_eq_ancSet hXC hxs] at hx
  unfold Schema.ancSet at hx
  obtain ⟨x0, -, hx0⟩ := Finset.mem_biUnion.mp hx
  simp only [Schema.anc, Finset.mem_filter] at hx0
  exact hx0.1

/-- The existential of rule 18 (`∃ M' Mx, ...`), written as a bounded
search:

* For `M'`, the search is over `M.powerset`.
* For `Mx`, the search is over
  `Finset.pi (ancSetReach S xs) (fun _ => M.powerset)`, restricted to the
  points where `Mx` is used.

`ancSetReach S xs` and `ancReach S x` replace `S.ancSet xs` and `S.anc x`.
This is sound because `xs ⊆ S.X`, from the `MOk` requirement of
`.extends xs h`. -/
theorem satisfiesExtends_iff_bounded {S : Schema} {τ : Typing}
    {restr : Finset Triple → ShapeExpr → Prop}
    (hXC : S.XClosed) {M : Finset Triple} {xs : Finset Label} {hs : List Shape}
    (hxs : xs ⊆ S.X) :
    (∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        (∃ h ∈ hs, SatisfiesShape τ M' h) ∧
        (∀ x ∈ S.ancSet xs,
          SatisfiesE τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          restr ((S.anc x).biUnion Mx) u)) ↔
      ∃ M' ∈ M.powerset, ∃ g ∈ Finset.pi (ancSetReach S xs) (fun _ => M.powerset),
        ∃ p ∈ Finset.pi (ancSetReach S xs) (ShapeExpr.pickBound S),
        DisjointUnionOn M M' (ancSetReach S xs) (extendMx (ancSetReach S xs) g) ∧
        (∃ h ∈ hs, SatisfiesShape τ M' h) ∧
        (∀ x ∈ ancSetReach S xs,
          SatisfiesE τ (extendMx (ancSetReach S xs) g x)
            ((S.shapeDef x).extTeAt (extendPick (ancSetReach S xs) p x))) ∧
        (∀ x ∈ ancSetReach S xs, ∀ u, (S.shapeDef x).restrOf = some u →
          restr ((ancReach S x).biUnion (extendMx (ancSetReach S xs) g)) u) := by
  have hSet : ancSetReach S xs = S.ancSet xs := ancSetReach_eq_ancSet hXC hxs
  constructor
  · rintro ⟨M', Mx, pick, ⟨hdisj, hpw, hunion⟩, hshape, hext, hrestr⟩
    have hM'sub : M' ⊆ M := hunion ▸ Finset.subset_union_left
    have hMxsub : ∀ x ∈ ancSetReach S xs, Mx x ⊆ M := fun x hx =>
      (Finset.subset_biUnion_of_mem Mx (hSet ▸ hx)).trans (hunion ▸ Finset.subset_union_right)
    obtain ⟨p, hpmem, hpeq⟩ :=
      exists_pickBound_eq_extTeAt (S := S) (Idx := ancSetReach S xs) pick
    refine ⟨M', Finset.mem_powerset.mpr hM'sub, fun a _ => Mx a, ?_, p, hpmem, ?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_pi]; intro a ha; exact Finset.mem_powerset.mpr (hMxsub a ha)
    · have hEq : ∀ x ∈ ancSetReach S xs, extendMx (ancSetReach S xs) (fun a _ => Mx a) x = Mx x :=
        fun x hx => extendMx_eq hx
      exact (DisjointUnionOn_congr hEq).mpr (hSet ▸ ⟨hdisj, hpw, hunion⟩)
    · exact hshape
    · intro x hx
      rw [extendMx_eq hx, hpeq x hx]
      exact hext x (hSet ▸ hx)
    · intro x hx u hu
      have hxX : x ∈ S.X := ancSetReach_subset_X hXC hxs hx
      have hEq : ∀ y ∈ ancReach S x, Mx y = extendMx (ancSetReach S xs) (fun a _ => Mx a) y :=
        fun y hy =>
          (extendMx_eq (g := fun a _ => Mx a) (ancReach_subset_ancSetReach hXC hxs hx hy)).symm
      have hb : (S.anc x).biUnion Mx = (ancReach S x).biUnion
          (extendMx (ancSetReach S xs) (fun a _ => Mx a)) := by
        rw [← ancReach_eq_anc hXC hxX]; exact Finset.biUnion_congr rfl hEq
      rw [← hb]
      exact hrestr x (hSet ▸ hx) u hu
  · rintro ⟨M', hM'mem, g, hgmem, p, hpmem, hdisj, hshape, hext, hrestr⟩
    refine ⟨M', extendMx (ancSetReach S xs) g, extendPick (ancSetReach S xs) p,
      hSet ▸ hdisj, hshape, ?_, ?_⟩
    · intro x hx
      exact hext x (hSet ▸ hx)
    · intro x hx u hu
      have hxX : x ∈ S.X := ancSetReach_subset_X hXC hxs (hSet ▸ hx)
      rw [← ancReach_eq_anc hXC hxX]
      exact hrestr x (hSet ▸ hx) u hu

/-- One layer of Table 3 is decidable on the `MOk` fragment (refer to the
section docstring above `ShapeExpr.MOk`), if `restr` is decidable on it.
It needs these items:

* `S.XClosed`, so that `anc` and `ancSet` compute.
* `S.RestrOk`, so that each `restr(x)` that the evaluation reaches stays
  in the `MOk` fragment.
* A proof of `s.MOk S`.

The proof is by structural recursion on `s`. -/
def satisfiesMAt_decidable (S : Schema) (τ : Typing) (restr : Finset Triple → ShapeExpr → Prop)
    (hXC : S.XClosed) (hRestr : S.RestrOk)
    (hr : ∀ N u, u.MOk S → Decidable (restr N u)) :
    ∀ (M : Finset Triple) (s : ShapeExpr), s.MOk S → Decidable (SatisfiesMAt S τ restr M s)
  | _, .constraint _, hOk => by exfalso; exact hOk
  | M, .ofShape h, _ => decidableSatisfiesShape τ M h
  | M, .or s1 s2, hOk => by
      haveI := satisfiesMAt_decidable S τ restr hXC hRestr hr M s1 hOk.1
      haveI := satisfiesMAt_decidable S τ restr hXC hRestr hr M s2 hOk.2
      exact instDecidableOr
  | M, .and s1 s2, hOk => by
      haveI := satisfiesMAt_decidable S τ restr hXC hRestr hr M s1 hOk.1
      haveI := satisfiesMAt_decidable S τ restr hXC hRestr hr M s2 hOk.2
      exact instDecidableAnd
  | M, .not s, hOk => by
      haveI := satisfiesMAt_decidable S τ restr hXC hRestr hr M s hOk
      exact instDecidableNot
  | M, .extends xs hs, hOk => by
      show Decidable (∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        (∃ h ∈ hs, SatisfiesShape τ M' h) ∧
        (∀ x ∈ S.ancSet xs, SatisfiesE τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          restr ((S.anc x).biUnion Mx) u))
      set Idx := ancSetReach S xs
      haveI hRestrClause : ∀ N : Finset Triple, ∀ x ∈ Idx,
          Decidable (∀ u, (S.shapeDef x).restrOf = some u → restr N u) :=
        fun N x hx => by
          rcases hu : (S.shapeDef x).restrOf with _ | u0
          · exact isTrue (fun u h => absurd h (by simp))
          · haveI := hr N u0 (hRestr x (ancSetReach_subset_X hXC hOk hx) u0 hu)
            exact decidable_of_iff (restr N u0)
              ⟨fun h u heq => by cases heq; exact h, fun h => h u0 rfl⟩
      haveI hMain : ∀ M' : Finset Triple, ∀ g : ∀ a ∈ Idx, Finset Triple,
          ∀ p : ∀ a ∈ Idx, ℕ,
          Decidable (DisjointUnionOn M M' Idx (extendMx Idx g) ∧
            (∃ h ∈ hs, SatisfiesShape τ M' h) ∧
            (∀ x (hx : x ∈ Idx), SatisfiesE τ (extendMx Idx g x)
              ((S.shapeDef x).extTeAt (extendPick Idx p x))) ∧
            (∀ x (hx : x ∈ Idx), ∀ u, (S.shapeDef x).restrOf = some u →
              restr ((ancReach S x).biUnion (extendMx Idx g)) u)) :=
        fun M' g p => by
          haveI hRestrDec : ∀ x (hx : x ∈ Idx),
              Decidable (∀ u, (S.shapeDef x).restrOf = some u →
                restr ((ancReach S x).biUnion (extendMx Idx g)) u) :=
            fun x hx => hRestrClause ((ancReach S x).biUnion (extendMx Idx g)) x hx
          haveI hd2 : Decidable (∀ x (hx : x ∈ Idx), ∀ u, (S.shapeDef x).restrOf = some u →
              restr ((ancReach S x).biUnion (extendMx Idx g)) u) :=
            @Multiset.decidableDforallMultiset _ Idx.val
              (fun a _ => ∀ u, (S.shapeDef a).restrOf = some u →
                restr ((ancReach S a).biUnion (extendMx Idx g)) u) hRestrDec
          infer_instance
      haveI hBounded : Decidable (∃ M' ∈ M.powerset, ∃ g ∈ Finset.pi Idx (fun _ => M.powerset),
          ∃ p ∈ Finset.pi Idx (ShapeExpr.pickBound S),
          DisjointUnionOn M M' Idx (extendMx Idx g) ∧
            (∃ h ∈ hs, SatisfiesShape τ M' h) ∧
            (∀ x (hx : x ∈ Idx), SatisfiesE τ (extendMx Idx g x)
              ((S.shapeDef x).extTeAt (extendPick Idx p x))) ∧
            (∀ x (hx : x ∈ Idx), ∀ u, (S.shapeDef x).restrOf = some u →
              restr ((ancReach S x).biUnion (extendMx Idx g)) u)) :=
        @Finset.decidableExistsAndFinset (Finset Triple) M.powerset _
          (fun M' => @Finset.decidableExistsAndFinset (∀ a ∈ Idx, Finset Triple)
            (Finset.pi Idx (fun _ => M.powerset)) _
            (fun g => @Finset.decidableExistsAndFinset (∀ a ∈ Idx, ℕ)
              (Finset.pi Idx (ShapeExpr.pickBound S)) _ (fun p => hMain M' g p)))
      exact decidable_of_iff _ (satisfiesExtends_iff_bounded hXC hOk).symm

/-- `SatisfiesMFuel` is decidable on the `MOk` fragment. The proof is by
recursion on the fuel. Each layer is `satisfiesMAt_decidable`. -/
def satisfiesMFuel_decidable (S : Schema) (τ : Typing) (hXC : S.XClosed) (hRestr : S.RestrOk) :
    ∀ (fuel : ℕ) (M : Finset Triple) (s : ShapeExpr), s.MOk S →
      Decidable (SatisfiesMFuel fuel S τ M s)
  | 0 => satisfiesMAt_decidable S τ _ hXC hRestr (fun _ _ _ => instDecidableFalse)
  | fuel + 1 => satisfiesMAt_decidable S τ _ hXC hRestr (satisfiesMFuel_decidable S τ hXC hRestr fuel)

/-- The fragment of `ShapeExpr` where the decidability of `SatisfiesFuel`
applies. It is similar to `MOk`:

* `.constraint c` is permitted here (rule 6 does not need `subjectOf`).
  Thus, it needs only the decidability of `c`.
* `.ofShape` and `.extends` go to `SatisfiesMFuel`. They need exactly what
  `MOk` needs at that node (trivially true, or `xs ⊆ S.X`).

This is a `Type`, not a `Prop` as `MOk` is. The `.constraint` leaf must
contain a real `DecidablePred c` witness, not only a statement that one
exists. With `Nonempty (DecidablePred c)`, you need `Classical.choice` to
get the witness. This adds again the noncomputability that this file
avoids. -/
def ShapeExpr.FOk (S : Schema) : ShapeExpr → Type
  | .constraint c => DecidablePred c
  | .ofShape _ => PUnit
  | .extends xs _ => PLift (xs ⊆ S.X)
  | .or s1 s2 => s1.FOk S × s2.FOk S
  | .and s1 s2 => s1.FOk S × s2.FOk S
  | .not s => s.FOk S

/-- `SatisfiesFuel` is decidable on the `FOk` fragment. The `.ofShape` and
`.extends` cases of Table 2 (rules 11 and 12) go directly to
`SatisfiesMFuel` on `neigh G n`. Thus, the proof is
`satisfiesMFuel_decidable`, and also:

* Rule 6 (`.constraint`), with the `DecidablePred c` of `FOk`.
* `or`, `and` and `not` (rules 7–9). -/
def satisfiesFuel_decidable (S : Schema) (G : Graph) (τ : Typing)
    (hXC : S.XClosed) (hRestr : S.RestrOk) (fuel : ℕ) :
    ∀ (n : RDFNode) (s : ShapeExpr), s.FOk S → Decidable (SatisfiesFuel fuel S G τ n s)
  | n, .constraint _, hOk => hOk n
  | n, .ofShape h, _ =>
      satisfiesMFuel_decidable S τ hXC hRestr fuel (neigh G n) (.ofShape h) trivial
  | n, .extends xs hs, hOk =>
      satisfiesMFuel_decidable S τ hXC hRestr fuel (neigh G n) (.extends xs hs) hOk.down
  | n, .or s1 s2, hOk =>
      @instDecidableOr _ _ (satisfiesFuel_decidable S G τ hXC hRestr fuel n s1 hOk.1)
        (satisfiesFuel_decidable S G τ hXC hRestr fuel n s2 hOk.2)
  | n, .and s1 s2, hOk =>
      @instDecidableAnd _ _ (satisfiesFuel_decidable S G τ hXC hRestr fuel n s1 hOk.1)
        (satisfiesFuel_decidable S G τ hXC hRestr fuel n s2 hOk.2)
  | n, .not s, hOk => @instDecidableNot _ (satisfiesFuel_decidable S G τ hXC hRestr fuel n s hOk)

end ShexLean.InheritanceDisjunction
