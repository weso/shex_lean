import ShexLean.Common.FixedPoint
import ShexLean.Shex2026InheritanceDisjunction.Semantics
import ShexLean.Shex2017Schemas.RepBound
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Pi
import ShexLean.InheritanceCore.Decidable
import ShexLean.InheritanceCore.SchemaDecidable

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

open ShexLean.InheritanceCore hiding Schema

open ShexLean

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

/-- The extension of a dependent witness
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

/-- The conditions of rule 18 on the parts `M'` and `Mx` of a partition,
with the computable `ancReach` in place of `S.anc`, and the bounded search
for `pick` (`exists_pickBound_eq_extTeAt`). -/
def extendsBody (S : Schema) (τ : Typing) (restr : Finset Triple → ShapeExpr → Prop)
    (hs : List Shape) (Idx : Finset Label) (M' : Finset Triple) (Mx : Label → Finset Triple) :
    Prop :=
  (∃ h ∈ hs, SatisfiesShape τ M' h) ∧
  (∃ p ∈ Finset.pi Idx (ShapeExpr.pickBound S),
    ∀ x (_ : x ∈ Idx), SatisfiesE τ (Mx x) ((S.shapeDef x).extTeAt (extendPick Idx p x))) ∧
  (∀ x ∈ Idx, ∀ u, (S.shapeDef x).restrOf = some u → restr ((ancReach S x).biUnion Mx) u)

/-- The existential of rule 18 (`∃ M' Mx pick, ...`), as a bounded search
over the assignments of the triples of `M` to the parts
(`exists_disjointUnionOn_iff_assignments`) and over the bounded values of
`pick`. `ancSetReach S xs` and `ancReach S x` replace `S.ancSet xs` and
`S.anc x`. This is sound because `xs ⊆ S.X`, from the `MOk` requirement of
`.extends xs hs`. -/
theorem satisfiesExtends_iff_bounded {S : Schema} {τ : Typing}
    {restr : Finset Triple → ShapeExpr → Prop}
    (hXC : S.XClosed) {M : Finset Triple} {xs : Finset Label} {hs : List Shape}
    (hxs : xs ⊆ S.X) :
    (∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        (∃ h ∈ hs, SatisfiesShape τ M' h) ∧
        (∀ x ∈ S.ancSet xs, SatisfiesE τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          restr ((S.anc x).biUnion Mx) u)) ↔
      ∃ f ∈ assignments M (ancSetReach S xs), extendsBody S τ restr hs (ancSetReach S xs)
        (partOf M f none) (fun x => partOf M f (some x)) := by
  have hSet : ancSetReach S xs = S.ancSet xs := ancSetReach_eq_ancSet hXC hxs
  have hanc : ∀ x ∈ ancSetReach S xs, ancReach S x = S.anc x := fun x hx =>
    ancReach_eq_anc hXC (Schema.ancSet_subset_X (hSet ▸ hx))
  rw [← exists_disjointUnionOn_iff_assignments]
  · refine exists₂_congr fun M' Mx => ?_
    constructor
    · rintro ⟨pick, hdu, hsh, hext, hres⟩
      obtain ⟨p, hp, hpeq⟩ := exists_pickBound_eq_extTeAt (S := S) (Idx := ancSetReach S xs) pick
      refine ⟨hSet ▸ hdu, hsh, ⟨p, hp, fun x hx => ?_⟩, fun x hx u hu => ?_⟩
      · rw [hpeq x hx]; exact hext x (hSet ▸ hx)
      · rw [hanc x hx]; exact hres x (hSet ▸ hx) u hu
    · rintro ⟨hdu, hsh, ⟨p, -, hext⟩, hres⟩
      refine ⟨extendPick (ancSetReach S xs) p, hSet ▸ hdu, hsh, fun x hx => ?_, fun x hx u hu => ?_⟩
      · exact hext x (hSet ▸ hx)
      · rw [← hanc x (hSet ▸ hx)]; exact hres x (hSet ▸ hx) u hu
  · intro M' Mx Mx' hEq
    refine and_congr_right fun _ => and_congr ?_ ?_
    · exact exists_congr fun p => and_congr_right fun _ => forall₂_congr fun x hx => by rw [hEq x hx]
    · refine forall₂_congr fun x hx => forall₂_congr fun u _ => ?_
      rw [Finset.biUnion_congr rfl fun y hy => hEq y (ancReach_subset_ancSetReach hXC hxs hx hy)]

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
      haveI : ∀ M' Mx, Decidable (extendsBody S τ restr hs Idx M' Mx) := fun M' Mx => by
        unfold extendsBody
        haveI hd0 : Decidable (∃ h ∈ hs, SatisfiesShape τ M' h) :=
          @List.decidableBEx _ _ (fun h => decidableSatisfiesShape τ M' h) hs
        haveI hd1 : ∀ p : ∀ a ∈ Idx, ℕ, Decidable (∀ x (hx : x ∈ Idx),
            SatisfiesE τ (Mx x) ((S.shapeDef x).extTeAt (extendPick Idx p x))) := fun p =>
          @Multiset.decidableDforallMultiset _ Idx.val
            (fun a _ => SatisfiesE τ (Mx a) ((S.shapeDef a).extTeAt (extendPick Idx p a)))
            (fun a _ => satisfiesE_decidable τ _ _)
        haveI hd2 : Decidable (∀ x ∈ Idx, ∀ u, (S.shapeDef x).restrOf = some u →
            restr ((ancReach S x).biUnion Mx) u) :=
          @Multiset.decidableDforallMultiset _ Idx.val
            (fun a _ => ∀ u, (S.shapeDef a).restrOf = some u → restr ((ancReach S a).biUnion Mx) u)
            (fun a ha => hRestrClause _ a ha)
        exact @instDecidableAnd _ _ hd0 (@instDecidableAnd _ _
          (@Finset.decidableExistsAndFinset _ _ _ hd1) hd2)
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
