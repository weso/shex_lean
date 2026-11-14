import ShexLean.Common.FixedPoint
import ShexLean.InheritanceCore.Schema

/-!
The ancestor sets `Schema.anc` and `Schema.ancSet` of rule 18, made computable.
They use `Classical.decPred`, because reachability over a general relation is not decidable.
With `Schema.XClosed` (the edges of `H_S` stay in `X`,
as Definition 3 assumes), `ancReach` and `ancSetReach`
compute the same sets by a fixed-point iteration.
The `Decidable.lean` files of `ShexLean/Shex2025Inheritance/`
and `ShexLean/Shex2026InheritanceDisjunction/` use them.
-/

namespace ShexLean.InheritanceCore

variable {E : Type} [ShapeSyntax E]

/-! ### `Schema.anc` and `ancSet`, made computable -/

/-- The assumption of the paper for Definition 3: the edges of `H_S` never go out of `X`.
Thus, `H_S` is a graph on the vertex set `X`.
It is not a larger graph that is filtered after. -/
def Schema.XClosed (S : Schema E) : Prop :=
  ∀ x ∈ S.X, ShapeSyntax.extendsTargets (S.shapeDef x) ⊆ S.X

/-- One step of the closure of the ancestor set: add each `X` vertex that
is not yet in the current set and that one more `extEdge` step can reach. -/
private def ancStep (S : Schema E) (t : Finset Label) : Finset Label :=
  t ∪ S.X.filter (fun y' => ∃ y ∈ t, S.extEdge y y')

private theorem mem_ancStep_iff {S : Schema E} {t : Finset Label} {x' : Label} :
    x' ∈ ancStep S t ↔ x' ∈ t ∨ (x' ∈ S.X ∧ ∃ y ∈ t, S.extEdge y x') := by
  unfold ancStep
  rw [Finset.mem_union, Finset.mem_filter]

private theorem ancStep_subset_X {S : Schema E} : ∀ t ⊆ S.X, ancStep S t ⊆ S.X := by
  intro t ht
  unfold ancStep
  exact Finset.union_subset ht (Finset.filter_subset _ _)

private theorem subset_ancStep {S : Schema E} : ∀ t ⊆ S.X, t ⊆ ancStep S t :=
  fun _ _ => Finset.subset_union_left

private theorem iterate_subset_X {S : Schema E} {x : Label} (hx : x ∈ S.X) :
    ∀ n, (ancStep S)^[n] {x} ⊆ S.X := by
  intro n
  induction n with
  | zero => simpa using Finset.singleton_subset_iff.mpr hx
  | succ n ih => rw [Function.iterate_succ_apply']; exact ancStep_subset_X _ ih

private theorem start_subset_iterate {S : Schema E} {x : Label}
    (hx : x ∈ S.X) : ∀ n, ({x} : Finset Label) ⊆ (ancStep S)^[n] {x} := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (subset_ancStep _ (iterate_subset_X hx n))

/-- The computable ancestor set: iterate `ancStep` from `{x}` until it is stable.
This occurs in `(S.X \ {x}).card` steps or fewer (`Finset.increasing_iterate_fixed`). -/
def ancReach (S : Schema E) (x : Label) : Finset Label :=
  (ancStep S)^[(S.X \ {x}).card] {x}

/-- Each `extEdge` step out of a point of `S.X` that is reachable from `x` stays in `S.X`.
(This is the result of `XClosed`, applied along a path.) -/
private theorem reflTransGen_mem_X {S : Schema E} (hXC : S.XClosed) {x : Label} (hx : x ∈ S.X)
    {x' : Label} (h : Relation.ReflTransGen S.extEdge x x') : x' ∈ S.X := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact hXC _ ih hbc

/-- The forward direction: each point that the
iteration reaches is really reachable with `extEdge`. -/
private theorem reflTransGen_of_mem_iterate {S : Schema E} {x : Label} :
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

/-- The reverse direction: with `XClosed`, each point
that is reachable with `extEdge` is in `ancReach`.
(`ancReach` is exactly the fixed point of `ancStep`
from `{x}`, by `Finset.increasing_iterate_fixed`.) -/
private theorem mem_ancReach_of_reflTransGen {S : Schema E} (hXC : S.XClosed) {x : Label}
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

/-- `ancReach` is exactly `Schema.anc`, with the natural
closure hypothesis that Definition 3 already assumes. -/
theorem ancReach_eq_anc {S : Schema E} (hXC : S.XClosed) {x : Label} (hx : x ∈ S.X) :
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
def ancSetReach (S : Schema E) (xs : Finset Label) : Finset Label :=
  xs.biUnion (ancReach S)

theorem ancSetReach_eq_ancSet {S : Schema E} (hXC : S.XClosed) {xs : Finset Label}
    (hxs : xs ⊆ S.X) : ancSetReach S xs = S.ancSet xs := by
  unfold ancSetReach Schema.ancSet
  apply Finset.biUnion_congr rfl
  intro x hx
  exact ancReach_eq_anc hXC (hxs hx)

/-- The ancestors of a point in `ancSetReach S xs` stay in this set.
Because of this, it is sound to use `Mx` only at points
of `ancSetReach S xs` in the `restr(x)` clause of rule 18
(`(S.anc x).biUnion Mx`, where `x` is in the same set). -/
theorem ancReach_subset_ancSetReach {S : Schema E} (hXC : S.XClosed) {xs : Finset Label}
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

/-- Each point of `ancSetReach S xs` is also in `S.X`.
(It is a union of images of `S.anc`, and `S.anc _ ⊆ S.X` always, by construction.) -/
theorem ancSetReach_subset_X {S : Schema E} (hXC : S.XClosed) {xs : Finset Label}
    (hxs : xs ⊆ S.X) : ancSetReach S xs ⊆ S.X := by
  intro x hx
  rw [ancSetReach_eq_ancSet hXC hxs] at hx
  unfold Schema.ancSet at hx
  obtain ⟨x0, -, hx0⟩ := Finset.mem_biUnion.mp hx
  simp only [Schema.anc, Finset.mem_filter] at hx0
  exact hx0.1

end ShexLean.InheritanceCore
