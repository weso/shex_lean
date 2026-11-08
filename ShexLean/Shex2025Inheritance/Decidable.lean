import ShexLean.Common.FixedPoint
import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2017Schemas.RepBound
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Pi

/-!
This file makes the semantics of the 2025 paper "Shape Expressions with
Inheritance" decidable. It is the 2025 equivalent of
`ShexLean.Shex2017Schemas.Decidable`. Two problems make this work larger
than in the 2017 case:

1. `Schema.anc` and `Schema.ancSet` (the ancestor sets of rule 18 of
   Table 3, in `Syntax.lean`) are `noncomputable`. They use
   `Classical.decPred`, because Mathlib has no general `Decidable`
   instance for the reflexive-transitive closure. This file proves that
   the same declarative proposition ("there is a path in `H_S`") is
   decidable with one hypothesis that Definition 3 already assumes: the
   edges of `H_S` out of each `x ∈ X` stay in `X`. (`Schema.XClosed`
   below makes explicit the statement of Definition 3 "the vertex set of
   `H_S` is `X`".) This file does not change `Schema.anc` and `ancSet`.
   `ancReach` and `ancSetReach` below are separate computable definitions,
   and the file proves that they are equal to `anc` and `ancSet`.
2. `NodeConstraint := RDFNode → Prop` (rule 13 of Table 3,
   `.constraint c`) is a general predicate with no canonical decision
   procedure. (The concrete `ValueDescr` of 2017 has one.) Thus, you can
   decide `SatisfiesMFuel` and `SatisfiesFuel` only if you give a
   `DecidablePred c` for each `c` that a schema uses. These instances go
   explicitly through the definitions below.
-/

namespace ShexLean.Inheritance

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

/-! ### `Me` and `Mnotin`, made computable

`Me` and `Mnotin` never needed `Classical.decPred`, as `anc` and `ancSet`
did. The existential `∃ z, (t.pred,z) ∈ e.tcs ∧ τ.has t.obj z` is already
bounded to the finite `e.tcs`. But the instance search of Lean does not
recognize this form, because, as written, `z` goes over all of `Label`.
When we write it as a bounded search over `e.tcs`, the same proposition
becomes directly decidable, with no extra hypothesis. -/

theorem meCond_iff_bounded (τ : Typing) (e : TripleExpr) (t : Triple) :
    (∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z) ↔
      ∃ p ∈ e.tcs, p.1 = t.pred ∧ τ.has t.obj p.2 := by
  constructor
  · rintro ⟨z, hz, hty⟩
    exact ⟨(t.pred, z), hz, rfl, hty⟩
  · rintro ⟨p, hp, heq, hty⟩
    exact ⟨p.2, heq ▸ hp, hty⟩

instance decidableMeCond (τ : Typing) (e : TripleExpr) (t : Triple) :
    Decidable (∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z) :=
  decidable_of_iff _ (meCond_iff_bounded τ e t).symm

/-- The computable `Me`. A proof shows that it is equal to the original. -/
def MeReach (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  M.filter (fun t => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)

theorem MeReach_eq_Me {τ : Typing} {M : Finset Triple} {e : TripleExpr} :
    MeReach τ M e = Me τ M e := by
  ext t
  unfold MeReach
  simp only [Finset.mem_filter]
  rw [mem_Me]

/-- The computable `Mnotin`. A proof shows that it is equal to the
original. -/
def MnotinReach (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  (M.filter (fun t => t.pred ∈ e.props)) \ MeReach τ M e

theorem MnotinReach_eq_Mnotin {τ : Typing} {M : Finset Triple} {e : TripleExpr} :
    MnotinReach τ M e = Mnotin τ M e := by
  unfold MnotinReach
  rw [MeReach_eq_Me]
  ext t
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  rw [mem_Mnotin]

/-! ### The unbounded repetition of `.star`, made decidable

The method of the 2017 `.rep` (a chain of the repeated sub-expression)
does not work here. Each piece of a `.star` witness is checked at the same
`Fuel`, not at a smaller one. Thus, if we encode "repeated `k` times" as a
chain of `k` `.seq`, the chain needs `k` fuel only to unfold. This is not
correct.

In its place, we decide the existence of a partition directly, by
well-founded recursion on `M.card` (`existsPartitionFuel`). Each step
removes, from the remaining triples, one nonempty piece that satisfies `Q`.
The bound uses the same `Finset` argument as the proof for the 2017 `.rep`
(`ShexLean.Shex2017Schemas.RepBound`). The nonempty pieces are pairwise
disjoint subsets of `M`. Thus, there are `M.card` or fewer of them. No
padding is necessary here, because `.star` has no minimum number of
repetitions. -/

open ShexLean (mem_subset_foldr_union disjoint_foldr_union_of_forall
  foldr_union_filter_nonempty nonempty_filter_length_le_card)

/-- `M` splits into a list of pieces, and each piece satisfies `Q`. This is
the form of the witness of rule 5 of Table 1. -/
def existsPartition (Q : Finset Triple → Prop) (M : Finset Triple) : Prop :=
  ∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧ ∀ Ni ∈ Ns, Q Ni

/-- The form with only nonempty pieces. `.star` needs no padding to get
this form, because it has no `min` to satisfy (the 2017 `.rep` has
one). -/
theorem existsPartition_iff_nonempty (Q : Finset Triple → Prop) (M : Finset Triple) :
    existsPartition Q M ↔
      ∃ Ns : List (Finset Triple), (∀ Ni ∈ Ns, Ni.Nonempty) ∧ DisjointUnionList M Ns ∧
        ∀ Ni ∈ Ns, Q Ni := by
  constructor
  · rintro ⟨Ns, ⟨hpw, hunion⟩, hQ⟩
    refine ⟨Ns.filter (·.Nonempty), fun Ni hNi => by simpa using (List.mem_filter.mp hNi).2,
      ⟨hpw.filter _, ?_⟩, fun Ni hNi => hQ Ni (List.mem_of_mem_filter hNi)⟩
    rw [hunion]; exact foldr_union_filter_nonempty Ns
  · rintro ⟨Ns, -, hd, hQ⟩
    exact ⟨Ns, hd, hQ⟩

/-- The one-step recursive characterization. One of these is true:

* `M` is empty (the empty list is a witness).
* You can remove a nonempty piece that satisfies `Q`. The remaining
  problem (`M \ piece`) is strictly smaller. -/
theorem existsPartitionNE_iff (Q : Finset Triple → Prop) (M : Finset Triple) :
    (∃ Ns : List (Finset Triple), (∀ Ni ∈ Ns, Ni.Nonempty) ∧ DisjointUnionList M Ns ∧
        ∀ Ni ∈ Ns, Q Ni) ↔
      M = ∅ ∨ ∃ piece ∈ M.powerset, piece.Nonempty ∧ Q piece ∧
        ∃ Ns : List (Finset Triple), (∀ Ni ∈ Ns, Ni.Nonempty) ∧
          DisjointUnionList (M \ piece) Ns ∧ ∀ Ni ∈ Ns, Q Ni := by
  constructor
  · rintro ⟨Ns, hne, ⟨hpw, hunion⟩, hQ⟩
    match Ns, hne, hpw, hunion, hQ with
    | [], _, _, hunion, _ => exact Or.inl (by simpa using hunion)
    | N1 :: Ns', hne, hpw, hunion, hQ =>
        rw [List.pairwise_cons] at hpw
        have hN1sub : N1 ⊆ M := by
          rw [hunion, List.foldr_cons]; exact Finset.subset_union_left
        refine Or.inr ⟨N1, Finset.mem_powerset.mpr hN1sub, hne N1 List.mem_cons_self,
          hQ N1 List.mem_cons_self, Ns', fun Ni hNi => hne Ni (List.mem_cons_of_mem _ hNi),
          ⟨hpw.2, ?_⟩, fun Ni hNi => hQ Ni (List.mem_cons_of_mem _ hNi)⟩
        have hdisj : Disjoint N1 (Ns'.foldr (· ∪ ·) ∅) := disjoint_foldr_union_of_forall hpw.1
        rw [hunion, List.foldr_cons, Finset.union_sdiff_cancel_left hdisj]
  · rintro (rfl | ⟨piece, hpiece, hne, hQpiece, Ns, hnsne, ⟨hpw, hunion⟩, hQ⟩)
    · exact ⟨[], by simp, ⟨List.Pairwise.nil, rfl⟩, by simp⟩
    · have hpsub : piece ⊆ M := Finset.mem_powerset.mp hpiece
      refine ⟨piece :: Ns, ?_, ⟨?_, ?_⟩, ?_⟩
      · intro Ni hNi
        rcases List.mem_cons.mp hNi with rfl | hNi
        · exact hne
        · exact hnsne Ni hNi
      · rw [List.pairwise_cons]
        refine ⟨fun a ha => ?_, hpw⟩
        have hasub : a ⊆ M \ piece := hunion ▸ mem_subset_foldr_union ha
        exact Finset.disjoint_left.mpr fun x hx1 hx2 => (Finset.mem_sdiff.mp (hasub hx2)).2 hx1
      · rw [List.foldr_cons, ← hunion, Finset.union_sdiff_of_subset hpsub]
      · intro Ni hNi
        rcases List.mem_cons.mp hNi with rfl | hNi
        · exact hQpiece
        · exact hQ Ni hNi

/-- `existsPartition` is decidable, with an explicit `Fuel` parameter.
This is the same method as `SatisfiesEFuel`: structural recursion from
`fuel+1` to `fuel`. We do not use a well-founded recursion measured by
`Finset.card`. That recursion compiles to `WellFounded.fix`, which does
not reduce, so it cannot decide anything.

`M.card ≤ fuel` justifies each case. At `fuel = 0`, it forces `M = ∅`. At
each recursive step, `fuel` covers `(M \ piece).card`. -/
def existsPartitionFuel (Q : Finset Triple → Prop) (hQ : ∀ N', Decidable (Q N')) :
    ∀ (fuel : ℕ) (M : Finset Triple), M.card ≤ fuel → Decidable (existsPartition Q M)
  | 0, M, hle => by
      have hM : M = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hle)
      exact isTrue (hM ▸ ⟨[], ⟨List.Pairwise.nil, rfl⟩, by simp⟩)
  | fuel + 1, M, _ => by
      rw [existsPartition_iff_nonempty, existsPartitionNE_iff]
      haveI : DecidablePred (Q ·) := hQ
      haveI hrec : ∀ piece : Finset Triple, piece ⊆ M → piece.Nonempty →
          Decidable (∃ Ns : List (Finset Triple), (∀ Ni ∈ Ns, Ni.Nonempty) ∧
            DisjointUnionList (M \ piece) Ns ∧ ∀ Ni ∈ Ns, Q Ni) :=
        fun piece hpM hne =>
          @decidable_of_iff _ (existsPartition Q (M \ piece))
            (existsPartition_iff_nonempty Q (M \ piece))
            (existsPartitionFuel Q hQ fuel (M \ piece)
              (by have := Finset.card_lt_card (Finset.sdiff_ssubset hpM hne); omega))
      haveI hstep : ∀ (piece : Finset Triple), piece ⊆ M → Decidable
          (piece.Nonempty ∧ Q piece ∧ ∃ Ns : List (Finset Triple), (∀ Ni ∈ Ns, Ni.Nonempty) ∧
            DisjointUnionList (M \ piece) Ns ∧ ∀ Ni ∈ Ns, Q Ni) :=
        fun piece hsub => by
          by_cases hne : piece.Nonempty
          · haveI := hrec piece hsub hne
            haveI : Decidable (Q piece) := hQ piece
            infer_instance
          · exact isFalse (fun h => hne h.1)
      haveI hboundedEx : Decidable (∃ piece, ∃ _ : piece ⊆ M,
          piece.Nonempty ∧ Q piece ∧ ∃ Ns : List (Finset Triple), (∀ Ni ∈ Ns, Ni.Nonempty) ∧
            DisjointUnionList (M \ piece) Ns ∧ ∀ Ni ∈ Ns, Q Ni) :=
        @Finset.decidableExistsOfDecidableSubsets _ M _ hstep
      have hiff : (∃ piece, ∃ _ : piece ⊆ M,
          piece.Nonempty ∧ Q piece ∧ ∃ Ns : List (Finset Triple), (∀ Ni ∈ Ns, Ni.Nonempty) ∧
            DisjointUnionList (M \ piece) Ns ∧ ∀ Ni ∈ Ns, Q Ni) ↔
          (∃ piece ∈ M.powerset, piece.Nonempty ∧ Q piece ∧
            ∃ Ns : List (Finset Triple), (∀ Ni ∈ Ns, Ni.Nonempty) ∧
              DisjointUnionList (M \ piece) Ns ∧ ∀ Ni ∈ Ns, Q Ni) := by
        simp only [Finset.mem_powerset, exists_prop]
      exact @instDecidableOr _ _ (inferInstance : Decidable (M = ∅))
        (decidable_of_iff _ hiff)

/-- The wrapper with no `Fuel`. Each `Finset Triple` needs `M.card` fuel or
less. -/
def existsPartitionDecidable (Q : Finset Triple → Prop) (hQ : ∀ N', Decidable (Q N'))
    (M : Finset Triple) : Decidable (existsPartition Q M) :=
  existsPartitionFuel Q hQ M.card M (le_refl _)

/-! ### `SatisfiesEFuel` (Table 1) is decidable -/

/-- Rule 2 of Table 1 (`.tc`), written as a search bounded to `M`. This is
the same as `matches_tPattern_iff` of 2017, but simpler, because the
property `p` of `.tc` is one fixed `IRI`, not a full `PropSet`. -/
theorem satisfiesTc_iff_bounded (τ : Typing) (p : IRI) (z : Label) (M : Finset Triple) :
    (∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z) ↔
      ∃ t ∈ M, M = {t} ∧ t.pred = p ∧ τ.has t.obj z := by
  constructor
  · rintro ⟨n, o, hM, hty⟩
    exact ⟨⟨n, p, o⟩, hM ▸ Finset.mem_singleton_self _, hM, rfl, hty⟩
  · rintro ⟨t, -, hM, hp, hty⟩
    refine ⟨t.subj, t.obj, ?_, hty⟩
    rw [hM, ← hp]

/-- `e1;e2` of Table 1 (rule 4), written as a search bounded to
`M.powerset`. This is the same as `matches_eachOf_iff` of 2017. -/
theorem satisfiesSeq_iff_bounded (S : Schema) (G : Graph) (τ : Typing) (M : Finset Triple)
    (e1 e2 : TripleExpr) (fuel : ℕ) :
    (∃ M1 M2, DisjointUnion M M1 M2 ∧ SatisfiesEFuel fuel S G τ M1 e1 ∧
        SatisfiesEFuel fuel S G τ M2 e2) ↔
      ∃ M1 ∈ M.powerset, ∃ M2 ∈ M.powerset,
        DisjointUnion M M1 M2 ∧ SatisfiesEFuel fuel S G τ M1 e1 ∧
          SatisfiesEFuel fuel S G τ M2 e2 := by
  constructor
  · rintro ⟨M1, M2, hdisj, hm1, hm2⟩
    have hM1 : M1 ⊆ M := hdisj.2 ▸ Finset.subset_union_left
    have hM2 : M2 ⊆ M := hdisj.2 ▸ Finset.subset_union_right
    exact ⟨M1, Finset.mem_powerset.mpr hM1, M2, Finset.mem_powerset.mpr hM2, hdisj, hm1, hm2⟩
  · rintro ⟨M1, -, M2, -, hdisj, hm1, hm2⟩
    exact ⟨M1, M2, hdisj, hm1, hm2⟩

/-- `SatisfiesEFuel` is decidable with no condition. Table 1 never uses
`NodeConstraint` or `extends`. Thus, it needs no extra hypotheses, as
`SatisfiesMFuel` and `SatisfiesFuel` below do. The proof is by structural
recursion on `(fuel, e)`, and follows the equations of `SatisfiesEFuel`. -/
def satisfiesEFuel_decidable :
    ∀ (fuel : ℕ) (S : Schema) (G : Graph) (τ : Typing) (M : Finset Triple) (e : TripleExpr),
      Decidable (SatisfiesEFuel fuel S G τ M e)
  | 0, _, _, _, _, _ => by show Decidable False; infer_instance
  | _ + 1, _, _, _, M, .empty => by show Decidable (M = ∅); infer_instance
  | _ + 1, _, _, τ, M, .tc p z => by
      show Decidable (∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z)
      exact decidable_of_iff _ (satisfiesTc_iff_bounded τ p z M).symm
  | fuel + 1, S, G, τ, M, .choice e1 e2 => by
      show Decidable (SatisfiesEFuel fuel S G τ M e1 ∨ SatisfiesEFuel fuel S G τ M e2)
      haveI := satisfiesEFuel_decidable fuel S G τ M e1
      haveI := satisfiesEFuel_decidable fuel S G τ M e2
      infer_instance
  | fuel + 1, S, G, τ, M, .seq e1 e2 => by
      show Decidable (∃ M1 M2, DisjointUnion M M1 M2 ∧
        SatisfiesEFuel fuel S G τ M1 e1 ∧ SatisfiesEFuel fuel S G τ M2 e2)
      haveI hd2 : ∀ M1 M2 : Finset Triple, Decidable
          (DisjointUnion M M1 M2 ∧ SatisfiesEFuel fuel S G τ M1 e1 ∧
            SatisfiesEFuel fuel S G τ M2 e2) :=
        fun M1 M2 => by
          haveI : Decidable (DisjointUnion M M1 M2) := by
            show Decidable (Disjoint M1 M2 ∧ M = M1 ∪ M2); infer_instance
          haveI := satisfiesEFuel_decidable fuel S G τ M1 e1
          haveI := satisfiesEFuel_decidable fuel S G τ M2 e2
          infer_instance
      have hd1 : ∀ M1 : Finset Triple, Decidable (∃ M2 ∈ M.powerset,
          DisjointUnion M M1 M2 ∧ SatisfiesEFuel fuel S G τ M1 e1 ∧
            SatisfiesEFuel fuel S G τ M2 e2) :=
        fun M1 => @Finset.decidableExistsAndFinset (Finset Triple) M.powerset _ (hd2 M1)
      exact @decidable_of_iff _ _ (satisfiesSeq_iff_bounded S G τ M e1 e2 fuel).symm
        (@Finset.decidableExistsAndFinset (Finset Triple) M.powerset _ hd1)
  | fuel + 1, S, G, τ, M, .star e => by
      show Decidable (existsPartition (SatisfiesEFuel fuel S G τ · e) M)
      exact existsPartitionDecidable _ (fun N' => satisfiesEFuel_decidable fuel S G τ N' e) M

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

/-- Extends a dependent witness `g : ∀ a ∈ Idx, Finset Triple` (as in
`Finset.pi`) to an ordinary `Label → Finset Triple`. Outside `Idx`, the
result is a junk value (`∅`). Rule 18 needs this for its
`Mx : Label → Finset Triple`, written as a bounded search over
`Idx = ancSetReach S xs`. -/
def extendMx (Idx : Finset Label) (g : ∀ a ∈ Idx, Finset Triple) :
    Label → Finset Triple :=
  fun x => if h : x ∈ Idx then g x h else ∅

theorem extendMx_eq {Idx : Finset Label} {g : ∀ a ∈ Idx, Finset Triple}
    {x : Label} (hx : x ∈ Idx) : extendMx Idx g x = g x hx := by
  unfold extendMx; simp [hx]

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

/-- `DisjointUnionOn` uses `Mx` only at points of `Idx`. Thus, two
functions that agree there give the same proposition. Because of this, the
decidability proof of rule 18 can replace `Mx` with `extendMx Idx g` (which
is `Mx` on `Idx`, and a junk value at other points). -/
theorem DisjointUnionOn_congr {M M' : Finset Triple} {Idx : Finset Label}
    {Mx Mx' : Label → Finset Triple} (hEq : ∀ x ∈ Idx, Mx x = Mx' x) :
    DisjointUnionOn M M' Idx Mx ↔ DisjointUnionOn M M' Idx Mx' := by
  unfold DisjointUnionOn
  have hbU : Idx.biUnion Mx = Idx.biUnion Mx' := Finset.biUnion_congr rfl hEq
  rw [hbU]
  refine and_congr_right fun _ => and_congr ?_ Iff.rfl
  constructor
  · intro h a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    have hd : Disjoint (Mx a) (Mx b) := h ha hb hab
    rwa [hEq a ha, hEq b hb] at hd
  · intro h a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    have hd : Disjoint (Mx' a) (Mx' b) := h ha hb hab
    rwa [← hEq a ha, ← hEq b hb] at hd

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
theorem satisfiesExtends_iff_bounded {S : Schema} {G : Graph} {τ : Typing}
    (hXC : S.XClosed) {fuel : ℕ} {M : Finset Triple} {xs : Finset Label} {h : Shape}
    (hxs : xs ⊆ S.X) :
    (∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        SatisfiesMFuel fuel S G τ M' (.ofShape h) ∧
        (∀ x ∈ S.ancSet xs, SatisfiesEFuel fuel S G τ (Mx x) (S.shapeDef x).extTe) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          SatisfiesMFuel fuel S G τ ((S.anc x).biUnion Mx) u)) ↔
      ∃ M' ∈ M.powerset, ∃ g ∈ Finset.pi (ancSetReach S xs) (fun _ => M.powerset),
        DisjointUnionOn M M' (ancSetReach S xs) (extendMx (ancSetReach S xs) g) ∧
        SatisfiesMFuel fuel S G τ M' (.ofShape h) ∧
        (∀ x ∈ ancSetReach S xs,
          SatisfiesEFuel fuel S G τ (extendMx (ancSetReach S xs) g x) (S.shapeDef x).extTe) ∧
        (∀ x ∈ ancSetReach S xs, ∀ u, (S.shapeDef x).restrOf = some u →
          SatisfiesMFuel fuel S G τ
            ((ancReach S x).biUnion (extendMx (ancSetReach S xs) g)) u) := by
  have hSet : ancSetReach S xs = S.ancSet xs := ancSetReach_eq_ancSet hXC hxs
  constructor
  · rintro ⟨M', Mx, ⟨hdisj, hpw, hunion⟩, hshape, hext, hrestr⟩
    have hM'sub : M' ⊆ M := hunion ▸ Finset.subset_union_left
    have hMxsub : ∀ x ∈ ancSetReach S xs, Mx x ⊆ M := fun x hx =>
      (Finset.subset_biUnion_of_mem Mx (hSet ▸ hx)).trans (hunion ▸ Finset.subset_union_right)
    refine ⟨M', Finset.mem_powerset.mpr hM'sub, fun a _ => Mx a, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_pi]; intro a ha; exact Finset.mem_powerset.mpr (hMxsub a ha)
    · have hEq : ∀ x ∈ ancSetReach S xs, extendMx (ancSetReach S xs) (fun a _ => Mx a) x = Mx x :=
        fun x hx => extendMx_eq hx
      exact (DisjointUnionOn_congr hEq).mpr (hSet ▸ ⟨hdisj, hpw, hunion⟩)
    · exact hshape
    · intro x hx
      rw [extendMx_eq hx]; exact hext x (hSet ▸ hx)
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
  · rintro ⟨M', hM'mem, g, hgmem, hdisj, hshape, hext, hrestr⟩
    refine ⟨M', extendMx (ancSetReach S xs) g, hSet ▸ hdisj, hshape, ?_, ?_⟩
    · intro x hx
      exact hext x (hSet ▸ hx)
    · intro x hx u hu
      have hxX : x ∈ S.X := ancSetReach_subset_X hXC hxs (hSet ▸ hx)
      rw [← ancReach_eq_anc hXC hxX]
      exact hrestr x (hSet ▸ hx) u hu

/-! The decidability of `DisjointUnionOn`. It is necessary when `Mx` is a
concrete computable function (for example, `extendMx Idx g`). It writes
`Set.PairwiseDisjoint` as a double `∀` bounded by a `Finset`. -/

theorem pairwiseDisjoint_iff_bounded (Idx : Finset Label) (f : Label → Finset Triple) :
    (Idx : Set Label).PairwiseDisjoint f ↔
      ∀ a ∈ Idx, ∀ b ∈ Idx, a ≠ b → Disjoint (f a) (f b) := by
  unfold Set.PairwiseDisjoint Set.Pairwise
  constructor
  · intro h a ha b hb hab
    exact h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
  · intro h a ha b hb hab
    exact h a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab

instance decidablePairwiseDisjoint (Idx : Finset Label) (f : Label → Finset Triple) :
    Decidable ((Idx : Set Label).PairwiseDisjoint f) :=
  decidable_of_iff _ (pairwiseDisjoint_iff_bounded Idx f).symm

instance decidableDisjointUnionOn (M M' : Finset Triple) (Idx : Finset Label)
    (Mx : Label → Finset Triple) : Decidable (DisjointUnionOn M M' Idx Mx) := by
  unfold DisjointUnionOn; infer_instance

/-- `SatisfiesMFuel` is decidable on the `MOk` fragment (refer to the
section docstring above `ShapeExpr.MOk`). It needs these items:

* `S.XClosed`, so that `anc` and `ancSet` compute.
* `S.RestrOk`, so that each `restr(x)` that the evaluation reaches stays
  in the `MOk` fragment.
* A proof of `s.MOk S`.

The proof is by structural recursion on `(fuel, s)`. -/
def satisfiesMFuel_decidable (S : Schema) (G : Graph) (τ : Typing)
    (hXC : S.XClosed) (hRestr : S.RestrOk) :
    ∀ (fuel : ℕ) (M : Finset Triple) (s : ShapeExpr), s.MOk S →
      Decidable (SatisfiesMFuel fuel S G τ M s)
  | 0, _, _, _ => by show Decidable False; infer_instance
  | _ + 1, _, .constraint _, hOk => by exfalso; exact hOk
  | fuel + 1, M, .ofShape h, _ => by
      show Decidable (SatisfiesEFuel fuel S G τ (Me τ M h.triples) h.triples ∧
        props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
        (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅))
      haveI h1 : Decidable (SatisfiesEFuel fuel S G τ (Me τ M h.triples) h.triples) := by
        rw [← MeReach_eq_Me]
        exact satisfiesEFuel_decidable fuel S G τ (MeReach τ M h.triples) h.triples
      haveI h2 : Decidable (props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅) := by
        rw [← MnotinReach_eq_Mnotin]; infer_instance
      infer_instance
  | fuel + 1, M, .or s1 s2, hOk => by
      show Decidable (SatisfiesMFuel fuel S G τ M s1 ∨ SatisfiesMFuel fuel S G τ M s2)
      haveI := satisfiesMFuel_decidable S G τ hXC hRestr fuel M s1 hOk.1
      haveI := satisfiesMFuel_decidable S G τ hXC hRestr fuel M s2 hOk.2
      infer_instance
  | fuel + 1, M, .and s1 s2, hOk => by
      show Decidable (SatisfiesMFuel fuel S G τ M s1 ∧ SatisfiesMFuel fuel S G τ M s2)
      haveI := satisfiesMFuel_decidable S G τ hXC hRestr fuel M s1 hOk.1
      haveI := satisfiesMFuel_decidable S G τ hXC hRestr fuel M s2 hOk.2
      infer_instance
  | fuel + 1, M, .not s, hOk => by
      show Decidable (¬ SatisfiesMFuel fuel S G τ M s)
      haveI := satisfiesMFuel_decidable S G τ hXC hRestr fuel M s hOk
      infer_instance
  | fuel + 1, M, .extends xs h, hOk => by
      show Decidable (∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        SatisfiesMFuel fuel S G τ M' (.ofShape h) ∧
        (∀ x ∈ S.ancSet xs, SatisfiesEFuel fuel S G τ (Mx x) (S.shapeDef x).extTe) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          SatisfiesMFuel fuel S G τ ((S.anc x).biUnion Mx) u))
      set Idx := ancSetReach S xs
      haveI hRestrClause : ∀ N : Finset Triple, ∀ x ∈ Idx,
          Decidable (∀ u, (S.shapeDef x).restrOf = some u → SatisfiesMFuel fuel S G τ N u) :=
        fun N x hx => by
          rcases hu : (S.shapeDef x).restrOf with _ | u0
          · exact isTrue (fun u h => absurd h (by simp))
          · have hMOk : u0.MOk S := hRestr x (ancSetReach_subset_X hXC hOk hx) u0 hu
            haveI := satisfiesMFuel_decidable S G τ hXC hRestr fuel N u0 hMOk
            exact decidable_of_iff (SatisfiesMFuel fuel S G τ N u0)
              ⟨fun h u heq => by cases heq; exact h, fun h => h u0 rfl⟩
      haveI hMain : ∀ M' : Finset Triple, ∀ g : ∀ a ∈ Idx, Finset Triple,
          Decidable (DisjointUnionOn M M' Idx (extendMx Idx g) ∧
            SatisfiesMFuel fuel S G τ M' (.ofShape h) ∧
            (∀ x (hx : x ∈ Idx), SatisfiesEFuel fuel S G τ (extendMx Idx g x)
              (S.shapeDef x).extTe) ∧
            (∀ x (hx : x ∈ Idx), ∀ u, (S.shapeDef x).restrOf = some u →
              SatisfiesMFuel fuel S G τ ((ancReach S x).biUnion (extendMx Idx g)) u)) :=
        fun M' g => by
          haveI := satisfiesMFuel_decidable S G τ hXC hRestr fuel M' (.ofShape h) trivial
          haveI hExtDec : ∀ x (_ : x ∈ Idx),
              Decidable (SatisfiesEFuel fuel S G τ (extendMx Idx g x) (S.shapeDef x).extTe) :=
            fun x _ => satisfiesEFuel_decidable fuel S G τ (extendMx Idx g x) (S.shapeDef x).extTe
          haveI hRestrDec : ∀ x (hx : x ∈ Idx),
              Decidable (∀ u, (S.shapeDef x).restrOf = some u →
                SatisfiesMFuel fuel S G τ ((ancReach S x).biUnion (extendMx Idx g)) u) :=
            fun x hx => hRestrClause ((ancReach S x).biUnion (extendMx Idx g)) x hx
          haveI hd1 : Decidable (∀ x (hx : x ∈ Idx), SatisfiesEFuel fuel S G τ
              (extendMx Idx g x) (S.shapeDef x).extTe) :=
            @Multiset.decidableDforallMultiset _ Idx.val
              (fun a _ => SatisfiesEFuel fuel S G τ (extendMx Idx g a) (S.shapeDef a).extTe) hExtDec
          haveI hd2 : Decidable (∀ x (hx : x ∈ Idx), ∀ u, (S.shapeDef x).restrOf = some u →
              SatisfiesMFuel fuel S G τ ((ancReach S x).biUnion (extendMx Idx g)) u) :=
            @Multiset.decidableDforallMultiset _ Idx.val
              (fun a _ => ∀ u, (S.shapeDef a).restrOf = some u →
                SatisfiesMFuel fuel S G τ ((ancReach S a).biUnion (extendMx Idx g)) u) hRestrDec
          infer_instance
      haveI hBounded : Decidable (∃ M' ∈ M.powerset, ∃ g ∈ Finset.pi Idx (fun _ => M.powerset),
          DisjointUnionOn M M' Idx (extendMx Idx g) ∧
            SatisfiesMFuel fuel S G τ M' (.ofShape h) ∧
            (∀ x (hx : x ∈ Idx), SatisfiesEFuel fuel S G τ (extendMx Idx g x)
              (S.shapeDef x).extTe) ∧
            (∀ x (hx : x ∈ Idx), ∀ u, (S.shapeDef x).restrOf = some u →
              SatisfiesMFuel fuel S G τ ((ancReach S x).biUnion (extendMx Idx g)) u)) :=
        @Finset.decidableExistsAndFinset (Finset Triple) M.powerset _
          (fun M' => @Finset.decidableExistsAndFinset (∀ a ∈ Idx, Finset Triple)
            (Finset.pi Idx (fun _ => M.powerset)) _ (fun g => hMain M' g))
      exact decidable_of_iff _ (satisfiesExtends_iff_bounded hXC hOk).symm

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
    (hXC : S.XClosed) (hRestr : S.RestrOk) :
    ∀ (fuel : ℕ) (n : RDFNode) (s : ShapeExpr), s.FOk S →
      Decidable (SatisfiesFuel fuel S G τ n s)
  | 0, _, _, _ => by show Decidable False; infer_instance
  | _ + 1, n, .constraint c, hOk => by
      show Decidable (c n)
      exact hOk n
  | fuel + 1, n, .ofShape h, _ => by
      show Decidable (SatisfiesMFuel fuel S G τ (neigh G n) (.ofShape h))
      exact satisfiesMFuel_decidable S G τ hXC hRestr fuel (neigh G n) (.ofShape h) trivial
  | fuel + 1, n, .extends xs h, hOk => by
      show Decidable (SatisfiesMFuel fuel S G τ (neigh G n) (.extends xs h))
      exact satisfiesMFuel_decidable S G τ hXC hRestr fuel (neigh G n) (.extends xs h) hOk.down
  | fuel + 1, n, .or s1 s2, hOk => by
      show Decidable (SatisfiesFuel fuel S G τ n s1 ∨ SatisfiesFuel fuel S G τ n s2)
      haveI := satisfiesFuel_decidable S G τ hXC hRestr fuel n s1 hOk.1
      haveI := satisfiesFuel_decidable S G τ hXC hRestr fuel n s2 hOk.2
      infer_instance
  | fuel + 1, n, .and s1 s2, hOk => by
      show Decidable (SatisfiesFuel fuel S G τ n s1 ∧ SatisfiesFuel fuel S G τ n s2)
      haveI := satisfiesFuel_decidable S G τ hXC hRestr fuel n s1 hOk.1
      haveI := satisfiesFuel_decidable S G τ hXC hRestr fuel n s2 hOk.2
      infer_instance
  | fuel + 1, n, .not s, hOk => by
      show Decidable (¬ SatisfiesFuel fuel S G τ n s)
      haveI := satisfiesFuel_decidable S G τ hXC hRestr fuel n s hOk
      infer_instance

end ShexLean.Inheritance
