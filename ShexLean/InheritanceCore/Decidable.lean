import ShexLean.InheritanceCore.TripleMatch
import ShexLean.Shex2017Schemas.RepBound
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Pi

/-!
Decidability of Table 1 (`SatisfiesE`) and rule 17
(`SatisfiesShape`), and the helpers for the bounded
searches of rule 18 (`assignments`, `DisjointUnionOn`).
The `Decidable.lean` files of `ShexLean/Shex2025Inheritance/` and
`ShexLean/Shex2026InheritanceDisjunction/` use them for Table 3 and Table 2.
-/

namespace ShexLean.InheritanceCore

/-! ### `Me` and `Mnotin`, made computable

`Me` and `Mnotin` never needed `Classical.decPred`, as `anc` and `ancSet` did.
The existential `∃ z, (t.pred,z) ∈ e.tcs ∧ τ.has t.obj z`
is already bounded to the finite `e.tcs`.
But the instance search of Lean does not recognize this
form, because, as written, `z` goes over all of `Label`.
When we write it as a bounded search over `e.tcs`, the same
proposition becomes directly decidable, with no extra hypothesis. -/

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

/-- The computable `Me`.
A proof shows that it is equal to the original. -/
def MeReach (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  M.filter (fun t => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)

theorem MeReach_eq_Me {τ : Typing} {M : Finset Triple} {e : TripleExpr} :
    MeReach τ M e = Me τ M e := by
  ext t
  unfold MeReach
  simp only [Finset.mem_filter]
  rw [mem_Me]

/-- The computable `Mnotin`.
A proof shows that it is equal to the original. -/
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

We decide the existence of a partition directly, by
well-founded recursion on `M.card` (`existsPartitionFuel`).
Each step removes, from the remaining triples, one nonempty piece that satisfies `Q`.
The bound uses the same `Finset` argument as the proof for
the 2017 `.rep` (`ShexLean.Shex2017Schemas.RepBound`).
The nonempty pieces are pairwise disjoint subsets of `M`.
Thus, there are `M.card` or fewer of them.
No padding is necessary here, because `.star` has no minimum number of repetitions. -/

open ShexLean (mem_subset_foldr_union disjoint_foldr_union_of_forall
  foldr_union_filter_nonempty nonempty_filter_length_le_card)

/-- `M` splits into a list of pieces, and each piece satisfies `Q`.
This is the form of the witness of rule 5 of Table 1. -/
def existsPartition (Q : Finset Triple → Prop) (M : Finset Triple) : Prop :=
  ∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧ ∀ Ni ∈ Ns, Q Ni

/-- The form with only nonempty pieces.
`.star` needs no padding to get this form, because it
has no `min` to satisfy (the 2017 `.rep` has one). -/
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

/-- The one-step recursive characterization.
One of these is true:

* `M` is empty (the empty list is a witness).
* You can remove a nonempty piece that satisfies `Q`.
  The remaining problem (`M \ piece`) is strictly smaller. -/
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

/-- `existsPartition` is decidable, with an explicit `Fuel`
parameter: a structural recursion from `fuel+1` to `fuel`.
We do not use a well-founded recursion measured by `Finset.card`.
That recursion compiles to `WellFounded.fix`, which
does not reduce, so it cannot decide anything.

`M.card ≤ fuel` justifies each case.
At `fuel = 0`, it forces `M = ∅`.
At each recursive step, `fuel` covers `(M \ piece).card`. -/
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

/-- The wrapper with no `Fuel`.
Each `Finset Triple` needs `M.card` fuel or less. -/
def existsPartitionDecidable (Q : Finset Triple → Prop) (hQ : ∀ N', Decidable (Q N'))
    (M : Finset Triple) : Decidable (existsPartition Q M) :=
  existsPartitionFuel Q hQ M.card M (le_refl _)

/-! ### `SatisfiesE` (Table 1) is decidable -/

/-- Rule 2 of Table 1 (`.tc`), written as a search bounded to `M`.
This is the same as `matches_tPattern_iff` of 2017, but simpler, because
the property `p` of `.tc` is one fixed `IRI`, not a full `PropSet`. -/
theorem satisfiesTc_iff_bounded (τ : Typing) (p : IRI) (z : Label) (M : Finset Triple) :
    (∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z) ↔
      ∃ t ∈ M, M = {t} ∧ t.pred = p ∧ τ.has t.obj z := by
  constructor
  · rintro ⟨n, o, hM, hty⟩
    exact ⟨⟨n, p, o⟩, hM ▸ Finset.mem_singleton_self _, hM, rfl, hty⟩
  · rintro ⟨t, -, hM, hp, hty⟩
    refine ⟨t.subj, t.obj, ?_, hty⟩
    rw [hM, ← hp]

/-- `e1;e2` of Table 1 (rule 4), written as a search bounded to `M.powerset`.
This is the same as `matches_eachOf_iff` of 2017. -/
theorem satisfiesSeq_iff_bounded (τ : Typing) (M : Finset Triple) (e1 e2 : TripleExpr) :
    (∃ M1 M2, DisjointUnion M M1 M2 ∧ SatisfiesE τ M1 e1 ∧ SatisfiesE τ M2 e2) ↔
      ∃ M1 ∈ M.powerset, ∃ M2 ∈ M.powerset,
        DisjointUnion M M1 M2 ∧ SatisfiesE τ M1 e1 ∧ SatisfiesE τ M2 e2 := by
  constructor
  · rintro ⟨M1, M2, hdisj, hm1, hm2⟩
    have hM1 : M1 ⊆ M := hdisj.2 ▸ Finset.subset_union_left
    have hM2 : M2 ⊆ M := hdisj.2 ▸ Finset.subset_union_right
    exact ⟨M1, Finset.mem_powerset.mpr hM1, M2, Finset.mem_powerset.mpr hM2, hdisj, hm1, hm2⟩
  · rintro ⟨M1, -, M2, -, hdisj, hm1, hm2⟩
    exact ⟨M1, M2, hdisj, hm1, hm2⟩

instance decidableDisjointUnion (M M1 M2 : Finset Triple) : Decidable (DisjointUnion M M1 M2) := by
  unfold DisjointUnion; infer_instance

/-- `SatisfiesE` is decidable with no condition.
Table 1 never uses `NodeConstraint` or `extends`.
Thus, it needs no extra hypotheses, as Table 3 and Table 2 below do.
The proof is by structural recursion on `e`, and follows the equations of `SatisfiesE`. -/
def satisfiesE_decidable (τ : Typing) : ∀ (M : Finset Triple) (e : TripleExpr),
    Decidable (SatisfiesE τ M e)
  | M, .empty => by show Decidable (M = ∅); infer_instance
  | M, .tc p z => by
      show Decidable (∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z)
      exact decidable_of_iff _ (satisfiesTc_iff_bounded τ p z M).symm
  | M, .choice e1 e2 => by
      haveI := satisfiesE_decidable τ M e1
      haveI := satisfiesE_decidable τ M e2
      exact instDecidableOr
  | M, .seq e1 e2 => by
      haveI : ∀ M1, Decidable (SatisfiesE τ M1 e1) := fun M1 => satisfiesE_decidable τ M1 e1
      haveI : ∀ M2, Decidable (SatisfiesE τ M2 e2) := fun M2 => satisfiesE_decidable τ M2 e2
      exact decidable_of_iff _ (satisfiesSeq_iff_bounded τ M e1 e2).symm
  | M, .star e => by
      show Decidable (existsPartition (SatisfiesE τ · e) M)
      exact existsPartitionDecidable _ (fun N' => satisfiesE_decidable τ N' e) M

instance (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Decidable (SatisfiesE τ M e) :=
  satisfiesE_decidable τ M e

/-- Rule 17 is decidable.
`Me` and `Mnotin` are replaced by their computable versions. -/
instance decidableSatisfiesShape (τ : Typing) (M : Finset Triple) (h : Shape) :
    Decidable (SatisfiesShape τ M h) := by
  unfold SatisfiesShape
  rw [← MeReach_eq_Me, ← MnotinReach_eq_Mnotin]
  infer_instance

/-! The decidability of `DisjointUnionOn`, for a computable `Mx`.
It writes `Set.PairwiseDisjoint` as a double `∀` bounded by a `Finset`. -/

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

/-! ### A faster search for the partition of rule 18

Rule 18 asks for a partition of `M` into `M'` and one part `Mx x` for each `x ∈ Idx`.
A search over a subset of `M` for each part tries `(2^|M|)^(|Idx|+1)` cases.
Because the parts are disjoint and cover `M`, it is sufficient to assign
each triple of `M` to one part: `none` for `M'`, or `some x` for `Mx x`.
This search tries only `(|Idx|+1)^|M|` cases. -/

/-- The triples that the assignment `f` gives to the part `o`. -/
def partOf (M : Finset Triple) (f : ∀ t ∈ M, Option Label) (o : Option Label) :
    Finset Triple :=
  (M.attach.filter fun t => f t.1 t.2 = o).map (Function.Embedding.subtype _)

theorem mem_partOf {M : Finset Triple} {f : ∀ t ∈ M, Option Label} {o : Option Label}
    {t : Triple} : t ∈ partOf M f o ↔ ∃ h : t ∈ M, f t h = o := by
  simp [partOf]

/-- The assignments of the triples of `M` to `M'` or to one part of `Idx`. -/
def assignments (M : Finset Triple) (Idx : Finset Label) : Finset (∀ t ∈ M, Option Label) :=
  M.pi fun _ => insert none (Idx.image some)

/-- The existential of rule 18, over the partitions of `M`, is the
same as an existential over the assignments of the triples of `M`.
The condition `P` must use `Mx` only at the points of `Idx`. -/
theorem exists_disjointUnionOn_iff_assignments (M : Finset Triple) (Idx : Finset Label)
    (P : Finset Triple → (Label → Finset Triple) → Prop)
    (hP : ∀ M' Mx Mx', (∀ x ∈ Idx, Mx x = Mx' x) → (P M' Mx ↔ P M' Mx')) :
    (∃ M' Mx, DisjointUnionOn M M' Idx Mx ∧ P M' Mx) ↔
      ∃ f ∈ assignments M Idx, P (partOf M f none) (fun x => partOf M f (some x)) := by
  classical
  constructor
  · rintro ⟨M', Mx, ⟨hdisj, hpw, hunion⟩, hP'⟩
    have hpart : ∀ t ∈ M, t ∉ M' → ∃ x ∈ Idx, t ∈ Mx x := fun t ht ht' => by
      rw [hunion, Finset.mem_union] at ht
      exact Finset.mem_biUnion.mp (ht.resolve_left ht')
    let f : ∀ t ∈ M, Option Label := fun t ht =>
      if h : t ∈ M' then none else some (hpart t ht h).choose
    have hfx : ∀ t (ht : t ∈ M) x, x ∈ Idx → t ∈ Mx x → f t ht = some x := by
      intro t ht x hx htx
      have htM' : t ∉ M' := fun h =>
        Finset.disjoint_left.mp hdisj h (Finset.mem_biUnion.mpr ⟨x, hx, htx⟩)
      simp only [f, htM', dite_false, Option.some.injEq]
      obtain ⟨hy, hty⟩ := (hpart t ht htM').choose_spec
      by_contra hne
      exact Finset.disjoint_left.mp (hpw hy hx hne) hty htx
    refine ⟨f, ?_, ?_⟩
    · rw [assignments, Finset.mem_pi]
      intro t ht
      by_cases h : t ∈ M'
      · simp [f, h]
      · simp only [f, h, dite_false, Finset.mem_insert, Finset.mem_image, reduceCtorEq,
          Option.some.injEq, false_or]
        exact ⟨_, (hpart t ht h).choose_spec.1, rfl⟩
    · have hM' : partOf M f none = M' := by
        ext t
        rw [mem_partOf]
        constructor
        · rintro ⟨ht, hft⟩
          by_contra h
          simp [f, h] at hft
        · intro h
          exact ⟨hunion ▸ Finset.mem_union_left _ h, by simp [f, h]⟩
      rw [hM']
      refine (hP M' Mx _ fun x hx => ?_).mp hP'
      ext t
      rw [mem_partOf]
      constructor
      · intro htx
        have ht : t ∈ M := hunion ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hx, htx⟩)
        exact ⟨ht, hfx t ht x hx htx⟩
      · rintro ⟨ht, hft⟩
        have htM' : t ∉ M' := fun h => by simp [f, h] at hft
        obtain ⟨hy, hty⟩ := (hpart t ht htM').choose_spec
        rw [hfx t ht _ hy hty, Option.some.injEq] at hft
        exact hft ▸ hty
  · rintro ⟨f, hf, hP'⟩
    rw [assignments, Finset.mem_pi] at hf
    refine ⟨_, _, ⟨?_, ?_, ?_⟩, hP'⟩
    · rw [Finset.disjoint_left]
      intro t h1 h2
      obtain ⟨_, h1⟩ := mem_partOf.mp h1
      obtain ⟨x, -, h2⟩ := Finset.mem_biUnion.mp h2
      obtain ⟨_, h2⟩ := mem_partOf.mp h2
      rw [h1] at h2
      exact absurd h2 (by simp)
    · intro x _ y _ hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro t h1 h2
      obtain ⟨_, h1⟩ := mem_partOf.mp h1
      obtain ⟨_, h2⟩ := mem_partOf.mp h2
      exact hxy (Option.some.inj (h1.symm.trans h2))
    · ext t
      simp only [Finset.mem_union, Finset.mem_biUnion, mem_partOf]
      constructor
      · intro ht
        have := hf t ht
        rcases Finset.mem_insert.mp this with h | h
        · exact Or.inl ⟨ht, h⟩
        · obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp h
          exact Or.inr ⟨x, hx, ht, hfx.symm⟩
      · rintro (⟨ht, -⟩ | ⟨-, -, ht, -⟩) <;> exact ht

end ShexLean.InheritanceCore
