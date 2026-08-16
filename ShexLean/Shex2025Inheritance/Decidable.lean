import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2017Schemas.RepBound
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Pi

/-!
Making the 2025 "Shape Expressions with Inheritance" semantics decidable —
the 2025 analogue of `ShexLean.Shex2017Schemas.Decidable`. Building this out
in full (every case of `SatisfiesEFuel`/`SatisfiesMFuel`/`SatisfiesFuel`) is
a substantially bigger undertaking than the 2017 side, for two reasons this
file confronts head-on rather than working around:

1. **`Schema.anc`/`Schema.ancSet` (Table 3 rule 18's ancestor sets,
   `Syntax.lean`) are themselves `noncomputable`** — built via
   `Classical.decPred (Relation.ReflTransGen S.extEdge x)`, since Mathlib
   doesn't ship a generic `Decidable` instance for reflexive-transitive
   closure (reachability over an arbitrary, possibly infinite relation
   genuinely isn't decidable). This file proves the *same* declarative
   proposition the paper states — "there is a path in `H_S`" — actually
   *is* decidable, given the one hypothesis the paper's own Definition 3
   already assumes but this Lean port never named separately: `H_S`'s
   edges, out of any `x ∈ X`, stay within `X` (`Schema.XClosed` below). Not
   an arbitrary extra restriction — Definition 3 states outright that
   `H_S`'s vertex set *is* `X`; `XClosed` is just that fact, made explicit
   enough to compute with. `Schema.anc`/`ancSet` themselves are left
   untouched (still `noncomputable`, still exactly as before, no risk to
   any existing proof) — `ancReach`/`ancSetReach` below are a *separate*,
   genuinely computable definition, proved equal to them.
2. **`NodeConstraint := RDFNode → Prop`** (Table 3 rule 13, `.constraint c`)
   is an arbitrary predicate with no canonical decision procedure — unlike
   2017's concrete `ValueDescr`. Deciding `SatisfiesMFuel`/`SatisfiesFuel`
   is only ever possible *given* a `DecidablePred c` for whichever specific
   `c`s a schema actually uses; threaded through explicitly below, the same
   way `matches_decidable`'s `.rep` case threads through a decidability
   witness for `repExact`'s repeated sub-expression.
-/

/-- Dual of `ShexLean.Shex2017Schemas.Algorithm1`'s `Finset.decreasing_
iterate_fixed`: an *increasing* self-map bounded above by a finite `U`
stabilizes within `U.card` steps too (same proof shape — strong induction
on how much of `U \ t` is left to fill in, rather than on `t` itself). -/
theorem Finset.increasing_iterate_fixed {α : Type*} [DecidableEq α] (f : Finset α → Finset α)
    (U : Finset α) (hf : ∀ t ⊆ U, t ⊆ f t) (hfU : ∀ t ⊆ U, f t ⊆ U) :
    ∀ (x : Finset α), x ⊆ U → f (f^[(U \ x).card] x) = f^[(U \ x).card] x := by
  have hfix : ∀ (y : Finset α), f y = y → ∀ n, f^[n] y = y := by
    intro y hy n
    induction n with
    | zero => rfl
    | succ n ihn => rw [Function.iterate_succ_apply', ihn, hy]
  intro x
  induction hcard : (U \ x).card using Nat.strong_induction_on generalizing x with
  | _ card ih =>
    intro hxU
    by_cases heq : f x = x
    · rw [hfix x heq card]
      exact heq
    · have hsub := hf x hxU
      have hfxU := hfU x hxU
      have hssubset : x ⊂ f x := hsub.ssubset_of_ne (fun h => heq h.symm)
      have hlt : (U \ f x).card < (U \ x).card := by
        have hsubd : U \ f x ⊆ U \ x := Finset.sdiff_subset_sdiff (le_refl U) hssubset.le
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset hsubd]
        obtain ⟨a, ha1, ha2⟩ := Finset.exists_of_ssubset hssubset
        refine ⟨a, ?_, ?_⟩
        · simp [hfxU ha1, ha2]
        · simp [ha1]
      have hcard' : (U \ f x).card < card := hcard ▸ hlt
      have hih := ih (U \ f x).card hcard' (f x) rfl hfxU
      have hpad : ∀ n, (U \ f x).card ≤ n → f^[n] (f x) = f^[(U \ f x).card] (f x) := by
        intro n hn
        obtain ⟨k, rfl⟩ := Nat.le.dest hn
        induction k with
        | zero => rfl
        | succ k ihk =>
            have heqn : (U \ f x).card + (k+1) = ((U \ f x).card + k) + 1 := by omega
            rw [heqn, Function.iterate_succ_apply', ihk (by omega), hih]
      have hcardpos : 0 < card := by omega
      obtain ⟨card', hcard'eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : card ≠ 0)
      subst hcard'eq
      have hle : (U \ f x).card ≤ card' := by omega
      rw [Function.iterate_succ_apply, hpad card' hle]
      exact hih

namespace ShexLean.Inheritance

open ShexLean

/-! ### `Schema.anc`/`ancSet`, made computable -/

/-- The paper's own standing assumption for Definition 3: `H_S`'s edges
never leave `X` — i.e. `H_S` genuinely *is* a graph on vertex set `X`, not
just filtered down to one afterward. -/
def Schema.XClosed (S : Schema) : Prop :=
  ∀ x ∈ S.X, (S.shapeDef x).extendsTargets ⊆ S.X

/-- One step of ancestor-set closure: add every not-yet-included `X`-vertex
reachable by one more `extEdge` hop from the current set. -/
private def ancStep (S : Schema) (t : Finset ShapeLabel) : Finset ShapeLabel :=
  t ∪ S.X.filter (fun y' => ∃ y ∈ t, S.extEdge y y')

private theorem mem_ancStep_iff {S : Schema} {t : Finset ShapeLabel} {x' : ShapeLabel} :
    x' ∈ ancStep S t ↔ x' ∈ t ∨ (x' ∈ S.X ∧ ∃ y ∈ t, S.extEdge y x') := by
  unfold ancStep
  rw [Finset.mem_union, Finset.mem_filter]

private theorem ancStep_subset_X {S : Schema} : ∀ t ⊆ S.X, ancStep S t ⊆ S.X := by
  intro t ht
  unfold ancStep
  exact Finset.union_subset ht (Finset.filter_subset _ _)

private theorem subset_ancStep {S : Schema} : ∀ t ⊆ S.X, t ⊆ ancStep S t :=
  fun _ _ => Finset.subset_union_left

private theorem iterate_subset_X {S : Schema} {x : ShapeLabel} (hx : x ∈ S.X) :
    ∀ n, (ancStep S)^[n] {x} ⊆ S.X := by
  intro n
  induction n with
  | zero => simpa using Finset.singleton_subset_iff.mpr hx
  | succ n ih => rw [Function.iterate_succ_apply']; exact ancStep_subset_X _ ih

private theorem start_subset_iterate {S : Schema} {x : ShapeLabel}
    (hx : x ∈ S.X) : ∀ n, ({x} : Finset ShapeLabel) ⊆ (ancStep S)^[n] {x} := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (subset_ancStep _ (iterate_subset_X hx n))

/-- The computable ancestor set: iterate `ancStep` from `{x}` until it
stabilizes (guaranteed within `(S.X \ {x}).card` steps, `Finset.increasing_
iterate_fixed`). -/
def ancReach (S : Schema) (x : ShapeLabel) : Finset ShapeLabel :=
  (ancStep S)^[(S.X \ {x}).card] {x}

/-- Every `extEdge`-step out of an `S.X`-point reached from `x` stays in
`S.X` (this is what `XClosed`, propagated along a path, actually buys). -/
private theorem reflTransGen_mem_X {S : Schema} (hXC : S.XClosed) {x : ShapeLabel} (hx : x ∈ S.X)
    {x' : ShapeLabel} (h : Relation.ReflTransGen S.extEdge x x') : x' ∈ S.X := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact hXC _ ih hbc

/-- Forward direction: anything the iteration reaches really is
`extEdge`-reachable. -/
private theorem reflTransGen_of_mem_iterate {S : Schema} {x : ShapeLabel} :
    ∀ n (x' : ShapeLabel), x' ∈ (ancStep S)^[n] {x} → Relation.ReflTransGen S.extEdge x x' := by
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

/-- Reverse direction: given `XClosed`, every `extEdge`-reachable point
lands inside `ancReach` (which is exactly the fixed point of `ancStep`
reached from `{x}`, by `Finset.increasing_iterate_fixed`). -/
private theorem mem_ancReach_of_reflTransGen {S : Schema} (hXC : S.XClosed) {x : ShapeLabel}
    (hx : x ∈ S.X) {x' : ShapeLabel} (h : Relation.ReflTransGen S.extEdge x x') :
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

/-- `ancReach` is exactly `Schema.anc`, given the natural closure hypothesis
Definition 3 already assumes. -/
theorem ancReach_eq_anc {S : Schema} (hXC : S.XClosed) {x : ShapeLabel} (hx : x ∈ S.X) :
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
def ancSetReach (S : Schema) (xs : Finset ShapeLabel) : Finset ShapeLabel :=
  xs.biUnion (ancReach S)

theorem ancSetReach_eq_ancSet {S : Schema} (hXC : S.XClosed) {xs : Finset ShapeLabel}
    (hxs : xs ⊆ S.X) : ancSetReach S xs = S.ancSet xs := by
  unfold ancSetReach Schema.ancSet
  apply Finset.biUnion_congr rfl
  intro x hx
  exact ancReach_eq_anc hXC (hxs hx)

/-! ### `Me`/`Mnotin`, made computable

Unlike `anc`/`ancSet`, these never needed `Classical.decPred` at all — the
existential `∃ z, (t.pred,z) ∈ e.tcs ∧ τ.has t.obj z` is already bounded to
the finite `e.tcs`, just not in a shape Lean's instance search recognizes
syntactically (`z` ranges over all of `ShapeLabel` as written). Restating
it as a bounded search over `e.tcs` itself makes the *same* proposition
directly decidable — no extra hypothesis needed, unlike `anc`/`ancSet`. -/

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

/-- The computable `Me`, provably equal to the original. -/
def MeReach (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  M.filter (fun t => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)

theorem MeReach_eq_Me {τ : Typing} {M : Finset Triple} {e : TripleExpr} :
    MeReach τ M e = Me τ M e := by
  ext t
  unfold MeReach
  simp only [Finset.mem_filter]
  rw [mem_Me]

/-- The computable `Mnotin`, provably equal to the original. -/
def MnotinReach (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  (M.filter (fun t => t.pred ∈ e.props)) \ MeReach τ M e

theorem MnotinReach_eq_Mnotin {τ : Typing} {M : Finset Triple} {e : TripleExpr} :
    MnotinReach τ M e = Mnotin τ M e := by
  unfold MnotinReach
  rw [MeReach_eq_Me]
  ext t
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  rw [mem_Mnotin]

/-! ### `.star`'s unbounded repetition, made decidable

Unlike 2017's `.rep`, chaining a repeated sub-expression (`repExact`-style)
doesn't work here: every piece of a `.star` witness is checked at the
*same* `Fuel`, not a further-decremented one, so encoding "repeated `k`
times" as a `k`-deep `.seq` chain would spuriously demand `k` fuel just to
unfold the chain. Instead: decide existence of a partition directly, by
well-founded recursion on `M.card` — peel one `Q`-satisfying nonempty piece
off the remaining triples at a time (`existsPartitionDecidableAux`), bounded
by the same `Finset` machinery 2017's `.rep` proof already established
(`ShexLean.Shex2017Schemas.RepBound`; nonempty pieces are pairwise disjoint
subsets of `M`, so there are at most `M.card` of them — no padding needed
here, since `.star` has no minimum repetition count to pad up to). -/

open ShexLean (mem_subset_foldr_union disjoint_foldr_union_of_forall
  foldr_union_filter_nonempty nonempty_filter_length_le_card)

/-- `M` splits into a list of pieces, each satisfying `Q` — the shape of
Table 1 rule 5's own witness. -/
def existsPartition (Q : Finset Triple → Prop) (M : Finset Triple) : Prop :=
  ∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧ ∀ Ni ∈ Ns, Q Ni

/-- The nonempty-only reformulation `.star` needs no padding to reach (no
`min` to satisfy, unlike 2017's `.rep`). -/
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

/-- The one-step recursive characterization: either `M` is empty (the
empty list works), or some nonempty `Q`-satisfying piece can be peeled off,
leaving a strictly smaller (`M \ piece`) sub-problem. -/
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

/-- **Decidability of `existsPartition`**, via an explicit `Fuel` parameter
(structural recursion, `fuel+1 → fuel` — the *same* idiom
`SatisfiesEFuel`/etc. already use, not a `Finset.card`-measured well-founded
recursion: those compile to `WellFounded.fix`, which — like this project's
own `noncomputable` `Algorithm2.lean`'s `proveAux`/`proveSupport` — doesn't
actually reduce/compile, defeating the entire point of *deciding*
anything). The `M.card ≤ fuel` hypothesis is threaded through so every case
is fully justified with no gap to paper over: at `fuel = 0` it forces
`M = ∅` outright (no recursion needed), and each recursive step's `fuel`
strictly covers `(M \ piece).card` by construction. -/
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

/-- The `Fuel`-free wrapper: any `Finset Triple` needs at most `M.card`
fuel. -/
def existsPartitionDecidable (Q : Finset Triple → Prop) (hQ : ∀ N', Decidable (Q N'))
    (M : Finset Triple) : Decidable (existsPartition Q M) :=
  existsPartitionFuel Q hQ M.card M (le_refl _)

/-! ### `SatisfiesEFuel` (Table 1) is decidable -/

/-- `te-tpattern`'s 2025 analogue (`.tc`, rule 2), restated as a search
bounded to `M` itself — same trick as the 2017 `matches_tPattern_iff`, one
level simpler since `.tc`'s property `p` is a single fixed `IRI`, not a
whole `PropSet`. -/
theorem satisfiesTc_iff_bounded (τ : Typing) (p : IRI) (z : ShapeLabel) (M : Finset Triple) :
    (∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z) ↔
      ∃ t ∈ M, M = {t} ∧ t.pred = p ∧ τ.has t.obj z := by
  constructor
  · rintro ⟨n, o, hM, hty⟩
    exact ⟨⟨n, p, o⟩, hM ▸ Finset.mem_singleton_self _, hM, rfl, hty⟩
  · rintro ⟨t, -, hM, hp, hty⟩
    refine ⟨t.subj, t.obj, ?_, hty⟩
    rw [hM, ← hp]

/-- Table 1's `e1;e2` (rule 4), restated as a search bounded to `M.powerset`
— same as 2017's `matches_eachOf_iff`. -/
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

/-- **`SatisfiesEFuel` is decidable, unconditionally** — Table 1 never
touches `NodeConstraint`/`extends`, so unlike `SatisfiesMFuel`/`SatisfiesFuel`
below, this needs no extra hypotheses at all. Structural recursion on
`(fuel, e)`, mirroring `SatisfiesEFuel`'s own equations exactly. -/
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

/-! ### `SatisfiesMFuel`/`SatisfiesFuel` (Tables 3/2) are decidable, on a
restricted-but-precedented fragment

Two genuinely new obstacles show up here, beyond `anc`/`ancSet`/`Me`/`Mnotin`/
`.star` above:

1. **`subjectOf` (rule 13's `c (subjectOf M)`) is itself `noncomputable`**
   (`Classical.choice`-based, since the paper only pins down its *value* up
   to "some triple's subject", never how to compute one). Unlike `anc`, there
   is no natural computable stand-in that provably agrees with it *in
   general* — only under an extra "every triple in `M` shares one subject"
   invariant the type doesn't track. Rather than silently swap in a
   possibly-different answer, `.constraint` is simply excluded from ever
   being evaluated *at the triple-set level* (`ShapeExpr.MOk` below) — it is
   still evaluated at the *node* level (rule 6, `c n`, no `subjectOf`
   involved at all), which is the only place `.constraint` is actually
   dereferenced when checking `n,τ ⊨ s` for `s = S.shapeDef x` on a
   well-formed schema's `Y`-labels; `.constraint` only reaches the
   triple-set level if some schema deliberately nests a bare `.constraint`
   inside an `extends`'s `restr(x)`, which none of the worked examples do.
2. **`NodeConstraint := RDFNode → Prop`, is arbitrary** (Def 1 leaves it
   fully abstract, unlike 2017's concrete `ValueDescr`), so no single
   `Decidable` instance can cover every `.constraint c` a schema might use —
   each occurrence needs its own `DecidablePred c` supplied by the caller
   (`ShapeExpr.AllConstraintsDecidable`, mirroring `MOk`'s recursion).
-/

/-- The fragment of `ShapeExpr` this file's `SatisfiesMFuel` decidability
covers: no bare `.constraint` (obstacle 1 above), and every nested
`.extends xs _`'s `xs` stays inside `S.X` (so `ancSetReach`/`ancReach`,
which are only proven equal to `S.ancSet`/`S.anc` under that containment,
actually apply). -/
def ShapeExpr.MOk (S : Schema) : ShapeExpr → Prop
  | .constraint _ => False
  | .ofShape _ => True
  | .extends xs _ => xs ⊆ S.X
  | .or s1 s2 => s1.MOk S ∧ s2.MOk S
  | .and s1 s2 => s1.MOk S ∧ s2.MOk S
  | .not s => s.MOk S

/-- The schema-level well-formedness `SatisfiesMFuel`'s decidability at rule
18 additionally needs: every `restr(x)` (for `x ∈ X`) that's actually
present must itself be in the `MOk` fragment, since rule 18 evaluates it at
the triple-set level too. -/
def Schema.RestrOk (S : Schema) : Prop :=
  ∀ x ∈ S.X, ∀ u, (S.shapeDef x).restrOf = some u → u.MOk S

/-- The recursive "every `.constraint` reachable via `or`/`and`/`not` has a
`Decidable` predicate" hypothesis `SatisfiesFuel`'s decidability needs for
its own rule 6 (obstacle 2 above). `.ofShape`/`.extends` contribute `True`:
`Shape` has no nested `ShapeExpr`, so no further `.constraint` can hide
inside one — any `.constraint`s reachable *from* an `.ofShape`/`.extends`
node (via `restr(x)`) are a different schema-level lookup, covered by
`MOk`, not this. -/
def ShapeExpr.AllConstraintsDecidable : ShapeExpr → Prop
  | .constraint c => Nonempty (DecidablePred c)
  | .ofShape _ => True
  | .extends _ _ => True
  | .or s1 s2 => s1.AllConstraintsDecidable ∧ s2.AllConstraintsDecidable
  | .and s1 s2 => s1.AllConstraintsDecidable ∧ s2.AllConstraintsDecidable
  | .not s => s.AllConstraintsDecidable

/-- Extends a `Finset.pi`-style dependent witness `g : ∀ a ∈ Idx, Finset
Triple` to an ordinary `ShapeLabel → Finset Triple`, junk (`∅`) outside
`Idx` — the shape rule 18's own `Mx : ShapeLabel → Finset Triple` needs,
reformulated as a bounded search over `Idx = ancSetReach S xs` alone. -/
def extendMx (Idx : Finset ShapeLabel) (g : ∀ a ∈ Idx, Finset Triple) :
    ShapeLabel → Finset Triple :=
  fun x => if h : x ∈ Idx then g x h else ∅

theorem extendMx_eq {Idx : Finset ShapeLabel} {g : ∀ a ∈ Idx, Finset Triple}
    {x : ShapeLabel} (hx : x ∈ Idx) : extendMx Idx g x = g x hx := by
  unfold extendMx; simp [hx]

/-- Ancestors of a point already inside `ancSetReach S xs` stay inside it —
what makes it sound to only ever query `Mx` at points of `ancSetReach S xs`
in rule 18's `restr(x)` clause (`(S.anc x).biUnion Mx`, `x` ranging over the
very same set). -/
theorem ancReach_subset_ancSetReach {S : Schema} (hXC : S.XClosed) {xs : Finset ShapeLabel}
    (hxs : xs ⊆ S.X) {x : ShapeLabel} (hx : x ∈ ancSetReach S xs) :
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

/-- `DisjointUnionOn` only ever queries `Mx` at points of `Idx`, so agreeing
functions there give the same proposition — what lets rule 18's decidability
freely swap `Mx` for `extendMx Idx g` (which is `Mx` on `Idx`, junk
elsewhere). -/
theorem DisjointUnionOn_congr {M M' : Finset Triple} {Idx : Finset ShapeLabel}
    {Mx Mx' : ShapeLabel → Finset Triple} (hEq : ∀ x ∈ Idx, Mx x = Mx' x) :
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

/-- Every point of `ancSetReach S xs` is itself in `S.X` (it's a union of
`S.anc`-images, and `S.anc _ ⊆ S.X` always, by construction). -/
theorem ancSetReach_subset_X {S : Schema} (hXC : S.XClosed) {xs : Finset ShapeLabel}
    (hxs : xs ⊆ S.X) : ancSetReach S xs ⊆ S.X := by
  intro x hx
  rw [ancSetReach_eq_ancSet hXC hxs] at hx
  unfold Schema.ancSet at hx
  obtain ⟨x0, -, hx0⟩ := Finset.mem_biUnion.mp hx
  simp only [Schema.anc, Finset.mem_filter] at hx0
  exact hx0.1

/-- Rule 18's own existential (`∃ M' Mx, ...`), reformulated as a search
bounded to `M.powerset` (for `M'`) and `Finset.pi (ancSetReach S xs) (fun _
=> M.powerset)` (for `Mx`, restricted to where it's ever queried) —
`ancSetReach S xs`/`ancReach S x` standing in for `S.ancSet xs`/`S.anc x`
via `ancSetReach_eq_ancSet`/`ancReach_eq_anc` (sound since `xs ⊆ S.X`, from
`.extends xs h`'s own `MOk` requirement, and every `x` in scope is reached
from `xs` and so itself `∈ S.X`). -/
theorem satisfiesExtends_iff_bounded {S : Schema} {G : Graph} {τ : Typing}
    (hXC : S.XClosed) {fuel : ℕ} {M : Finset Triple} {xs : Finset ShapeLabel} {h : Shape}
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

/-! `DisjointUnionOn`'s decidability, needed once `Mx` is a concrete
computable function (e.g. `extendMx Idx g`): `Set.PairwiseDisjoint`
restated as a `Finset`-bounded double `∀`. -/

theorem pairwiseDisjoint_iff_bounded (Idx : Finset ShapeLabel) (f : ShapeLabel → Finset Triple) :
    (Idx : Set ShapeLabel).PairwiseDisjoint f ↔
      ∀ a ∈ Idx, ∀ b ∈ Idx, a ≠ b → Disjoint (f a) (f b) := by
  unfold Set.PairwiseDisjoint Set.Pairwise
  constructor
  · intro h a ha b hb hab
    exact h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
  · intro h a ha b hb hab
    exact h a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab

instance decidablePairwiseDisjoint (Idx : Finset ShapeLabel) (f : ShapeLabel → Finset Triple) :
    Decidable ((Idx : Set ShapeLabel).PairwiseDisjoint f) :=
  decidable_of_iff _ (pairwiseDisjoint_iff_bounded Idx f).symm

instance decidableDisjointUnionOn (M M' : Finset Triple) (Idx : Finset ShapeLabel)
    (Mx : ShapeLabel → Finset Triple) : Decidable (DisjointUnionOn M M' Idx Mx) := by
  unfold DisjointUnionOn; infer_instance

/-- **`SatisfiesMFuel` is decidable, on the `MOk` fragment** (see the module
docstring above `ShapeExpr.MOk`): given `S.XClosed` (so `anc`/`ancSet`
compute) and `S.RestrOk` (so every `restr(x)` actually reached also stays
in the `MOk` fragment), and a proof `s.MOk S` for the specific shape
expression at hand. Structural recursion on `(fuel, s)`. -/
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

/-- The fragment of `ShapeExpr` `SatisfiesFuel`'s decidability covers,
analogous to `MOk` one level up: `.constraint c` is fine *here* (rule 6
needs no `subjectOf`), so it just needs `c`'s own decidability; `.ofShape`/
`.extends` immediately hand off to `SatisfiesMFuel`, so need exactly what
`MOk` needs at that single node (trivially true / `xs ⊆ S.X`).

`Type`-valued, not `Prop`-valued like `MOk`: the `.constraint` leaf must
*carry* an actual `DecidablePred c` witness, not just assert one exists
(`Nonempty (DecidablePred c)` would need `Classical.choice` to unerase,
reintroducing exactly the noncomputability this whole file works around). -/
def ShapeExpr.FOk (S : Schema) : ShapeExpr → Type
  | .constraint c => DecidablePred c
  | .ofShape _ => PUnit
  | .extends xs _ => PLift (xs ⊆ S.X)
  | .or s1 s2 => s1.FOk S × s2.FOk S
  | .and s1 s2 => s1.FOk S × s2.FOk S
  | .not s => s.FOk S

/-- **`SatisfiesFuel` is decidable, on the `FOk` fragment** — Table 2's own
`.ofShape`/`.extends` cases (rules 11/12) reduce directly to `SatisfiesMFuel`
on `neigh G n`, so this is really just `satisfiesMFuel_decidable` plus
handling rule 6 (`.constraint`, using the per-occurrence `DecidablePred c`
`FOk` supplies) and threading `or`/`and`/`not` (rules 7–9). -/
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
