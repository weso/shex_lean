import Mathlib.Data.Finset.Card
import Mathlib.Dynamics.FixedPoints.Basic

/-!
Paper-independent order theory: iterating a monotone self-map of `Finset α`
reaches a fixed point within finitely many steps. Used by both papers'
`refine`-style validation algorithms (`ShexLean/Shex2017Schemas/Algorithm1.lean`,
`ShexLean/Shex2025Inheritance/Algorithm1.lean`) to show the per-stratum
refinement loop terminates, and by `ShexLean/Shex2025Inheritance/Decidable.lean`
to show ancestor-set closure (`ancStep`, an *increasing* map) also terminates.
-/

namespace ShexLean

/-- Iterating a *decreasing* self-map (`f t ⊆ t` always) of `Finset α`
stabilizes within `x.card` steps: each non-fixed step strictly shrinks the
card, which is bounded below by `0`. -/
theorem Finset.decreasing_iterate_fixed {α : Type*} [DecidableEq α] (f : Finset α → Finset α)
    (hf : ∀ t, f t ⊆ t) (x : Finset α) : f (f^[x.card] x) = f^[x.card] x := by
  induction hcard : x.card using Nat.strong_induction_on generalizing x with
  | _ card ih =>
    by_cases heq : f x = x
    · rw [(Function.IsFixedPt.iterate heq card : f^[card] x = x), heq]
    · have hsub := hf x
      have hlt : (f x).card < x.card := Finset.card_lt_card (hsub.ssubset_of_ne heq)
      have hcard' : (f x).card < card := hcard ▸ hlt
      have hxne : x ≠ ∅ := by rintro rfl; exact heq (by simpa using hf (∅ : Finset α))
      have hcardpos : 0 < card := by
        rw [← hcard]; exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hxne)
      have hih := ih (f x).card hcard' (f x) rfl
      have hpad : ∀ n, (f x).card ≤ n → f^[n] (f x) = f^[(f x).card] (f x) := by
        intro n hn
        obtain ⟨k, rfl⟩ : ∃ k, n = k + (f x).card := ⟨n - (f x).card, by omega⟩
        rw [Function.iterate_add_apply]
        exact Function.IsFixedPt.iterate hih k
      have hstep : f^[card] x = f^[card - 1] (f x) := by
        conv_lhs => rw [show card = (card - 1) + 1 by omega]
        rw [Function.iterate_succ_apply]
      rw [hstep, hpad (card - 1) (by omega)]
      exact hih

/-- Dual of `Finset.decreasing_iterate_fixed`: iterating an *increasing*
self-map (`t ⊆ f t` always) bounded above by a finite `U` (`f t ⊆ U` for
`t ⊆ U`) also stabilizes, within `U.card` steps of any starting `x ⊆ U`
(same proof shape, by strong induction on how much of `U \ x` is left to
fill in, instead of on `x` itself). -/
theorem Finset.increasing_iterate_fixed {α : Type*} [DecidableEq α] (f : Finset α → Finset α)
    (U : Finset α) (hf : ∀ t ⊆ U, t ⊆ f t) (hfU : ∀ t ⊆ U, f t ⊆ U) :
    ∀ (x : Finset α), x ⊆ U → f (f^[(U \ x).card] x) = f^[(U \ x).card] x := by
  intro x
  induction hcard : (U \ x).card using Nat.strong_induction_on generalizing x with
  | _ card ih =>
    intro hxU
    by_cases heq : f x = x
    · rw [(Function.IsFixedPt.iterate heq card : f^[card] x = x)]
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

end ShexLean
