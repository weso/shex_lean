import ShexLean.Shex2017Schemas.Semantics
import Mathlib.Data.Finset.Card

/-!
Bounds `.rep`'s witness-list length, the piece `Decidable.lean` leaves
open. `te-repet`'s existential (`∃ Ns : List (Finset Triple), …`) quantifies
over arbitrary-length lists, unlike `te-tpattern`/`te-each-of`'s
existentials. It doesn't need to: for a fixed `N`, `Matches G t N (.rep E
min none)` (no upper cap) is equivalent to the bounded
`Matches G t N (.rep E min (some (N.card + min)))`.

Argument: any witness list splits into its nonempty pieces (at most
`N.card` of them, being pairwise disjoint subsets of `N`) and its empty
pieces (valid only if `Matches G t ∅ E` holds). Given a witness of length
`≥ min`: if the nonempty-piece count `k` is already `≥ min`, drop every
empty piece (new length `k ≤ N.card`). If `k < min`, the original witness
contained at least `min − k` empty pieces, so `Matches G t ∅ E` holds; pad
to exactly `min`. Either way a witness of length `≤ N.card + min` exists.

Formalized via `repExact E k` (`E` matched exactly `k` times, as a chain of
`.eachOf`s) rather than by manipulating witness lists directly:
`matches_repExact_iff` reduces "some length-`k` witness list" to
`Matches _ (repExact E k)`, turning the `.rep` existential over lists into
an existential over `ℕ`, which `matches_rep_bound` then bounds.
-/

namespace ShexLean

theorem mem_subset_foldr_union {l : List (Finset Triple)} {x : Finset Triple}
    (hx : x ∈ l) : x ⊆ l.foldr (· ∪ ·) ∅ := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Finset.subset_union_left
    · exact (ih hx).trans Finset.subset_union_right

theorem disjoint_foldr_union_of_forall {a : Finset Triple} {l : List (Finset Triple)}
    (h : ∀ x ∈ l, Disjoint a x) : Disjoint a (l.foldr (· ∪ ·) ∅) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.foldr_cons]
    exact Finset.disjoint_union_right.mpr
      ⟨h b List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

/-- `E` matched exactly `k` times in sequence: `repExact E 0 = .empty`,
`repExact E (k+1) = .eachOf E (repExact E k)`. A derived `TExpr`, not a
new constructor, used only to restate `.rep`'s witness-list existential as
an existential over `ℕ` (`matches_repExact_iff` below). -/
def repExact (E : TExpr) : ℕ → TExpr
  | 0 => .empty
  | k + 1 => .eachOf E (repExact E k)

/-- `Matches _ N (repExact E k)` iff `N` splits into a length-`k` list of
pieces, each matching `E`: `repExact E k` is `.rep E k (some k)`'s own
witness-list existential, restricted to length `k`. -/
theorem matches_repExact_iff (G : Graph) (t : Typing) (E : TExpr) :
    ∀ (k : ℕ) (N : Finset Triple), Matches G t N (repExact E k) ↔
      ∃ Ns : List (Finset Triple), Ns.length = k ∧ DisjointUnionList N Ns ∧
        ∀ Ni ∈ Ns, Matches G t Ni E
  | 0, N => by
      show N = ∅ ↔ _
      constructor
      · rintro rfl
        exact ⟨[], rfl, ⟨List.Pairwise.nil, rfl⟩, by simp⟩
      · rintro ⟨Ns, hlen, ⟨-, hunion⟩, -⟩
        rw [List.length_eq_zero_iff] at hlen
        subst hlen
        simpa using hunion
  | k + 1, N => by
      show (∃ N1 N2, DisjointUnion N N1 N2 ∧ Matches G t N1 E ∧
        Matches G t N2 (repExact E k)) ↔ _
      constructor
      · rintro ⟨N1, N2, ⟨hdisj, hunion⟩, hm1, hm2⟩
        obtain ⟨Ns, hlen, ⟨hpw, hunion'⟩, hmatch⟩ := (matches_repExact_iff G t E k N2).mp hm2
        refine ⟨N1 :: Ns, by simp [hlen], ⟨?_, ?_⟩, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨fun x hx => hdisj.mono_right (hunion' ▸ mem_subset_foldr_union hx), hpw⟩
        · rw [List.foldr_cons, ← hunion']; exact hunion
        · intro Ni hNi
          rcases List.mem_cons.mp hNi with rfl | hNi
          · exact hm1
          · exact hmatch Ni hNi
      · rintro ⟨Ns, hlen, ⟨hpw, hunion⟩, hmatch⟩
        match Ns, hlen with
        | N1 :: Ns', hlen =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          rw [List.pairwise_cons] at hpw
          refine ⟨N1, Ns'.foldr (· ∪ ·) ∅,
            ⟨disjoint_foldr_union_of_forall hpw.1, by rw [hunion, List.foldr_cons]⟩,
            hmatch N1 List.mem_cons_self,
            (matches_repExact_iff G t E k _).mpr
              ⟨Ns', hlen, ⟨hpw.2, rfl⟩, fun Ni hNi => hmatch Ni (List.mem_cons_of_mem _ hNi)⟩⟩

/-- `.rep`'s own witness-list existential, restated as an existential over
the witness length alone, via `matches_repExact_iff`. -/
theorem matches_rep_iff_exists_repExact (G : Graph) (t : Typing) (N : Finset Triple)
    (E : TExpr) (min : ℕ) (max : Option ℕ) :
    Matches G t N (.rep E min max) ↔
      ∃ k, min ≤ k ∧ (∀ m', max = some m' → k ≤ m') ∧ Matches G t N (repExact E k) := by
  constructor
  · rintro ⟨Ns, hdisj, hmin, hmax, hmatch⟩
    exact ⟨Ns.length, hmin, hmax,
      (matches_repExact_iff G t E Ns.length N).mpr ⟨Ns, rfl, hdisj, hmatch⟩⟩
  · rintro ⟨k, hmin, hmax, hm⟩
    obtain ⟨Ns, hlen, hdisj, hmatch⟩ := (matches_repExact_iff G t E k N).mp hm
    exact ⟨Ns, hdisj, hlen ▸ hmin, fun m' hm' => hlen ▸ hmax m' hm', hmatch⟩

theorem foldr_union_filter_nonempty (l : List (Finset Triple)) :
    l.foldr (· ∪ ·) ∅ = (l.filter (·.Nonempty)).foldr (· ∪ ·) ∅ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a.Nonempty
    · rw [List.filter_cons_of_pos (by simpa using ha), List.foldr_cons, List.foldr_cons, ih]
    · rw [List.filter_cons_of_neg (by simpa using ha), List.foldr_cons,
        Finset.not_nonempty_iff_eq_empty.mp ha, Finset.empty_union, ih]

theorem nonempty_filter_length_le_card {Ns : List (Finset Triple)} {N : Finset Triple}
    (hpw : Ns.Pairwise Disjoint) (hunion : N = Ns.foldr (· ∪ ·) ∅) :
    (Ns.filter (·.Nonempty)).length ≤ N.card := by
  induction Ns generalizing N with
  | nil => simp
  | cons a Ns ih =>
    rw [List.pairwise_cons] at hpw
    by_cases ha : a.Nonempty
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      have hcard : N.card = a.card + (Ns.foldr (· ∪ ·) ∅).card := by
        rw [hunion, List.foldr_cons, Finset.card_union_of_disjoint
          (disjoint_foldr_union_of_forall hpw.1)]
      have h1 : 1 ≤ a.card := Finset.Nonempty.card_pos ha
      have h2 := ih hpw.2 (N := Ns.foldr (· ∪ ·) ∅) rfl
      simp only [List.length_cons]
      omega
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      have heq : N = Ns.foldr (· ∪ ·) ∅ := by
        rw [hunion, List.foldr_cons, Finset.not_nonempty_iff_eq_empty.mp ha, Finset.empty_union]
      exact heq ▸ ih hpw.2 rfl

/-- Any witness of `repExact E k` for `N` (with `k ≥ min`) can be shrunk to
one of length `≤ N.card + min`. This is what lets `.rep _ min none` (no
upper cap) be decided as if it were `.rep _ min (some (N.card + min))`. -/
theorem matches_rep_bound (G : Graph) (t : Typing) (N : Finset Triple) (E : TExpr)
    (min k : ℕ) (hmin : min ≤ k) (hm : Matches G t N (repExact E k)) :
    ∃ k' ≤ N.card + min, k' ≤ k ∧ min ≤ k' ∧ Matches G t N (repExact E k') := by
  obtain ⟨Ns, hlen, ⟨hpw, hunion⟩, hmatch⟩ := (matches_repExact_iff G t E k N).mp hm
  set Nsnz := Ns.filter (·.Nonempty) with hNsnz_def
  have hpwnz : Nsnz.Pairwise Disjoint := hpw.filter _
  have hunionnz : N = Nsnz.foldr (· ∪ ·) ∅ := by rw [hunion]; exact foldr_union_filter_nonempty Ns
  have hmatchnz : ∀ Ni ∈ Nsnz, Matches G t Ni E := fun Ni hNi =>
    hmatch Ni (List.mem_of_mem_filter hNi)
  have hcard : Nsnz.length ≤ N.card := nonempty_filter_length_le_card hpw hunion
  have hleNs : Nsnz.length ≤ Ns.length := List.length_filter_le _ Ns
  by_cases hge : min ≤ Nsnz.length
  · exact ⟨Nsnz.length, hcard.trans (Nat.le_add_right _ _), hlen ▸ hleNs, hge,
      (matches_repExact_iff G t E Nsnz.length N).mpr ⟨Nsnz, rfl, ⟨hpwnz, hunionnz⟩, hmatchnz⟩⟩
  · push Not at hge
    have hlt : Nsnz.length < Ns.length := by omega
    have hex : ∃ x ∈ Ns, ¬ x.Nonempty := by
      by_contra hcon
      push Not at hcon
      have heq : Nsnz = Ns := by
        rw [hNsnz_def]; exact List.filter_eq_self.mpr (fun a ha => by simp [hcon a ha])
      rw [heq] at hlt; omega
    obtain ⟨x, hxNs, hxne⟩ := hex
    have hxempty : x = (∅ : Finset Triple) := Finset.not_nonempty_iff_eq_empty.mp hxne
    have hMatchesEmpty : Matches G t (∅ : Finset Triple) E := hxempty ▸ hmatch x hxNs
    refine ⟨min, Nat.le_add_left _ _, hmin, le_refl _,
      (matches_repExact_iff G t E min N).mpr
        ⟨Nsnz ++ List.replicate (min - Nsnz.length) (∅ : Finset Triple), ?_, ⟨?_, ?_⟩, ?_⟩⟩
    · rw [List.length_append, List.length_replicate]; omega
    · rw [List.pairwise_append]
      refine ⟨hpwnz, ?_, fun a ha b hb => ?_⟩
      · rw [List.pairwise_iff_forall_sublist]
        intro a b hsub
        have ha := List.eq_of_mem_replicate (hsub.subset (List.mem_cons_self))
        subst ha
        exact Finset.disjoint_empty_left _
      · have hb' : b = ∅ := List.eq_of_mem_replicate hb
        subst hb'
        exact Finset.disjoint_empty_right _
    · have hreplicate : ∀ n : ℕ, (List.replicate n (∅ : Finset Triple)).foldr (· ∪ ·) ∅ = ∅ := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [List.replicate_succ, List.foldr_cons, ih, Finset.union_empty]
      rw [List.foldr_append, hreplicate, ← hunionnz]
    · intro Ni hNi
      rcases List.mem_append.mp hNi with hNi | hNi
      · exact hmatchnz Ni hNi
      · rw [List.eq_of_mem_replicate hNi]; exact hMatchesEmpty

/-- The bounded reformulation `Decidable.lean` needs. -/
theorem matches_rep_iff_bounded (G : Graph) (t : Typing) (N : Finset Triple) (E : TExpr)
    (min : ℕ) (max : Option ℕ) :
    Matches G t N (.rep E min max) ↔
      ∃ k ∈ Finset.range (N.card + min + 1),
        min ≤ k ∧ (∀ m', max = some m' → k ≤ m') ∧ Matches G t N (repExact E k) := by
  rw [matches_rep_iff_exists_repExact]
  constructor
  · rintro ⟨k, hmin, hmax, hm⟩
    obtain ⟨k', hk'le, hk'k, hk'min, hk'm⟩ := matches_rep_bound G t N E min k hmin hm
    exact ⟨k', Finset.mem_range.mpr (by omega), hk'min,
      fun m' hm' => hk'k.trans (hmax m' hm'), hk'm⟩
  · rintro ⟨k, -, hmin, hmax, hm⟩
    exact ⟨k, hmin, hmax, hm⟩

end ShexLean
