import ShexLean.Shex2017Schemas.Lemma2

/-!
A "lexicographic combination" of two stratifications (`combStrat`), and the
invariance of refinement along it (`MTyping_combStrat`).

The proof of Lemma 2 (`ShexLean/Shex2017Schemas/Lemma2.lean`) does not need
this result. We keep it because it is a useful fact. In general, the
checkpoints of `combStrat` cannot align exactly with a second
stratification of your choice. Two labels that do not depend on each other
can have a different order in two valid stratifications. For this reason,
the proof of Lemma 2 uses a different method.
-/

namespace ShexLean

/-!
The combined ("lexicographically refined") stratification. `str1` is the
primary key, and `str2` breaks ties. Its checkpoints at multiples of
`str2.k + 1` are the checkpoints of `str1`. Thus, we can relate
`MTyping str1` to the `MTyping` of a stratification made from `str1` and
`str2`.
-/

private theorem lex_strict_mono {a1 a2 b1 b2 k2 : ℕ} (ha1 : 1 ≤ a1) (ha2 : 1 ≤ a2)
    (_hb1 : b1 ≤ k2) (hb2 : b2 ≤ k2) (ha : a2 < a1) :
    (a2 - 1) * (k2 + 1) + b2 < (a1 - 1) * (k2 + 1) + b1 := by
  obtain ⟨a1', rfl⟩ := Nat.exists_eq_add_of_le ha1
  obtain ⟨a2', rfl⟩ := Nat.exists_eq_add_of_le ha2
  have he1 : 1 + a1' - 1 = a1' := by omega
  have he2 : 1 + a2' - 1 = a2' := by omega
  rw [he1, he2]
  have hlt : a2' < a1' := by omega
  have hmul : (a2' + 1) * (k2 + 1) ≤ a1' * (k2 + 1) := Nat.mul_le_mul (by omega) (le_refl _)
  calc a2' * (k2 + 1) + b2 ≤ a2' * (k2 + 1) + k2 := by omega
    _ < a2' * (k2 + 1) + (k2 + 1) := by omega
    _ = (a2' + 1) * (k2 + 1) := by ring
    _ ≤ a1' * (k2 + 1) := hmul
    _ ≤ a1' * (k2 + 1) + b1 := by omega

private theorem lex_le {a1 a2 b1 b2 k2 : ℕ} (ha1 : 1 ≤ a1) (ha2 : 1 ≤ a2)
    (hb1 : b1 ≤ k2) (hb2 : b2 ≤ k2) (ha : a2 ≤ a1) (hab : a1 = a2 → b2 ≤ b1) :
    (a2 - 1) * (k2 + 1) + b2 ≤ (a1 - 1) * (k2 + 1) + b1 := by
  rcases eq_or_lt_of_le ha with heq | hlt
  · have hb : b2 ≤ b1 := hab heq.symm
    rw [show a2 = a1 from heq]
    omega
  · exact le_of_lt (lex_strict_mono ha1 ha2 hb1 hb2 hlt)

private theorem lex_upper {a k1 b k2 : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ k1) (hb : b ≤ k2) :
    (a - 1) * (k2 + 1) + b ≤ k1 * (k2 + 1) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha1
  have he : 1 + a' - 1 = a' := by omega
  rw [he]
  have hle : a' + 1 ≤ k1 := by omega
  have hmul : (a' + 1) * (k2 + 1) ≤ k1 * (k2 + 1) := Nat.mul_le_mul hle (le_refl _)
  have : a' * (k2 + 1) + b < (a' + 1) * (k2 + 1) := by
    calc a' * (k2 + 1) + b ≤ a' * (k2 + 1) + k2 := by omega
      _ < a' * (k2 + 1) + (k2 + 1) := by omega
      _ = (a' + 1) * (k2 + 1) := by ring
  omega

/-- `str1` is the primary key, and `str2` breaks ties. -/
noncomputable def combStrat {S : Schema} (hClosed : S.Closed) (str1 str2 : Strat S) :
    Strat S where
  k := str1.k * (str2.k + 1)
  str := fun L => (str1.str L - 1) * (str2.k + 1) + str2.str L
  mem_range := by
    intro L hL
    obtain ⟨h1lo, h1hi⟩ := str1.mem_range L hL
    obtain ⟨h2lo, h2hi⟩ := str2.mem_range L hL
    exact ⟨by omega, lex_upper h1lo h1hi h2hi⟩
  neg_strict := by
    intro L1 hL1 L2 hdep
    have h1 := str1.neg_strict L1 hL1 L2 hdep
    have hL2 : L2 ∈ S.labels := hClosed L1 hL1 (Finset.mem_union_right _ hdep)
    obtain ⟨h1lo, -⟩ := str1.mem_range L1 hL1
    obtain ⟨h1lo', -⟩ := str1.mem_range L2 hL2
    obtain ⟨-, h2hi⟩ := str2.mem_range L1 hL1
    obtain ⟨-, h2hi'⟩ := str2.mem_range L2 hL2
    exact lex_strict_mono h1lo h1lo' h2hi h2hi' h1
  pos_le := by
    intro L1 hL1 L2 hdep
    have h1 := str1.pos_le L1 hL1 L2 hdep
    have hL2 : L2 ∈ S.labels := hClosed L1 hL1 (Finset.mem_union_left _ hdep)
    obtain ⟨h1lo, -⟩ := str1.mem_range L1 hL1
    obtain ⟨h1lo', -⟩ := str1.mem_range L2 hL2
    obtain ⟨-, h2hi⟩ := str2.mem_range L1 hL1
    obtain ⟨-, h2hi'⟩ := str2.mem_range L2 hL2
    refine lex_le h1lo h1lo' h2hi h2hi' h1 (fun heq => ?_)
    have h2 := str2.pos_le L1 hL1 L2 hdep
    exact h2

theorem stratum_combStrat_align {S : Schema} (hClosed : S.Closed)
    (str1 str2 : Strat S) (i : ℕ) :
    S.stratum str1.str i = S.stratum (combStrat hClosed str1 str2).str (i * (str2.k + 1)) := by
  apply Finset.ext
  intro L
  simp only [Schema.stratum, Finset.mem_filter]
  constructor
  · rintro ⟨hL, hle⟩
    refine ⟨hL, ?_⟩
    show (str1.str L - 1) * (str2.k + 1) + str2.str L ≤ i * (str2.k + 1)
    obtain ⟨-, h2hi⟩ := str2.mem_range L hL
    obtain ⟨h1lo, -⟩ := str1.mem_range L hL
    obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le h1lo
    have he : str1.str L - 1 = a' := by omega
    rw [he]
    have : a' + 1 ≤ i := by omega
    have hmul : (a' + 1) * (str2.k + 1) ≤ i * (str2.k + 1) := Nat.mul_le_mul this (le_refl _)
    have : a' * (str2.k + 1) + str2.str L < (a' + 1) * (str2.k + 1) := by
      calc a' * (str2.k + 1) + str2.str L ≤ a' * (str2.k + 1) + str2.k := by omega
        _ < a' * (str2.k + 1) + (str2.k + 1) := by omega
        _ = (a' + 1) * (str2.k + 1) := by ring
    omega
  · rintro ⟨hL, hle⟩
    refine ⟨hL, ?_⟩
    show str1.str L ≤ i
    obtain ⟨h1lo, -⟩ := str1.mem_range L hL
    obtain ⟨h2lo, h2hi⟩ := str2.mem_range L hL
    obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le h1lo
    have he : str1.str L - 1 = a' := by omega
    change (str1.str L - 1) * (str2.k + 1) + str2.str L ≤ i * (str2.k + 1) at hle
    rw [he] at hle
    by_contra hcon
    push Not at hcon
    have : i + 1 ≤ a' + 1 := by omega
    have hmul : i * (str2.k + 1) + (str2.k + 1) ≤ (a' + 1) * (str2.k + 1) :=
      calc i * (str2.k + 1) + (str2.k + 1) = (i + 1) * (str2.k + 1) := by ring
        _ ≤ (a' + 1) * (str2.k + 1) := Nat.mul_le_mul this (le_refl _)
    have hexpand : (a' + 1) * (str2.k + 1) = a' * (str2.k + 1) + (str2.k + 1) := by ring
    omega

/-- Invariance of refinement. `MTyping` with `str1` is equal to `MTyping`
with `combStrat hClosed str1 str2`. (`combStrat` refines `str1` exactly,
at multiples of `str2.k + 1`.)

The proof is by induction on the strata of `str1`. It has an inner
induction (with `maxAgree_fusion` many times) over the `str2.k + 1` finer
steps of `combStrat` in each layer of `str1`. -/
theorem typ_combStrat_align {S : Schema} (hClosed : S.Closed)
    (str1 str2 : Strat S) (G : Graph) :
    ∀ i ≤ str1.k,
      typ S (combStrat hClosed str1 str2).str G (i * (str2.k + 1)) =
        typ S str1.str G i
  | 0, _ => by simp [typ]
  | (i + 1), hi1 => by
      have hi : i ≤ str1.k := by omega
      have houter := typ_combStrat_align hClosed str1 str2 G i hi
      have hT1 := typ_correct S str1 hClosed G i
      have halign : ∀ i' : ℕ, S.stratum str1.str i' =
          S.stratum (combStrat hClosed str1 str2).str (i' * (str2.k + 1)) :=
        stratum_combStrat_align hClosed str1 str2
      set combined := combStrat hClosed str1 str2 with hcombined_def
      set Ls := S.stratum str1.str i with hLs_def
      set T := typ S str1.str G i with hT_def
      have hTsub : T ⊆ (S.restrictLabels Ls).univTyping G := hT1.1
      have hTcorrect : (S.restrictLabels Ls).CorrTyping G T := hT1.2
      have inner : ∀ j, j ≤ str2.k →
          typ S combined.str G (i * (str2.k + 1) + j) =
            maxAgree (S.restrictLabels (S.stratum combined.str (i * (str2.k + 1) + j)))
              G Ls T := by
        intro j
        induction j with
        | zero =>
            intro _
            rw [Nat.add_zero, ← halign i, houter]
            exact (maxAgree_self hTsub hTcorrect).symm
        | succ j ihj =>
            intro hj1
            have hj : j ≤ str2.k := by omega
            have hj' := ihj hj
            set Ls1 := S.stratum combined.str (i * (str2.k + 1) + j) with hLs1_def
            set Ls2 := S.stratum combined.str (i * (str2.k + 1) + (j + 1)) with hLs2_def
            have hLs1Ls2 : Ls1 ⊆ Ls2 := by
              rw [hLs1_def, hLs2_def]; apply Schema.stratum_mono; omega
            have hLsLs1 : Ls ⊆ Ls1 := by
              rw [hLs_def, halign i, hLs1_def]; apply Schema.stratum_mono; omega
            have hLs2sub1 : Ls2 ⊆ S.stratum str1.str (i + 1) := by
              rw [hLs2_def, halign (i + 1)]
              apply Schema.stratum_mono
              have : i * (str2.k + 1) + (j + 1) ≤ i * (str2.k + 1) + (str2.k + 1) := by omega
              have heq : i * (str2.k + 1) + (str2.k + 1) = (i + 1) * (str2.k + 1) := by ring
              omega
            have hneg2 : ∀ L ∈ Ls2, (S.shapeDef L).negDeps ⊆ Ls := by
              intro L hL
              have := Schema.stratum_neg_confined S str1 hClosed (i + 1) L (hLs2sub1 hL)
              simpa using this
            have hpos1 : ∀ L ∈ Ls1, (S.shapeDef L).posDeps ⊆ Ls1 := by
              intro L hL
              exact Finset.subset_union_left.trans
                (Schema.stratum_self_contained S combined hClosed
                  (i * (str2.k + 1) + j) L hL)
            have hfusion := maxAgree_fusion (S := S) (G := G) hLsLs1 hLs1Ls2
              hneg2 hpos1 hTsub hTcorrect
            have hstep : typ S combined.str G (i * (str2.k + 1) + (j + 1)) =
                maxAgree (S.restrictLabels Ls2) G Ls1
                  (typ S combined.str G (i * (str2.k + 1) + j)) := by
              have heq : i * (str2.k + 1) + (j + 1) = (i * (str2.k + 1) + j) + 1 := by omega
              rw [heq]; rfl
            calc typ S combined.str G (i * (str2.k + 1) + (j + 1))
                = maxAgree (S.restrictLabels Ls2) G Ls1
                    (typ S combined.str G (i * (str2.k + 1) + j)) := hstep
              _ = maxAgree (S.restrictLabels Ls2) G Ls1
                    (maxAgree (S.restrictLabels Ls1) G Ls T) := by rw [hj']
              _ = maxAgree (S.restrictLabels Ls2) G Ls T := hfusion
      have hk2 := inner str2.k (le_refl _)
      have hLs1last : S.stratum combined.str (i * (str2.k + 1) + str2.k) ⊆
          S.stratum str1.str (i + 1) := by
        rw [halign (i + 1)]
        apply Schema.stratum_mono
        have heq : i * (str2.k + 1) + (str2.k + 1) = (i + 1) * (str2.k + 1) := by ring
        omega
      have hLsLs1last : Ls ⊆ S.stratum combined.str (i * (str2.k + 1) + str2.k) := by
        rw [hLs_def, halign i]
        apply Schema.stratum_mono
        omega
      have hneg2last : ∀ L ∈ S.stratum str1.str (i + 1), (S.shapeDef L).negDeps ⊆ Ls := by
        intro L hL
        have := Schema.stratum_neg_confined S str1 hClosed (i + 1) L hL
        simpa using this
      have hpos1last : ∀ L ∈ S.stratum combined.str (i * (str2.k + 1) + str2.k),
          (S.shapeDef L).posDeps ⊆ S.stratum combined.str (i * (str2.k + 1) + str2.k) := by
        intro L hL
        exact Finset.subset_union_left.trans
          (Schema.stratum_self_contained S combined hClosed (i * (str2.k + 1) + str2.k) L hL)
      have hfusionlast := maxAgree_fusion (S := S) (G := G) hLsLs1last
        (halign (i + 1) ▸ hLs1last) (halign (i + 1) ▸ hneg2last) hpos1last hTsub hTcorrect
      have hstep : typ S combined.str G ((i + 1) * (str2.k + 1)) =
          maxAgree (S.restrictLabels (S.stratum combined.str ((i + 1) * (str2.k + 1)))) G
            (S.stratum combined.str (i * (str2.k + 1) + str2.k))
            (typ S combined.str G (i * (str2.k + 1) + str2.k)) := by
        have heq : (i + 1) * (str2.k + 1) = (i * (str2.k + 1) + str2.k) + 1 := by ring
        rw [heq]; rfl
      calc typ S combined.str G ((i + 1) * (str2.k + 1))
          = maxAgree (S.restrictLabels (S.stratum combined.str ((i + 1) * (str2.k + 1)))) G
              (S.stratum combined.str (i * (str2.k + 1) + str2.k))
              (typ S combined.str G (i * (str2.k + 1) + str2.k)) := hstep
        _ = maxAgree (S.restrictLabels (S.stratum combined.str ((i + 1) * (str2.k + 1)))) G
              (S.stratum combined.str (i * (str2.k + 1) + str2.k))
              (maxAgree (S.restrictLabels (S.stratum combined.str
                (i * (str2.k + 1) + str2.k))) G Ls T) := by rw [hk2]
        _ = maxAgree (S.restrictLabels (S.stratum combined.str ((i + 1) * (str2.k + 1)))) G
              Ls T := hfusionlast
        _ = maxAgree (S.restrictLabels (S.stratum str1.str (i + 1))) G Ls T := by
              rw [halign (i + 1)]
        _ = typ S str1.str G (i + 1) := rfl

/-- `combStrat hClosed str1 str2` gives `MTyping G S str1`. This is the
instance `i = str1.k` of `typ_combStrat_align`, written with `MTyping`. -/
theorem MTyping_combStrat (S : Schema) (hClosed : S.Closed)
    (str1 str2 : Strat S) (G : Graph) :
    MTyping G S (combStrat hClosed str1 str2) = MTyping G S str1 := by
  show typ S (combStrat hClosed str1 str2).str G
      (str1.k * (str2.k + 1)) = typ S str1.str G str1.k
  exact typ_combStrat_align hClosed str1 str2 G str1.k (le_refl _)

end ShexLean
