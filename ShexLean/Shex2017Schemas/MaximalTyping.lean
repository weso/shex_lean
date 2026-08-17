import ShexLean.Shex2017Schemas.Semantics
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
§3.3 ("Maximal Correct Typing") of Boneva, Labra Gayo, Prud'hommeaux (2017),
up to and including Lemma 1.

> Lemma 1. Let `S` be a schema that does not use the negation operator NOT.
> Then for all graphs `G`, there exists a correct typing `typing_g` of `G`
> by `S` such that for every typing `t'`, if `t'` is a correct
> typing of `G` by `S`, then `t' ⊆ typing_g`.
>
> The typing `typing_g` can be computed as the union of all correct
> typings.

Since (Definition 1) a typing of `G` by `S` is, by convention, a subset of
`Nodes(G) × L`, "the union of all correct typings" is a union of finitely
many finite sets — a subset of the finite set `Nodes(G) × L` itself — so it
is again a `Typing`. We build it as `Finset.sup` over the `Finset` of
correct typings among the (finitely many) subsets of `Nodes(G) × L`, using
classical choice to decide `CorrTyping` (which is not decidable in
general, e.g. across `TExpr.rep`'s existential over `List (Finset
Triple)`) — Lemma 1 is a pure existence statement, so this is harmless.
-/

namespace ShexLean

mutual

/-- `S` contains no occurrence of the `NOT` operator. -/
def ShExpr.NegFree : ShExpr → Prop
  | .valueDescr _ => True
  | .neigDescr E  => TExpr.NegFree E
  | .and S1 S2    => S1.NegFree ∧ S2.NegFree
  | .or S1 S2     => S1.NegFree ∧ S2.NegFree
  | .not _        => False

/-- Same as `ShExpr.NegFree`, for a triple expression. -/
def TExpr.NegFree : TExpr → Prop
  | .tPattern _ _ => True
  | .empty        => True
  | .someOf E1 E2 => E1.NegFree ∧ E2.NegFree
  | .eachOf E1 E2 => E1.NegFree ∧ E2.NegFree
  | .rep E _ _    => E.NegFree

end

/-- Lemma 1's hypothesis: "a schema that does not use the negation operator
NOT", i.e. every label's definition is negation-free. -/
def Schema.NegFree (S : Schema) : Prop := ∀ L ∈ S.labels, (S.shapeDef L).NegFree

/-- Definition 2 (correct typing), named: `t` is a correct typing of
`G` by `S` if every node-type association it contains is backed by a `⊢`
derivation. -/
def Schema.CorrTyping (S : Schema) (G : Graph) (t : Typing) : Prop :=
  ∀ n L, (n, L) ∈ t → Satisfies G t n (S.shapeDef L)

mutual

/-- Monotonicity of `⊢` in `t`, for negation-free shape expressions:
growing `t` can only make more nodes satisfy `S`. This is exactly what
fails for `NOT` (Rule se-shape-not's premise gets *harder* to satisfy as
`t` grows), which is why `S.NegFree` is needed. -/
theorem Satisfies.mono {G : Graph} {t t' : Typing} (hsub : t ⊆ t') :
    ∀ (S : ShExpr), S.NegFree → ∀ (n : RDFNode),
      Satisfies G t n S → Satisfies G t' n S
  | .valueDescr _, _, _, h => h
  | .neigDescr E, hnf, n, h => Matches.mono hsub E hnf (neigh G n) h
  | .and S1 S2, ⟨hnf1, hnf2⟩, n, ⟨h1, h2⟩ =>
      ⟨Satisfies.mono hsub S1 hnf1 n h1, Satisfies.mono hsub S2 hnf2 n h2⟩
  | .or S1 _S2, ⟨hnf1, _hnf2⟩, n, Or.inl h => Or.inl (Satisfies.mono hsub S1 hnf1 n h)
  | .or _S1 S2, ⟨_hnf1, hnf2⟩, n, Or.inr h => Or.inr (Satisfies.mono hsub S2 hnf2 n h)
  | .not _, hnf, _, _ => hnf.elim

/-- Monotonicity of `⊨` in `t`, for negation-free triple expressions. -/
theorem Matches.mono {G : Graph} {t t' : Typing} (hsub : t ⊆ t') :
    ∀ (E : TExpr), E.NegFree → ∀ (N : Finset Triple),
      Matches G t N E → Matches G t' N E
  | .tPattern _ _, _, _, ⟨subj, pred, obj, hN, hP, htyp⟩ =>
      ⟨subj, pred, obj, hN, hP, hsub htyp⟩
  | .empty, _, _, h => h
  | .someOf E1 _E2, ⟨hnf1, _hnf2⟩, N, Or.inl h => Or.inl (Matches.mono hsub E1 hnf1 N h)
  | .someOf _E1 E2, ⟨_hnf1, hnf2⟩, N, Or.inr h => Or.inr (Matches.mono hsub E2 hnf2 N h)
  | .eachOf E1 E2, ⟨hnf1, hnf2⟩, _N, ⟨N1, N2, hdu, h1, h2⟩ =>
      ⟨N1, N2, hdu, Matches.mono hsub E1 hnf1 N1 h1, Matches.mono hsub E2 hnf2 N2 h2⟩
  | .rep E _ _, hnf, _N, ⟨Ns, hdu, hmin, hmax, hall⟩ =>
      ⟨Ns, hdu, hmin, hmax, fun Ni hNi => Matches.mono hsub E hnf Ni (hall Ni hNi)⟩

end

/-- The finite set of all node-type associations, standing for `Nodes(G) ×
L` in Definition 1 — every typing of `G` by `S` is, by convention, a subset
of this set. -/
def Schema.univTyping (S : Schema) (G : Graph) : Typing := G.nodes ×ˢ S.labels

/-- `typing_g` from Lemma 1: the union of all correct typings of `G` by `S`
among the subsets of `Schema.univTyping`. Uses classical choice to decide
`CorrTyping` (see the module docstring); Lemma 1 is a pure existence
statement, so this is harmless. -/
noncomputable def Schema.maximalTyping (S : Schema) (G : Graph) : Typing :=
  haveI := Classical.decPred (S.CorrTyping G)
  ((S.univTyping G).powerset.filter (fun t => S.CorrTyping G t)).sup id

theorem Schema.subset_maximalTyping {S : Schema} {G : Graph} {t : Typing}
    (hsub : t ⊆ S.univTyping G) (hcorrect : S.CorrTyping G t) :
    t ⊆ S.maximalTyping G := by
  have := Classical.decPred (S.CorrTyping G)
  apply Finset.le_sup (f := id)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hcorrect⟩

theorem Schema.maximalTyping_subset (S : Schema) (G : Graph) :
    S.maximalTyping G ⊆ S.univTyping G := by
  have := Classical.decPred (S.CorrTyping G)
  apply Finset.sup_le
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_powerset] at ht
  exact ht.1

/-- `typing_g` is itself a correct typing of `G` by `S`: any `(n, L)` it
contains comes from some correct typing `t` (a member of the union), and
`Satisfies G t n (def L)` transports to `Satisfies G typing_g n (def L)` by
monotonicity, since `S` is negation-free. -/
theorem Schema.maximalTyping_correct (S : Schema) (hnf : S.NegFree) (G : Graph) :
    S.CorrTyping G (S.maximalTyping G) := by
  have := Classical.decPred (S.CorrTyping G)
  intro n L hmem
  obtain ⟨t, htmem, hnLt⟩ := Finset.mem_sup.mp hmem
  simp only [Finset.mem_filter, Finset.mem_powerset] at htmem
  obtain ⟨htsub, htcorrect⟩ := htmem
  have hL : L ∈ S.labels := (Finset.mem_product.mp (htsub hnLt)).2
  exact Satisfies.mono (S.subset_maximalTyping htsub htcorrect) (S.shapeDef L) (hnf L hL) n
    (htcorrect n L hnLt)

/-- Lemma 1. For a negation-free schema `S` and any graph `G`, there is a
correct typing `typing_g` of `G` by `S` (computed as the union of all
correct typings) that contains every correct typing of `G` by `S`. -/
theorem lemma1 (S : Schema) (hnf : S.NegFree) (G : Graph) :
    ∃ typingG : Typing, typingG ⊆ S.univTyping G ∧ S.CorrTyping G typingG ∧
      ∀ t', t' ⊆ S.univTyping G → S.CorrTyping G t' → t' ⊆ typingG :=
  ⟨S.maximalTyping G, S.maximalTyping_subset G, S.maximalTyping_correct hnf G,
    fun _ hsub' hcorrect' => S.subset_maximalTyping hsub' hcorrect'⟩

end ShexLean
