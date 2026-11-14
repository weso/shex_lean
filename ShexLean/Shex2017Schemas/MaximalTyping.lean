import ShexLean.Shex2017Schemas.Semantics
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
§3.3 ("Maximal Correct Typing") of Boneva, Labra Gayo,
Prud'hommeaux (2017), up to Lemma 1 (Lemma 1 included).

> Lemma 1. Let `S` be a schema that does not use the negation operator NOT.
> Then for all graphs `G`, there exists a correct typing `typing_g` of `G`
> by `S` such that for every typing `t'`, if `t'` is a correct
> typing of `G` by `S`, then `t' ⊆ typing_g`.
>
> The typing `typing_g` can be computed as the union of all correct
> typings.

By convention (Definition 1), a typing of `G` by `S` is a subset of `Nodes(G) × L`.
Thus, "the union of all correct typings" is a union of a finite number of finite sets.
This union is also a subset of `Nodes(G) × L`.
Thus, it is also a `Typing`.

We make it with `Finset.sup` over the `Finset` of the
correct typings in the subsets of `Nodes(G) × L`.
There is a finite number of these subsets.
We use classical choice to decide `CorrTyping`.
`CorrTyping` is decidable with no classical axioms.
Some cases of `Satisfies` and `Matches` have existentials over infinite types
(for example, `TExpr.rep` has an existential over `List (Finset Triple)`).
But `ShexLean/Shex2017Schemas/Decidable.lean` proves that each of these
cases is equivalent to a bounded search, in `satisfies_decidable`.
`CorrTyping` quantifies only over the elements of a finite typing.

We do not use these instances here, for these reasons:

* Lemma 1 is only a statement of existence.
  Thus, classical choice is satisfactory, and no part of the code runs `Schema.maximalTyping`.
* The search is over all the subsets of `Nodes(G) × L`.
  Thus, a computation is exponential in the size of the graph.
  The validation algorithms of the paper are `Algorithm1` and `Algorithm2`, not this definition.
* Each proof about `Schema.maximalTyping` must use
  the same `Decidable` instance as the definition.
  With `Classical.decPred`, each proof gets this instance with one `have`.
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

/-- The same as `ShExpr.NegFree`, for a triple expression. -/
def TExpr.NegFree : TExpr → Prop
  | .tPattern _ _ => True
  | .empty        => True
  | .someOf E1 E2 => E1.NegFree ∧ E2.NegFree
  | .eachOf E1 E2 => E1.NegFree ∧ E2.NegFree
  | .rep E _ _    => E.NegFree

end

/-- The hypothesis of Lemma 1: "a schema that does not use the negation operator NOT".
Thus, the definition of each label has no negation. -/
def Schema.NegFree (S : Schema) : Prop := ∀ L ∈ S.labels, (S.shapeDef L).NegFree

/-- Definition 2 (correct typing), with a name.
`t` is a correct typing of `G` by `S` if a `⊢`
derivation supports each node-type association in `t`. -/
def Schema.CorrTyping (S : Schema) (G : Graph) (t : Typing) : Prop :=
  ∀ n L, (n, L) ∈ t → Satisfies G t n (S.shapeDef L)

mutual

/-- `⊢` is monotone in `t`, for shape expressions with no negation.
If `t` becomes larger, more nodes can satisfy `S`, but no node stops satisfying `S`.
This is not true for `NOT`.
When `t` becomes larger, the premise of Rule se-shape-not becomes *more difficult* to satisfy.
For this reason, the proof needs `S.NegFree`. -/
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

/-- `⊨` is monotone in `t`, for triple expressions with no negation. -/
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

/-- The finite set of all node-type associations.
This set is `Nodes(G) × L` in Definition 1.
By convention, each typing of `G` by `S` is a subset of this set. -/
def Schema.univTyping (S : Schema) (G : Graph) : Typing := G.nodes ×ˢ S.labels

/-- `typing_g` of Lemma 1: the union of all the correct
typings of `G` by `S` in the subsets of `Schema.univTyping`.
It uses classical choice to decide `CorrTyping` (refer to the module docstring).
This is satisfactory, because Lemma 1 is only a statement of existence. -/
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

/-- `typing_g` is also a correct typing of `G` by `S`.
Each `(n, L)` in it comes from a correct typing `t` in the union.
By monotonicity, `Satisfies G t n (def L)` gives
`Satisfies G typing_g n (def L)`, because `S` has no negation. -/
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

/-- Lemma 1.
Let `S` be a schema with no negation, and let `G` be a graph.
Then there is a correct typing `typing_g` of `G` by
`S` that contains each correct typing of `G` by `S`.
`typing_g` is the union of all the correct typings. -/
theorem lemma1 (S : Schema) (hnf : S.NegFree) (G : Graph) :
    ∃ typingG : Typing, typingG ⊆ S.univTyping G ∧ S.CorrTyping G typingG ∧
      ∀ t', t' ⊆ S.univTyping G → S.CorrTyping G t' → t' ⊆ typingG :=
  ⟨S.maximalTyping G, S.maximalTyping_subset G, S.maximalTyping_correct hnf G,
    fun _ hsub' hcorrect' => S.subset_maximalTyping hsub' hcorrect'⟩

end ShexLean
