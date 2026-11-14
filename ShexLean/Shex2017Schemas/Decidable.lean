import ShexLean.Shex2017Schemas.RepBound
import ShexLean.Shex2017Schemas.Semantics
import Mathlib.Data.Finset.Powerset

/-!
This file makes `Satisfies` and `Matches` `Decidable` for each
`ShExpr` and each `TExpr`, with no restriction to a fragment.
(`Satisfies` and `Matches` are in `ShexLean.Shex2017Schemas.Semantics`,
Fig. 2 of Boneva, Labra Gayo, Prud'hommeaux 2017.)
Thus, you can run them with `decide` or `native_decide`, and not only use them in proofs.

**Method.**
Some cases of the definitions have quantifiers over infinite types:

* `∃ subj pred obj, …` over all of `RDFNode × IRI × RDFNode`.
* `∃ N1 N2, …` over all of `Finset Triple × Finset Triple`.
* `∃ Ns : List (Finset Triple), …` over lists of any length.

But in each case, an equation in the same clause forces
each possible witness to be in the finite graph or typing.
This file proves that each of these cases is equivalent to a bounded search:

* `te-tpattern` (`matches_tPattern_iff`): the witness must
  be the element of `N` (`N` has one element or none).
* `te-each-of` (`matches_eachOf_iff`): `N1` and `N2` must be `⊆ N`.
  Thus, they are `∈ N.powerset`.
* `te-repet` (`matches_rep_iff_bounded` in `RepBound.lean`):
  this is the only case with no static limit on the length.
  You can make each witness shorter or longer, to a length of `N.card + min` or less.

The other cases (`.valueDescr`, `.and`, `.or`, `.not`, `.someOf`,
`.empty`) are already structural recursions over decidable parts.
These results together give `satisfies_decidable` and `matches_decidable` at the end of the file.

`ShexLean/Shex2017Schemas/Render.lean` uses these instances directly, with `renderDecide`.
`ShexLean/Shex2025Inheritance/Render.lean` uses them through it.
With these instances, the `true` and `false` claims of each worked example are computed.
They are not facts that a person proved by hand and then wrote as strings.
Refer to the "Decidability" section of the top-level `README.md`.

Each instance here uses structural recursion into a
`Finset` or `Fintype` search, with no `Classical`.
Thus, the instances reduce in the kernel, and `decide` and `native_decide` can run them.
This is stronger than "decidable in the classical sense".
With the classical axioms of Mathlib, each `Prop` has a `Decidable`
instance from `Classical.propDecidable`, but that instance does not reduce.

This file does not depend on an example file.
Thus, the files in `examples/` (and the rendering layer
that uses this file) can import it with no import cycle.
-/

namespace ShexLean

/-! ### Bounded reformulations -/

/-- `te-tpattern`, written as a search bounded to `N`. -/
theorem matches_tPattern_iff (G : Graph) (t : Typing) (N : Finset Triple)
    (P : PropSet) (L : Label) :
    Matches G t N (.tPattern P L) ↔
      ∃ tr ∈ N, N = {tr} ∧ tr.pred ∈ P ∧ t.has tr.obj L := by
  constructor
  · rintro ⟨subj, pred, obj, hNeq, hpred, hty⟩
    exact ⟨⟨subj, pred, obj⟩, hNeq ▸ Finset.mem_singleton_self _, hNeq, hpred, hty⟩
  · rintro ⟨tr, -, hNeq, hpred, hty⟩
    exact ⟨tr.subj, tr.pred, tr.obj, hNeq, hpred, hty⟩

/-- `te-each-of`, written as a search bounded to `N.powerset`. -/
theorem matches_eachOf_iff (G : Graph) (t : Typing) (N : Finset Triple)
    (E1 E2 : TExpr) :
    Matches G t N (.eachOf E1 E2) ↔
      ∃ N1 ∈ N.powerset, ∃ N2 ∈ N.powerset,
        DisjointUnion N N1 N2 ∧ Matches G t N1 E1 ∧ Matches G t N2 E2 := by
  constructor
  · rintro ⟨N1, N2, hdisj, hm1, hm2⟩
    have hN1 : N1 ⊆ N := hdisj.2 ▸ Finset.subset_union_left
    have hN2 : N2 ⊆ N := hdisj.2 ▸ Finset.subset_union_right
    exact ⟨N1, Finset.mem_powerset.mpr hN1, N2, Finset.mem_powerset.mpr hN2, hdisj, hm1, hm2⟩
  · rintro ⟨N1, -, N2, -, hdisj, hm1, hm2⟩
    exact ⟨N1, N2, hdisj, hm1, hm2⟩

/-- `∀ m', max = some m' → k ≤ m'` is decidable.
This is the side condition for the upper bound of `.rep`.
`max : Option ℕ` has only two forms.
Each form changes the statement into a statement that is already decidable (`True`, or `k ≤ m'`). -/
instance decidableRepUpperBound (max : Option ℕ) (k : ℕ) :
    Decidable (∀ m', max = some m' → k ≤ m') :=
  match max with
  | none => isTrue (by simp)
  | some m' => decidable_of_iff (k ≤ m')
      ⟨fun h _ heq => (Option.some.inj heq) ▸ h, fun h => h m' rfl⟩

/-- `Matches _ N (repExact E k)` is decidable if `E` is decidable.
`E` must be decidable at each possible sub-neighbourhood, not only at `N`.
The reason is that each step of the chain unfolds `.eachOf` at a new `Finset`.
The proof is by structural recursion on `k` only.
`repExact E (k+1) = .eachOf E (repExact E k)` uses the same
bounded search over `N.powerset` as the `.eachOf` case below.

This code is written inline.
It does not use a shared `.eachOf` helper.
Thus, the compiler can specialize each recursive call to its concrete `E` or `repExact E k`.
An opaque, non-recursive helper that takes the sub-decidability
witnesses as plain function arguments stops this specialization.
With such a helper, this exponential-search instance was too slow to
use on worked examples with many nested `.rep`, `.eachOf` and `AND`.
Use only direct self-recursive calls here. -/
def repExactDecidableAux (G : Graph) (t : Typing) (E : TExpr)
    (hE : ∀ N' : Finset Triple, Decidable (Matches G t N' E)) :
    ∀ (k : ℕ) (N : Finset Triple), Decidable (Matches G t N (repExact E k))
  | 0, N => by show Decidable (N = ∅); infer_instance
  | k + 1, N =>
      have hd2 : ∀ N1 N2 : Finset Triple, Decidable
          (DisjointUnion N N1 N2 ∧ Matches G t N1 E ∧ Matches G t N2 (repExact E k)) :=
        fun N1 N2 => by
          haveI : Decidable (DisjointUnion N N1 N2) := by
            show Decidable (Disjoint N1 N2 ∧ N = N1 ∪ N2); infer_instance
          haveI := hE N1
          haveI := repExactDecidableAux G t E hE k N2
          infer_instance
      have hd1 : ∀ N1 : Finset Triple, Decidable (∃ N2 ∈ N.powerset,
          DisjointUnion N N1 N2 ∧ Matches G t N1 E ∧ Matches G t N2 (repExact E k)) :=
        fun N1 => @Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ (hd2 N1)
      @decidable_of_iff _ _ (matches_eachOf_iff G t N E (repExact E k)).symm
        (@Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ hd1)

/-- `InV n V` is decidable.
Do a case analysis on the constructors of `n` (there is a finite number of them).
Each case is a plain `Finset` membership. -/
instance decidableInV : ∀ (n : RDFNode) (V : ValueDescr),
    Decidable (InV n V)
  | .iri i, V => inferInstanceAs (Decidable (ValueItem.iri i ∈ V))
  | .lit l, V => inferInstanceAs (Decidable (ValueItem.lit l ∈ V))
  | .bnode _, _ => inferInstanceAs (Decidable False)

/-- `BNodeInV n V` is decidable.
The proof is also a case analysis on `n`. -/
instance decidableBNodeInV : ∀ (n : RDFNode) (V : ValueDescr),
    Decidable (BNodeInV n V)
  | .bnode _, V => inferInstanceAs (Decidable (ValueItem.anyBlank ∈ V))
  | .iri _, _ => inferInstanceAs (Decidable False)
  | .lit _, _ => inferInstanceAs (Decidable False)

mutual
/-- `Satisfies` is decidable for each `ShExpr`, with no restriction.

The proof is by structural recursion.
It follows the mutual definition of `Satisfies`.
Each case was already decidable, except `.neigDescr`, which uses `matches_decidable`.

The proof needs `show` in many locations.
`Satisfies` and `Matches` are plain `def`s (not `@[reducible]`).
Thus, instance search does not unfold them to find
the `∨`, `∧` or `Finset` proposition below them.
The kernel reduction that `decide` uses later does not have this restriction.
(Refer to `Typing.has` in `ShexLean.Common.Typing` for the
same problem in a different location of this project.) -/
def satisfies_decidable (G : Graph) (t : Typing) (n : RDFNode) :
    ∀ S : ShExpr, Decidable (Satisfies G t n S)
  | .valueDescr V => by
      show Decidable (InV n V ∨ BNodeInV n V)
      infer_instance
  | .neigDescr E => by
      show Decidable (Matches G t (neigh G n) E)
      exact matches_decidable G t (neigh G n) E
  | .and S1 S2 => by
      show Decidable (Satisfies G t n S1 ∧ Satisfies G t n S2)
      haveI := satisfies_decidable G t n S1
      haveI := satisfies_decidable G t n S2
      infer_instance
  | .or S1 S2 => by
      show Decidable (Satisfies G t n S1 ∨ Satisfies G t n S2)
      haveI := satisfies_decidable G t n S1
      haveI := satisfies_decidable G t n S2
      infer_instance
  | .not S => by
      show Decidable (¬ Satisfies G t n S)
      haveI := satisfies_decidable G t n S
      infer_instance

/-- `Matches` is decidable for each `TExpr`, with no restriction.
`.tPattern` and `.eachOf` use the bounded forms above.
`.rep` uses `matches_rep_iff_bounded` (`RepBound.lean`),
which gives a bound also for the case `max = none`. -/
def matches_decidable (G : Graph) (t : Typing) (N : Finset Triple) :
    ∀ E : TExpr, Decidable (Matches G t N E)
  | .tPattern P L =>
      decidable_of_iff _ (matches_tPattern_iff G t N P L).symm
  | .empty => by show Decidable (N = ∅); infer_instance
  | .someOf E1 E2 => by
      show Decidable (Matches G t N E1 ∨ Matches G t N E2)
      haveI := matches_decidable G t N E1
      haveI := matches_decidable G t N E2
      infer_instance
  | .eachOf E1 E2 =>
      haveI hd2 : ∀ N1 N2 : Finset Triple, Decidable
          (DisjointUnion N N1 N2 ∧ Matches G t N1 E1 ∧ Matches G t N2 E2) :=
        fun N1 N2 => by
          haveI : Decidable (DisjointUnion N N1 N2) := by
            show Decidable (Disjoint N1 N2 ∧ N = N1 ∪ N2); infer_instance
          haveI := matches_decidable G t N1 E1
          haveI := matches_decidable G t N2 E2
          infer_instance
      have hd1 : ∀ N1 : Finset Triple, Decidable (∃ N2 ∈ N.powerset,
          DisjointUnion N N1 N2 ∧ Matches G t N1 E1 ∧ Matches G t N2 E2) :=
        fun N1 => @Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ (hd2 N1)
      @decidable_of_iff _ _ (matches_eachOf_iff G t N E1 E2).symm
        (@Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ hd1)
  | .rep E min max =>
      haveI hE : ∀ N' : Finset Triple, Decidable (Matches G t N' E) :=
        fun N' => matches_decidable G t N' E
      haveI hbound : ∀ k : ℕ, Decidable (Matches G t N (repExact E k)) :=
        fun k => repExactDecidableAux G t E hE k N
      decidable_of_iff _ (matches_rep_iff_bounded G t N E min max).symm
end

end ShexLean
