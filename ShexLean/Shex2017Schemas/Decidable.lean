import ShexLean.Shex2017Schemas.RepBound
import ShexLean.Shex2017Schemas.Semantics
import Mathlib.Data.Finset.Powerset

/-!
Makes `Satisfies`/`Matches` (`ShexLean.Shex2017Schemas.Semantics`, Fig. 2 of
Boneva, Labra Gayo, Prud'hommeaux 2017) `Decidable` for every `ShExpr`/
`TExpr`, with no restriction to a fragment, so they can be run via
`decide`/`native_decide` instead of only reasoned about.

**How.** As stated, a few cases quantify over infinite types (`∃ subj pred
obj, …` over all of `RDFNode × IRI × RDFNode`, `∃ N1 N2, …` over all of
`Finset Triple × Finset Triple`, `∃ Ns : List (Finset Triple), …` over
arbitrary-length lists), even though any witness that could satisfy the
constraint is already forced, by an equation in the same clause, to lie
inside the finite graph/typing at hand. This file proves each such case
equivalent to a bounded search:

* `te-tpattern` (`matches_tPattern_iff`): the witness is forced to be `N`'s
  own (at most one) element.
* `te-each-of` (`matches_eachOf_iff`): `N1`/`N2` are forced `⊆ N`, i.e.
  `∈ N.powerset`.
* `te-repet` (`RepBound.lean`'s `matches_rep_iff_bounded`): the one case
  with no static length cap; any witness can be shrunk/padded to length
  `≤ N.card + min`.

Every other case (`.valueDescr`/`.and`/`.or`/`.not`/`.someOf`/`.empty`) is
already structural recursion over decidable pieces. Combining all of this
gives `satisfies_decidable`/`matches_decidable` at the bottom of the file.

`ShexLean/Shex2017Schemas/Render.lean` (and, through it,
`ShexLean/Shex2025Inheritance/Render.lean`) builds every worked example's
displayed `true`/`false` claims directly on these instances via
`renderDecide`/`native_decide`, instead of transcribing hand-proved facts
as strings; see the "Decidability" section of the top-level `README.md`.

Every instance here is built by `Classical`-free structural recursion into
`Finset`/`Fintype` search, so it reduces in the kernel and
`decide`/`native_decide` actually run. This is stronger than "decidable in
the classical sense": under Mathlib's ambient classical axioms, every
`Prop` trivially has some `Decidable` instance via `Classical.propDecidable`,
which does not reduce.

This file doesn't depend on any example file, so `examples/` files (and the
rendering layer built on this file) can import it without a cycle.
-/

namespace ShexLean

/-! ### Bounded reformulations -/

/-- `te-tpattern`, restated as a search bounded to `N` itself. -/
theorem matches_tPattern_iff (G : Graph) (t : Typing) (N : Finset Triple)
    (P : PropSet) (L : Label) :
    Matches G t N (.tPattern P L) ↔
      ∃ tr ∈ N, N = {tr} ∧ tr.pred ∈ P ∧ t.has tr.obj L := by
  constructor
  · rintro ⟨subj, pred, obj, hNeq, hpred, hty⟩
    exact ⟨⟨subj, pred, obj⟩, hNeq ▸ Finset.mem_singleton_self _, hNeq, hpred, hty⟩
  · rintro ⟨tr, -, hNeq, hpred, hty⟩
    exact ⟨tr.subj, tr.pred, tr.obj, hNeq, hpred, hty⟩

/-- `te-each-of`, restated as a search bounded to `N.powerset`. -/
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

/-- `∀ m', max = some m' → k ≤ m'`, the `.rep` upper-bound side condition,
is decidable: `max : Option ℕ` has only two shapes, and each reduces the
statement to something already decidable (`True`, resp. `k ≤ m'`). -/
instance decidableRepUpperBound (max : Option ℕ) (k : ℕ) :
    Decidable (∀ m', max = some m' → k ≤ m') :=
  match max with
  | none => isTrue (by simp)
  | some m' => decidable_of_iff (k ≤ m')
      ⟨fun h _ heq => (Option.some.inj heq) ▸ h, fun h => h m' rfl⟩

/-- `Matches _ N (.eachOf E1 E2)` is decidable given `E1`/`E2`'s own
decidability at every possible sub-neighbourhood, not just `N`: the search
below tries every `N1 ∈ N.powerset` against `E1`, and `N \ N1` against
`E2`, via `matches_eachOf_iff`'s bounded reformulation. Shared by
`matches_decidable`'s `.eachOf` case and `repExactDecidableAux` (whose
`.eachOf E (repExact E k)` unfolding has the same shape). -/
def eachOfDecidableAux (G : Graph) (t : Typing) (N : Finset Triple) (E1 E2 : TExpr)
    (hE1 : ∀ N1 : Finset Triple, Decidable (Matches G t N1 E1))
    (hE2 : ∀ N2 : Finset Triple, Decidable (Matches G t N2 E2)) :
    Decidable (Matches G t N (.eachOf E1 E2)) :=
  have hd2 : ∀ N1 N2 : Finset Triple, Decidable
      (DisjointUnion N N1 N2 ∧ Matches G t N1 E1 ∧ Matches G t N2 E2) :=
    fun N1 N2 => by
      haveI : Decidable (DisjointUnion N N1 N2) := by
        show Decidable (Disjoint N1 N2 ∧ N = N1 ∪ N2); infer_instance
      haveI := hE1 N1
      haveI := hE2 N2
      infer_instance
  have hd1 : ∀ N1 : Finset Triple, Decidable (∃ N2 ∈ N.powerset,
      DisjointUnion N N1 N2 ∧ Matches G t N1 E1 ∧ Matches G t N2 E2) :=
    fun N1 => @Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ (hd2 N1)
  @decidable_of_iff _ _ (matches_eachOf_iff G t N E1 E2).symm
    (@Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ hd1)

/-- `Matches _ N (repExact E k)` is decidable given `E`'s own decidability
at every possible sub-neighbourhood, not just `N` (the `.eachOf` unfolding
at each step of the chain needs it at a new `Finset` each time), by
structural recursion on `k`: `repExact E (k+1) = .eachOf E (repExact E k)`
routes through `eachOfDecidableAux`. -/
def repExactDecidableAux (G : Graph) (t : Typing) (E : TExpr)
    (hE : ∀ N' : Finset Triple, Decidable (Matches G t N' E)) :
    ∀ (k : ℕ) (N : Finset Triple), Decidable (Matches G t N (repExact E k))
  | 0, N => by show Decidable (N = ∅); infer_instance
  | k + 1, N => eachOfDecidableAux G t N E (repExact E k) hE (repExactDecidableAux G t E hE k)

/-- `InV n V` is decidable: case on `n`'s (finitely many)
constructors, each reducing it to plain `Finset` membership. -/
instance decidableInV : ∀ (n : RDFNode) (V : ValueDescr),
    Decidable (InV n V)
  | .iri i, V => inferInstanceAs (Decidable (ValueItem.iri i ∈ V))
  | .lit l, V => inferInstanceAs (Decidable (ValueItem.lit l ∈ V))
  | .bnode _, _ => inferInstanceAs (Decidable False)

/-- `BNodeInV n V` is decidable, likewise by cases on `n`. -/
instance decidableBNodeInV : ∀ (n : RDFNode) (V : ValueDescr),
    Decidable (BNodeInV n V)
  | .bnode _, V => inferInstanceAs (Decidable (ValueItem.anyBlank ∈ V))
  | .iri _, _ => inferInstanceAs (Decidable False)
  | .lit _, _ => inferInstanceAs (Decidable False)

mutual
/-- `Satisfies` is decidable for every `ShExpr`, with no restriction.
Proved by structural recursion mirroring `Satisfies`'s own mutual
definition: every case was already decidable except `.neigDescr`, which
routes through `matches_decidable`. `show`s are needed throughout since
`Satisfies`/`Matches` are plain (non-`@[reducible]`) `def`s, so instance
search won't unfold them to see the underlying `∨`/`∧`/`Finset`
proposition, even though the kernel reduction `decide` relies on later
isn't restricted that way (see `ShexLean.Common.Typing`'s `Typing.has` for
the same gotcha elsewhere in this project). -/
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

/-- `Matches` is decidable for every `TExpr`, with no restriction.
`.tPattern`/`.eachOf` go through the bounded reformulations above; `.rep`
goes through `matches_rep_iff_bounded` (`RepBound.lean`), which bounds
even the `max = none` case. -/
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
      eachOfDecidableAux G t N E1 E2 (matches_decidable G t · E1) (matches_decidable G t · E2)
  | .rep E min max =>
      haveI hE : ∀ N' : Finset Triple, Decidable (Matches G t N' E) :=
        fun N' => matches_decidable G t N' E
      haveI hbound : ∀ k : ℕ, Decidable (Matches G t N (repExact E k)) :=
        fun k => repExactDecidableAux G t E hE k N
      decidable_of_iff _ (matches_rep_iff_bounded G t N E min max).symm
end

end ShexLean
