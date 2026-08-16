import ShexLean.InductiveRDF.Graph
import ShexLean.InductiveRDF.RepBound
import ShexLean.Shex2017Schemas.Semantics
import Mathlib.Data.Finset.Powerset

/-!
Does representing `G` as an inductive triple graph (`Graph.lean`) make
`Satisfies`/`Matches` (`ShexLean.Shex2017Schemas.Semantics`, Fig. 2 of
Boneva, Labra Gayo, Prud'hommeaux 2017) *decidable* — i.e. lets the `prove`
algorithm (Algorithm 2) actually be *run*, rather than only reasoned about?

**No — and switching graph representations was never going to change the
answer.** `Satisfies`/`Matches` are already defined over this project's
existing `Graph := Finset Triple` (`ShexLean.Common.RDF`), which is already
finite and has decidable equality throughout (`RDFNode`, `IRI := String`,
`Triple` all `deriving DecidableEq`) — exactly as `Finset (TContext …)`-style
data built from an inductive triple graph would be. Neither representation
is "more finite" than the other; converting between them (`ofGraph`/
`toGraph`, proved inverse in `RoundTrip.lean`) doesn't touch what actually
blocks `Decidable`.

The real blocker, visible directly in `Semantics.lean`'s equations, is that
several cases are stated as **quantifiers ranging over the ambient infinite
types** `RDFNode`/`IRI`/arbitrary `Finset Triple`/arbitrary-length
`List (Finset Triple)`, even though every witness that can actually satisfy
the constraint is forced — by an equation in the same clause — to already
lie inside the finite graph/typing at hand:

* `te-tpattern`: `∃ subj pred obj, N = {⟨subj,pred,obj⟩} ∧ …` quantifies
  over all of `RDFNode × IRI × RDFNode`, but the `N = {…}` conjunct forces
  the witness to be `N`'s own (at most one) element.
* `te-each-of`: `∃ N1 N2, DisjointUnion N N1 N2 ∧ …` quantifies over all of
  `Finset Triple × Finset Triple`, but `DisjointUnion`'s `N = N1 ∪ N2`
  conjunct forces `N1, N2 ⊆ N`, i.e. `N1, N2 ∈ N.powerset`.
* `te-repet`: `∃ Ns : List (Finset Triple), …` quantifies over
  arbitrary-length lists — the one that looked genuinely unbounded, since
  the union constraint alone doesn't bound the list *length* when `max =
  none` and `E` itself accepts `∅` (nothing stops padding with arbitrarily
  many empty pieces). `RepBound.lean` closes this gap too:
  `matches_rep_iff_bounded` shows `.rep E min none`'s witness can always be
  shrunk to length `≤ N.card + min` (drop excess empty pieces, or pad up to
  `min` with `∅`s when `Matches G typing ∅ E` holds), so *every* case is
  bounded after all.

This file proves *reformulation* lemmas (`matches_tPattern_iff`,
`matches_eachOf_iff`, and `RepBound.lean`'s `matches_rep_iff_bounded`)
restating all three existentials as bounded `Finset`/`Finset.powerset`/`ℕ`
searches — logically equivalent to the originals, but with a body Lean can
decide — and uses them (plus the fact that `.valueDescr`/`.and`/`.or`/
`.not`/`.someOf`/`.empty` were never the problem: they're already
structural recursion over decidable pieces) to build a genuine, `decide`-
able `Decidable` instance for `Satisfies`/`Matches`, for **every**
`ShapeExpr`/`TripleExpr` — no restricted fragment needed. This file itself
doesn't depend on any example file (kept import-free of `examples/` so
those files — and the rendering layer built on top of this file — can
import *it* without a cycle); `DecidablePayoff.lean` re-derives a few
example facts by `native_decide` instead of by hand, as a demonstration.

**What's `decide`-able and what isn't, precisely:** every proposition
proved `Decidable` this way is proved so via `Classical`-free, structural
recursion into genuine `Finset`/`Fintype` search — reducible by the kernel,
so `decide` actually runs, not just "exists as a classical fact" (under
Mathlib's ambient classical axioms, *every* `Prop` trivially has *some*
`Decidable` instance via `Classical.propDecidable`; that fact would be true
regardless of any of this investigation and is not what's being claimed
here).

**Retrospective, once the 2025 formalism's own decidability layer
(`ShexLean.Shex2025Inheritance.Decidable`) existed too: this file's "the
representation was never the problem" conclusion held up a second time,
independently.** The 2025 work needed the *exact same* bounded-
reformulation technique — `Schema.anc`/`ancSet` (an unbounded `Finset.filter`
over a classically-decided reachability `Prop`), `Me`/`Mnotin`, and `.star`'s
unbounded repetition (this file's `.rep`, one level harder: no static upper
bound at all, only a `Fuel`-threaded search) all got the same "restate the
existential as a search over a known finite set" treatment as
`matches_eachOf_iff`/`matches_tPattern_iff`/`RepBound.lean` here — on top of
the *same* `Finset Triple`-based `Graph`, no alternative representation
involved. The one place 2025 diverges from this file's "no restricted
fragment needed" result: `subjectOf` (Table 3 rule 13) is `Classical.choice`-
based with no computable equivalent *in general* (unlike every quantifier
here, its witness isn't forced finite by a co-occurring equation — it's
genuinely unconstrained without an extra invariant the type doesn't track),
so `Shex2025Inheritance.Decidable` had to name an explicit restricted
fragment (`ShapeExpr.MOk`/`FOk`) rather than getting the fully general
result this file gets for `Satisfies`/`Matches`. That's a difference in the
*semantics themselves* (2025's Table 3 has no 2017 analogue), not evidence
that inductive triple graphs would have helped 2017 after all.
-/

namespace ShexLean.InductiveRDF

open ShexLean

/-! ### Bounded reformulations -/

/-- `te-tpattern`, restated as a search bounded to `N` itself. -/
theorem matches_tPattern_iff (G : Graph) (typing : Typing) (N : Finset Triple)
    (P : PropSet) (L : ShapeLabel) :
    Matches G typing N (.tPattern P L) ↔
      ∃ t ∈ N, N = {t} ∧ t.pred ∈ P ∧ typing.has t.obj L := by
  constructor
  · rintro ⟨subj, pred, obj, hNeq, hpred, hty⟩
    exact ⟨⟨subj, pred, obj⟩, hNeq ▸ Finset.mem_singleton_self _, hNeq, hpred, hty⟩
  · rintro ⟨t, -, hNeq, hpred, hty⟩
    exact ⟨t.subj, t.pred, t.obj, hNeq, hpred, hty⟩

/-- `te-each-of`, restated as a search bounded to `N.powerset`. -/
theorem matches_eachOf_iff (G : Graph) (typing : Typing) (N : Finset Triple)
    (E1 E2 : TripleExpr) :
    Matches G typing N (.eachOf E1 E2) ↔
      ∃ N1 ∈ N.powerset, ∃ N2 ∈ N.powerset,
        DisjointUnion N N1 N2 ∧ Matches G typing N1 E1 ∧ Matches G typing N2 E2 := by
  constructor
  · rintro ⟨N1, N2, hdisj, hm1, hm2⟩
    have hN1 : N1 ⊆ N := hdisj.2 ▸ Finset.subset_union_left
    have hN2 : N2 ⊆ N := hdisj.2 ▸ Finset.subset_union_right
    exact ⟨N1, Finset.mem_powerset.mpr hN1, N2, Finset.mem_powerset.mpr hN2, hdisj, hm1, hm2⟩
  · rintro ⟨N1, -, N2, -, hdisj, hm1, hm2⟩
    exact ⟨N1, N2, hdisj, hm1, hm2⟩

/-- `∀ m', max = some m' → k ≤ m'` — the `.rep` upper-bound side condition
— is decidable: `max : Option ℕ` has only two shapes, and each reduces the
statement to something already decidable (`True`, resp. `k ≤ m'`). -/
instance decidableRepUpperBound (max : Option ℕ) (k : ℕ) :
    Decidable (∀ m', max = some m' → k ≤ m') :=
  match max with
  | none => isTrue (by simp)
  | some m' => decidable_of_iff (k ≤ m')
      ⟨fun h _ heq => (Option.some.inj heq) ▸ h, fun h => h m' rfl⟩

/-- `Matches _ N (repExact E k)` is decidable given `E`'s own decidability
(at every possible sub-neighbourhood, not just `N` — the `.eachOf`
unfolding at each step of the chain needs it at a *new* Finset each time),
by structural recursion on `k` alone: `repExact E (k+1) = .eachOf E
(repExact E k)` routes through the exact same bounded-`N.powerset` search
as `.eachOf`'s own case below. -/
def repExactDecidableAux (G : Graph) (typing : Typing) (E : TripleExpr)
    (hE : ∀ N' : Finset Triple, Decidable (Matches G typing N' E)) :
    ∀ (k : ℕ) (N : Finset Triple), Decidable (Matches G typing N (repExact E k))
  | 0, N => by show Decidable (N = ∅); infer_instance
  | k + 1, N =>
      have hd2 : ∀ N1 N2 : Finset Triple, Decidable
          (DisjointUnion N N1 N2 ∧ Matches G typing N1 E ∧ Matches G typing N2 (repExact E k)) :=
        fun N1 N2 => by
          haveI : Decidable (DisjointUnion N N1 N2) := by
            show Decidable (Disjoint N1 N2 ∧ N = N1 ∪ N2); infer_instance
          haveI := hE N1
          haveI := repExactDecidableAux G typing E hE k N2
          infer_instance
      have hd1 : ∀ N1 : Finset Triple, Decidable (∃ N2 ∈ N.powerset,
          DisjointUnion N N1 N2 ∧ Matches G typing N1 E ∧ Matches G typing N2 (repExact E k)) :=
        fun N1 => @Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ (hd2 N1)
      @decidable_of_iff _ _ (matches_eachOf_iff G typing N E (repExact E k)).symm
        (@Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ hd1)

/-- `NodeInValueDescr n V` is decidable: case on `n`'s (finitely many)
constructors, each reducing it to plain `Finset` membership. -/
instance decidableNodeInValueDescr : ∀ (n : RDFNode) (V : ValueDescr),
    Decidable (NodeInValueDescr n V)
  | .iri i, V => inferInstanceAs (Decidable (ValueItem.iri i ∈ V))
  | .lit l, V => inferInstanceAs (Decidable (ValueItem.lit l ∈ V))
  | .bnode _, _ => inferInstanceAs (Decidable False)

/-- `NodeIsAnyBlankInValueDescr n V` is decidable, likewise by cases on `n`. -/
instance decidableNodeIsAnyBlankInValueDescr : ∀ (n : RDFNode) (V : ValueDescr),
    Decidable (NodeIsAnyBlankInValueDescr n V)
  | .bnode _, V => inferInstanceAs (Decidable (ValueItem.anyBlank ∈ V))
  | .iri _, _ => inferInstanceAs (Decidable False)
  | .lit _, _ => inferInstanceAs (Decidable False)

mutual
/-- **`Satisfies` is decidable — for every `ShapeExpr`, no restriction.**
Proved by structural recursion mirroring `Satisfies`'s own mutual
definition — every case was already decidable except `.neigDescr`, which
routes through `matches_decidable`. `show`s are needed throughout since
`Satisfies`/`Matches` are plain (non-`@[reducible]`) `def`s: instance
search won't unfold them on its own to see the underlying `∨`/`∧`/`Finset`
proposition, even though the kernel reduction `decide` itself relies on
later isn't restricted that way (see `ShexLean.Common.Typing`'s
`Typing.has` for the same gotcha elsewhere in this project). -/
def satisfies_decidable (G : Graph) (typing : Typing) (n : RDFNode) :
    ∀ S : ShapeExpr, Decidable (Satisfies G typing n S)
  | .valueDescr V => by
      show Decidable (NodeInValueDescr n V ∨ NodeIsAnyBlankInValueDescr n V)
      infer_instance
  | .neigDescr E => by
      show Decidable (Matches G typing (neigh G n) E)
      exact matches_decidable G typing (neigh G n) E
  | .and S1 S2 => by
      show Decidable (Satisfies G typing n S1 ∧ Satisfies G typing n S2)
      haveI := satisfies_decidable G typing n S1
      haveI := satisfies_decidable G typing n S2
      infer_instance
  | .or S1 S2 => by
      show Decidable (Satisfies G typing n S1 ∨ Satisfies G typing n S2)
      haveI := satisfies_decidable G typing n S1
      haveI := satisfies_decidable G typing n S2
      infer_instance
  | .not S => by
      show Decidable (¬ Satisfies G typing n S)
      haveI := satisfies_decidable G typing n S
      infer_instance

/-- **`Matches` is decidable — for every `TripleExpr`, no restriction.**
`.tPattern`/`.eachOf` go through the bounded reformulations above; `.rep`
goes through `matches_rep_iff_bounded` (`RepBound.lean`), which bounds
even the `max = none` case. -/
def matches_decidable (G : Graph) (typing : Typing) (N : Finset Triple) :
    ∀ E : TripleExpr, Decidable (Matches G typing N E)
  | .tPattern P L =>
      decidable_of_iff _ (matches_tPattern_iff G typing N P L).symm
  | .empty => by show Decidable (N = ∅); infer_instance
  | .someOf E1 E2 => by
      show Decidable (Matches G typing N E1 ∨ Matches G typing N E2)
      haveI := matches_decidable G typing N E1
      haveI := matches_decidable G typing N E2
      infer_instance
  | .eachOf E1 E2 =>
      haveI hd2 : ∀ N1 N2 : Finset Triple, Decidable
          (DisjointUnion N N1 N2 ∧ Matches G typing N1 E1 ∧ Matches G typing N2 E2) :=
        fun N1 N2 => by
          haveI : Decidable (DisjointUnion N N1 N2) := by
            show Decidable (Disjoint N1 N2 ∧ N = N1 ∪ N2); infer_instance
          haveI := matches_decidable G typing N1 E1
          haveI := matches_decidable G typing N2 E2
          infer_instance
      have hd1 : ∀ N1 : Finset Triple, Decidable (∃ N2 ∈ N.powerset,
          DisjointUnion N N1 N2 ∧ Matches G typing N1 E1 ∧ Matches G typing N2 E2) :=
        fun N1 => @Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ (hd2 N1)
      @decidable_of_iff _ _ (matches_eachOf_iff G typing N E1 E2).symm
        (@Finset.decidableExistsAndFinset (Finset Triple) N.powerset _ hd1)
  | .rep E min max =>
      haveI hE : ∀ N' : Finset Triple, Decidable (Matches G typing N' E) :=
        fun N' => matches_decidable G typing N' E
      haveI hbound : ∀ k : ℕ, Decidable (Matches G typing N (repExact E k)) :=
        fun k => repExactDecidableAux G typing E hE k N
      decidable_of_iff _ (matches_rep_iff_bounded G typing N E min max).symm
end

end ShexLean.InductiveRDF
