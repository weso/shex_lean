import ShexLean.Common.RDF
import ShexLean.Common.Typing
import ShexLean.Common.DisjointUnion
import ShexLean.Shex2017Schemas.Syntax
import Mathlib.Data.Finset.Basic

/-!
The `⊢` and `⊨` relations of Fig. 2 in Boneva, Labra Gayo, Prud'hommeaux
(2017): "node satisfies a shape expression" and "set of triples matches a
triple expression".

Both relations are parameterized by a `t`, exactly as `t, n ⊢ S`
and `t, N ⊨ E` in the paper. The paper stresses that `t, n ⊢ S` "is
by recursion on the structure of `S`" (§3.1, Discussion on `⊢`) — the only
place a *shape label* gets resolved is by consulting `t` in Rule
te-tpattern, not by a recursive call into `⊢` on `def(L)`. So for a fixed
`t` the relation is a well-founded recursion on the finite AST of `S`
(resp. `E`), not a fixpoint over `⊢` itself. This is exactly why it can be
defined as ordinary mutually recursive `Prop`-valued functions below, rather
than as a mutual `inductive`: Rule se-shape-not's premise `¬ (t, n ⊢ S)`
is a negative occurrence of `⊢`, which Lean's strict-positivity check would
reject for an `inductive` family but which is entirely fine for a recursive
function, since `S` is a strictly smaller subterm than `NOT S`.

Where the paper lists several rules with the same conclusion shape (the two
`se-value-descr` rules, and the two `te-some-of` rules), the corresponding
function equation below is their disjunction: the relation holds iff *some*
rule instance applies, matching "there exists a derivation".

Definition 2 ("correct typing") is stated directly in terms of `Satisfies`:
`t` is correct if for every `(n, L) ∈ t`, `Satisfies G t n
(S.shapeDef L)` holds. The later machinery of §3.2–3.3 (stratification,
maximal correct typing) that turns `⊢`/`⊨` into a well-defined `SHAPES_SEM`
is left for a follow-up step.
-/

namespace ShexLean

/-- `n ∈ V` (Rule se-value-descr1): whether the RDF node `n` belongs to the
value description `V`, i.e. `n` is an IRI or a literal explicitly listed in
`V`. Blank nodes are never members of `V` this way — they can only satisfy
`V` via the separate `_b` constant, Rule se-value-descr2. -/
abbrev InV (n : RDFNode) (V : ValueDescr) : Prop :=
  match n with
  | .iri i => ValueItem.iri i ∈ V
  | .lit l => ValueItem.lit l ∈ V
  | .bnode _ => False

/-- `_b ∈ V` and `n` is a blank node (Rule se-value-descr2). An `abbrev`,
like `InV`, for `decide`. -/
abbrev BNodeInV (n : RDFNode) (V : ValueDescr) : Prop :=
  match n with
  | .bnode _ => ValueItem.anyBlank ∈ V
  | _ => False

mutual

/-- `t, n ⊢ S` (Fig. 2a): node `n` (of graph `G`) satisfies shape
expression `S` under `t`. -/
def Satisfies (G : Graph) (t : Typing) (n : RDFNode) : ShExpr → Prop
  -- se-value-descr1 ∨ se-value-descr2.
  | .valueDescr V => InV n V ∨ BNodeInV n V
  -- se-neig-descr.
  | .neigDescr E => Matches G t (neigh G n) E
  -- se-shape-and.
  | .and S1 S2 => Satisfies G t n S1 ∧ Satisfies G t n S2
  -- se-shape-or1 ∨ se-shape-or2.
  | .or S1 S2 => Satisfies G t n S1 ∨ Satisfies G t n S2
  -- se-shape-not: `n` satisfies `NOT S` iff it does *not* satisfy `S`.
  | .not S => ¬ Satisfies G t n S

/-- `t, N ⊨ E` (Fig. 2b): the set of triples `N` matches triple
expression `E` under `t`. -/
def Matches (G : Graph) (t : Typing) (N : Finset Triple) : TExpr → Prop
  -- te-tpattern: `N` is the singleton `{(subj, pred, obj)}` for some triple
  -- whose predicate is in `P` and whose object has type `L` in `t`.
  | .tPattern P L =>
      ∃ subj pred obj, N = {(⟨subj, pred, obj⟩ : Triple)} ∧ pred ∈ P ∧ t.has obj L
  -- te-empty.
  | .empty => N = ∅
  -- te-some-of1 ∨ te-some-of2.
  | .someOf E1 E2 => Matches G t N E1 ∨ Matches G t N E2
  -- te-each-of.
  | .eachOf E1 E2 =>
      ∃ N1 N2, DisjointUnion N N1 N2 ∧ Matches G t N1 E1 ∧ Matches G t N2 E2
  -- te-repet: `N` splits into some `k`-tuple of disjoint sets `Ns`, each
  -- matching `E`, with `min ≤ k` and (when `max = some m`) `k ≤ m`.
  | .rep E min max =>
      ∃ Ns : List (Finset Triple), DisjointUnionList N Ns ∧
        min ≤ Ns.length ∧ (∀ m', max = some m' → Ns.length ≤ m') ∧
        ∀ Ni ∈ Ns, Matches G t Ni E
end

/-! ### Smart constructors

Every worked example proves `Matches`/`Satisfies` goals by supplying an
explicit witness (a triple's subject/predicate/object, or the list of
`Finset`s a `.rep` splits `N` into) and then discharging the rule's side
conditions — usually `Finset`/`List` (dis)equalities and memberships, all
`Decidable` — one at a time via `by decide`. The three lemmas below package
that: each takes the witness as an explicit argument and the recursive
`Matches` premise(s) as an ordinary argument, and gives every *decidable*
side condition a `by decide` (or, for `.rep`'s length bound, an equivalent
short tactic) default, so `refine Matches.rep_of G t Ns ?_` etc. leaves
only the substantive goal(s) instead of every side condition individually.
This changes proof *packaging* only, not the underlying rules: each lemma's
body is exactly the anonymous-constructor term the un-packaged proof would
have written by hand. -/

/-- Smart constructor for Rule te-tpattern: a single triple `(subj, pred,
obj)` matches `.tPattern P L` when its predicate is in `P` and its object
has type `L` in `t`. -/
theorem Matches.tPattern_of (G : Graph) (t : Typing) (subj : Subject) (pred : IRI)
    (obj : RDFNode) {P : PropSet} {L : Label}
    (hpred : pred ∈ P := by decide) (htyp : t.has obj L := by decide) :
    Matches G t {(⟨subj, pred, obj⟩ : Triple)} (.tPattern P L) :=
  ⟨subj, pred, obj, rfl, hpred, htyp⟩

/-- Smart constructor for Rule te-each-of: `N` matches `.eachOf E1 E2` via an
explicit disjoint split `N1 ⊎ N2 = N`, given `N1`/`N2` each match `E1`/`E2`.
-/
theorem Matches.eachOf_of (G : Graph) (t : Typing) {N : Finset Triple} (N1 N2 : Finset Triple)
    {E1 E2 : TExpr} (h1 : Matches G t N1 E1) (h2 : Matches G t N2 E2)
    (hdisj : Disjoint N1 N2 := by decide) (hunion : N = N1 ∪ N2 := by decide) :
    Matches G t N (.eachOf E1 E2) :=
  ⟨N1, N2, ⟨hdisj, hunion⟩, h1, h2⟩

/-- Smart constructor for Rule te-repet: `N` matches `.rep E min max` via an
explicit disjoint split `Ns` of `N`, given every `Ni ∈ Ns` matches `E`. The
`min`/`max` length bounds are discharged automatically: `hmax`'s `cases hm'
<;> decide` closes both the `max = none` case (`cases` alone finds no
matching constructor) and a concrete `max = some k` case (`cases` fixes
`m' := k`, leaving `Ns.length ≤ k` for `decide`). -/
theorem Matches.rep_of (G : Graph) (t : Typing) {N : Finset Triple} (Ns : List (Finset Triple))
    {E : TExpr} {min : ℕ} {max : Option ℕ} (hmem : ∀ Ni ∈ Ns, Matches G t Ni E)
    (hpairwise : Ns.Pairwise Disjoint := by decide)
    (hunion : N = Ns.foldr (· ∪ ·) ∅ := by decide)
    (hmin : min ≤ Ns.length := by decide)
    (hmax : ∀ m', max = some m' → Ns.length ≤ m' := by intro m' hm'; cases hm' <;> decide) :
    Matches G t N (.rep E min max) :=
  ⟨Ns, ⟨hpairwise, hunion⟩, hmin, hmax, hmem⟩

/-- Specialization of `Matches.rep_of` for the common case of a *singleton*
witness split (`Ns := [N]`, so the matched set is just `N` itself) —
collapses the `∀ Ni ∈ [N], Matches G t Ni E` obligation to a single
`Matches G t N E` premise, discharging the `List.Pairwise`/union bookkeeping
via `simp` instead of `decide` since `N` is an arbitrary (not necessarily
concrete) `Finset Triple` here. -/
theorem Matches.rep_single_of (G : Graph) (t : Typing) (N : Finset Triple) {E : TExpr}
    {min : ℕ} {max : Option ℕ} (h : Matches G t N E) (hmin : min ≤ 1 := by decide)
    (hmax : ∀ m', max = some m' → 1 ≤ m' := by intro m' hm'; cases hm' <;> decide) :
    Matches G t N (.rep E min max) :=
  Matches.rep_of G t [N]
    (by intro Ni hNi; simp only [List.mem_singleton] at hNi; subst hNi; exact h)
    (by simp) (by simp) hmin hmax

/-- Specialization of `Matches.rep_of` for the common case of an *empty*
witness split (`Ns := []`, so `N = ∅`) — the `∀ Ni ∈ [], ...` obligation
discharges itself, leaving only the (still decidable, since `min`/`max` are
concrete at any real call site) length bounds. -/
theorem Matches.rep_empty_of (G : Graph) (t : Typing) {E : TExpr} {min : ℕ}
    {max : Option ℕ} (hmin : min ≤ 0 := by decide)
    (hmax : ∀ m', max = some m' → 0 ≤ m' := by intro m' hm'; cases hm' <;> decide) :
    Matches G t (∅ : Finset Triple) (.rep E min max) :=
  Matches.rep_of G t [] (by intro Ni hNi; cases hNi) (by simp) (by simp) hmin hmax

end ShexLean
