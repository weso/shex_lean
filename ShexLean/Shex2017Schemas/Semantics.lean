import ShexLean.Common.RDF
import ShexLean.Common.Typing
import ShexLean.Common.DisjointUnion
import ShexLean.Shex2017Schemas.Syntax
import Mathlib.Data.Finset.Basic

/-!
The `⊢` and `⊨` relations of Fig. 2 in Boneva, Labra Gayo, Prud'hommeaux
(2017):

* `⊢`: "a node satisfies a shape expression".
* `⊨`: "a set of triples matches a triple expression".

The two relations have a parameter `t`, as `t, n ⊢ S` and `t, N ⊨ E` have in the paper.

The paper says that `t, n ⊢ S` "is by recursion on
the structure of `S`" (§3.1, Discussion on `⊢`).
Rule te-tpattern finds the shape of a label in `t`.
It does not make a recursive call of `⊢` on `def(L)`.
Thus, for a fixed `t`, the relation is a well-founded
recursion on the syntax tree of `S` (or `E`).
It is not a fixed point of `⊢`.

For this reason, `Satisfies` and `Matches` below are
mutually recursive functions, not a mutual `inductive`.
The premise of Rule se-shape-not is `¬ (t, n ⊢ S)`.
This is a negative occurrence of `⊢`.
The positivity check of Lean does not accept this in an `inductive` family.
A recursive function accepts it, because `S` is a smaller subterm than `NOT S`.

Some rules of the paper have the same form of conclusion: the
two `se-value-descr` rules, and the two `te-some-of` rules.
For these rules, the function equation below is their disjunction.
The relation is true if and only if *one* of the rules applies.
This agrees with "there is a derivation".

Definition 2 ("correct typing") uses `Satisfies` directly.
The typing `t` is correct if `Satisfies G t n (S.shapeDef L)` is true for each `(n, L) ∈ t`.
§3.2 and §3.3 (stratification, maximal correct typing)
change `⊢` and `⊨` into a well-defined `SHAPES_SEM`.
Other files do this work.
-/

namespace ShexLean


/-- `n ∈ V` (Rule se-value-descr1): the RDF node `n` is in the value description `V`.
Thus, `n` is an IRI or a literal that `V` lists explicitly.
With this rule, a blank node is never in `V`.
A blank node can satisfy `V` only with the constant `_b` (Rule se-value-descr2). -/
abbrev InV (n : RDFNode) (V : ValueDescr) : Prop :=
  match n with
  | .iri i => ValueItem.iri i ∈ V
  | .lit l => ValueItem.lit l ∈ V
  | .bnode _ => False

/-- `_b ∈ V`, and `n` is a blank node (Rule se-value-descr2).
This is an `abbrev`, as `InV` is, for `decide`. -/
abbrev BNodeInV (n : RDFNode) (V : ValueDescr) : Prop :=
  match n with
  | .bnode _ => ValueItem.anyBlank ∈ V
  | _ => False

mutual

/-- `t, n ⊢ S` (Fig. 2a): the node `n` (of the graph
`G`) satisfies the shape expression `S` with `t`. -/
def Satisfies (G : Graph) (t : Typing) (n : RDFNode) : ShExpr → Prop
  -- se-value-descr1 ∨ se-value-descr2.
  | .valueDescr V => InV n V ∨ BNodeInV n V
  -- se-neig-descr.
  | .neigDescr E => Matches G t (neigh G n) E
  -- se-shape-and.
  | .and S1 S2 => Satisfies G t n S1 ∧ Satisfies G t n S2
  -- se-shape-or1 ∨ se-shape-or2.
  | .or S1 S2 => Satisfies G t n S1 ∨ Satisfies G t n S2
  -- se-shape-not: `n` satisfies `NOT S` if and only if `n` does *not* satisfy `S`.
  | .not S => ¬ Satisfies G t n S

/-- `t, N ⊨ E` (Fig. 2b): the set of triples `N` matches the triple expression `E` with `t`. -/
def Matches (G : Graph) (t : Typing) (N : Finset Triple) : TExpr → Prop
  -- te-tpattern: `N` is the singleton `{(subj, pred, obj)}` for a triple.
  -- The predicate of this triple is in `P`, and its object has the type `L` in `t`.
  | .tPattern P L =>
      ∃ subj pred obj, N = {(⟨subj, pred, obj⟩ : Triple)} ∧ pred ∈ P ∧ t.has obj L
  -- te-empty.
  | .empty => N = ∅
  -- te-some-of1 ∨ te-some-of2.
  | .someOf E1 E2 => Matches G t N E1 ∨ Matches G t N E2
  -- te-each-of.
  | .eachOf E1 E2 =>
      ∃ N1 N2, DisjointUnion N N1 N2 ∧ Matches G t N1 E1 ∧ Matches G t N2 E2
  -- te-repet: `N` splits into a `k`-tuple `Ns` of disjoint sets.
  -- Each set matches `E`.
  -- Also, `min ≤ k`, and `k ≤ m` when `max = some m`.
  | .rep E min max =>
      ∃ Ns : List (Finset Triple), DisjointUnionList N Ns ∧
        min ≤ Ns.length ∧ (∀ m', max = some m' → Ns.length ≤ m') ∧
        ∀ Ni ∈ Ns, Matches G t Ni E
end


-- The two notations below do not bind `G`.
-- The paper also does not show the graph explicitly.
-- `G` is the local variable with the name `G` at the location where you use the notation.
-- We disable `quotPrecheck` and `hygiene` only for these two declarations.
-- If they are enabled, Lean does not accept a free `G` (quotation
-- precheck), or uses a new `G` and not the `G` in scope (hygiene).
set_option quotPrecheck false in
set_option hygiene false in
/-- `(t, n) ⊢ S` (Fig. 2a): infix notation for `Satisfies`. -/
scoped notation:50 "(" t ", " n ")" " ⊢ " S:51 => Satisfies G t n S

set_option quotPrecheck false in
set_option hygiene false in
/-- `(t, N) ⊨ E` (Fig. 2b): infix notation for `Matches`. -/
scoped notation:50 "(" t ", " N ")" " ⊨ " E:51 => Matches G t N E

/-! ### Smart constructors

A worked example proves a `Matches` or `Satisfies` goal in two steps:

1. It gives an explicit witness.
   The witness is the subject, predicate and object of a triple,
   or the list of `Finset`s that `.rep` splits `N` into.
2. It proves the side conditions of the rule with `by decide`.
   These side conditions are equalities, inequalities and memberships of `Finset` and `List`.
   They are all `Decidable`.

The three lemmas below package these steps:

* The witness is an explicit argument.
* Each recursive `Matches` premise is an ordinary argument.
* Each decidable side condition has the default value `by decide`.

For example, `refine Matches.rep_of G t Ns ?_` leaves only the important goals.
These lemmas change only the packaging of the proofs.
They do not change the rules.
The body of each lemma is the same anonymous-constructor
term that you write by hand without the lemma. -/

/-- Smart constructor for Rule te-tpattern.
A single triple `(subj, pred, obj)` matches `.tPattern P L` if
its predicate is in `P` and its object has the type `L` in `t`. -/
theorem Matches.tPattern_of (G : Graph) (t : Typing) (subj : Subject) (pred : IRI)
    (obj : RDFNode) {P : PropSet} {L : Label}
    (hpred : pred ∈ P := by decide) (htyp : t.has obj L := by decide) :
    Matches G t {(⟨subj, pred, obj⟩ : Triple)} (.tPattern P L) :=
  ⟨subj, pred, obj, rfl, hpred, htyp⟩

/-- Smart constructor for Rule te-each-of.
`N` matches `.eachOf E1 E2` with an explicit disjoint split
`N1 ⊎ N2 = N`, if `N1` matches `E1` and `N2` matches `E2`.
-/
theorem Matches.eachOf_of (G : Graph) (t : Typing) {N : Finset Triple} (N1 N2 : Finset Triple)
    {E1 E2 : TExpr} (h1 : Matches G t N1 E1) (h2 : Matches G t N2 E2)
    (hdisj : Disjoint N1 N2 := by decide) (hunion : N = N1 ∪ N2 := by decide) :
    Matches G t N (.eachOf E1 E2) :=
  ⟨N1, N2, ⟨hdisj, hunion⟩, h1, h2⟩

/-- Smart constructor for Rule te-repet.
`N` matches `.rep E min max` with an explicit disjoint
split `Ns` of `N`, if each `Ni ∈ Ns` matches `E`.

The lemma proves the length bounds `min` and `max` automatically.
In `hmax`, `cases hm' <;> decide` closes the two cases:

* `max = none`: `cases` finds no constructor that matches.
* `max = some k`, with a concrete `k`: `cases` sets `m' := k`.
  Then `decide` proves `Ns.length ≤ k`. -/
theorem Matches.rep_of (G : Graph) (t : Typing) {N : Finset Triple} (Ns : List (Finset Triple))
    {E : TExpr} {min : ℕ} {max : Option ℕ} (hmem : ∀ Ni ∈ Ns, Matches G t Ni E)
    (hpairwise : Ns.Pairwise Disjoint := by decide)
    (hunion : N = Ns.foldr (· ∪ ·) ∅ := by decide)
    (hmin : min ≤ Ns.length := by decide)
    (hmax : ∀ m', max = some m' → Ns.length ≤ m' := by intro m' hm'; cases hm' <;> decide) :
    Matches G t N (.rep E min max) :=
  ⟨Ns, ⟨hpairwise, hunion⟩, hmin, hmax, hmem⟩

/-- A special case of `Matches.rep_of` for the *singleton* witness split (`Ns := [N]`).
Thus, the matched set is `N`.
The obligation `∀ Ni ∈ [N], Matches G t Ni E` becomes one premise, `Matches G t N E`.
The lemma proves the `List.Pairwise` and union
conditions with `simp`, not with `decide`, because here
`N` is a `Finset Triple` that is possibly not concrete. -/
theorem Matches.rep_single_of (G : Graph) (t : Typing) (N : Finset Triple) {E : TExpr}
    {min : ℕ} {max : Option ℕ} (h : Matches G t N E) (hmin : min ≤ 1 := by decide)
    (hmax : ∀ m', max = some m' → 1 ≤ m' := by intro m' hm'; cases hm' <;> decide) :
    Matches G t N (.rep E min max) :=
  Matches.rep_of G t [N]
    (by intro Ni hNi; simp only [List.mem_singleton] at hNi; subst hNi; exact h)
    (by simp) (by simp) hmin hmax

/-- A special case of `Matches.rep_of` for the *empty* witness split (`Ns := []`).
Thus, `N = ∅`.
The obligation `∀ Ni ∈ [], ...` is automatically true.
Only the length bounds stay.
They are decidable, because `min` and `max` are concrete at each real call site. -/
theorem Matches.rep_empty_of (G : Graph) (t : Typing) {E : TExpr} {min : ℕ}
    {max : Option ℕ} (hmin : min ≤ 0 := by decide)
    (hmax : ∀ m', max = some m' → 0 ≤ m' := by intro m' hm'; cases hm' <;> decide) :
    Matches G t (∅ : Finset Triple) (.rep E min max) :=
  Matches.rep_of G t [] (by intro Ni hNi; cases hNi) (by simp) (by simp) hmin hmax

end ShexLean
