import ShexLean.Shex2025Inheritance.Syntax
import ShexLean.Common.DisjointUnion

/-!
Tables 1–3 (§4.1) of the paper: the three mutually-recursive satisfiability
relations `M,τ ⊨ e` (`SatisfiesEFuel`, triple expressions), `n,τ ⊨ s`
(`SatisfiesFuel`, a shape expression under a node), and `M,τ ⊨ s`
(`SatisfiesMFuel`, a shape expression under a set of triples — new for
ShEx with inheritance, needed for `extends`).

**Why a `Fuel` parameter.** In the 2017 version, a shape reference is
resolved by consulting `typing`, so `Satisfies`/`Matches` are well-founded
by plain structural recursion on the AST. Here, Table 3's rule 18
(`extends X h`) recurses into other labels' own definitions
(`ext-te(x)`/`restr(x)` = `(S.shapeDef x).extTe`/`.restrOf`, for `x`
ranging over ancestors) — a schema lookup, not a subterm of the current
expression. The paper proves this terminates separately (its own Lemma 1),
using acyclicity of the extension hierarchy `H_S` (Definition 3/6). A
plain structurally-recursive definition would in fact be false in general:
an extends-cycle (`H_S` not acyclic) makes the relation non-terminating.

To get a total Lean function before proving Lemma 1, we use the standard
fuel idiom: an explicit `Fuel : ℕ` argument threaded through all three
relations, decremented on every recursive call (not just extends-hops, so
`Fuel` is a conservative step-counter but termination is trivial `Nat`
recursion), returning `False` when `Fuel` runs out.

`SatisfiesFuel`/`SatisfiesMFuel`/`SatisfiesEFuel` are consequently not yet
the paper's real relations — they are a fuel-bounded under-approximation,
total by construction. That a concrete fuel bound makes them agree with
the paper's real (fuel-independent) relations, for well-defined schemas,
is the content of the paper's Lemma 1, proved in `Termination.lean`.

**Why no `mutual` keyword**, despite the paper presenting the three
relations as mutually recursive: tracing the call graph, Table 1
(`SatisfiesEFuel`) only calls itself (`.tc`'s use of `@z` is inlined as a
`typing` lookup — Table 2's rule 10 has no further recursion, matching
`te-tpattern` in the 2017 formalization). Table 3 (`SatisfiesMFuel`) calls
itself and Table 1, never Table 2. Table 2 (`SatisfiesFuel`) calls itself
and Table 3, and neither Table 3 nor 1 call back into Table 2. So the
dependency order is a strict chain `SatisfiesEFuel → SatisfiesMFuel →
SatisfiesFuel`, and each can be defined as an ordinary (non-mutual)
`Fuel`-decreasing recursive `def`, in that order.
-/

namespace ShexLean.Inheritance

/-- `subject(M)`: the common subject of a nonempty set of triples `M`
(unique when `M` is an actual neighbourhood set). Classically chosen;
junk value (`.iri ""`) on `M = ∅`, where the paper's notion is undefined
too (rule 13 is only ever exercised with `M` a node's neighbourhood). -/
noncomputable def subjectOf (M : Finset Triple) : RDFNode :=
  if h : M.Nonempty then (h.choose.subj : RDFNode) else RDFNode.iri ""

/-- `M^e` (Table 3, discussion before rule 18): the triples of `M` that
satisfy some triple constraint of `e` under `τ`, i.e. whose predicate
matches a triple constraint `p @z` of `e` and whose object has type `z`
in `τ`. -/
noncomputable def Me (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  haveI := Classical.decPred (fun t : Triple => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)
  M.filter (fun t => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)

/-- `M^{e'}` (Table 3): the triples of `M` whose property appears in `e`
but that satisfy none of `e`'s triple constraints. -/
noncomputable def Mnotin (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  haveI := Classical.decPred (fun t : Triple => t.pred ∈ e.props)
  (M.filter (fun t => t.pred ∈ e.props)) \ Me τ M e

/-- `props(M)` (Table 3): the properties of the triples in `M`. -/
def props (M : Finset Triple) : Finset IRI := M.image Triple.pred

/-- Membership characterization of `Me`, fixing the filter's
`Classical.decPred` instance once here to avoid instance mismatches at
call sites (see `Proposition1.lean`'s notes on this issue). -/
theorem mem_Me {τ : Typing} {M : Finset Triple} {e : TripleExpr} {t : Triple} :
    t ∈ Me τ M e ↔ t ∈ M ∧ ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z := by
  unfold Me; simp only [Finset.mem_filter]

/-- Membership characterization of `Mnotin`, same reasoning as `mem_Me`. -/
theorem mem_Mnotin {τ : Typing} {M : Finset Triple} {e : TripleExpr} {t : Triple} :
    t ∈ Mnotin τ M e ↔ (t ∈ M ∧ t.pred ∈ e.props) ∧ t ∉ Me τ M e := by
  unfold Mnotin; simp only [Finset.mem_sdiff, Finset.mem_filter]

/-- `M = M' ⊎ (⊎_{x ∈ Idx} Mx)`: `M'` and the finitely many `Mx x` (for
`x ∈ Idx`) are pairwise disjoint and their union is `M`. Table 3's rule 18
uses this to partition a neighbourhood set into the portion satisfying `h`
and one portion per (transitively) extended ancestor. -/
def DisjointUnionOn (M M' : Finset Triple) (Idx : Finset Label)
    (Mx : Label → Finset Triple) : Prop :=
  Disjoint M' (Idx.biUnion Mx) ∧ (Idx : Set Label).PairwiseDisjoint Mx ∧
    M = M' ∪ Idx.biUnion Mx

/-- `M,τ ⊨ e` (Table 1), `Fuel`-bounded — see the module docstring. -/
def SatisfiesEFuel : (Fuel : ℕ) → Schema → Graph → Typing → Finset Triple → TripleExpr → Prop
  | 0, _, _, _, _, _ => False
  -- Rule 1 (`ε`).
  | _+1, _, _, _, M, .empty => M = ∅
  -- Rule 2 (`p @z`), with `o,τ ⊨ @z` inlined as `τ.has o z` (Table 2 rule
  -- 10 has no further recursion, see the module docstring).
  | _+1, _, _, τ, M, .tc p z => ∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z
  -- Rules 3 (`e1|e2`).
  | fuel+1, S, G, τ, M, .choice e1 e2 =>
      SatisfiesEFuel fuel S G τ M e1 ∨ SatisfiesEFuel fuel S G τ M e2
  -- Rule 4 (`e1;e2`).
  | fuel+1, S, G, τ, M, .seq e1 e2 =>
      ∃ M1 M2, DisjointUnion M M1 M2 ∧
        SatisfiesEFuel fuel S G τ M1 e1 ∧ SatisfiesEFuel fuel S G τ M2 e2
  -- Rule 5 (`e1*`).
  | fuel+1, S, G, τ, M, .star e =>
      ∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧
        ∀ Ni ∈ Ns, SatisfiesEFuel fuel S G τ Ni e

/-- `M,τ ⊨ s` (Table 3), `Fuel`-bounded. -/
def SatisfiesMFuel : (Fuel : ℕ) → Schema → Graph → Typing → Finset Triple → ShapeExpr → Prop
  | 0, _, _, _, _, _ => False
  -- Rule 13 (`c`).
  | _+1, _, _, _, M, .constraint c => c (subjectOf M)
  -- Rule 17 (`[closed][extra P]⟨e⟩`).
  | fuel+1, S, G, τ, M, .ofShape h =>
      SatisfiesEFuel fuel S G τ (Me τ M h.triples) h.triples ∧
      props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
      (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)
  -- Rules 14/15/16 (`or`/`and`/`not`).
  | fuel+1, S, G, τ, M, .or s1 s2 =>
      SatisfiesMFuel fuel S G τ M s1 ∨ SatisfiesMFuel fuel S G τ M s2
  | fuel+1, S, G, τ, M, .and s1 s2 =>
      SatisfiesMFuel fuel S G τ M s1 ∧ SatisfiesMFuel fuel S G τ M s2
  | fuel+1, S, G, τ, M, .not s => ¬ SatisfiesMFuel fuel S G τ M s
  -- Rule 18 (`extends X h`): `M` splits into `M'` (satisfying `h` as a
  -- shape, rule 17, respecting `h`'s `closed`/`extra`, per the paper's
  -- `M', τ ⊨ h`, not a bare Table 1 check on `h`'s triple expression) and
  -- one `Mx x` per `x ∈ anc(X)` (satisfying `ext-te(x)`, and, if `restr(x)`
  -- is present, the union of `Mx z` over `z ∈ anc(x)` satisfies `restr(x)`).
  | fuel+1, S, G, τ, M, .extends xs h =>
      ∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        SatisfiesMFuel fuel S G τ M' (.ofShape h) ∧
        (∀ x ∈ S.ancSet xs, SatisfiesEFuel fuel S G τ (Mx x) (S.shapeDef x).extTe) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          SatisfiesMFuel fuel S G τ ((S.anc x).biUnion Mx) u)

/-- `n,τ ⊨ s` (Table 2), `Fuel`-bounded. -/
def SatisfiesFuel : (Fuel : ℕ) → Schema → Graph → Typing → RDFNode → ShapeExpr → Prop
  | 0, _, _, _, _, _ => False
  -- Rule 6 (`c`).
  | _+1, _, _, _, n, .constraint c => c n
  -- Rules 11/12 (`[closed][extra P]⟨e⟩` / `extends X h`): both reduce to
  -- the `M,τ ⊨ s` judgment on `neigh_G(n)`, for the very same `s`.
  | fuel+1, S, G, τ, n, .ofShape h => SatisfiesMFuel fuel S G τ (neigh G n) (.ofShape h)
  | fuel+1, S, G, τ, n, .extends xs h => SatisfiesMFuel fuel S G τ (neigh G n) (.extends xs h)
  -- Rules 7/8/9 (`or`/`and`/`not`).
  | fuel+1, S, G, τ, n, .or s1 s2 => SatisfiesFuel fuel S G τ n s1 ∨ SatisfiesFuel fuel S G τ n s2
  | fuel+1, S, G, τ, n, .and s1 s2 => SatisfiesFuel fuel S G τ n s1 ∧ SatisfiesFuel fuel S G τ n s2
  | fuel+1, S, G, τ, n, .not s => ¬ SatisfiesFuel fuel S G τ n s

/-! General-purpose lemmas about `Me`/`Mnotin`/`SatisfiesMFuel`'s `.ofShape`
case, reused by several worked examples. -/

/-- When `Me τ M e = M` (every triple of `M` is consumed by some triple
constraint of `e`), `M` satisfying `e` (Table 1) lifts to `M` satisfying
the trivial `[closed:=false][extra:=none]⟨e⟩` shape (rule 17): `Mnotin` is
forced empty since it's always `⊆ M \ Me = M \ M = ∅`. This is what an
`extends X h`'s `M'` piece needs to satisfy: `M', τ ⊨ h` (rule 18), checked
against `h` as a shape rather than directly against `h.triples`. -/
theorem ofShape_of_Me_eq_self {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {M : Finset Triple} {e : TripleExpr} (hMe : Me τ M e = M)
    (hE : SatisfiesEFuel fuel S G τ M e) :
    SatisfiesMFuel (fuel + 1) S G τ M (.ofShape ⟨false, none, e⟩) := by
  refine ⟨?_, ?_, by simp⟩
  · show SatisfiesEFuel fuel S G τ (Me τ M e) e
    rw [hMe]; exact hE
  · show props (Mnotin τ M e) ⊆ (∅ : Finset IRI)
    rw [Finset.subset_empty, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    unfold props at ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    rw [mem_Mnotin] at ht'
    obtain ⟨⟨htM, _⟩, hnotMe⟩ := ht'
    exact hnotMe (by rw [hMe]; exact htM)

/-- A singleton `{(n,p,o)}` satisfying a bare `p @z` triple constraint
under `τ` also satisfies the trivial shape `[closed:=false][extra:=none]
⟨p @z⟩` (rule 17, `.ofShape`): the special case of `ofShape_of_Me_eq_self`
most `.extends` proofs need. -/
theorem singleton_tc_ofShape {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {p : IRI} {z : Label} {n : Subject} {o : RDFNode} (hty : τ.has o z) :
    SatisfiesMFuel (fuel + 2) S G τ {(⟨n, p, o⟩ : Triple)} (.ofShape ⟨false, none, .tc p z⟩) := by
  apply ofShape_of_Me_eq_self (fuel := fuel + 1) (e := .tc p z) (M := {(⟨n, p, o⟩ : Triple)})
  · apply Finset.Subset.antisymm
    · intro t ht; rw [mem_Me] at ht; exact ht.1
    · intro t ht
      simp only [Finset.mem_singleton] at ht
      subst ht
      rw [mem_Me]
      exact ⟨Finset.mem_singleton_self _, z, by simp [TripleExpr.tcs], hty⟩
  · exact ⟨n, o, rfl, hty⟩

/-- Converse of `ofShape_of_Me_eq_self`: if every triple of `M` has a
predicate already among `e`'s (so none can escape into the "extra"
bucket), an `M, τ ⊨ [extra:=none]⟨e⟩` witness (rule 17) forces
`Me τ M e = M`, i.e. `M` itself satisfies `e` (Table 1), not just some
sub-multiset of it. Needed to turn a `M', τ ⊨ h` obligation (rule 18's
`.ofShape h` piece) back into a `SatisfiesEFuel` fact about `M'`, since
rule 18 checks `M'` against `h` as a shape rather than `h.triples`
directly. -/
theorem Me_eq_self_of_props_subset {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {M : Finset Triple} {e : TripleExpr}
    (hM : SatisfiesMFuel (fuel + 1) S G τ M (.ofShape ⟨false, none, e⟩))
    (hsub : props M ⊆ e.props) :
    Me τ M e = M := by
  obtain ⟨-, hMnotinSub, -⟩ := hM
  apply Finset.Subset.antisymm
  · intro t ht; rw [mem_Me] at ht; exact ht.1
  · intro t ht
    by_contra hnotMe
    have htin : t ∈ Mnotin τ M e := by
      rw [mem_Mnotin]
      exact ⟨⟨ht, hsub (Finset.mem_image_of_mem Triple.pred ht)⟩, hnotMe⟩
    have := hMnotinSub (Finset.mem_image_of_mem Triple.pred htin)
    simp at this

end ShexLean.Inheritance
