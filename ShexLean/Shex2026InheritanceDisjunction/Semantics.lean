import ShexLean.Shex2026InheritanceDisjunction.Syntax
import ShexLean.Common.DisjointUnion

/-!
Tables 1–3 (§4.1) of the 2025 paper "Shape Expressions with Inheritance".
Here, rule 18 (`extends`) has a more general form: it accepts a
disjunction of shapes. Refer to the module docstring of `Syntax.lean` for
the background of §6 and for the design with `hs : List Shape`.

All the definitions here are the same as in
`ShexLean.Shex2025Inheritance.Semantics`, *except* rule 18 (the
`.extends` case of `SatisfiesMFuel`). Refer to that case below for the
change: one more existential witness, `pick`. Its docstring tells why one
witness, shared by the full `S.ancSet xs` of one `.extends` occurrence, is
exactly the fix that §6 describes ("(1) record which disjunct... (2) check
all subtypes agree").

**Why the relations need a `Fuel` parameter, which the 2017 formalization
does not need.** In `ShexLean/Shex2017Schemas/Semantics.lean`, `typing`
gives the shape of a *reference* (Rule te-tpattern: `typing.has obj L`,
with no recursive call into `def(L)`). Thus, `Satisfies` and `Matches` are
well-founded by plain structural recursion on the finite syntax tree.

Here, rule 18 of Table 3 (`extends X hs`) does a recursion into the
*definitions of other labels* (`ext-te(x)` and `restr(x)`, which are
`(S.shapeDef x).extTeAt _` and `.restrOf`, for each ancestor `x`). This is
a schema lookup. It is not a subterm of the current expression. The paper
must prove termination separately (its Lemma 1), with a call-tree
argument that uses the acyclicity of the extension hierarchy `H_S`
(Definition 3 and Definition 6).

Thus, a plain structurally recursive definition of `Satisfies` is in fact
not correct in general. If there is an extends cycle (`H_S` is not
acyclic), the relation does not terminate. To get a *total* Lean function
first, before the proof of the real Lemma 1, we use the usual fuel method.
(The `remMin` process of `ShexLean/Shex2017Schemas/Lemma2.lean` also uses
fuel.)

* An explicit argument `Fuel : ℕ` goes through all three relations.
* *Each* recursive call decreases `Fuel` by one, not only the `extends`
  steps. Thus, termination is trivial: it is a structural `Nat` recursion
  on `Fuel`. The cost is that `Fuel` is a conservative step counter.
* When `Fuel` is `0`, the result is `False`.

Thus, `SatisfiesFuel`, `SatisfiesMFuel` and `SatisfiesEFuel` are *not* yet
the real relations of the paper. They are an under-approximation bounded
by fuel, and they are total by construction. Lemma 1 of the paper says
that, for well-defined schemas, a canonical concrete fuel bound makes them
agree with the real relations (which do not depend on fuel).
`Termination.lean` proves it.

**Why the three relations do not need the Lean keyword `mutual`.** The
paper gives them as mutually recursive. But the call graph is as follows:

* Table 1 (`SatisfiesEFuel`) calls only itself. (For `.tc`, the use of
  `@z` is a `typing` lookup written inline. Rule 10 of Table 2,
  `@z: (n,z) ∈ τ`, has no more recursion, exactly as `te-tpattern` in the
  2017 formalization. Thus, a real mutual call gives no advantage.)
* Table 3 (`SatisfiesMFuel`) calls itself and Table 1. It never calls
  Table 2.
* Table 2 (`SatisfiesFuel`) calls itself and Table 3. Table 3 and Table 1
  never call Table 2.

Thus, the dependency order is a strict chain:
`SatisfiesEFuel → SatisfiesMFuel → SatisfiesFuel`. We define each relation
as an ordinary (not mutual) recursive `def` that decreases `Fuel`, in this
order.
-/

namespace ShexLean.InheritanceDisjunction

/-- `subject(M)`: the common subject of a nonempty set of triples `M`. (In
the paper, this subject is unique, because `M` is a real neighbourhood
set.) It is selected with classical choice. On `M = ∅`, the result is a
junk value (`.iri ""`). The notion of the paper is also not defined for
this case. (Rule 13 of Table 3 applies only when `M` is the neighbourhood
of a real node.) -/
noncomputable def subjectOf (M : Finset Triple) : RDFNode :=
  if h : M.Nonempty then (h.choose.subj : RDFNode) else RDFNode.iri ""

/-- `M^e` (Table 3, the discussion before rule 18): the triples of `M` that
satisfy a triple constraint of `e` with `τ`. Thus, their predicate matches
a triple constraint `p @z` of `e`, and their object has the type `z` in
`τ`. -/
noncomputable def Me (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  haveI := Classical.decPred (fun t : Triple => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)
  M.filter (fun t => ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z)

/-- `M^{e'}` (Table 3): the triples of `M` whose property occurs in `e`,
but that satisfy no triple constraint of `e`. -/
noncomputable def Mnotin (τ : Typing) (M : Finset Triple) (e : TripleExpr) : Finset Triple :=
  haveI := Classical.decPred (fun t : Triple => t.pred ∈ e.props)
  (M.filter (fun t => t.pred ∈ e.props)) \ Me τ M e

/-- `props(M)` (Table 3): the properties of the triples in `M`. -/
def props (M : Finset Triple) : Finset IRI := M.image Triple.pred

/-- The membership property of `Me`. This lemma fixes the instance of the
filter one time, here, and not at each call site. This prevents a frequent
problem: an instance mismatch between `Classical.decPred` and
`Finset.filter`. (Refer to the notes about this problem in
`ShexLean/Shex2025Inheritance/Proposition1.lean`.) -/
theorem mem_Me {τ : Typing} {M : Finset Triple} {e : TripleExpr} {t : Triple} :
    t ∈ Me τ M e ↔ t ∈ M ∧ ∃ z, (t.pred, z) ∈ e.tcs ∧ τ.has t.obj z := by
  unfold Me; simp only [Finset.mem_filter]

/-- The membership property of `Mnotin`. The reason is the same as for
`mem_Me`. -/
theorem mem_Mnotin {τ : Typing} {M : Finset Triple} {e : TripleExpr} {t : Triple} :
    t ∈ Mnotin τ M e ↔ (t ∈ M ∧ t.pred ∈ e.props) ∧ t ∉ Me τ M e := by
  unfold Mnotin; simp only [Finset.mem_sdiff, Finset.mem_filter]

/-- `M = M' ⊎ (⊎_{x ∈ Idx} Mx)`: `M'` and the sets `Mx x` (for `x ∈ Idx`)
are pairwise disjoint, and their union is `M`. There is a finite number of
sets `Mx x`. This is the partition of rule 18 of Table 3. It divides a
neighbourhood set into one part that satisfies `h`, and one part for each
ancestor that is extended (transitively). -/
def DisjointUnionOn (M M' : Finset Triple) (Idx : Finset Label)
    (Mx : Label → Finset Triple) : Prop :=
  Disjoint M' (Idx.biUnion Mx) ∧ (Idx : Set Label).PairwiseDisjoint Mx ∧
    M = M' ∪ Idx.biUnion Mx

/-- `M,τ ⊨ e` (Table 1), bounded by `Fuel`. Refer to the module
docstring. -/
def SatisfiesEFuel : (Fuel : ℕ) → Schema → Graph → Typing → Finset Triple → TripleExpr → Prop
  | 0, _, _, _, _, _ => False
  -- Rule 1 (`ε`).
  | _+1, _, _, _, M, .empty => M = ∅
  -- Rule 2 (`p @z`). `o,τ ⊨ @z` is written inline as `τ.has o z` (rule 10 of
  -- Table 2 has no more recursion, refer to the module docstring).
  | _+1, _, _, τ, M, .tc p z => ∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z
  -- Rule 3 (`e1|e2`).
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

/-- `M,τ ⊨ s` (Table 3), bounded by `Fuel`. -/
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
  -- Rule 18 (`extends X hs`, a general form of `extends X h` of the paper).
  -- `M` splits into two types of parts. `M'` satisfies *one* disjunct of `hs`
  -- *as a shape* (rule 17 of Table 3, with the `closed` and `extra` of that disjunct).
  -- This is `M', τ ⊨ h` in the general form `∃ h ∈ hs, M', τ ⊨ h`. This part alone
  -- has no ambiguity, because the plain `or` of rule 14 already lets one node
  -- select a disjunct. There is one `Mx x` for each `x ∈ anc(X)`. It satisfies
  -- `ext-te(x)`. If there is a `restr(x)`, the union of the `Mx z` for
  -- `z ∈ anc(x)` satisfies `restr(x)`.
  --
  -- **The fix for §6.** One witness `pick : Label → ℕ` is selected one time
  -- for each `.extends` occurrence. (It is bound in the same existential as `Mx`.
  -- It does not go globally through `Satisfies`.) It selects *which* disjunct of
  -- `(S.shapeDef x).extTeList` is the check for each ancestor `x`. `extTeAt` takes
  -- the element of that list at this index. `S.ancSet xs` already puts each
  -- ancestor that `xs` can reach into one `Finset`, with no duplicates. (Thus, if
  -- two different direct parents reach the same grandparent, the grandparent has
  -- *one* slot, not two.) Also, `pick` is selected one time for the *full*
  -- `S.ancSet xs`, in this one existential. Thus, two inheritance paths that go to
  -- the same disjunctive ancestor must agree on the same `Mx` and the same
  -- disjunct. This is exactly "(1) record which disjunct has been satisfied...
  -- (2) check all subtypes satisfy the same disjunct" from the sketch of the
  -- paper. The fix adds no global parameter for the schema or for the typing
  -- at any other location.
  | fuel+1, S, G, τ, M, .extends xs hs =>
      ∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        (∃ h ∈ hs, SatisfiesMFuel fuel S G τ M' (.ofShape h)) ∧
        (∀ x ∈ S.ancSet xs,
          SatisfiesEFuel fuel S G τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          SatisfiesMFuel fuel S G τ ((S.anc x).biUnion Mx) u)

/-- `n,τ ⊨ s` (Table 2), bounded by `Fuel`. -/
def SatisfiesFuel : (Fuel : ℕ) → Schema → Graph → Typing → RDFNode → ShapeExpr → Prop
  | 0, _, _, _, _, _ => False
  -- Rule 6 (`c`).
  | _+1, _, _, _, n, .constraint c => c n
  -- Rules 11/12 (`[closed][extra P]⟨e⟩` / `extends X hs`): the two rules use
  -- the judgment `M,τ ⊨ s` on `neigh_G(n)`, for the same `s`.
  | fuel+1, S, G, τ, n, .ofShape h => SatisfiesMFuel fuel S G τ (neigh G n) (.ofShape h)
  | fuel+1, S, G, τ, n, .extends xs hs => SatisfiesMFuel fuel S G τ (neigh G n) (.extends xs hs)
  -- Rules 7/8/9 (`or`/`and`/`not`).
  | fuel+1, S, G, τ, n, .or s1 s2 => SatisfiesFuel fuel S G τ n s1 ∨ SatisfiesFuel fuel S G τ n s2
  | fuel+1, S, G, τ, n, .and s1 s2 => SatisfiesFuel fuel S G τ n s1 ∧ SatisfiesFuel fuel S G τ n s2
  | fuel+1, S, G, τ, n, .not s => ¬ SatisfiesFuel fuel S G τ n s

/-! General lemmas about `Me`, `Mnotin` and the `.ofShape` case of
`SatisfiesMFuel`. Many worked examples
(`ShexLean/Shex2026InheritanceDisjunction/examples/`) use them. They are
not specific to one example. They are the same as in
`ShexLean.Shex2025Inheritance.Semantics`. None of them use `.extends`. -/

/-- Let `Me τ M e = M` (a triple constraint of `e` "consumes" each triple
of `M`). If `M` satisfies `e` (Table 1), then `M` also satisfies the
trivial shape `[closed:=false][extra:=none]⟨e⟩` (rule 17 of Table 3).
`Mnotin` must be empty, because it is always `⊆ M \ Me = M \ M = ∅`.

The `M'` part of an `extends X hs` must satisfy exactly this:
`M', τ ⊨ h` for the `h ∈ hs` that is selected (rule 18 of Table 3). -/
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

/-- Let a singleton `{(n,p,o)}` satisfy a plain triple constraint `p @z`
with `τ`. Then it also satisfies the trivial shape
`[closed:=false][extra:=none] ⟨p @z⟩` (rule 17, `.ofShape`). This is the
special case of `ofShape_of_Me_eq_self` that most `.extends` proofs
need. -/
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

/-- The converse of the argument in `ofShape_of_Me_eq_self`. Let each
triple of `M` have a predicate that is already in `e`. (Thus, no triple
can go into the "extra" set.) Then a witness of
`M, τ ⊨ [extra:=none]⟨e⟩` (rule 17 of Table 3) forces `Me τ M e = M`.
Thus, `M` itself satisfies `e` (Table 1), not only a part of `M`. -/
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

end ShexLean.InheritanceDisjunction
