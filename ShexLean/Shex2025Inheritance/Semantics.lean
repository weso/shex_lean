import ShexLean.Shex2025Inheritance.Syntax
import ShexLean.Common.DisjointUnion

/-!
Tables 1–3 (§4.1) of the paper. They give three satisfaction relations
that are mutually recursive:

* `M,τ ⊨ e` (`SatisfiesEFuel`): triple expressions.
* `n,τ ⊨ s` (`SatisfiesFuel`): a shape expression for a node.
* `M,τ ⊨ s` (`SatisfiesMFuel`): a shape expression for a set of triples.
  This relation is new in ShEx with inheritance. `extends` needs it.

**Why there is a `Fuel` parameter.** In the 2017 version, `typing` gives
the shape of a reference. Thus, `Satisfies` and `Matches` are well-founded
by plain structural recursion on the syntax tree. Here, rule 18 of Table 3
(`extends X h`) does a recursion into the definitions of other labels
(`ext-te(x)` and `restr(x)`, which are `(S.shapeDef x).extTe` and
`.restrOf`, for each ancestor `x`). This is a schema lookup. It is not a
subterm of the current expression.

The paper proves termination separately (its Lemma 1). The proof uses the
acyclicity of the extension hierarchy `H_S` (Definition 3 and Definition 6).
A plain structurally recursive definition is in fact not correct in
general. If there is an extends cycle (`H_S` is not acyclic), the relation
does not terminate.

To get a total Lean function before the proof of Lemma 1, we use the
usual fuel method:

* An explicit argument `Fuel : ℕ` goes through all three relations.
* Each recursive call decreases `Fuel` by one. This applies to all calls,
  not only to the `extends` steps. Thus, `Fuel` is a conservative step
  counter, but termination is a trivial `Nat` recursion.
* When `Fuel` is `0`, the result is `False`.

Thus, `SatisfiesFuel`, `SatisfiesMFuel` and `SatisfiesEFuel` are not yet
the real relations of the paper. They are an under-approximation bounded
by fuel, and they are total by construction. Lemma 1 of the paper says
that, for well-defined schemas, a concrete fuel bound makes them agree with
the real relations (which do not depend on fuel). `Termination.lean`
proves it.

**Why there is no `mutual` keyword.** The paper gives the three relations
as mutually recursive. But the call graph is as follows:

* Table 1 (`SatisfiesEFuel`) calls only itself. (For `.tc`, the use of
  `@z` is a `typing` lookup written inline. Rule 10 of Table 2 has no more
  recursion. This agrees with `te-tpattern` in the 2017 formalization.)
* Table 3 (`SatisfiesMFuel`) calls itself and Table 1. It never calls
  Table 2.
* Table 2 (`SatisfiesFuel`) calls itself and Table 3. Table 3 and Table 1
  never call Table 2.

Thus, the dependency order is a strict chain:
`SatisfiesEFuel → SatisfiesMFuel → SatisfiesFuel`. We define each relation
as an ordinary (not mutual) recursive `def` that decreases `Fuel`, in this
order.
-/

namespace ShexLean.Inheritance

/-- `subject(M)`: the common subject of a nonempty set of triples `M`. (If
`M` is a real neighbourhood set, this subject is unique.) It is selected
with classical choice. On `M = ∅`, the result is a junk value
(`.iri ""`). The notion of the paper is also not defined for this case.
(Rule 13 applies only when `M` is the neighbourhood of a node.) -/
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

/-- The membership property of `Me`. This lemma fixes the
`Classical.decPred` instance of the filter one time, here. This prevents
instance mismatches at the call sites. (Refer to the notes about this
problem in `Proposition1.lean`.) -/
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
sets `Mx x`. Rule 18 of Table 3 uses this to divide a neighbourhood set
into one part that satisfies `h`, and one part for each ancestor that is
extended (transitively). -/
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
  -- Rule 18 (`extends X h`). `M` splits into two types of parts. `M'` satisfies
  -- `h` as a shape (rule 17, with the `closed` and `extra` of `h`). This is the
  -- `M', τ ⊨ h` of the paper, not only a Table 1 check on the triple expression of `h`.
  -- There is one `Mx x` for each `x ∈ anc(X)`. It satisfies `ext-te(x)`. If there is a
  -- `restr(x)`, the union of the `Mx z` for `z ∈ anc(x)` satisfies `restr(x)`.
  | fuel+1, S, G, τ, M, .extends xs h =>
      ∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        SatisfiesMFuel fuel S G τ M' (.ofShape h) ∧
        (∀ x ∈ S.ancSet xs, SatisfiesEFuel fuel S G τ (Mx x) (S.shapeDef x).extTe) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          SatisfiesMFuel fuel S G τ ((S.anc x).biUnion Mx) u)

/-- `n,τ ⊨ s` (Table 2), bounded by `Fuel`. -/
def SatisfiesFuel : (Fuel : ℕ) → Schema → Graph → Typing → RDFNode → ShapeExpr → Prop
  | 0, _, _, _, _, _ => False
  -- Rule 6 (`c`).
  | _+1, _, _, _, n, .constraint c => c n
  -- Rules 11/12 (`[closed][extra P]⟨e⟩` / `extends X h`): the two rules use
  -- the judgment `M,τ ⊨ s` on `neigh_G(n)`, for the same `s`.
  | fuel+1, S, G, τ, n, .ofShape h => SatisfiesMFuel fuel S G τ (neigh G n) (.ofShape h)
  | fuel+1, S, G, τ, n, .extends xs h => SatisfiesMFuel fuel S G τ (neigh G n) (.extends xs h)
  -- Rules 7/8/9 (`or`/`and`/`not`).
  | fuel+1, S, G, τ, n, .or s1 s2 => SatisfiesFuel fuel S G τ n s1 ∨ SatisfiesFuel fuel S G τ n s2
  | fuel+1, S, G, τ, n, .and s1 s2 => SatisfiesFuel fuel S G τ n s1 ∧ SatisfiesFuel fuel S G τ n s2
  | fuel+1, S, G, τ, n, .not s => ¬ SatisfiesFuel fuel S G τ n s

/-! General lemmas about `Me`, `Mnotin` and the `.ofShape` case of
`SatisfiesMFuel`. Many worked examples use them. -/

/-- Let `Me τ M e = M` (a triple constraint of `e` consumes each triple of
`M`). If `M` satisfies `e` (Table 1), then `M` also satisfies the trivial
shape `[closed:=false][extra:=none]⟨e⟩` (rule 17). `Mnotin` must be empty,
because it is always `⊆ M \ Me = M \ M = ∅`.

The `M'` part of an `extends X h` must satisfy this: `M', τ ⊨ h`
(rule 18). The check is against `h` as a shape, not directly against
`h.triples`. -/
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

/-- The converse of `ofShape_of_Me_eq_self`. Let each triple of `M` have a
predicate that is already in `e`. (Thus, no triple can go into the "extra"
set.) Then a witness of `M, τ ⊨ [extra:=none]⟨e⟩` (rule 17) forces
`Me τ M e = M`. Thus, `M` itself satisfies `e` (Table 1), not only a part
of `M`.

This lemma is necessary to change an obligation `M', τ ⊨ h` (the
`.ofShape h` part of rule 18) back into a `SatisfiesEFuel` fact about
`M'`. The reason is that rule 18 checks `M'` against `h` as a shape, not
directly against `h.triples`. -/
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
