import ShexLean.Shex2025Inheritance.Syntax
import ShexLean.Common.DisjointUnion

/-!
Tables 1–3 (§4.1) of the paper. They give three satisfaction relations
that are mutually recursive:

* `M,τ ⊨ e` (`SatisfiesE`): triple expressions.
* `n,τ ⊨ s` (`SatisfiesAt`, `SatisfiesFuel`): a shape expression for a
  node.
* `M,τ ⊨ s` (`SatisfiesMAt`, `SatisfiesMFuel`): a shape expression for a
  set of triples. This relation is new in ShEx with inheritance. `extends`
  needs it.

**Where a `Fuel` parameter is necessary.** In the 2017 version, `typing`
gives the shape of a reference. Thus, `Satisfies` and `Matches` are
well-founded by plain structural recursion on the syntax tree. Here, most
of the rules are also structural:

* Table 1 is structural on the triple expression. (For `.tc`, the use of
  `@z` is a `typing` lookup written inline. Rule 10 of Table 2 has no more
  recursion. This agrees with `te-tpattern` in the 2017 formalization.)
* Table 2 is structural on the shape expression. Rules 11 and 12 use
  Table 3 on `neigh_G(n)`.
* Table 3 is structural on the shape expression, except for one call. In
  rule 18 (`extends X h`), the restriction `restr(x)` of each ancestor `x`
  is a schema lookup. It is not a subterm of the current expression.

The paper proves termination separately (its Lemma 1). The proof uses the
acyclicity of the extension hierarchy `H_S` (Definition 3 and Definition 6).
If there is an extends cycle, the relation does not terminate.

Thus, we use fuel only for the `restr(x)` call:

* `SatisfiesMAt S τ restr` is one layer of Table 3. It is structural, and
  it evaluates each `restr(x)` with the parameter `restr`.
* `SatisfiesMFuel fuel S τ` stacks `fuel + 1` layers. The lowest layer
  evaluates each `restr(x)` as `False`.

Thus, `fuel` counts the depth of nested `restr(x)` evaluations, not the
size of the syntax tree. `Termination.lean` proves that, for an acyclic
`H_S`, the rank bound `S.X.sup S.extRank + 1` is sufficient (Lemma 1), and
defines the real relation `Satisfies` with this bound.
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

/-- `M,τ ⊨ e` (Table 1). It is structural on `e`. -/
def SatisfiesE (τ : Typing) : Finset Triple → TripleExpr → Prop
  -- Rule 1 (`ε`).
  | M, .empty => M = ∅
  -- Rule 2 (`p @z`). `o,τ ⊨ @z` is written inline as `τ.has o z` (rule 10 of
  -- Table 2 has no more recursion, refer to the module docstring).
  | M, .tc p z => ∃ n o, M = {(⟨n, p, o⟩ : Triple)} ∧ τ.has o z
  -- Rule 3 (`e1|e2`).
  | M, .choice e1 e2 => SatisfiesE τ M e1 ∨ SatisfiesE τ M e2
  -- Rule 4 (`e1;e2`).
  | M, .seq e1 e2 =>
      ∃ M1 M2, DisjointUnion M M1 M2 ∧ SatisfiesE τ M1 e1 ∧ SatisfiesE τ M2 e2
  -- Rule 5 (`e1*`).
  | M, .star e =>
      ∃ Ns : List (Finset Triple), DisjointUnionList M Ns ∧ ∀ Ni ∈ Ns, SatisfiesE τ Ni e

/-- `M,τ ⊨ [closed][extra P]⟨e⟩` (rule 17 of Table 3). Rule 18 also uses it,
for the part `M'` that satisfies the shape `h` of `extends X h`. -/
def SatisfiesShape (τ : Typing) (M : Finset Triple) (h : Shape) : Prop :=
  SatisfiesE τ (Me τ M h.triples) h.triples ∧
  props (Mnotin τ M h.triples) ⊆ h.extra.getD ∅ ∧
  (h.closed → props M ⊆ h.triples.props ∪ h.extra.getD ∅)

/-- `M,τ ⊨ s` (Table 3), one layer. It is structural on `s`. The parameter
`restr` evaluates the restriction `restr(x)` of each ancestor in rule 18,
the only call that is not on a subterm. -/
def SatisfiesMAt (S : Schema) (τ : Typing) (restr : Finset Triple → ShapeExpr → Prop) :
    Finset Triple → ShapeExpr → Prop
  -- Rule 13 (`c`).
  | M, .constraint c => c (subjectOf M)
  -- Rule 17 (`[closed][extra P]⟨e⟩`).
  | M, .ofShape h => SatisfiesShape τ M h
  -- Rules 14/15/16 (`or`/`and`/`not`).
  | M, .or s1 s2 => SatisfiesMAt S τ restr M s1 ∨ SatisfiesMAt S τ restr M s2
  | M, .and s1 s2 => SatisfiesMAt S τ restr M s1 ∧ SatisfiesMAt S τ restr M s2
  | M, .not s => ¬ SatisfiesMAt S τ restr M s
  -- Rule 18 (`extends X h`). `M` splits into two types of parts. `M'` satisfies
  -- `h` as a shape (rule 17, with the `closed` and `extra` of `h`). There is one
  -- `Mx x` for each `x ∈ anc(X)`. It satisfies `ext-te(x)`. If there is a
  -- `restr(x)`, the union of the `Mx z` for `z ∈ anc(x)` satisfies `restr(x)`.
  | M, .extends xs h =>
      ∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        SatisfiesShape τ M' h ∧
        (∀ x ∈ S.ancSet xs, SatisfiesE τ (Mx x) (S.shapeDef x).extTe) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          restr ((S.anc x).biUnion Mx) u)

/-- `M,τ ⊨ s` (Table 3), with `fuel + 1` layers of `SatisfiesMAt`. Refer to
the module docstring. -/
def SatisfiesMFuel : (fuel : ℕ) → Schema → Typing → Finset Triple → ShapeExpr → Prop
  | 0, S, τ => SatisfiesMAt S τ (fun _ _ => False)
  | fuel + 1, S, τ => SatisfiesMAt S τ (SatisfiesMFuel fuel S τ)

/-- `n,τ ⊨ s` (Table 2). It is structural on `s`. The parameter `satM`
evaluates Table 3 for rules 11 and 12. -/
def SatisfiesAt (G : Graph) (satM : Finset Triple → ShapeExpr → Prop) (n : RDFNode) :
    ShapeExpr → Prop
  -- Rule 6 (`c`).
  | .constraint c => c n
  -- Rules 11/12 (`[closed][extra P]⟨e⟩` / `extends X h`): the two rules use
  -- the judgment `M,τ ⊨ s` on `neigh_G(n)`, for the same `s`.
  | .ofShape h => satM (neigh G n) (.ofShape h)
  | .extends xs h => satM (neigh G n) (.extends xs h)
  -- Rules 7/8/9 (`or`/`and`/`not`).
  | .or s1 s2 => SatisfiesAt G satM n s1 ∨ SatisfiesAt G satM n s2
  | .and s1 s2 => SatisfiesAt G satM n s1 ∧ SatisfiesAt G satM n s2
  | .not s => ¬ SatisfiesAt G satM n s

/-- `n,τ ⊨ s` (Table 2), with Table 3 at `fuel`. -/
def SatisfiesFuel (fuel : ℕ) (S : Schema) (G : Graph) (τ : Typing) (n : RDFNode)
    (s : ShapeExpr) : Prop :=
  SatisfiesAt G (SatisfiesMFuel fuel S τ) n s

/-- Each `SatisfiesMFuel fuel S τ` is one layer of `SatisfiesMAt`. Thus, a
lemma about `SatisfiesMAt` with any `restr` applies to it. -/
theorem SatisfiesMFuel_eq (fuel : ℕ) (S : Schema) (τ : Typing) :
    ∃ restr, SatisfiesMFuel fuel S τ = SatisfiesMAt S τ restr := by
  cases fuel <;> exact ⟨_, rfl⟩

/-! General lemmas about `Me`, `Mnotin` and `SatisfiesShape`. Many worked
examples use them. -/

/-- Let `Me τ M e = M` (a triple constraint of `e` consumes each triple of
`M`). If `M` satisfies `e` (Table 1), then `M` also satisfies the trivial
shape `[closed:=false][extra:=none]⟨e⟩` (rule 17). `Mnotin` must be empty,
because it is always `⊆ M \ Me = M \ M = ∅`.

The `M'` part of an `extends X h` must satisfy this: `M', τ ⊨ h`
(rule 18). The check is against `h` as a shape, not directly against
`h.triples`. -/
theorem ofShape_of_Me_eq_self {τ : Typing} {M : Finset Triple} {e : TripleExpr}
    (hMe : Me τ M e = M) (hE : SatisfiesE τ M e) :
    SatisfiesShape τ M ⟨false, none, e⟩ := by
  refine ⟨?_, ?_, by simp⟩
  · show SatisfiesE τ (Me τ M e) e
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
`[closed:=false][extra:=none] ⟨p @z⟩` (rule 17). This is the special case
of `ofShape_of_Me_eq_self` that most `.extends` proofs need. -/
theorem singleton_tc_ofShape {τ : Typing} {p : IRI} {z : Label} {n : Subject} {o : RDFNode}
    (hty : τ.has o z) :
    SatisfiesShape τ {(⟨n, p, o⟩ : Triple)} ⟨false, none, .tc p z⟩ := by
  apply ofShape_of_Me_eq_self (e := .tc p z) (M := {(⟨n, p, o⟩ : Triple)})
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

This lemma is necessary to change an obligation `M', τ ⊨ h` (the shape
part of rule 18) back into a `SatisfiesE` fact about `M'`. The reason is
that rule 18 checks `M'` against `h` as a shape, not directly against
`h.triples`. -/
theorem Me_eq_self_of_props_subset {τ : Typing} {M : Finset Triple} {e : TripleExpr}
    (hM : SatisfiesShape τ M ⟨false, none, e⟩) (hsub : props M ⊆ e.props) :
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
