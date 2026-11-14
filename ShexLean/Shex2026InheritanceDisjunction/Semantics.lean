import ShexLean.Shex2026InheritanceDisjunction.Stratification
import ShexLean.Common.DisjointUnion
import ShexLean.InheritanceCore.TripleMatch

/-!
Tables 1–3 (§4.1) of the 2025 paper "Shape Expressions with Inheritance".
Here, rule 18 (`extends`) has a more general form: it accepts a
disjunction of shapes. Refer to the module docstring of `Syntax.lean` for
the background of §6 and for the design with `hs : List Shape`.

All the definitions here are the same as in
`ShexLean/Shex2025Inheritance/Semantics.lean`, *except* rule 18 (the
`.extends` case of `SatisfiesMAt`). Refer to that case below for the
change: one more existential witness, `pick`. Its comment tells why one
witness, shared by the full `S.ancSet xs` of one `.extends` occurrence, is
exactly the fix that §6 describes ("(1) record which disjunct... (2) check
all subtypes agree").

The three relations:

* `M,τ ⊨ e` (`SatisfiesE`, `ShexLean/InheritanceCore/TripleMatch.lean`):
  triple expressions.
* `n,τ ⊨ s` (`SatisfiesAt`, `SatisfiesFuel`): a shape expression for a
  node.
* `M,τ ⊨ s` (`SatisfiesMAt`, `SatisfiesMFuel`): a shape expression for a
  set of triples.

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

* `SatisfiesMAt S τ evalRestr` is one layer of Table 3. It is structural, and
  it evaluates each `restr(x)` with the parameter `evalRestr`.
* `SatisfiesMFuel fuel S τ` stacks `fuel + 1` layers. The lowest layer
  evaluates each `restr(x)` as `False`.

Thus, `fuel` counts the depth of nested `restr(x)` evaluations, not the
size of the syntax tree. `Termination.lean` proves that, for an acyclic
`H_S`, the rank bound `S.X.sup S.extRank + 1` is sufficient (Lemma 1), and
defines the real relation `Satisfies` with this bound.
-/

namespace ShexLean.InheritanceDisjunction

open ShexLean.InheritanceCore hiding Schema

/-- `M,τ ⊨ s` (Table 3), one layer. It is structural on `s`. The parameter
`evalRestr` evaluates the restriction `restr(x)` of each ancestor in rule 18,
the only call that is not on a subterm. -/
def SatisfiesMAt (S : Schema) (τ : Typing) (evalRestr : Finset Triple → ShapeExpr → Prop) :
    Finset Triple → ShapeExpr → Prop
  -- Rule 13 (`c`).
  | M, .constraint c => c (subjectOf M)
  -- Rule 17 (`[closed][extra P]⟨e⟩`).
  | M, .ofShape h => SatisfiesShape τ M h
  -- Rules 14/15/16 (`or`/`and`/`not`).
  | M, .or s1 s2 => SatisfiesMAt S τ evalRestr M s1 ∨ SatisfiesMAt S τ evalRestr M s2
  | M, .and s1 s2 => SatisfiesMAt S τ evalRestr M s1 ∧ SatisfiesMAt S τ evalRestr M s2
  | M, .not s => ¬ SatisfiesMAt S τ evalRestr M s
  -- Rule 18 (`extends X hs`, a general form of `extends X h` of the paper).
  -- `M` splits into two types of parts. `M'` satisfies *one* disjunct of `hs`
  -- as a shape (rule 17, with the `closed` and `extra` of that disjunct). This
  -- part alone has no ambiguity, because the plain `or` of rule 14 already lets
  -- one node select a disjunct. There is one `Mx x` for each `x ∈ anc(X)`. It
  -- satisfies `ext-te(x)`. If there is a `restr(x)`, the union of the `Mx z` for
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
  | M, .extends xs hs =>
      ∃ M' Mx, ∃ pick : Label → ℕ, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        (∃ h ∈ hs, SatisfiesShape τ M' h) ∧
        (∀ x ∈ S.ancSet xs, SatisfiesE τ (Mx x) ((S.shapeDef x).extTeAt (pick x))) ∧
        (∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u →
          evalRestr ((S.anc x).biUnion Mx) u)

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
  -- Rules 11/12 (`[closed][extra P]⟨e⟩` / `extends X hs`): the two rules use
  -- the judgment `M,τ ⊨ s` on `neigh_G(n)`, for the same `s`.
  | .ofShape h => satM (neigh G n) (.ofShape h)
  | .extends xs hs => satM (neigh G n) (.extends xs hs)
  -- Rules 7/8/9 (`or`/`and`/`not`).
  | .or s1 s2 => SatisfiesAt G satM n s1 ∨ SatisfiesAt G satM n s2
  | .and s1 s2 => SatisfiesAt G satM n s1 ∧ SatisfiesAt G satM n s2
  | .not s => ¬ SatisfiesAt G satM n s

/-- `n,τ ⊨ s` (Table 2), with Table 3 at `fuel`. -/
def SatisfiesFuel (fuel : ℕ) (S : Schema) (G : Graph) (τ : Typing) (n : RDFNode)
    (s : ShapeExpr) : Prop :=
  SatisfiesAt G (SatisfiesMFuel fuel S τ) n s

/-- Each `SatisfiesMFuel fuel S τ` is one layer of `SatisfiesMAt`. Thus, a
lemma about `SatisfiesMAt` with any `evalRestr` applies to it. -/
theorem SatisfiesMFuel_eq (fuel : ℕ) (S : Schema) (τ : Typing) :
    ∃ evalRestr, SatisfiesMFuel fuel S τ = SatisfiesMAt S τ evalRestr := by
  cases fuel <;> exact ⟨_, rfl⟩

end ShexLean.InheritanceDisjunction
