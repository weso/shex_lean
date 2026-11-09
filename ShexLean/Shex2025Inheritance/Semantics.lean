import ShexLean.Shex2025Inheritance.Syntax
import ShexLean.Common.DisjointUnion
import ShexLean.InheritanceCore.TripleMatch

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

open ShexLean.InheritanceCore

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

end ShexLean.Inheritance
