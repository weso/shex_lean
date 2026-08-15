import ShexLean.Shex2025Inheritance.Syntax
import ShexLean.Common.DisjointUnion

/-!
Tables 1–3 (§4.1) of the 2025 "Shape Expressions with Inheritance" paper:
the three mutually-recursive satisfiability relations `M,τ ⊨ e`
(`SatisfiesEFuel`, triple expressions), `n,τ ⊨ s` (`SatisfiesFuel`, a shape
expression under a node), and `M,τ ⊨ s` (`SatisfiesMFuel`, a shape
expression under a set of triples — new for ShEx with inheritance, needed
for `extends`).

**Why "mutually recursive" here needs a `Fuel` parameter, unlike the 2017
formalization.** In `ShexLean/Shex2017Schemas/Semantics.lean`, a shape *reference* is
resolved purely by consulting `typing` (Rule te-tpattern: `typing.has obj
L`, no recursive call into `def(L)`), so `Satisfies`/`Matches` are
well-founded by plain structural recursion on the finite AST. Here, Table
3's rule 18 (`extends X h`) genuinely recurses into *other labels' own
definitions* (`ext-te(x)`/`restr(x)` = `(S.shapeDef x).extTe`/`.restrOf`,
for `x` ranging over ancestors) — a schema lookup, not a subterm of the
current expression. The paper itself has to prove this terminates
separately (its own Lemma 1), via a call-tree argument that uses
acyclicity of the extension hierarchy `H_S` (Definition 3/6).

So a plain structurally-recursive Lean definition of `Satisfies` is not
just inconvenient here, it is actually false in general (an
extends-cycle — `H_S` not acyclic — makes the relation genuinely
non-terminating). The honest way to get a *total* Lean function first,
before separately proving the real (paper's) Lemma 1, is the standard
fuel idiom already used in `ShexLean/Shex2017Schemas/Algorithm1.lean`/`Algorithm2.lean`
for similar well-founded-but-not-structural recursions: thread an explicit
`Fuel : ℕ` argument through all three relations, decremented on *every*
recursive call (not just extends-hops — this makes termination trivial,
literally `Nat`-structural recursion on `Fuel`, at the cost of `Fuel`
being a conservative/pessimistic step-counter), and return `False` when
`Fuel` runs out.

`SatisfiesFuel`/`SatisfiesMFuel`/`SatisfiesEFuel` are consequently *not*
the paper's real relations yet — they are a fuel-bounded
under-approximation of them, total by construction. Establishing that a
canonical, concrete fuel bound makes them agree with the paper's real
(fuel-independent) relations, for well-defined schemas, is exactly the
content of the paper's own Lemma 1 and is deferred to a follow-up
`Termination.lean`, matching the incremental-porting plan.

**Why the three relations don't need Lean's `mutual` keyword despite the
paper presenting them as mutually recursive.** Tracing the actual call
graph: Table 1 (`SatisfiesEFuel`) only calls itself (`.tc`'s use of `@z` is
inlined as a `typing` lookup — Table 2's own rule 10, `@z: (n,z) ∈ τ`, has
zero further recursion, exactly like `te-tpattern` in the 2017
formalization, so there is nothing to gain from routing it through a
genuine mutual call). Table 3 (`SatisfiesMFuel`) calls itself and Table 1,
but never Table 2. Table 2 (`SatisfiesFuel`) calls itself and Table 3, but
Table 3/1 never call back into Table 2. So the true dependency order is a
strict chain `SatisfiesEFuel → SatisfiesMFuel → SatisfiesFuel`, and each
can be defined as an ordinary (non-mutual) `Fuel`-decreasing recursive
`def`, in that order.
-/

namespace ShexLean.Inheritance

/-- `subject(M)`: the (paper: unique, by `M` being a genuine neighbourhood
set) common subject of a nonempty set of triples `M`. Classically chosen;
junk value (`.iri ""`) on `M = ∅`, where the paper's own notion is not
defined either (Table 3's rule 13 is only ever exercised with `M` an
actual node's neighbourhood). -/
noncomputable def subjectOf (M : Finset Triple) : RDFNode :=
  if h : M.Nonempty then h.choose.subj else RDFNode.iri ""

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

/-- `M = M' ⊎ (⊎_{x ∈ Idx} Mx)`: `M'` and the finitely many `Mx x` (for
`x ∈ Idx`) are pairwise disjoint and their union is `M` — Table 3's rule
18 partition of a neighbourhood set into the portion satisfying `h` and
one portion per ancestor being (transitively) extended. -/
def DisjointUnionOn (M M' : Finset Triple) (Idx : Finset ShapeLabel)
    (Mx : ShapeLabel → Finset Triple) : Prop :=
  Disjoint M' (Idx.biUnion Mx) ∧ (Idx : Set ShapeLabel).PairwiseDisjoint Mx ∧
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
  -- Rule 18 (`extends X h`): `M` splits into `M'` (satisfying `h`) and one
  -- `Mx x` per `x ∈ anc(X)` (satisfying `ext-te(x)`, and — if `restr(x)`
  -- is present — the union of `Mx z` over `z ∈ anc(x)` satisfies
  -- `restr(x)`).
  | fuel+1, S, G, τ, M, .extends xs h =>
      ∃ M' Mx, DisjointUnionOn M M' (S.ancSet xs) Mx ∧
        SatisfiesEFuel fuel S G τ M' h.triples ∧
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

end ShexLean.Inheritance
