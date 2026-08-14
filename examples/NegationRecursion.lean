import ShexLean.Semantics
import ShexLean.Stratification
import Example

/-!
Example 4 from Boneva, Labra Gayo, Prud'hommeaux (2017), used to show that
correct typings (Definition 2) alone are not enough to give a sound
semantics once negation is mixed with recursion, and that the schema below
is (as claimed right after Ex. 4) *not* with stratified negation
(Definition 3, `ShexLean.Stratification`).

```
<L1> → NOT(ex:p @<L2>)      <n1> ex:p <n2> .
<L2> → NOT(ex:p @<L1>)      <n2> ex:p <n1> .
```

> These two typings of `G₂` by `S₂` are both correct: `typing₅ =
> {(<n1>, <L1>)}` and `typing₆ = {(<n2>, <L2>)}`.
> [...] `S₂` from Ex. 4 is not with stratified negation because
> `dep⁻(<L1>, <L2>)` and `dep⁻(<L2>, <L1>)`.
-/

namespace Examples.NegationRecursion

open ShexLean

@[reducible] private def n1 : RDFNode := .iri "n1"
@[reducible] private def n2 : RDFNode := .iri "n2"

@[reducible] private def p : IRI := "ex:p"

@[reducible] private def t1 : Triple := ⟨n1, p, n2⟩
@[reducible] private def t2 : Triple := ⟨n2, p, n1⟩

/-- The graph `G₂` from Example 4. -/
def G₂ : Graph := {t1, t2}

@[reducible] private def L1 : ShapeLabel := "L1"
@[reducible] private def L2 : ShapeLabel := "L2"

/-- `<L1> → NOT(ex:p @<L2>)`. -/
@[reducible] private def L1Def : ShapeExpr := .not (.neigDescr (.tPattern {p} L2))

/-- `<L2> → NOT(ex:p @<L1>)`. -/
@[reducible] private def L2Def : ShapeExpr := .not (.neigDescr (.tPattern {p} L1))

/-- The schema `S₂` from Example 4. -/
@[reducible] def S₂ : Schema where
  labels := {L1, L2}
  shapeDef
    | "L1" => L1Def
    | _ => L2Def

/-- `typing₅` from Example 4. -/
def typing5 : Typing := {(n1, L1)}

/-- `typing₆` from Example 4. -/
def typing6 : Typing := {(n2, L2)}

private theorem neigh_n1 : neigh G₂ n1 = {t1} := by decide
private theorem neigh_n2 : neigh G₂ n2 = {t2} := by decide

/-- `typing₅` is a correct typing of `G₂` by `S₂` (Definition 2): `<n1>`
satisfies `<L1>` because the only way it could fail to (having a `<L2>`
neighbour via `ex:p`) is not witnessed by `typing₅`. -/
theorem typing5_correct :
    ∀ n L, (n, L) ∈ typing5 → Satisfies G₂ typing5 n (S₂.shapeDef L) := by
  intro n L hmem
  simp only [typing5, Finset.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨hn, hL⟩ := hmem
  subst hn; subst hL
  show ¬ Matches G₂ typing5 (neigh G₂ n1) (.tPattern {p} L2)
  rw [neigh_n1]
  rintro ⟨subj, pred, obj, hEq, -, htyp⟩
  have ht : t1 = (⟨subj, pred, obj⟩ : Triple) := Finset.singleton_inj.mp hEq
  injection ht with hsubj hpred hobj
  exact absurd (hobj ▸ htyp) (by decide)

/-- `typing₆` is a correct typing of `G₂` by `S₂` (Definition 2), symmetric
to `typing5_correct`. -/
theorem typing6_correct :
    ∀ n L, (n, L) ∈ typing6 → Satisfies G₂ typing6 n (S₂.shapeDef L) := by
  intro n L hmem
  simp only [typing6, Finset.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨hn, hL⟩ := hmem
  subst hn; subst hL
  show ¬ Matches G₂ typing6 (neigh G₂ n2) (.tPattern {p} L1)
  rw [neigh_n2]
  rintro ⟨subj, pred, obj, hEq, -, htyp⟩
  have ht : t2 = (⟨subj, pred, obj⟩ : Triple) := Finset.singleton_inj.mp hEq
  injection ht with hsubj hpred hobj
  exact absurd (hobj ▸ htyp) (by decide)

/-- `S₂` is not with stratified negation (Definition 3): `dep⁻(<L1>, <L2>)`
and `dep⁻(<L2>, <L1>)` would force `strat(<L1>) > strat(<L2>) > strat(<L1>)`,
which is impossible. -/
theorem S₂_not_stratified : ¬ S₂.StratifiedNegation := by
  rintro ⟨strat⟩
  have hdepL1L2 : DepNeg S₂ L1 L2 := by decide
  have hdepL2L1 : DepNeg S₂ L2 L1 := by decide
  have h1 := strat.neg_strict L1 L2 hdepL1L2
  have h2 := strat.neg_strict L2 L1 hdepL2L1
  omega

end Examples.NegationRecursion

namespace Examples

/-- Example 4: negation mixed with recursion, showing correct typings are
not enough for a sound semantics, and `S₂` is not with stratified negation. -/
def negationRecursion : Example where
  name := "negation-recursion"
  summary :=
    "Example 4: NOT and mutual recursion give two contradicting correct " ++
    "typings; the schema is not stratified."
  schemaText :=
    "<L1> → NOT(ex:p @<L2>)\n" ++
    "<L2> → NOT(ex:p @<L1>)"
  graphText :=
    "<n1> ex:p <n2> .\n" ++
    "<n2> ex:p <n1> ."
  typingText :=
    "typing₅ = {(<n1>, <L1>)}    (correct)\n" ++
    "typing₆ = {(<n2>, <L2>)}    (also correct, and contradicts typing₅)\n" ++
    "S₂ is NOT with stratified negation (dep⁻(<L1>,<L2>) and dep⁻(<L2>,<L1>))."

end Examples
