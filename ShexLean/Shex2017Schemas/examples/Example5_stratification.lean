import ShexLean.Shex2017Schemas.Semantics
import ShexLean.Shex2017Schemas.Stratification
import ShexLean.Shex2017Schemas.Render
import Example

/-!
Example 5 from Boneva, Labra Gayo, Prud'hommeaux (2017), illustrating
Definition 3 ("schema with stratified negation",
`ShexLean.Stratification.Schema.StratNeg`) on a schema that mixes
`NOT` and recursion, but *is* stratified (unlike `S₂` from Example 4,
`Examples.NegationRecursion`).

```
<L1> → NOT(ex:a @<L2> ; ex:b @<Str>)      <L3> → ex:c @<L2>
<L2> → ex:c @<L3>                         <Str> → xsd:string
```

> The dependency graph contains the edges `dep⁻(<L1>,<L2>)`,
> `dep⁻(<L1>,<Str>)`, `dep⁺(<L2>,<L3>)`, `dep⁺(<L3>,<L2>)`. The unique loop
> is around `<L2>` and `<L3>` and it goes through positive dependencies
> only, so the schema is stratified. [...] One possible stratification is
> `<L1>` on stratum 2 and the other three shape labels on stratum 1.

Example 5 introduces no RDF graph of its own (it is purely about Definition
3); a graph exercising `S₃` appears later, in Example 6 (§4.2 of the paper),
which is out of scope here.
-/

namespace Examples.StratificationExample

open ShexLean

private abbrev L1  : Label := "L1"
private abbrev L2  : Label := "L2"
private abbrev L3  : Label := "L3"
private abbrev Str : Label := "Str"

private abbrev a : IRI := "ex:a"
private abbrev b : IRI := "ex:b"
private abbrev c : IRI := "ex:c"

/-- `<L1> → NOT(ex:a @<L2> ; ex:b @<Str>)`. -/
private abbrev L1Def : ShExpr :=
  .not (.neigDescr (.eachOf (.tPattern {a} L2) (.tPattern {b} Str)))

/-- `<L2> → ex:c @<L3>`. -/
private abbrev L2Def : ShExpr := .neigDescr (.tPattern {c} L3)

/-- `<L3> → ex:c @<L2>`. -/
private abbrev L3Def : ShExpr := .neigDescr (.tPattern {c} L2)

/-- `<Str> → xsd:string`, stood in (as elsewhere, e.g. `ShexLean.Examples`)
by a placeholder literal, since Example 5 has no accompanying graph to
size the set against. -/
private abbrev StrDef : ShExpr := .valueDescr {.lit (.str "placeholder")}

/-- The schema `S₃` from Example 5. Written with an explicit `if`-chain
(rather than the `|`-pattern style used elsewhere) so that `S₃.shapeDef`'s
case split is directly available to `simp` in the proofs below. -/
abbrev S₃ : Schema where
  labels := {L1, L2, L3, Str}
  shapeDef := fun L =>
    if L = L1 then L1Def
    else if L = L2 then L2Def
    else if L = L3 then L3Def
    else StrDef

private theorem shapeDef_L1 : S₃.shapeDef L1 = L1Def := by simp

private theorem shapeDef_L2 : S₃.shapeDef L2 = L2Def := by simp [L1, L2]

private theorem shapeDef_L3 : S₃.shapeDef L3 = L3Def := by simp [L1, L2, L3]

private theorem shapeDef_other (L : Label) (h1 : L ≠ L1) (h2 : L ≠ L2) (h3 : L ≠ L3) :
    S₃.shapeDef L = StrDef := by simp [h1, h2, h3]

/-- `dep⁻(<L1>, <L2>)`. -/
theorem depNeg_L1_L2 : DepNeg S₃ L1 L2 := by rw [DepNeg, shapeDef_L1]; decide

/-- `dep⁻(<L1>, <Str>)`. -/
theorem depNeg_L1_Str : DepNeg S₃ L1 Str := by rw [DepNeg, shapeDef_L1]; decide

/-- `dep⁺(<L2>, <L3>)`. -/
theorem depPos_L2_L3 : DepPos S₃ L2 L3 := by rw [DepPos, shapeDef_L2]; decide

/-- `dep⁺(<L3>, <L2>)`. -/
theorem depPos_L3_L2 : DepPos S₃ L3 L2 := by rw [DepPos, shapeDef_L3]; decide

/-- The stratification from the paper: `<L1>` on stratum 2, the other three
labels on stratum 1. -/
private def strat1 : Label → ℕ := fun L => if L = L1 then 2 else 1

/-- `S₃` is with stratified negation (Definition 3), witnessed by `strat1`. -/
theorem S₃_stratified : S₃.StratNeg := by
  refine ⟨2, strat1, ?_, ?_, ?_⟩
  · intro L hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with hL | hL | hL | hL <;> subst hL <;> simp [strat1, L1, L2, L3, Str]
  · intro L1' _ L2' hdep
    by_cases h1 : L1' = L1
    · subst h1
      rw [DepNeg, shapeDef_L1] at hdep
      simp [ShExpr.negDeps, TExpr.depsAux] at hdep
      rcases hdep with hdep | hdep <;> subst hdep <;> simp [strat1, L1, L2, Str]
    · by_cases h2 : L1' = L2
      · subst h2
        rw [DepNeg, shapeDef_L2] at hdep
        simp [ShExpr.negDeps, ShExpr.depsAux, TExpr.depsAux] at hdep
      · by_cases h3 : L1' = L3
        · subst h3
          rw [DepNeg, shapeDef_L3] at hdep
          simp [ShExpr.negDeps, ShExpr.depsAux, TExpr.depsAux] at hdep
        · rw [DepNeg, shapeDef_other L1' h1 h2 h3] at hdep
          simp [ShExpr.negDeps] at hdep
  · intro L1' _ L2' hdep
    by_cases h1 : L1' = L1
    · subst h1
      rw [DepPos, shapeDef_L1] at hdep
      simp [ShExpr.posDeps, TExpr.depsAux] at hdep
    · by_cases h2 : L1' = L2
      · subst h2
        rw [DepPos, shapeDef_L2] at hdep
        simp [ShExpr.posDeps, ShExpr.depsAux, TExpr.depsAux] at hdep
        subst hdep; simp [strat1, L1, L2, L3]
      · by_cases h3 : L1' = L3
        · subst h3
          rw [DepPos, shapeDef_L3] at hdep
          simp [ShExpr.posDeps, ShExpr.depsAux, TExpr.depsAux] at hdep
          subst hdep; simp [strat1, L1, L2, L3]
        · rw [DepPos, shapeDef_other L1' h1 h2 h3] at hdep
          simp [ShExpr.posDeps] at hdep

end Examples.StratificationExample

namespace Examples

open Examples.StratificationExample (S₃ L1 L2 L3 Str)
open ShexLean (Schema.render renderDecide DepNeg DepPos)

/-- Example 5: `S₃` mixes `NOT` and recursion but is with stratified
negation. `schemaText` generated from the real `S₃`; the four dependency
edges are each a genuine `Decidable` (`DepNeg`/`DepPos`) computation.
`S₃.StratNeg` itself (`Nonempty (Stratification S₃)`) isn't
decidable — same reason as Example 4 — so that claim still names the
witnessing theorem/stratification. -/
def stratificationExample : Example where
  name := "schemas2017-example5-stratification"
  summary := "NOT + recursion, with stratified negation."
  schemaText := Schema.render S₃
  graphText :=
    "(none — Example 5 illustrates Definition 3 on the schema alone;\n" ++
    " a graph for S₃ appears later, in Example 6.)"
  typingText :=
    s!"dep⁻(<L1>,<L2>) = {renderDecide (inferInstance : Decidable (DepNeg S₃ L1 L2))}, " ++
      s!"dep⁻(<L1>,<Str>) = {renderDecide (inferInstance : Decidable (DepNeg S₃ L1 Str))}\n" ++
    s!"dep⁺(<L2>,<L3>) = {renderDecide (inferInstance : Decidable (DepPos S₃ L2 L3))}, " ++
      s!"dep⁺(<L3>,<L2>) = {renderDecide (inferInstance : Decidable (DepPos S₃ L3 L2))}\n" ++
    "⇒ S₃ IS with stratified negation (`S₃_stratified`, witnessed by " ++
    "`strat1`: <L1> on stratum 2, the rest on stratum 1)."

end Examples
