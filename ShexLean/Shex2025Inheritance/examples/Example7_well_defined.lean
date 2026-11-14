import ShexLean.Shex2025Inheritance.examples.Example6_dependency_graph
import Example

/-!
Example 7 from the 2025 paper "Shape Expressions with Inheritance" (§4.2,
Def. 6): the well-definedness results for `S1`, `S2` and `S3` of
Example 6 (`Example6_dependency_graph.lean`). The checks use Definition 6
(`Schema.WellDefined`, in
`ShexLean/Shex2025Inheritance/Stratification.lean`).

* `S1` is well-defined. Its only cycles, `y1↔y2` and `y1,y3`, have no
  negative dependency.
* `S2` is not well-defined. The cycle `y4,y5` has the negative dependency
  `dep-shape-neg(y5,y4)`.
* `S3` is not well-defined. The cycle `y7,x2,x1` has the negative
  dependency `dep-shape-neg(y7,x2)`. This cycle needs `dep-extends`
  (made symmetric) to go from `x2` back to `x1`.

Without the `dep-extends` relation, the cycle in `S3` does not exist. This
shows that you cannot mix extension and negation in all possible ways.
-/

namespace ShexLean.Inheritance

open ShexLean.InheritanceCore hiding Schema

/-- `S1` is well-defined (Example 7). `H_{S1}` is trivially acyclic
(`X1 = ∅`), and `S1` has no negative dependency for any pair of labels:

* The `extra {r}` of `y3` never matches the predicate `p` of its triple
  constraint `p @y1`. Thus, `dep-extra-neg` never applies.
* `S1` has no `not`. Thus, `dep-shape-neg` also never applies. (This is
  also true for each label outside `{y1,y2,y3}`, whose `shapeDef` is
  `.constraint (fun _ => False)`, which has no references.) -/
theorem S1_wellDefined : S1.WellDefined := by
  refine ⟨?_, ?_⟩
  · have hX : S1.X = (∅ : Finset Label) := rfl
    intro x hx; rw [hX] at hx; exact absurd hx (Finset.notMem_empty x)
  · rintro ⟨a, b, hDNeg, -⟩
    have hnoNeg : ∀ z z', ¬ S1.depShapeNeg z z' ∧ ¬ S1.depExtraNeg z z' := by
      intro z z'
      have hshape : S1.shapeDef z =
          (if z = "y1" then
            .and (.ofShape ⟨false, none, .tc "p" "y2"⟩) (.ofShape ⟨false, none, .tc "q" "y3"⟩)
          else if z = "y2" then .ofShape ⟨false, none, .tc "q" "y1"⟩
          else if z = "y3" then .ofShape ⟨false, some {"r"}, .tc "p" "y1"⟩
          else .constraint (fun _ => False)) := rfl
      unfold Schema.depShapeNeg Schema.depExtraNeg
      rw [hshape]
      by_cases hz1 : z = "y1"
      · simp [hz1, ShapeExpr.depsAux, Shape.depInfo, TripleExpr.tcs]
      · by_cases hz2 : z = "y2"
        · simp [hz2, ShapeExpr.depsAux, Shape.depInfo, TripleExpr.tcs]
        · by_cases hz3 : z = "y3"
          · simp [hz3, ShapeExpr.depsAux, Shape.depInfo, TripleExpr.tcs, Finset.mem_singleton,
              Finset.mem_filter, Prod.mk.injEq]
          · simp [hz1, hz2, hz3, ShapeExpr.depsAux]
    exact hDNeg.elim (hnoNeg a b).1 (hnoNeg a b).2

/-- `S2` is not well-defined (Example 7). The cycle `y4, y5` has the
negative dependency `dep-shape-neg(y5,y4)` (`y5 = not ⟨q@y4⟩`). `y4` goes
back to `y5` directly through `dep(y4,y5)` (the disjunct `⟨p@y5⟩` of
`y4`). -/
theorem S2_not_wellDefined : ¬ S2.WellDefined := by
  rintro ⟨-, hNC⟩
  apply hNC
  have hy5shape : S2.shapeDef "y5" = .not (.ofShape ⟨false, none, .tc "q" "y4"⟩) := rfl
  have hy4shape : S2.shapeDef "y4" =
      .or (.ofShape ⟨false, none, .tc "p" "y5"⟩) (.ofShape ⟨false, none, .tc "q" "y6"⟩) := rfl
  refine ⟨"y5", "y4", Or.inl ?_, Relation.ReflTransGen.single (Or.inl ?_)⟩
  · show "y4" ∈ ((S2.shapeDef "y5").depsAux false).negRefs
    rw [hy5shape]; decide
  · show "y5" ∈ ((S2.shapeDef "y4").depsAux false).refs
    rw [hy4shape]; decide

/-- `S3` is not well-defined (Example 7). The cycle `y7, x2, x1` has the
negative dependency `dep-shape-neg(y7,x2)` (`y7 = not ⟨q@x2⟩`). `x2` goes
back to `y7` through `dep-extends(x2,x1)` (`x2 extends x1`, made
symmetric) and then `dep(x1,y7)` (the `⟨p@y7⟩` of `x1`). The paper says
that the cycle does not exist without the `dep-extends` relation. -/
theorem S3_not_wellDefined : ¬ S3.WellDefined := by
  rintro ⟨-, hNC⟩
  apply hNC
  have hy7shape : S3.shapeDef "y7" = .not (.ofShape ⟨false, none, .tc "q" "x2"⟩) := rfl
  have hx1shape : S3.shapeDef "x1" = .extends ∅ ⟨false, none, .tc "p" "y7"⟩ := rfl
  have hx2shape : S3.shapeDef "x2" = .extends {"x1"} ⟨false, none, .tc "p" "y8"⟩ := rfl
  refine ⟨"y7", "x2", Or.inl ?_, ?_⟩
  · show "x2" ∈ ((S3.shapeDef "y7").depsAux false).negRefs
    rw [hy7shape]; decide
  · have step1 : S3.DEdge "x2" "x1" := Or.inr (Or.inl (by
      show S3.extEdge "x2" "x1"
      unfold Schema.extEdge; rw [hx2shape]; simp [ShapeExpr.extendsTargets]))
    have step2 : S3.DEdge "x1" "y7" := Or.inl (by
      show "y7" ∈ ((S3.shapeDef "x1").depsAux false).refs
      rw [hx1shape]; decide)
    exact Relation.ReflTransGen.head step1 (Relation.ReflTransGen.single step2)

end ShexLean.Inheritance

namespace Examples

open ShexLean.Inheritance (S1 S2 S3 renderDepG renderDepShapeNeg renderDepExtends)

/-- The well-definedness results of Example 7 for `S1`, `S2` and `S3`.

`Schema.WellDefined` is `ExtAcyclic ∧ ¬NegCycle`. Its negative part is an
unbounded existential over `ReflTransGen` reachability. It has no
`Decidable` instance in this formalization. This is the same as
`StratifiedNegation` of 2017
(`ShexLean.Shex2017Schemas.examples.Example5_stratification`).

Thus, the three main results still give the names of the theorems that
are their witnesses (`S1_wellDefined`, `S2_not_wellDefined` and
`S3_not_wellDefined`). But each sub-fact that a proof uses (`dep`,
`dep-shape-neg` and `dep-extends`) is a `renderDecide` computation, with
`renderDepG`, `renderDepShapeNeg` and `renderDepExtends` of Example 6. -/
def inheritance2025WellDefined : Example where
  name := "inheritance2025-example7-well-defined"
  summary := "Well-definedness results (Def. 6) for S1, S2 and S3 of Example 6."
  schemaText := "(S1/S2/S3 as in inheritance2025-example6-dependency-graph)"
  graphText := "(Example 7 is purely about well-definedness, no RDF graph of its own.)"
  typingText :=
    "S1 is well-defined (`S1_wellDefined`): its cycles (y1↔y2, y1,y3) carry no\n" ++
    "  negative dependency — S1.X = ∅ (ExtAcyclic trivial), and no dep-shape-neg/\n" ++
    "  dep-extra-neg pair exists at all (checked for every label pair in the proof).\n\n" ++
    s!"S2 is not well-defined (`S2_not_wellDefined`): dep-shape-neg(y5,y4) = " ++
      s!"{renderDepShapeNeg S2 "y5" "y4"} and dep(y4,y5) = {renderDepG S2 "y4" "y5"}\n" ++
    "  — the cycle y4,y5 carries the negative dependency y5 = not ⟨q@y4⟩.\n\n" ++
    s!"S3 is not well-defined (`S3_not_wellDefined`): dep-shape-neg(y7,x2) = " ++
      s!"{renderDepShapeNeg S3 "y7" "x2"}, dep-extends(x2,x1) = " ++
      s!"{renderDepExtends S3 "x2" "x1"}, dep(x1,y7) = {renderDepG S3 "x1" "y7"}\n" ++
    "  — the cycle y7,x2,x1 only closes via dep-extends(x2,x1): it would not exist\n" ++
    "    without the extends relation."

end Examples
