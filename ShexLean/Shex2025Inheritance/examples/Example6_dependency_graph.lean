import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2025Inheritance.Stratification
import ShexLean.Shex2025Inheritance.Render
import Example

/-!
Example 6 from the 2025 paper "Shape Expressions with Inheritance" (§4.2,
Def. 5): three small schemas `S1`, `S2` and `S3`, and the facts about
their dependency relations (`dep`, `dep-shape-neg`, `dep-extra-neg` and
`dep-extends`) that Example 7 (`Example7_well_defined.lean`) needs. These
are regression checks on the definitions of the dependency graph.
-/

namespace ShexLean.Inheritance

/-- `S1 = (Y1,∅,def,∅)` (Example 6): `y1 → ⟨p@y2⟩ and ⟨q@y3⟩`,
`y2 → ⟨q@y1⟩`, `y3 → extra{r} ⟨p@y1⟩`.

`shapeDef` is an explicit `if` chain, not `|` pattern matching (as in the
other definitions of this file). The proof of `S1_wellDefined` does a case
split on any label, not only on the three named labels. With the `if`
chain, `simp` can resolve each branch directly. Refer to
`ShexLean/Shex2025Inheritance/Proposition1.lean` for this method. -/
def S1 : Schema where
  Y := {"y1", "y2", "y3"}
  X := ∅
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef z :=
    if z = "y1" then
      .and (.ofShape ⟨false, none, .tc "p" "y2"⟩) (.ofShape ⟨false, none, .tc "q" "y3"⟩)
    else if z = "y2" then .ofShape ⟨false, none, .tc "q" "y1"⟩
    else if z = "y3" then .ofShape ⟨false, some {"r"}, .tc "p" "y1"⟩
    else .constraint (fun _ => False)

/-- `S2 = (Y2,∅,def,∅)` (Example 6): `y4 → ⟨p@y5⟩ or ⟨q@y6⟩`,
`y5 → not ⟨q@y4⟩`, `y6 → extra{p} ⟨p@y4⟩`. -/
def S2 : Schema where
  Y := {"y4", "y5", "y6"}
  X := ∅
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "y4" => .or (.ofShape ⟨false, none, .tc "p" "y5"⟩) (.ofShape ⟨false, none, .tc "q" "y6"⟩)
    | "y5" => .not (.ofShape ⟨false, none, .tc "q" "y4"⟩)
    | "y6" => .ofShape ⟨false, some {"p"}, .tc "p" "y4"⟩
    | _ => .constraint (fun _ => False)

/-- `S3 = (Y3,X3,def,∅)` (Example 6): `x1 → extends _ ⟨p@y7⟩`,
`x2 → extends x1 ⟨p@y8⟩`, `y7 → not ⟨q@x2⟩`, `y8 → c` (a node constraint
of your choice). -/
def S3 : Schema where
  Y := {"y7", "y8"}
  X := {"x1", "x2"}
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "x1" => .extends ∅ ⟨false, none, .tc "p" "y7"⟩
    | "x2" => .extends {"x1"} ⟨false, none, .tc "p" "y8"⟩
    | "y7" => .not (.ofShape ⟨false, none, .tc "q" "x2"⟩)
    | "y8" => .constraint (fun _ => True)
    | _ => .constraint (fun _ => False)

/-! The 13 dependency-relation facts that Example 6 lists (the table of the
paper, page 10). This file checks each of them separately. The
well-definedness results of `Example7_well_defined.lean`
(`S1_wellDefined`, `S2_not_wellDefined` and `S3_not_wellDefined`) need
only some of them as intermediate steps. -/

theorem dep_S1_y1_y2 : S1.dep "y1" "y2" := by
  show "y2" ∈ ((S1.shapeDef "y1").depsAux false).refs; decide
theorem dep_S1_y2_y1 : S1.dep "y2" "y1" := by
  show "y1" ∈ ((S1.shapeDef "y2").depsAux false).refs; decide
theorem dep_S1_y1_y3 : S1.dep "y1" "y3" := by
  show "y3" ∈ ((S1.shapeDef "y1").depsAux false).refs; decide
theorem dep_S1_y3_y1 : S1.dep "y3" "y1" := by
  show "y1" ∈ ((S1.shapeDef "y3").depsAux false).refs; decide

theorem dep_S2_y4_y5 : S2.dep "y4" "y5" := by
  show "y5" ∈ ((S2.shapeDef "y4").depsAux false).refs; decide
theorem dep_S2_y4_y6 : S2.dep "y4" "y6" := by
  show "y6" ∈ ((S2.shapeDef "y4").depsAux false).refs; decide
theorem depShapeNeg_S2_y5_y4 : S2.depShapeNeg "y5" "y4" := by
  show "y4" ∈ ((S2.shapeDef "y5").depsAux false).negRefs; decide
theorem depExtraNeg_S2_y6_y4 : S2.depExtraNeg "y6" "y4" := by
  show "y4" ∈ ((S2.shapeDef "y6").depsAux false).extraNegRefs; decide

theorem dep_S3_x1_y7 : S3.dep "x1" "y7" := by
  show "y7" ∈ ((S3.shapeDef "x1").depsAux false).refs; decide
theorem dep_S3_x2_y8 : S3.dep "x2" "y8" := by
  show "y8" ∈ ((S3.shapeDef "x2").depsAux false).refs; decide
theorem depShapeNeg_S3_y7_x2 : S3.depShapeNeg "y7" "x2" := by
  show "x2" ∈ ((S3.shapeDef "y7").depsAux false).negRefs; decide
theorem depExtends_S3_x1_x2 : S3.depExtends "x1" "x2" := by
  show S3.extEdge "x1" "x2" ∨ S3.extEdge "x2" "x1"
  right; show "x1" ∈ (S3.shapeDef "x2").extendsTargets; decide
theorem depExtends_S3_x2_x1 : S3.depExtends "x2" "x1" := by
  show S3.extEdge "x2" "x1" ∨ S3.extEdge "x1" "x2"
  left; show "x1" ∈ (S3.shapeDef "x2").extendsTargets; decide

/-- The result of `renderDecide`, computed with `native_decide`, for
`S.dep z z'`. `Schema.dep` unfolds to a plain `Finset` or `List`
membership check (`ShapeExpr.depsAux`, structural on the syntax tree, with
no `Classical` and no fuel). Thus, `unfold` and then `infer_instance` are
sufficient to get the `Decidable` instance. This is not true for
`Satisfies*`. -/
def renderDepG (S : Schema) (z z' : Label) : String :=
  renderDecide (show Decidable (S.dep z z') by unfold Schema.dep; infer_instance)

def renderDepShapeNeg (S : Schema) (z z' : Label) : String :=
  renderDecide (show Decidable (S.depShapeNeg z z') by unfold Schema.depShapeNeg; infer_instance)

def renderDepExtraNeg (S : Schema) (z z' : Label) : String :=
  renderDecide (show Decidable (S.depExtraNeg z z') by unfold Schema.depExtraNeg; infer_instance)

def renderDepExtends (S : Schema) (z z' : Label) : String :=
  renderDecide (show Decidable (S.depExtends z z') by unfold Schema.depExtends; infer_instance)

end ShexLean.Inheritance

namespace Examples

open ShexLean.Inheritance (S1 S2 S3 renderDepG renderDepShapeNeg renderDepExtraNeg
  renderDepExtends)

/-- The three schemas `S1`, `S2` and `S3` of Example 6, and their
dependency facts. Each `dep*` claim in `typingText` is a `native_decide`
computation on the real `S1`, `S2` and `S3`. -/
def inheritance2025DependencyGraph : Example where
  name := "inheritance2025-example6-dependency-graph"
  summary := "Dependency-relation facts (dep, dep-shape-neg, dep-extends) of S1, S2 and S3."
  schemaText :=
    "S1: y1 → ⟨p@y2⟩ and ⟨q@y3⟩       S2: y4 → ⟨p@y5⟩ or ⟨q@y6⟩       S3: x1 → extends _ ⟨p@y7⟩\n" ++
    "    y2 → ⟨q@y1⟩                     y5 → not ⟨q@y4⟩                 x2 → extends x1 ⟨p@y8⟩\n" ++
    "    y3 → extra{r} ⟨p@y1⟩             y6 → extra{p} ⟨p@y4⟩            y7 → not ⟨q@x2⟩\n" ++
    "                                                                     y8 → c  (some constraint)"
  graphText := "(Example 6 is purely about the dependency graph, no RDF graph of its own.)"
  typingText :=
    s!"dep_S1(y1,y2) = {renderDepG S1 "y1" "y2"}, dep_S1(y2,y1) = {renderDepG S1 "y2" "y1"}, " ++
      s!"dep_S1(y1,y3) = {renderDepG S1 "y1" "y3"}, dep_S1(y3,y1) = {renderDepG S1 "y3" "y1"}\n" ++
    s!"dep_S2(y4,y5) = {renderDepG S2 "y4" "y5"}, dep_S2(y4,y6) = {renderDepG S2 "y4" "y6"}, " ++
      s!"dep-shape-neg_S2(y5,y4) = {renderDepShapeNeg S2 "y5" "y4"}, " ++
      s!"dep-extra-neg_S2(y6,y4) = {renderDepExtraNeg S2 "y6" "y4"}\n" ++
    s!"dep_S3(x1,y7) = {renderDepG S3 "x1" "y7"}, dep_S3(x2,y8) = {renderDepG S3 "x2" "y8"}, " ++
      s!"dep-shape-neg_S3(y7,x2) = {renderDepShapeNeg S3 "y7" "x2"}\n" ++
    s!"dep-extends_S3(x1,x2) = {renderDepExtends S3 "x1" "x2"}, " ++
      s!"dep-extends_S3(x2,x1) = {renderDepExtends S3 "x2" "x1"} (dep-extends is symmetrized)"

end Examples
