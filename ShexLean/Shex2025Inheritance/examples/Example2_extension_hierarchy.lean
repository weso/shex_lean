import ShexLean.Shex2025Inheritance.examples.Example1_figures
import ShexLean.Shex2025Inheritance.Render
import Example

/-!
Example 2 from the 2025 paper "Shape Expressions with Inheritance"
(§3, Def. 3): `H_{S1}`, the extension hierarchy (Fig. 3) of the
schema `S1` from Example 1 (`Example1_figures.lean`).

The proofs of the ancestor sets (`hancAttribute`, `hancFigure`,
`hancCircle`, `hancColouredFigure`, `hancColour`, `hancRadius` and
`hancSetCircleColouredFigure`) are already in `Example1_figures.lean`.
The reason is that `f1_satisfies_ColouredCircle` of Example 1 needs
`hancSetCircleColouredFigure` to state its rule-18 partition.
This file only shows them again.
-/

namespace Examples

open ShexLean.Inheritance (S_fig1)
open ShexLean.InheritanceCore (ancReach ancSetReach)
open ShexLean (Label)

/-- `{L1, L2, …}`, sorted, for a `Finset Label`.
`ancReach` and `ancSetReach` are computable, but `Schema.anc` and `ancSet` are not.
`ShexLean.Inheritance.ancReach_eq_anc` relates the
two, and the proofs of `Example1_figures.lean` use it. -/
def renderLabels (s : Finset Label) : String :=
  "{" ++ ", ".intercalate (s.sort (· ≤ ·)) ++ "}"

/-- The extension hierarchy `H_{S1}` of Fig. 3, for the schema from Example 1.
Each `anc(...)` line is computed with `renderLabels (ancReach S_fig1 ...)`.
It is not copied by hand.
`ancReach_eq_anc` proves that this is equal to the `S_fig1.anc` and `ancSet`
that `hancAttribute` and the other proofs of `Example1_figures.lean` use. -/
def inheritance2025ExtensionHierarchy : Example where
  name := "inheritance2025-example2-extension-hierarchy"
  summary := "H_S1 (Fig. 3): anc(ColouredCircle) counts Figure one time, not two times."
  schemaText := "(H_S1's edges, from S1's own `extends` targets, Example 1)"
  graphText :=
    "Attribute ← Colour        Figure ← Circle\n" ++
    "Attribute ← Radius        Figure ← ColouredFigure ← ColouredCircle\n" ++
    "                          Figure ← Circle ← ColouredCircle"
  typingText :=
    s!"anc(Attribute) = {renderLabels (ancReach S_fig1 "Attribute")}" ++
      s!"                anc(Figure) = {renderLabels (ancReach S_fig1 "Figure")}\n" ++
    s!"anc(Colour) = {renderLabels (ancReach S_fig1 "Colour")}" ++
      s!"            anc(Circle) = {renderLabels (ancReach S_fig1 "Circle")}\n" ++
    s!"anc(Radius) = {renderLabels (ancReach S_fig1 "Radius")}" ++
      s!"            anc(ColouredFigure) = {renderLabels (ancReach S_fig1 "ColouredFigure")}\n\n" ++
    "anc({Circle, ColouredFigure}) = " ++
      renderLabels (ancSetReach S_fig1 {"Circle", "ColouredFigure"}) ++ "\n" ++
    "— Figure is an ancestor of both f1's parents (Circle, ColouredFigure), but\n" ++
    "counted only once, per rule 18's partition over anc(X)."

end Examples
