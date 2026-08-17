import ShexLean.Shex2025Inheritance.examples.Example1_figures
import ShexLean.Shex2025Inheritance.Render
import Example

/-!
Example 2 from the 2025 "Shape Expressions with Inheritance" paper (§3,
Def. 3): `H_{S1}`, the extension hierarchy (Fig. 3) of the schema `S1`
from Example 1 (`Example1_figures.lean`). The ancestor-set proofs
(`hancAttribute`/`hancFigure`/`hancCircle`/`hancColouredFigure`/
`hancColour`/`hancRadius`/`hancSetCircleColouredFigure`) already live in
`Example1_figures.lean`, since Example 1's own
`f1_satisfies_ColouredCircle` needs `hancSetCircleColouredFigure` to state
its rule-18 partition — this file just re-displays them.
-/

namespace Examples

open ShexLean.Inheritance (S_fig1 ancReach ancSetReach)
open ShexLean (Label)

/-- `{L1, L2, …}`, sorted, for a `Finset Label` — the display form
`ancReach`/`ancSetReach` (both genuinely computed, not the noncomputable
`Schema.anc`/`ancSet` — see `ShexLean.Inheritance.ancReach_eq_anc`, which
`Example1_figures.lean`'s own proofs invoke to relate the two) need. -/
def renderLabels (s : Finset Label) : String :=
  "{" ++ ", ".intercalate (s.sort (· ≤ ·)) ++ "}"

/-- Fig. 3's extension hierarchy `H_{S1}` for the schema from Example 1.
Every `anc(...)` line is `renderLabels (ancReach S_fig1 ...)`, a genuine
computation (`ancReach_eq_anc` proves this equals `S_fig1.anc`/`ancSet`
itself, `Example1_figures.lean`'s own `hancAttribute`/etc.), not a
transcription. -/
def inheritance2025ExtensionHierarchy : Example where
  name := "inheritance2025-example2-extension-hierarchy"
  summary := "H_S1 (Fig. 3): anc(ColouredCircle) counts Figure once, not twice."
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
