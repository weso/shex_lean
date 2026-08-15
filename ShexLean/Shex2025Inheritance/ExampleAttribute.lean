import Example

/-!
Display data for the 2025 "Shape Expressions with Inheritance" paper's §2
motivating example (Fig. 1/2): the `Attribute` shape and node `a1`. Only
this first slice of the fuller multiple-inheritance `ColouredCircle`
example is formalized so far (see `ShexLean/Shex2025Inheritance/
Examples.lean`'s module docstring for why). This file only carries the
text shown by the executable; the proof (`a1_satisfies_Attribute`) lives
in `ShexLean/Shex2025Inheritance/Examples.lean`.
-/

namespace Examples

/-- Fig. 1/2's `Attribute` shape, satisfied by node `a1`. -/
def inheritance2025Attribute : Example where
  name := "inheritance2025-attribute"
  summary := "§2's Attribute shape (Fig. 1/2), satisfied by node a1."
  schemaText := "Attribute → extends _ ⟨name @T_str ; value @T_any⟩"
  graphText := "a1 name \"radius\" ; value 10"
  typingText :=
    "τ = {\"radius\"↦T_str, 10↦T_any}\n" ++
    "a1 ⊨ Attribute"

end Examples
