import Example

/-!
Display data for the 2025 "Shape Expressions with Inheritance" paper's
Examples 4-5 (§4.1-4.2): a chain of `extends`-related shapes `x0..x6`,
exercising Table 3's rule 18 partition. This file only carries the text
shown by the executable; the proof (`M24_satisfies_defx1`) lives in
`ShexLean/Shex2025Inheritance/Examples.lean`.
-/

namespace Examples

/-- Examples 4-5's `extends` chain, with `M24, τ ⊨ def(x1)` proved via
`x1`'s rule-18 partition against its ancestor `x0`. -/
def inheritance2025Extends : Example where
  name := "inheritance2025-extends"
  summary := "extends chain x0..x6; M24,τ ⊨ def(x1) via x1's rule-18 partition."
  schemaText :=
    "x0 → extends _ ⟨p @T_even⟩\n" ++
    "x1 → extends x0 ⟨p @T_even⟩\n" ++
    "x2 → extends x1 ⟨p @T_<5⟩\n" ++
    "x3 → extends x0 ⟨p @T_even⟩ and ⟨p @T_>5*⟩\n" ++
    "x4 → extends x6 ⟨p @T_<5⟩\n" ++
    "x5 → extends x0 extra {p} ⟨ε⟩\n" ++
    "x6 → extends x3 ⟨p @T_even⟩"
  graphText := "M24 = {(n,p,2), (n,p,4)}"
  typingText :=
    "τ = {2↦T_even, 2↦T_lt5, 4↦T_even, 4↦T_lt5, 6↦T_even, 6↦T_gt5, \"a\"↦T_str}\n" ++
    "M24, τ ⊨ def(x1)"

end Examples
