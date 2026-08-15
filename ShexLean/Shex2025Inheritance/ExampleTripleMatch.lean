import Example

/-!
Display data for the 2025 "Shape Expressions with Inheritance" paper's
Example 3 (§4.1): a triple expression matched against three different
neighbourhood sets. This file only carries the text shown by the
executable; the proofs (`M24_satisfies_e`/`M246_satisfies_e`/
`M2a_satisfies_e`) live in `ShexLean/Shex2025Inheritance/Examples.lean`.
-/

namespace Examples

/-- Example 3's triple expression, matched against `M24`/`M246`/`M2a`. -/
def inheritance2025TripleMatch : Example where
  name := "inheritance2025-triple-match"
  summary := "Triple expression p@T_even;(p@T_<5*|p@T_str) matched against three sets."
  schemaText := "e = p @T_even ; (p @T_<5* | p @T_str)"
  graphText :=
    "M24  = {(n,p,2), (n,p,4)}\n" ++
    "M246 = {(n,p,2), (n,p,4), (n,p,6)}\n" ++
    "M2a  = {(n,p,2), (n,p,\"a\")}"
  typingText :=
    "τ = {2↦T_even, 2↦T_lt5, 4↦T_even, 4↦T_lt5, 6↦T_even, 6↦T_gt5, \"a\"↦T_str}\n" ++
    "M24, τ ⊨ e ∧ M246, τ ⊨ e ∧ M2a, τ ⊨ e"

end Examples
