import ShexLean.Shex2025Inheritance.Proposition1
import ShexLean.InheritanceCore.Algorithm1

/-!
§5: the validation and refinement algorithm (`refine`) for the 2025 paper,
and the proof that it is correct. The algorithm and the proof are generic.
They are in `ShexLean/InheritanceCore/Algorithm1.lean`, and apply to this
development through the instance of `InheritanceSemantics` in
`Proposition1.lean`.
-/

namespace ShexLean.Inheritance

open ShexLean.InheritanceCore hiding Schema

/-- **Algorithm 1 is correct.** It computes exactly `τ_max(S,σ,G)`
(Definition 8). -/
theorem algorithm1_correct (G : Graph) (S : Schema) (strat : Stratification S)
    (hAcyclic : S.ExtAcyclic) (hWFExtra : S.WellFormedExtra)
    (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed) :
    Algorithm1 G S strat = Typing8 G S strat :=
  InheritanceCore.algorithm1_correct G S strat hAcyclic hWFExtra hNEF hDClosed

/-- **Algorithm 1 computes a correct typing.** -/
theorem algorithm1_correctTyping (G : Graph) (S : Schema) (strat : Stratification S)
    (hAcyclic : S.ExtAcyclic) (hWFExtra : S.WellFormedExtra)
    (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed) :
    S.CorrectTyping G (Algorithm1 G S strat) :=
  InheritanceCore.algorithm1_correctTyping G S strat hAcyclic hWFExtra hNEF hDClosed

end ShexLean.Inheritance
