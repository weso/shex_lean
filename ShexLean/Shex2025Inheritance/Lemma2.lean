import ShexLean.Shex2025Inheritance.Proposition1
import ShexLean.InheritanceCore.Lemma2

/-!
Lemma 2 (§4.3) for the 2025 paper: the maximal typing does not depend on the
stratification. The proof is generic. It is in
`ShexLean/InheritanceCore/Lemma2.lean`, and applies to this development
through the instance of `InheritanceSemantics` in `Proposition1.lean`.
-/

namespace ShexLean.Inheritance

open ShexLean.InheritanceCore hiding Schema

/-- **Lemma 2.** `τ_max(S,σ,G)` does not depend on the stratification `σ`. -/
theorem lemma2 {S : Schema} (hAcyclic : S.ExtAcyclic)
    (hWFExtra : S.WellFormedExtra) (hNEF : S.NotIsExtendsFree) (hDClosed : S.DClosed)
    (strat1 strat2 : Stratification S) (G : Graph) :
    Typing8 G S strat1 = Typing8 G S strat2 :=
  InheritanceCore.lemma2 hAcyclic hWFExtra hNEF hDClosed strat1 strat2 G

end ShexLean.Inheritance
