import Proof

/-!
The list of proofs that the `shex_lean` executable can `list` and `run`,
together with the worked examples (`Examples.Registry`).

Each name starts with a prefix that identifies the paper:

* `schemas2017-` for the 2017 paper.
* `inheritance2025-` for the 2025 paper.
* `inheritance2026-` for the 2026 exploration of the 2025 paper.

Each summary is one line.
-/

namespace Examples

/-- All the proofs that the `list` and `run` commands of the executable
can use. -/
def proofs : List ProofItem :=
  [ { name := "schemas2017-lemma1"
      summary := "A schema with no negation has a maximal correct typing (§3.3)."
      path := "ShexLean/Shex2017Schemas/MaximalTyping.lean" },
    { name := "schemas2017-proposition1"
      summary := "Typing(G,S,strat) is a correct typing of G by S (§3.3)."
      path := "ShexLean/Shex2017Schemas/Proposition1.lean" },
    { name := "schemas2017-lemma2"
      summary := "Typing(G,S,strat) does not depend on the stratification (§3.3)."
      path := "ShexLean/Shex2017Schemas/Lemma2.lean" },
    { name := "schemas2017-shapes-sem"
      summary := "Typing(G,S) is well-defined and correct, and SHAPES_SEM (§3.3)."
      path := "ShexLean/Shex2017Schemas/ShapesSem.lean" },
    { name := "schemas2017-algorithm1"
      summary := "refine computes exactly Typing(G,S,strat) (§4.1)."
      path := "ShexLean/Shex2017Schemas/Algorithm1.lean" },
    { name := "schemas2017-algorithm2"
      summary := "prove decides membership in Typing(G,S,strat) and does not build it (§4.2)."
      path := "ShexLean/Shex2017Schemas/Algorithm2.lean" },
    { name := "inheritance2025-lemma1"
      summary := "Evaluation of n,τ⊨def(z) always terminates (§4.2)."
      path := "ShexLean/Shex2025Inheritance/Termination.lean" },
    { name := "inheritance2025-proposition1"
      summary := "τ_max(S,σ,G) is a correct typing of G by S (§4.3)."
      path := "ShexLean/InheritanceCore/MaxTyping.lean" },
    { name := "inheritance2025-lemma2"
      summary := "τ_max(S,σ,G) does not depend on the stratification (§4.3)."
      path := "ShexLean/InheritanceCore/Lemma2.lean" },
    { name := "inheritance2026-lemma1"
      summary := "Termination is still true with disjunctive extends (§6 explored, §4.2)."
      path := "ShexLean/Shex2026InheritanceDisjunction/Termination.lean" },
    { name := "inheritance2026-proposition1"
      summary := "τ_max(S,σ,G) is still a correct typing with disjunctive extends (§6 explored, §4.3)."
      path := "ShexLean/Shex2026InheritanceDisjunction/Proposition1.lean" },
    { name := "inheritance2026-lemma2"
      summary := "τ_max still does not depend on the stratification, with disjunctive extends (§6, §4.3)."
      path := "ShexLean/InheritanceCore/Lemma2.lean" } ]

/-- Find a registered proof by its name. -/
def findProof? (name : String) : Option ProofItem :=
  proofs.find? (·.name == name)

end Examples
