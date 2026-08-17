import Proof

/-!
The list of proofs the `shex_lean` executable can `list`/`run` alongside the
worked examples (`Examples.Registry`). Names are prefixed `schemas2017-`/
`inheritance2025-`/`inheritance2026-` so it's clear at a glance which paper
(or exploratory variant) each proof belongs to, and each summary is kept to
one line.
-/

namespace Examples

/-- All proofs registered for the executable's `list`/`run` commands. -/
def proofs : List ProofItem :=
  [ { name := "schemas2017-lemma1"
      summary := "A negation-free schema has a maximal correct typing (§3.3)."
      path := "ShexLean/Shex2017Schemas/MaximalTyping.lean" },
    { name := "schemas2017-proposition1"
      summary := "Typing(G,S,strat) is a correct typing of G by S (§3.3)."
      path := "ShexLean/Shex2017Schemas/Proposition1.lean" },
    { name := "schemas2017-lemma2"
      summary := "Typing(G,S,strat) doesn't depend on the stratification chosen (§3.3)."
      path := "ShexLean/Shex2017Schemas/Lemma2.lean" },
    { name := "schemas2017-shapes-sem"
      summary := "Typing(G,S) is well-defined and correct; SHAPES_SEM itself (§3.3)."
      path := "ShexLean/Shex2017Schemas/ShapesSem.lean" },
    { name := "schemas2017-algorithm1"
      summary := "refine computes Typing(G,S,strat) exactly (§4.1)."
      path := "ShexLean/Shex2017Schemas/Algorithm1.lean" },
    { name := "schemas2017-algorithm2"
      summary := "prove decides Typing(G,S,strat) membership without building it (§4.2)."
      path := "ShexLean/Shex2017Schemas/Algorithm2.lean" },
    { name := "inheritance2025-lemma1"
      summary := "Evaluation of n,τ⊨def(z) always terminates (§4.2)."
      path := "ShexLean/Shex2025Inheritance/Termination.lean" },
    { name := "inheritance2025-proposition1"
      summary := "τ_max(S,σ,G) is a correct typing of G by S (§4.3)."
      path := "ShexLean/Shex2025Inheritance/Proposition1.lean" },
    { name := "inheritance2025-lemma2"
      summary := "τ_max(S,σ,G) doesn't depend on the stratification chosen (§4.3)."
      path := "ShexLean/Shex2025Inheritance/Lemma2.lean" },
    { name := "inheritance2026-lemma1"
      summary := "Termination still holds with disjunctive extends (§6 explored, §4.2)."
      path := "ShexLean/Shex2026InheritanceDisjunction/Termination.lean" },
    { name := "inheritance2026-proposition1"
      summary := "τ_max(S,σ,G) is still correct with disjunctive extends (§6 explored, §4.3)."
      path := "ShexLean/Shex2026InheritanceDisjunction/Proposition1.lean" },
    { name := "inheritance2026-lemma2"
      summary := "τ_max still stratification-independent with disjunctive extends (§6, §4.3)."
      path := "ShexLean/Shex2026InheritanceDisjunction/Lemma2.lean" } ]

/-- Look up a registered proof by name. -/
def findProof? (name : String) : Option ProofItem :=
  proofs.find? (·.name == name)

end Examples
