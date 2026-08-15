import Proof

/-!
The list of proofs the `shex_lean` executable can `list`/`run` alongside the
worked examples (`Examples.Registry`).
-/

namespace Examples

/-- All proofs registered for the executable's `list`/`run` commands. -/
def proofs : List ProofItem :=
  [ { name := "lemma1"
      summary :=
        "Lemma 1 (§3.3): a negation-free schema has a maximal correct typing " ++
        "(the union of all correct typings)."
      path := "ShexLean/MaximalTyping.lean" },
    { name := "proposition1"
      summary :=
        "Proposition 1 (§3.3): Typing(G,S,strat) (Definition 4) is a correct typing " ++
        "of G by S, for any stratified schema."
      path := "ShexLean/Proposition1.lean" },
    { name := "lemma2"
      summary :=
        "Lemma 2 (§3.3): Typing(G,S,strat) does not depend on the stratification " ++
        "chosen. Proved in full via a canonical batch-revealing process and an " ++
        "independence-of-schedule argument (the paper itself only sketches this proof)."
      path := "ShexLean/Lemma2.lean" },
    { name := "algorithm1"
      summary :=
        "Algorithm 1 (§4.1): the per-stratum iterative-refinement procedure `refine` " ++
        "computes exactly Typing(G,S,strat) (Definition 4)."
      path := "ShexLean/Algorithm1.lean" },
    { name := "algorithm2"
      summary :=
        "Algorithm 2/Proposition 2 (§4.2): the recursive, cycle-detecting `prove` " ++
        "algorithm decides Typing(G,S,strat)-membership correctly, without building " ++
        "the whole typing (the paper's own proof sketch covers only termination)."
      path := "ShexLean/Algorithm2.lean" } ]

/-- Look up a registered proof by name. -/
def findProof? (name : String) : Option ProofItem :=
  proofs.find? (·.name == name)

end Examples
