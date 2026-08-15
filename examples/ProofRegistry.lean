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
      path := "ShexLean/Shex2017Schemas/MaximalTyping.lean" },
    { name := "proposition1"
      summary :=
        "Proposition 1 (§3.3): Typing(G,S,strat) (Definition 4) is a correct typing " ++
        "of G by S, for any stratified schema."
      path := "ShexLean/Shex2017Schemas/Proposition1.lean" },
    { name := "lemma2"
      summary :=
        "Lemma 2 (§3.3): Typing(G,S,strat) does not depend on the stratification " ++
        "chosen. Proved in full via a canonical batch-revealing process and an " ++
        "independence-of-schedule argument (the paper itself only sketches this proof)."
      path := "ShexLean/Shex2017Schemas/Lemma2.lean" },
    { name := "shapes-sem"
      summary :=
        "Definitions 5-6 (§3.3): the maximal correct typing Typing(G,S) is " ++
        "well-defined (independent of the chosen stratification, by Lemma 2) and " ++
        "correct (by Proposition 1), and SHAPES_SEM itself: node n has shape L " ++
        "from S iff (n,L) ∈ Typing(G,S)."
      path := "ShexLean/Shex2017Schemas/ShapesSem.lean" },
    { name := "algorithm1"
      summary :=
        "Algorithm 1 (§4.1): the per-stratum iterative-refinement procedure `refine` " ++
        "computes exactly Typing(G,S,strat) (Definition 4)."
      path := "ShexLean/Shex2017Schemas/Algorithm1.lean" },
    { name := "algorithm2"
      summary :=
        "Algorithm 2/Proposition 2 (§4.2): the recursive, cycle-detecting `prove` " ++
        "algorithm decides Typing(G,S,strat)-membership correctly, without building " ++
        "the whole typing (the paper's own proof sketch covers only termination)."
      path := "ShexLean/Shex2017Schemas/Algorithm2.lean" },
    { name := "inheritance-lemma1"
      summary :=
        "Shape Expressions with Inheritance (2025), Lemma 1 (§4.2): evaluation of " ++
        "n,τ⊨def(z) always terminates. The paper's own proof is a one-sentence " ++
        "sketch (a finite call tree, via acyclicity of the extension hierarchy); " ++
        "this file builds real well-founded machinery for it, under an extra, " ++
        "explicitly-documented hypothesis beyond the paper's literal text."
      path := "ShexLean/Shex2025Inheritance/Termination.lean" },
    { name := "inheritance-proposition1"
      summary :=
        "Shape Expressions with Inheritance (2025), Proposition 1 (§4.3): the " ++
        "maximal typing τ_max(S,σ,G) (Definition 8) is a correct typing of G by S, " ++
        "for any stratified schema. Needed a genuinely new schema-invariance " ++
        "argument beyond the 2017 formalization's own Proposition 1 (Satisfies " ++
        "here depends on the schema, not just typing), plus two documented " ++
        "strengthenings of the paper's Table 3/Definition 5 (an implicit " ++
        "monotonicity invariant, and negation-dependency tracking under nested " ++
        "`not`)."
      path := "ShexLean/Shex2025Inheritance/Proposition1.lean" },
    { name := "inheritance-lemma2"
      summary :=
        "Shape Expressions with Inheritance (2025), Lemma 2 (§4.3): τ_max(S,σ,G) " ++
        "does not depend on which stratification σ of S is chosen. Ports the 2017 " ++
        "formalization's own from-scratch proof (Fusion/Swap/a schedule-agnostic " ++
        "batch-revealing process/Independence — the paper itself only sketches " ++
        "this), needing a further schema-invariance argument the 2017 proof never " ++
        "did: restricting the schema to an arbitrary D_S-closed label set, not " ++
        "just a stratum, since Satisfies here depends on the schema."
      path := "ShexLean/Shex2025Inheritance/Lemma2.lean" } ]

/-- Look up a registered proof by name. -/
def findProof? (name : String) : Option ProofItem :=
  proofs.find? (·.name == name)

end Examples
