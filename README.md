# Formalizing Shape Expressions in Lean 4

This repository is a Lean 4 formalization of
[ShEx (Shape Expressions)](https://shex.io/). ShEx is a schema language
that validates RDF graphs.

The repository formalizes **two** papers:

> Iovka Boneva, Jose Emilio Labra Gayo, Eric Prud'hommeaux,
> *"Semantics and Validation of Shapes Schemas for RDF"*, ISWC 2017.

> Iovka Boneva, Jose Emilio Labra Gayo, Eric Prud'hommeaux, Katherine
> Thornton, Andra Waagmeester, *"Shape Expressions with Inheritance"*,
> arXiv:2503.24299, 2025.

It also contains some experiments about RDF and ShEx.

The 2025 paper adds an inheritance mechanism (`extends` and `abstract`) to
ShEx 2.1. It is not a strict extension of the 2017 formalism: the node
constraints, `closed`/`extra` and the extension hierarchy are all
different. Thus, the two papers are separate developments. They share
only the RDF and typing vocabulary, which does not depend on a paper.

The goal is a machine-checked model of each paper. The model contains RDF
graphs, the syntax of shape expressions and the satisfaction relations.
For the 2017 paper, it also contains a full proof of soundness and
completeness for two validation algorithms. The goal is not a production
ShEx validator.

A third directory, `ShexLean/Shex2026InheritanceDisjunction/`, is an
**exploration**. It is not a third paper. §6 ("Design Choices") of the
2025 paper explicitly does *not* allow `extends` on a disjunction of
shapes, because of an ambiguity with multiple inheritance. The exploration
asks if we can remove this restriction and keep the same correctness
results. The directory is a copy of `Shex2025Inheritance/` with that one
restriction removed, and with a fix for the ambiguity that is designed and
proved sound. Refer to "What is implemented (2026 exploration)" below.

## Repository structure

```
ShexLean/
  Common/                          -- vocabulary that the two papers share (RDF, Typing, ...)
  InductiveRDF/                    -- a different representation of RDF graphs. We examined it
                                      as a possible route to decidability (refer to
                                      "Decidability" below). It is proved correct, but no
                                      other part uses it.
  Shex2017Schemas/                 -- 2017 paper: syntax, semantics, algorithms, decidability
    examples/                      -- worked examples from the paper
  Shex2025Inheritance/             -- 2025 paper: syntax, semantics, algorithm, decidability
    examples/                      -- worked examples from the paper
  Shex2026InheritanceDisjunction/  -- exploration: "extends on a disjunction" (§6 of 2025).
                                      Same structure as Shex2025Inheritance/ (from the syntax
                                      to decidability and rendering)
    examples/                      -- worked example for the exploration
examples/                          -- infrastructure of the shex_lean CLI (does not depend on a paper)
STYLE.md                           -- writing rules for comments and documentation
```

`ShexLean.lean` imports each file that is not an example. Thus,
`lake build ShexLean` type-checks the full formalization. The `Examples`
library and the `shex_lean` executable build the worked examples
separately (refer to "Running" below). `examples/Registry.lean` imports
each example file. Thus, `lake build` type-checks all of them.

## Decidability

In the two papers, the satisfaction relations are `Prop`s with quantifiers
over infinite types. Thus, as written, you cannot execute them.

Each paper has a `Decidable.lean` file. This file shows that you can bound
each such quantifier to the finite graph, typing or schema. This gives
real `Decidable` instances, which `decide` and `native_decide` can use.

The 2025 side needs one restriction. `subjectOf` uses `Classical.choice`.
Thus, `.constraint` is decided only at the node level (`ShapeExpr.MOk`
and `FOk`). No worked example uses the excluded case.

The 2026 exploration needs one more bound. Rule 18 has a new existential
witness, `pick : Label → ℕ`. `ShapeExpr.extTeAt_mod` shows that only the
index modulo the number of disjuncts is important. Thus, `Decidable.lean`
searches only over the finite set `ShapeExpr.pickBound S x` for each
ancestor `x`.

The `Render.lean` file of each paper pretty-prints real `Schema`, `Graph`
and `Typing` values. It computes the `true` and `false` claims with these
instances.

## What is implemented (2017 paper)

- `Common/RDF.lean`, `Common/Typing.lean`: RDF graphs and typings (§1,
  §3.1).
- `Shex2017Schemas/Syntax.lean`, `Semantics.lean`: the grammar and the
  satisfaction relations (Fig. 1, Fig. 2).
- `Shex2017Schemas/Stratification.lean`: stratified negation (§3.2).
- `Shex2017Schemas/MaximalTyping.lean`, `Proposition1.lean`: the
  construction of the maximal correct typing, Lemma 1 and Proposition 1
  (§3.3).
- `Shex2017Schemas/Lemma2.lean`: the maximal typing does not depend on the
  stratification. The paper gives only a proof sketch for this result.
- `Shex2017Schemas/CombStrat.lean`: a lexicographic combination of two
  stratifications. The proof of Lemma 2 does not need it, but it is a
  useful fact.
- `Shex2017Schemas/ShapesSem.lean`: Definitions 5 and 6, `SHAPES_SEM`.
- `Shex2017Schemas/Algorithm1.lean`: Algorithm 1 (§4.1). It is proved
  equal to the semantics.
- `Shex2017Schemas/Algorithm2.lean`: Algorithm 2 (§4.2), the recursive
  validation procedure that detects cycles. It is proved sound and
  complete. (The proof sketch of the paper covers only termination.)
- `Shex2017Schemas/examples/`: each numbered example from the paper, one
  file for each example. Each file has proofs, and its rendered output is
  generated from real `Schema`, `Graph` and `Typing` values. Nobody copied
  the output by hand.

## What is implemented (2025 paper: Shape Expressions with Inheritance)

This part is in the namespace `ShexLean.Inheritance`. It uses
`Common/RDF.lean` and `Common/Typing.lean` with no change.

- `Shex2025Inheritance/Syntax.lean`: the grammar, `Schema = (Y, X, def, A)`,
  and the extension hierarchy `H_S` (Definitions 1-3).
- `Shex2025Inheritance/Semantics.lean`: the three satisfaction relations
  (Tables 1-3). They have a fuel parameter, because the recursion of
  `extends` is not structural.
- `Shex2025Inheritance/Termination.lean`: Lemma 1. A sufficiently large
  fuel makes the relations independent of fuel. The proof is complete. It
  needs only `WellFormedX` and `ExtAcyclic`.
- `Shex2025Inheritance/Stratification.lean`: the dependency graph and
  well-definedness (Definitions 5-6).
- `Shex2025Inheritance/CorrectTyping.lean`: correct typing, with the case
  of abstract labels (Definition 4).
- `Shex2025Inheritance/Proposition1.lean`: the maximal typing and
  Proposition 1. The proof is complete.
- `Shex2025Inheritance/Lemma2.lean`: the maximal typing does not depend on
  the stratification (§4.3). The proof is complete. The paper gives only a
  sketch.
- `Shex2025Inheritance/Algorithm1.lean`: the validation algorithm of §5,
  proved correct.
- `Shex2025Inheritance/Decidable.lean`, `Render.lean`: refer to
  "Decidability".
- `Shex2025Inheritance/examples/`: each numbered example from the paper,
  with the same structure as the 2017 side.

## What is implemented (2026 exploration: disjunctive `extends`)

§6 ("Design Choices") of the 2025 paper restricts `extends X h [and u]`.
`h` must be one plain shape, not a general shape expression. Thus, it
cannot be a disjunction `s1 or s2`.

The paper tells why. Let a node inherit from the same disjunctive ancestor
along two different paths. The example of the paper is a hypothetical
`Figure → ⟨coord@Cartesian⟩ or ⟨coord@Polar⟩`, which `ColouredCircle`
reaches through `ColouredFigure` and through `Circle`. Then the two paths
can select different disjuncts, and one node can satisfy the two. The
paper says that this is undesirable. It says that a correct fix needs
"(1) recording which disjunct... has been satisfied by each subtype, and
(2) checking whether all the subtypes satisfy the same disjunct."

The paper does not give that fix. This directory gives it, and checks if
Proposition 1 and Lemma 2 are still true with the fix. **They are true.
There is no `sorry` in the directory.**

- `Shex2026InheritanceDisjunction/Syntax.lean`: the payload of
  `ShapeExpr.extends` is now a *nonempty `List Shape`* (`hs`), not one
  `Shape`. A singleton list gives exactly the grammar of the original
  paper. Thus, the original formalism is the special case
  `hs.length = 1` of this one.
  - `ShapeExpr.extTeAt i` resolves `ext-te(x)` at a selected disjunct
    index.
  - `extTeAt_one` and `extTeAt_two` connect it to concrete triple
    expressions for the singleton case and the pair case.
  - `extTeAt_mod` shows that `extTeAt` depends only on its index modulo
    the number of disjuncts. This fact makes the new existential
    decidable.
- `Shex2026InheritanceDisjunction/Semantics.lean`: the same as
  `Shex2025Inheritance/Semantics.lean`, except rule 18 (the `.extends` case
  of `SatisfiesMFuel`). Rule 18 has one more existential witness,
  `pick : ShapeLabel → ℕ`. Each `.extends` occurrence selects `pick` one
  time, and all the ancestors that this occurrence reaches share it. This
  is the fix:
  - `S.ancSet` already puts each ancestor that one `.extends` clause can
    reach into one `Finset`, with no duplicates. (Multiple inheritance is
    written as many labels in one `xs`, not as many separate `.extends`
    nodes. `WellFormedX` and `WellFormedExtends` already exclude the
    second form.)
  - Thus, two inheritance paths that go to the same disjunctive ancestor
    must use the *same* shared `pick` and `Mx` witness.
  - This is exactly "(1) record the choice, (2) check that the subtypes
    agree". The fix needs no global parameter for the schema or the
    typing.
- `Shex2026InheritanceDisjunction/Stratification.lean`, `Termination.lean`:
  the dependency graph and Lemma 1 (independence from fuel), done again
  for `hs` and `pick`. There are two new parts:
  - `Shape.listDepInfo` is the union of the dependency information of all
    the disjuncts. `pick` can select any of them, so a sound
    stratification analysis must count them all.
  - `Shape.listSize` and `extTeAt_size_le` give a bound on the syntax-tree
    size that covers all the disjuncts together.

  Note: this version of Lemma 1 needs an extra hypothesis,
  `Schema.WellFormedExtends`, which forbids an `extends` nested in a
  restriction `u`. (The 2025 version needs only `WellFormedX` and
  `ExtAcyclic`.) The module docstring of `Termination.lean` tells why.
- `Shex2026InheritanceDisjunction/CorrectTyping.lean`, `Algorithm1.lean`:
  almost the same as the 2025 versions. They do not use the payload of
  `.extends`. Their hypotheses use `WellFormedExtends` (from
  `Termination.lean` above) where the 2025 versions use `ExtAcyclic`.
- `Shex2026InheritanceDisjunction/Proposition1.lean`: Proposition 1 of
  the paper, done again and **proved** for the relaxed semantics. The
  agreement and monotonicity lemmas `agreeM`, `stratMonoM` and
  `schemaAgreeM` are the lemmas that dereference `.extends`. Each of them
  gets the same `pick` existential as rule 18, at the location where the
  `Mx` witness already was. The other cases (`or`, `and`, `not`,
  `.ofShape`) do not change.
- `Shex2026InheritanceDisjunction/Lemma2.lean`: Lemma 2 of the paper (the
  maximal typing does not depend on the stratification). It is a
  mechanical port. It uses the results of `Proposition1.lean` abstractly,
  and never refers to `.extends` or `extTeAt` itself.
- `Shex2026InheritanceDisjunction/Decidable.lean`, `Render.lean`:
  decidability and rendering for the relaxed semantics. Refer to
  "Decidability" above for the new bound on `pick`.
- `Shex2026InheritanceDisjunction/examples/Example1_coloured_circle.lean`:
  a formalized version of the hypothetical case of §6 of the paper.
  - The body of `Figure` is relaxed to
    `[⟨coord@CartesianCoord⟩, ⟨coord@PolarCoord⟩]`.
  - `Circle` and `ColouredFigure` both extend `Figure`.
  - `ColouredCircle` inherits from the two (the motivating schema of §2,
    with `Attribute`, `Colour` and `Radius` removed, because they are not
    related to the coordinate question).

  There are three claims, verified with `native_decide`:
  - A node with *consistent* Cartesian coordinates is a `ColouredCircle`.
  - A node with *consistent* polar coordinates is a `ColouredCircle`.
    (The paper says that this legitimate use is the reason to want the
    relaxation.)
  - A node whose coordinate data matches *neither* disjunct is not a
    `ColouredCircle`. This is true for each possible witness, not only for
    the witnesses that we tried. `f3_not_satisfies_ColouredCircle` is a
    real proof of non-existence, not an omission.

## CLI infrastructure (`examples/`)

- `Example.lean`, `Registry.lean`: a record for each worked example (name,
  summary, and the schema, graph and typing as text), and the registry
  from which the executable lists and selects the examples.
- `Proof.lean`, `ProofRegistry.lean`: a record that points to the `.lean`
  file that contains a theorem. Thus, the executable shows each proof from
  its real source, not from text that a person selected.

## Requirements

- [`elan`](https://github.com/leanprover/elan), with the Lean toolchain
  that `lean-toolchain` specifies. (The first build installs it
  automatically.)
- Internet access on the first build, so that `lake` can get Mathlib.

## Running

Build the library and the executable:

```
lake build
```

List the worked examples and the proofs (this is also the default when
there are no arguments):

```
$ lake exe shex_lean list
...
Examples:
  2017 — Semantics and Validation of Shapes Schemas for RDF:
    schemas2017-example1-introduction — §1 Introductory Example: users, programmers, clients, issues.
    schemas2017-example2-issue-tracker — Recursive <IssueSh> schema, two issues reporting on each other.
    ...
  2025 — Shape Expressions with Inheritance:
    inheritance2025-example1-figures — Fig. 1/2's full ColouredCircle schema: f1 is both a Circle and a ColouredFigure.
    ...

Proofs:
  2017 — Semantics and Validation of Shapes Schemas for RDF:
    schemas2017-lemma1 — A schema with no negation has a maximal correct typing (§3.3).
    ...
  2025 — Shape Expressions with Inheritance:
    inheritance2025-lemma1 — Evaluation of n,τ⊨def(z) always terminates (§4.2).
    ...
```

Print the schema, the graph and the typing of one example:

```
$ lake exe shex_lean run schemas2017-example2-issue-tracker
schemas2017-example2-issue-tracker — Recursive <IssueSh> schema, two issues reporting on each other.

Schema:
<IssueSh> → ({is:reportedBy} @<Str> ; {is:relatedTo} @<IssueSh> [0;*])
<Str> → {"Bob", "Ren"}

Graph:
<i1> is:relatedTo <i2> .
<i1> is:reportedBy "Ren" .
<i2> is:relatedTo <i1> .
<i2> is:reportedBy "Bob" .

Typing:
{("Bob",<Str>), ("Ren",<Str>), (<i1>,<IssueSh>), (<i2>,<IssueSh>)}   (correct = true)
```

The executable pretty-prints the schema, graph and typing text from the
real Lean values. `correct = true` is a `native_decide` computation that
runs when you run the CLI. It is independent of the theorem that
`lake build` checks.

Print the Lean source of a proof. Run this command from the project root,
because it reads the `.lean` file directly:

```
lake exe shex_lean run schemas2017-lemma1
```

To step through the definitions and proofs interactively, open the
project in an editor with Lean support (for example, VS Code with the
Lean 4 extension).

## Writing style

The comments, docstrings and this README use a style based on
Simplified Technical English (ASD-STE100). Refer to [`STYLE.md`](STYLE.md)
for the rules.
