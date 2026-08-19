# Formalizing Shape Expressions in Lean 4

A Lean 4 formalization of [ShEx (Shape Expressions)](https://shex.io/), the
schema language for validating RDF graphs. This repository formalizes two
papers, side by side, each in its own directory and Lean namespace:

> Iovka Boneva, Jose Emilio Labra Gayo, Eric Prud'hommeaux,
> *"Semantics and Validation of Shapes Schemas for RDF"*, ISWC 2017.

> Iovka Boneva, Jose Emilio Labra Gayo, Eric Prud'hommeaux, Katherine
> Thornton, Andra Waagmeester, *"Shape Expressions with Inheritance"*,
> arXiv:2503.24299, 2025.

The 2025 paper extends ShEx 2.1 with an `extends`/`abstract` inheritance
mechanism. It is not a strict extension of the 2017 formalism — node
constraints, `closed`/`extra`, and the extension hierarchy all differ — so
the two live as separate developments, sharing only the paper-independent
RDF/typing vocabulary they agree on.

The goal is a machine-checked model of each paper (RDF graphs, shape
expression syntax, satisfaction relations, and for 2017 a full
soundness/completeness proof for two validation algorithms), not a
production ShEx validator. The repository also contains the LaTeX source
of a paper describing this formalization — see [`paper/`](paper/).

## Repository structure

```
ShexLean/
  Common/                 -- vocabulary shared by both papers (RDF, Typing, ...)
  Shex2017Schemas/         -- 2017 paper: syntax, semantics, algorithms, decidability
    examples/               -- worked examples from the paper
  Shex2025Inheritance/     -- 2025 paper: syntax, semantics, algorithm, decidability
    examples/               -- worked examples from the paper
examples/                 -- shex_lean CLI infrastructure (paper-agnostic)
paper/                    -- LaTeX source of the accompanying paper
```

`ShexLean.lean` imports every non-example file, so `lake build ShexLean`
type-checks the whole formalization. The worked examples are built
separately via the `Examples` library and the `shex_lean` executable (see
"Running" below).

## Decidability

Both papers' satisfaction relations are stated as `Prop`s quantifying over
infinite types, so as written they are not executable. Each paper has a
`Decidable.lean` that shows every such quantifier can be bounded to the
finite graph/typing/schema at hand, giving genuine `Decidable` instances
(`decide`/`native_decide`-able). On the 2025 side, one restriction is
needed: `subjectOf` relies on `Classical.choice`, so `.constraint` is only
decided at the node level (`ShapeExpr.MOk`/`FOk`); no worked example hits
the excluded case. Each paper's `Render.lean` pretty-prints real `Schema`/
`Graph`/`Typing` values and computes true/false claims via these instances.

## What's implemented (2017 paper)

- `Common/RDF.lean`, `Common/Typing.lean` — RDF graphs and typings (§1, §3.1).
- `Shex2017Schemas/Syntax.lean`, `Semantics.lean` — grammar and satisfaction
  relations (Fig. 1, 2).
- `Shex2017Schemas/Stratification.lean` — stratified negation (§3.2).
- `Shex2017Schemas/MaximalTyping.lean`, `Proposition1.lean` — the maximal
  correct typing construction, Lemma 1 and Proposition 1 (§3.3).
- `Shex2017Schemas/Lemma2.lean` — stratification-independence of the
  maximal typing; the paper gives only a proof sketch here.
- `Shex2017Schemas/ShapesSem.lean` — Definitions 5-6, `SHAPES_SEM`.
- `Shex2017Schemas/Algorithm1.lean` — Algorithm 1 (§4.1), proved equal to
  the semantics.
- `Shex2017Schemas/Algorithm2.lean` — Algorithm 2 (§4.2), the recursive
  cycle-detecting validation procedure, proved sound and complete (the
  paper's own proof sketch covers only termination).
- `Shex2017Schemas/examples/` — every numbered example from the paper, one
  file per example, with proofs and rendered output generated from real
  `Schema`/`Graph`/`Typing` values rather than transcribed by hand.

## What's implemented (2025 paper: Shape Expressions with Inheritance)

Lives in the `ShexLean.Inheritance` namespace, reusing `Common/RDF.lean`
and `Common/Typing.lean` unchanged.

- `Shex2025Inheritance/Syntax.lean` — grammar, `Schema = (Y, X, def, A)`,
  and the extension hierarchy `H_S` (Definitions 1-3).
- `Shex2025Inheritance/Semantics.lean` — the three satisfaction relations
  (Tables 1-3), defined with a fuel parameter since `extends` recursion
  isn't structural.
- `Shex2025Inheritance/Termination.lean` — Lemma 1: a large-enough fuel
  makes the relations fuel-independent, fully proved.
- `Shex2025Inheritance/Stratification.lean` — dependency graph and
  well-definedness (Definitions 5-6).
- `Shex2025Inheritance/CorrectTyping.lean` — correct typing with the
  abstract-label case (Definition 4).
- `Shex2025Inheritance/Proposition1.lean` — the maximal typing and
  Proposition 1, fully proved.
- `Shex2025Inheritance/Lemma2.lean` — stratification-independence (§4.3),
  fully proved; the paper only sketches this.
- `Shex2025Inheritance/Algorithm1.lean` — the §5 validation algorithm,
  proved correct.
- `Shex2025Inheritance/Decidable.lean`, `Render.lean` — see "Decidability".
- `Shex2025Inheritance/examples/` — every numbered example from the paper,
  same structure as the 2017 side.

## CLI infrastructure (`examples/`)

- `Example.lean`, `Registry.lean` — a record wrapping each worked example
  (name, summary, schema/graph/typing as text) and the registry the
  executable lists and selects from.
- `Proof.lean`, `ProofRegistry.lean` — a record pointing at the `.lean`
  file containing a given theorem, so proofs are shown by their actual
  source rather than curated text.

## Requirements

- [`elan`](https://github.com/leanprover/elan) with the Lean toolchain
  pinned in `lean-toolchain` (installed automatically on first build).
- Internet access on first build to fetch Mathlib via `lake`.

## Running

Build the library and executable:

```
lake build
```

List the worked examples and proofs (also the default with no arguments):

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
    schemas2017-lemma1 — A negation-free schema has a maximal correct typing (§3.3).
    ...
  2025 — Shape Expressions with Inheritance:
    inheritance2025-lemma1 — Evaluation of n,τ⊨def(z) always terminates (§4.2).
    ...
```

Print one example's schema, graph, and typing:

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

The schema/graph/typing text is pretty-printed from the real Lean values,
and `correct = true` is a `native_decide` computation run at CLI time,
independent of the theorem checked by `lake build`.

Print a proof's Lean source (run from the project root, since this reads
the `.lean` file directly):

```
lake exe shex_lean run schemas2017-lemma1
```

Open the project in an editor with Lean support (e.g. VS Code with the
Lean 4 extension) to step through definitions and proofs interactively.
