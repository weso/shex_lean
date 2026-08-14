# shex_lean

A Lean 4 formalization of [ShEx (Shape Expressions)](https://shex.io/), the
schema language for validating RDF graphs. This is an incremental port of
the semantics from:

> Iovka Boneva, Jose Emilio Labra Gayo, Eric Prud'hommeaux,
> *"Semantics and Validation of Shapes Schemas for RDF"*, ISWC 2017.

The goal is to build up a machine-checked model of the paper — RDF graphs,
shape expression syntax, the satisfaction relations `⊢`/`⊨`, and eventually
a certified type checker — rather than a production ShEx validator.

## What's implemented

- `ShexLean/RDF.lean` — RDF terms, triples, and graphs (§1 of the paper).
- `ShexLean/Typing.lean` — node-type associations and typings (Definition 1,
  §3.1).
- `ShexLean/Syntax.lean` — the grammar of shape expressions and triple
  expressions (Fig. 1).
- `ShexLean/Semantics.lean` — the `⊢` ("node satisfies a shape expression")
  and `⊨` ("triples match a triple expression") relations (Fig. 2).
- `ShexLean/Stratification.lean` — the dependency graph (`dep⁻`/`dep⁺`) and
  Definition 3 ("schema with stratified negation"), §3.2.
- `ShexLean/MaximalTyping.lean` — §3.3 up to Lemma 1: negation-free shape
  expressions, Definition 2 named as `Schema.CorrectTyping`, monotonicity of
  `⊢`/`⊨` in `typing` for negation-free schemas, and Lemma 1 itself (a
  negation-free schema has a correct typing containing every correct
  typing, computed as the union of all correct typings).
- `ShexLean/Examples.lean` — Example 2/3 from the paper (a recursive
  `<IssueSh>` schema over two issues that report on each other), a worked
  example used as a regression check that the pieces fit together.
- `examples/Introduction.lean` — the paper's §1 Introductory Example
  (`S₀`/`G₀`: users, programmers, clients and issues), a second, larger
  regression check exercising `AND`/`someOf`/`eachOf`/repetition together,
  with its typing proved correct (Definition 2) for all 18 node/shape
  associations it induces.
- `examples/NegationRecursion.lean` — Example 4: `NOT` mixed with mutual
  recursion gives two contradicting correct typings, and the schema is not
  with stratified negation.
- `examples/StratificationExample.lean` — Example 5: a schema mixing `NOT`
  and recursion that *is* with stratified negation, with a witness
  stratification.
- `examples/Example.lean`, `examples/IssueTracker.lean`,
  `examples/Registry.lean` — a small `Example` record (name, summary,
  schema/graph/typing as text) wrapping each worked example above for
  display, plus a registry the executable lists and selects from.

`ShexLean.lean` re-exports the first group of files above as the `ShexLean`
library. `examples/` holds worked examples (their proofs, plus plain-text
descriptions used by the executable) as a separate `Examples` library, and
`Main.lean` builds an executable that lists and prints them — see
"Running" below.

## Requirements

- [`elan`](https://github.com/leanprover/elan) with the Lean toolchain
  pinned in `lean-toolchain` (currently `leanprover/lean4:v4.34.0-rc1`),
  installed automatically by `elan` on first build.
- Internet access on first build to fetch Mathlib via `lake`.

## Running

Build the library and executable:

```
lake build
```

List the worked examples in `examples/` (also the default with no
arguments):

```
$ lake exe shex_lean list
...
Examples:
  issue-tracker — Example 2/3: a recursive <IssueSh> schema over two issues that report on each other.
  introduction — The paper's §1 Introductory Example: users, programmers, clients and issues.
```

Print one example's schema, graph, and typing:

```
lake exe shex_lean run introduction
lake exe shex_lean run issue-tracker
```

This only prints the example's text — the actual proof that its typing is
correct (Definition 2) lives in the corresponding `.lean` file and is
checked by `lake build`, not re-derived at runtime (`Satisfies`/`Matches`
are `Prop`s over infinite types, so they aren't executable).

Open the project in an editor with Lean support (e.g. VS Code with the Lean
4 extension) to step through the definitions and proofs interactively, or
explore them from the command line with `lake env lean --run`.
