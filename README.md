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
- `ShexLean/Proposition1.lean` — the rest of §3.3: a fully general
  "agreement" lemma (`⊢`/`⊨` depend on `typing` only through its restriction
  to the labels actually referenced, for *any* use of `NOT`) and a
  "stratified monotonicity" lemma built on it; Definition 4
  (`Typing(G,S,strat)`, built stratum-by-stratum, each stratum reusing
  Lemma 1's construction with an added "agrees with the previous stratum"
  constraint); and Proposition 1 (`Typing(G,S,strat)` is a correct typing of
  `G` by `S`, for any stratified, well-formed — `Schema.Closed` — schema).
- `ShexLean/Lemma2.lean` — Lemma 2 (stratification-independence of
  `Typing(G,S,strat)`), proved in full (no `sorry`; `#print axioms` shows
  only `propext`/`Classical.choice`/`Quot.sound`) — the paper itself only
  gives a proof sketch for this one. Built on: a Fusion lemma (revealing a
  schema's labels in one batch vs. two nested batches gives the same
  `maxTypingAgreeing` result, via a "whole object is itself a candidate"
  argument rather than per-candidate reasoning); a Swap lemma (two batches
  that each individually depend only on a common base, not on each other,
  can be revealed in either order); a canonical process `cont1` that
  repeatedly reveals the least-valued remaining batch under some fixed
  stratification until every label is settled; an Independence lemma
  (`cont1`'s final answer doesn't change if the first step instead reveals
  *any* other valid batch, via Swap and strong induction on the number of
  remaining labels — the mathematical heart of the proof); and a chaining
  argument showing `cont1` agrees with `Typing4` along *any* valid
  stratification's own checkpoints, hence `Typing4 strat1 = Typing4 strat2`
  for arbitrary `strat1`, `strat2`. (An earlier `combineStrat`/checkpoint-
  alignment approach, also complete and kept in the file as
  `Typing4_combineStrat`, turned out unable to reach the fully general
  case — no fixed linearization can align with an *arbitrary* second
  stratification's ordering of mutually-independent labels — which is what
  motivated the `cont1`/Independence route that closes it instead.)
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
- `examples/Proof.lean`, `examples/ProofRegistry.lean` — a `ProofItem`
  record (name, summary, and the `.lean` file path containing the theorem)
  for theorems shown by their actual Lean source rather than curated text
  — Lemma 1 (`ShexLean/MaximalTyping.lean`), Proposition 1
  (`ShexLean/Proposition1.lean`), and Lemma 2 (`ShexLean/Lemma2.lean`).

`ShexLean.lean` re-exports the first group of files above as the `ShexLean`
library. `examples/` holds worked examples and proof entries (plus
plain-text/registry data used by the executable) as a separate `Examples`
library, and `Main.lean` builds an executable that lists and prints them —
see "Running" below.

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

List the worked examples and proofs in `examples/` (also the default with
no arguments):

```
$ lake exe shex_lean list
...
Examples:
  issue-tracker — Example 2/3: a recursive <IssueSh> schema over two issues that report on each other.
  introduction — The paper's §1 Introductory Example: users, programmers, clients and issues.
  ...

Proofs:
  lemma1 — Lemma 1 (§3.3): a negation-free schema has a maximal correct typing (the union of all correct typings).
  proposition1 — Proposition 1 (§3.3): Typing(G,S,strat) (Definition 4) is a correct typing of G by S, for any stratified schema.
  lemma2 — Lemma 2 (§3.3): Typing(G,S,strat) does not depend on the stratification chosen.
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

Print a proof's Lean source (statement and tactic proof) — unlike
examples, this reads the `.lean` file directly, so run it from the project
root:

```
lake exe shex_lean run lemma1
```

Open the project in an editor with Lean support (e.g. VS Code with the Lean
4 extension) to step through the definitions and proofs interactively, or
explore them from the command line with `lake env lean --run`.
