# Formalizing Shape Expressions in Lean 4

A Lean 4 formalization of [ShEx (Shape Expressions)](https://shex.io/), the
schema language for validating RDF graphs. 

This repository formalizes **two** papers and contains some experiments about RDF and ShEx:

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

A third directory, `ShexLean/Shex2026InheritanceDisjunction/`, is an
**exploration**, not a third paper: it asks whether the 2025 paper's own
§6 ("Design Choices") — which explicitly *declines* to allow `extends` on
a disjunction of shapes, citing an unresolved multiple-inheritance
ambiguity — could be relaxed while keeping the same correctness results.
It's a copy of `Shex2025Inheritance/` with that one restriction lifted and
a fix for the ambiguity designed and proved sound; see "What's implemented
(2026 exploration)" below.

## Repository structure

```
ShexLean/
  Common/                 -- vocabulary shared by both papers (RDF, Typing, ...)
  InductiveRDF/               -- an alternative RDF graph representation,
                                investigated (see "Decidability" below) as a
                                possible route to decidability and kept as a
                                proved-correct but non-load-bearing detour
  Shex2017Schemas/         -- 2017 paper: syntax, semantics, algorithms, decidability
    examples/               -- worked examples from the paper
  Shex2025Inheritance/     -- 2025 paper: syntax, semantics, algorithm, decidability
    examples/               -- worked examples from the paper
  Shex2026InheritanceDisjunction/ -- exploration: 2025's §6 "extends on a
                                disjunction" relaxation, same shape as
                                Shex2025Inheritance/ (syntax through
                                decidability/renderer)
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

## What's implemented (2026 exploration: disjunctive `extends`)

§6 ("Design Choices") of the 2025 paper restricts `extends X h [and u]` so
`h` must be a single plain shape, not a general shape expression — in
particular, not a disjunction `s1 or s2`. The paper explains why: if a
node inherits from the same disjunctive ancestor along two different
paths (their own example — a hypothetical `Figure → ⟨coord@Cartesian⟩ or
⟨coord@Polar⟩`, reached by `ColouredCircle` via both `ColouredFigure` and
`Circle`), nothing stops the two paths from independently picking
different disjuncts, letting one node satisfy both — which the paper
calls undesirable — and fixing it properly would need "(1) recording
which disjunct... has been satisfied by each subtype, and (2) checking
whether all the subtypes satisfy the same disjunct." The paper doesn't
work out that fix; this directory does, and checks whether Proposition 1
and Lemma 2 still hold once it's in place. **They do, with no `sorry`
anywhere in the directory.**

- `ShexLean/Shex2026InheritanceDisjunction/Syntax.lean` — `ShapeExpr.
  extends`'s payload generalized from a single `Shape` to a *nonempty
  `List Shape`* (`hs`); a singleton list reproduces the original paper's
  grammar exactly, so the unmodified formalism is the `hs.length = 1`
  special case of this one. `ShapeExpr.extTeAt i` resolves `ext-te(x)` at
  a chosen disjunct index (`extTeAt_one`/`extTeAt_two` connect this back
  to concrete triple expressions for the singleton/pair cases;
  `extTeAt_mod` — the fact `extTeAt` only depends on its index mod the
  disjunct count — is what later makes the new existential decidable).
- `ShexLean/Shex2026InheritanceDisjunction/Semantics.lean` — identical to
  `Shex2025Inheritance/Semantics.lean` except rule 18 (`SatisfiesMFuel`'s
  `.extends` case), which gains one more existential witness, `pick :
  ShapeLabel → ℕ`, chosen once per `.extends` occurrence and shared
  across every ancestor that occurrence reaches. This is the actual fix:
  `S.ancSet` already deduplicates every ancestor reachable from one
  `.extends` clause into a single `Finset` (multiple inheritance is
  expressed as multiple labels in one `xs`, not multiple separate
  `.extends` nodes — a shape `WellFormedX`/`WellFormedExtends` already
  rule out), so the *same* shared `pick`/`Mx` witness is forced onto two
  inheritance paths that converge on the same disjunctive ancestor —
  exactly "(1) record the choice, (2) check subtypes agree," without a
  schema- or typing-global parameter anywhere else.
- `ShexLean/Shex2026InheritanceDisjunction/Stratification.lean`,
  `Termination.lean` — the dependency graph and Lemma 1 (fuel-
  independence), re-derived against `hs`/`pick`: `Shape.listDepInfo`
  (the union of every disjunct's own dependency info — any of them could
  be `pick`ed, so a sound stratification analysis must count them all) and
  `Shape.listSize`/`extTeAt_size_le` (an AST-size bound covering every
  disjunct at once) are the two new pieces; the stabilization induction
  itself carries over unchanged in shape.
- `ShexLean/Shex2026InheritanceDisjunction/CorrectTyping.lean`,
  `Algorithm1.lean` — unchanged from the 2025 versions, verbatim mechanical
  ports (neither touches `.extends`'s payload at all).
- `ShexLean/Shex2026InheritanceDisjunction/Proposition1.lean` — the paper's
  own Proposition 1, re-derived and **proved** for the relaxed semantics.
  The `agreeM`/`stratMonoM`/`schemaAgreeM` agreement/monotonicity lemmas
  (the ones that actually dereference `.extends`) each gain the same
  `pick` existential rule 18 itself gained, threaded through exactly where
  the existing `Mx` witness already was — every other case (`or`/`and`/
  `not`/`.ofShape`) is untouched.
- `ShexLean/Shex2026InheritanceDisjunction/Lemma2.lean` — the paper's
  Lemma 2 (stratification-independence), a verbatim mechanical port: it
  consumes `Proposition1.lean`'s machinery abstractly and never itself
  references `.extends`/`extTeAt`.
- `ShexLean/Shex2026InheritanceDisjunction/Decidable.lean`,
  `Render.lean` — decidability and rendering for the relaxed semantics,
  see "Decidability" above for the new `pick`-bounding piece.
- `ShexLean/Shex2026InheritanceDisjunction/examples/
  Example1_coloured_circle.lean` — a formalized version of the paper's own
  §6 hypothetical: `Figure`'s body relaxed to `[⟨coord@CartesianCoord⟩,
  ⟨coord@PolarCoord⟩]`, with `Circle`/`ColouredFigure` both extending it
  and `ColouredCircle` multiply-inheriting from both (§2's motivating
  schema, `Attribute`/`Colour`/`Radius` stripped out as irrelevant to the
  coordinate question). Three `native_decide`-verified claims: a node with
  *consistent* Cartesian-only or Polar-only coordinates is a
  `ColouredCircle` (the legitimate use the paper says motivated wanting
  this), and a node whose coordinate data matches *neither* disjunct is
  rejected — for every possible witness, not just the ones tried, since
  `f3_not_satisfies_ColouredCircle` is a genuine non-existence proof, not
  an omission.

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
