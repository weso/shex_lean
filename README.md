# Formalizing Shape Expressions in Lean 4

A Lean 4 formalization of [ShEx (Shape Expressions)](https://shex.io/), the
schema language for validating RDF graphs. This repository formalizes
**two** papers:

> Iovka Boneva, Jose Emilio Labra Gayo, Eric Prud'hommeaux,
> *"Semantics and Validation of Shapes Schemas for RDF"*, ISWC 2017.

> Iovka Boneva, Jose Emilio Labra Gayo, Eric Prud'hommeaux, Katherine
> Thornton, Andra Waagmeester, *"Shape Expressions with Inheritance"*,
> arXiv:2503.24299, 2025.

The 2025 paper is a genuine *second* formalism built on top of ShEx 2.1 (an
`extends`/`abstract` inheritance mechanism), not a strict extension of the
2017 one — node constraints become an arbitrary predicate rather than a
concrete `ValueDescr`, `closed`/`extra` become first-class shape modifiers,
and shapes can extend one another along a new *extension hierarchy*. The
two formalisms live side by side, each in its own directory and Lean
namespace, sharing only the paper-independent RDF/typing vocabulary both
papers actually agree on.

The goal for both is a machine-checked model of each paper — RDF graphs,
shape expression syntax, the satisfaction relations, and (for the 2017
paper) a full soundness/completeness story for two validation algorithms
— rather than a production ShEx validator.

## Repository structure

```
ShexLean/
  Common/                    -- shared between both papers, paper-independent
  InductiveRDF/               -- makes both papers' semantics decidable/executable
                                (see "Decidability" below) — paper-agnostic
  Shex2017Schemas/            -- the 2017 paper: syntax, semantics, propositions,
                                lemmas, algorithms, a Decidable-backed renderer
    examples/                 -- the paper's own worked examples, one file per
                                example (ExampleN_slug.lean), with real
                                native_decide-computed display text
  Shex2025Inheritance/         -- the 2025 paper: syntax, semantics, propositions,
                                lemmas, algorithm, a Decidable-backed renderer
    examples/                 -- the paper's own worked examples, one file per
                                example (ExampleN_slug.lean), with real
                                native_decide-computed display text
examples/                     -- the shex_lean executable's CLI infrastructure
                                (example/proof registries) — paper-agnostic
```

- **`ShexLean/Common/`** holds the vocabulary both papers use *unchanged*:
  `RDF.lean` (IRIs, RDF nodes, triples, graphs — §1 of the 2017 paper),
  `Typing.lean` (shape labels, node-type associations, typings —
  Definition 1, §3.1), and `DisjointUnion.lean` (the disjoint-union helpers
  both papers' triple-expression semantics need for `;`/`*`, originally
  written once for 2017's Rules te-each-of/te-repet and reused as-is by
  2025's analogous Table 1 rules). Neither paper's `Schema`/`ShapeExpr`
  type is here — those genuinely differ between the two formalisms (2025's
  `Schema = (Y, X, def, A)` vs. 2017's `Schema = (L, def)`, in particular)
  and live in each paper's own directory/namespace instead
  (`ShexLean.Inheritance` for the 2025 side — the Lean *namespace* kept its
  original name even though the *directory* is now `Shex2025Inheritance/`;
  see that section below).
- **`ShexLean/InductiveRDF/`** makes both papers' satisfaction relations
  genuinely `Decidable` — see "Decidability" below.
- **`ShexLean/Shex2017Schemas/`** is the 2017 paper's content: syntax,
  semantics, stratification, the maximal-typing propositions/lemmas, both
  validation algorithms, a renderer built on `InductiveRDF/`'s
  decidability, and (in its own `examples/` subfolder) the paper's own
  worked examples, one file per numbered example — see "What's implemented
  (2017 paper)" below.
- **`ShexLean/Shex2025Inheritance/`** is the 2025 paper's content, the same
  shape as the 2017 side (semantics, propositions, lemmas, its own
  validation algorithm, its own decidability layer and renderer, worked
  examples) — see "What's implemented (2025 paper)" below.
- **`examples/`** now holds only paper-*agnostic* infrastructure for the
  `shex_lean` CLI: `Example.lean`/`Proof.lean` (the plain-data record types
  for a displayable worked example / a displayable proof), and
  `Registry.lean`/`ProofRegistry.lean` (the lists the CLI's `list`/`run`
  commands read from, referencing content in both `Shex2017Schemas/` and
  `Shex2025Inheritance/`).

`ShexLean.lean` is the single `ShexLean` library's root and imports every
non-worked-example file across `Common/`, `InductiveRDF/`,
`Shex2017Schemas/`, and `Shex2025Inheritance/` explicitly (so `lake build
ShexLean` alone type-checks the whole formalization, not just whichever
subset happens to be reachable from the CLI); `examples/` (top-level,
including both papers' `examples/` subfolders under `ShexLean/`) is built
separately via the `Examples` library and the `shex_lean` executable, which
is what actually exercises the worked examples and proofs — see "Running"
below. Build any file explicitly if you want to check it in isolation
(`lake build ShexLean.Shex2017Schemas.Algorithm2`, etc.).

## Decidability

Both papers' satisfaction relations are naturally stated as `Prop`s
quantifying over infinite types (`RDFNode`, arbitrary `Finset Triple`,
arbitrary-length lists, …), so *as written* they're existence claims, not
executable code. `ShexLean/InductiveRDF/Decidable.lean` and
`ShexLean/Shex2025Inheritance/Decidable.lean` close that gap: every
quantifier that looks unbounded turns out to be **restatable as a search
bounded to the finite graph/typing/schema at hand**, because every witness
that could actually satisfy the constraint is already forced — by an
equation in the same clause — to lie inside it. Reformulated that way, the
whole relation becomes a genuine, kernel-reducible `Decidable` instance
(`decide`/`native_decide`-able, not just "classically decidable" the way
literally every `Prop` trivially is under Mathlib's ambient axioms).

- **2017 side** (`ShexLean/InductiveRDF/`): `satisfies_decidable`/
  `matches_decidable` are decidable **unconditionally, for every
  `ShapeExpr`/`TripleExpr`, no restricted fragment needed** — including
  `.rep`'s unbounded repetition (`RepBound.lean`: any witness can be
  shrunk/padded to length `≤ N.card + min`). `Graph.lean`/`RoundTrip.lean`
  also port Labra Gayo/Jeuring/Álvarez Rodríguez's 2013 "Inductive
  representations of RDF Graphs" triple-graph encoding as an alternative
  graph representation, with a proved round-trip to this project's own
  `Finset Triple`-based `Graph` — investigated as a possible route to
  decidability, but (see `Decidable.lean`'s own docstring) the graph
  representation was never actually the obstacle; the bounded-
  reformulation technique above works identically over the existing
  representation, so nothing in this repo depends on the inductive-graph
  encoding for decidability. `DecidablePayoff.lean` re-derives a handful of
  hand-proved example facts by nothing but `native_decide`, as a
  regression check on the whole layer.
- **2025 side** (`ShexLean/Shex2025Inheritance/Decidable.lean`): the same
  technique, applied to a harder semantics (Table 3's `extends` rule
  recurses into *other labels'* definitions and an ancestor-indexed
  partition search, not just the current expression) — `Schema.anc`/
  `ancSet` made computable (`ancReach`/`ancSetReach`, proved equal given
  the paper's own `XClosed` hierarchy assumption), `.star`'s unbounded
  repetition made decidable via a `Fuel`-threaded partition search, and
  rule 18's ancestor-indexed partition made decidable via a `Finset.pi`-
  bounded reformulation of its witness function. One genuine restriction
  *is* needed here, unlike 2017: `subjectOf` (rule 13) is
  `Classical.choice`-based with no computable equivalent in general, so
  `.constraint` is only decided at the node level (where it needs no
  `subjectOf` at all) — `ShapeExpr.MOk`/`FOk` name the resulting fragment
  explicitly, following this repo's existing `WellFormedX`/
  `WellFormedExtends`-style precedent of naming restrictions rather than
  leaving them implicit. Verified to cost nothing in practice: none of the
  worked examples below ever hit the excluded case.
- **Rendering** (`ShexLean/Shex2017Schemas/Render.lean`,
  `ShexLean/Shex2025Inheritance/Render.lean`): pretty-prints the *real*
  `Schema`/`Graph`/`Typing` Lean values (not hand-typed transcriptions) and
  computes every true/false claim in a worked example's display text via
  `renderDecide`, wrapping the `Decidable` instances above — see "Running"
  below for what this looks like from the CLI.

## What's implemented (2017 paper)

- `ShexLean/Common/RDF.lean` — RDF terms, triples, and graphs (§1 of the
  paper).
- `ShexLean/Common/Typing.lean` — node-type associations and typings
  (Definition 1, §3.1).
- `ShexLean/Shex2017Schemas/Syntax.lean` — the grammar of shape expressions
  and triple expressions (Fig. 1).
- `ShexLean/Shex2017Schemas/Semantics.lean` — the `⊢` ("node satisfies a
  shape expression") and `⊨` ("triples match a triple expression")
  relations (Fig. 2).
- `ShexLean/Shex2017Schemas/Stratification.lean` — the dependency graph
  (`dep⁻`/`dep⁺`) and Definition 3 ("schema with stratified negation"),
  §3.2.
- `ShexLean/Shex2017Schemas/MaximalTyping.lean` — §3.3 up to Lemma 1:
  negation-free shape expressions, Definition 2 named as
  `Schema.CorrectTyping`, monotonicity of `⊢`/`⊨` in `typing` for
  negation-free schemas, and Lemma 1 itself (a negation-free schema has a
  correct typing containing every correct typing, computed as the union of
  all correct typings).
- `ShexLean/Shex2017Schemas/Proposition1.lean` — the rest of §3.3: a fully
  general "agreement" lemma (`⊢`/`⊨` depend on `typing` only through its
  restriction to the labels actually referenced, for *any* use of `NOT`)
  and a "stratified monotonicity" lemma built on it; Definition 4
  (`Typing(G,S,strat)`, built stratum-by-stratum, each stratum reusing
  Lemma 1's construction with an added "agrees with the previous stratum"
  constraint); and Proposition 1 (`Typing(G,S,strat)` is a correct typing of
  `G` by `S`, for any stratified, well-formed — `Schema.Closed` — schema).
- `ShexLean/Shex2017Schemas/Lemma2.lean` — Lemma 2 (stratification-
  independence of `Typing(G,S,strat)`), proved in full (no `sorry`;
  `#print axioms` shows only `propext`/`Classical.choice`/`Quot.sound`) —
  the paper itself only gives a proof sketch for this one. Built on: a
  Fusion lemma (revealing a schema's labels in one batch vs. two nested
  batches gives the same `maxTypingAgreeing` result, via a "whole object is
  itself a candidate" argument rather than per-candidate reasoning); a Swap
  lemma (two batches that each individually depend only on a common base,
  not on each other, can be revealed in either order); a canonical process
  `cont1` that repeatedly reveals the least-valued remaining batch under
  some fixed stratification until every label is settled; an Independence
  lemma (`cont1`'s final answer doesn't change if the first step instead
  reveals *any* other valid batch, via Swap and strong induction on the
  number of remaining labels — the mathematical heart of the proof); and a
  chaining argument showing `cont1` agrees with `Typing4` along *any* valid
  stratification's own checkpoints, hence `Typing4 strat1 = Typing4 strat2`
  for arbitrary `strat1`, `strat2`. (An earlier `combineStrat`/checkpoint-
  alignment approach, also complete and kept in the file as
  `Typing4_combineStrat`, turned out unable to reach the fully general
  case — no fixed linearization can align with an *arbitrary* second
  stratification's ordering of mutually-independent labels — which is what
  motivated the `cont1`/Independence route that closes it instead.)
- `ShexLean/Shex2017Schemas/ShapesSem.lean` — Definitions 5 and 6, closing
  out §3.3: `Schema.maximalCorrectTyping` (`Typing(G,S)`, Definition 5 —
  pick any stratification witnessing `S.StratifiedNegation` and take
  `Typing(G,S,strat)`), shown well-defined regardless of the choice
  (`maximalCorrectTyping_eq_Typing4`, immediate from Lemma 2) and correct
  (`maximalCorrectTyping_correct`, immediate from Proposition 1); and
  `Schema.ShapesSem` (Definition 6, `SHAPES_SEM` itself — node `n` has shape
  `L` from `S` iff `(n,L) ∈ Typing(G,S)`), with `shapesSem_iff_typing4`
  recording that it too can be tested against any stratification.
- `ShexLean/Shex2017Schemas/Algorithm1.lean` — Algorithm 1 (§4.1): the
  paper's actual iterative-refinement procedure (`refine`) for computing
  `Typing(G,S,strat)` — per stratum, start from every possible node-type
  association for the new labels (keeping the previous stratum's typing
  frozen) and repeatedly strip out any association currently failing `⊢`,
  until nothing more changes. Proved equal to `Typing4` (no `sorry`), via:
  a generic order-theoretic fact that iterating any decreasing self-map of
  a finite type stabilizes within its cardinality's number of steps
  (`Finset.decreasing_iterate_fixed`); a per-stratum core lemma
  (`refine1_eq_maxTypingAgreeing`) showing the fixed-point refinement
  equals `maxTypingAgreeing` (Definition 4's own per-stratum construction)
  via mutual inclusion, reusing `Satisfies.agree` and
  `Satisfies.stratMono` from `Proposition1.lean`; and a chaining induction
  (`refineAlg_eq_stratTypingSeq`) across all strata giving
  `algorithm1_correct : Algorithm1 G S strat = Typing4 G S strat`. So
  Algorithm 1 really does compute the semantics Definition 4 claims for it.
- `ShexLean/Shex2017Schemas/Algorithm2.lean` — Algorithm 2/Proposition 2
  (§4.2): the recursive, cycle-detecting `prove(n, L, Hyp)` procedure that
  decides `(n, L) ∈ Typing(G, S, strat)` without building the whole typing,
  by visiting only the portion of the dependency graph reachable from
  `(n, L)` and trusting an ancestor already on the call stack (rather than
  re-deriving it) to handle positive recursive cycles. Proved fully correct
  (`prove_correct`, no `sorry`) — a materially harder result than
  Algorithm 1's, since the paper's own proof sketch for Proposition 2
  covers only termination, not correctness at all. Built on: a
  neighbor-local strengthening of `Satisfies.agree`/`Satisfies.stratMono`
  (`Satisfies.agreeLocal`/`Satisfies.stratMonoLocal` — `⊢` depends on
  `typing` only through actual graph-neighbors of the node in question, not
  every node in `G`, which is what lets `prove` get away with tracking a
  local `Dep`/`Hyp` instead of a whole typing); completeness
  (`completeness_step`, `(n,L) ∈ Typing4 → prove` confirms it — a clean
  induction with no circularity, since extending `Hyp` with an already-known
  member needs no further justification); and soundness
  (`soundness_step`, `prove` confirming `(n,L) → (n,L) ∈ Typing4` — the
  hard direction, needing a genuine witness typing `T := stratTypingSeq i
  ∪ (support of the whole computation, restricted to same-stratum content)`,
  shown correct via `subset_maxTypingAgreeing`, with `T` fixed once from the
  outermost call and threaded unchanged through the recursion so that a
  descendant's dependency chain looping back to `(n, L)` itself — a genuine
  positive cycle — never needs `(n, L)`'s own correctness re-derived first,
  only its `T`-membership, which is immediate by construction).
- `ShexLean/Shex2017Schemas/examples/` — every numbered example from the
  paper, one file per example (`ExampleN_slug.lean`), each combining the
  worked-out proof with display text generated from the *real* `Schema`/
  `Graph`/`Typing` values (`Render.lean`) and true/false claims computed
  via `renderDecide (satisfies_decidable …)` (`ShexLean/InductiveRDF/
  Decidable.lean`, see "Decidability" above) rather than hand-transcribed;
  a later example's file imports an earlier one when it genuinely reuses
  its definitions (e.g. Example 3 imports Example 2 for `G₂`/`S₁`):
  - `Example1_introduction.lean` — the paper's §1 Introductory Example
    (`S₀`/`G₀`: users, programmers, clients and issues), a regression check
    exercising `AND`/`someOf`/`eachOf`/repetition together, with its typing
    proved correct (Definition 2) for all 18 node/shape associations it
    induces.
  - `Example2_issue_tracker.lean` — a recursive `<IssueSh>` schema over two
    issues that report on each other (`G₂`/`S₁`), with `typing_1` proved
    correct.
  - `Example3_typings.lean` — the other three typings of `G₂` by `S₁`:
    `typing_2`/`typing_4` proved correct, `typing_3` proved *not* correct
    (the paper's own counterexample).
  - `Example4_negation_recursion.lean` — `NOT` mixed with mutual recursion
    gives two contradicting correct typings, and the schema is not with
    stratified negation.
  - `Example5_stratification.lean` — a schema mixing `NOT` and recursion
    that *is* with stratified negation, with a witness stratification.
  - `Example6_prove_motivation.lean` — a new graph `G₃` over Example 5's
    `S₃`, motivating Algorithm 2 (§4.2): `ex:n1` has shape `<L1>`, proved
    directly against the declarative semantics (`⊢`/`⊨`).
  - `Example7_trace.lean` — Algorithm 2's own execution trace of
    `prove(ex:n1, <L1>, [])` on `G₃`/`S₃`: all six recursive-call outcomes
    (three `true`, three `false`) are computed live via
    `satisfies_decidable`/`native_decide` against the declarative
    semantics (`⊢`/`⊨`) — Algorithm 2's own recursive `prove` procedure
    isn't itself formalized as executable code (it's `Algorithm2.lean`'s
    *subject*, related to `⊢`/`⊨` only via Proposition 2), but the
    semantics it's proved equal to now genuinely is.

## What's implemented (2025 paper: Shape Expressions with Inheritance)

It lives in its own `ShexLean.Inheritance` Lean namespace (the directory
is `ShexLean/Shex2025Inheritance/` — namespace and directory names don't
have to match in Lean, and this one is kept stable across the directory
rename since every theorem statement in the 2017 code below refers to it)
so its `Schema`/`ShapeExpr`/etc. don't clash with the 2017 ones, but
reuses the paper-independent vocabulary directly: `ShexLean/Common/RDF.lean`
and `ShexLean/Common/Typing.lean` (`ShapeLabel`/`Typing`/`Typing.has`) are
imported unchanged, and `ShexLean/Common/DisjointUnion.lean` is shared with
the 2017 side's own triple-expression semantics.

- `ShexLean/Shex2025Inheritance/Syntax.lean` — Definitions 1-3: the
  `ShapeExpr`/`TripleExpr` grammar (`extends`, `closed`/`extra`, abstract
  node constraints), `Schema = (Y, X, def, A)`, and the extension hierarchy
  `H_S` (`Schema.anc`/`Schema.desc`, via `Relation.ReflTransGen` on the
  `extends`-edge relation). References `@z` are not a `ShapeExpr`
  constructor: Definition 1's grammar for `def`'s codomain has no `@z`
  alternative (it only ever occurs inside a triple constraint `p @z`), and
  Table 2's own rule for `@z` is a zero-recursion `typing` lookup, so it is
  inlined directly in `Semantics.lean` instead.
- `ShexLean/Shex2025Inheritance/Semantics.lean` — Tables 1-3: the three
  satisfiability relations (`M,τ⊨e`, `n,τ⊨s`, `M,τ⊨s`), as
  `SatisfiesEFuel`/`SatisfiesFuel`/`SatisfiesMFuel`. Unlike the 2017
  formalization, these can't be plain structural recursion on the AST:
  Table 3's `extends` rule genuinely recurses into *other labels' own
  definitions* (an ancestor's `ext-te(x)`/`restr(x)`), which the paper
  itself has to prove terminates separately (its own Lemma 1, via
  acyclicity of `H_S`). So for now these are `Fuel`-bounded
  under-approximations (fuel decremented on every recursive call, `False`
  on exhaustion) — a total Lean function by construction, exactly the fuel
  idiom already used in `ShexLean/Shex2017Schemas/Algorithm1.lean`/
  `Algorithm2.lean`.
- `ShexLean/Shex2025Inheritance/Termination.lean` — the real Lemma 1,
  **fully proved, no `sorry`** (`#print axioms lemma1` shows only
  `propext`/`Classical.choice`/`Quot.sound`): a large-enough `Fuel` makes
  `SatisfiesFuel`/`SatisfiesMFuel`/`SatisfiesEFuel` stop depending on
  `Fuel` at all. Built in two layers:
  - `Schema.ExtAcyclic` (`H_S` has no cycle) and `Schema.extRank` (`:=
    (S.anc x).card`, the standard rank-function-on-a-DAG trick, strictly
    decreasing along every `H_S` edge under acyclicity) — correct and
    reusable, but *not* actually load-bearing for the theorem this file
    ends up proving (see next point).
  - `Schema.WellFormedExtends` — a documented *extra* hypothesis beyond
    the paper's literal text, added after `ExtAcyclic`/`extRank` turned
    out insufficient on their own: Definition 3 builds `H_S`'s edges only
    from a label's *outermost* `extends X h [and u]` clause, but the
    grammar technically allows `u` (`restr(x)`) to itself contain a
    further, *unrelated* `extends`, invisible to that edge relation but
    still something the runtime evaluator would chase. The paper's
    one-sentence proof sketch doesn't address this case and none of its
    own examples exercise it. `WellFormedExtends` rules it out directly
    (every `extends` node, wherever nested, must itself be one of the two
    shallow forms Definition 2 describes) — strictly stronger than mere
    acyclicity, but enough to make every `extends`-hop's target provably
    bounded by a fixed, schema-wide constant (`Schema.maxDefSize`), which
    is what the actual stabilization induction (`stableE` → `stableM` →
    `stableFuel`, following the same one-way dependency chain as the
    definitions themselves) is built on. Packaged as fuel-free
    `Satisfies`/`SatisfiesM`/`SatisfiesE` definitions plus the `lemma1`
    theorem itself.
- `ShexLean/Shex2025Inheritance/Stratification.lean` — Definitions 5-6: the
  dependency graph `D_S` (`Schema.dep`/`depExtends`/`depShapeNeg`/
  `depExtraNeg`, built from a single recursive walk over a label's
  definition, `ShapeExpr.depsAux`, tracking whether the current position
  is under an odd number of `not` — mirrors the 2017 formalism's
  `depsAux` in spirit, but now collects *three* label-sets at once, since
  `[closed][extra P]⟨e⟩` being a first-class shape modifier gives a third,
  new kind of dependency, `dep-extra-neg`, with no 2017 analogue), the
  "`dep` subsumes `dep-shape-neg`/`dep-extra-neg`" fact the paper states
  as an aside (`Schema.dep_of_depShapeNeg`/`dep_of_depExtraNeg`), and
  Definition 6 (`Schema.WellDefined` — `H_S` acyclic, `Schema.ExtAcyclic`,
  moved here from `Termination.lean` to match the paper's own order, plus
  no negative-dependency cycle in `D_S`, `Schema.NegCycle`, phrased via
  `Relation.ReflTransGen` rather than an explicit path/list, mirroring
  `ExtAcyclic`'s own style).
- `ShexLean/Shex2025Inheritance/CorrectTyping.lean` — Definition 4
  (`Schema.CorrectTyping`, stated directly against `Satisfies` from
  `Termination.lean`, with the new abstract-label case: `(n,z) ∈ τ` for
  `z ∈ A` requires *some* non-abstract descendant of `z` to be satisfied,
  not `z`'s own definition).
- `ShexLean/Shex2025Inheritance/examples/` — every numbered example from
  the paper, one file per example (`ExampleN_slug.lean`), each combining
  the worked-out proof with display text generated from the real `Schema`/
  `Graph` values and true/false claims computed via `renderDecide
  (satisfiesFuel_decidable …)` (`Decidable.lean`, see "Decidability"
  above) rather than hand-transcribed; a later example's file imports an
  earlier one when it genuinely reuses its definitions:
  - `Example1_figures.lean` — the full `ColouredCircle` schema/graph
    (`S_fig1`/`G_fig1`, Fig. 1/2), proving every headline claim
    (`c1_satisfies_Coord`, …, `f1_satisfies_ColouredCircle` — the
    multiple-inheritance punchline). Also hosts `H_{S1}`'s own ancestor
    facts (Fig. 3, `hancCircle`/`hancColouredFigure`/
    `hancSetCircleColouredFigure`) since `f1_satisfies_ColouredCircle`
    needs them for its own rule-18 partition, even though the extension
    hierarchy is Example 2's own subject.
  - `Example2_extension_hierarchy.lean` — imports Example 1 and re-displays
    its `H_{S1}` ancestor facts (the one that shows `Figure` counted once,
    not twice, for `ColouredCircle`).
  - `Example3_triple_match.lean` — the triple expression
    `e = p @T_even ; (p @T_<5* | p @T_str)` proved to match/not match all
    four of the paper's example triple sets. Also hosts the ambient schema
    `S_ex5` (Example 5's own schema) and node constraints, since Examples
    3-5 all state their claims against it.
  - `Example4_closed_extra.lean` — imports Example 3 for `S_ex5`/`M24`/
    `M246`/`M2a`/`M24a`; the `closed`/`extra` semantics on the same triple
    sets.
  - `Example5_extends.lean` — imports Example 3 for `S_ex5`; the
    `extends`-chain schema (labels `x0..x6`) with `M24,τ ⊨ def(x1)` proved
    by explicitly constructing the `extends` rule's partition (the one
    proof here that exercises `Schema.anc`/`Schema.ancSet`, via
    `Relation.ReflTransGen`).
  - `Example6_dependency_graph.lean` — three small schemas `S1`/`S2`/`S3`
    and their 13 enumerated dependency-relation facts.
  - `Example7_well_defined.lean` — imports Example 6 for `S1`/`S2`/`S3`;
    their well-definedness verdicts.

  The generic `ofShape`-lifting helper lemmas several of these files need
  (`ofShape_of_Me_eq_self`/`singleton_tc_ofShape`/
  `Me_eq_self_of_props_subset`) live in `Semantics.lean` itself instead,
  since they aren't tied to any particular example.
- `ShexLean/Shex2025Inheritance/Proposition1.lean` — Definition 7
  (`Stratification`, edge-based, plus the path form the paper states it
  with), Definition 8 (`stratTypingSeq`/`Typing8`, the maximal typing
  `τ_max(S,σ,G)`), and Proposition 1 itself, all proved, no `sorry`. Three
  real subtleties surfaced and were fixed along the way (documented at
  length in the file): Table 3's `Me`/`Mnotin` make `SatisfiesMFuel`
  non-monotone in `τ` even without negation (a Lean-verified counterexample
  is in the file's docstring), fixed via another paper-implicit invariant
  (`Schema.WellFormedExtra`, "(*)" from the paper's own Proposition 1
  appendix proof); `not` needs *latching* negative-dependency tracking
  rather than the paper's literal "odd parity", plus a new restriction
  that `not` never contains `extends` (`Schema.NotIsExtendsFree`); and —
  unlike the 2017 formalization, where `Satisfies` never consults the
  schema at all — lifting correctness across `stratRestrict`'s strata
  needed a genuinely new schema-invariance argument
  (`Satisfies_stratRestrict_agree`, via a `schemaAgreeM`/`schemaAgreeFuel`
  pair mirroring `Termination.lean`'s `stableE`/`stableM`/`stableFuel`
  chain, but varying the *schema* instead of the fuel) closing the gap
  that blocked a direct 2017-style port of `stratTypingSeq_correct`'s
  inductive step.
- `ShexLean/Shex2025Inheritance/Lemma2.lean` — Lemma 2 (§4.3):
  `τ_max(S,σ,G)` does not depend on the stratification chosen, proved in
  full, no `sorry`. Ports 2017's own `Lemma2.lean` (Fusion/Swap/a
  schedule-agnostic `remainingMin`-batch-revealing process
  `cont1`/Independence — the paper only sketches this proof), which
  transfers almost unchanged in *shape*. What doesn't transfer for free:
  2017's `Satisfies` never consults the schema, so "restrict to a
  self-contained label set" was free; here it first generalizes
  `Proposition1.lean`'s stratum-specific schema-invariance argument
  (`Satisfies_stratRestrict_agree`) to an arbitrary `D_S`-closed label set
  (`Schema.restrictLabels`, `Satisfies_restrictLabels_agree`), since
  `cont1`'s schedule-agnostic batches aren't shaped like strata.
- `ShexLean/Shex2025Inheritance/Algorithm1.lean` — the §5 validation/
  refinement algorithm for ShEx with inheritance, ported from the 2017
  formalism's own `Algorithm1.lean` the same way `Lemma2.lean` was: proved
  fully correct (`algorithm1_correct : Algorithm1 = Typing8`,
  `algorithm1_correctTyping`), no `sorry`.
- `ShexLean/Shex2025Inheritance/Decidable.lean`,
  `ShexLean/Shex2025Inheritance/Render.lean` — decidability and rendering
  for this formalism, see "Decidability" above.

## CLI infrastructure (`examples/`)

- `examples/Example.lean`, `examples/Registry.lean` — a small `Example`
  record (name, summary, schema/graph/typing as text) wrapping each worked
  example, from either paper, for display, plus a registry the executable
  lists and selects from.
- `examples/Proof.lean`, `examples/ProofRegistry.lean` — a `ProofItem`
  record (name, summary, and the `.lean` file path containing the theorem)
  for theorems shown by their actual Lean source rather than curated text
  — covering both papers' Lemma 1/Proposition 1/Lemma 2/algorithms
  (2017, `Shex2017Schemas/`) and Lemma 1/Proposition 1/Lemma 2 (2025,
  `Shex2025Inheritance/`).

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
  2017 — Semantics and Validation of Shapes Schemas for RDF:
    schemas2017-example1-introduction — §1 Introductory Example: users, programmers, clients, issues.
    schemas2017-example2-issue-tracker — Recursive <IssueSh> schema, two issues reporting on each other.
    schemas2017-example3-typings — Four typings of G₂ by S₁ from Ex. 2; which are correct (Def. 2).
    ...
  2025 — Shape Expressions with Inheritance:
    inheritance2025-example1-figures — Fig. 1/2's full ColouredCircle schema: f1 is both a Circle and a ColouredFigure.
    inheritance2025-example2-extension-hierarchy — H_S1 (Fig. 3): anc(ColouredCircle) counts Figure once, not twice.
    inheritance2025-example3-triple-match — Triple expression p@T_even;(p@T_<5*|p@T_str) matched against three sets.
    ...

Proofs:
  2017 — Semantics and Validation of Shapes Schemas for RDF:
    schemas2017-lemma1 — A negation-free schema has a maximal correct typing (§3.3).
    schemas2017-proposition1 — Typing(G,S,strat) is a correct typing of G by S (§3.3).
    ...
  2025 — Shape Expressions with Inheritance:
    inheritance2025-lemma1 — Evaluation of n,τ⊨def(z) always terminates (§4.2).
    inheritance2025-proposition1 — τ_max(S,σ,G) is a correct typing of G by S (§4.3).
    inheritance2025-lemma2 — τ_max(S,σ,G) doesn't depend on the stratification chosen (§4.3).
```

Names are prefixed `schemas2017-`/`inheritance2025-` so it's clear which
paper each item belongs to, and the listing groups them under a per-paper
sub-header; every summary is kept to one line.

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

Every part of that output is generated, not transcribed: `schemaText`/
`graphText`/`typingText` are pretty-printed straight from the real `Schema`/
`Graph`/`Typing` Lean values (`Render.lean`), and the `correct = true`
verdict is a `native_decide` computation of `Schema.CorrectTyping` against
the `Decidable` instances in "Decidability" above, run *at CLI runtime* —
not a value asserted once in a proof and copied into a string. The
underlying theorem that this typing is correct (`typing_1_correct` etc.)
still lives in the corresponding `.lean` file and is checked by `lake
build`; the CLI's `true`/`false` is an independent, second computation of
the same fact.

Print a proof's Lean source (statement and tactic proof) — unlike
examples, this reads the `.lean` file directly, so run it from the project
root:

```
lake exe shex_lean run schemas2017-lemma1
```

Open the project in an editor with Lean support (e.g. VS Code with the Lean
4 extension) to step through the definitions and proofs interactively, or
explore them from the command line with `lake env lean --run`.
