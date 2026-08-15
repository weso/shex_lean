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
- `ShexLean/ShapesSem.lean` — Definitions 5 and 6, closing out §3.3:
  `Schema.maximalCorrectTyping` (`Typing(G,S)`, Definition 5 — pick any
  stratification witnessing `S.StratifiedNegation` and take
  `Typing(G,S,strat)`), shown well-defined regardless of the choice
  (`maximalCorrectTyping_eq_Typing4`, immediate from Lemma 2) and correct
  (`maximalCorrectTyping_correct`, immediate from Proposition 1); and
  `Schema.ShapesSem` (Definition 6, `SHAPES_SEM` itself — node `n` has shape
  `L` from `S` iff `(n,L) ∈ Typing(G,S)`), with `shapesSem_iff_typing4`
  recording that it too can be tested against any stratification.
- `ShexLean/Algorithm1.lean` — Algorithm 1 (§4.1): the paper's actual
  iterative-refinement procedure (`refine`) for computing `Typing(G,S,strat)`
  — per stratum, start from every possible node-type association for the new
  labels (keeping the previous stratum's typing frozen) and repeatedly strip
  out any association currently failing `⊢`, until nothing more changes.
  Proved equal to `Typing4` (no `sorry`), via: a generic order-theoretic fact
  that iterating any decreasing self-map of a finite type stabilizes within
  its cardinality's number of steps (`Finset.decreasing_iterate_fixed`); a
  per-stratum core lemma (`refine1_eq_maxTypingAgreeing`) showing the
  fixed-point refinement equals `maxTypingAgreeing` (Definition 4's own
  per-stratum construction) via mutual inclusion, reusing `Satisfies.agree`
  and `Satisfies.stratMono` from `Proposition1.lean`; and a chaining
  induction (`refineAlg_eq_stratTypingSeq`) across all strata giving
  `algorithm1_correct : Algorithm1 G S strat = Typing4 G S strat`. So
  Algorithm 1 really does compute the semantics Definition 4 claims for it.
- `ShexLean/Algorithm2.lean` — Algorithm 2/Proposition 2 (§4.2): the
  recursive, cycle-detecting `prove(n, L, Hyp)` procedure that decides
  `(n, L) ∈ Typing(G, S, strat)` without building the whole typing, by
  visiting only the portion of the dependency graph reachable from
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
  (`ShexLean/Proposition1.lean`), Lemma 2 (`ShexLean/Lemma2.lean`),
  Definitions 5-6/`SHAPES_SEM` (`ShexLean/ShapesSem.lean`), Algorithm 1
  (`ShexLean/Algorithm1.lean`), and Algorithm 2/Proposition 2
  (`ShexLean/Algorithm2.lean`).

## Shape Expressions with Inheritance (2025 extension)

`ShexLean/Inheritance/` is an incremental port of a second, later paper:

> Iovka Boneva, Jose Emilio Labra Gayo, Eric Prud'hommeaux, Katherine
> Thornton, Andra Waagmeester, *"Shape Expressions with Inheritance"*,
> arXiv:2503.24299, 2025.

It is a genuine second formalism (an `extends`/`abstract` mechanism on top
of ShEx 2.1), not a strict extension of the 2017 one — node constraints
are now an arbitrary predicate rather than a concrete `ValueDescr`,
`closed`/`extra` are first-class shape modifiers, and shapes can extend
one another along a new *extension hierarchy*. It lives in its own
`ShexLean.Inheritance` namespace so its `Schema`/`ShapeExpr`/etc. don't
clash with the 2017 ones, but reuses the paper-independent vocabulary
directly: `ShexLean/RDF.lean` and `ShexLean/Typing.lean`
(`ShapeLabel`/`Typing`/`Typing.has`) are imported unchanged.

- `ShexLean/Inheritance/Syntax.lean` — Definitions 1-3: the
  `ShapeExpr`/`TripleExpr` grammar (`extends`, `closed`/`extra`, abstract
  node constraints), `Schema = (Y, X, def, A)`, and the extension hierarchy
  `H_S` (`Schema.anc`/`Schema.desc`, via `Relation.ReflTransGen` on the
  `extends`-edge relation). References `@z` are not a `ShapeExpr`
  constructor: Definition 1's grammar for `def`'s codomain has no `@z`
  alternative (it only ever occurs inside a triple constraint `p @z`), and
  Table 2's own rule for `@z` is a zero-recursion `typing` lookup, so it is
  inlined directly in `Semantics.lean` instead.
- `ShexLean/Inheritance/Semantics.lean` — Tables 1-3: the three
  satisfiability relations (`M,τ⊨e`, `n,τ⊨s`, `M,τ⊨s`), as
  `SatisfiesEFuel`/`SatisfiesFuel`/`SatisfiesMFuel`. Unlike the 2017
  formalization, these can't be plain structural recursion on the AST:
  Table 3's `extends` rule genuinely recurses into *other labels' own
  definitions* (an ancestor's `ext-te(x)`/`restr(x)`), which the paper
  itself has to prove terminates separately (its own Lemma 1, via
  acyclicity of `H_S`). So for now these are `Fuel`-bounded
  under-approximations (fuel decremented on every recursive call, `False`
  on exhaustion) — a total Lean function by construction, exactly the fuel
  idiom already used in `ShexLean/Algorithm1.lean`/`Algorithm2.lean`.
- `ShexLean/Inheritance/Termination.lean` — the real Lemma 1, **fully
  proved, no `sorry`** (`#print axioms lemma1` shows only
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
- `ShexLean/Inheritance/Stratification.lean` — Definitions 5-6: the
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
- `ShexLean/Inheritance/CorrectTyping.lean` — Definition 4
  (`Schema.CorrectTyping`, stated directly against `Satisfies` from
  `Termination.lean`, with the new abstract-label case: `(n,z) ∈ τ` for
  `z ∈ A` requires *some* non-abstract descendant of `z` to be satisfied,
  not `z`'s own definition).
- `ShexLean/Inheritance/Examples.lean` — regression checks against the
  files above, playing the same role as `ShexLean/Examples.lean`/
  `examples/Introduction.lean` do for the 2017 formalism: Example 3's
  triple expression `e = p @T_even ; (p @T_<5* | p @T_str)` proved to
  match/not match all four of the paper's example triple sets; Example 5's
  schema (labels `x0..x6`) with `M24,τ ⊨ def(x1)` proved by explicitly
  constructing the `extends` rule's partition (the one proof here that
  exercises `Schema.anc`/`Schema.ancSet`, via `Relation.ReflTransGen`); and
  a first slice of §2's motivating example (the `Attribute` shape and node
  `a1`, Fig. 1/2) — the fuller multiple-inheritance `ColouredCircle` chain
  of that example is left for later.

- `ShexLean/Inheritance/Proposition1.lean` — Definition 7 (`Stratification`,
  edge-based, plus the path form the paper states it with), Definition 8
  (`stratTypingSeq`/`Typing8`, the maximal typing `τ_max(S,σ,G)`), and
  Proposition 1 itself, all proved, no `sorry`. Three real subtleties
  surfaced and were fixed along the way (documented at length in the file):
  Table 3's `Me`/`Mnotin` make `SatisfiesMFuel` non-monotone in `τ` even
  without negation (a Lean-verified counterexample is in the file's
  docstring), fixed via another paper-implicit invariant
  (`Schema.WellFormedExtra`, "(*)" from the paper's own Proposition 1
  appendix proof); `not` needs *latching* negative-dependency tracking
  rather than the paper's literal "odd parity", plus a new restriction that
  `not` never contains `extends` (`Schema.NotIsExtendsFree`); and — unlike
  the 2017 formalization, where `Satisfies` never consults the schema at
  all — lifting correctness across `stratRestrict`'s strata needed a
  genuinely new schema-invariance argument
  (`Satisfies_stratRestrict_agree`, via a `schemaAgreeM`/`schemaAgreeFuel`
  pair mirroring `Termination.lean`'s `stableE`/`stableM`/`stableFuel`
  chain, but varying the *schema* instead of the fuel) closing the gap that
  blocked a direct 2017-style port of `stratTypingSeq_correct`'s inductive
  step.

- `ShexLean/Inheritance/Lemma2.lean` — Lemma 2 (§4.3): `τ_max(S,σ,G)` does
  not depend on the stratification chosen, proved in full, no `sorry`. Ports
  2017's own `ShexLean/Lemma2.lean` (Fusion/Swap/a schedule-agnostic
  `remainingMin`-batch-revealing process `cont1`/Independence — the paper
  only sketches this proof), which transfers almost unchanged in *shape*.
  What doesn't transfer for free: 2017's `Satisfies` never consults the
  schema, so "restrict to a self-contained label set" was free; here it
  first generalizes `Proposition1.lean`'s stratum-specific schema-invariance
  argument (`Satisfies_stratRestrict_agree`) to an arbitrary `D_S`-closed
  label set (`Schema.restrictLabels`, `Satisfies_restrictLabels_agree`),
  since `cont1`'s schedule-agnostic batches aren't shaped like strata.

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
  shapes-sem — Definitions 5-6 (§3.3): the maximal correct typing Typing(G,S) is well-defined and correct, and SHAPES_SEM itself.
  algorithm1 — Algorithm 1 (§4.1): the per-stratum iterative-refinement procedure `refine` computes exactly Typing(G,S,strat) (Definition 4).
  algorithm2 — Algorithm 2/Proposition 2 (§4.2): the recursive, cycle-detecting `prove` algorithm decides Typing(G,S,strat)-membership correctly, without building the whole typing.
  inheritance-lemma1 — Shape Expressions with Inheritance (2025), Lemma 1 (§4.2): evaluation of n,τ⊨def(z) always terminates.
  inheritance-proposition1 — Shape Expressions with Inheritance (2025), Proposition 1 (§4.3): the maximal typing τ_max(S,σ,G) is a correct typing of G by S.
  inheritance-lemma2 — Shape Expressions with Inheritance (2025), Lemma 2 (§4.3): τ_max(S,σ,G) does not depend on which stratification σ of S is chosen.
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
