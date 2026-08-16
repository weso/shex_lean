import ShexLean.Common.RDF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
An alternative representation of RDF graphs as *inductive triple graphs*,
following Labra Gayo, Jeuring, Álvarez Rodríguez, "Inductive representations
of RDF Graphs" (2013), §2.2 ("Inductive triple graphs") and §4 ("Functional
representation of RDF Graphs") — a specialization of Erwig's inductive
functional graphs to RDF's "predicates are nodes too" shape.

The paper's `TGraph a`/`TContext a` (§2.2):

```
data TGraph a = Empty | TContext a :& TGraph a
type TContext a = (a, [(a,a)], [(a,a)], [(a,a)])
```

i.e. a graph is either empty, or a *context* — a node together with its
predecessors, successors, and (since an edge label can itself be a node,
Fig. 3) the pairs it relates when acting as a predicate — extending a
smaller graph. Ported below as `TContext`/`TGraph`. This file only defines
the datatype and the two conversions to/from this project's existing
`Finset Triple`-based `Graph` (`ShexLean.Common.RDF`); whether this
representation actually buys *decidability* of `Satisfies`/`Matches`
(`ShexLean.Shex2017Schemas.Semantics`) is investigated separately, in
`ShexLean.Shex2017Schemas.Decidable` — spoiler: it doesn't, see that file's
docstring.

Not ported: the paper's `RDFGraph = Ground (TGraph Resource) | Exists
(BNodeId -> RDFGraph)` (§4), which models a blank node as a
higher-order/existential binder (`Exists`) rather than a concrete
identifier. This project already represents blank nodes concretely as
`RDFNode.bnode : BNodeId → RDFNode` (`ShexLean.Common.RDF`), matching the
2017/2025 papers being formalized elsewhere in this repo, so the `Ground`/
`Exists` split has no counterpart here — `Resource` below is just
`RDFNode` itself.
-/

namespace ShexLean.InductiveRDF

open ShexLean (RDFNode IRI Triple Graph)

/-- §4's `Resource`: the shared node/edge-label universe. The paper unifies
nodes and edge labels into one type, since an IRI can be both a node and a
predicate; we reuse `RDFNode` for both roles, wrapping a predicate `IRI` as
`RDFNode.iri` wherever it appears as an edge label below. -/
abbrev Resource := RDFNode

/-- §2.2's `TContext a = (a, [(a,a)], [(a,a)], [(a,a)])`: the context of
`node`, i.e. `node` together with its predecessors, successors, and (Fig. 3)
the pairs it relates when used as an edge label. `pred` pairs each
predecessor with the edge label pointing *from* it; `succ` pairs each edge
label with the successor it points *to*.

`rels` is never populated by `ofGraph`/`toGraph` below: this repo's
`Triple.pred : IRI` is a plain string, never literally one of a triple's own
subject/object `RDFNode`s, so the "edge that is also a node" scenario the
paper motivates `rels` with (Fig. 3, §2.2) cannot arise for graphs built via
`ofGraph`. Kept only so `TContext` matches the paper's shape exactly. -/
structure TContext where
  node : Resource
  pred : List (Subject × Resource)
  succ : List (Resource × Resource)
  rels : List (Resource × Resource)
  deriving Repr

/-- §2.2's `TGraph a = Empty | TContext a :& TGraph a`. -/
inductive TGraph where
  | empty : TGraph
  | ext   : TContext → TGraph → TGraph
  deriving Repr

/-! ### `Graph → TGraph`

Erwig's inductive graphs satisfy an invariant that makes decomposition
well-defined: a `Context` only ever records an edge to a node that is still
"in the rest of the graph" it extends — an edge to a node processed earlier
(so already unwound off the front of the `:&` chain) was already recorded
*there*, and would double-count if repeated. `buildContext`/`buildFrom`
below implement that invariant explicitly, processing nodes in a fixed
order `ns` and, for the node `n` at the head, only recording edges whose
other endpoint lies in `later := ns.tail.toFinset` (or *is* `n` itself, for
a self-loop, which — having no distinct "other endpoint" — is recorded once
in `succ` regardless of `later`). -/

/-- The context of `n`, recording only its edges to nodes still in `later`
(plus any self-loop at `n`, recorded once, in `succ`). Noncomputable only
because it goes via `Finset.toList` (itself noncomputable in Mathlib, since
`Finset`/`Multiset` pick a representative list via `Quot.out`); this doesn't
affect `decide`-based reasoning about it, only native code generation. -/
noncomputable def buildContext (n : Resource) (later : Finset Resource) (G : Graph) : TContext where
  node := n
  pred := (G.filter (fun t => t.obj = n ∧ t.subj ∈ later)).toList.map
            (fun t => (t.subj, RDFNode.iri t.pred))
  succ := (G.filter (fun t => t.subj = n ∧ (t.obj ∈ later ∨ t.obj = n))).toList.map
            (fun t => (RDFNode.iri t.pred, t.obj))
  rels := []

/-- Build a `TGraph` from `G`, processing the nodes listed in `ns` in order.
Called with `ns := G.nodes.toList` by `ofGraph`; kept as an explicit
recursion argument so each step's `later` set is exactly the (structurally
smaller) tail. -/
noncomputable def buildFrom : List Resource → Graph → TGraph
  | [], _ => .empty
  | n :: ns, G => .ext (buildContext n ns.toFinset G) (buildFrom ns G)

/-- `Graph → TGraph`: decompose `G` into an inductive triple graph, one
context per node of `G`. -/
noncomputable def ofGraph (G : Graph) : TGraph := buildFrom G.nodes.toList G

/-! ### `TGraph → Graph` -/

/-- The triples recorded directly in one context: `(source, label, node)`
for each `pred` entry (only when `label` is an `IRI`, always true for
contexts built by `buildContext`; `pred`'s source is already a `Subject`,
since it's `t.subj` for some real triple `t`) and `(node, label, target)`
for each `succ` entry — here `node` needs converting *to* a `Subject` via
`RDFNode.toSubject?` first (dropping the entry on `none`, which never
actually happens for contexts built by `buildContext`: `succ` is only ever
populated from a real triple's own `Subject` subject, so `c.node` is
always `Subject`-representable whenever `succ` is nonempty — see
`RoundTrip.lean`'s `mem_context_succ_triples` for the proof). -/
def TContext.toTriples (c : TContext) : List Triple :=
  c.pred.filterMap (fun (src, lbl) =>
    match lbl with
    | .iri p => some (⟨src, p, c.node⟩ : Triple)
    | _ => none) ++
  c.succ.filterMap (fun (lbl, tgt) =>
    match c.node.toSubject?, lbl with
    | some ns, .iri p => some (⟨ns, p, tgt⟩ : Triple)
    | _, _ => none)

/-- All triples recorded across a `TGraph`'s contexts. -/
def TGraph.toTriples : TGraph → List Triple
  | .empty => []
  | .ext c g => c.toTriples ++ TGraph.toTriples g

/-- `TGraph → Graph`: collect every context's triples back into a
`Finset Triple`. -/
def toGraph (g : TGraph) : Graph := g.toTriples.toFinset

end ShexLean.InductiveRDF
