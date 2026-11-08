import ShexLean.Common.RDF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
A different representation of RDF graphs: *inductive triple graphs*. It
follows Labra Gayo, Jeuring, Álvarez Rodríguez, "Inductive representations
of RDF Graphs" (2013):

* §2.2 ("Inductive triple graphs").
* §4 ("Functional representation of RDF Graphs").

This representation is a special case of the inductive functional graphs
of Erwig. In RDF, a predicate can also be a node. The representation
supports this.

The paper defines `TGraph a` and `TContext a` (§2.2):

```
data TGraph a = Empty | TContext a :& TGraph a
type TContext a = (a, [(a,a)], [(a,a)], [(a,a)])
```

Thus, a graph is one of these two items:

* The empty graph.
* A *context* that extends a smaller graph. A context is a node together
  with its predecessors, its successors, and the pairs that it relates
  when it is a predicate. (An edge label can also be a node, Fig. 3.)

This file gives `TContext` and `TGraph` in Lean. It defines only the
datatype and the two conversions between it and the `Graph` of this
project (`Finset Triple`, in `ShexLean.Common.RDF`).

Does this representation make `Satisfies` and `Matches`
(`ShexLean.Shex2017Schemas.Semantics`) decidable? The file
`ShexLean.Shex2017Schemas.Decidable` examines this question. The answer
is no. Refer to the docstring of that file.

This file does not include the `RDFGraph` type of the paper (§4):
`RDFGraph = Ground (TGraph Resource) | Exists (BNodeId -> RDFGraph)`. That
type uses a higher-order (existential) binder `Exists` for a blank node,
not a concrete identifier. This project uses a concrete identifier for
blank nodes: `RDFNode.bnode : BNodeId → RDFNode` (`ShexLean.Common.RDF`).
The 2017 and 2025 papers also do this. Thus, there is no `Ground`/`Exists`
split here, and `Resource` below is equal to `RDFNode`.
-/

namespace ShexLean.InductiveRDF

open ShexLean (RDFNode IRI Triple Graph)

/-- `Resource` of §4: one type for nodes and edge labels. The paper uses
one type for the two roles, because an IRI can be a node and also a
predicate. We use `RDFNode` for the two roles. Below, when a predicate
`IRI` is an edge label, we wrap it as `RDFNode.iri`. -/
abbrev Resource := RDFNode

/-- `TContext a = (a, [(a,a)], [(a,a)], [(a,a)])` of §2.2: the context of
`node`. The context contains `node`, its predecessors, its successors, and
the pairs that it relates when it is an edge label (Fig. 3).

* `pred` pairs each predecessor with the edge label that goes *from* it.
* `succ` pairs each edge label with the successor that it goes *to*.

`ofGraph` and `toGraph` below never put data in `rels`. In this project,
`Triple.pred : IRI` is a plain string. It is never one of the subject or
object `RDFNode`s of a triple. Thus, the paper's case "an edge that is
also a node" (Fig. 3, §2.2) cannot occur in a graph that `ofGraph` makes.
We keep `rels` only to make `TContext` have the same structure as in the
paper. -/
structure TContext where
  node : Resource
  pred : List (Subject × Resource)
  succ : List (Resource × Resource)
  rels : List (Resource × Resource)
  deriving Repr

/-- `TGraph a = Empty | TContext a :& TGraph a` of §2.2. -/
inductive TGraph where
  | empty : TGraph
  | ext   : TContext → TGraph → TGraph
  deriving Repr

/-! ### `Graph → TGraph`

The inductive graphs of Erwig have an invariant. This invariant makes
decomposition well-defined. A `Context` records an edge only if the other
node of the edge is still in the rest of the graph that the context
extends. An edge to a node from an earlier step is already in the context
of that node. If you record it again, you count it two times.

`buildContext` and `buildFrom` below implement this invariant explicitly:

* They process the nodes in a fixed order `ns`.
* For the node `n` at the head, they record an edge only if its other
  endpoint is in `later := ns.tail.toFinset`.
* A self-loop at `n` has no different "other endpoint". They record it one
  time, in `succ`, and do not look at `later`. -/

/-- The context of `n`. It records only the edges of `n` to nodes in
`later`, and a self-loop at `n` one time, in `succ`.

This definition is noncomputable only because it uses `Finset.toList`.
`Finset.toList` is noncomputable in Mathlib, because `Finset` and
`Multiset` use `Quot.out` to select a representative list. This has no
effect on proofs that use `decide`. It has an effect only on native code
generation. -/
noncomputable def buildContext (n : Resource) (later : Finset Resource) (G : Graph) : TContext where
  node := n
  pred := (G.filter (fun t => t.obj = n ∧ t.subj ∈ later)).toList.map
            (fun t => (t.subj, RDFNode.iri t.pred))
  succ := (G.filter (fun t => t.subj = n ∧ (t.obj ∈ later ∨ t.obj = n))).toList.map
            (fun t => (RDFNode.iri t.pred, t.obj))
  rels := []

/-- Make a `TGraph` from `G`. Process the nodes in `ns` in their order.
`ofGraph` calls this function with `ns := G.nodes.toList`. We keep `ns` as
an explicit recursion argument. Thus, the `later` set of each step is the
tail, which is structurally smaller. -/
noncomputable def buildFrom : List Resource → Graph → TGraph
  | [], _ => .empty
  | n :: ns, G => .ext (buildContext n ns.toFinset G) (buildFrom ns G)

/-- `Graph → TGraph`: decompose `G` into an inductive triple graph, with
one context for each node of `G`. -/
noncomputable def ofGraph (G : Graph) : TGraph := buildFrom G.nodes.toList G

/-! ### `TGraph → Graph` -/

/-- The triples that one context records directly:

* `(source, label, node)` for each `pred` entry. This occurs only if
  `label` is an `IRI`. This is always true for a context from
  `buildContext`. The `source` of `pred` is already a `Subject`, because it
  is `t.subj` for a real triple `t`.
* `(node, label, target)` for each `succ` entry. Here, `RDFNode.toSubject?`
  must first change `node` to a `Subject`. If the result is `none`, the
  entry is removed.

For a context from `buildContext`, the result `none` never occurs. Only
the `Subject` of a real triple puts data in `succ`. Thus, if `succ` is not
empty, `c.node` is always a `Subject`. For the proof, refer to
`mem_context_succ_triples` in `RoundTrip.lean`. -/
def TContext.toTriples (c : TContext) : List Triple :=
  c.pred.filterMap (fun (src, lbl) =>
    match lbl with
    | .iri p => some (⟨src, p, c.node⟩ : Triple)
    | _ => none) ++
  c.succ.filterMap (fun (lbl, tgt) =>
    match c.node.toSubject?, lbl with
    | some ns, .iri p => some (⟨ns, p, tgt⟩ : Triple)
    | _, _ => none)

/-- All the triples that the contexts of a `TGraph` record. -/
def TGraph.toTriples : TGraph → List Triple
  | .empty => []
  | .ext c g => c.toTriples ++ TGraph.toTriples g

/-- `TGraph → Graph`: collect the triples of each context into one
`Finset Triple`. -/
def toGraph (g : TGraph) : Graph := g.toTriples.toFinset

end ShexLean.InductiveRDF
