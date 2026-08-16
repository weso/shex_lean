import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
Basic RDF structures, following the RDF Graph Model in §1 of
"Semantics and Validation of Shapes Schemas for RDF" (Boneva, Labra Gayo,
Prud'hommeaux, 2017).

> As usual, we assume three disjoint sets: IRI a set of IRIs, Lit a set of
> literals, and Blank a set of blank nodes. An RDF graph is a set of triples
> over IRI ∪ Blank × IRI × IRI ∪ Lit ∪ Blank.
-/

namespace ShexLean

/-- The set `IRI` of the paper. -/
abbrev IRI := String

/-- The set `Blank` of blank node identifiers. -/
abbrev BNodeId := String

/-- The set `Lit` of RDF literals. Minimal to start with; extend with more
datatypes (langtag strings, decimals, dates, ...) as they become needed. -/
inductive Literal where
  | str : String → Literal
  | int : Int → Literal
  deriving DecidableEq, Repr

/-- An RDF term, i.e. an element of `IRI ∪ Lit ∪ Blank`. -/
inductive RDFNode where
  | iri   : IRI → RDFNode
  | lit   : Literal → RDFNode
  | bnode : BNodeId → RDFNode
  deriving DecidableEq, Repr

/-- An RDF *subject*: `IRI ∪ Blank`, i.e. an `RDFNode` that isn't a literal.
The paper's own grammar box (§1) already draws this distinction — "An RDF
graph is a set of triples over `IRI ∪ Blank × IRI × IRI ∪ Lit ∪ Blank`" —
but the original `Triple` below didn't enforce it: `RDFNode` includes
`.lit`, so nothing prevented constructing an ill-formed triple with a
literal subject. `Subject` makes that unrepresentable. -/
inductive Subject where
  | iri   : IRI → Subject
  | bnode : BNodeId → Subject
  deriving DecidableEq, Repr

/-- Every subject is in particular an RDF node (used, via the `Coe`
instance below, wherever a subject is compared against/passed as a general
`RDFNode` — e.g. `Graph.nodes`, `neigh`, or a shape-satisfaction query,
which may ask about a literal that can never be *anyone's* subject). -/
@[reducible] def Subject.toNode : Subject → RDFNode
  | .iri i => .iri i
  | .bnode b => .bnode b

instance : Coe Subject RDFNode := ⟨Subject.toNode⟩

/-- The partial converse: an `RDFNode` is a `Subject` iff it isn't a
literal. Used wherever some *other* representation of a graph only tracks
"the node," but needs to rebuild an actual `Triple` — e.g.
`ShexLean.InductiveRDF.Graph`'s `TContext.toTriples`. -/
@[reducible] def RDFNode.toSubject? : RDFNode → Option Subject
  | .iri i => some (.iri i)
  | .bnode b => some (.bnode b)
  | .lit _ => none

theorem toSubject_eq_some_iff {n : RDFNode} {s : Subject} :
    n.toSubject? = some s ↔ (s : RDFNode) = n := by
  cases n <;> cases s <;> simp [RDFNode.toSubject?, Subject.toNode, eq_comm]

/-- `Subject.toNode` is injective (`.iri`/`.bnode` map to disjoint `RDFNode`
constructors, each preserving the payload). -/
theorem Subject.toNode_inj {s1 s2 : Subject} (h : (s1 : RDFNode) = (s2 : RDFNode)) : s1 = s2 := by
  cases s1 <;> cases s2 <;> simp_all [Subject.toNode]

/-- A triple `(s, p, o) ∈ (IRI ∪ Blank) × IRI × (IRI ∪ Lit ∪ Blank)` — `s`'s
type (`Subject`, not `RDFNode`) rules out a literal subject at the type
level; `o` is unrestricted, matching the grammar box. -/
structure Triple where
  subj : Subject
  pred : IRI
  obj  : RDFNode
  deriving DecidableEq, Repr

/-- An RDF graph is a (finite) set of triples. -/
abbrev Graph := Finset Triple

/-- `Nodes(G)`: the nodes that appear in a subject or object position of `G`. -/
def Graph.nodes (G : Graph) : Finset RDFNode :=
  G.image (fun t => (t.subj : RDFNode)) ∪ G.image Triple.obj

/-- `neigh_G(n)`: the triples of `G` that have `n` as subject. `n` ranges
over all of `RDFNode` (not just `Subject`), since the neighbourhood of a
literal is well-defined too — always `∅`, as no triple can have a literal
subject. -/
def neigh (G : Graph) (n : RDFNode) : Finset Triple :=
  G.filter (fun t => (t.subj : RDFNode) = n)

end ShexLean
