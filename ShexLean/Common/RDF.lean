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

/-- The set `Lit` of RDF literals: strings and integers. Extend with more
datatypes (langtag strings, decimals, dates, ...) as needed. -/
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
The paper's grammar restricts triples to `(IRI ∪ Blank) × IRI × (IRI ∪ Lit ∪ Blank)`
(§1); `Subject` makes a literal subject unrepresentable at the type level. -/
inductive Subject where
  | iri   : IRI → Subject
  | bnode : BNodeId → Subject
  deriving DecidableEq, Repr

/-- Every subject is in particular an RDF node. -/
def Subject.toNode : Subject → RDFNode
  | .iri i => .iri i
  | .bnode b => .bnode b

instance : Coe Subject RDFNode := ⟨Subject.toNode⟩

/-- The partial converse: an `RDFNode` is a `Subject` iff it isn't a literal. -/
def RDFNode.toSubject? : RDFNode → Option Subject
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

/-- A triple `(s, p, o) ∈ (IRI ∪ Blank) × IRI × (IRI ∪ Lit ∪ Blank)`. -/
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

/-- `neigh_G(n)`: the triples of `G` that have `n` as subject. `n` ranges over
all of `RDFNode`, not just `Subject`: the neighbourhood of a literal is
well-defined too, always `∅`. -/
def neigh (G : Graph) (n : RDFNode) : Finset Triple :=
  G.filter (fun t => (t.subj : RDFNode) = n)

end ShexLean
