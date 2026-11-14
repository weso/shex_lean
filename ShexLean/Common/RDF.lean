import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
Basic RDF structures.
They follow the RDF Graph Model in §1 of "Semantics and Validation of
Shapes Schemas for RDF" (Boneva, Labra Gayo, Prud'hommeaux, 2017).

> As usual, we assume three disjoint sets: IRI a set of IRIs, Lit a set of
> literals, and Blank a set of blank nodes. An RDF graph is a set of triples
> over IRI ∪ Blank × IRI × IRI ∪ Lit ∪ Blank.
-/

namespace ShexLean

abbrev IRI := String
abbrev BNodeId := String
inductive Literal where
  | str : String → Literal
  | int : Int → Literal
  deriving DecidableEq, Repr

inductive RDFNode where
  | iri   : IRI → RDFNode
  | lit   : Literal → RDFNode
  | bnode : BNodeId → RDFNode
  deriving DecidableEq, Repr

inductive Subject where
  | iri   : IRI → Subject
  | bnode : BNodeId → Subject
  deriving DecidableEq, Repr

def Subject.toNode : Subject → RDFNode
  | .iri i => .iri i
  | .bnode b => .bnode b

instance : Coe Subject RDFNode := ⟨Subject.toNode⟩

def RDFNode.toSubject? : RDFNode → Option Subject
  | .iri i => some (.iri i)
  | .bnode b => some (.bnode b)
  | .lit _ => none

theorem toSubject_eq_some_iff {n : RDFNode} {s : Subject} :
    n.toSubject? = some s ↔ (s : RDFNode) = n := by
  cases n <;> cases s <;> simp [RDFNode.toSubject?, Subject.toNode, eq_comm]

/-- `Subject.toNode` is injective.
    The constructors `.iri` and `.bnode` go to different `RDFNode` constructors -/
theorem Subject.toNode_inj {s1 s2 : Subject} (h : (s1 : RDFNode) = (s2 : RDFNode)) : s1 = s2 := by
  cases s1 <;> cases s2 <;> simp_all [Subject.toNode]

structure Triple where
  subj : Subject
  pred : IRI
  obj  : RDFNode
  deriving DecidableEq, Repr

/-- An RDF graph is a finite set of triples. -/
abbrev Graph := Finset Triple

/-- `Nodes(G)`: the nodes that are in a subject or an object position of `G`. -/
def Graph.nodes (G : Graph) : Finset RDFNode :=
  G.image (fun t => (t.subj : RDFNode)) ∪ G.image Triple.obj

/-- `neigh_G(n)`: the triples of `G` that have `n` as their subject.
 The argument `n` can be any `RDFNode`, not only a `Subject`.
  The neighbourhood of a literal is also defined: it is always `∅`. -/
def neigh (G : Graph) (n : RDFNode) : Finset Triple :=
  G.filter (fun t => (t.subj : RDFNode) = n)

end ShexLean
