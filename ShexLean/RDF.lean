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

/-- A triple `(s, p, o) ∈ (IRI ∪ Blank) × IRI × (IRI ∪ Lit ∪ Blank)`.
Subject/object are not refined to exclude ill-formed terms (e.g. a literal
subject) at the type level; the semantics never inspects that distinction. -/
structure Triple where
  subj : RDFNode
  pred : IRI
  obj  : RDFNode
  deriving DecidableEq, Repr

/-- An RDF graph is a (finite) set of triples. -/
abbrev Graph := Finset Triple

/-- `Nodes(G)`: the nodes that appear in a subject or object position of `G`. -/
def Graph.nodes (G : Graph) : Finset RDFNode :=
  G.image Triple.subj ∪ G.image Triple.obj

/-- `neigh_G(n)`: the triples of `G` that have `n` as subject. -/
def neigh (G : Graph) (n : RDFNode) : Finset Triple :=
  G.filter (fun t => t.subj = n)

end ShexLean
