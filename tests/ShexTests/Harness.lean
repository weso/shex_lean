import ShexLean.Shex2025Inheritance.Decidable
import Mathlib.Data.Finset.Sort

/-!
The test harness: a validator that a program can run, for
the 2025 formalism (`ShexLean/Shex2025Inheritance/`).

It uses only the definitions and the decision procedures of the formalization:

* `satisfiesFuel_decidable` decides `SatisfiesFuel`.
  At the fuel `S.X.card + 1`, `SatisfiesFuel` is
  `Satisfies` (`satisfies_iff_satisfiesFuel_card`).
* `ancReach` computes `anc` (`ancReach_eq_anc`).

The validator computes the maximal typing with the
stratified refinement of Algorithm 1 (§5 of the paper):

1. It computes a stratification from the edges of `D_S`.
2. For each stratum, it starts from all the pairs `(n, L)`
   of the stratum, and removes each pair that is not locally
   correct (Definition 4), until the typing is stable.

The focus node conforms to the shape `L` if and only if `(focus, L)` is in the result.

This file is not part of the formalization.
No proof shows that its algorithm gives the same result as `ShexLean.InheritanceCore.Algorithm1`.
It follows the same steps.
-/

namespace ShexTests

open ShexLean hiding Schema
open ShexLean.Inheritance
open ShexLean.InheritanceCore hiding Schema

/-! ### Node constraints of ShExJ

The generator (`tests/tools/gen_shextest.py`) writes each
node constraint of a test with these Boolean functions.
The data of the tests has only the literals of
`ShexLean/Common/RDF.lean` (`xsd:string` and canonical `xsd:integer`).
The generator skips the other tests.
Thus, a constraint on another datatype or on a language tag never matches. -/

/-- The lexical form of a literal. -/
def lexical : RDFNode → Option String
  | .lit (.str s) => some s
  | .lit (.int k) => some (toString k)
  | _ => none

/-- One element of a value set. -/
inductive VI where
  | iri (s : String)
  | str (s : String)
  | int (k : Int)
  /-- A value that no node of the test data can have. -/
  | none
  | iriStem (s : String)
  | litStem (s : String)
  /-- A stem range: an optional stem (`none` is the wildcard) and the exclusions.
  An exclusion is a stem (`true`) or one value (`false`). -/
  | iriRange (stem : Option String) (excl : List (Bool × String))
  | litRange (stem : Option String) (excl : List (Bool × String))

def inRange (stem : Option String) (excl : List (Bool × String)) (s : String) : Bool :=
  stem.all (·.isPrefixOf s) && excl.all fun (isStem, e) => if isStem then !e.isPrefixOf s else s != e

def VI.matches : VI → RDFNode → Bool
  | .iri s, n => n == .iri s
  | .str s, n => n == .lit (.str s)
  | .int k, n => n == .lit (.int k)
  | .none, _ => false
  | .iriStem s, .iri i => s.isPrefixOf i
  | .iriStem _, _ => false
  | .litStem s, n => (lexical n).any s.isPrefixOf
  | .iriRange stem excl, .iri i => inRange stem excl i
  | .iriRange _ _, _ => false
  | .litRange stem excl, n => (lexical n).any (inRange stem excl)

namespace NC

def any : RDFNode → Bool := fun _ => true
def never : RDFNode → Bool := fun _ => false
def all (fs : List (RDFNode → Bool)) : RDFNode → Bool := fun n => fs.all (· n)
def isIri : RDFNode → Bool | .iri _ => true | _ => false
def isBNode : RDFNode → Bool | .bnode _ => true | _ => false
def isLiteral : RDFNode → Bool | .lit _ => true | _ => false
def isNonLiteral : RDFNode → Bool | .lit _ => false | _ => true
def isString : RDFNode → Bool | .lit (.str _) => true | _ => false
def isInteger : RDFNode → Bool | .lit (.int _) => true | _ => false
def values (vs : List VI) : RDFNode → Bool := fun n => vs.any (·.matches n)

/-- The string that the string facets check: the IRI, the
label of a blank node, or the lexical form of a literal.
(The ShEx test suite checks the label of a blank node.) -/
def strForm : RDFNode → Option String
  | .iri i => some i
  | .bnode b => some b
  | n => lexical n

def length (k : ℕ) : RDFNode → Bool := fun n => (strForm n).any (·.length == k)
def minLength (k : ℕ) : RDFNode → Bool := fun n => (strForm n).any (k ≤ ·.length)
def maxLength (k : ℕ) : RDFNode → Bool := fun n => (strForm n).any (·.length ≤ k)

def intBetween (lo hi : Option Int) : RDFNode → Bool
  | .lit (.int k) => lo.all (· ≤ k) && hi.all (k ≤ ·)
  | _ => false

def totalDigits (d : ℕ) : RDFNode → Bool
  | .lit (.int k) => (toString k.natAbs).length ≤ d
  | _ => false

end NC

/-! ### Shape expressions with node constraints that a program can compute

The node constraints of the formalism are general predicates (`RDFNode → Prop`).
The decision procedures need a `DecidablePred` for each of them.
The generated tests use `CShape`, in which each node constraint is a Boolean function.
`CShape.toExpr` gives the shape expression of the
formalism, and `CShape.fok` gives the decidability witness. -/

/-- A shape expression with Boolean node constraints. -/
inductive CShape where
  | ofShape (h : Shape)
  | ext (xs : List Label) (h : Shape)
  | constraint (f : RDFNode → Bool)
  | or (a b : CShape)
  | and (a b : CShape)
  | not (a : CShape)

/-- The shape expression of the formalism. -/
def CShape.toExpr : CShape → ShapeExpr
  | .ofShape h => .ofShape h
  | .ext xs h => .extends xs.toFinset h
  | .constraint f => .constraint (fun n => f n = true)
  | .or a b => .or a.toExpr b.toExpr
  | .and a b => .and a.toExpr b.toExpr
  | .not a => .not a.toExpr

/-- The witness that `satisfiesFuel_decidable` needs.
The result is `none` if an `extends` goes out of `X`. -/
def CShape.fok (S : Schema) : (c : CShape) → Option (c.toExpr.FOk S)
  | .ofShape _ => some PUnit.unit
  | .ext xs _ => if h : xs.toFinset ⊆ S.X then some ⟨h⟩ else none
  | .constraint f => some (fun n => inferInstanceAs (Decidable (f n = true)))
  | .or a b => do
      let x ← a.fok S
      let y ← b.fok S
      pure (x, y)
  | .and a b => do
      let x ← a.fok S
      let y ← b.fok S
      pure (x, y)
  | .not a => a.fok S

/-! ### Test cases -/

/-- A schema of a test: the labels `Y`, `X` and `A`, and the definition of each label. -/
structure TestSchema where
  Y : List Label
  X : List Label
  A : List Label
  defs : List (Label × CShape)

/-- One validation test of the ShEx test suite. -/
structure TestCase where
  name : String
  /-- `structural` or `inheritance`. -/
  group : String
  schema : TestSchema
  data : List Triple
  focus : RDFNode
  shape : Label
  /-- `true` for `sht:ValidationTest`, `false` for `sht:ValidationFailure`. -/
  expected : Bool

def TestSchema.lookup (T : TestSchema) (l : Label) : CShape :=
  (T.defs.lookup l).getD (.ofShape ⟨false, none, .empty⟩)

/-- The schema of the formalism. -/
def TestSchema.toSchema (T : TestSchema) (h1 : Disjoint T.Y.toFinset T.X.toFinset)
    (h2 : T.A.toFinset ⊆ T.X.toFinset) : Schema where
  Y := T.Y.toFinset
  X := T.X.toFinset
  A := T.A.toFinset
  disjointYX := h1
  A_subX := h2
  shapeDef l := (T.lookup l).toExpr

/-! ### Decidability of the conditions of `satisfiesFuel_decidable` -/

instance (S : Schema) : Decidable S.XClosed := by unfold Schema.XClosed; infer_instance

def decMOk (S : Schema) : (s : ShapeExpr) → Decidable (s.MOk S)
  | .constraint _ => isFalse id
  | .ofShape _ => isTrue trivial
  | .extends xs _ => inferInstanceAs (Decidable (xs ⊆ S.X))
  | .or a b => @instDecidableAnd _ _ (decMOk S a) (decMOk S b)
  | .and a b => @instDecidableAnd _ _ (decMOk S a) (decMOk S b)
  | .not a => decMOk S a

theorem restrOk_iff (S : Schema) :
    S.RestrOk ↔ ∀ x ∈ S.X, match (S.shapeDef x).restrOf with
      | some u => u.MOk S
      | none => True := by
  refine forall₂_congr fun x _ => ?_
  cases (S.shapeDef x).restrOf <;> simp

instance (S : Schema) : Decidable S.RestrOk := by
  rw [restrOk_iff]
  haveI : ∀ x, Decidable (match (S.shapeDef x).restrOf with
      | some u => u.MOk S
      | none => True) := fun x => by
    cases (S.shapeDef x).restrOf with
    | none => exact isTrue trivial
    | some u => exact decMOk S u
  infer_instance

/-! ### The validator -/

/-- The edges of `D_S` out of `z`: `dep` and
`dep-extends` (`ShexLean/InheritanceCore/Schema.lean`).
The second component tells if the edge is negative (`dep-shape-neg` or `dep-extra-neg`). -/
def dEdges (S : Schema) (labels : List Label) (z : Label) : List (Label × Bool) :=
  let d := (S.shapeDef z).depsAux false
  let neg := d.negRefs ∪ d.extraNegRefs
  let targets := d.refs ∪ (S.shapeDef z).extendsTargets ∪
    (labels.filter fun w => z ∈ (S.shapeDef w).extendsTargets).toFinset
  (targets.sort (· ≤ ·)).map fun z' => (z', decide (z' ∈ neg))

/-- A stratification (Definition 7).
It starts with stratum 1 for each label.
It raises the stratum of `z` until `σ(z') ≤ σ(z)` for
each edge, and `σ(z') < σ(z)` for each negative edge.
The result is `none` if this does not stop.
Then `D_S` has a negative cycle. -/
def stratify (S : Schema) (labels : List Label) : Option (Label → ℕ) := Id.run do
  let edges := labels.map fun z => (z, dEdges S labels z)
  let mut σ : List (Label × ℕ) := labels.map (·, 1)
  for _ in [0:labels.length + 2] do
    let get := fun l => (σ.lookup l).getD 1
    let σ' := σ.map fun (z, v) =>
      let es := (edges.lookup z).getD []
      (z, es.foldl (fun m (z', neg) => max m (get z' + if neg then 1 else 0)) v)
    if σ' == σ then return some get
    σ := σ'
  return none

/-- The result of one test. -/
inductive Outcome where
  | result (b : Bool)
  | unsupported (reason : String)

/-- The validation of the focus node of a test against its shape. -/
def run (t : TestCase) : Outcome :=
  let T := t.schema
  if h1 : Disjoint T.Y.toFinset T.X.toFinset then
  if h2 : T.A.toFinset ⊆ T.X.toFinset then
  let S := T.toSchema h1 h2
  if hXC : S.XClosed then
  if hR : S.RestrOk then
  let G : Graph := t.data.toFinset
  let labels := (T.Y ++ T.X).dedup
  match stratify S labels with
  | none => .unsupported "D_S has a negative cycle"
  | some σ =>
  if labels.any (fun l => ((T.lookup l).fok S).isNone) then
    .unsupported "an extends target is not in X"
  else
  let fuel := S.X.card + 1
  let nodes := G.nodes ∪ {t.focus}
  -- `sat τ n l` decides `n, τ ⊨ def(l)`.
  let sat : Typing → RDFNode → Label → Bool := fun τ n l =>
    match (T.lookup l).fok S with
    | none => false
    | some ok => @decide _ (satisfiesFuel_decidable S G τ hXC hR fuel n (S.shapeDef l) ok)
  let desc : Label → List Label := fun l =>
    T.X.filter fun x => x ∉ T.A ∧ l ∈ ancReach S x
  -- Definition 4: the local correctness of one pair.
  let ok : Typing → Assoc → Bool := fun τ (n, l) =>
    if l ∈ T.A then (desc l).any (sat τ n) else sat τ n l
  let k := labels.foldl (fun m l => max m (σ l)) 0
  let τ := Id.run do
    let mut τ : Typing := ∅
    for i in [1:k+1] do
      let start := τ ∪ (nodes ×ˢ (labels.filter (σ · = i)).toFinset)
      let mut cur := start
      for _ in [0:start.card + 1] do
        let next := cur.filter fun p => σ p.2 < i || ok cur p
        if next = cur then break
        cur := next
      τ := cur
    return τ
  .result (decide ((t.focus, t.shape) ∈ τ))
  else .unsupported "a restriction is not in the MOk fragment"
  else .unsupported "an extends target is not in X"
  else .unsupported "A is not a subset of X"
  else .unsupported "Y and X are not disjoint"

end ShexTests
