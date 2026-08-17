import ShexLean.Shex2026InheritanceDisjunction.Decidable
import ShexLean.Shex2017Schemas.Render
import Mathlib.Data.Finset.Sort

/-!
The 2025 formalism's analogue of `ShexLean.Shex2017Schemas.Render`: turns
the *real* `Graph`/`Schema`/`Typing` values of a 2025 worked example into
display text, and hand-typed `true`/`false`/prose claims into values
computed via `ShexLean.Inheritance`'s `Decidable` instances
(`satisfiesFuel_decidable`/`satisfiesMFuel_decidable`/
`satisfiesEFuel_decidable`, `ShexLean/Shex2025Inheritance/Decidable.lean`).

Reuses `ShexLean.renderSorted`/`RDFNode.render`/`Subject.render`/
`Triple.render`/`Graph.render`/`renderDecide` from the 2017 side directly —
those operate on the shared `Common/RDF.lean` types, unchanged here.

**`NodeConstraint := RDFNode → Prop` is opaque** (Def 1, unlike 2017's
concrete `ValueDescr`), so `.constraint c` can't be rendered from `c`
itself — every worked example's `.constraint` leaves are `Y`-labels
referenced only via `Schema.render`'s own `<L> → …` line, so a generic
placeholder is all a `.constraint` node ever needs to show on its own line.
-/

namespace ShexLean.InheritanceDisjunction

def TripleExpr.render : TripleExpr → String
  | .empty => "ε"
  | .tc p z => s!"{p} @<{z}>"
  | .choice e1 e2 => s!"({e1.render} | {e2.render})"
  | .seq e1 e2 => s!"({e1.render} ; {e2.render})"
  | .star e => s!"{e.render}*"

def Shape.render (h : Shape) : String :=
  (if h.closed then "closed " else "") ++
    (match h.extra with | none => "" | some P => s!"extra {ShexLean.renderSorted (·) P} ") ++
    s!"⟨{h.triples.render}⟩"

def ShapeExpr.render : ShapeExpr → String
  | .ofShape h => h.render
  | .extends xs hs =>
      let xsStr := if xs = ∅ then "_" else ", ".intercalate (xs.sort (· ≤ ·))
      let hsStr := " OR ".intercalate (hs.map Shape.render)
      s!"extends {xsStr} {hsStr}"
  | .constraint _ => "<boolean-constraint>"
  | .or s1 s2 => s!"({s1.render} OR {s2.render})"
  | .and s1 s2 => s!"({s1.render} AND {s2.render})"
  | .not s => s!"NOT({s.render})"

/-- `Schema.render`, one `<L> → def(L)` line per label in `Y ∪ X`
(`shapeDef` is total, but only these labels are the schema's own — matching
`ShexLean.Shex2017Schemas.Render`'s `Schema.render`). Sorted directly via
`Finset.sort` (unlike `renderSorted`, which sorts *rendered strings* for
types with no order of their own — `ShapeLabel := String` already has one,
and here each label `L` is still needed, not just its rendering, to look up
`S.shapeDef L`/`L ∈ S.A`). -/
def Schema.render (S : Schema) : String :=
  "\n".intercalate
    (((S.Y ∪ S.X).sort (· ≤ ·)).map
      (fun L => s!"{if L ∈ S.A then "abstract " else ""}{L} → {(S.shapeDef L).render}"))

end ShexLean.InheritanceDisjunction
