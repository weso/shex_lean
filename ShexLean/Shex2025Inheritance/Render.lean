import ShexLean.Shex2025Inheritance.Decidable
import ShexLean.Shex2017Schemas.Render
import Mathlib.Data.Finset.Sort

/-!
Renders `Graph`/`Schema`/`Typing` values as display text for worked
examples, using the `Decidable` instances in
`ShexLean/Shex2025Inheritance/Decidable.lean`
(`satisfiesFuel_decidable`/`satisfiesMFuel_decidable`/`satisfiesEFuel_decidable`)
to compute the `true`/`false` results.

`NodeConstraint := RDFNode → Prop` is opaque (Def 1, unlike 2017's
concrete `ValueDescr`), so `.constraint c` can't be rendered from `c`
itself. Worked examples' `.constraint` leaves are `Y`-labels already shown
via `Schema.render`'s `<L> → …` line, so a generic placeholder suffices.
-/

namespace ShexLean.Inheritance

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
  | .extends xs h =>
      let xsStr := if xs = ∅ then "_" else ", ".intercalate (xs.sort (· ≤ ·))
      s!"extends {xsStr} {h.render}"
  | .constraint _ => "<boolean-constraint>"
  | .or s1 s2 => s!"({s1.render} OR {s2.render})"
  | .and s1 s2 => s!"({s1.render} AND {s2.render})"
  | .not s => s!"NOT({s.render})"

/-- One `<L> → def(L)` line per label in `Y ∪ X` (`shapeDef` is total, but
only these labels belong to the schema, matching
`ShexLean.Shex2017Schemas.Render`'s `Schema.render`). Sorted via
`Finset.sort` on the label itself, not via `renderSorted` (which sorts
rendered strings), since the label `L` is still needed to look up
`S.shapeDef L`/`L ∈ S.A`. -/
def Schema.render (S : Schema) : String :=
  "\n".intercalate
    (((S.Y ∪ S.X).sort (· ≤ ·)).map
      (fun L => s!"{if L ∈ S.A then "abstract " else ""}{L} → {(S.shapeDef L).render}"))

end ShexLean.Inheritance
