import ShexLean.Shex2026InheritanceDisjunction.Decidable
import ShexLean.Shex2017Schemas.Render
import Mathlib.Data.Finset.Sort

/-!
The equivalent of `ShexLean.Shex2017Schemas.Render` for this formalism. It
does two things:

* It changes the *real* `Graph`, `Schema` and `Typing` values of a worked
  example into display text.
* It replaces `true`, `false` and text claims that a person typed by hand
  with values that the `Decidable` instances of this formalism compute
  (`satisfiesFuel_decidable`, `satisfiesMFuel_decidable` and
  `satisfiesEFuel_decidable`, in
  `ShexLean/Shex2026InheritanceDisjunction/Decidable.lean`).

It uses directly these functions of the 2017 formalization:
`ShexLean.renderSorted`, `RDFNode.render`, `Subject.render`,
`Triple.render`, `Graph.render` and `renderDecide`. They operate on the
shared types of `Common/RDF.lean`, which do not change here.

**`NodeConstraint := RDFNode → Prop` is opaque** (Def 1). (In 2017, the
concrete `ValueDescr` is not opaque.) Thus, this file cannot render
`.constraint c` from `c`. In each worked example, the `.constraint` leaves
are `Y` labels, and only the line `<L> → …` of `Schema.render` refers to
them. Thus, a general placeholder is sufficient for a `.constraint` node
on its own line.
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

/-- `Schema.render`: one line `<L> → def(L)` for each label in `Y ∪ X`.
(`shapeDef` is total, but only these labels are part of the schema. This
agrees with `Schema.render` in `ShexLean.Shex2017Schemas.Render`.)

The labels are sorted directly with `Finset.sort`. `renderSorted` sorts
*rendered strings*, for types that have no order. Here, `Label := String`
already has an order. Also, the function needs each label `L`, not only
its rendered text, to find `S.shapeDef L` and `L ∈ S.A`. -/
def Schema.render (S : Schema) : String :=
  "\n".intercalate
    (((S.Y ∪ S.X).sort (· ≤ ·)).map
      (fun L => s!"{if L ∈ S.A then "abstract " else ""}{L} → {(S.shapeDef L).render}"))

end ShexLean.InheritanceDisjunction
