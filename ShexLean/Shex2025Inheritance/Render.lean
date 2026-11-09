import ShexLean.Shex2025Inheritance.Decidable
import ShexLean.InheritanceCore.Render
import Mathlib.Data.Finset.Sort

/-!
This file renders `Graph`, `Schema` and `Typing` values as display text for
the worked examples. It uses the `Decidable` instances in
`ShexLean/Shex2025Inheritance/Decidable.lean` (`satisfiesFuel_decidable`,
`satisfiesMFuel_decidable` and `satisfiesE_decidable`) to compute the
`true` and `false` results.

`NodeConstraint := RDFNode → Prop` is opaque (Def 1). (In 2017, the
concrete `ValueDescr` is not opaque.) Thus, this file cannot render
`.constraint c` from `c`. In the worked examples, each `.constraint` leaf
is a `Y` label, and the line `<L> → …` of `Schema.render` already shows
it. Thus, a general placeholder is sufficient.
-/

namespace ShexLean.Inheritance

open ShexLean.InheritanceCore hiding Schema

def ShapeExpr.render : ShapeExpr → String
  | .ofShape h => h.render
  | .extends xs h =>
      let xsStr := if xs = ∅ then "_" else ", ".intercalate (xs.sort (· ≤ ·))
      s!"extends {xsStr} {h.render}"
  | .constraint _ => "<boolean-constraint>"
  | .or s1 s2 => s!"({s1.render} OR {s2.render})"
  | .and s1 s2 => s!"({s1.render} AND {s2.render})"
  | .not s => s!"NOT({s.render})"

/-- One line `<L> → def(L)` for each label in `Y ∪ X`. (`shapeDef` is
total, but only these labels are part of the schema. This agrees with
`Schema.render` in `ShexLean.Shex2017Schemas.Render`.)

The labels are sorted with `Finset.sort` on the label. They are not sorted
with `renderSorted`, which sorts rendered strings, because the function
still needs the label `L` to find `S.shapeDef L` and `L ∈ S.A`. -/
def Schema.render (S : Schema) : String :=
  "\n".intercalate
    (((S.Y ∪ S.X).sort (· ≤ ·)).map
      (fun L => s!"{if L ∈ S.A then "abstract " else ""}{L} → {(S.shapeDef L).render}"))

end ShexLean.Inheritance
