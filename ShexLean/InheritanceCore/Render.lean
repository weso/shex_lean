import ShexLean.InheritanceCore.Syntax
import ShexLean.Shex2017Schemas.Render

/-!
Display text for triple expressions and shapes.
The `Render.lean` files of `ShexLean/Shex2025Inheritance/`
and `ShexLean/Shex2026InheritanceDisjunction/` use it for
their `ShapeExpr` and `Schema` values.
-/

namespace ShexLean.InheritanceCore

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

end ShexLean.InheritanceCore
