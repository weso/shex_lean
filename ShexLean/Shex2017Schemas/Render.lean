import ShexLean.Shex2017Schemas.Decidable
import ShexLean.Shex2017Schemas.MaximalTyping
import Mathlib.Data.Finset.Sort

/-!
This file changes the real `Graph`, `Schema` and `Typing` values of an
example into the text that `Example.render` (`examples/Example.lean`)
shows. It does two things:

* A pretty-printer goes through the Lean values. It replaces text that a
  person wrote by hand.
* The `Decidable` instances of `Decidable.lean` compute the `true`,
  `false` and "correct" claims. They replace claims that a person typed by
  hand.

**Why we do not use `Finset.sort` directly on `Finset RDFNode`,
`Finset Triple` and the other types.** `Finset.sort` needs a total order
on the element type. `RDFNode`, `Triple`, `ValueItem` and the other types
do not have one. We do not make and prove such an order. In its place,
each `Finset` below maps each element to its rendered `String`
(`Finset.image`, which is computable). Then it sorts the result
(`Finset String`, which already has a `LinearOrder`). Thus, the original
type does not need an order.

**Why we do not use `Finset.toList`.** In this version of Mathlib, it is
`noncomputable`. It selects a representative list with `Quot.out`, which
needs choice. `renderSorted` below is the computable replacement. Use it
at each location where you must list the elements of a `Finset` for
display.
-/

namespace ShexLean

/-- Render each element of `s` with `render`, remove duplicates, and sort
the rendered strings. The result is a `Finset`. Thus, two elements with
the same rendered text become one line. Refer to the module docstring to
know why this function does not sort the elements of `s` directly. -/
def renderSorted {α : Type*} [DecidableEq α] (render : α → String) (s : Finset α) : List String :=
  (s.image render).sort (· ≤ ·)

def Literal.render : Literal → String
  | .str s => s!"\"{s}\""
  | .int i => toString i

def RDFNode.render : RDFNode → String
  | .iri i => s!"<{i}>"
  | .lit l => l.render
  | .bnode b => s!"_:{b}"

def Subject.render (s : Subject) : String := (s : RDFNode).render

def Triple.render (t : Triple) : String := s!"{t.subj.render} {t.pred} {t.obj.render} ."

/-- `Graph.render`. It is generated from the real `Finset Triple`. It is
not Turtle text that a person typed by hand. -/
def Graph.render (G : Graph) : String :=
  "\n".intercalate (renderSorted Triple.render G)

def ValueItem.render : ValueItem → String
  | .iri i => s!"<{i}>"
  | .lit l => l.render
  | .anyBlank => "_b"

def ValueDescr.render (V : ValueDescr) : String :=
  "{" ++ ", ".intercalate (renderSorted ValueItem.render V) ++ "}"

def PropSet.render (P : PropSet) : String :=
  "{" ++ ", ".intercalate (renderSorted (·) P) ++ "}"

mutual
/-- `ShExpr.render`. It goes through the `ShExpr` syntax tree, and uses
the concrete syntax of Fig. 1 (`AND`, `OR`, `NOT`, `@<L>`, `;`, `|`,
`[min;max]`). -/
def ShExpr.render : ShExpr → String
  | .valueDescr V => V.render
  | .neigDescr E => E.render
  | .and S1 S2 => s!"({S1.render} AND {S2.render})"
  | .or S1 S2 => s!"({S1.render} OR {S2.render})"
  | .not S => s!"NOT({S.render})"

def TExpr.render : TExpr → String
  | .tPattern P L => s!"{P.render} @<{L}>"
  | .empty => "EMPTY"
  | .someOf E1 E2 => s!"({E1.render} | {E2.render})"
  | .eachOf E1 E2 => s!"({E1.render} ; {E2.render})"
  | .rep E min max => s!"{E.render} [{min};{max.map toString |>.getD "*"}]"
end

/-- `Schema.render`: one line `<L> → def(L)` for each label in
`S.labels`. -/
def Schema.render (S : Schema) : String :=
  "\n".intercalate ((renderSorted (·) S.labels).map (fun L => s!"<{L}> → {(S.shapeDef L).render}"))

/-- `Typing.render`, `{(n,<L>), …}`: only the data, with no claim about
the data. -/
def Typing.render (t : Typing) : String :=
  "{" ++ ", ".intercalate
    (renderSorted (fun p : RDFNode × Label => s!"({p.1.render},<{p.2}>)") t) ++ "}"

/-! ### Computed claims

`Schema.CorrTyping` has the quantifier `∀ n L, (n,L) ∈ t → …` over all of
`RDFNode × Label`. This has the same form as the existentials of
`Satisfies` and `Matches` that `Decidable.lean` bounds. But the premise
`(n,L) ∈ t` already forces `n` and `L` to be in the finite set `t`. Thus,
the same method ("write it as a bounded search") applies one level
higher. -/

theorem corrTyping_iff_bounded (S : Schema) (G : Graph) (t : Typing) :
    S.CorrTyping G t ↔
      ∀ p ∈ t, Satisfies G t p.1 (S.shapeDef p.2) := by
  constructor
  · exact fun h p hp => h p.1 p.2 hp
  · exact fun h n L hnL => h (n, L) hnL

/-- `Schema.CorrTyping` is decidable. It is bounded with
`corrTyping_iff_bounded`, and uses `satisfies_decidable`. This rendering
layer also uses `satisfies_decidable`. -/
def corrTyping_decidable (S : Schema) (G : Graph) (t : Typing) :
    Decidable (S.CorrTyping G t) :=
  haveI : ∀ p : RDFNode × Label, Decidable (Satisfies G t p.1 (S.shapeDef p.2)) :=
    fun p => satisfies_decidable G t p.1 (S.shapeDef p.2)
  decidable_of_iff _ (corrTyping_iff_bounded S G t).symm

/-- `"true"` or `"false"` for a proposition with an explicit `Decidable`
instance. This is the computed replacement for a claim that a person typed
by hand in a `typingText`.

The command-line tool computes this value with the compiled code of
`@decide P inst` when it runs. This is not a proof: the kernel does not
check the value, and no theorem uses it. The theorems of each example are
the checked results. (This file does not use the tactic `native_decide`.)

The function takes the instance explicitly. It does not use typeclass
search, because that search needs `satisfies_decidable` and the other
instances as global instances. `@decide` needs a closed instance term to
reduce. A local instance is not sufficient. (A `haveI` that stays in the
proof term does not work.) -/
def renderDecide {P : Prop} (inst : Decidable P) : String :=
  toString (@decide P inst)

end ShexLean
