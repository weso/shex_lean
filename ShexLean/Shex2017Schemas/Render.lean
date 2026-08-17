import ShexLean.Shex2017Schemas.Decidable
import ShexLean.Shex2017Schemas.MaximalTyping
import Mathlib.Data.Finset.Sort

/-!
Turns the *real* `Graph`/`Schema`/`Typing` values of an example into the
display text `examples/Example.lean`'s `Example.render` shows — replacing
hand-written prose transcriptions with a genuine pretty-printer walking the
actual Lean values, and replacing hand-typed `true`/`false`/"correct"
claims with values computed via `Decidable.lean`'s `Decidable` instances.

**Why `Finset.sort` isn't used directly on `Finset RDFNode`/`Finset
Triple`/etc.** `Finset.sort` needs a total order on the element type, and
none of `RDFNode`/`Triple`/`ValueItem`/… have one. Rather than build and
prove one (real work, and this repo's `RDFNode`/`Triple` are exactly the
kind of small hand-rolled types where "derive `Ord`, then prove it's a
`LinearOrder`" is more machinery than the payoff justifies), every `Finset`
below is rendered by mapping each element to its *own* rendered `String`
first (`Finset.image`, ordinary and computable) and sorting *that*
(`Finset String`, whose `LinearOrder` already exists) — sidesteps needing
any order on the original type entirely.

**Why not `Finset.toList`.** It's `noncomputable` in this Mathlib (picks a
representative list via `Quot.out`, which needs choice) — `renderSorted`
below is the computable replacement used everywhere a `Finset` needs
enumerating for display.
-/

namespace ShexLean

/-- Render every element of `s` via `render`, deduplicating (as a `Finset`,
so two elements that render identically collapse to one line) and sorting
the *rendered strings* — see the module docstring for why not `s`'s own
elements directly. -/
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

/-- `Graph.render`, generated from the actual `Finset Triple`, not
hand-typed Turtle prose. -/
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
/-- `ShExpr.render`, walking the real `ShExpr` AST — Fig. 1's own
concrete syntax (`AND`/`OR`/`NOT`, `@<L>`, `;`/`|`, `[min;max]`). -/
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

/-- `Schema.render`, one `<L> → def(L)` line per label in `S.labels`. -/
def Schema.render (S : Schema) : String :=
  "\n".intercalate ((renderSorted (·) S.labels).map (fun L => s!"<{L}> → {(S.shapeDef L).render}"))

/-- `Typing.render`, `{(n,<L>), …}` — the *data*, not any claim about it. -/
def Typing.render (t : Typing) : String :=
  "{" ++ ", ".intercalate
    (renderSorted (fun p : RDFNode × Label => s!"({p.1.render},<{p.2}>)") t) ++ "}"

/-! ### Computed claims

`Schema.CorrTyping`'s own `∀ n L, (n,L) ∈ t → …` quantifies over
all of `RDFNode × Label`, same shape as the `Satisfies`/`Matches`
existentials `Decidable.lean` bounds — but the `(n,L) ∈ t` premise
already forces `n`/`L` to range over the finite `t` itself, so the
same "restate as a bounded search" trick applies directly, one level up. -/

theorem corrTyping_iff_bounded (S : Schema) (G : Graph) (t : Typing) :
    S.CorrTyping G t ↔
      ∀ p ∈ t, Satisfies G t p.1 (S.shapeDef p.2) := by
  constructor
  · exact fun h p hp => h p.1 p.2 hp
  · exact fun h n L hnL => h (n, L) hnL

/-- `Schema.CorrTyping` is decidable — bounded, via
`corrTyping_iff_bounded`, over the same `satisfies_decidable` this whole
rendering layer is built on. -/
def corrTyping_decidable (S : Schema) (G : Graph) (t : Typing) :
    Decidable (S.CorrTyping G t) :=
  haveI : ∀ p : RDFNode × Label, Decidable (Satisfies G t p.1 (S.shapeDef p.2)) :=
    fun p => satisfies_decidable G t p.1 (S.shapeDef p.2)
  decidable_of_iff _ (corrTyping_iff_bounded S G t).symm

/-- `"true"`/`"false"` for any proposition with an *explicit* `Decidable`
instance — the computed replacement for a hand-typed claim in a
`typingText`. Takes the instance explicitly (not via typeclass search,
which would need `satisfies_decidable`/etc. registered as global
instances) — matters once this is actually evaluated: `@decide` needs a
*closed* instance term to reduce/compile, not a local one (a `haveI` left
in the proof term won't do). -/
def renderDecide {P : Prop} (inst : Decidable P) : String :=
  toString (@decide P inst)

end ShexLean
