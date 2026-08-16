import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2025Inheritance.Stratification
import ShexLean.Shex2025Inheritance.Render
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Example

/-!
Example 3 from the 2025 "Shape Expressions with Inheritance" paper (§4.1,
Table 1): the triple expression `e = p @T_even ; (p @T_<5* | p @T_str)`,
matched/not matched against three example sets of triples. Also hosts the
ambient schema `S_ex5` (Example 5's own schema, §4.2) and node constraints
`T_even`/`T_<5`/`T_>5`/`T_str`, since Examples 3-5 all state their claims
against this same schema — `Example4_closed_extra.lean`/
`Example5_extends.lean` both import this file to reuse them, along with
the `M24`/`M246`/`M2a`/`M24a` triple sets. The generic `ofShape`-lifting
helper lemmas both files also need (`ofShape_of_Me_eq_self`/
`singleton_tc_ofShape`/`Me_eq_self_of_props_subset`) live in
`ShexLean/Shex2025Inheritance/Semantics.lean` instead, since they aren't
tied to any particular example.
-/

namespace ShexLean.Inheritance

/-! ### Node constraints for Example 3/Example 4/Example 5 (§4.1) -/

/-- `T_even`: the node is an even integer literal. -/
def cEven : NodeConstraint
  | .lit (.int i) => i % 2 = 0
  | _ => False

/-- `T_<5`: the node is an integer literal less than 5. -/
def cLt5 : NodeConstraint
  | .lit (.int i) => i < 5
  | _ => False

/-- `T_>5`: the node is an integer literal greater than 5. -/
def cGt5 : NodeConstraint
  | .lit (.int i) => i > 5
  | _ => False

/-- `T_str`: the node is a string literal. -/
def cStr : NodeConstraint
  | .lit (.str _) => True
  | _ => False

/-- Example 5's schema `S = (Y, X, def, ∅)`, with `Y = {T_even, T_<5,
T_>5}`, `X = {x0,...,x6}` (see the module docstring for why `x0` is
included), `def` as listed in the paper. -/
def S_ex5 : Schema where
  Y := {"T_even", "T_lt5", "T_gt5"}
  X := {"x0", "x1", "x2", "x3", "x4", "x5", "x6"}
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "T_even" => .constraint cEven
    | "T_lt5" => .constraint cLt5
    | "T_gt5" => .constraint cGt5
    -- x0 → extends _ ⟨p @T_even⟩
    | "x0" => .extends ∅ ⟨false, none, .tc "p" "T_even"⟩
    -- x1 → extends x0 ⟨p @T_even⟩
    | "x1" => .extends {"x0"} ⟨false, none, .tc "p" "T_even"⟩
    -- x2 → extends x1 ⟨p @T_<5⟩
    | "x2" => .extends {"x1"} ⟨false, none, .tc "p" "T_lt5"⟩
    -- x3 → extends x0 ⟨p @T_even⟩ and ⟨p @T_>5*⟩
    | "x3" =>
        .and (.extends {"x0"} ⟨false, none, .tc "p" "T_even"⟩)
          (.ofShape ⟨false, none, .star (.tc "p" "T_gt5")⟩)
    -- x4 → extends x6 ⟨p @T_<5⟩
    | "x4" => .extends {"x6"} ⟨false, none, .tc "p" "T_lt5"⟩
    -- x5 → extends x0 extra {p} ⟨ε⟩
    | "x5" => .extends {"x0"} ⟨false, some {"p"}, .empty⟩
    -- x6 → extends x3 ⟨p @T_even⟩
    | "x6" => .extends {"x3"} ⟨false, none, .tc "p" "T_even"⟩
    | _ => .constraint (fun _ => False)

/-- The fixed subject used by every neighbourhood set in Examples 3-5. -/
def n_ex3 : Subject := .iri "n"

/-- Example 3's typing `τ`. -/
def τ_ex3 : Typing :=
  { (RDFNode.lit (.int 2), "T_even"), (RDFNode.lit (.int 2), "T_lt5"),
    (RDFNode.lit (.int 4), "T_even"), (RDFNode.lit (.int 4), "T_lt5"),
    (RDFNode.lit (.int 6), "T_even"), (RDFNode.lit (.int 6), "T_gt5"),
    (RDFNode.lit (.str "a"), "T_str") }

/-- `t p o` is the triple `(n_ex3, p, o)`, the common shape of every
triple used in Examples 3-4. -/
def tp (p : IRI) (o : RDFNode) : Triple := ⟨n_ex3, p, o⟩

def M24 : Finset Triple := {tp "p" (.lit (.int 2)), tp "p" (.lit (.int 4))}
def M246 : Finset Triple :=
  {tp "p" (.lit (.int 2)), tp "p" (.lit (.int 4)), tp "p" (.lit (.int 6))}
def M2a : Finset Triple := {tp "p" (.lit (.int 2)), tp "p" (.lit (.str "a"))}
def M24a : Finset Triple :=
  {tp "p" (.lit (.int 2)), tp "p" (.lit (.int 4)), tp "p" (.lit (.str "a"))}

/-- Example 3's triple expression `e = p @T_even ; (p @T_<5* | p @T_str)`. -/
def e_ex3 : TripleExpr :=
  .seq (.tc "p" "T_even") (.choice (.star (.tc "p" "T_lt5")) (.tc "p" "T_str"))

/-- A fuel bound generous enough for every proof in Examples 3-5 (`e_ex3`
has depth 4, and the deepest `extends` chain used below, `x4 → x6 → x3 →
x0`, is 4 levels; `10` is comfortably more than either needs). -/
def bigFuel : ℕ := 10

/-- `M24, τ ⊨ e` (Example 3): split into `{(n,p,2)}` (satisfying
`p @T_even`) and `{(n,p,4)}` (satisfying `(p @T_<5)*` via a single part). -/
theorem M24_satisfies_e : SatisfiesEFuel bigFuel S_ex5 default τ_ex3 M24 e_ex3 := by
  refine ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.int 4))}, ⟨by decide, by decide⟩, ?_, ?_⟩
  · exact ⟨n_ex3, .lit (.int 2), rfl, by decide⟩
  · refine Or.inl ⟨[{tp "p" (.lit (.int 4))}], ⟨by decide, by decide⟩, ?_⟩
    intro Ni hNi
    simp only [List.mem_singleton] at hNi
    subst hNi
    exact ⟨n_ex3, .lit (.int 4), rfl, by decide⟩

/-- `M246, τ ⊨ e` (Example 3): split into `{(n,p,6)}` (satisfying
`p @T_even`) and `{(n,p,2),(n,p,4)}` (satisfying `(p @T_<5)*` via two
parts). -/
theorem M246_satisfies_e : SatisfiesEFuel bigFuel S_ex5 default τ_ex3 M246 e_ex3 := by
  refine ⟨{tp "p" (.lit (.int 6))}, {tp "p" (.lit (.int 2)), tp "p" (.lit (.int 4))},
    ⟨by decide, by decide⟩, ?_, ?_⟩
  · exact ⟨n_ex3, .lit (.int 6), rfl, by decide⟩
  · refine Or.inl ⟨[{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.int 4))}], ⟨by decide, by decide⟩, ?_⟩
    intro Ni hNi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hNi
    rcases hNi with hNi | hNi <;> subst hNi
    · exact ⟨n_ex3, .lit (.int 2), rfl, by decide⟩
    · exact ⟨n_ex3, .lit (.int 4), rfl, by decide⟩

/-- `M2a, τ ⊨ e` (Example 3): split into `{(n,p,2)}` (satisfying
`p @T_even`) and `{(n,p,"a")}` (satisfying `p @T_str`). -/
theorem M2a_satisfies_e : SatisfiesEFuel bigFuel S_ex5 default τ_ex3 M2a e_ex3 := by
  refine ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.str "a"))}, ⟨by decide, by decide⟩, ?_, ?_⟩
  · exact ⟨n_ex3, .lit (.int 2), rfl, by decide⟩
  · exact Or.inr ⟨n_ex3, .lit (.str "a"), rfl, by decide⟩

/-! `S_ex5`'s decidability prerequisites (`ShexLean.Shex2025Inheritance.
Decidable`'s `satisfiesFuel_decidable`/`satisfiesMFuel_decidable`), needed
by every `SatisfiesFuel`/`SatisfiesMFuel` display claim in Examples 4/5. -/

theorem S_ex5_XClosed : S_ex5.XClosed := by unfold Schema.XClosed; decide

theorem S_ex5_RestrOk : S_ex5.RestrOk := by
  intro x hx u hu
  fin_cases hx <;> simp_all [S_ex5, ShapeExpr.restrOf] <;> (try subst hu) <;> trivial

end ShexLean.Inheritance

namespace Examples

open ShexLean.Inheritance (e_ex3 M24 M246 M2a S_ex5 τ_ex3 bigFuel satisfiesEFuel_decidable)
open ShexLean (Graph.render Typing.render renderDecide)

/-- Example 3's triple expression, matched against `M24`/`M246`/`M2a`.
`graphText`/`typingText`'s typing line are rendered from the real
`Finset Triple`/`Typing` values; every `M,τ ⊨ e` claim is a `native_decide`
computation via `satisfiesEFuel_decidable` (unconditionally decidable —
Table 1 never touches `NodeConstraint`/`extends`, so no `XClosed`/`RestrOk`/
`FOk` witnesses are needed here, unlike the `SatisfiesFuel` claims in the
other 2025 examples). -/
def inheritance2025TripleMatch : Example where
  name := "inheritance2025-example3-triple-match"
  summary := "Triple expression p@T_even;(p@T_<5*|p@T_str) matched against three sets."
  schemaText := s!"e = {e_ex3.render}"
  graphText :=
    s!"M24  = {Graph.render M24}\n" ++
    s!"M246 = {Graph.render M246}\n" ++
    s!"M2a  = {Graph.render M2a}"
  typingText :=
    s!"τ = {Typing.render τ_ex3}\n" ++
    s!"M24, τ ⊨ e = {renderDecide (satisfiesEFuel_decidable bigFuel S_ex5 default τ_ex3 M24 e_ex3)}\n" ++
    s!"M246, τ ⊨ e = {renderDecide (satisfiesEFuel_decidable bigFuel S_ex5 default τ_ex3 M246 e_ex3)}\n" ++
    s!"M2a, τ ⊨ e = {renderDecide (satisfiesEFuel_decidable bigFuel S_ex5 default τ_ex3 M2a e_ex3)}"

end Examples
