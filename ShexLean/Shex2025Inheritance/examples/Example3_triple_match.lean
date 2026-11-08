import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2025Inheritance.Stratification
import ShexLean.Shex2025Inheritance.Render
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Example

/-!
Example 3 from the 2025 paper "Shape Expressions with Inheritance" (§4.1,
Table 1): the triple expression `e = p @T_even ; (p @T_<5* | p @T_str)`,
and four example sets of triples that match it or do not match it.

This file also contains the schema `S_ex5` (the schema of Example 5, §4.2)
and the node constraints `T_even`, `T_<5`, `T_>5` and `T_str`, because
the claims of Examples 3-5 all use this schema. `Example4_closed_extra.lean`
and `Example5_extends.lean` both import this file to use them again,
together with the triple sets `M24`, `M246`, `M2a` and `M24a`.

The two files also need the general helper lemmas that lift to `ofShape`
(`ofShape_of_Me_eq_self`, `singleton_tc_ofShape` and
`Me_eq_self_of_props_subset`). These lemmas are in
`ShexLean/Shex2025Inheritance/Semantics.lean`, because they are not
specific to one example.
-/

namespace ShexLean.Inheritance

/-! ### Node constraints for Examples 3, 4 and 5 (§4.1) -/

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

/-- The schema of Example 5, `S = (Y, X, def, ∅)`, with
`Y = {T_even, T_<5, T_>5}`, `X = {x0,...,x6}`, and `def` as in the
paper. -/
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

/-- The fixed subject of all the neighbourhood sets in Examples 3-5. -/
def n_ex3 : Subject := .iri "n"

/-- The typing `τ` of Example 3. -/
def τ_ex3 : Typing :=
  { (RDFNode.lit (.int 2), "T_even"), (RDFNode.lit (.int 2), "T_lt5"),
    (RDFNode.lit (.int 4), "T_even"), (RDFNode.lit (.int 4), "T_lt5"),
    (RDFNode.lit (.int 6), "T_even"), (RDFNode.lit (.int 6), "T_gt5"),
    (RDFNode.lit (.str "a"), "T_str") }

/-- `t p o` is the triple `(n_ex3, p, o)`. All the triples of Examples 3-4
have this form. -/
def tp (p : IRI) (o : RDFNode) : Triple := ⟨n_ex3, p, o⟩

def M24 : Finset Triple := {tp "p" (.lit (.int 2)), tp "p" (.lit (.int 4))}
def M246 : Finset Triple :=
  {tp "p" (.lit (.int 2)), tp "p" (.lit (.int 4)), tp "p" (.lit (.int 6))}
def M2a : Finset Triple := {tp "p" (.lit (.int 2)), tp "p" (.lit (.str "a"))}
def M24a : Finset Triple :=
  {tp "p" (.lit (.int 2)), tp "p" (.lit (.int 4)), tp "p" (.lit (.str "a"))}

/-- The triple expression of Example 3,
`e = p @T_even ; (p @T_<5* | p @T_str)`. -/
def e_ex3 : TripleExpr :=
  .seq (.tc "p" "T_even") (.choice (.star (.tc "p" "T_lt5")) (.tc "p" "T_str"))

/-- A fuel bound that is sufficient for all the proofs in Examples 3-5.
`e_ex3` has depth 4, and the deepest `extends` chain below,
`x4 → x6 → x3 → x0`, has 4 levels. -/
def bigFuel : ℕ := 10

/-- `M24, τ ⊨ e` (Example 3). Split it into `{(n,p,2)}` (which satisfies
`p @T_even`) and `{(n,p,4)}` (which satisfies `(p @T_<5)*` with one
part). -/
theorem M24_satisfies_e : SatisfiesEFuel bigFuel S_ex5 default τ_ex3 M24 e_ex3 := by
  refine ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.int 4))}, ⟨by decide, by decide⟩, ?_, ?_⟩
  · exact ⟨n_ex3, .lit (.int 2), rfl, by decide⟩
  · refine Or.inl ⟨[{tp "p" (.lit (.int 4))}], ⟨by decide, by decide⟩, ?_⟩
    intro Ni hNi
    simp only [List.mem_singleton] at hNi
    subst hNi
    exact ⟨n_ex3, .lit (.int 4), rfl, by decide⟩

/-- `M246, τ ⊨ e` (Example 3). Split it into `{(n,p,6)}` (which satisfies
`p @T_even`) and `{(n,p,2),(n,p,4)}` (which satisfies `(p @T_<5)*` with
two parts). -/
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

/-- `M2a, τ ⊨ e` (Example 3). Split it into `{(n,p,2)}` (which satisfies
`p @T_even`) and `{(n,p,"a")}` (which satisfies `p @T_str`). -/
theorem M2a_satisfies_e : SatisfiesEFuel bigFuel S_ex5 default τ_ex3 M2a e_ex3 := by
  refine ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.str "a"))}, ⟨by decide, by decide⟩, ?_, ?_⟩
  · exact ⟨n_ex3, .lit (.int 2), rfl, by decide⟩
  · exact Or.inr ⟨n_ex3, .lit (.str "a"), rfl, by decide⟩

/-- `x` is in a piece of a `List.foldr (· ∪ ·) ∅` union. This is the
converse of `mem_subset_foldr_union` in `RepBound.lean`. -/
private theorem mem_of_mem_foldr_union {α : Type*} [DecidableEq α] (l : List (Finset α))
    {x : α} (hx : x ∈ l.foldr (· ∪ ·) ∅) : ∃ N ∈ l, x ∈ N := by
  induction l with
  | nil => simp at hx
  | cons N l ih =>
      rw [List.foldr_cons, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact ⟨N, List.mem_cons_self, hx⟩
      · obtain ⟨N', hN', hxN'⟩ := ih hx
        exact ⟨N', List.mem_cons_of_mem _ hN', hxN'⟩

/-- `M24a, τ ¬⊨ e` (the fourth fact of Example 3). No split of `M24a`
satisfies `e`. (`M24`, `M246` and `M2a` have such a split.) -/
theorem M24a_not_satisfies_e : ¬ SatisfiesEFuel bigFuel S_ex5 default τ_ex3 M24a e_ex3 := by
  rintro ⟨N1, N2, ⟨hdisj, hunion⟩, ⟨n1, o1, hN1eq, hty1⟩, hN2⟩
  have ha_mem : tp "p" (.lit (.str "a")) ∈ M24a := by decide
  have ha_notin_N1 : tp "p" (.lit (.str "a")) ∉ N1 := by
    rw [hN1eq, Finset.mem_singleton]
    rintro heq
    have ho1 : o1 = .lit (.str "a") := by
      simp only [tp] at heq; injection heq with _ _ ho1; exact ho1.symm
    rw [ho1] at hty1
    simp [Typing.has, τ_ex3] at hty1
  have ha_mem_N2 : tp "p" (.lit (.str "a")) ∈ N2 := by
    rcases Finset.mem_union.mp (hunion ▸ ha_mem) with h | h
    · exact absurd h ha_notin_N1
    · exact h
  rcases (hN2 : SatisfiesEFuel _ S_ex5 default τ_ex3 N2 (.star (.tc "p" "T_lt5")) ∨
      SatisfiesEFuel _ S_ex5 default τ_ex3 N2 (.tc "p" "T_str")) with hN2star | hN2str
  · obtain ⟨Ns, ⟨-, hunion2⟩, hall⟩ := hN2star
    obtain ⟨Ni, hNi_mem, ha_in_Ni⟩ := mem_of_mem_foldr_union Ns (hunion2 ▸ ha_mem_N2)
    obtain ⟨ni, oi, hNieq, htyi⟩ := hall Ni hNi_mem
    rw [hNieq, Finset.mem_singleton] at ha_in_Ni
    have hoi : oi = .lit (.str "a") := by
      simp only [tp] at ha_in_Ni; injection ha_in_Ni with _ _ hoi; exact hoi.symm
    rw [hoi] at htyi
    simp [Typing.has, τ_ex3] at htyi
  · obtain ⟨n2, o2, hN2eq, -⟩ := hN2str
    have hcardEq := Finset.card_union_of_disjoint hdisj
    rw [← hunion, hN1eq, hN2eq] at hcardEq
    simp only [Finset.card_singleton] at hcardEq
    have hcard3 : M24a.card = 3 := by decide
    omega

/-! The prerequisites for the decidability of `S_ex5`
(`satisfiesFuel_decidable` and `satisfiesMFuel_decidable` in
`ShexLean.Shex2025Inheritance.Decidable`). Each `SatisfiesFuel` or
`SatisfiesMFuel` claim that Examples 4 and 5 show needs them. -/

theorem S_ex5_XClosed : S_ex5.XClosed := by unfold Schema.XClosed; decide

theorem S_ex5_RestrOk : S_ex5.RestrOk := by
  intro x hx u hu
  fin_cases hx <;> (simp_all [S_ex5, ShapeExpr.restrOf]; try subst hu; trivial)

end ShexLean.Inheritance

namespace Examples

open ShexLean.Inheritance (e_ex3 M24 M246 M2a M24a S_ex5 τ_ex3 bigFuel satisfiesEFuel_decidable)
open ShexLean (Graph.render Typing.render renderDecide)

/-- The triple expression of Example 3, matched against `M24`, `M246`,
`M2a` and `M24a`.

* `graphText` and `typingText` render the real `Finset Triple` and
  `Typing` values.
* Each claim `M,τ ⊨ e` is a `native_decide` computation with
  `satisfiesEFuel_decidable`.

This is decidable with no condition, because Table 1 never uses
`NodeConstraint` or `extends`. Thus, no `XClosed`, `RestrOk` or `FOk`
witnesses are necessary here. (The `SatisfiesFuel` claims in the other
2025 examples need them.) -/
def inheritance2025TripleMatch : Example where
  name := "inheritance2025-example3-triple-match"
  summary := "Triple expression p@T_even;(p@T_<5*|p@T_str) matched against four sets."
  schemaText := s!"e = {e_ex3.render}"
  graphText :=
    s!"M24  = {Graph.render M24}\n" ++
    s!"M246 = {Graph.render M246}\n" ++
    s!"M2a  = {Graph.render M2a}\n" ++
    s!"M24a = {Graph.render M24a}"
  typingText :=
    s!"τ = {Typing.render τ_ex3}\n" ++
    s!"M24, τ ⊨ e = {renderDecide (satisfiesEFuel_decidable bigFuel S_ex5 default τ_ex3 M24 e_ex3)}\n" ++
    s!"M246, τ ⊨ e = {renderDecide (satisfiesEFuel_decidable bigFuel S_ex5 default τ_ex3 M246 e_ex3)}\n" ++
    s!"M2a, τ ⊨ e = {renderDecide (satisfiesEFuel_decidable bigFuel S_ex5 default τ_ex3 M2a e_ex3)}\n" ++
    s!"M24a, τ ⊨ e = {renderDecide (satisfiesEFuel_decidable bigFuel S_ex5 default τ_ex3 M24a e_ex3)}"

end Examples
