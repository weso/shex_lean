import ShexLean.Inheritance.Semantics

/-!
Worked examples from the 2025 "Shape Expressions with Inheritance" paper
(§2 and §4.1-4.2), formalized as regression checks that
`ShexLean/Inheritance/Syntax.lean`/`Semantics.lean` actually behave as the
paper's own examples say they should — the same role
`ShexLean/Examples.lean`/`examples/Introduction.lean` play for the 2017
formalism.

Two representational simplifications, both purely about the *data* used,
not the semantics:

- The RDF model's `Literal` (`ShexLean/RDF.lean`) has only `str`/`int`
  constructors, no float. Fig. 1/2's `T_float` and the coordinate/radius
  values (`10.1`, `7.2`, `0.2`, `-2.3`) are approximated with `Literal.int`
  values instead — the *structure* of the example (which properties are
  required, which node constraint decides `T_float`-ness) is preserved
  faithfully, only the exact numerals differ.
- Example 5's schema is stated in the paper as
  `S = (Y, {x1,...,x6}, def, ∅)`, but `def(x1)` and `def(x3)` both use
  `extends x0`, i.e. `x0` genuinely needs to be a member of the
  extendable-label set `X` for `Schema.anc`/`Schema.WellFormedX` to see it
  as a node of `H_S` at all (Definition 3: `H_S`'s vertex set *is* `X`).
  This looks like a minor omission in the paper's own statement of the
  example (`x0`'s own definition, `extends _ ⟨p @Teven⟩`, is exactly the
  form Definition 2 requires of an `X`-label). This file's `x_ex5.X`
  includes `x0`.
-/

namespace ShexLean.Inheritance

/-! ### Node constraints for `Example 3`/`Example 4`/`Example 5` (§4.1) -/

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
def n_ex3 : RDFNode := .iri "n"

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

/-- A fuel bound generous enough for every proof in this file (`e_ex3` has
depth 4, and the deepest `extends` chain used below, `x4 → x6 → x3 → x0`,
is 4 levels; `10` is comfortably more than either needs). -/
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

/-- `M24, τ ⊨ def(x1)` (Example 4/5): `def(x1) = extends x0 ⟨p @T_even⟩`,
so `anc({x0}) = {x1's own } ... = {x0}` and `M24` splits into `M'`
(satisfying `⟨p @T_even⟩`) and `Mx0` (satisfying `ext-te(x0) = p @T_even`,
`x0` having no restriction of its own). -/
theorem M24_satisfies_defx1 :
    SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M24 (S_ex5.shapeDef "x1") := by
  have hx1shape : S_ex5.shapeDef "x1" = .extends {"x0"} ⟨false, none, .tc "p" "T_even"⟩ := rfl
  rw [hx1shape]
  have hx0shape : S_ex5.shapeDef "x0" = .extends ∅ ⟨false, none, .tc "p" "T_even"⟩ := rfl
  have hx0edge : ∀ c, ¬ S_ex5.extEdge "x0" c := by
    intro c hc
    unfold Schema.extEdge at hc
    rw [hx0shape] at hc
    simp [ShapeExpr.extendsTargets] at hc
  have hx0 : ∀ x', Relation.ReflTransGen S_ex5.extEdge "x0" x' → x' = "x0" := by
    intro x' h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
    · exact heq.symm
    · exact absurd hc (hx0edge c)
  have hanc0 : S_ex5.anc "x0" = {"x0"} := by
    apply Finset.ext
    intro x'
    unfold Schema.anc
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact hx0 x' h
    · rintro rfl; exact ⟨by decide, Relation.ReflTransGen.refl⟩
  have hanc : S_ex5.ancSet {"x0"} = {"x0"} := by
    unfold Schema.ancSet; simp [hanc0]
  refine ⟨{tp "p" (.lit (.int 2))}, fun _ => {tp "p" (.lit (.int 4))}, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hanc]; decide
  · rw [hanc]
    intro a ha b hb hab
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · rw [hanc]; decide
  · exact ⟨n_ex3, .lit (.int 2), rfl, by decide⟩
  · rw [hanc]
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    show SatisfiesEFuel bigFuel S_ex5 default τ_ex3 {tp "p" (.lit (.int 4))}
      (S_ex5.shapeDef "x0").extTe
    exact ⟨n_ex3, .lit (.int 4), rfl, by decide⟩
  · rw [hanc]
    intro x hx u hu
    simp only [Finset.mem_singleton] at hx
    subst hx
    rw [hx0shape] at hu
    simp [ShapeExpr.restrOf] at hu

/-! ### §2's motivating example (Fig. 1/2)

Only the `Attribute` shape and node `a1` are formalized here, not the full
multiple-inheritance `ColouredCircle` chain of Fig. 1/2/3 — the paper's own
prose ("Nodes a1, a2, a3 satisfy Attribute...") pins down exactly the
`name`/`value` triples `a1` needs to have, which is enough for a faithful,
self-contained regression check without needing to reconstruct every edge
of Fig. 2's graph image. The rest of Fig. 1 (`Coord`, abstract `Figure`,
`Circle`, `Radius`, `ColouredFigure`, and the `ColouredCircle` multiple
extends) is future work, best attempted once `Termination.lean` (and,
later, `CorrectTyping.lean`) exist to test against a *validated* `Satisfies`
rather than the fuel-bounded under-approximation used here. -/

/-- `Attribute → extends _ ⟨name @T_str ; value @T_any⟩` (Fig. 1). -/
def S_fig1 : Schema where
  Y := {"T_str", "T_any"}
  X := {"Attribute"}
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "T_str" => .constraint cStr
    | "T_any" => .constraint (fun _ => True)
    | "Attribute" =>
        .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩
    | _ => .constraint (fun _ => False)

/-- `a1`'s neighbourhood in Fig. 2: `a1 name "radius" ; value 10.1` (the
`value` here approximated as an integer literal, see the module
docstring). -/
def a1 : RDFNode := .iri "a1"
def G_fig1 : Graph := {⟨a1, "name", .lit (.str "radius")⟩, ⟨a1, "value", .lit (.int 10)⟩}

/-- A typing witnessing that `a1`'s `name`/`value` objects have the types
`Attribute` requires — `p @z` triple constraints are resolved against
`τ` (a typing lookup, per Table 1 rule 2/Table 2 rule 10), not by directly
re-invoking `z`'s own node constraint; connecting the two is Definition 4
("correct typing"), not yet formalized. -/
def τ_fig1 : Typing := {(RDFNode.lit (.str "radius"), "T_str"), (RDFNode.lit (.int 10), "T_any")}

/-- `a1` satisfies `Attribute` (Fig. 2's claim "Nodes a1, a2, a3 satisfy
`Attribute`", restricted to `a1`). `Attribute` has no `extends` targets of
its own (`extends _`), so the rule-18 partition is trivial: `M' = M`,
`Mx` vacuous over `anc(∅) = ∅`. -/
theorem a1_satisfies_Attribute :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 a1 (S_fig1.shapeDef "Attribute") := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  rw [hshape]
  have hneigh : neigh G_fig1 a1 = G_fig1 := by decide
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a1) _)
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset ShapeLabel) = ∅ := by
    unfold Schema.ancSet; simp
  refine ⟨G_fig1, fun _ => ∅, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hanc]; decide
  · rw [hanc]; intro a ha; simp at ha
  · rw [hanc]; decide
  · refine ⟨{⟨a1, "name", .lit (.str "radius")⟩}, {⟨a1, "value", .lit (.int 10)⟩},
      ⟨by decide, by decide⟩, ?_, ?_⟩
    · exact ⟨a1, .lit (.str "radius"), rfl, by decide⟩
    · exact ⟨a1, .lit (.int 10), rfl, by decide⟩
  · rw [hanc]; intro x hx; simp at hx
  · rw [hanc]; intro x hx; simp at hx

end ShexLean.Inheritance
