import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2025Inheritance.Stratification
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Worked examples from the 2025 "Shape Expressions with Inheritance" paper
(§2 and §4.1-4.2), formalized as regression checks that
`ShexLean/Shex2025Inheritance/Syntax.lean`/`Semantics.lean` actually behave as the
paper's own examples say they should — the same role
`ShexLean/Shex2017Schemas/Examples.lean`/`examples/Introduction.lean` play for the 2017
formalism.

Two representational simplifications, both purely about the *data* used,
not the semantics:

- The RDF model's `Literal` (`ShexLean/Common/RDF.lean`) has only `str`/`int`
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

/-- Whenever `Me τ M e = M` (every triple of `M` is "consumed" by some
triple constraint of `e`), `M` satisfying `e` (Table 1) lifts directly to
`M` satisfying the trivial `[closed:=false][extra:=none]⟨e⟩` shape (Table
3 rule 17) — `Mnotin` is forced empty since it's always `⊆ M \ Me = M \ M
= ∅`. This is exactly what an `extends X h`'s own `M'` piece needs to
satisfy (`M', τ ⊨ h`, Table 3 rule 18), now that it's checked against `h`
as a shape rather than directly against `h.triples` (see
`ShexLean/Shex2025Inheritance/Termination.lean`'s module docstring for
why). -/
theorem ofShape_of_Me_eq_self {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {M : Finset Triple} {e : TripleExpr} (hMe : Me τ M e = M)
    (hE : SatisfiesEFuel fuel S G τ M e) :
    SatisfiesMFuel (fuel + 1) S G τ M (.ofShape ⟨false, none, e⟩) := by
  refine ⟨?_, ?_, by simp⟩
  · show SatisfiesEFuel fuel S G τ (Me τ M e) e
    rw [hMe]; exact hE
  · show props (Mnotin τ M e) ⊆ (∅ : Finset IRI)
    rw [Finset.subset_empty, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    unfold props at ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    rw [mem_Mnotin] at ht'
    obtain ⟨⟨htM, _⟩, hnotMe⟩ := ht'
    exact hnotMe (by rw [hMe]; exact htM)

/-- A singleton `{(n,p,o)}` satisfying a bare `p @z` triple constraint
under `τ` also satisfies the trivial shape `[closed:=false][extra:=none]
⟨p @z⟩` (rule 17, `.ofShape`) — the special case of `ofShape_of_Me_eq_self`
this file's `.extends` proofs actually need. -/
theorem singleton_tc_ofShape {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {p : IRI} {z : ShapeLabel} {n o : RDFNode} (hty : τ.has o z) :
    SatisfiesMFuel (fuel + 2) S G τ {(⟨n, p, o⟩ : Triple)} (.ofShape ⟨false, none, .tc p z⟩) := by
  apply ofShape_of_Me_eq_self (fuel := fuel + 1) (e := .tc p z) (M := {(⟨n, p, o⟩ : Triple)})
  · apply Finset.Subset.antisymm
    · intro t ht; rw [mem_Me] at ht; exact ht.1
    · intro t ht
      simp only [Finset.mem_singleton] at ht
      subst ht
      rw [mem_Me]
      exact ⟨Finset.mem_singleton_self _, z, by simp [TripleExpr.tcs], hty⟩
  · exact ⟨n, o, rfl, hty⟩

/-- Converse of the reasoning inside `ofShape_of_Me_eq_self`: if every
triple of `M` has a predicate already among `e`'s (so none can escape into
the "extra" bucket), an `M, τ ⊨ [extra:=none]⟨e⟩` witness (Table 3 rule 17)
forces `Me τ M e = M`, i.e. `M` itself, not just some sub-multiset of it,
is exactly what satisfies `e` (Table 1). Needed once a `M', τ ⊨ h`
obligation (Table 3 rule 18's `.ofShape h` piece) must be turned back into
a `SatisfiesEFuel` fact about the concrete `M'` at hand, now that rule 18
no longer checks `h.triples` directly (see
`ShexLean/Shex2025Inheritance/Termination.lean`'s module docstring). -/
theorem Me_eq_self_of_props_subset {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {M : Finset Triple} {e : TripleExpr}
    (hM : SatisfiesMFuel (fuel + 1) S G τ M (.ofShape ⟨false, none, e⟩))
    (hsub : props M ⊆ e.props) :
    Me τ M e = M := by
  obtain ⟨-, hMnotinSub, -⟩ := hM
  apply Finset.Subset.antisymm
  · intro t ht; rw [mem_Me] at ht; exact ht.1
  · intro t ht
    by_contra hnotMe
    have htin : t ∈ Mnotin τ M e := by
      rw [mem_Mnotin]
      exact ⟨⟨ht, hsub (Finset.mem_image_of_mem Triple.pred ht)⟩, hnotMe⟩
    have := hMnotinSub (Finset.mem_image_of_mem Triple.pred htin)
    simp at this

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

/-! ### Example 4 (§4.1, Table 3 rule 17): `closed`/`extra` semantics

Reuses Example 3's `M24`/`M246`/`M2a`/`M24a`/`τ_ex3`, but a *different*
triple expression: `e = p @T_even ; p @T_lt5` (a bare two-element sequence,
no `|`/`*` — unlike `e_ex3`, this one needs `M` to consist of *exactly*
two triples once the shape's own `closed`/`extra` bookkeeping strips away
anything not "consumed", which is exactly what this section exercises and
Example 3 never did (a bare, unwrapped triple expression has no
`closed`/`extra` to speak of at all). -/

/-- Example 4's triple expression `e = p @T_even ; p @T_lt5`. -/
def e_ex4 : TripleExpr := .seq (.tc "p" "T_even") (.tc "p" "T_lt5")

/-- Any `M` satisfying a bare `e1;e2` sequence of two triple constraints
has exactly two elements — each side of the split is forced to a singleton
by `.tc`'s own semantics. The cardinality fact behind Example 4's negative
claims (`M2a`/`M246` can't satisfy `e_ex4`, for unrelated reasons: `M2a`'s
matching part is too small, `M246` itself is too big). -/
theorem seq_tc_tc_card_two {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ} {M : Finset Triple}
    {p1 : IRI} {z1 : ShapeLabel} {p2 : IRI} {z2 : ShapeLabel}
    (hSat : SatisfiesEFuel (fuel + 2) S G τ M (.seq (.tc p1 z1) (.tc p2 z2))) : M.card = 2 := by
  obtain ⟨M1, M2, ⟨hdisj, hunion⟩, ⟨n1, o1, hM1, _⟩, ⟨n2, o2, hM2, _⟩⟩ := hSat
  subst hM1; subst hM2
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton, Finset.card_singleton]

/-- `M24, τ ⊨ ⟨e⟩` (Example 4): both of `M24`'s triples are "consumed" by
`e_ex4` (`2` matches `p @T_even`, `4` matches `p @T_lt5`), so `Me = M24`
and `Mnotin` is automatically empty. -/
theorem M24_satisfies_ofShape_e4 :
    SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M24 (.ofShape ⟨false, none, e_ex4⟩) := by
  apply ofShape_of_Me_eq_self (e := e_ex4)
  · apply Finset.Subset.antisymm
    · intro t ht; rw [mem_Me] at ht; exact ht.1
    · intro t ht
      have ht2 : t = tp "p" (.lit (.int 2)) ∨ t = tp "p" (.lit (.int 4)) := by
        unfold M24 at ht; simpa using ht
      rw [mem_Me]
      refine ⟨ht, "T_even", ?_, ?_⟩
      all_goals rcases ht2 with rfl | rfl <;> decide
  · refine ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.int 4))}, ⟨by decide, by decide⟩, ?_, ?_⟩
    · exact ⟨n_ex3, .lit (.int 2), rfl, by decide⟩
    · exact ⟨n_ex3, .lit (.int 4), rfl, by decide⟩

/-- `M2a, τ ¬⊨ ⟨e⟩` (Example 4): only `2` (not `"a"`) matches any triple
constraint of `e_ex4`, so `Me τ M2a e_ex4` has one element, but `e_ex4`
needs exactly two (`seq_tc_tc_card_two`). -/
theorem M2a_not_satisfies_ofShape_e4 :
    ¬ SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M2a (.ofShape ⟨false, none, e_ex4⟩) := by
  rintro ⟨hE, -, -⟩
  have hcard : (Me τ_ex3 M2a e_ex4).card = 2 := seq_tc_tc_card_two hE
  have hMe_sub : Me τ_ex3 M2a e_ex4 ⊆ {tp "p" (.lit (.int 2))} := by
    intro t ht
    rw [mem_Me] at ht
    obtain ⟨htM, z, hz, hty⟩ := ht
    unfold M2a at htM
    simp only [Finset.mem_insert, Finset.mem_singleton] at htM
    rcases htM with rfl | rfl
    · exact Finset.mem_singleton_self _
    · simp only [tp, e_ex4, TripleExpr.tcs, Finset.mem_union, Finset.mem_singleton,
        Prod.mk.injEq] at hz
      rcases hz with ⟨-, hz⟩ | ⟨-, hz⟩ <;> subst hz <;> exact absurd hty (by decide)
  have : (Me τ_ex3 M2a e_ex4).card ≤ 1 := Finset.card_le_card hMe_sub |>.trans (by decide)
  omega

/-- `M246, τ ¬⊨ ⟨e⟩` (Example 4): `M246` already has three elements, too
many for `e_ex4`'s exactly-two requirement, regardless of which match. -/
theorem M246_not_satisfies_ofShape_e4 :
    ¬ SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M246 (.ofShape ⟨false, none, e_ex4⟩) := by
  rintro ⟨hE, hMnotin, -⟩
  have hcard := seq_tc_tc_card_two hE
  have hMnotin_empty : Mnotin τ_ex3 M246 e_ex4 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have := hMnotin (Finset.mem_image_of_mem Triple.pred ht)
    simp at this
  have hMe_eq : Me τ_ex3 M246 e_ex4 = M246 := by
    apply Finset.Subset.antisymm
    · intro t ht; rw [mem_Me] at ht; exact ht.1
    · intro t ht
      by_contra hnotMe
      have : t ∈ Mnotin τ_ex3 M246 e_ex4 := by
        rw [mem_Mnotin]
        refine ⟨⟨ht, ?_⟩, hnotMe⟩
        unfold M246 at ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl <;> simp [tp, e_ex4, TripleExpr.props, TripleExpr.tcs]
      rw [hMnotin_empty] at this
      exact absurd this (Finset.notMem_empty t)
  rw [hMe_eq] at hcard
  have : M246.card = 3 := by unfold M246; decide
  omega

/-- `M24a, τ ⊨ extra {p} ⟨e⟩` (Example 4): the leftover `"a"`-triple is
allowed since its property `p` is listed in `extra`. -/
theorem M24a_satisfies_extra :
    SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M24a (.ofShape ⟨false, some {"p"}, e_ex4⟩) := by
  have hMe_eq : Me τ_ex3 M24a e_ex4 = M24 := by
    apply Finset.Subset.antisymm
    · intro t ht
      rw [mem_Me] at ht
      obtain ⟨htM, z, hz, hty⟩ := ht
      unfold M24a at htM; unfold M24
      simp only [Finset.mem_insert, Finset.mem_singleton] at htM ⊢
      rcases htM with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp only [tp, e_ex4, TripleExpr.tcs, Finset.mem_union, Finset.mem_singleton,
          Prod.mk.injEq] at hz
        rcases hz with ⟨-, hz⟩ | ⟨-, hz⟩ <;> subst hz <;> exact absurd hty (by decide)
    · intro t ht
      rw [mem_Me]
      unfold M24 at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      unfold M24a
      refine ⟨?_, "T_even", ?_, ?_⟩ <;> rcases ht with rfl | rfl <;> decide
  refine ⟨by rw [hMe_eq]; exact ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.int 4))},
    ⟨by decide, by decide⟩, ⟨n_ex3, .lit (.int 2), rfl, by decide⟩,
    ⟨n_ex3, .lit (.int 4), rfl, by decide⟩⟩, ?_, by simp⟩
  intro t ht
  unfold props at ht
  obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
  rw [mem_Mnotin, hMe_eq] at ht'
  obtain ⟨⟨htM, hpred⟩, htnotMe⟩ := ht'
  unfold M24a at htM
  simp only [Finset.mem_insert, Finset.mem_singleton] at htM
  rcases htM with rfl | rfl | rfl
  · exact absurd (by unfold M24; decide) htnotMe
  · exact absurd (by unfold M24; decide) htnotMe
  · decide

/-- `M24a ∪ {(n,q,2)}, τ ⊨ extra {p} ⟨e⟩` (Example 4): the extra
`q`-predicated triple is invisible to a non-closed shape (`q ∉
props(e_ex4) = {p}`, so it is captured by neither `M^e` nor `M^{e'}` at
all — Table 3 rule 17's `closed`/`extra` bookkeeping only ever inspects
`M^{e'}`, whose own filter already excludes predicates outside
`props(e)`). Contrasts with `M24a_q_not_satisfies_closed_extra` right
below: adding `closed` is exactly what makes this same set fail. -/
theorem M24a_q_satisfies_extra :
    SatisfiesMFuel bigFuel S_ex5 default τ_ex3 (M24a ∪ {tp "q" (.lit (.int 2))})
      (.ofShape ⟨false, some {"p"}, e_ex4⟩) := by
  have hMe_eq : Me τ_ex3 (M24a ∪ {tp "q" (.lit (.int 2))}) e_ex4 = M24 := by
    apply Finset.Subset.antisymm
    · intro t ht
      rw [mem_Me] at ht
      obtain ⟨htM, z, hz, hty⟩ := ht
      simp only [M24a, M24, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at htM ⊢
      simp only [e_ex4, TripleExpr.tcs, Finset.mem_union, Finset.mem_singleton,
        Prod.mk.injEq] at hz
      rcases htM with (rfl | rfl | rfl) | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rcases hz with ⟨-, hz⟩ | ⟨-, hz⟩ <;> subst hz <;> exact absurd hty (by decide)
      · rcases hz with ⟨hz, -⟩ | ⟨hz, -⟩ <;> exact absurd hz (by decide)
    · intro t ht
      rw [mem_Me]
      unfold M24 at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      refine ⟨?_, "T_even", ?_, ?_⟩ <;> rcases ht with rfl | rfl <;>
        first | (unfold M24a; decide) | decide
  refine ⟨by rw [hMe_eq]; exact ⟨{tp "p" (.lit (.int 2))}, {tp "p" (.lit (.int 4))},
    ⟨by decide, by decide⟩, ⟨n_ex3, .lit (.int 2), rfl, by decide⟩,
    ⟨n_ex3, .lit (.int 4), rfl, by decide⟩⟩, ?_, by simp⟩
  intro t ht
  unfold props at ht
  obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
  rw [mem_Mnotin, hMe_eq] at ht'
  obtain ⟨⟨htM, hpred⟩, htnotMe⟩ := ht'
  simp only [M24a, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at htM
  rcases htM with (rfl | rfl | rfl) | rfl
  · exact absurd (by unfold M24; decide) htnotMe
  · exact absurd (by unfold M24; decide) htnotMe
  · decide
  · exact absurd hpred (by decide)

/-- `M24a ∪ {(n,q,2)}, τ ¬⊨ closed extra {p} ⟨e⟩` (Example 4): `closed`
now forbids the extra `q`-predicated triple entirely, since `q ∉
props(e_ex4) ∪ {p} = {p}`. -/
theorem M24a_q_not_satisfies_closed_extra :
    ¬ SatisfiesMFuel bigFuel S_ex5 default τ_ex3 (M24a ∪ {tp "q" (.lit (.int 2))})
      (.ofShape ⟨true, some {"p"}, e_ex4⟩) := by
  rintro ⟨-, -, hclosed⟩
  have hpq : "q" ∈ props (M24a ∪ {tp "q" (.lit (.int 2))}) :=
    Finset.mem_image_of_mem Triple.pred (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have := hclosed rfl hpq
  simp only [Finset.mem_union] at this
  rcases this with h | h
  · simp [e_ex4, TripleExpr.props, TripleExpr.tcs] at h
  · simp at h

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
  · exact singleton_tc_ofShape (by decide)
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

/-- `M246, τ ⊨ def(x2)` (Example 5): `def(x2) = extends x1 ⟨p @T_<5⟩`, so
`anc({x1}) = {x1, x0}` (`x1` extends `x0`) and `M246` splits three ways:
`M'={2}` (satisfying `⟨p @T_<5⟩`), `Mx1={4}`, `Mx0={6}` (both satisfying
`ext-te = p @T_even`, neither `x0` nor `x1` having a restriction). -/
theorem M246_satisfies_defx2 :
    SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M246 (S_ex5.shapeDef "x2") := by
  have hx2shape : S_ex5.shapeDef "x2" = .extends {"x1"} ⟨false, none, .tc "p" "T_lt5"⟩ := rfl
  rw [hx2shape]
  have hx1shape : S_ex5.shapeDef "x1" = .extends {"x0"} ⟨false, none, .tc "p" "T_even"⟩ := rfl
  have hx0shape : S_ex5.shapeDef "x0" = .extends ∅ ⟨false, none, .tc "p" "T_even"⟩ := rfl
  have hx0edge : ∀ c, ¬ S_ex5.extEdge "x0" c := by
    intro c hc; unfold Schema.extEdge at hc; rw [hx0shape] at hc
    simp [ShapeExpr.extendsTargets] at hc
  have hx0 : ∀ x', Relation.ReflTransGen S_ex5.extEdge "x0" x' → x' = "x0" := by
    intro x' h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
    · exact heq.symm
    · exact absurd hc (hx0edge c)
  have hx1edge : S_ex5.extEdge "x1" "x0" := by
    unfold Schema.extEdge; rw [hx1shape]; simp [ShapeExpr.extendsTargets]
  have hx1 : ∀ x', Relation.ReflTransGen S_ex5.extEdge "x1" x' → x' = "x1" ∨ x' = "x0" := by
    intro x' h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, hc'⟩
    · exact Or.inl heq.symm
    · have hceq : c = "x0" := by
        unfold Schema.extEdge at hc; rw [hx1shape] at hc
        simpa [ShapeExpr.extendsTargets] using hc
      exact Or.inr (hceq ▸ hx0 x' (hceq ▸ hc'))
  have hanc1 : S_ex5.anc "x1" = {"x1", "x0"} := by
    apply Finset.ext; intro x'
    unfold Schema.anc
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact hx1 x' h
    · rintro (rfl | rfl)
      · exact ⟨by decide, Relation.ReflTransGen.refl⟩
      · exact ⟨by decide, Relation.ReflTransGen.single hx1edge⟩
  have hancSet1 : S_ex5.ancSet {"x1"} = {"x1", "x0"} := by unfold Schema.ancSet; simp [hanc1]
  refine ⟨{tp "p" (.lit (.int 2))},
    fun x => if x = "x1" then {tp "p" (.lit (.int 4))} else {tp "p" (.lit (.int 6))},
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hancSet1]; decide
  · rw [hancSet1]
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp_all [Function.onFun] <;> decide
  · rw [hancSet1]; decide
  · exact singleton_tc_ofShape (by decide)
  · rw [hancSet1]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨n_ex3, .lit (.int 4), rfl, by decide⟩
    · exact ⟨n_ex3, .lit (.int 6), rfl, by decide⟩
  · rw [hancSet1]
    intro x hx u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [hx1shape] at hu; simp [ShapeExpr.restrOf] at hu
    · rw [hx0shape] at hu; simp [ShapeExpr.restrOf] at hu

/-- `M24, τ ¬⊨ def(x2)` (Example 5): `def(x2)`'s rule-18 partition needs
*three* pairwise-disjoint singletons (`M'`, `Mx1`, `Mx0`, each forced by a
bare `.tc`), so any satisfying `M` has exactly three elements — but
`M24.card = 2`. -/
theorem M24_not_satisfies_defx2 :
    ¬ SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M24 (S_ex5.shapeDef "x2") := by
  have hx2shape : S_ex5.shapeDef "x2" = .extends {"x1"} ⟨false, none, .tc "p" "T_lt5"⟩ := rfl
  rw [hx2shape]
  rintro ⟨M', Mx, ⟨hdisjM', hpw, hunion⟩, hM', hMx, -⟩
  have hancSet1 : S_ex5.ancSet {"x1"} = {"x1", "x0"} := by
    have hx1shape : S_ex5.shapeDef "x1" = .extends {"x0"} ⟨false, none, .tc "p" "T_even"⟩ := rfl
    have hx0shape : S_ex5.shapeDef "x0" = .extends ∅ ⟨false, none, .tc "p" "T_even"⟩ := rfl
    have hx0edge : ∀ c, ¬ S_ex5.extEdge "x0" c := by
      intro c hc; unfold Schema.extEdge at hc; rw [hx0shape] at hc
      simp [ShapeExpr.extendsTargets] at hc
    have hx0 : ∀ x', Relation.ReflTransGen S_ex5.extEdge "x0" x' → x' = "x0" := by
      intro x' h
      rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
      · exact heq.symm
      · exact absurd hc (hx0edge c)
    have hx1edge : S_ex5.extEdge "x1" "x0" := by
      unfold Schema.extEdge; rw [hx1shape]; simp [ShapeExpr.extendsTargets]
    have hx1 : ∀ x', Relation.ReflTransGen S_ex5.extEdge "x1" x' → x' = "x1" ∨ x' = "x0" := by
      intro x' h
      rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, hc'⟩
      · exact Or.inl heq.symm
      · have hceq : c = "x0" := by
          unfold Schema.extEdge at hc; rw [hx1shape] at hc
          simpa [ShapeExpr.extendsTargets] using hc
        exact Or.inr (hceq ▸ hx0 x' (hceq ▸ hc'))
    have hanc1 : S_ex5.anc "x1" = {"x1", "x0"} := by
      apply Finset.ext; intro x'
      unfold Schema.anc
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩; exact hx1 x' h
      · rintro (rfl | rfl)
        · exact ⟨by decide, Relation.ReflTransGen.refl⟩
        · exact ⟨by decide, Relation.ReflTransGen.single hx1edge⟩
    unfold Schema.ancSet; simp [hanc1]
  have hx0anc : ("x0" : ShapeLabel) ∈ S_ex5.ancSet {"x1"} := by rw [hancSet1]; decide
  have hx1anc : ("x1" : ShapeLabel) ∈ S_ex5.ancSet {"x1"} := by rw [hancSet1]; decide
  have hM'sub : M' ⊆ M24 := hunion ▸ Finset.subset_union_left
  have hM'propsub : props M' ⊆ (TripleExpr.tc "p" "T_lt5" : TripleExpr).props := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    have ht24 := hM'sub ht
    unfold M24 at ht24
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht24
    simp only [TripleExpr.props, TripleExpr.tcs, Finset.image_singleton, Finset.mem_singleton]
    rcases ht24 with rfl | rfl <;> rfl
  have hMeeq : Me τ_ex3 M' (TripleExpr.tc "p" "T_lt5") = M' :=
    Me_eq_self_of_props_subset hM' hM'propsub
  have hM'card : M'.card = 1 := by
    obtain ⟨hEMe, -, -⟩ := hM'
    rw [hMeeq] at hEMe
    obtain ⟨n, o, hM'eq, -⟩ := hEMe
    rw [hM'eq]; exact Finset.card_singleton _
  have hMx1card : (Mx "x1").card = 1 := by
    obtain ⟨n, o, hMxeq, -⟩ := hMx "x1" hx1anc; rw [hMxeq]; exact Finset.card_singleton _
  have hMx0card : (Mx "x0").card = 1 := by
    obtain ⟨n, o, hMxeq, -⟩ := hMx "x0" hx0anc; rw [hMxeq]; exact Finset.card_singleton _
  have hbUcard : ((S_ex5.ancSet {"x1"}).biUnion Mx).card = 2 := by
    rw [hancSet1] at hpw ⊢
    rw [Finset.card_biUnion hpw, Finset.sum_insert (by decide), Finset.sum_singleton, hMx1card,
      hMx0card]
  have hcard : M24.card = M'.card + ((S_ex5.ancSet {"x1"}).biUnion Mx).card := by
    rw [hunion]; exact Finset.card_union_of_disjoint hdisjM'
  rw [hM'card, hbUcard] at hcard
  have : M24.card = 2 := by unfold M24; decide
  omega

/-- `M2a, τ ⊨ def(x5)` (Example 5): `def(x5) = extends x0 extra {p} ⟨ε⟩`,
so `M'` must satisfy the *shape* `[extra {p}]⟨ε⟩` — allowing the leftover
`"a"`-triple, which a bare `⟨ε⟩` (forcing `M' = ∅`) would not — and
`Mx0={2}` satisfies `ext-te(x0) = p @T_even`. -/
theorem M2a_satisfies_defx5 :
    SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M2a (S_ex5.shapeDef "x5") := by
  have hx5shape : S_ex5.shapeDef "x5" = .extends {"x0"} ⟨false, some {"p"}, .empty⟩ := rfl
  rw [hx5shape]
  have hx0shape : S_ex5.shapeDef "x0" = .extends ∅ ⟨false, none, .tc "p" "T_even"⟩ := rfl
  have hx0edge : ∀ c, ¬ S_ex5.extEdge "x0" c := by
    intro c hc; unfold Schema.extEdge at hc; rw [hx0shape] at hc
    simp [ShapeExpr.extendsTargets] at hc
  have hx0 : ∀ x', Relation.ReflTransGen S_ex5.extEdge "x0" x' → x' = "x0" := by
    intro x' h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
    · exact heq.symm
    · exact absurd hc (hx0edge c)
  have hanc0 : S_ex5.anc "x0" = {"x0"} := by
    apply Finset.ext; intro x'
    unfold Schema.anc
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact hx0 x' h
    · rintro rfl; exact ⟨by decide, Relation.ReflTransGen.refl⟩
  have hancSet : S_ex5.ancSet {"x0"} = {"x0"} := by unfold Schema.ancSet; simp [hanc0]
  refine ⟨{tp "p" (.lit (.str "a"))}, fun _ => {tp "p" (.lit (.int 2))}, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hancSet]; decide
  · rw [hancSet]; intro a ha b hb hab
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · rw [hancSet]; decide
  · have hMe_empty : Me τ_ex3 {tp "p" (.lit (.str "a"))} (TripleExpr.empty) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      rw [mem_Me] at ht
      obtain ⟨-, z, hz, -⟩ := ht
      simp [TripleExpr.tcs] at hz
    have hMnotin_empty : Mnotin τ_ex3 {tp "p" (.lit (.str "a"))} (TripleExpr.empty) = ∅ := by
      unfold Mnotin
      simp [TripleExpr.props, TripleExpr.tcs]
    refine ⟨?_, ?_, by simp⟩
    · show SatisfiesEFuel _ S_ex5 default τ_ex3
        (Me τ_ex3 {tp "p" (.lit (.str "a"))} TripleExpr.empty) TripleExpr.empty
      rw [hMe_empty]; rfl
    · show props (Mnotin τ_ex3 {tp "p" (.lit (.str "a"))} (TripleExpr.empty)) ⊆ ({"p"} : Finset IRI)
      rw [hMnotin_empty]; simp [props]
  · rw [hancSet]
    intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
    exact ⟨n_ex3, .lit (.int 2), rfl, by decide⟩
  · rw [hancSet]
    intro x hx u hu
    simp only [Finset.mem_singleton] at hx; subst hx
    rw [hx0shape] at hu; simp [ShapeExpr.restrOf] at hu

/-- `M24a, τ ¬⊨ def(x6)` (Example 5): `def(x6) = extends x3 ⟨p @T_even⟩`,
and `x3`'s own `extra {p}` (from `x5`'s sibling definition, *not* an
ancestor of `x6` at all) plays no role here — `x6` extends `x3` (whose own
`h` is `⟨p @T_even⟩ and ⟨(p@T_>5)*⟩`, no `extra`), so nothing licenses
`M24a`'s leftover `"a"`-triple, and (as `M24_not_satisfies_defx2` already
shows for a similarly-shaped chain) the underlying cardinality doesn't
even work out — `x3` itself needs 2 further p-triples beyond `x6`'s own,
none of which the paper's four sets provide without reuse. We only check
the specific `"a"`-triple obstruction the paper's own claim highlights. -/
theorem M24a_not_satisfies_defx6 :
    ¬ SatisfiesMFuel bigFuel S_ex5 default τ_ex3 M24a (S_ex5.shapeDef "x6") := by
  have hx6shape : S_ex5.shapeDef "x6" = .extends {"x3"} ⟨false, none, .tc "p" "T_even"⟩ := rfl
  rw [hx6shape]
  rintro ⟨M', Mx, ⟨-, -, hunion⟩, hM', hMx, -⟩
  have hx3shape : S_ex5.shapeDef "x3" = .and (.extends {"x0"} ⟨false, none, .tc "p" "T_even"⟩)
      (.ofShape ⟨false, none, .star (.tc "p" "T_gt5")⟩) := rfl
  have hx0shape : S_ex5.shapeDef "x0" = .extends ∅ ⟨false, none, .tc "p" "T_even"⟩ := rfl
  have hx3edge : ∀ c, S_ex5.extEdge "x3" c ↔ c = "x0" := by
    intro c; unfold Schema.extEdge; rw [hx3shape]
    simp [ShapeExpr.extendsTargets]
  have hx0edge : ∀ c, ¬ S_ex5.extEdge "x0" c := by
    intro c hc; unfold Schema.extEdge at hc; rw [hx0shape] at hc
    simp [ShapeExpr.extendsTargets] at hc
  have hx0 : ∀ x', Relation.ReflTransGen S_ex5.extEdge "x0" x' → x' = "x0" := by
    intro x' h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
    · exact heq.symm
    · exact absurd hc (hx0edge c)
  have hx3 : ∀ x', Relation.ReflTransGen S_ex5.extEdge "x3" x' → x' = "x3" ∨ x' = "x0" := by
    intro x' h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, hc'⟩
    · exact Or.inl heq.symm
    · have hceq : c = "x0" := (hx3edge c).mp hc
      exact Or.inr (hceq ▸ hx0 x' (hceq ▸ hc'))
  have hanc3 : S_ex5.anc "x3" = {"x3", "x0"} := by
    apply Finset.ext; intro x'
    unfold Schema.anc
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact hx3 x' h
    · rintro (rfl | rfl)
      · exact ⟨by decide, Relation.ReflTransGen.refl⟩
      · exact ⟨by decide, Relation.ReflTransGen.single ((hx3edge "x0").mpr rfl)⟩
  have hancSet3 : S_ex5.ancSet {"x3"} = {"x3", "x0"} := by unfold Schema.ancSet; simp [hanc3]
  have haMem : tp "p" (.lit (.str "a")) ∈ M24a := by unfold M24a; simp
  have haMem' : tp "p" (.lit (.str "a")) ∈ M' ∪ (S_ex5.ancSet {"x3"}).biUnion Mx := hunion ▸ haMem
  rw [Finset.mem_union] at haMem'
  rcases haMem' with haM' | haMx
  · obtain ⟨-, hMnotin, -⟩ := hM'
    have haMnotin : tp "p" (.lit (.str "a")) ∈ Mnotin τ_ex3 M' (TripleExpr.tc "p" "T_even") := by
      rw [mem_Mnotin]
      refine ⟨⟨haM', ?_⟩, ?_⟩
      · simp [TripleExpr.props, TripleExpr.tcs, tp]
      · rw [mem_Me]
        rintro ⟨-, z, hz, hty⟩
        simp only [TripleExpr.tcs, Finset.mem_singleton, Prod.mk.injEq] at hz
        obtain ⟨-, hz⟩ := hz
        subst hz
        exact absurd hty (by decide)
    have hpmem : "p" ∈ props (Mnotin τ_ex3 M' (TripleExpr.tc "p" "T_even")) :=
      Finset.mem_image_of_mem Triple.pred haMnotin
    have := hMnotin hpmem
    simp at this
  · rw [hancSet3, Finset.mem_biUnion] at haMx
    obtain ⟨x, hx, hax⟩ := haMx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hextte : (S_ex5.shapeDef x).extTe = TripleExpr.tc "p" "T_even" := by
      rcases hx with rfl | rfl
      · rw [hx3shape]; rfl
      · rw [hx0shape]; rfl
    have hxmem : x ∈ S_ex5.ancSet {"x3"} := by
      rw [hancSet3]; simp only [Finset.mem_insert, Finset.mem_singleton]; exact hx
    have hEx := hMx x hxmem
    rw [hextte] at hEx
    obtain ⟨n, o, hMxeq, hty⟩ := hEx
    rw [hMxeq] at hax
    simp only [Finset.mem_singleton] at hax
    have hobj : (tp "p" (.lit (.str "a"))).obj = o := by rw [hax]
    simp only [tp] at hobj
    rw [← hobj] at hty
    exact absurd hty (by decide)

/-! ### §2's motivating example (Fig. 1/2/3)

The full multiple-inheritance `ColouredCircle` chain: `Coord`, `Attribute`,
`Colour`, abstract `Figure`, `Circle`, `Radius`, `ColouredFigure`, and
`ColouredCircle` (Fig. 1), instantiated over Fig. 2's graph (nodes `f1`,
`f2`, `a1`, `a2`, `a3`, `c1`, `c2`), proving the paper's own headline claims:
`c1`/`c2 ⊨ Coord`, `a1`/`a2`/`a3 ⊨ Attribute`, `a2 ⊨ Colour`,
`a1`/`a3 ⊨ Radius`, `f2` is a `Circle`, and — the multiple-inheritance
punchline — `f1` is a `ColouredCircle` (Fig. 3's `H_S` gives
`anc({Circle,ColouredFigure}) = {Circle, Figure, ColouredFigure}`, `Figure`
counted once even though inherited via both parents). -/

/-- `T_float` (approximated, per the module docstring, as "any integer
literal" since `Literal` has no float constructor). -/
def cFloat : NodeConstraint
  | .lit (.int _) => True
  | _ => False

/-- `T_"colour"`: the literal string `"colour"`. -/
def cColourLit : NodeConstraint
  | .lit (.str s) => s = "colour"
  | _ => False

/-- `T_"radius"`: the literal string `"radius"`. -/
def cRadiusLit : NodeConstraint
  | .lit (.str s) => s = "radius"
  | _ => False

/-- Fig. 1's schema: `Coord` is a `Y`-label (a plain shape, no `extends`);
`Attribute, Colour, Figure, Circle, Radius, ColouredFigure, ColouredCircle`
are `X`-labels; `Figure` is `abstract` (`A = {Figure}`, though `A` plays no
role in the fuel-bounded `Satisfies*` relations themselves — only in
well-definedness, not yet formalized). -/
def S_fig1 : Schema where
  Y := {"Coord", "T_str", "T_any", "T_float", "T_colour", "T_radius"}
  X := {"Attribute", "Colour", "Figure", "Circle", "Radius", "ColouredFigure", "ColouredCircle"}
  A := {"Figure"}
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "Coord" => .ofShape ⟨false, none, .seq (.tc "x" "T_float") (.tc "y" "T_float")⟩
    | "T_str" => .constraint cStr
    | "T_any" => .constraint (fun _ => True)
    | "T_float" => .constraint cFloat
    | "T_colour" => .constraint cColourLit
    | "T_radius" => .constraint cRadiusLit
    | "Attribute" =>
        .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩
    | "Colour" =>
        .and (.extends {"Attribute"} ⟨false, none, .tc "scope" "T_str"⟩)
          (.ofShape ⟨false, none, .tc "name" "T_colour"⟩)
    | "Figure" => .extends ∅ ⟨false, none, .tc "coord" "Coord"⟩
    | "Circle" => .extends {"Figure"} ⟨false, none, .tc "attr" "Radius"⟩
    | "Radius" =>
        .and (.extends {"Attribute"} ⟨false, none, .empty⟩)
          (.ofShape ⟨false, none, .seq (.tc "name" "T_radius") (.tc "value" "T_float")⟩)
    | "ColouredFigure" => .extends {"Figure"} ⟨false, none, .tc "attr" "Colour"⟩
    | "ColouredCircle" => .extends {"Circle", "ColouredFigure"} ⟨false, none, .empty⟩
    | _ => .constraint (fun _ => False)

/-- Fig. 2's graph nodes. -/
def a1 : RDFNode := .iri "a1"
def a2 : RDFNode := .iri "a2"
def a3 : RDFNode := .iri "a3"
def c1 : RDFNode := .iri "c1"
def c2 : RDFNode := .iri "c2"
def f1 : RDFNode := .iri "f1"
def f2 : RDFNode := .iri "f2"

/-- Fig. 2's graph. Coordinates/`value`s are approximated as integer
literals (see the module docstring): `a1`'s `10.1` ↦ `10`, `a3`'s `7.2` ↦
`7`, `c1`'s `(2.0, 4.0)` ↦ `(2, 4)`, `c2`'s `(0.2, -2.3)` ↦ `(0, -2)`. `f1`
has *two* `attr` triples (to `a1`, the `Radius`, and to `a2`, the
`Colour`) plus one `coord` triple — exactly the three pieces
`ColouredCircle`'s rule-18 partition over `{Circle, Figure, ColouredFigure}`
needs. -/
def G_fig1 : Graph :=
  { ⟨a1, "name", .lit (.str "radius")⟩, ⟨a1, "value", .lit (.int 10)⟩,
    ⟨a2, "scope", .lit (.str "fill")⟩, ⟨a2, "name", .lit (.str "colour")⟩,
    ⟨a2, "value", .lit (.str "#ff0000")⟩,
    ⟨a3, "name", .lit (.str "radius")⟩, ⟨a3, "value", .lit (.int 7)⟩,
    ⟨c1, "x", .lit (.int 2)⟩, ⟨c1, "y", .lit (.int 4)⟩,
    ⟨c2, "x", .lit (.int 0)⟩, ⟨c2, "y", .lit (.int (-2))⟩,
    ⟨f1, "attr", a1⟩, ⟨f1, "attr", a2⟩, ⟨f1, "coord", c1⟩,
    ⟨f2, "attr", a3⟩, ⟨f2, "coord", c2⟩ }

/-- A typing witnessing every `p @z` lookup the claims below need — `τ.has`
resolutions are given directly (Definition 4 "correct typing", connecting
`τ` back to the node constraints' own truth values, is not yet
formalized), including both a node's *literal* triple-constraint types
(`T_str`/`T_any`/`T_float`/`T_"colour"`/`T_"radius"`) and, for `a1`, `a2`,
`a3`, `c1`, `c2` themselves, the shape-reference types (`Radius`, `Colour`,
`Coord`) that `f1`/`f2`'s own `attr`/`coord` triple constraints look up. -/
def τ_fig1 : Typing :=
  { (RDFNode.lit (.str "radius"), "T_str"), (RDFNode.lit (.str "radius"), "T_radius"),
    (RDFNode.lit (.int 10), "T_any"), (RDFNode.lit (.int 10), "T_float"),
    (RDFNode.lit (.int 7), "T_any"), (RDFNode.lit (.int 7), "T_float"),
    (RDFNode.lit (.str "fill"), "T_str"),
    (RDFNode.lit (.str "colour"), "T_str"), (RDFNode.lit (.str "colour"), "T_colour"),
    (RDFNode.lit (.str "#ff0000"), "T_any"),
    (RDFNode.lit (.int 2), "T_float"), (RDFNode.lit (.int 4), "T_float"),
    (RDFNode.lit (.int 0), "T_float"), (RDFNode.lit (.int (-2)), "T_float"),
    (a1, "Radius"), (a2, "Colour"), (c1, "Coord"), (a3, "Radius"), (c2, "Coord") }

/-! General-purpose helpers for the claims below: reachability in `H_S` for
"root" (no outgoing edges) and "single parent" extendable labels, and
rule-17 (`.ofShape`) satisfaction facts for the small triple-expression
shapes Fig. 1 actually uses (`⟨ε⟩`, a bare `p @z`, and a bare `p1 @z1 ; p2
@z2`), each allowing arbitrary "junk" triples with an unrelated predicate
since none of Fig. 1's own shapes are `closed`. -/

theorem reach_root {S : Schema} {p : ShapeLabel} (hparent : ∀ c, ¬ S.extEdge p c) :
    ∀ x', Relation.ReflTransGen S.extEdge p x' → x' = p := by
  intro x' h
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
  · exact heq.symm
  · exact absurd hc (hparent c)

theorem anc_root {S : Schema} {x : ShapeLabel} (hx : x ∈ S.X)
    (hedge : ∀ c, ¬ S.extEdge x c) : S.anc x = {x} := by
  apply Finset.ext; intro x'
  unfold Schema.anc
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩; exact reach_root hedge x' h
  · rintro rfl; exact ⟨hx, Relation.ReflTransGen.refl⟩

theorem anc_one_parent {S : Schema} {x p : ShapeLabel} (hx : x ∈ S.X) (hp : p ∈ S.X)
    (hedge : ∀ c, S.extEdge x c ↔ c = p) (hparent : ∀ c, ¬ S.extEdge p c) :
    S.anc x = {x, p} := by
  apply Finset.ext; intro x'
  unfold Schema.anc
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, hc'⟩
    · exact Or.inl heq.symm
    · have hceq : c = p := (hedge c).mp hc
      exact Or.inr (hceq ▸ reach_root hparent x' (hceq ▸ hc'))
  · rintro (heq | heq)
    · rw [heq]; exact ⟨hx, Relation.ReflTransGen.refl⟩
    · rw [heq]; exact ⟨hp, Relation.ReflTransGen.single ((hedge p).mpr rfl)⟩

/-- The empty set trivially satisfies the (non-closed, no-`extra`) trivial
shape `[ε]` (Table 3 rule 17) — reused wherever an `extends X ⟨ε⟩`'s own
`M'` piece is chosen to be empty (`Radius`/`ColouredCircle`, both of which
use a bare `⟨ε⟩` as their own shape). -/
theorem empty_satisfies_emptyShape {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ} :
    SatisfiesMFuel (fuel + 2) S G τ (∅ : Finset Triple) (.ofShape ⟨false, none, .empty⟩) := by
  have hMeEmpty : Me τ (∅ : Finset Triple) TripleExpr.empty = ∅ := by unfold Me; simp
  refine ⟨?_, ?_, fun h => absurd h (by decide)⟩
  · show SatisfiesEFuel (fuel + 1) S G τ (Me τ (∅ : Finset Triple) TripleExpr.empty) TripleExpr.empty
    rw [hMeEmpty]; rfl
  · show props (Mnotin τ (∅ : Finset Triple) TripleExpr.empty) ⊆ (∅ : Finset IRI)
    unfold Mnotin
    simp [props, TripleExpr.props, TripleExpr.tcs]

/-- `insert t junk, τ ⊨ [false,none]⟨p @z⟩` (Table 3 rule 17) whenever `t`
is the unique triple with predicate `p`, and `junk`'s predicates are all
different from `p` (so, non-closed, entirely unconstrained). Reused for
`Colour`'s own `name @T_"colour"` restriction applied to `a2`'s full
neighbourhood (which also has `scope`/`value` triples). -/
theorem single_tc_ofShape_junk {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {p : IRI} {z : ShapeLabel} {t : Triple} {junk : Finset Triple}
    (hp : t.pred = p) (hjunk : ∀ t' ∈ junk, t'.pred ≠ p) (hty : τ.has t.obj z) :
    SatisfiesMFuel (fuel + 2) S G τ (insert t junk) (.ofShape ⟨false, none, .tc p z⟩) := by
  have hMe : Me τ (insert t junk) (.tc p z) = {t} := by
    apply Finset.Subset.antisymm
    · intro t' ht'
      rw [mem_Me] at ht'
      obtain ⟨htM, z', hz, -⟩ := ht'
      simp only [Finset.mem_insert] at htM
      simp only [TripleExpr.tcs, Finset.mem_singleton, Prod.mk.injEq] at hz
      rcases htM with rfl | htj
      · exact Finset.mem_singleton_self _
      · exact absurd hz.1 (hjunk t' htj)
    · intro t' ht'
      simp only [Finset.mem_singleton] at ht'
      subst ht'
      rw [mem_Me]
      exact ⟨Finset.mem_insert_self _ _, z, by simp [TripleExpr.tcs, hp], hty⟩
  refine ⟨?_, ?_, by simp⟩
  · rw [hMe]; exact ⟨t.subj, t.obj, by rw [← hp], hty⟩
  · show props (Mnotin τ (insert t junk) (.tc p z)) ⊆ (∅ : Finset IRI)
    rw [Finset.subset_empty, Finset.eq_empty_iff_forall_notMem]
    intro t' ht'
    unfold props at ht'
    obtain ⟨t'', ht'', rfl⟩ := Finset.mem_image.mp ht'
    rw [mem_Mnotin, hMe] at ht''
    obtain ⟨⟨htM, hpred⟩, hnotMe⟩ := ht''
    simp only [Finset.mem_insert] at htM
    simp only [TripleExpr.props, TripleExpr.tcs, Finset.image_singleton, Finset.mem_singleton]
      at hpred
    rcases htM with rfl | htj
    · exact hnotMe (Finset.mem_singleton_self _)
    · exact (hjunk t'' htj) hpred

/-- `{t1, t2}, τ ⊨ [false,none]⟨p1 @z1 ; p2 @z2⟩` (Table 3 rule 17) for
exactly two triples, no junk — the two-triple-constraint analogue of
`singleton_tc_ofShape`, reused for Fig. 1's `Coord`, `Attribute` (nodes
`a1`/`a3`, which have no other triples), and `Radius`'s own
`name @T_"radius" ; value @T_float` restriction. -/
theorem pair_tc_tc_ofShape {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {p1 p2 : IRI} {z1 z2 : ShapeLabel} {t1 t2 : Triple}
    (hp1 : t1.pred = p1) (hp2 : t2.pred = p2) (hne : t1 ≠ t2)
    (hty1 : τ.has t1.obj z1) (hty2 : τ.has t2.obj z2) :
    SatisfiesMFuel (fuel + 3) S G τ {t1, t2}
      (.ofShape ⟨false, none, .seq (.tc p1 z1) (.tc p2 z2)⟩) := by
  have hMe : Me τ ({t1, t2} : Finset Triple) (.seq (.tc p1 z1) (.tc p2 z2)) = {t1, t2} := by
    apply Finset.Subset.antisymm
    · intro t ht; rw [mem_Me] at ht; exact ht.1
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [mem_Me]
      rcases ht with rfl | rfl
      · exact ⟨Finset.mem_insert_self _ _, z1, by simp [TripleExpr.tcs, hp1], hty1⟩
      · exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), z2,
          by simp [TripleExpr.tcs, hp2], hty2⟩
  refine ofShape_of_Me_eq_self (fuel := fuel + 2) hMe ⟨{t1}, {t2}, ⟨?_, ?_⟩,
    ⟨t1.subj, t1.obj, by rw [← hp1], hty1⟩, ⟨t2.subj, t2.obj, by rw [← hp2], hty2⟩⟩
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_singleton] at hx1 hx2
    exact hne (hx1.symm.trans hx2)
  · ext x; simp

/-- `insert t1 (insert t2 junk), τ ⊨ [false,none]⟨p1 @z1 ; p2 @z2⟩` (Table
3 rule 17): the junk-tolerant analogue of `pair_tc_tc_ofShape`, reused for
`a2 ⊨ Attribute` (`a2`'s neighbourhood also has a `scope` triple, unrelated
to `Attribute`'s own `name`/`value`). -/
theorem pair_tc_tc_ofShape_junk {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ}
    {p1 p2 : IRI} {z1 z2 : ShapeLabel} {t1 t2 : Triple} {junk : Finset Triple}
    (hp1 : t1.pred = p1) (hp2 : t2.pred = p2) (hne : t1 ≠ t2)
    (hjunk : ∀ t ∈ junk, t.pred ≠ p1 ∧ t.pred ≠ p2)
    (hty1 : τ.has t1.obj z1) (hty2 : τ.has t2.obj z2) :
    SatisfiesMFuel (fuel + 3) S G τ (insert t1 (insert t2 junk))
      (.ofShape ⟨false, none, .seq (.tc p1 z1) (.tc p2 z2)⟩) := by
  have hMe : Me τ (insert t1 (insert t2 junk)) (.seq (.tc p1 z1) (.tc p2 z2)) = {t1, t2} := by
    apply Finset.Subset.antisymm
    · intro t ht
      rw [mem_Me] at ht
      obtain ⟨htM, z, hz, -⟩ := ht
      simp only [Finset.mem_insert] at htM
      simp only [TripleExpr.tcs, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hz
      rcases htM with rfl | rfl | htj
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exfalso
        rcases hz with ⟨hzp, -⟩ | ⟨hzp, -⟩
        · exact (hjunk t htj).1 hzp
        · exact (hjunk t htj).2 hzp
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [mem_Me]
      rcases ht with rfl | rfl
      · exact ⟨Finset.mem_insert_self _ _, z1, by simp [TripleExpr.tcs, hp1], hty1⟩
      · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), z2,
          by simp [TripleExpr.tcs, hp2], hty2⟩
  refine ⟨?_, ?_, by simp⟩
  · rw [hMe]
    refine ⟨{t1}, {t2}, ⟨?_, ?_⟩, ⟨t1.subj, t1.obj, by rw [← hp1], hty1⟩,
      ⟨t2.subj, t2.obj, by rw [← hp2], hty2⟩⟩
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_singleton] at hx1 hx2
      exact hne (hx1.symm.trans hx2)
    · ext x; simp
  · show props (Mnotin τ (insert t1 (insert t2 junk)) (.seq (.tc p1 z1) (.tc p2 z2)))
      ⊆ (∅ : Finset IRI)
    rw [Finset.subset_empty, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    unfold props at ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    rw [mem_Mnotin, hMe] at ht'
    obtain ⟨⟨htM, hpred⟩, hnotMe⟩ := ht'
    simp only [Finset.mem_insert] at htM
    simp only [TripleExpr.props, TripleExpr.tcs, Finset.image_union, Finset.image_singleton,
      Finset.mem_union, Finset.mem_singleton] at hpred
    rcases htM with rfl | rfl | htj
    · exact hnotMe (Finset.mem_insert_self _ _)
    · exact hnotMe (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · rcases hpred with hp | hp
      · exact (hjunk t' htj).1 hp
      · exact (hjunk t' htj).2 hp

/-! `H_S`'s edges (Fig. 3) among the `X`-labels actually used below. -/

theorem hAttributeEdge : ∀ c, ¬ S_fig1.extEdge "Attribute" c := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  intro c hc; unfold Schema.extEdge at hc; rw [hshape] at hc
  simp [ShapeExpr.extendsTargets] at hc

theorem hFigureEdge : ∀ c, ¬ S_fig1.extEdge "Figure" c := by
  have hshape : S_fig1.shapeDef "Figure" = .extends ∅ ⟨false, none, .tc "coord" "Coord"⟩ := rfl
  intro c hc; unfold Schema.extEdge at hc; rw [hshape] at hc
  simp [ShapeExpr.extendsTargets] at hc

theorem hCircleEdge : ∀ c, S_fig1.extEdge "Circle" c ↔ c = "Figure" := by
  have hshape : S_fig1.shapeDef "Circle" =
      .extends {"Figure"} ⟨false, none, .tc "attr" "Radius"⟩ := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem hColouredFigureEdge : ∀ c, S_fig1.extEdge "ColouredFigure" c ↔ c = "Figure" := by
  have hshape : S_fig1.shapeDef "ColouredFigure" =
      .extends {"Figure"} ⟨false, none, .tc "attr" "Colour"⟩ := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem hColourEdge : ∀ c, S_fig1.extEdge "Colour" c ↔ c = "Attribute" := by
  have hshape : S_fig1.shapeDef "Colour" =
      .and (.extends {"Attribute"} ⟨false, none, .tc "scope" "T_str"⟩)
        (.ofShape ⟨false, none, .tc "name" "T_colour"⟩) := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem hRadiusEdge : ∀ c, S_fig1.extEdge "Radius" c ↔ c = "Attribute" := by
  have hshape : S_fig1.shapeDef "Radius" =
      .and (.extends {"Attribute"} ⟨false, none, .empty⟩)
        (.ofShape ⟨false, none, .seq (.tc "name" "T_radius") (.tc "value" "T_float")⟩) := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem hancAttribute : S_fig1.anc "Attribute" = {"Attribute"} := anc_root (by decide) hAttributeEdge
theorem hancFigure : S_fig1.anc "Figure" = {"Figure"} := anc_root (by decide) hFigureEdge
theorem hancCircle : S_fig1.anc "Circle" = {"Circle", "Figure"} :=
  anc_one_parent (by decide) (by decide) hCircleEdge hFigureEdge
theorem hancColouredFigure : S_fig1.anc "ColouredFigure" = {"ColouredFigure", "Figure"} :=
  anc_one_parent (by decide) (by decide) hColouredFigureEdge hFigureEdge
theorem hancColour : S_fig1.anc "Colour" = {"Colour", "Attribute"} :=
  anc_one_parent (by decide) (by decide) hColourEdge hAttributeEdge
theorem hancRadius : S_fig1.anc "Radius" = {"Radius", "Attribute"} :=
  anc_one_parent (by decide) (by decide) hRadiusEdge hAttributeEdge

theorem hancSetAttribute : S_fig1.ancSet {"Attribute"} = {"Attribute"} := by
  unfold Schema.ancSet; simp [hancAttribute]
theorem hancSetFigure : S_fig1.ancSet {"Figure"} = {"Figure"} := by
  unfold Schema.ancSet; simp [hancFigure]
theorem hancSetCircleColouredFigure :
    S_fig1.ancSet {"Circle", "ColouredFigure"} = {"Circle", "Figure", "ColouredFigure"} := by
  unfold Schema.ancSet
  rw [show ({"Circle", "ColouredFigure"} : Finset ShapeLabel) = insert "Circle" {"ColouredFigure"}
      from rfl, Finset.biUnion_insert, Finset.singleton_biUnion, hancCircle, hancColouredFigure]
  decide

/-- `c1, τ ⊨ Coord` (Fig. 2's claim "node c1 satisfies Coord"). `Coord` is
a `Y`-label (a bare, `extends`-free shape), so this reduces directly to a
rule-17 check on `neigh(c1)`. -/
theorem c1_satisfies_Coord :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 c1 (S_fig1.shapeDef "Coord") := by
  have hshape : S_fig1.shapeDef "Coord" =
      .ofShape ⟨false, none, .seq (.tc "x" "T_float") (.tc "y" "T_float")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 c1) _)
  have hneigh : neigh G_fig1 c1 =
      {(⟨c1, "x", .lit (.int 2)⟩ : Triple), ⟨c1, "y", .lit (.int 4)⟩} := by decide
  rw [hneigh]
  exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `c2, τ ⊨ Coord`. -/
theorem c2_satisfies_Coord :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 c2 (S_fig1.shapeDef "Coord") := by
  have hshape : S_fig1.shapeDef "Coord" =
      .ofShape ⟨false, none, .seq (.tc "x" "T_float") (.tc "y" "T_float")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 c2) _)
  have hneigh : neigh G_fig1 c2 =
      {(⟨c2, "x", .lit (.int 0)⟩ : Triple), ⟨c2, "y", .lit (.int (-2))⟩} := by decide
  rw [hneigh]
  exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `a1, τ ⊨ Attribute` (Fig. 2's claim "Nodes a1, a2, a3 satisfy
`Attribute`", restricted to `a1`). `Attribute` has no `extends` targets of
its own, so the rule-18 partition is trivial: `M' = M`, `Mx` vacuous over
`anc(∅) = ∅`. -/
theorem a1_satisfies_Attribute :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 a1 (S_fig1.shapeDef "Attribute") := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a1) _)
  have hneigh : neigh G_fig1 a1 =
      {(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩} := by decide
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset ShapeLabel) = ∅ := by unfold Schema.ancSet; simp
  refine ⟨{(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩},
    fun _ => ∅, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hanc]; decide
  · rw [hanc]; intro a ha; simp at ha
  · rw [hanc]; decide
  · exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)
  · rw [hanc]; intro x hx; simp at hx
  · rw [hanc]; intro x hx; simp at hx

/-- `a3, τ ⊨ Attribute`. -/
theorem a3_satisfies_Attribute :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 a3 (S_fig1.shapeDef "Attribute") := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a3) _)
  have hneigh : neigh G_fig1 a3 =
      {(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩} := by decide
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset ShapeLabel) = ∅ := by unfold Schema.ancSet; simp
  refine ⟨{(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩},
    fun _ => ∅, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hanc]; decide
  · rw [hanc]; intro a ha; simp at ha
  · rw [hanc]; decide
  · exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)
  · rw [hanc]; intro x hx; simp at hx
  · rw [hanc]; intro x hx; simp at hx

/-- `a2, τ ⊨ Attribute`: `a2`'s neighbourhood also has a `scope` triple
(needed for `Colour`, see `a2_satisfies_Colour`), which `Attribute` (not
`closed`) simply ignores as junk. -/
theorem a2_satisfies_Attribute :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 a2 (S_fig1.shapeDef "Attribute") := by
  have hshape : S_fig1.shapeDef "Attribute" =
      .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a2) _)
  have hneigh : neigh G_fig1 a2 =
      insert (⟨a2, "name", .lit (.str "colour")⟩ : Triple)
        (insert (⟨a2, "value", .lit (.str "#ff0000")⟩ : Triple) {⟨a2, "scope", .lit (.str "fill")⟩}) := by
    decide
  rw [hneigh]
  have hanc : S_fig1.ancSet (∅ : Finset ShapeLabel) = ∅ := by unfold Schema.ancSet; simp
  refine ⟨insert (⟨a2, "name", .lit (.str "colour")⟩ : Triple)
      (insert (⟨a2, "value", .lit (.str "#ff0000")⟩ : Triple) {⟨a2, "scope", .lit (.str "fill")⟩}),
    fun _ => ∅, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hanc]; decide
  · rw [hanc]; intro a ha; simp at ha
  · rw [hanc]; decide
  · refine pair_tc_tc_ofShape_junk rfl rfl (by decide) ?_ (by decide) (by decide)
    intro t ht; simp only [Finset.mem_singleton] at ht; subst ht; exact ⟨by decide, by decide⟩
  · rw [hanc]; intro x hx; simp at hx
  · rw [hanc]; intro x hx; simp at hx

/-- `a2, τ ⊨ Colour` (Fig. 2's claim "node a2 satisfies Colour"). `Colour =
extends Attribute ⟨scope @T_str⟩ and ⟨name @T_"colour"⟩`: the first
conjunct splits `neigh(a2)` into `M' = {scope-triple}` (matching `scope
@T_str`) and `Mx(Attribute) = {name-triple, value-triple}` (matching
`ext-te(Attribute) = name @T_str ; value @T_any`); the second conjunct
checks `name @T_"colour"` directly against all of `neigh(a2)` (the
`scope`/`value` triples are junk to it). -/
theorem a2_satisfies_Colour :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 a2 (S_fig1.shapeDef "Colour") := by
  have hshape : S_fig1.shapeDef "Colour" =
      .and (.extends {"Attribute"} ⟨false, none, .tc "scope" "T_str"⟩)
        (.ofShape ⟨false, none, .tc "name" "T_colour"⟩) := rfl
  rw [hshape]
  have hneigh : neigh G_fig1 a2 =
      insert (⟨a2, "name", .lit (.str "colour")⟩ : Triple)
        (insert (⟨a2, "scope", .lit (.str "fill")⟩ : Triple)
          {⟨a2, "value", .lit (.str "#ff0000")⟩}) := by decide
  refine ⟨?_, ?_⟩
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a2) _)
    rw [hneigh]
    refine ⟨{(⟨a2, "scope", .lit (.str "fill")⟩ : Triple)}, fun _ =>
      {(⟨a2, "name", .lit (.str "colour")⟩ : Triple), ⟨a2, "value", .lit (.str "#ff0000")⟩},
      ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hancSetAttribute]; decide
    · rw [hancSetAttribute]; intro a ha b hb hab
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · rw [hancSetAttribute]; decide
    · exact singleton_tc_ofShape (by decide)
    · rw [hancSetAttribute]
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      exact ⟨{(⟨a2, "name", .lit (.str "colour")⟩ : Triple)},
        {(⟨a2, "value", .lit (.str "#ff0000")⟩ : Triple)}, ⟨by decide, by decide⟩,
        ⟨a2, .lit (.str "colour"), rfl, by decide⟩, ⟨a2, .lit (.str "#ff0000"), rfl, by decide⟩⟩
    · rw [hancSetAttribute]
      intro x hx u hu; simp only [Finset.mem_singleton] at hx; subst hx
      have hAshape : S_fig1.shapeDef "Attribute" =
          .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
      rw [hAshape] at hu; simp [ShapeExpr.restrOf] at hu
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a2) _)
    rw [hneigh]
    refine single_tc_ofShape_junk rfl ?_ (by decide)
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide

/-- `a1, τ ⊨ Radius` (Fig. 2's claim "a1, a3 satisfy Radius"). `Radius =
extends Attribute ⟨ε⟩ and ⟨name @T_"radius" ; value @T_float⟩`: the first
conjunct's own `M' = ∅` (trivially, `⟨ε⟩` is unconstrained when
non-closed) and `Mx(Attribute) = neigh(a1)` (all of it, matching
`ext-te(Attribute)`); the second conjunct checks `name @T_"radius" ; value
@T_float` directly against `neigh(a1)` (no junk here — `a1` has exactly
those two triples). -/
theorem a1_satisfies_Radius :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 a1 (S_fig1.shapeDef "Radius") := by
  have hshape : S_fig1.shapeDef "Radius" =
      .and (.extends {"Attribute"} ⟨false, none, .empty⟩)
        (.ofShape ⟨false, none, .seq (.tc "name" "T_radius") (.tc "value" "T_float")⟩) := rfl
  rw [hshape]
  have hneigh : neigh G_fig1 a1 =
      {(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩} := by decide
  refine ⟨?_, ?_⟩
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a1) _)
    rw [hneigh]
    refine ⟨∅, fun _ =>
      {(⟨a1, "name", .lit (.str "radius")⟩ : Triple), ⟨a1, "value", .lit (.int 10)⟩},
      ⟨?_, ?_, ?_⟩, empty_satisfies_emptyShape, ?_, ?_⟩
    · rw [hancSetAttribute]; decide
    · rw [hancSetAttribute]; intro a ha b hb hab
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · rw [hancSetAttribute]; simp
    · rw [hancSetAttribute]
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      exact ⟨{(⟨a1, "name", .lit (.str "radius")⟩ : Triple)}, {⟨a1, "value", .lit (.int 10)⟩},
        ⟨by decide, by decide⟩, ⟨a1, .lit (.str "radius"), rfl, by decide⟩,
        ⟨a1, .lit (.int 10), rfl, by decide⟩⟩
    · rw [hancSetAttribute]
      intro x hx u hu; simp only [Finset.mem_singleton] at hx; subst hx
      have hAshape : S_fig1.shapeDef "Attribute" =
          .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
      rw [hAshape] at hu; simp [ShapeExpr.restrOf] at hu
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a1) _)
    rw [hneigh]
    exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `a3, τ ⊨ Radius`. -/
theorem a3_satisfies_Radius :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 a3 (S_fig1.shapeDef "Radius") := by
  have hshape : S_fig1.shapeDef "Radius" =
      .and (.extends {"Attribute"} ⟨false, none, .empty⟩)
        (.ofShape ⟨false, none, .seq (.tc "name" "T_radius") (.tc "value" "T_float")⟩) := rfl
  rw [hshape]
  have hneigh : neigh G_fig1 a3 =
      {(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩} := by decide
  refine ⟨?_, ?_⟩
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a3) _)
    rw [hneigh]
    refine ⟨∅, fun _ =>
      {(⟨a3, "name", .lit (.str "radius")⟩ : Triple), ⟨a3, "value", .lit (.int 7)⟩},
      ⟨?_, ?_, ?_⟩, empty_satisfies_emptyShape, ?_, ?_⟩
    · rw [hancSetAttribute]; decide
    · rw [hancSetAttribute]; intro a ha b hb hab
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · rw [hancSetAttribute]; simp
    · rw [hancSetAttribute]
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      exact ⟨{(⟨a3, "name", .lit (.str "radius")⟩ : Triple)}, {⟨a3, "value", .lit (.int 7)⟩},
        ⟨by decide, by decide⟩, ⟨a3, .lit (.str "radius"), rfl, by decide⟩,
        ⟨a3, .lit (.int 7), rfl, by decide⟩⟩
    · rw [hancSetAttribute]
      intro x hx u hu; simp only [Finset.mem_singleton] at hx; subst hx
      have hAshape : S_fig1.shapeDef "Attribute" =
          .extends ∅ ⟨false, none, .seq (.tc "name" "T_str") (.tc "value" "T_any")⟩ := rfl
      rw [hAshape] at hu; simp [ShapeExpr.restrOf] at hu
  · refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 a3) _)
    rw [hneigh]
    exact pair_tc_tc_ofShape rfl rfl (by decide) (by decide) (by decide)

/-- `f2, τ ⊨ Circle` (Fig. 2's claim "f2 is a Circle"). `Circle = extends
Figure ⟨attr @Radius⟩`: `M' = {(f2,attr,a3)}` (matching `attr @Radius`,
via `τ`'s `(a3, Radius)` assertion) and `Mx(Figure) = {(f2,coord,c2)}`
(matching `ext-te(Figure) = coord @Coord`, via `(c2, Coord)`). -/
theorem f2_satisfies_Circle :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 f2 (S_fig1.shapeDef "Circle") := by
  have hshape : S_fig1.shapeDef "Circle" =
      .extends {"Figure"} ⟨false, none, .tc "attr" "Radius"⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 f2) _)
  have hneigh : neigh G_fig1 f2 =
      {(⟨f2, "attr", a3⟩ : Triple), ⟨f2, "coord", c2⟩} := by decide
  rw [hneigh]
  refine ⟨{(⟨f2, "attr", a3⟩ : Triple)}, fun _ => {(⟨f2, "coord", c2⟩ : Triple)}, ⟨?_, ?_, ?_⟩,
    singleton_tc_ofShape (by decide), ?_, ?_⟩
  · rw [hancSetFigure]; decide
  · rw [hancSetFigure]; intro a ha b hb hab
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · rw [hancSetFigure]; decide
  · rw [hancSetFigure]
    intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
    exact ⟨f2, c2, rfl, by decide⟩
  · rw [hancSetFigure]
    intro x hx u hu; simp only [Finset.mem_singleton] at hx; subst hx
    have hFshape : S_fig1.shapeDef "Figure" = .extends ∅ ⟨false, none, .tc "coord" "Coord"⟩ := rfl
    rw [hFshape] at hu; simp [ShapeExpr.restrOf] at hu

/-- `f1, τ ⊨ ColouredCircle` (Fig. 2/3's headline multiple-inheritance
claim: "f1 is a ColouredCircle"). `ColouredCircle = extends Circle,
ColouredFigure ⟨ε⟩`: `M' = ∅` (`⟨ε⟩`, non-closed, unconstrained), and the
rule-18 partition over `anc({Circle,ColouredFigure}) = {Circle, Figure,
ColouredFigure}` (Fig. 3: `Figure`, inherited via *both* parents, appears
only once) splits `neigh(f1)`'s three triples one-to-one:
`Mx(Circle) = {(f1,attr,a1)}` (`ext-te(Circle) = attr @Radius`),
`Mx(Figure) = {(f1,coord,c1)}` (`ext-te(Figure) = coord @Coord`),
`Mx(ColouredFigure) = {(f1,attr,a2)}` (`ext-te(ColouredFigure) = attr
@Colour`) — `coord` used once even though both `Circle` and
`ColouredFigure` route through `Figure`. -/
theorem f1_satisfies_ColouredCircle :
    SatisfiesFuel bigFuel S_fig1 G_fig1 τ_fig1 f1 (S_fig1.shapeDef "ColouredCircle") := by
  have hshape : S_fig1.shapeDef "ColouredCircle" =
      .extends {"Circle", "ColouredFigure"} ⟨false, none, .empty⟩ := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_fig1 G_fig1 τ_fig1 (neigh G_fig1 f1) _)
  have hneigh : neigh G_fig1 f1 =
      {(⟨f1, "attr", a1⟩ : Triple), ⟨f1, "attr", a2⟩, ⟨f1, "coord", c1⟩} := by decide
  rw [hneigh]
  refine ⟨∅, fun x => if x = "Circle" then {(⟨f1, "attr", a1⟩ : Triple)}
      else if x = "Figure" then {(⟨f1, "coord", c1⟩ : Triple)} else {⟨f1, "attr", a2⟩},
    ⟨?_, ?_, ?_⟩, empty_satisfies_emptyShape, ?_, ?_⟩
  · rw [hancSetCircleColouredFigure]; simp
  · rw [hancSetCircleColouredFigure]
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    unfold Function.onFun
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp_all <;> decide
  · rw [hancSetCircleColouredFigure]; decide
  · rw [hancSetCircleColouredFigure]
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨f1, a1, by decide, by decide⟩
    · exact ⟨f1, c1, by decide, by decide⟩
    · exact ⟨f1, a2, by decide, by decide⟩
  · rw [hancSetCircleColouredFigure]
    intro x hx u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hCshape : S_fig1.shapeDef "Circle" =
        .extends {"Figure"} ⟨false, none, .tc "attr" "Radius"⟩ := rfl
    have hFshape : S_fig1.shapeDef "Figure" = .extends ∅ ⟨false, none, .tc "coord" "Coord"⟩ := rfl
    have hCFshape : S_fig1.shapeDef "ColouredFigure" =
        .extends {"Figure"} ⟨false, none, .tc "attr" "Colour"⟩ := rfl
    rcases hx with rfl | rfl | rfl
    · rw [hCshape] at hu; simp [ShapeExpr.restrOf] at hu
    · rw [hFshape] at hu; simp [ShapeExpr.restrOf] at hu
    · rw [hCFshape] at hu; simp [ShapeExpr.restrOf] at hu

/-! ### Examples 6/7 (§4.2): the dependency graph and well-defined schemas

Three small schemas `S1`, `S2`, `S3`, matching the paper's own Example 6,
checked against Definition 6 (`Schema.WellDefined`,
`ShexLean/Shex2025Inheritance/Stratification.lean`) per Example 7's own
verdicts: `S1` is well-defined (its only cycles, `y1↔y2` and `y1,y3`, carry
no negative dependency), `S2` is not (the cycle `y4,y5` carries the
negative `dep-shape-neg(y5,y4)`), and `S3` is not (the cycle
`y7,x2,x1` — needing `dep-extends`, symmetrized, to get from `x2` back to
`x1` — carries the negative `dep-shape-neg(y7,x2)`). These are regression
checks on the dependency-graph machinery itself, not CLI-registered
examples. -/

/-- `S1 = (Y1,∅,def,∅)` (Example 6): `y1 → ⟨p@y2⟩ and ⟨q@y3⟩`,
`y2 → ⟨q@y1⟩`, `y3 → extra{r} ⟨p@y1⟩`. `shapeDef` is written as an
explicit `if`-chain (rather than `|`-pattern matching, used everywhere
else in this file) so that `S1_wellDefined`'s proof — which needs to
case-split on an *arbitrary* label, not just the three named ones — can
resolve each branch by `simp`-ing the `if`s directly (see
`ShexLean/Shex2025Inheritance/Proposition1.lean`'s own memory notes on
this trick). -/
def S1 : Schema where
  Y := {"y1", "y2", "y3"}
  X := ∅
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef z :=
    if z = "y1" then
      .and (.ofShape ⟨false, none, .tc "p" "y2"⟩) (.ofShape ⟨false, none, .tc "q" "y3"⟩)
    else if z = "y2" then .ofShape ⟨false, none, .tc "q" "y1"⟩
    else if z = "y3" then .ofShape ⟨false, some {"r"}, .tc "p" "y1"⟩
    else .constraint (fun _ => False)

/-- `S2 = (Y2,∅,def,∅)` (Example 6): `y4 → ⟨p@y5⟩ or ⟨q@y6⟩`,
`y5 → not ⟨q@y4⟩`, `y6 → extra{p} ⟨p@y4⟩`. -/
def S2 : Schema where
  Y := {"y4", "y5", "y6"}
  X := ∅
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "y4" => .or (.ofShape ⟨false, none, .tc "p" "y5"⟩) (.ofShape ⟨false, none, .tc "q" "y6"⟩)
    | "y5" => .not (.ofShape ⟨false, none, .tc "q" "y4"⟩)
    | "y6" => .ofShape ⟨false, some {"p"}, .tc "p" "y4"⟩
    | _ => .constraint (fun _ => False)

/-- `S3 = (Y3,X3,def,∅)` (Example 6): `x1 → extends _ ⟨p@y7⟩`,
`x2 → extends x1 ⟨p@y8⟩`, `y7 → not ⟨q@x2⟩`, `y8 → c` (an arbitrary node
constraint). -/
def S3 : Schema where
  Y := {"y7", "y8"}
  X := {"x1", "x2"}
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "x1" => .extends ∅ ⟨false, none, .tc "p" "y7"⟩
    | "x2" => .extends {"x1"} ⟨false, none, .tc "p" "y8"⟩
    | "y7" => .not (.ofShape ⟨false, none, .tc "q" "x2"⟩)
    | "y8" => .constraint (fun _ => True)
    | _ => .constraint (fun _ => False)

/-! Example 6's own 13 enumerated dependency-relation facts (the paper's own table,
page 10), checked individually here on top of the aggregate well-definedness verdicts
below (`S1_wellDefined`/`S2_not_wellDefined`/`S3_not_wellDefined`, which only ever need
*some* of these as intermediate steps). -/

theorem dep_S1_y1_y2 : S1.dep "y1" "y2" := by
  show "y2" ∈ ((S1.shapeDef "y1").depsAux false).refs; decide
theorem dep_S1_y2_y1 : S1.dep "y2" "y1" := by
  show "y1" ∈ ((S1.shapeDef "y2").depsAux false).refs; decide
theorem dep_S1_y1_y3 : S1.dep "y1" "y3" := by
  show "y3" ∈ ((S1.shapeDef "y1").depsAux false).refs; decide
theorem dep_S1_y3_y1 : S1.dep "y3" "y1" := by
  show "y1" ∈ ((S1.shapeDef "y3").depsAux false).refs; decide

theorem dep_S2_y4_y5 : S2.dep "y4" "y5" := by
  show "y5" ∈ ((S2.shapeDef "y4").depsAux false).refs; decide
theorem dep_S2_y4_y6 : S2.dep "y4" "y6" := by
  show "y6" ∈ ((S2.shapeDef "y4").depsAux false).refs; decide
theorem depShapeNeg_S2_y5_y4 : S2.depShapeNeg "y5" "y4" := by
  show "y4" ∈ ((S2.shapeDef "y5").depsAux false).negRefs; decide
theorem depExtraNeg_S2_y6_y4 : S2.depExtraNeg "y6" "y4" := by
  show "y4" ∈ ((S2.shapeDef "y6").depsAux false).extraNegRefs; decide

theorem dep_S3_x1_y7 : S3.dep "x1" "y7" := by
  show "y7" ∈ ((S3.shapeDef "x1").depsAux false).refs; decide
theorem dep_S3_x2_y8 : S3.dep "x2" "y8" := by
  show "y8" ∈ ((S3.shapeDef "x2").depsAux false).refs; decide
theorem depShapeNeg_S3_y7_x2 : S3.depShapeNeg "y7" "x2" := by
  show "x2" ∈ ((S3.shapeDef "y7").depsAux false).negRefs; decide
theorem depExtends_S3_x1_x2 : S3.depExtends "x1" "x2" := by
  show S3.extEdge "x1" "x2" ∨ S3.extEdge "x2" "x1"
  right; show "x1" ∈ (S3.shapeDef "x2").extendsTargets; decide
theorem depExtends_S3_x2_x1 : S3.depExtends "x2" "x1" := by
  show S3.extEdge "x2" "x1" ∨ S3.extEdge "x1" "x2"
  left; show "x1" ∈ (S3.shapeDef "x2").extendsTargets; decide

/-- `S1` is well-defined (Example 7): `H_{S1}` is trivially acyclic
(`X1 = ∅`), and `S1` has no negative dependency at all, for *any* pair of
labels — `y3`'s own `extra {r}` never matches its `p @y1` triple
constraint's predicate `p`, so `dep-extra-neg` never fires, and `S1` has
no `not` at all, so `dep-shape-neg` never fires either (nor for any label
outside `{y1,y2,y3}`, whose `shapeDef` is the referenceless
`.constraint (fun _ => False)`). -/
theorem S1_wellDefined : S1.WellDefined := by
  refine ⟨?_, ?_⟩
  · have hX : S1.X = (∅ : Finset ShapeLabel) := rfl
    intro x hx; rw [hX] at hx; exact absurd hx (Finset.notMem_empty x)
  · rintro ⟨a, b, hDNeg, -⟩
    have hnoNeg : ∀ z z', ¬ S1.depShapeNeg z z' ∧ ¬ S1.depExtraNeg z z' := by
      intro z z'
      have hshape : S1.shapeDef z =
          (if z = "y1" then
            .and (.ofShape ⟨false, none, .tc "p" "y2"⟩) (.ofShape ⟨false, none, .tc "q" "y3"⟩)
          else if z = "y2" then .ofShape ⟨false, none, .tc "q" "y1"⟩
          else if z = "y3" then .ofShape ⟨false, some {"r"}, .tc "p" "y1"⟩
          else .constraint (fun _ => False)) := rfl
      unfold Schema.depShapeNeg Schema.depExtraNeg
      rw [hshape]
      by_cases hz1 : z = "y1"
      · simp [hz1, ShapeExpr.depsAux, Shape.depInfo, TripleExpr.tcs]
      · by_cases hz2 : z = "y2"
        · simp [hz2, ShapeExpr.depsAux, Shape.depInfo, TripleExpr.tcs]
        · by_cases hz3 : z = "y3"
          · simp [hz3, ShapeExpr.depsAux, Shape.depInfo, TripleExpr.tcs, Finset.mem_singleton,
              Finset.mem_filter, Prod.mk.injEq]
          · simp [hz1, hz2, hz3, ShapeExpr.depsAux]
    exact hDNeg.elim (hnoNeg a b).1 (hnoNeg a b).2

/-- `S2` is not well-defined (Example 7): the cycle `y4, y5` carries the
negative dependency `dep-shape-neg(y5,y4)` (`y5 = not ⟨q@y4⟩`), and `y4`
reaches back to `y5` directly via `dep(y4,y5)` (`y4`'s own `⟨p@y5⟩`
disjunct). -/
theorem S2_not_wellDefined : ¬ S2.WellDefined := by
  rintro ⟨-, hNC⟩
  apply hNC
  have hy5shape : S2.shapeDef "y5" = .not (.ofShape ⟨false, none, .tc "q" "y4"⟩) := rfl
  have hy4shape : S2.shapeDef "y4" =
      .or (.ofShape ⟨false, none, .tc "p" "y5"⟩) (.ofShape ⟨false, none, .tc "q" "y6"⟩) := rfl
  refine ⟨"y5", "y4", Or.inl ?_, Relation.ReflTransGen.single (Or.inl ?_)⟩
  · show "y4" ∈ ((S2.shapeDef "y5").depsAux false).negRefs
    rw [hy5shape]; decide
  · show "y5" ∈ ((S2.shapeDef "y4").depsAux false).refs
    rw [hy4shape]; decide

/-- `S3` is not well-defined (Example 7): the cycle `y7, x2, x1` carries
the negative dependency `dep-shape-neg(y7,x2)` (`y7 = not ⟨q@x2⟩`), and
`x2` reaches back to `y7` via `dep-extends(x2,x1)` (`x2 extends x1`,
symmetrized) followed by `dep(x1,y7)` (`x1`'s own `⟨p@y7⟩`) — "the cycle
won't be present without the `dep-extends` relation" (paper's own remark).
-/
theorem S3_not_wellDefined : ¬ S3.WellDefined := by
  rintro ⟨-, hNC⟩
  apply hNC
  have hy7shape : S3.shapeDef "y7" = .not (.ofShape ⟨false, none, .tc "q" "x2"⟩) := rfl
  have hx1shape : S3.shapeDef "x1" = .extends ∅ ⟨false, none, .tc "p" "y7"⟩ := rfl
  have hx2shape : S3.shapeDef "x2" = .extends {"x1"} ⟨false, none, .tc "p" "y8"⟩ := rfl
  refine ⟨"y7", "x2", Or.inl ?_, ?_⟩
  · show "x2" ∈ ((S3.shapeDef "y7").depsAux false).negRefs
    rw [hy7shape]; decide
  · have step1 : S3.DEdge "x2" "x1" := Or.inr (Or.inl (by
      show S3.extEdge "x2" "x1"
      unfold Schema.extEdge; rw [hx2shape]; simp [ShapeExpr.extendsTargets]))
    have step2 : S3.DEdge "x1" "y7" := Or.inl (by
      show "y7" ∈ ((S3.shapeDef "x1").depsAux false).refs
      rw [hx1shape]; decide)
    exact Relation.ReflTransGen.head step1 (Relation.ReflTransGen.single step2)

end ShexLean.Inheritance
