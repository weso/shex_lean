import ShexLean.Shex2025Inheritance.examples.Example3_triple_match
import ShexLean.Shex2025Inheritance.Render
import Example

/-!
Example 5 from the 2025 "Shape Expressions with Inheritance" paper (§4.2,
Table 3 rule 18): a chain of `extends`-related shapes `x0..x6` (schema
`S_ex5`, `Example3_triple_match.lean`), exercising the `extends` rule's
partition over `anc(X)`.

Example 5's schema is stated in the paper as `S = (Y, {x1,...,x6}, def,
∅)`, but `def(x1)` and `def(x3)` both use `extends x0`, i.e. `x0`
genuinely needs to be a member of the extendable-label set `X` for
`Schema.anc`/`Schema.WellFormedX` to see it as a node of `H_S` at all
(Definition 3: `H_S`'s vertex set *is* `X`). This looks like a minor
omission in the paper's own statement of the example (`x0`'s own
definition, `extends _ ⟨p @Teven⟩`, is exactly the form Definition 2
requires of an `X`-label). `Example3_triple_match.lean`'s `S_ex5.X`
includes `x0`.
-/

namespace ShexLean.Inheritance

/-- `M24, τ ⊨ def(x1)` (Example 5): `def(x1) = extends x0 ⟨p @T_even⟩`,
so `anc({x0}) = {x0}` and `M24` splits into `M'` (satisfying `⟨p
@T_even⟩`) and `Mx0` (satisfying `ext-te(x0) = p @T_even`, `x0` having no
restriction of its own). -/
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

end ShexLean.Inheritance

namespace Examples

open ShexLean.Inheritance (S_ex5 τ_ex3 bigFuel M24 M246 M2a M24a
  S_ex5_XClosed S_ex5_RestrOk satisfiesMFuel_decidable)
open ShexLean (Triple ShapeLabel Graph.render Typing.render renderDecide)

/-- `renderDecide`'s `native_decide`-computed verdict for `M ⊨ def(L)`. -/
def satMEx5 (M : Finset Triple) (L : ShapeLabel)
    (hOk : (S_ex5.shapeDef L).MOk S_ex5) : String :=
  renderDecide (satisfiesMFuel_decidable S_ex5 default τ_ex3 S_ex5_XClosed S_ex5_RestrOk
    bigFuel M (S_ex5.shapeDef L) hOk)

/-- Example 5's `extends` chain. `schemaText` is generated from the real
`S_ex5`; every `M ⊨ def(L)` claim in `typingText` is a `native_decide`
computation via `satisfiesMFuel_decidable`, including `M24, τ ⊨ def(x1)`
(proved above via `x1`'s rule-18 partition against its ancestor `x0`) and
the two negative claims proved above by cardinality/leftover-triple
arguments. -/
def inheritance2025Extends : Example where
  name := "inheritance2025-example5-extends"
  summary := "extends chain x0..x6; M24,τ ⊨ def(x1) via x1's rule-18 partition."
  schemaText := S_ex5.render
  graphText :=
    s!"M24  = {Graph.render M24}\n" ++
    s!"M246 = {Graph.render M246}\n" ++
    s!"M2a  = {Graph.render M2a}\n" ++
    s!"M24a = {Graph.render M24a}"
  typingText :=
    s!"τ = {Typing.render τ_ex3}\n" ++
    s!"M24,  τ ⊨ def(x1) = " ++
      s!"{satMEx5 M24 "x1" (show ({"x0"} : Finset ShapeLabel) ⊆ S_ex5.X by decide)}\n" ++
    s!"M246, τ ⊨ def(x2) = " ++
      s!"{satMEx5 M246 "x2" (show ({"x1"} : Finset ShapeLabel) ⊆ S_ex5.X by decide)}\n" ++
    s!"M24,  τ ⊨ def(x2) = " ++
      s!"{satMEx5 M24 "x2" (show ({"x1"} : Finset ShapeLabel) ⊆ S_ex5.X by decide)}\n" ++
    s!"M2a,  τ ⊨ def(x5) = " ++
      s!"{satMEx5 M2a "x5" (show ({"x0"} : Finset ShapeLabel) ⊆ S_ex5.X by decide)}\n" ++
    s!"M24a, τ ⊨ def(x6) = " ++
      s!"{satMEx5 M24a "x6" (show ({"x3"} : Finset ShapeLabel) ⊆ S_ex5.X by decide)}"

end Examples
