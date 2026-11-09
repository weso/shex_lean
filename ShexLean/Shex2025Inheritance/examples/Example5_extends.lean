import ShexLean.Shex2025Inheritance.examples.Example3_triple_match
import ShexLean.Shex2025Inheritance.Render
import Example

/-!
Example 5 from the 2025 paper "Shape Expressions with Inheritance" (§4.2,
rule 18 of Table 3): a chain of shapes `x0..x6` related by `extends`
(schema `S_ex5`, in `Example3_triple_match.lean`). It tests the partition
of the `extends` rule over `anc(X)`.

The paper gives the schema of Example 5 as `S = (Y, {x1,...,x6}, def, ∅)`.
But `def(x1)` and `def(x3)` both use `extends x0`. Thus, `x0` must be a
member of the extendable-label set `X`, so that `Schema.anc` and
`Schema.WellFormedX` see it as a node of `H_S` (Definition 3: the vertex
set of `H_S` is `X`). This is possibly a small omission in the statement
of the example in the paper. The definition of `x0`,
`extends _ ⟨p @Teven⟩`, has exactly the form that Definition 2 requires
for an `X` label. The `S_ex5.X` of `Example3_triple_match.lean` includes
`x0`.
-/

namespace ShexLean.Inheritance

open ShexLean.InheritanceCore hiding Schema

/-- `M24, τ ⊨ def(x1)` (Example 5). `def(x1) = extends x0 ⟨p @T_even⟩`.
Thus, `anc({x0}) = {x0}`, and `M24` splits into two parts:

* `M'`, which satisfies `⟨p @T_even⟩`.
* `Mx0`, which satisfies `ext-te(x0) = p @T_even`. (`x0` has no
  restriction.) -/
theorem M24_satisfies_defx1 :
    SatisfiesMFuel bigFuel S_ex5 τ_ex3 M24 (S_ex5.shapeDef "x1") := by
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
    show SatisfiesE τ_ex3 {tp "p" (.lit (.int 4))}
      (S_ex5.shapeDef "x0").extTe
    exact ⟨n_ex3, .lit (.int 4), rfl, by decide⟩
  · rw [hanc]
    intro x hx u hu
    simp only [Finset.mem_singleton] at hx
    subst hx
    rw [hx0shape] at hu
    simp [ShapeExpr.restrOf] at hu

/-- `M246, τ ⊨ def(x2)` (Example 5). `def(x2) = extends x1 ⟨p @T_<5⟩`.
Thus, `anc({x1}) = {x1, x0}` (`x1` extends `x0`), and `M246` splits into
three parts:

* `M'={2}`, which satisfies `⟨p @T_<5⟩`.
* `Mx1={4}` and `Mx0={6}`, which both satisfy `ext-te = p @T_even`.
  (`x0` and `x1` have no restriction.) -/
theorem M246_satisfies_defx2 :
    SatisfiesMFuel bigFuel S_ex5 τ_ex3 M246 (S_ex5.shapeDef "x2") := by
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

/-- `M24, τ ¬⊨ def(x2)` (Example 5). The rule-18 partition of `def(x2)`
needs *three* pairwise disjoint singletons (`M'`, `Mx1` and `Mx0`; a plain
`.tc` forces each of them). Thus, each `M` that satisfies it has exactly
three elements. But `M24.card = 2`. -/
theorem M24_not_satisfies_defx2 :
    ¬ SatisfiesMFuel bigFuel S_ex5 τ_ex3 M24 (S_ex5.shapeDef "x2") := by
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
  have hx0anc : ("x0" : Label) ∈ S_ex5.ancSet {"x1"} := by rw [hancSet1]; decide
  have hx1anc : ("x1" : Label) ∈ S_ex5.ancSet {"x1"} := by rw [hancSet1]; decide
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

/-- `M2a, τ ⊨ def(x5)` (Example 5). `def(x5) = extends x0 extra {p} ⟨ε⟩`.

* `M'` must satisfy the shape `[extra {p}]⟨ε⟩`. This shape permits the
  leftover triple with `"a"`. (A plain `⟨ε⟩` forces `M' = ∅`.)
* `Mx0={2}` satisfies `ext-te(x0) = p @T_even`. -/
theorem M2a_satisfies_defx5 :
    SatisfiesMFuel bigFuel S_ex5 τ_ex3 M2a (S_ex5.shapeDef "x5") := by
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
    · show SatisfiesE τ_ex3
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

/-- `M24a, τ ¬⊨ def(x6)` (Example 5). `def(x6) = extends x3 ⟨p @T_even⟩`.

The `extra {p}` of the definition of `x5` has no effect here, because `x5`
is not an ancestor of `x6`. `x6` extends `x3`, whose `h` is
`⟨p @T_even⟩ and ⟨(p@T_>5)*⟩`, with no `extra`. Thus, nothing permits the
leftover triple with `"a"` in `M24a`.

As `M24_not_satisfies_defx2` shows for a chain of similar form, the
cardinality is also not correct. `x3` needs 2 more `p` triples in
addition to the triples of `x6`, and the four sets of the paper do not
give them without reuse. This proof checks only the obstruction of the
`"a"` triple, which the claim of the paper shows. -/
theorem M24a_not_satisfies_defx6 :
    ¬ SatisfiesMFuel bigFuel S_ex5 τ_ex3 M24a (S_ex5.shapeDef "x6") := by
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
open ShexLean (Triple Label Graph.render Typing.render renderDecide)

/-- The result of `renderDecide`, computed with `native_decide`, for
`M ⊨ def(L)`. -/
def satMEx5 (M : Finset Triple) (L : Label)
    (hOk : (S_ex5.shapeDef L).MOk S_ex5) : String :=
  renderDecide (satisfiesMFuel_decidable S_ex5 τ_ex3 S_ex5_XClosed S_ex5_RestrOk
    bigFuel M (S_ex5.shapeDef L) hOk)

/-- The `extends` chain of Example 5.

* `schemaText` is generated from the real `S_ex5`.
* Each claim `M ⊨ def(L)` in `typingText` is a `native_decide` computation
  with `satisfiesMFuel_decidable`. This includes `M24, τ ⊨ def(x1)`
  (proved above with the rule-18 partition of `x1` against its ancestor
  `x0`), and the two negative claims proved above with the cardinality
  and leftover-triple arguments. -/
def inheritance2025Extends : Example where
  name := "inheritance2025-example5-extends"
  summary := "extends chain x0..x6. M24,τ ⊨ def(x1) with the rule-18 partition of x1."
  schemaText := S_ex5.render
  graphText :=
    s!"M24  = {Graph.render M24}\n" ++
    s!"M246 = {Graph.render M246}\n" ++
    s!"M2a  = {Graph.render M2a}\n" ++
    s!"M24a = {Graph.render M24a}"
  typingText :=
    s!"τ = {Typing.render τ_ex3}\n" ++
    s!"M24,  τ ⊨ def(x1) = " ++
      s!"{satMEx5 M24 "x1" (show ({"x0"} : Finset Label) ⊆ S_ex5.X by decide)}\n" ++
    s!"M246, τ ⊨ def(x2) = " ++
      s!"{satMEx5 M246 "x2" (show ({"x1"} : Finset Label) ⊆ S_ex5.X by decide)}\n" ++
    s!"M24,  τ ⊨ def(x2) = " ++
      s!"{satMEx5 M24 "x2" (show ({"x1"} : Finset Label) ⊆ S_ex5.X by decide)}\n" ++
    s!"M2a,  τ ⊨ def(x5) = " ++
      s!"{satMEx5 M2a "x5" (show ({"x0"} : Finset Label) ⊆ S_ex5.X by decide)}\n" ++
    s!"M24a, τ ⊨ def(x6) = " ++
      s!"{satMEx5 M24a "x6" (show ({"x3"} : Finset Label) ⊆ S_ex5.X by decide)}"

end Examples
