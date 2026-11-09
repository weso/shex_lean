import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2025Inheritance.Stratification
import ShexLean.Shex2025Inheritance.Render
import Mathlib.Tactic.FinCases
import Example

-- The draft definitions are in their own namespace, so that their names do
-- not conflict with the worked examples of `Example3_triple_match.lean`.
namespace ShexLean.Inheritance.Drafts

open ShexLean.InheritanceCore hiding Schema

def bigFuel1 : ℕ := 4

/-!
 Simple draft examples to check the definitions.

 ShEx:

:x2 { :p ["v2"] }
:x1 extends @:x2 { :p [ "v1" ] }

Data:

:ok1 :p "v1"; :p "v2" .

`x2` must also have the `.extends` form. (The second bullet of
Definition 2: each label in `X` needs `def(x) = extends X h [and u]`.) The
reason is that `x2` comes after the `extends` of `x1`, and rule 18 of
Table 3 reads `ext-te(x2)` from `(S.shapeDef "x2").extTe`. This has a
meaning only for that form.

`x2` is a leaf of the hierarchy (`extends ∅`, with nothing more to
inherit). Its constraint is only `p @c2`. We removed the
`{p xsd:string} AND {p ["v2"]}` of the original draft, because `c2` (the
literal `"v2"`) already implies `cStr` (any string). Thus, the
conjunction was redundant. -/

def cStr : NodeConstraint
  | .lit (.str _) => True
  | _ => False

def c1 : NodeConstraint
  | .lit (.str "v1") => True
  | _ => False

def c2 : NodeConstraint
  | .lit (.str "v2") => True
  | _ => False

def S: Schema where
  Y := { "c1", "c2", "cStr"}
  X := { "x1", "x2"}
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "x1" => .extends { "x2" } ⟨false, none, .tc "p" "c1" ⟩
    | "x2" => .extends ∅ ⟨false, none, .tc "p" "c2" ⟩
    | "c1" => .constraint c1
    | "c2" => .constraint c2
    | "cStr" => .constraint cStr
    | _ => .constraint (fun _ => False)

def a : Subject := .iri "a"
def b : Subject := .iri "b"


def G: Graph :=
 {
  ⟨a, "p", .lit (.str "v1")⟩,
  ⟨a, "p", .lit (.str "v2")⟩,
  ⟨b, "p", .lit (.str "v1")⟩,
  ⟨b, "p", .lit (.str "v3")⟩
 }


def τ : Typing :=
  { (RDFNode.lit (.str "v1"), "c1"),
    (RDFNode.lit (.str "v2"), "c2"),
    (RDFNode.lit (.str "v1"), "cStr"),
    (RDFNode.lit (.str "v2"), "cStr"),
    ((a: RDFNode), "x1"),
    ((a: RDFNode), "x2"),
    ((b: RDFNode), "x1")
  }

/-- `a, τ ⊨ def(x1)`. `def(x1) = extends x2 ⟨p @c1⟩`. Thus,
`anc({x2}) = {x2}` (`x2` is a leaf, `extends ∅`), and
`neigh_G(a) = {(a,p,v1), (a,p,v2)}` splits into two parts:

* `M' = {(a,p,v1)}`, which satisfies the `⟨p @c1⟩` of `x1`.
* `Mx2 = {(a,p,v2)}`, which satisfies `ext-te(x2) = p @c2`. -/
theorem a_satisfies_x1 :
    SatisfiesFuel bigFuel1 S G τ a (S.shapeDef "x1") := by
  have hx1shape : S.shapeDef "x1" = .extends {"x2"} ⟨false, none, .tc "p" "c1"⟩ := rfl
  have hx2shape : S.shapeDef "x2" = .extends ∅ ⟨false, none, .tc "p" "c2"⟩ := rfl
  have hx2edge : ∀ c, ¬ S.extEdge "x2" c := by
    intro c hc
    unfold Schema.extEdge at hc
    rw [hx2shape] at hc
    simp [ShapeExpr.extendsTargets] at hc
  have hx2 : ∀ x', Relation.ReflTransGen S.extEdge "x2" x' → x' = "x2" := by
    intro x' h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
    · exact heq.symm
    · exact absurd hc (hx2edge c)
  have hanc2 : S.anc "x2" = {"x2"} := by
    apply Finset.ext
    intro x'
    unfold Schema.anc
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact hx2 x' h
    · rintro rfl; exact ⟨by decide, Relation.ReflTransGen.refl⟩
  have hancSet : S.ancSet {"x2"} = {"x2"} := by
    unfold Schema.ancSet; simp [hanc2]
  rw [hx1shape]
  show SatisfiesMFuel bigFuel1 S τ (neigh G a) (.extends {"x2"} ⟨false, none, .tc "p" "c1"⟩)
  refine ⟨{⟨a, "p", .lit (.str "v1")⟩}, fun _ => {⟨a, "p", .lit (.str "v2")⟩},
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hancSet]; decide
  · rw [hancSet]; intro x hx y hy hxy
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · rw [hancSet]; decide
  · exact singleton_tc_ofShape (by decide)
  · rw [hancSet]
    intro x hx
    simp only [Finset.mem_singleton] at hx; subst hx
    show SatisfiesE τ {⟨a, "p", .lit (.str "v2")⟩} (S.shapeDef "x2").extTe
    rw [hx2shape]
    exact ⟨a, .lit (.str "v2"), rfl, by decide⟩
  · rw [hancSet]
    intro x hx u hu
    simp only [Finset.mem_singleton] at hx; subst hx
    rw [hx2shape] at hu
    simp [ShapeExpr.restrOf] at hu


/-- `b, τ ⊭ def(x1)`. `neigh_G(b) = {(b,p,v1), (b,p,v3)}`.

The `v1` triple is the only triple with the type `c1`. Thus, the
`⟨p @c1⟩` of `x1` (`extra := none`) can take only this triple. This
forces the `v3` triple into `Mx "x2"`, which must satisfy
`ext-te(x2) = p @c2` (rule 18). But `v3` also does not have the type `c2`
in `τ` (it has no type). Thus, no partition of `neigh_G(b)` works. -/
theorem b_doesnt_satisfy_x1 :
    ¬ SatisfiesFuel bigFuel1 S G τ b (S.shapeDef "x1") := by
  have hx1shape : S.shapeDef "x1" = .extends {"x2"} ⟨false, none, .tc "p" "c1"⟩ := rfl
  have hx2shape : S.shapeDef "x2" = .extends ∅ ⟨false, none, .tc "p" "c2"⟩ := rfl
  have hx2edge : ∀ c, ¬ S.extEdge "x2" c := by
    intro c hc
    unfold Schema.extEdge at hc
    rw [hx2shape] at hc
    simp [ShapeExpr.extendsTargets] at hc
  have hx2 : ∀ x', Relation.ReflTransGen S.extEdge "x2" x' → x' = "x2" := by
    intro x' h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
    · exact heq.symm
    · exact absurd hc (hx2edge c)
  have hanc2 : S.anc "x2" = {"x2"} := by
    apply Finset.ext
    intro x'
    unfold Schema.anc
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact hx2 x' h
    · rintro rfl; exact ⟨by decide, Relation.ReflTransGen.refl⟩
  have hancSet : S.ancSet {"x2"} = {"x2"} := by
    unfold Schema.ancSet; simp [hanc2]
  rw [hx1shape]
  show ¬ SatisfiesMFuel bigFuel1 S τ (neigh G b) (.extends {"x2"} ⟨false, none, .tc "p" "c1"⟩)
  have hneighb : neigh G b =
      {⟨b, "p", .lit (.str "v1")⟩, ⟨b, "p", .lit (.str "v3")⟩} := by decide
  rw [hneighb]
  rintro ⟨M', Mx, ⟨-, -, hunion⟩, hM', hMx, -⟩
  rw [hancSet] at hunion hMx
  have hv3mem : (⟨b, "p", .lit (.str "v3")⟩ : Triple) ∈ M' ∪ ({"x2"} : Finset Label).biUnion Mx :=
    hunion ▸ (by decide)
  rw [Finset.mem_union, Finset.mem_biUnion] at hv3mem
  rcases hv3mem with hv3M' | ⟨x, hx, hv3Mx⟩
  · -- v3 ∈ M': ⟨p @c1⟩ cannot take it (v3 does not have the type c1). Thus,
    -- it goes into Mnotin, which contradicts extra := none.
    obtain ⟨-, hMnotin, -⟩ := hM'
    have hv3notin : (⟨b, "p", .lit (.str "v3")⟩ : Triple) ∈
        Mnotin τ M' (TripleExpr.tc "p" "c1") := by
      rw [mem_Mnotin]
      refine ⟨⟨hv3M', ?_⟩, ?_⟩
      · simp [TripleExpr.props, TripleExpr.tcs]
      · rw [mem_Me]
        rintro ⟨-, z, hz, hty⟩
        simp only [TripleExpr.tcs, Finset.mem_singleton, Prod.mk.injEq] at hz
        obtain ⟨-, hz⟩ := hz; subst hz
        exact absurd hty (by decide)
    have hpmem : "p" ∈ props (Mnotin τ M' (TripleExpr.tc "p" "c1")) :=
      Finset.mem_image_of_mem Triple.pred hv3notin
    have := hMnotin hpmem
    simp at this
  · -- v3 ∈ Mx "x2": it must satisfy ext-te(x2) = p @c2, but v3 also does not
    -- have the type c2 in τ.
    simp only [Finset.mem_singleton] at hx; subst hx
    have hEx := hMx "x2" (by decide)
    obtain ⟨n, o, heq, hty⟩ := hEx
    rw [heq] at hv3Mx
    simp only [Finset.mem_singleton] at hv3Mx
    have hobj : (⟨b, "p", .lit (.str "v3")⟩ : Triple).obj = o := by rw [hv3Mx]
    rw [← hobj] at hty
    exact absurd hty (by decide)

end ShexLean.Inheritance.Drafts
