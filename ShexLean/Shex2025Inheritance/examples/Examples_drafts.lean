import ShexLean.Shex2025Inheritance.Semantics
import ShexLean.Shex2025Inheritance.Stratification
import ShexLean.Shex2025Inheritance.Render
import Mathlib.Tactic.FinCases
import Example

namespace ShexLean.Inheritance

def bigFuel1 : ℕ := 4

/-!
 Simple example drafts to check definitions

 ShEx:

:x2 { :p ["v2"] }
:x1 extends @:x2 { :p [ "v1" ] }

Data:

:ok1 :p "v1"; :p "v2" .

`x2` must itself be `.extends`-shaped (Definition 2's second bullet: every
label in `X` needs `def(x) = extends X h [and u]`), since it is named
after `x1`'s `extends` and Table 3's rule 18 reads `ext-te(x2)` off
`(S.shapeDef "x2").extTe`, which is only meaningful for that form. `x2` is
a leaf of the hierarchy (`extends ∅`, nothing further to inherit), and its
own constraint is just `p @c2` — the original draft's `{p xsd:string} AND
{p ["v2"]}` is dropped since `c2` (literal `"v2"`) already implies
`cStr` (any string), so the conjunction was redundant. -/

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

/-- `a, τ ⊨ def(x1)`: `def(x1) = extends x2 ⟨p @c1⟩`, so `anc({x2}) = {x2}`
(`x2` is a leaf, `extends ∅`) and `neigh_G(a) = {(a,p,v1), (a,p,v2)}` splits
into `M' = {(a,p,v1)}` (satisfying `x1`'s own `⟨p @c1⟩`) and
`Mx2 = {(a,p,v2)}` (satisfying `ext-te(x2) = p @c2`). -/
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
  show SatisfiesMFuel 3 S G τ (neigh G a) (.extends {"x2"} ⟨false, none, .tc "p" "c1"⟩)
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
    show SatisfiesEFuel 2 S G τ {⟨a, "p", .lit (.str "v2")⟩} (S.shapeDef "x2").extTe
    rw [hx2shape]
    exact ⟨a, .lit (.str "v2"), rfl, by decide⟩
  · rw [hancSet]
    intro x hx u hu
    simp only [Finset.mem_singleton] at hx; subst hx
    rw [hx2shape] at hu
    simp [ShapeExpr.restrOf] at hu


/-- `b, τ ⊭ def(x1)`: `neigh_G(b) = {(b,p,v1), (b,p,v3)}`. The `v1` triple
is the only one typed `c1`, so `x1`'s own `⟨p @c1⟩` (`extra := none`) can
only ever absorb it, forcing the `v3` triple into `Mx "x2"`, which must
satisfy `ext-te(x2) = p @c2` (rule 18) — but `v3` isn't typed `c2` in `τ`
either (it isn't typed anything), so no partition of `neigh_G(b)` works. -/
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
  show ¬ SatisfiesMFuel 3 S G τ (neigh G b) (.extends {"x2"} ⟨false, none, .tc "p" "c1"⟩)
  have hneighb : neigh G b =
      {⟨b, "p", .lit (.str "v1")⟩, ⟨b, "p", .lit (.str "v3")⟩} := by decide
  rw [hneighb]
  rintro ⟨M', Mx, ⟨-, -, hunion⟩, hM', hMx, -⟩
  rw [hancSet] at hunion hMx
  have hv3mem : (⟨b, "p", .lit (.str "v3")⟩ : Triple) ∈ M' ∪ ({"x2"} : Finset Label).biUnion Mx :=
    hunion ▸ (by decide)
  rw [Finset.mem_union, Finset.mem_biUnion] at hv3mem
  rcases hv3mem with hv3M' | ⟨x, hx, hv3Mx⟩
  · -- v3 ∈ M': it can't be absorbed by ⟨p @c1⟩ (v3 isn't typed c1), so it
    -- leaks into Mnotin, contradicting extra := none.
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
  · -- v3 ∈ Mx "x2": it must satisfy ext-te(x2) = p @c2, but v3 isn't typed
    -- c2 in τ either.
    simp only [Finset.mem_singleton] at hx; subst hx
    have hEx := hMx "x2" (by decide)
    obtain ⟨n, o, heq, hty⟩ := hEx
    rw [heq] at hv3Mx
    simp only [Finset.mem_singleton] at hv3Mx
    have hobj : (⟨b, "p", .lit (.str "v3")⟩ : Triple).obj = o := by rw [hv3Mx]
    rw [← hobj] at hty
    exact absurd hty (by decide)
