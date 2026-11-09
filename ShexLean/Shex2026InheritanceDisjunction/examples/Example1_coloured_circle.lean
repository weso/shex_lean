import ShexLean.Shex2026InheritanceDisjunction.Render
import Mathlib.Tactic.FinCases
import Example

/-!
An example for the exploration of disjunctive `extends` (refer to the
module docstring of `ShexLean/Shex2026InheritanceDisjunction/Syntax.lean`).
It is a formalized version of the hypothetical case of §6 "Design
Choices" in Boneva, Labra Gayo, Prud'hommeaux, Thornton, Waagmeester
(2025):

> Suppose that the definition was `Figure → ⟨coord @CartesianCoord⟩ or
> ⟨coord @PolarCoord⟩`. This raises the question whether we allow a
> `ColouredCircle` to have both Cartesian and polar coordinates, the one
> inherited from `ColouredFigure`, the other inherited from `Circle`.
> Allowing it would be undesirable.

`S_disj` below is exactly this variant of the motivating schema of §2. We
removed `Attribute`, `Colour` and `Radius`, because they are not related
to the coordinate question of this file.

* The body of `Figure` is now the disjunction of two shapes
  `[⟨coord @CartesianCoord⟩, ⟨coord @PolarCoord⟩]` (the `hs` field of
  `ShapeExpr.extends`, in `Syntax.lean`).
* `Circle` and `ColouredFigure` both `extends {"Figure"}`.
* `ColouredCircle` inherits from the two (multiple inheritance).

This is exactly the structure that tests the problem of the paper.

There are three claims. Each claim is a direct `SatisfiesFuel` or
`SatisfiesMFuel` derivation, proved by hand:

- `f1_satisfies_ColouredCircle`: a node with *consistent* Cartesian
  coordinates is a `ColouredCircle` (`pick "Figure" := 0`).
- `f2_satisfies_ColouredCircle`: a node with *consistent* polar
  coordinates is *also* a `ColouredCircle` (`pick "Figure" := 1`). The
  paper says that this legitimate use is the reason to want the
  relaxation.
- `f3_not_satisfies_ColouredCircle`: a node whose `coord` object has
  *neither* type is *not* a `ColouredCircle`, for *each* choice of
  `pick`, `Mx` and `M'`.

For `f3`, refer to the rule-18 mechanism in the module docstring of
`Semantics.lean`. `Circle` and `ColouredFigure` get a shared part through
`Figure`. The mechanism forces this part to be the *same* single
`Mx "Figure"` and `pick "Figure"`, through each of the two parents. Thus,
"Cartesian through one path, and polar through the other path" is not
possible, also in principle. We made `f3` so that neither disjunct alone
is available. Thus, this proof is the nearest that this file gets to a
*demonstration* of the fix, not only a statement of it.

At the end, the file also computes the three claims with `native_decide`,
with the `Decidable` instances of this folder.
-/

namespace ShexLean.InheritanceDisjunction

open ShexLean.InheritanceCore

/-- A fuel bound that is sufficient for all the proofs in this file. -/
def bigFuelDisj : ℕ := 10

/-- `T_float`, approximated as "any integer literal". This is the same
convention as in `ShexLean.Shex2025Inheritance.examples.Example1_figures`,
for the same reason: `Literal` has no float constructor. -/
def cFloatDisj : NodeConstraint
  | .lit (.int _) => True
  | _ => False

/-- `S_disj`: the schema of §2, with `Attribute`, `Colour` and `Radius`
removed, and the body of `Figure` replaced with the hypothetical shape of
§6, which has two disjuncts. -/
def S_disj : Schema where
  Y := {"T_float"}
  X := {"Figure", "Circle", "ColouredFigure", "ColouredCircle"}
  A := ∅
  disjointYX := by decide
  A_subX := by decide
  shapeDef
    | "T_float" => .constraint cFloatDisj
    | "CartesianCoord" =>
        .ofShape ⟨false, none, .seq (.tc "x" "T_float") (.tc "y" "T_float")⟩
    | "PolarCoord" =>
        .ofShape ⟨false, none, .seq (.tc "r" "T_float") (.tc "theta" "T_float")⟩
    | "Figure" =>
        .extends ∅ [⟨false, none, .tc "coord" "CartesianCoord"⟩,
          ⟨false, none, .tc "coord" "PolarCoord"⟩]
    | "Circle" => .extends {"Figure"} [⟨false, none, .empty⟩]
    | "ColouredFigure" => .extends {"Figure"} [⟨false, none, .empty⟩]
    | "ColouredCircle" => .extends {"Circle", "ColouredFigure"} [⟨false, none, .empty⟩]
    | _ => .constraint (fun _ => False)

/-- A coordinate node with real (consistent) Cartesian data. -/
def cCart : Subject := .iri "cCart"
/-- A coordinate node with real (consistent) polar data. -/
def cPolar : Subject := .iri "cPolar"
/-- A coordinate node with neither: only an `x`, and no `y`, `r` or
`theta`. -/
def cBad : Subject := .iri "cBad"

/-- A `ColouredCircle` candidate with consistent Cartesian coordinates. -/
def f1 : Subject := .iri "f1"
/-- A `ColouredCircle` candidate with consistent polar coordinates. -/
def f2 : Subject := .iri "f2"
/-- A `ColouredCircle` candidate whose coordinates are neither. -/
def f3 : Subject := .iri "f3"

def G_disj : Graph :=
  { ⟨cCart, "x", .lit (.int 2)⟩, ⟨cCart, "y", .lit (.int 4)⟩,
    ⟨cPolar, "r", .lit (.int 5)⟩, ⟨cPolar, "theta", .lit (.int 1)⟩,
    ⟨cBad, "x", .lit (.int 9)⟩,
    ⟨f1, "coord", cCart⟩, ⟨f2, "coord", cPolar⟩, ⟨f3, "coord", cBad⟩ }

/-- The typing facts:

* The literal values of `x`, `y`, `r` and `theta` have the type `T_float`.
* `cCart` has the type `CartesianCoord`.
* `cPolar` has the type `PolarCoord`.
* `cBad` has *neither* type. `f3_not_satisfies_ColouredCircle` depends on
  this one fact. -/
def τ_disj : Typing :=
  { (RDFNode.lit (.int 2), "T_float"), (RDFNode.lit (.int 4), "T_float"),
    (RDFNode.lit (.int 5), "T_float"), (RDFNode.lit (.int 1), "T_float"),
    ((cCart : RDFNode), "CartesianCoord"), ((cPolar : RDFNode), "PolarCoord") }

theorem hFigureEdge : ∀ c, ¬ S_disj.extEdge "Figure" c := by
  have hshape : S_disj.shapeDef "Figure" =
      .extends ∅ [⟨false, none, .tc "coord" "CartesianCoord"⟩,
        ⟨false, none, .tc "coord" "PolarCoord"⟩] := rfl
  intro c hc; unfold Schema.extEdge at hc; rw [hshape] at hc
  simp [ShapeExpr.extendsTargets] at hc

theorem hCircleEdge : ∀ c, S_disj.extEdge "Circle" c ↔ c = "Figure" := by
  have hshape : S_disj.shapeDef "Circle" = .extends {"Figure"} [⟨false, none, .empty⟩] := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem hColouredFigureEdge : ∀ c, S_disj.extEdge "ColouredFigure" c ↔ c = "Figure" := by
  have hshape : S_disj.shapeDef "ColouredFigure" =
      .extends {"Figure"} [⟨false, none, .empty⟩] := rfl
  intro c; unfold Schema.extEdge; rw [hshape]
  simp [ShapeExpr.extendsTargets]

theorem reach_root {S : Schema} {p : Label} (hparent : ∀ c, ¬ S.extEdge p c) :
    ∀ x', Relation.ReflTransGen S.extEdge p x' → x' = p := by
  intro x' h
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
  · exact heq.symm
  · exact absurd hc (hparent c)

theorem anc_root {S : Schema} {x : Label} (hx : x ∈ S.X)
    (hedge : ∀ c, ¬ S.extEdge x c) : S.anc x = {x} := by
  apply Finset.ext; intro x'
  unfold Schema.anc
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩; exact reach_root hedge x' h
  · rintro rfl; exact ⟨hx, Relation.ReflTransGen.refl⟩

theorem anc_one_parent {S : Schema} {x p : Label} (hx : x ∈ S.X) (hp : p ∈ S.X)
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

theorem hancFigure : S_disj.anc "Figure" = {"Figure"} := anc_root (by decide) hFigureEdge
theorem hancCircle : S_disj.anc "Circle" = {"Circle", "Figure"} :=
  anc_one_parent (by decide) (by decide) hCircleEdge hFigureEdge
theorem hancColouredFigure : S_disj.anc "ColouredFigure" = {"ColouredFigure", "Figure"} :=
  anc_one_parent (by decide) (by decide) hColouredFigureEdge hFigureEdge

theorem hancSetCircleColouredFigure :
    S_disj.ancSet {"Circle", "ColouredFigure"} = {"Circle", "Figure", "ColouredFigure"} := by
  unfold Schema.ancSet
  rw [show ({"Circle", "ColouredFigure"} : Finset Label) = insert "Circle" {"ColouredFigure"}
      from rfl, Finset.biUnion_insert, Finset.singleton_biUnion, hancCircle, hancColouredFigure]
  decide

/-- The empty set trivially satisfies the trivial shape `[ε]`, which is not
closed and has no `extra` (rule 17 of Table 3). -/
theorem empty_satisfies_emptyShape {τ : Typing} :
    SatisfiesShape τ (∅ : Finset Triple) ⟨false, none, .empty⟩ := by
  have hMeEmpty : Me τ (∅ : Finset Triple) TripleExpr.empty = ∅ := by unfold Me; simp
  refine ⟨?_, ?_, fun h => absurd h (by decide)⟩
  · show SatisfiesE τ (Me τ (∅ : Finset Triple) TripleExpr.empty) TripleExpr.empty
    rw [hMeEmpty]; rfl
  · show props (Mnotin τ (∅ : Finset Triple) TripleExpr.empty) ⊆ (∅ : Finset IRI)
    unfold Mnotin
    simp [props, TripleExpr.props, TripleExpr.tcs]

/-- `f1` (with `coord` to `cCart`, a node with consistent Cartesian data)
is a `ColouredCircle`. The proof selects `pick "Figure" := 0`
(`CartesianCoord`, the first disjunct of the body of `Figure`).
`Mx "Circle"` and `Mx "ColouredFigure"` are both `∅` (their own `hs` is
`[⟨ε⟩]`). `Mx "Figure"` takes the one `coord` triple. -/
theorem f1_satisfies_ColouredCircle :
    SatisfiesFuel bigFuelDisj S_disj G_disj τ_disj f1 (S_disj.shapeDef "ColouredCircle") := by
  have hshape : S_disj.shapeDef "ColouredCircle" =
      .extends {"Circle", "ColouredFigure"} [⟨false, none, .empty⟩] := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_disj τ_disj (neigh G_disj f1) _)
  have hneigh : neigh G_disj f1 = {(⟨f1, "coord", cCart⟩ : Triple)} := by decide
  rw [hneigh]
  refine ⟨∅, fun x => if x = "Figure" then {(⟨f1, "coord", cCart⟩ : Triple)} else ∅,
    fun _ => 0, ⟨?_, ?_, ?_⟩, ⟨⟨false, none, .empty⟩, by decide, empty_satisfies_emptyShape⟩, ?_, ?_⟩
  · rw [hancSetCircleColouredFigure]; simp
  · rw [hancSetCircleColouredFigure]
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    unfold Function.onFun
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all
  · rw [hancSetCircleColouredFigure]; decide
  · rw [hancSetCircleColouredFigure]
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> [rfl; skip; rfl]
    show SatisfiesE τ_disj {(⟨f1, "coord", cCart⟩ : Triple)}
      ((S_disj.shapeDef "Figure").extTeAt 0)
    have : (S_disj.shapeDef "Figure").extTeAt 0 = .tc "coord" "CartesianCoord" := rfl
    rw [this]
    exact ⟨f1, cCart, rfl, by decide⟩
  · rw [hancSetCircleColouredFigure]
    intro x hx u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hCshape : S_disj.shapeDef "Circle" = .extends {"Figure"} [⟨false, none, .empty⟩] := rfl
    have hFshape : S_disj.shapeDef "Figure" =
        .extends ∅ [⟨false, none, .tc "coord" "CartesianCoord"⟩,
          ⟨false, none, .tc "coord" "PolarCoord"⟩] := rfl
    have hCFshape : S_disj.shapeDef "ColouredFigure" =
        .extends {"Figure"} [⟨false, none, .empty⟩] := rfl
    rcases hx with rfl | rfl | rfl
    · rw [hCshape] at hu; simp [ShapeExpr.restrOf] at hu
    · rw [hFshape] at hu; simp [ShapeExpr.restrOf] at hu
    · rw [hCFshape] at hu; simp [ShapeExpr.restrOf] at hu

/-- `f2` (with `coord` to `cPolar`, a node with consistent polar data) is
*also* a `ColouredCircle`. The proof selects `pick "Figure" := 1`
(`PolarCoord`). The discussion of §6 in the paper says that this
legitimate use, with one consistent choice, is what was wanted. The proof
has the same structure as `f1_satisfies_ColouredCircle`. Only the `pick`
and the typing fact are different. -/
theorem f2_satisfies_ColouredCircle :
    SatisfiesFuel bigFuelDisj S_disj G_disj τ_disj f2 (S_disj.shapeDef "ColouredCircle") := by
  have hshape : S_disj.shapeDef "ColouredCircle" =
      .extends {"Circle", "ColouredFigure"} [⟨false, none, .empty⟩] := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_disj τ_disj (neigh G_disj f2) _)
  have hneigh : neigh G_disj f2 = {(⟨f2, "coord", cPolar⟩ : Triple)} := by decide
  rw [hneigh]
  refine ⟨∅, fun x => if x = "Figure" then {(⟨f2, "coord", cPolar⟩ : Triple)} else ∅,
    fun _ => 1, ⟨?_, ?_, ?_⟩, ⟨⟨false, none, .empty⟩, by decide, empty_satisfies_emptyShape⟩, ?_, ?_⟩
  · rw [hancSetCircleColouredFigure]; simp
  · rw [hancSetCircleColouredFigure]
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    unfold Function.onFun
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all
  · rw [hancSetCircleColouredFigure]; decide
  · rw [hancSetCircleColouredFigure]
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> [rfl; skip; rfl]
    show SatisfiesE τ_disj {(⟨f2, "coord", cPolar⟩ : Triple)}
      ((S_disj.shapeDef "Figure").extTeAt 1)
    have : (S_disj.shapeDef "Figure").extTeAt 1 = .tc "coord" "PolarCoord" := rfl
    rw [this]
    exact ⟨f2, cPolar, rfl, by decide⟩
  · rw [hancSetCircleColouredFigure]
    intro x hx u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hCshape : S_disj.shapeDef "Circle" = .extends {"Figure"} [⟨false, none, .empty⟩] := rfl
    have hFshape : S_disj.shapeDef "Figure" =
        .extends ∅ [⟨false, none, .tc "coord" "CartesianCoord"⟩,
          ⟨false, none, .tc "coord" "PolarCoord"⟩] := rfl
    have hCFshape : S_disj.shapeDef "ColouredFigure" =
        .extends {"Figure"} [⟨false, none, .empty⟩] := rfl
    rcases hx with rfl | rfl | rfl
    · rw [hCshape] at hu; simp [ShapeExpr.restrOf] at hu
    · rw [hFshape] at hu; simp [ShapeExpr.restrOf] at hu
    · rw [hCFshape] at hu; simp [ShapeExpr.restrOf] at hu

/-- `f3` (with `coord` to `cBad`, which has neither `CartesianCoord` nor
`PolarCoord` in `τ_disj`) is **not** a `ColouredCircle`. This is true for
*each* choice of `M'`, `Mx` and `pick`, not only for the choices above.

* `Mx "Circle"` and `Mx "ColouredFigure"` must be `∅`. (Rule 1 of Table 1:
  `.empty` requires the set to *be* `∅`. It is not "no constraint", as the
  case of `.ofShape` that is not closed in rule 17.)
* Thus, the one `coord` triple must go into `Mx "Figure"`. Then it needs
  `τ_disj.has cBad "CartesianCoord"` (if `pick "Figure"` is even) or
  `τ_disj.has cBad "PolarCoord"` (if it is odd). The two are false.

This is the nearest that this file gets to a *demonstration* of the fix of
§6, not only a statement of it. `f3` cannot get through with "half" a
Cartesian coordinate and "half" a polar coordinate from its two different
parents, because the two parents must use the same `Mx "Figure"` slot. -/
theorem f3_not_satisfies_ColouredCircle :
    ¬ SatisfiesFuel bigFuelDisj S_disj G_disj τ_disj f3 (S_disj.shapeDef "ColouredCircle") := by
  have hshape : S_disj.shapeDef "ColouredCircle" =
      .extends {"Circle", "ColouredFigure"} [⟨false, none, .empty⟩] := rfl
  rw [hshape]
  show ¬ SatisfiesMFuel _ S_disj τ_disj (neigh G_disj f3) _
  have hneigh : neigh G_disj f3 = {(⟨f3, "coord", cBad⟩ : Triple)} := by decide
  rw [hneigh]
  rintro ⟨M', Mx, pick, ⟨-, -, hunion⟩, -, hext, -⟩
  rw [hancSetCircleColouredFigure] at hunion hext
  have hCshape : S_disj.shapeDef "Circle" = .extends {"Figure"} [⟨false, none, .empty⟩] := rfl
  have hCFshape : S_disj.shapeDef "ColouredFigure" =
      .extends {"Figure"} [⟨false, none, .empty⟩] := rfl
  have hFshape : S_disj.shapeDef "Figure" =
      .extends ∅ [⟨false, none, .tc "coord" "CartesianCoord"⟩,
        ⟨false, none, .tc "coord" "PolarCoord"⟩] := rfl
  have hCircleEmpty : Mx "Circle" = ∅ := by
    have h := hext "Circle" (by decide)
    rwa [hCshape, ShapeExpr.extTeAt_one] at h
  have hCFEmpty : Mx "ColouredFigure" = ∅ := by
    have h := hext "ColouredFigure" (by decide)
    rwa [hCFshape, ShapeExpr.extTeAt_one] at h
  have hFig := hext "Figure" (by decide)
  have hMxFigSub : Mx "Figure" ⊆ {(⟨f3, "coord", cBad⟩ : Triple)} := by
    intro t ht
    rw [hunion]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨"Figure", by decide, ht⟩)
  rw [hFshape, ShapeExpr.extTeAt_two] at hFig
  rcases Nat.mod_two_eq_zero_or_one (pick "Figure") with hpar | hpar <;>
    simp only [hpar] at hFig <;>
    obtain ⟨n, o, hMeq, hty⟩ := hFig <;>
    (have ho : o = cBad := by
      have hmem := hMxFigSub (hMeq ▸ Finset.mem_singleton_self _)
      simp only [Finset.mem_singleton, Triple.mk.injEq] at hmem
      exact hmem.2.2) <;>
    subst ho <;>
    exact absurd hty (by decide)

/-! The prerequisites for the decidability of `S_disj` (`Decidable.lean`),
and the three claims above computed again with `native_decide`. This is
the same method as `ShexLean.Shex2025Inheritance.examples.Example1_figures`
for the original formalism. The expected results are:

* `f1 ⊨ ColouredCircle` and `f2 ⊨ ColouredCircle` compute `true`.
* `f3 ⊨ ColouredCircle` computes `false`. -/

theorem S_disj_XClosed : S_disj.XClosed := by unfold Schema.XClosed; decide

theorem S_disj_RestrOk : S_disj.RestrOk := by
  intro x hx u hu
  fin_cases hx <;> simp [S_disj, ShapeExpr.restrOf] at hu

def cartesianCoordFOk : (S_disj.shapeDef "CartesianCoord").FOk S_disj := PUnit.unit
def polarCoordFOk : (S_disj.shapeDef "PolarCoord").FOk S_disj := PUnit.unit
def figureFOk : (S_disj.shapeDef "Figure").FOk S_disj := PLift.up (by decide)
def circleFOk : (S_disj.shapeDef "Circle").FOk S_disj := PLift.up (by decide)
def colouredFigureFOk : (S_disj.shapeDef "ColouredFigure").FOk S_disj := PLift.up (by decide)
def colouredCircleFOk : (S_disj.shapeDef "ColouredCircle").FOk S_disj := PLift.up (by decide)

/-- The result of `renderDecide`, computed with `native_decide`, for
`n ⊨ S_disj.shapeDef L`. There is one line for each main claim below. -/
def satDisj (n : RDFNode) (L : Label) (hOk : (S_disj.shapeDef L).FOk S_disj) : String :=
  renderDecide (satisfiesFuel_decidable S_disj G_disj τ_disj S_disj_XClosed S_disj_RestrOk
    bigFuelDisj n (S_disj.shapeDef L) hOk)

end ShexLean.InheritanceDisjunction

namespace Examples

open ShexLean.InheritanceDisjunction (S_disj G_disj τ_disj satDisj colouredCircleFOk f1 f2 f3)
open ShexLean (Graph.render renderDecide)

/-- The `ColouredCircle` counterexample of §6 "Design Choices". The body of
`Figure` is relaxed to an `extends` with two disjuncts. This tests the
ambiguity that the paper does not resolve.

* `f1 ⊨ ColouredCircle` and `f2 ⊨ ColouredCircle` (consistent Cartesian
  or polar coordinates) compute `true` with `native_decide`. Thus, the
  relaxation still accepts the legitimate use.
* `f3 ⊨ ColouredCircle` (neither) computes `false`. Thus, the fix with the
  `pick` witness (`Semantics.lean`) blocks the case "half Cartesian, half
  polar" that the paper warns about. This is a checked computation, not
  only an omission. -/
def inheritanceDisjunctionColouredCircle : Example where
  name := "inheritance2026-disjunction-coloured-circle"
  summary := "§6 relaxation, ColouredCircle with Cartesian or polar coordinates: " ++
    "consistent use accepted, inconsistent use rejected."
  schemaText := S_disj.render
  graphText := Graph.render G_disj
  typingText :=
    s!"f1 ⊨ ColouredCircle = {satDisj f1 "ColouredCircle" colouredCircleFOk} " ++
      "(consistent Cartesian coordinates)\n" ++
    s!"f2 ⊨ ColouredCircle = {satDisj f2 "ColouredCircle" colouredCircleFOk} " ++
      "(consistent Polar coordinates)\n" ++
    s!"f3 ⊨ ColouredCircle = {satDisj f3 "ColouredCircle" colouredCircleFOk} " ++
      "(neither — the §6 ambiguity, correctly rejected)"

end Examples
