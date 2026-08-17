import ShexLean.Shex2026InheritanceDisjunction.Render
import Mathlib.Tactic.FinCases
import Example

/-!
Phase 3 of the disjunction-extension exploration (`ShexLean/
Shex2026InheritanceDisjunction/Syntax.lean`'s module docstring): a formalized
version of the §6 "Design Choices" hypothetical from Boneva, Labra Gayo,
Prud'hommeaux, Thornton, Waagmeester (2025):

> Suppose that the definition was `Figure → ⟨coord @CartesianCoord⟩ or
> ⟨coord @PolarCoord⟩`. This raises the question whether we allow a
> `ColouredCircle` to have both Cartesian and polar coordinates, the one
> inherited from `ColouredFigure`, the other inherited from `Circle`.
> Allowing it would be undesirable.

`S_disj` below is exactly this variant of §2's motivating schema (with
`Attribute`/`Colour`/`Radius` stripped out — irrelevant to the coordinate
question this file is about): `Figure`'s body is now the two-shape
disjunction `[⟨coord @CartesianCoord⟩, ⟨coord @PolarCoord⟩]`
(`ShapeExpr.extends`'s `hs` field, `Syntax.lean`), and `Circle`/
`ColouredFigure` both `extends {"Figure"}`, with `ColouredCircle` multiply
inheriting from both — the exact shape needed to exercise the paper's own
worry.

Three claims, each a direct `SatisfiesFuel`/`SatisfiesMFuel` derivation
(hand-proved — this folder's `Decidable.lean`/`Render.lean` analogues are
future work, see the top-level exploration plan):

- `f1_satisfies_ColouredCircle`: a node with *consistent* Cartesian
  coordinates is a `ColouredCircle` (`pick "Figure" := 0`).
- `f2_satisfies_ColouredCircle`: a node with *consistent* Polar coordinates
  is *also* a `ColouredCircle` (`pick "Figure" := 1`) — the legitimate use
  the paper says motivated wanting this in the first place.
- `f3_not_satisfies_ColouredCircle`: a node whose `coord` object has
  *neither* type is *not* a `ColouredCircle`, for *any* choice of `pick`/
  `Mx`/`M'` — the rule-18 mechanism (`Semantics.lean`'s module docstring)
  structurally forces `Circle`'s and `ColouredFigure`'s shared contribution
  through `Figure` to be the *same* single `Mx "Figure"`/`pick "Figure"`
  regardless of which parent it's viewed through, so there is no way to
  satisfy "Cartesian via one path, Polar via the other" even in principle —
  this proof is the closest this file gets to *demonstrating* that rather
  than just asserting it, since `f3` is constructed precisely so that
  neither disjunct alone is available either.
-/

namespace ShexLean.InheritanceDisjunction

/-- A fuel bound generous enough for every proof in this file. -/
def bigFuelDisj : ℕ := 10

/-- `T_float`, approximated as "any integer literal" (matching the
convention `ShexLean.Shex2025Inheritance.examples.Example1_figures` already
uses for the same reason: `Literal` has no float constructor). -/
def cFloatDisj : NodeConstraint
  | .lit (.int _) => True
  | _ => False

/-- `S_disj`: §2's schema with `Attribute`/`Colour`/`Radius` removed and
`Figure`'s body replaced by the §6 hypothetical two-disjunct shape. -/
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

/-- A coordinate node with genuine (consistent) Cartesian data. -/
def cCart : Subject := .iri "cCart"
/-- A coordinate node with genuine (consistent) Polar data. -/
def cPolar : Subject := .iri "cPolar"
/-- A coordinate node with neither: an `x` only, no `y`/`r`/`theta`. -/
def cBad : Subject := .iri "cBad"

/-- A `ColouredCircle` candidate with consistent Cartesian coordinates. -/
def f1 : Subject := .iri "f1"
/-- A `ColouredCircle` candidate with consistent Polar coordinates. -/
def f2 : Subject := .iri "f2"
/-- A `ColouredCircle` candidate whose coordinates are neither. -/
def f3 : Subject := .iri "f3"

def G_disj : Graph :=
  { ⟨cCart, "x", .lit (.int 2)⟩, ⟨cCart, "y", .lit (.int 4)⟩,
    ⟨cPolar, "r", .lit (.int 5)⟩, ⟨cPolar, "theta", .lit (.int 1)⟩,
    ⟨cBad, "x", .lit (.int 9)⟩,
    ⟨f1, "coord", cCart⟩, ⟨f2, "coord", cPolar⟩, ⟨f3, "coord", cBad⟩ }

/-- Typing facts: literal `x`/`y`/`r`/`theta` values are `T_float`; `cCart`
has type `CartesianCoord`, `cPolar` has type `PolarCoord`; `cBad` has
*neither* — the one fact `f3_not_satisfies_ColouredCircle` turns on. -/
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

theorem hancFigure : S_disj.anc "Figure" = {"Figure"} := anc_root (by decide) hFigureEdge
theorem hancCircle : S_disj.anc "Circle" = {"Circle", "Figure"} :=
  anc_one_parent (by decide) (by decide) hCircleEdge hFigureEdge
theorem hancColouredFigure : S_disj.anc "ColouredFigure" = {"ColouredFigure", "Figure"} :=
  anc_one_parent (by decide) (by decide) hColouredFigureEdge hFigureEdge

theorem hancSetCircleColouredFigure :
    S_disj.ancSet {"Circle", "ColouredFigure"} = {"Circle", "Figure", "ColouredFigure"} := by
  unfold Schema.ancSet
  rw [show ({"Circle", "ColouredFigure"} : Finset ShapeLabel) = insert "Circle" {"ColouredFigure"}
      from rfl, Finset.biUnion_insert, Finset.singleton_biUnion, hancCircle, hancColouredFigure]
  decide

/-- The empty set trivially satisfies the (non-closed, no-`extra`) trivial
shape `[ε]` (Table 3 rule 17). -/
theorem empty_satisfies_emptyShape {S : Schema} {G : Graph} {τ : Typing} {fuel : ℕ} :
    SatisfiesMFuel (fuel + 2) S G τ (∅ : Finset Triple) (.ofShape ⟨false, none, .empty⟩) := by
  have hMeEmpty : Me τ (∅ : Finset Triple) TripleExpr.empty = ∅ := by unfold Me; simp
  refine ⟨?_, ?_, fun h => absurd h (by decide)⟩
  · show SatisfiesEFuel (fuel + 1) S G τ (Me τ (∅ : Finset Triple) TripleExpr.empty) TripleExpr.empty
    rw [hMeEmpty]; rfl
  · show props (Mnotin τ (∅ : Finset Triple) TripleExpr.empty) ⊆ (∅ : Finset IRI)
    unfold Mnotin
    simp [props, TripleExpr.props, TripleExpr.tcs]

/-- `f1` (`coord` to `cCart`, a consistent-Cartesian node) is a
`ColouredCircle`, choosing `pick "Figure" := 0` (`CartesianCoord`, the
first disjunct of `Figure`'s body). `Mx "Circle"`/`Mx "ColouredFigure"` are
both `∅` (their own `hs` is `[⟨ε⟩]`); `Mx "Figure"` takes the one `coord`
triple. -/
theorem f1_satisfies_ColouredCircle :
    SatisfiesFuel bigFuelDisj S_disj G_disj τ_disj f1 (S_disj.shapeDef "ColouredCircle") := by
  have hshape : S_disj.shapeDef "ColouredCircle" =
      .extends {"Circle", "ColouredFigure"} [⟨false, none, .empty⟩] := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_disj G_disj τ_disj (neigh G_disj f1) _)
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
    show SatisfiesEFuel _ S_disj G_disj τ_disj {(⟨f1, "coord", cCart⟩ : Triple)}
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

/-- `f2` (`coord` to `cPolar`, a consistent-Polar node) is *also* a
`ColouredCircle`, choosing `pick "Figure" := 1` (`PolarCoord`) — the
legitimate single-consistent-choice use the paper's own §6 discussion says
was wanted. Structurally identical to `f1_satisfies_ColouredCircle` other
than the `pick`/typing-fact swap. -/
theorem f2_satisfies_ColouredCircle :
    SatisfiesFuel bigFuelDisj S_disj G_disj τ_disj f2 (S_disj.shapeDef "ColouredCircle") := by
  have hshape : S_disj.shapeDef "ColouredCircle" =
      .extends {"Circle", "ColouredFigure"} [⟨false, none, .empty⟩] := rfl
  rw [hshape]
  refine (?_ : SatisfiesMFuel _ S_disj G_disj τ_disj (neigh G_disj f2) _)
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
    show SatisfiesEFuel _ S_disj G_disj τ_disj {(⟨f2, "coord", cPolar⟩ : Triple)}
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

/-- `f3` (`coord` to `cBad`, which has neither `CartesianCoord` nor
`PolarCoord` in `τ_disj`) is **not** a `ColouredCircle` — for *any* choice
of `M'`/`Mx`/`pick`, not just the ones tried above. `Mx "Circle"`/
`Mx "ColouredFigure"` are forced to `∅` (Table 1 rule 1, `.empty` requires
the set to *be* `∅`, not just "no constraint" the way rule 17's `.ofShape`
non-closed case is), so the single `coord` triple must land in
`Mx "Figure"`, which then needs `τ_disj.has cBad "CartesianCoord"` (if
`pick "Figure"` is even) or `τ_disj.has cBad "PolarCoord"` (if odd) — both
false. This is the closest this file gets to *demonstrating* rather than
just asserting the §6 fix: there is no way for `f3` to sneak through by
having "half" a Cartesian and "half" a Polar coordinate contributed via
its two different parents, because both parents are forced to route
through the very same `Mx "Figure"` slot. -/
theorem f3_not_satisfies_ColouredCircle :
    ¬ SatisfiesFuel bigFuelDisj S_disj G_disj τ_disj f3 (S_disj.shapeDef "ColouredCircle") := by
  have hshape : S_disj.shapeDef "ColouredCircle" =
      .extends {"Circle", "ColouredFigure"} [⟨false, none, .empty⟩] := rfl
  rw [hshape]
  show ¬ SatisfiesMFuel _ S_disj G_disj τ_disj (neigh G_disj f3) _
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

/-! `S_disj`'s decidability prerequisites (`Decidable.lean`) and a
`native_decide`-verified re-derivation of the three claims above, the same
way `ShexLean.Shex2025Inheritance.examples.Example1_figures` does for the
unmodified formalism — `f1`/`f2 ⊨ ColouredCircle` should compute `true`,
`f3 ⊨ ColouredCircle` should compute `false`. -/

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

/-- `renderDecide`'s `native_decide`-computed verdict for `n ⊨
S_disj.shapeDef L`, one line per headline claim below. -/
def satDisj (n : RDFNode) (L : ShapeLabel) (hOk : (S_disj.shapeDef L).FOk S_disj) : String :=
  renderDecide (satisfiesFuel_decidable S_disj G_disj τ_disj S_disj_XClosed S_disj_RestrOk
    bigFuelDisj n (S_disj.shapeDef L) hOk)

end ShexLean.InheritanceDisjunction

namespace Examples

open ShexLean.InheritanceDisjunction (S_disj G_disj τ_disj satDisj colouredCircleFOk f1 f2 f3)
open ShexLean (Graph.render renderDecide)

/-- The §6 "Design Choices" `ColouredCircle` counterexample: `Figure`'s
body relaxed to a two-disjunct `extends`, exercising the very ambiguity the
paper declines to resolve. `f1`/`f2 ⊨ ColouredCircle` (consistent
Cartesian/Polar coordinates, `native_decide`-computed `true`) show the
relaxation still admits the legitimate use case; `f3 ⊨ ColouredCircle`
(neither) computes `false` — the `pick`-witness fix (`Semantics.lean`)
blocks the "half Cartesian, half Polar" case the paper warns about, not
just by omission but as a checked computation. -/
def inheritanceDisjunctionColouredCircle : Example where
  name := "inheritance2026-disjunction-coloured-circle"
  summary := "§6's declined ColouredCircle/Cartesian-or-Polar relaxation: legitimate use " ++
    "accepted, inconsistent use rejected."
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
