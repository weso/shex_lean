import ShexLean.Shex2025Inheritance.Stratification
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
Lemma 1 (§4.2) of the 2025 paper "Shape Expressions with Inheritance":

> Lemma 1. The evaluation of `G, n, τ ⊨_S def(z)` always terminates, for
> every schema `S = (Y, X, def, A)`, graph `G`, node `n` of `G`, typing `τ`
> of `G` by `S`, and label `z ∈ Y ∪ X`.

`Semantics.lean` avoids the termination problem with an explicit argument
`Fuel : ℕ` in `SatisfiesMFuel`. The fuel counts the depth of nested
`restr(x)` evaluations in rule 18. At the lowest layer, each `restr(x)` is
`False`. Thus, the Lean function is total by construction, but it is not
yet the real relation of the paper (which does not depend on fuel).

This file shows that, for a well-defined schema, the result stops
depending on `Fuel` when `Fuel` is sufficiently large. Thus, the
approximation bounded by fuel becomes equal to the real relation.

The termination argument of the paper (the proof sketch of Lemma 1) is one
sentence: the tree of recursive calls is finite "due to the acyclic nature
of the extension hierarchy". A precise proof needs two items:

* A rank function on labels that is a witness of the acyclicity of `H_S`
  (`Schema.extRank` below).
* A proof that `extRank` bounds the depth of nested `restr(x)` evaluations
  (`Schema.RankOk` and `Schema.rankOk_any`).

The proof has the same generality as Lemma 1 of the paper. It assumes only
`ExtAcyclic` (Definition 6). (`WellFormedX` is not necessary: for a label
that is not well-formed, `ext-te(x)` and `restr(x)` are junk values that
do not recurse.) It puts no restriction on the locations of `extends`
nodes. An `extends` node can also be inside a restriction `u`
(`extends X h and u`).
-/

namespace ShexLean.Inheritance

/-! ### Extension-hierarchy acyclicity -/

/-- `S.anc` becomes strictly smaller along each edge of `H_S`, if
`S.ExtAcyclic` is true (the acyclicity condition of Definition 6).

If `x` extends `y`, then `x` also extends each label that `y` extends
transitively. But `x ∈ S.anc x`, and `x ∈ S.anc y` closes a cycle through
the edge `x → y`. This is the usual argument with the number of ancestors
as a rank function on a DAG. Because of it, `ExtAcyclic` alone gives a
well-founded measure. -/
theorem Schema.anc_ssubset_of_extEdge {S : Schema} (hAcyclic : S.ExtAcyclic)
    {x y : Label} (hxX : x ∈ S.X) (hxy : S.extEdge x y) :
    S.anc y ⊂ S.anc x := by
  have hsub : S.anc y ⊆ S.anc x := by
    intro z hz
    rw [Schema.mem_anc] at hz ⊢
    exact ⟨hz.1, Relation.ReflTransGen.head hxy hz.2⟩
  refine ⟨hsub, fun hsub' => ?_⟩
  have hxy' : Relation.ReflTransGen S.extEdge y x :=
    (Schema.mem_anc.mp (hsub' (Schema.mem_anc_self hxX))).2
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy' with heq | htrans
  · exact hAcyclic x hxX (Relation.TransGen.single (heq.symm ▸ hxy))
  · exact hAcyclic x hxX (Relation.TransGen.head hxy htrans)

/-- `S.extRank x := (S.anc x).card`: a rank in `ℕ` that is a witness of the
acyclicity of `H_S`. It decreases strictly along each edge
(`extRank_lt_of_extEdge` below). The termination argument in the rest of
this file uses this well-founded measure. -/
noncomputable def Schema.extRank (S : Schema) (x : Label) : ℕ := (S.anc x).card

/-- The rank form of `anc_ssubset_of_extEdge`: `extRank` decreases
strictly along each edge of `H_S` that starts at a label of `S`. -/
theorem Schema.extRank_lt_of_extEdge {S : Schema} (hAcyclic : S.ExtAcyclic)
    {x y : Label} (hxX : x ∈ S.X) (hxy : S.extEdge x y) :
    S.extRank y < S.extRank x :=
  Finset.card_lt_card (S.anc_ssubset_of_extEdge hAcyclic hxX hxy)

/-- `extRank` does not increase along an ancestor path. If `x' ∈ S.anc x`,
then `extRank x' ≤ extRank x`. (The inequality is not strict, because
`x ∈ S.anc x` reflexively.) This bounds the rank of each label that a
rule-18 partition reaches (`x' ∈ S.ancSet xs`), not only the direct
targets `xs`. -/
theorem Schema.extRank_le_of_mem_anc {S : Schema} {x x' : Label} (hx' : x' ∈ S.anc x) :
    S.extRank x' ≤ S.extRank x := by
  apply Finset.card_le_card
  intro z hz
  rw [Schema.mem_anc] at hx' hz ⊢
  exact ⟨hz.1, hx'.2.trans hz.2⟩

/-! ### The base case: `NoExtends` shapes need no schema lookups -/

/-- `s` contains no `.extends` node at any location (also not nested in
`or`, `and` or `not`). -/
def ShapeExpr.NoExtends : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends _ _ => False
  | .or s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .and s1 s2 => s1.NoExtends ∧ s2.NoExtends
  | .not s => s.NoExtends

/-! ### The rank witness

`Schema.RankOk S r s` says that `r` layers of `SatisfiesMAt` are
sufficient for `s`. It is made in the same way as `SatisfiesMFuel`:

* `RankOkAt S lowerOk s` checks one layer. For each `.extends` node of
  `s`, the restriction `restr(x)` of each ancestor `x` must satisfy
  `lowerOk`.
* `RankOk S 0 := RankOkAt S (fun _ => False)`: no `restr(x)` is reachable.
* `RankOk S (r+1) := RankOkAt S (RankOk S r)`.

`Schema.rankOk_shapeDef` is the acyclicity argument. For `x ∈ S.X`,
`RankOk S (extRank x) (S.shapeDef x)` is true, by strong induction on
`extRank x`. The reason is that each extends target reachable from the
definition of `x` has a strictly smaller rank (`extRank_lt_of_extEdge`).

`Schema.rankOk_any` extends this result to each `ShapeExpr`, with one
global rank bound, `S.X.sup S.extRank + 1`. -/

/-- One layer of the rank witness. Refer to the section docstring. -/
def Schema.RankOkAt (S : Schema) (lowerOk : ShapeExpr → Prop) : ShapeExpr → Prop
  | .constraint _ => True
  | .ofShape _ => True
  | .extends xs _ => ∀ x ∈ S.ancSet xs, ∀ u, (S.shapeDef x).restrOf = some u → lowerOk u
  | .or s1 s2 => Schema.RankOkAt S lowerOk s1 ∧ Schema.RankOkAt S lowerOk s2
  | .and s1 s2 => Schema.RankOkAt S lowerOk s1 ∧ Schema.RankOkAt S lowerOk s2
  | .not s => Schema.RankOkAt S lowerOk s

def Schema.RankOk (S : Schema) : ℕ → ShapeExpr → Prop
  | 0 => Schema.RankOkAt S (fun _ => False)
  | r + 1 => Schema.RankOkAt S (Schema.RankOk S r)

theorem Schema.RankOkAt.of_noExtends (S : Schema) (lowerOk : ShapeExpr → Prop) :
    ∀ s : ShapeExpr, s.NoExtends → Schema.RankOkAt S lowerOk s := by
  intro s
  induction s with
  | constraint _ | ofShape _ => intro _; trivial
  | «extends» _ _ => intro hs; exact hs.elim
  | or _ _ ih1 ih2 | and _ _ ih1 ih2 => intro hs; exact ⟨ih1 hs.1, ih2 hs.2⟩
  | not _ ih => exact ih

theorem Schema.RankOkAt.mono_pred (S : Schema) {P Q : ShapeExpr → Prop} (hPQ : ∀ u, P u → Q u) :
    ∀ s, Schema.RankOkAt S P s → Schema.RankOkAt S Q s := by
  intro s
  induction s with
  | constraint c => intro _; trivial
  | ofShape h => intro _; trivial
  | «extends» xs h =>
      intro hs x hx u hu
      exact hPQ u (hs x hx u hu)
  | or s1 s2 ih1 ih2 => intro hs; exact ⟨ih1 hs.1, ih2 hs.2⟩
  | and s1 s2 ih1 ih2 => intro hs; exact ⟨ih1 hs.1, ih2 hs.2⟩
  | not s ih => intro hs; exact ih hs

/-- `RankOk` is monotone. If a rank is sufficient for `s`, each higher
rank is also sufficient. -/
theorem Schema.RankOk.mono {S : Schema} : ∀ r s, Schema.RankOk S r s → Schema.RankOk S (r + 1) s := by
  intro r
  induction r with
  | zero => exact Schema.RankOkAt.mono_pred S (fun _ h => h.elim)
  | succ r' ih => exact Schema.RankOkAt.mono_pred S ih

theorem Schema.RankOk.mono_le {S : Schema} {r r' : ℕ} (h : r ≤ r') :
    ∀ s, Schema.RankOk S r s → Schema.RankOk S r' s := by
  induction h with
  | refl => intro s hs; exact hs
  | step _ ih => intro s hs; exact Schema.RankOk.mono _ s (ih s hs)

/-- Each `x ∈ S.X` has `extRank x ≥ 1` (reflexively, `x ∈ S.anc x`). Thus,
you can always write `extRank x` as `m + 1`. -/
theorem Schema.extRank_succ {S : Schema} {x : Label} (hx : x ∈ S.X) :
    ∃ m, S.extRank x = m + 1 := by
  have h1 : 1 ≤ S.extRank x := Finset.one_le_card.mpr ⟨x, Schema.mem_anc_self hx⟩
  exact ⟨S.extRank x - 1, by omega⟩

/-- From the `RankOk` of the definition of `x` (`extends xs h [and u]`),
get the `RankOk` of its restriction `u`. -/
theorem Schema.RankOk_restrOf {S : Schema} {x : Label} (hx : x ∈ S.X)
    {u : ShapeExpr} (hu : (S.shapeDef x).restrOf = some u)
    (hRank : Schema.RankOk S (S.extRank x) (S.shapeDef x)) :
    Schema.RankOk S (S.extRank x) u := by
  obtain ⟨xs, h, heq⟩ := ShapeExpr.restrOf_eq_some.mp hu
  rw [heq] at hRank
  obtain ⟨m, hm⟩ := Schema.extRank_succ hx
  rw [hm] at hRank ⊢
  exact hRank.2

/-- Let `e` be a `ShapeExpr` whose direct `.extends` targets are all real
edges of `H_S` out of `x`. Let each `x' ∈ S.X` with a strictly smaller
rank already have `RankOk` of its definition. Then `e` is `RankOkAt` at
rank `m := extRank x - 1`.

With `e := S.shapeDef x`, this closes the induction in
`rankOk_shapeDef`. The statement is for a general `e`, because the
restriction `u` of `x` needs the same fact. -/
theorem Schema.RankOkAt_of_edges {S : Schema} (hAcyclic : S.ExtAcyclic)
    {x : Label} (hx : x ∈ S.X)
    (IH : ∀ x' ∈ S.X, S.extRank x' < S.extRank x → Schema.RankOk S (S.extRank x') (S.shapeDef x'))
    {m : ℕ} (hm : S.extRank x = m + 1) :
    ∀ e : ShapeExpr, (∀ z ∈ e.extendsTargets, S.extEdge x z) →
      Schema.RankOkAt S (Schema.RankOk S m) e := by
  intro e
  induction e with
  | constraint c => intro _; trivial
  | ofShape h => intro _; trivial
  | «extends» zs h =>
      intro hzs x' hx' u hu
      obtain ⟨z, hzzs, hx'z⟩ := Finset.mem_biUnion.mp hx'
      have hxz : S.extEdge x z := hzs z (by simpa [ShapeExpr.extendsTargets] using hzzs)
      have hrankz : S.extRank z < S.extRank x := Schema.extRank_lt_of_extEdge hAcyclic hx hxz
      have hx'X : x' ∈ S.X := Schema.anc_subset_X hx'z
      have hrankx' : S.extRank x' ≤ S.extRank z := Schema.extRank_le_of_mem_anc hx'z
      have hrankx'm : S.extRank x' ≤ m := by omega
      have hIHx' : Schema.RankOk S (S.extRank x') (S.shapeDef x') := IH x' hx'X (by omega)
      have hru := Schema.RankOk_restrOf hx'X hu hIHx'
      exact Schema.RankOk.mono_le hrankx'm u hru
  | or s1 s2 ih1 ih2 =>
      intro hst
      refine ⟨ih1 (fun z hz => hst z ?_), ih2 (fun z hz => hst z ?_)⟩
      · simp only [ShapeExpr.extendsTargets, Finset.mem_union]; exact Or.inl hz
      · simp only [ShapeExpr.extendsTargets, Finset.mem_union]; exact Or.inr hz
  | and s1 s2 ih1 ih2 =>
      intro hst
      refine ⟨ih1 (fun z hz => hst z ?_), ih2 (fun z hz => hst z ?_)⟩
      · simp only [ShapeExpr.extendsTargets, Finset.mem_union]; exact Or.inl hz
      · simp only [ShapeExpr.extendsTargets, Finset.mem_union]; exact Or.inr hz
  | not s ih =>
      intro hst
      exact ih (fun z hz => hst z (by simpa [ShapeExpr.extendsTargets] using hz))

/-- For `x ∈ S.X`, the definition of `x` is `RankOk` at exactly the rank
of `x`. The proof is by strong induction on `extRank x`, with
`RankOkAt_of_edges`. This is the precise form of the termination argument
of Lemma 1. `ExtAcyclic` alone is sufficient. There is no other
restriction on the locations of `extends` nodes. -/
theorem Schema.rankOk_shapeDef {S : Schema} (hAcyclic : S.ExtAcyclic) :
    ∀ x ∈ S.X, Schema.RankOk S (S.extRank x) (S.shapeDef x) := by
  have key : ∀ n x, x ∈ S.X → S.extRank x = n → Schema.RankOk S (S.extRank x) (S.shapeDef x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro x hx hxn
      obtain ⟨m, hm⟩ := Schema.extRank_succ hx
      have hIH : ∀ x' ∈ S.X, S.extRank x' < S.extRank x →
          Schema.RankOk S (S.extRank x') (S.shapeDef x') := by
        intro x' hx' hlt
        exact IH (S.extRank x') (hxn ▸ hlt) x' hx' rfl
      have hedges : ∀ z ∈ (S.shapeDef x).extendsTargets, S.extEdge x z := fun z hz => hz
      have hres := Schema.RankOkAt_of_edges hAcyclic hx hIH hm (S.shapeDef x) hedges
      rw [hm]
      exact hres
  intro x hx
  exact key (S.extRank x) x hx rfl

/-- Extends `rankOk_shapeDef` from one `x ∈ S.X` to each `ShapeExpr`
(also to `S.shapeDef z` for a simple label `z` that is not in `S.X`). The
global bound `S.X.sup S.extRank + 1` is always sufficient. -/
theorem Schema.rankOk_any {S : Schema} (hAcyclic : S.ExtAcyclic) :
    ∀ e : ShapeExpr, Schema.RankOk S (S.X.sup S.extRank + 1) e := by
  intro e
  induction e with
  | constraint c => trivial
  | ofShape h => trivial
  | «extends» xs h =>
      show Schema.RankOkAt S (Schema.RankOk S (S.X.sup S.extRank)) (.extends xs h)
      intro x' hx' u hu
      have hx'X : x' ∈ S.X := Schema.ancSet_subset_X hx'
      have hrank : S.extRank x' ≤ S.X.sup S.extRank := Finset.le_sup hx'X
      have hok := Schema.rankOk_shapeDef hAcyclic x' hx'X
      have hru := Schema.RankOk_restrOf hx'X hu hok
      exact Schema.RankOk.mono_le hrank u hru
  | or s1 s2 ih1 ih2 => exact ⟨ih1, ih2⟩
  | and s1 s2 ih1 ih2 => exact ⟨ih1, ih2⟩
  | not s ih => exact ih

/-- The fuel that is always sufficient for `S` (refer to `rankOk_any`). -/
noncomputable def Schema.fuelBound (S : Schema) : ℕ := S.X.sup S.extRank + 1

theorem Schema.rankOk_fuelBound {S : Schema} (hAcyclic : S.ExtAcyclic) {r : ℕ}
    (hr : S.fuelBound ≤ r) (s : ShapeExpr) : Schema.RankOk S r s :=
  Schema.RankOk.mono_le hr s (Schema.rankOk_any hAcyclic s)

/-! ### The stabilization argument -/

/-- One layer of Table 3 depends on `restr` only through its values on the
restrictions that the rank witness covers. The proof is a plain
structural induction. -/
theorem SatisfiesMAt_congr_restr {S : Schema} {τ : Typing}
    {restr1 restr2 : Finset Triple → ShapeExpr → Prop} {P : ShapeExpr → Prop}
    (hr : ∀ u, P u → ∀ M, restr1 M u ↔ restr2 M u) :
    ∀ s, S.RankOkAt P s → ∀ M, SatisfiesMAt S τ restr1 M s ↔ SatisfiesMAt S τ restr2 M s := by
  intro s
  induction s with
  | constraint _ | ofShape _ => intros; rfl
  | «extends» xs h =>
      intro hRank M
      simp only [SatisfiesMAt]
      refine exists_congr fun M' => exists_congr fun Mx => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => ?_
      exact forall₂_congr fun x hx => forall₂_congr fun u hu => hr u (hRank x hx u hu) _
  | or s1 s2 ih1 ih2 => intro hRank M; exact or_congr (ih1 hRank.1 M) (ih2 hRank.2 M)
  | and s1 s2 ih1 ih2 => intro hRank M; exact and_congr (ih1 hRank.1 M) (ih2 hRank.2 M)
  | not s ih => intro hRank M; exact not_congr (ih hRank M)

/-- `SatisfiesMFuel` is stable above a sufficient rank: if `RankOk S r s`,
each fuel `r' ≥ r` gives the same result. The proof is an induction on
`r`. Each step is `SatisfiesMAt_congr_restr`. -/
theorem stableM {S : Schema} {τ : Typing} :
    ∀ r s, Schema.RankOk S r s → ∀ r', r ≤ r' → ∀ M,
      SatisfiesMFuel r S τ M s ↔ SatisfiesMFuel r' S τ M s := by
  intro r
  induction r with
  | zero =>
      intro s hs r' _ M
      cases r' with
      | zero => rfl
      | succ r' => exact SatisfiesMAt_congr_restr (fun _ h => h.elim) s hs M
  | succ r ih =>
      intro s hs r' hr' M
      obtain ⟨r', rfl⟩ : ∃ k, r' = k + 1 := ⟨r' - 1, by omega⟩
      exact SatisfiesMAt_congr_restr (fun u hu M => ih u hu r' (by omega) M) s hs M

/-- Table 2 is structural. Thus, if two Table-3 evaluators agree on the
leaves (`.ofShape` and `.extends`) that satisfy a predicate `Q`, and `Q`
goes down through `or`, `and` and `not`, the two results agree. -/
theorem SatisfiesAt_congr {G : Graph} {satM1 satM2 : Finset Triple → ShapeExpr → Prop}
    {n : RDFNode} (Q : ShapeExpr → Prop)
    (hor : ∀ {a b}, Q (.or a b) → Q a ∧ Q b) (hand : ∀ {a b}, Q (.and a b) → Q a ∧ Q b)
    (hnot : ∀ {a}, Q (.not a) → Q a) (hleaf : ∀ t, Q t → ∀ M, satM1 M t ↔ satM2 M t) :
    ∀ s, Q s → (SatisfiesAt G satM1 n s ↔ SatisfiesAt G satM2 n s) := by
  intro s
  induction s with
  | constraint _ => intros; rfl
  | ofShape h => intro hQ; exact hleaf _ hQ _
  | «extends» xs h => intro hQ; exact hleaf _ hQ _
  | or s1 s2 ih1 ih2 => intro hQ; exact or_congr (ih1 (hor hQ).1) (ih2 (hor hQ).2)
  | and s1 s2 ih1 ih2 => intro hQ; exact and_congr (ih1 (hand hQ).1) (ih2 (hand hQ).2)
  | not s ih => intro hQ; exact not_congr (ih (hnot hQ))

/-- `SatisfiesFuel` (Table 2) is stable above `S.fuelBound`. -/
theorem stableFuel {S : Schema} (hAcyclic : S.ExtAcyclic) {r r' : ℕ}
    (hr : S.fuelBound ≤ r) (hr' : r ≤ r') (G : Graph) (τ : Typing) (n : RDFNode) (s : ShapeExpr) :
    SatisfiesFuel r S G τ n s ↔ SatisfiesFuel r' S G τ n s :=
  SatisfiesAt_congr (fun _ => True) (fun _ => ⟨trivial, trivial⟩) (fun _ => ⟨trivial, trivial⟩)
    (fun _ => trivial)
    (fun t _ M => stableM r t (Schema.rankOk_fuelBound hAcyclic hr t) r' hr' M) s trivial

/-! ### Packaging: the real `Satisfies`, and Lemma 1 -/

/-- The real `n, τ ⊨_S s` (with no `Fuel` parameter). It evaluates at the
fuel `S.fuelBound`, which is sufficient. By `stableFuel`, each larger fuel
gives the same result. `lemma1` below records this. -/
noncomputable def Satisfies (S : Schema) (G : Graph) (τ : Typing) (n : RDFNode)
    (s : ShapeExpr) : Prop :=
  SatisfiesFuel S.fuelBound S G τ n s

/-- Lemma 1. Let `S` be a schema that satisfies `ExtAcyclic`. (This is the
hypothesis of the paper. There is no restriction on the locations of
`extends` nodes.) Then the evaluation of `n, τ ⊨_S def(z)` terminates.
Each sufficiently large `Fuel` gives the same answer as `Satisfies`, for
each node `n`, typing `τ` and label `z`. -/
theorem lemma1 {S : Schema} (hAcyclic : S.ExtAcyclic)
    (G : Graph) (τ : Typing) (n : RDFNode) (z : Label) (fuel : ℕ)
    (hfuel : S.fuelBound ≤ fuel) :
    SatisfiesFuel fuel S G τ n (S.shapeDef z) ↔ Satisfies S G τ n (S.shapeDef z) :=
  (stableFuel hAcyclic le_rfl hfuel G τ n (S.shapeDef z)).symm

end ShexLean.Inheritance
