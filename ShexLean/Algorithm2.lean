import ShexLean.Lemma2

set_option maxHeartbeats 1000000

/-!
§4.2: Algorithm 2 (`prove`), and its correctness (Proposition 2) — it
decides `(n, L) ∈ Typing(G, S, strat)` without constructing the whole
typing, by recursively visiting only the portion of the dependency graph
reachable from `(n, L)`.

```
Input: n: node in G, L: label in L, Hyp: a stack over Nodes(G) × L
Output: true if n has label L, false otherwise
1  Hyp = Hyp.push((n, L));
2  Dep = ∅;
3  foreach (n', L') in dep(n, L) \ Hyp do
4    if prove(n', L', Hyp) then
5      Dep = Dep ∪ {(n', L')};
6  result = Dep ∪ Hyp, n ⊢ def(L);
7  Hyp = Hyp.pop();
8  return result;
```

where `dep(n, L)` is the set of node-type associations `(n', L')` such that
`n'` is a neighbor of `n` and `L'` appears as a shape reference in
`def(L)` (i.e. `L' ∈ posDeps(def(L)) ∪ negDeps(def(L))`).

This file first strengthens `Satisfies.agree`/`Matches.agree`
(`ShexLean/Proposition1.lean`) to a *neighbor-local* form: `⊢`/`⊨` at node
`n` depend on `typing` only through its restriction to `dep(n, L)`
(actual graph-neighbors of `n`, not every node) — the fact that lets
`prove` get away with tracking `Dep`/`Hyp` instead of a whole typing.
-/

namespace ShexLean

/-- The nodes appearing as the object of some triple in `N`. -/
def objsOf (N : Finset Triple) : Finset RDFNode := N.image Triple.obj

theorem objsOf_mono {N N' : Finset Triple} (h : N ⊆ N') : objsOf N ⊆ objsOf N' :=
  Finset.image_subset_image h

theorem mem_objsOf_singleton {t : Triple} : t.obj ∈ objsOf ({t} : Finset Triple) := by
  simp [objsOf]

/-- Each piece of a `DisjointUnionList` decomposition is a subset of the
whole — needed to know that node-type associations relevant to a
sub-expression `Ni` (Rule te-repet) are still confined to `objsOf N`. -/
theorem subset_of_mem_disjointUnionList {N : Finset Triple} {Ns : List (Finset Triple)}
    (h : DisjointUnionList N Ns) {Ni : Finset Triple} (hNi : Ni ∈ Ns) : Ni ⊆ N := by
  rw [h.2]
  clear h
  induction Ns with
  | nil => simp at hNi
  | cons N0 Ns ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hNi with rfl | hNi'
      · exact Finset.subset_union_left
      · exact (ih hNi').trans Finset.subset_union_right

/-- Neighbor-local agreement for `⊨`: if `typing` and `typing'` agree on
every `(n', L)` with `n'` an object of some triple in `N` and `L`
referenced by `E`, then `⊨` for `N` and `E` agrees between them. Stated
with `N`/`E` as ordinary parameters (not matched via top-level equation
clauses) and proved by a tactic-mode `match`, since the equation-compiler
chokes on a clause list mixing a plain-typed argument (`N`) with one whose
type it appears in (`hagree`) ahead of the recursed argument. -/
theorem Matches.agreeLocal {G : Graph} {typing typing' : Typing} (N : Finset Triple)
    (E : TripleExpr)
    (hagree : ∀ n' L, n' ∈ objsOf N → L ∈ E.posDeps ∪ E.negDeps →
      ((n', L) ∈ typing ↔ (n', L) ∈ typing')) :
    Matches G typing N E ↔ Matches G typing' N E := by
  match E, hagree with
  | .tPattern P L, hagree =>
      have hL : L ∈ (TripleExpr.tPattern P L).posDeps ∪ (TripleExpr.tPattern P L).negDeps := by
        simp [TripleExpr.posDeps, TripleExpr.negDeps, TripleExpr.depsAux]
      constructor
      · rintro ⟨subj, pred, obj, hN, hP, htyp⟩
        have hobj : obj ∈ objsOf N := hN ▸ mem_objsOf_singleton
        exact ⟨subj, pred, obj, hN, hP, (hagree obj L hobj hL).mp htyp⟩
      · rintro ⟨subj, pred, obj, hN, hP, htyp⟩
        have hobj : obj ∈ objsOf N := hN ▸ mem_objsOf_singleton
        exact ⟨subj, pred, obj, hN, hP, (hagree obj L hobj hL).mpr htyp⟩
  | .empty, _ => exact Iff.rfl
  | .someOf E1 E2, hagree =>
      have h1 := Matches.agreeLocal (G := G) N E1 (fun n' L hn' hL => hagree n' L hn' (by
        simp only [TripleExpr.posDeps, TripleExpr.negDeps, Finset.mem_union] at hL ⊢
        tauto))
      have h2 := Matches.agreeLocal (G := G) N E2 (fun n' L hn' hL => hagree n' L hn' (by
        simp only [TripleExpr.posDeps, TripleExpr.negDeps, Finset.mem_union] at hL ⊢
        tauto))
      exact or_congr h1 h2
  | .eachOf E1 E2, hagree =>
      have hN1 : ∀ N1 N2 : Finset Triple, DisjointUnion N N1 N2 → N1 ⊆ N := by
        rintro N1 N2 ⟨-, rfl⟩; exact Finset.subset_union_left
      have hN2 : ∀ N1 N2 : Finset Triple, DisjointUnion N N1 N2 → N2 ⊆ N := by
        rintro N1 N2 ⟨-, rfl⟩; exact Finset.subset_union_right
      constructor
      · rintro ⟨N1, N2, hdu, h1, h2⟩
        have a1 := Matches.agreeLocal (G := G) N1 E1 (fun n' L hn' hL =>
          hagree n' L (objsOf_mono (hN1 N1 N2 hdu) hn') (by
            simp only [TripleExpr.posDeps, TripleExpr.negDeps, Finset.mem_union] at hL ⊢
            tauto))
        have a2 := Matches.agreeLocal (G := G) N2 E2 (fun n' L hn' hL =>
          hagree n' L (objsOf_mono (hN2 N1 N2 hdu) hn') (by
            simp only [TripleExpr.posDeps, TripleExpr.negDeps, Finset.mem_union] at hL ⊢
            tauto))
        exact ⟨N1, N2, hdu, a1.mp h1, a2.mp h2⟩
      · rintro ⟨N1, N2, hdu, h1, h2⟩
        have a1 := Matches.agreeLocal (G := G) N1 E1 (fun n' L hn' hL =>
          hagree n' L (objsOf_mono (hN1 N1 N2 hdu) hn') (by
            simp only [TripleExpr.posDeps, TripleExpr.negDeps, Finset.mem_union] at hL ⊢
            tauto))
        have a2 := Matches.agreeLocal (G := G) N2 E2 (fun n' L hn' hL =>
          hagree n' L (objsOf_mono (hN2 N1 N2 hdu) hn') (by
            simp only [TripleExpr.posDeps, TripleExpr.negDeps, Finset.mem_union] at hL ⊢
            tauto))
        exact ⟨N1, N2, hdu, a1.mpr h1, a2.mpr h2⟩
  | .rep E _ _, hagree =>
      constructor
      · rintro ⟨Ns, hdu, hmin, hmax, hall⟩
        refine ⟨Ns, hdu, hmin, hmax, fun Ni hNi => ?_⟩
        have hsub : Ni ⊆ N := subset_of_mem_disjointUnionList hdu hNi
        exact (Matches.agreeLocal (G := G) Ni E
          (fun n' L hn' hL => hagree n' L (objsOf_mono hsub hn') hL)).mp (hall Ni hNi)
      · rintro ⟨Ns, hdu, hmin, hmax, hall⟩
        refine ⟨Ns, hdu, hmin, hmax, fun Ni hNi => ?_⟩
        have hsub : Ni ⊆ N := subset_of_mem_disjointUnionList hdu hNi
        exact (Matches.agreeLocal (G := G) Ni E
          (fun n' L hn' hL => hagree n' L (objsOf_mono hsub hn') hL)).mpr (hall Ni hNi)

/-- Neighbor-local agreement for `⊢`: if `typing` and `typing'` agree on
every `(n', L)` with `n'` an actual graph-neighbor of `n` and `L` referenced
by `S`, then `⊢` for `n` and `S` agrees between them. Strictly finer than
`Satisfies.agree` (which needs agreement at *every* node, not just `n`'s
neighbors) — the fact Algorithm 2 exploits to only ever look at
`dep(n, L)`. -/
theorem Satisfies.agreeLocal {G : Graph} {typing typing' : Typing} (n : RDFNode) (S : ShapeExpr)
    (hagree : ∀ n' L, n' ∈ objsOf (neigh G n) → L ∈ S.posDeps ∪ S.negDeps →
      ((n', L) ∈ typing ↔ (n', L) ∈ typing')) :
    Satisfies G typing n S ↔ Satisfies G typing' n S := by
  match S, hagree with
  | .valueDescr V, _ => exact Iff.rfl
  | .neigDescr E, hagree => exact Matches.agreeLocal (G := G) (neigh G n) E hagree
  | .and S1 S2, hagree =>
      have h1 := Satisfies.agreeLocal (G := G) n S1 (fun n' L hn' hL => hagree n' L hn' (by
        simp only [ShapeExpr.posDeps, ShapeExpr.negDeps, Finset.mem_union] at hL ⊢
        tauto))
      have h2 := Satisfies.agreeLocal (G := G) n S2 (fun n' L hn' hL => hagree n' L hn' (by
        simp only [ShapeExpr.posDeps, ShapeExpr.negDeps, Finset.mem_union] at hL ⊢
        tauto))
      exact and_congr h1 h2
  | .or S1 S2, hagree =>
      have h1 := Satisfies.agreeLocal (G := G) n S1 (fun n' L hn' hL => hagree n' L hn' (by
        simp only [ShapeExpr.posDeps, ShapeExpr.negDeps, Finset.mem_union] at hL ⊢
        tauto))
      have h2 := Satisfies.agreeLocal (G := G) n S2 (fun n' L hn' hL => hagree n' L hn' (by
        simp only [ShapeExpr.posDeps, ShapeExpr.negDeps, Finset.mem_union] at hL ⊢
        tauto))
      exact or_congr h1 h2
  | .not S, hagree =>
      have h := Satisfies.agreeLocal (G := G) n S (fun n' L hn' hL => hagree n' L hn' (by
        rw [ShapeExpr.not_posDeps, ShapeExpr.not_negDeps]
        simpa using hL))
      exact not_congr h

theorem Finset.mem_product_mono {α β : Type*} [DecidableEq α] [DecidableEq β]
    {Ns Ns' : Finset α} {A B : Finset β} (hNs : Ns ⊆ Ns') (hAB : A ⊆ B) {p : α × β}
    (hp : p ∈ Ns ×ˢ A) : p ∈ Ns' ×ˢ B :=
  Finset.mem_product.mpr ⟨hNs (Finset.mem_product.mp hp).1, hAB (Finset.mem_product.mp hp).2⟩

theorem Finset.mem_product_mono_right {α β : Type*} [DecidableEq α] [DecidableEq β]
    {Ns : Finset α} {A B : Finset β} (hAB : A ⊆ B) {p : α × β} (hp : p ∈ Ns ×ˢ A) :
    p ∈ Ns ×ˢ B :=
  Finset.mem_product_mono (Finset.Subset.refl Ns) hAB hp

/-- Neighbor-local, mixed (`⊆`/exact) monotonicity for `⊨`: growing
`typing ⊆ typing'` transports `⊨` for `E`, provided they agree *exactly* on
`E`'s negative dependencies — both restricted to `objsOf N`. Combines
`Matches.stratMono` (Proposition1.lean) with the neighbor-locality of
`Matches.agreeLocal` above. -/
theorem Matches.stratMonoLocal {G : Graph} {typing typing' : Typing} (N : Finset Triple)
    (E : TripleExpr)
    (hsub : ∀ p ∈ objsOf N ×ˢ E.posDeps, p ∈ typing → p ∈ typing')
    (hagree : ∀ p ∈ objsOf N ×ˢ E.negDeps, (p ∈ typing ↔ p ∈ typing')) :
    Matches G typing N E → Matches G typing' N E := by
  match E, hsub, hagree with
  | .tPattern P L, hsub, _ =>
      rintro ⟨subj, pred, obj, hN, hP, htyp⟩
      have hLpos : L ∈ (TripleExpr.tPattern P L).posDeps := by
        simp [TripleExpr.posDeps, TripleExpr.depsAux]
      have hobj : obj ∈ objsOf N := hN ▸ mem_objsOf_singleton
      exact ⟨subj, pred, obj, hN, hP, hsub (obj, L) (Finset.mem_product.mpr ⟨hobj, hLpos⟩) htyp⟩
  | .empty, _, _ => exact id
  | .someOf E1 E2, hsub, hagree =>
      have h1 := Matches.stratMonoLocal (G := G) N E1
        (fun p hp => hsub p (Finset.mem_product_mono_right Finset.subset_union_left hp))
        (fun p hp => hagree p (Finset.mem_product_mono_right Finset.subset_union_left hp))
      have h2 := Matches.stratMonoLocal (G := G) N E2
        (fun p hp => hsub p (Finset.mem_product_mono_right Finset.subset_union_right hp))
        (fun p hp => hagree p (Finset.mem_product_mono_right Finset.subset_union_right hp))
      exact fun h => h.imp h1 h2
  | .eachOf E1 E2, hsub, hagree =>
      have hN1 : ∀ N1 N2 : Finset Triple, DisjointUnion N N1 N2 → N1 ⊆ N := by
        rintro N1 N2 ⟨-, rfl⟩; exact Finset.subset_union_left
      have hN2 : ∀ N1 N2 : Finset Triple, DisjointUnion N N1 N2 → N2 ⊆ N := by
        rintro N1 N2 ⟨-, rfl⟩; exact Finset.subset_union_right
      rintro ⟨N1, N2, hdu, hm1, hm2⟩
      have h1 := Matches.stratMonoLocal (G := G) N1 E1
        (fun p hp => hsub p (Finset.mem_product_mono (objsOf_mono (hN1 N1 N2 hdu))
          Finset.subset_union_left hp))
        (fun p hp => hagree p (Finset.mem_product_mono (objsOf_mono (hN1 N1 N2 hdu))
          Finset.subset_union_left hp))
      have h2 := Matches.stratMonoLocal (G := G) N2 E2
        (fun p hp => hsub p (Finset.mem_product_mono (objsOf_mono (hN2 N1 N2 hdu))
          Finset.subset_union_right hp))
        (fun p hp => hagree p (Finset.mem_product_mono (objsOf_mono (hN2 N1 N2 hdu))
          Finset.subset_union_right hp))
      exact ⟨N1, N2, hdu, h1 hm1, h2 hm2⟩
  | .rep E _ _, hsub, hagree =>
      rintro ⟨Ns, hdu, hmin, hmax, hall⟩
      refine ⟨Ns, hdu, hmin, hmax, fun Ni hNi => ?_⟩
      have hsubNi : Ni ⊆ N := subset_of_mem_disjointUnionList hdu hNi
      have h1 := Matches.stratMonoLocal (G := G) Ni E
        (fun p hp => hsub p (Finset.mem_product_mono (objsOf_mono hsubNi)
          (Finset.Subset.refl _) hp))
        (fun p hp => hagree p (Finset.mem_product_mono (objsOf_mono hsubNi)
          (Finset.Subset.refl _) hp))
      exact h1 (hall Ni hNi)

/-- Neighbor-local, mixed monotonicity for `⊢`: same as `Satisfies.stratMono`
(Proposition1.lean), but agreement need only hold on `n`'s actual
graph-neighbors rather than every node. -/
theorem Satisfies.stratMonoLocal {G : Graph} {typing typing' : Typing} (n : RDFNode)
    (S : ShapeExpr)
    (hsub : ∀ p ∈ objsOf (neigh G n) ×ˢ S.posDeps, p ∈ typing → p ∈ typing')
    (hagree : ∀ p ∈ objsOf (neigh G n) ×ˢ S.negDeps, (p ∈ typing ↔ p ∈ typing')) :
    Satisfies G typing n S → Satisfies G typing' n S := by
  match S, hsub, hagree with
  | .valueDescr _, _, _ => exact id
  | .neigDescr E, hsub, hagree => exact Matches.stratMonoLocal (G := G) (neigh G n) E hsub hagree
  | .and S1 S2, hsub, hagree =>
      have h1 := Satisfies.stratMonoLocal (G := G) n S1
        (fun p hp => hsub p (Finset.mem_product_mono_right Finset.subset_union_left hp))
        (fun p hp => hagree p (Finset.mem_product_mono_right Finset.subset_union_left hp))
      have h2 := Satisfies.stratMonoLocal (G := G) n S2
        (fun p hp => hsub p (Finset.mem_product_mono_right Finset.subset_union_right hp))
        (fun p hp => hagree p (Finset.mem_product_mono_right Finset.subset_union_right hp))
      exact fun ⟨ha, hb⟩ => ⟨h1 ha, h2 hb⟩
  | .or S1 S2, hsub, hagree =>
      have h1 := Satisfies.stratMonoLocal (G := G) n S1
        (fun p hp => hsub p (Finset.mem_product_mono_right Finset.subset_union_left hp))
        (fun p hp => hagree p (Finset.mem_product_mono_right Finset.subset_union_left hp))
      have h2 := Satisfies.stratMonoLocal (G := G) n S2
        (fun p hp => hsub p (Finset.mem_product_mono_right Finset.subset_union_right hp))
        (fun p hp => hagree p (Finset.mem_product_mono_right Finset.subset_union_right hp))
      exact fun h => h.imp h1 h2
  | .not S, hsub, hagree =>
      have hagree' : ∀ n' L, n' ∈ objsOf (neigh G n) → L ∈ S.posDeps ∪ S.negDeps →
          ((n', L) ∈ typing ↔ (n', L) ∈ typing') := by
        intro n' L hn' hL
        have hL' : L ∈ (ShapeExpr.not S).negDeps := by
          rw [ShapeExpr.not_negDeps]; exact hL
        exact hagree (n', L) (Finset.mem_product.mpr ⟨hn', hL'⟩)
      have h := Satisfies.agreeLocal (G := G) n S hagree'
      exact fun hc hcs => hc (h.mpr hcs)

/-- `dep(n, L)`: the node-type associations `(n', L')` such that `n'` is a
graph-neighbor of `n` and `L'` is referenced (positively or negatively) by
`def(L)`. -/
def depSet (S : Schema) (G : Graph) (n : RDFNode) (L : ShapeLabel) : Finset NodeTypeAssoc :=
  objsOf (neigh G n) ×ˢ ((S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps)

theorem mem_depSet {S : Schema} {G : Graph} {n : RDFNode} {L : ShapeLabel} {p : NodeTypeAssoc} :
    p ∈ depSet S G n L ↔
      p.1 ∈ objsOf (neigh G n) ∧ p.2 ∈ (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps :=
  Finset.mem_product

/-- The neighbor-local agreement fact Algorithm 2 relies on: `⊢` for `def(L)`
at `n` depends on `typing` only through `typing`'s restriction to
`depSet S G n L`. -/
theorem Satisfies.agree_depSet {S : Schema} {G : Graph} {n : RDFNode} {L : ShapeLabel}
    {typing typing' : Typing}
    (hagree : ∀ p ∈ depSet S G n L, (p ∈ typing ↔ p ∈ typing')) :
    Satisfies G typing n (S.shapeDef L) ↔ Satisfies G typing' n (S.shapeDef L) :=
  Satisfies.agreeLocal (G := G) n (S.shapeDef L)
    (fun n' L' hn' hL' => hagree (n', L') (mem_depSet.mpr ⟨hn', hL'⟩))

/-- The mixed (`⊆`/exact) analogue of `Satisfies.agree_depSet`: `⊢` for
`def(L)` at `n` transports from `typing` to a superset `typing'`, provided
they agree exactly on `depSet S G n L`'s *negatively*-referenced part. -/
theorem Satisfies.stratMono_depSet {S : Schema} {G : Graph} {n : RDFNode} {L : ShapeLabel}
    {typing typing' : Typing}
    (hsub : ∀ p ∈ objsOf (neigh G n) ×ˢ (S.shapeDef L).posDeps, p ∈ typing → p ∈ typing')
    (hagree : ∀ p ∈ objsOf (neigh G n) ×ˢ (S.shapeDef L).negDeps, (p ∈ typing ↔ p ∈ typing')) :
    Satisfies G typing n (S.shapeDef L) → Satisfies G typing' n (S.shapeDef L) :=
  Satisfies.stratMonoLocal (G := G) n (S.shapeDef L) hsub hagree

theorem objsOf_neigh_subset_nodes (G : Graph) (n : RDFNode) : objsOf (neigh G n) ⊆ G.nodes := by
  intro n' hn'
  simp only [objsOf, Finset.mem_image] at hn'
  obtain ⟨t, ht, rfl⟩ := hn'
  have htG : t ∈ G := (Finset.mem_filter.mp ht).1
  simp only [Graph.nodes, Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨t, htG, rfl⟩)

/-- `depSet S G n L` stays within `G.nodes ×ˢ S.stratum strat.strat (strat.strat L)` —
neighbors of `n` are graph nodes, and `def(L)`'s references are confined to
`L`'s own stratum-checkpoint (`Schema.stratum_self_contained`). -/
theorem depSet_subset_stratum {S : Schema} (strat : Stratification S) (hClosed : S.Closed)
    {G : Graph} {n : RDFNode} {L : ShapeLabel} (hL : L ∈ S.labels) :
    depSet S G n L ⊆ G.nodes ×ˢ S.stratum strat.strat (strat.strat L) := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := mem_depSet.mp hp
  refine Finset.mem_product.mpr ⟨objsOf_neigh_subset_nodes G n hp1, ?_⟩
  exact Schema.stratum_self_contained S strat hClosed (strat.strat L) L
    (by simp only [Schema.stratum, Finset.mem_filter]; exact ⟨hL, le_refl _⟩) hp2

/-!
**Algorithm 2 itself.** `proveAux S G U n L Hyp` is the paper's `prove(n, L,
Hyp)`, with `Hyp` represented as a `Finset` (only membership ever matters —
the paper's "stack" discipline is exactly LIFO push/pop of a set, so no
information is lost) and `⊢` decided classically (`Satisfies` isn't
computable in general, matching how `Algorithm1.lean`'s `refineStep`
already handles this). `U` is a fixed finite superset of every `(n, L)`
pair the recursion can ever reach — termination measures how much of `U`
is still outside `Hyp`.
-/

/-- `dep(n, L)` intersected with the fixed universe `U`: guarantees every
recursive call stays within `U`, regardless of what `U` is, so termination
doesn't need to separately re-derive "`depSet` stays inside `U`" from
closedness at each step. -/
noncomputable def proveAux (S : Schema) (G : Graph) (U : Finset NodeTypeAssoc) :
    RDFNode → ShapeLabel → Finset NodeTypeAssoc → Bool
  | n, L, Hyp =>
    if (n, L) ∈ Hyp then true
    else if (n, L) ∉ U then false
    else
      let Hyp' := insert (n, L) Hyp
      let cand := (depSet S G n L ∩ U) \ Hyp'
      let Dep := cand.filter (fun p => proveAux S G U p.1 p.2 Hyp' = true)
      haveI := Classical.propDecidable (Satisfies G (Dep ∪ Hyp') n (S.shapeDef L))
      decide (Satisfies G (Dep ∪ Hyp') n (S.shapeDef L))
  termination_by _n _L Hyp => (U \ Hyp).card
  decreasing_by
    all_goals (
      rename_i h1 h2
      simp only [not_not] at h2
      have hmem : (n, L) ∈ U \ Hyp := Finset.mem_sdiff.mpr ⟨h2, h1⟩
      have heq : U \ insert (n, L) Hyp = (U \ Hyp).erase (n, L) := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      rw [heq]
      exact Finset.card_erase_lt_of_mem hmem
    )

/-- `prove(n, L, [])`: Algorithm 2 run from an empty hypothesis stack. The
universe `G.nodes ×ˢ S.labels` is exactly `Typing4`'s own universe
(`Schema.univTyping`) — if `n ∉ G.nodes`, `proveAux`'s own "outside `U`"
base case correctly returns `false`, matching `(n, L) ∉ Typing4` (which
always holds automatically for `n ∉ G.nodes`, since every correct typing
is `⊆ G.nodes ×ˢ S.labels`), so no special-casing of "foreign" `n` is
needed here. -/
noncomputable def prove (S : Schema) (G : Graph) (n : RDFNode) (L : ShapeLabel) : Bool :=
  proveAux S G (G.nodes ×ˢ S.labels) n L ∅

/-- `Dep`, named: the node-type associations `proveAux` (lines 3–5, 9–11)
confirms while processing `(n, L)` with `Hyp` already pushed. Naming it
keeps later statements from re-stating this filter expression verbatim
(which makes some `simp`/`rw` calls time out on elaboration). -/
noncomputable def proveDep (S : Schema) (G : Graph) (U : Finset NodeTypeAssoc) (n : RDFNode)
    (L : ShapeLabel) (Hyp : Finset NodeTypeAssoc) : Finset NodeTypeAssoc :=
  ((depSet S G n L ∩ U) \ insert (n, L) Hyp).filter
    (fun p => proveAux S G U p.1 p.2 (insert (n, L) Hyp) = true)

/-- Unfolding `proveAux` one step, in the base case: an already-trusted
pair is immediately `true`. -/
theorem proveAux_of_mem {S : Schema} {G : Graph} {U : Finset NodeTypeAssoc} {n : RDFNode}
    {L : ShapeLabel} {Hyp : Finset NodeTypeAssoc} (h : (n, L) ∈ Hyp) :
    proveAux S G U n L Hyp = true := by
  rw [proveAux.eq_1]; simp [h]

/-- Unfolding `proveAux` one step, in the recursive case — via the
auto-generated `proveAux.eq_1` and `simp` rather than `unfold` (`unfold`
recurses into the nested `proveAux` occurrence inside `Dep`'s filter too,
introducing a second, syntactically-distinct `Classical.propDecidable`
instance that later tactics can't see through; `rw` with the one-step
equation lemma only touches the outermost occurrence). -/
theorem proveAux_unfold {S : Schema} {G : Graph} {U : Finset NodeTypeAssoc} {n : RDFNode}
    {L : ShapeLabel} {Hyp : Finset NodeTypeAssoc} (h1 : (n, L) ∉ Hyp) (h2 : (n, L) ∈ U) :
    proveAux S G U n L Hyp = true ↔
      Satisfies G (proveDep S G U n L Hyp ∪ insert (n, L) Hyp) n (S.shapeDef L) := by
  rw [proveAux.eq_1]
  simp only [h1, h2, if_neg, not_false_eq_true, not_true_eq_false, decide_eq_true_eq, proveDep]

/-- The set of node-type associations `proveAux` commits to while
computing `proveAux S G U n L Hyp` — `{(n, L)}` plus every `Dep`-confirmed
descendant, transitively. Mirrors `proveAux`'s own recursive structure and
termination measure exactly; used only to build a witness typing for the
soundness half of Proposition 2 below. -/
noncomputable def proveSupport (S : Schema) (G : Graph) (U : Finset NodeTypeAssoc) :
    RDFNode → ShapeLabel → Finset NodeTypeAssoc → Finset NodeTypeAssoc
  | n, L, Hyp =>
    if (n, L) ∈ Hyp then ∅
    else if (n, L) ∉ U then ∅
    else
      let Dep := proveDep S G U n L Hyp
      insert (n, L) (Dep ∪ Dep.biUnion (fun p => proveSupport S G U p.1 p.2 (insert (n, L) Hyp)))
  termination_by _n _L Hyp => (U \ Hyp).card
  decreasing_by
    all_goals (
      rename_i h1 h2
      simp only [not_not] at h2
      have hmem : (n, L) ∈ U \ Hyp := Finset.mem_sdiff.mpr ⟨h2, h1⟩
      have heq : U \ insert (n, L) Hyp = (U \ Hyp).erase (n, L) := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      rw [heq]
      exact Finset.card_erase_lt_of_mem hmem
    )

/-- Unfolding `proveSupport` one step (recursive case), matching
`proveAux_unfold`. -/
theorem proveSupport_unfold {S : Schema} {G : Graph} {U : Finset NodeTypeAssoc} {n : RDFNode}
    {L : ShapeLabel} {Hyp : Finset NodeTypeAssoc} (h1 : (n, L) ∉ Hyp) (h2 : (n, L) ∈ U) :
    proveSupport S G U n L Hyp =
      insert (n, L) (proveDep S G U n L Hyp ∪
        (proveDep S G U n L Hyp).biUnion (fun p => proveSupport S G U p.1 p.2 (insert (n, L) Hyp))) := by
  rw [proveSupport.eq_1]
  simp only [h1, h2, if_neg, not_false_eq_true, not_true_eq_false]

theorem proveSupport_of_mem {S : Schema} {G : Graph} {U : Finset NodeTypeAssoc} {n : RDFNode}
    {L : ShapeLabel} {Hyp : Finset NodeTypeAssoc} (h : (n, L) ∈ Hyp) :
    proveSupport S G U n L Hyp = ∅ := by
  rw [proveSupport.eq_1]; simp [h]

theorem proveSupport_of_not_mem_U {S : Schema} {G : Graph} {U : Finset NodeTypeAssoc} {n : RDFNode}
    {L : ShapeLabel} {Hyp : Finset NodeTypeAssoc} (h1 : (n, L) ∉ Hyp) (h2 : (n, L) ∉ U) :
    proveSupport S G U n L Hyp = ∅ := by
  rw [proveSupport.eq_1]; simp [h1, h2]

theorem mem_proveSupport_self {S : Schema} {G : Graph} {U : Finset NodeTypeAssoc} {n : RDFNode}
    {L : ShapeLabel} {Hyp : Finset NodeTypeAssoc} (h1 : (n, L) ∉ Hyp) (h2 : (n, L) ∈ U) :
    (n, L) ∈ proveSupport S G U n L Hyp := by
  rw [proveSupport_unfold h1 h2]; exact Finset.mem_insert_self _ _

theorem dep_subset_proveSupport {S : Schema} {G : Graph} {U : Finset NodeTypeAssoc} {n : RDFNode}
    {L : ShapeLabel} {Hyp : Finset NodeTypeAssoc} (h1 : (n, L) ∉ Hyp) (h2 : (n, L) ∈ U) :
    proveDep S G U n L Hyp ⊆ proveSupport S G U n L Hyp := by
  rw [proveSupport_unfold h1 h2]
  exact Finset.subset_union_left.trans (Finset.subset_insert _ _)

theorem proveSupport_subset_of_mem_dep {S : Schema} {G : Graph} {U : Finset NodeTypeAssoc}
    {n : RDFNode} {L : ShapeLabel} {Hyp : Finset NodeTypeAssoc} (h1 : (n, L) ∉ Hyp) (h2 : (n, L) ∈ U)
    {p : NodeTypeAssoc} (hp : p ∈ proveDep S G U n L Hyp) :
    proveSupport S G U p.1 p.2 (insert (n, L) Hyp) ⊆ proveSupport S G U n L Hyp := by
  rw [proveSupport_unfold h1 h2]
  refine Finset.Subset.trans ?_ (Finset.subset_insert _ _)
  exact Finset.Subset.trans
    (Finset.subset_biUnion_of_mem (fun p => proveSupport S G U p.1 p.2 (insert (n, L) Hyp)) hp)
    Finset.subset_union_right

/-- Every pair `proveAux`/`proveSupport` ever visits while processing
`(n, L)` has stratum `≤ strat.strat L` — `depSet`'s labels never exceed
the current label's own stratum (`Schema.stratum_self_contained`), and
this bound is preserved at every recursive depth. Purely structural: no
`outerIH` needed. -/
theorem proveSupport_stratum_le (S : Schema) (strat : Stratification S) (hClosed : S.Closed)
    (G : Graph) (U : Finset NodeTypeAssoc) :
    ∀ k : ℕ, ∀ Hyp : Finset NodeTypeAssoc, (U \ Hyp).card ≤ k →
      ∀ n L, L ∈ S.labels → n ∈ G.nodes → ∀ q ∈ proveSupport S G U n L Hyp,
        strat.strat q.2 ≤ strat.strat L ∧ q.2 ∈ S.labels ∧ q.1 ∈ G.nodes := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Hyp hk n L hLlabels hnnodes q hq
    by_cases hinHyp : (n, L) ∈ Hyp
    · rw [proveSupport_of_mem hinHyp] at hq; simp at hq
    by_cases hinU : (n, L) ∈ U
    · rw [proveSupport_unfold hinHyp hinU] at hq
      have hLstratum : L ∈ S.stratum strat.strat (strat.strat L) :=
        Finset.mem_filter.mpr ⟨hLlabels, le_refl _⟩
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion] at hq
      rcases hq with rfl | hqDep | ⟨p, hpDep, hqSup⟩
      · exact ⟨le_refl _, hLlabels, hnnodes⟩
      · obtain ⟨hqmem, -⟩ := Finset.mem_filter.mp hqDep
        obtain ⟨hqdepSet, -⟩ := Finset.mem_sdiff.mp hqmem
        obtain ⟨hqdepSet', -⟩ := Finset.mem_inter.mp hqdepSet
        obtain ⟨hq1, hq2⟩ := mem_depSet.mp hqdepSet'
        have hqfact := Finset.mem_filter.mp
          (Schema.stratum_self_contained S strat hClosed (strat.strat L) L hLstratum hq2)
        exact ⟨hqfact.2, hqfact.1, objsOf_neigh_subset_nodes G n hq1⟩
      · obtain ⟨hpmem, -⟩ := Finset.mem_filter.mp hpDep
        obtain ⟨hpdepSet, -⟩ := Finset.mem_sdiff.mp hpmem
        obtain ⟨hpdepSet', -⟩ := Finset.mem_inter.mp hpdepSet
        obtain ⟨hp1, hp2⟩ := mem_depSet.mp hpdepSet'
        have hpfact := Finset.mem_filter.mp
          (Schema.stratum_self_contained S strat hClosed (strat.strat L) L hLstratum hp2)
        have hple : strat.strat p.2 ≤ strat.strat L := hpfact.2
        have hpLabels : p.2 ∈ S.labels := hpfact.1
        have hpNodes : p.1 ∈ G.nodes := objsOf_neigh_subset_nodes G n hp1
        have hmemUHyp : (n, L) ∈ U \ Hyp := Finset.mem_sdiff.mpr ⟨hinU, hinHyp⟩
        have heqset : U \ insert (n, L) Hyp = (U \ Hyp).erase (n, L) := by
          ext r; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
        have hcard : (U \ insert (n, L) Hyp).card < k := by
          rw [heqset]; exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem hmemUHyp) hk
        have hres := ih (U \ insert (n, L) Hyp).card hcard (insert (n, L) Hyp) le_rfl p.1 p.2
          hpLabels hpNodes q hqSup
        exact ⟨hres.1.trans hple, hres.2⟩
    · rw [proveSupport_of_not_mem_U hinHyp hinU] at hq
      simp at hq

/-!
**Proposition 2: correctness of `prove`.** This is the hard direction —
the paper's own proof sketch for Proposition 2 only covers termination,
not correctness. `prove` is a coinductive-style algorithm (it trusts an
ancestor on the call stack rather than re-deriving it), so relating it to
`Typing4` needs the stratification made explicit, even though `proveAux`
itself never consults `strat`.
-/

/-- `stratTypingSeq j`, restricted to an earlier stratum's labels
(`i ≤ j`), is exactly `stratTypingSeq i` — Definition 4's `typing_i` never
changes on labels already fixed by an earlier step. -/
theorem stratTypingSeq_restrictTo_stable (S : Schema) (strat : Stratification S)
    (hClosed : S.Closed) (G : Graph) {i j : ℕ} (hij : i ≤ j) :
    (stratTypingSeq S strat.strat G j).restrictTo (S.stratum strat.strat i) =
      stratTypingSeq S strat.strat G i := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  clear hij
  induction k with
  | zero =>
      have hsub : ∀ p ∈ stratTypingSeq S strat.strat G i, p.2 ∈ S.stratum strat.strat i := by
        intro p hp
        have hp' := (stratTypingSeq_correct S strat hClosed G i).1 hp
        simp only [Schema.univTyping, Schema.stratRestrict] at hp'
        exact (Finset.mem_product.mp hp').2
      apply Finset.ext
      rintro ⟨n, L⟩
      simp only [Typing.mem_restrictTo]
      exact ⟨fun h => h.1, fun h => ⟨h, hsub _ h⟩⟩
  | succ k ih =>
      have step : (stratTypingSeq S strat.strat G (i + k + 1)).restrictTo
          (S.stratum strat.strat (i + k)) = stratTypingSeq S strat.strat G (i + k) := by
        obtain ⟨hsub_ik, hcorrect_ik⟩ := stratTypingSeq_correct S strat hClosed G (i + k)
        have hsub_ik' : stratTypingSeq S strat.strat G (i + k) ⊆
            (S.stratRestrict strat.strat (i + k + 1)).univTyping G := by
          intro p hp
          have hp' := hsub_ik hp
          simp only [Schema.univTyping, Schema.stratRestrict] at hp' ⊢
          exact Finset.mem_product.mpr
            ⟨(Finset.mem_product.mp hp').1,
              Schema.stratum_mono (Nat.le_succ (i + k)) (Finset.mem_product.mp hp').2⟩
        have hnoop : (stratTypingSeq S strat.strat G (i + k)).restrictTo
            (S.stratum strat.strat (i + k)) = stratTypingSeq S strat.strat G (i + k) := by
          apply Finset.ext
          rintro ⟨n, L⟩
          simp only [Typing.mem_restrictTo]
          refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
          have hp' := hsub_ik h
          simp only [Schema.univTyping, Schema.stratRestrict] at hp'
          exact (Finset.mem_product.mp hp').2
        show (maxTypingAgreeing (S.stratRestrict strat.strat (i + k + 1)) G
          (S.stratum strat.strat (i + k)) (stratTypingSeq S strat.strat G (i + k))).restrictTo
          (S.stratum strat.strat (i + k)) = _
        rw [maxTypingAgreeing_restrictTo hsub_ik' hcorrect_ik, hnoop]
      have hsub : S.stratum strat.strat i ⊆ S.stratum strat.strat (i + k) :=
        Schema.stratum_mono (by omega)
      calc (stratTypingSeq S strat.strat G (i + k + 1)).restrictTo (S.stratum strat.strat i)
          = ((stratTypingSeq S strat.strat G (i + k + 1)).restrictTo
              (S.stratum strat.strat (i + k))).restrictTo (S.stratum strat.strat i) :=
            (Typing.restrictTo_restrictTo hsub).symm
        _ = (stratTypingSeq S strat.strat G (i + k)).restrictTo (S.stratum strat.strat i) := by
            rw [step]
        _ = stratTypingSeq S strat.strat G i := ih

/-- The statement to establish at stratum `i`: for any `Hyp` whose own
stratum-`≤ i` content is already known-correct, `proveAux` (run with that
`Hyp`, on any `L` at exactly stratum `i`) decides `Typing4`-membership
correctly. Named as a `Prop` so the two halves (`completeness_step`,
`soundness_step` below) can each take "this already holds at every smaller
stratum" as an explicit, reusable hypothesis. -/
def MainThmProp (S : Schema) (strat : Stratification S) (G : Graph) (U : Finset NodeTypeAssoc)
    (i : ℕ) : Prop :=
  ∀ Hyp : Finset NodeTypeAssoc,
    (∀ p ∈ Hyp, p.2 ∈ S.stratum strat.strat i → p ∈ stratTypingSeq S strat.strat G i) →
    ∀ n L, strat.strat L = i → L ∈ S.labels →
      (proveAux S G U n L Hyp = true ↔ (n, L) ∈ stratTypingSeq S strat.strat G i)

/-- **Completeness**, at a fixed stratum `i`: `(n, L) ∈ stratTypingSeq i` ⟹
`proveAux` confirms it. Proved by induction on the well-founded measure
alone (no circularity: the recursive step is *given* `(n, L) ∈
stratTypingSeq i`, so extending `Hyp` with it needs no further
justification) — using `outerIH` only for negative (strictly lower
stratum) dependencies, where `Hyp`'s stratum-`< i` part is always empty
(every pair pushed onto `Hyp` while processing stratum `i` is itself at
stratum `≥ i`, so it can never coincide with a stratum-`< i` target),
hence trivially satisfies `MainThmProp`'s own hypothesis at that lower
stratum. -/
theorem completeness_step (S : Schema) (strat : Stratification S) (hClosed : S.Closed) (G : Graph)
    (U : Finset NodeTypeAssoc) (hU : G.nodes ×ˢ S.labels ⊆ U) (i : ℕ)
    (outerIH : ∀ j < i, MainThmProp S strat G U j) :
    ∀ Hyp : Finset NodeTypeAssoc,
      (∀ p ∈ Hyp, p.2 ∈ S.stratum strat.strat i → p ∈ stratTypingSeq S strat.strat G i) →
      ∀ n L, strat.strat L = i → L ∈ S.labels → (n, L) ∈ stratTypingSeq S strat.strat G i →
      proveAux S G U n L Hyp = true := by
  have key : ∀ k : ℕ, ∀ Hyp : Finset NodeTypeAssoc, (U \ Hyp).card ≤ k →
      (∀ p ∈ Hyp, p.2 ∈ S.stratum strat.strat i → p ∈ stratTypingSeq S strat.strat G i) →
      ∀ n L, strat.strat L = i → L ∈ S.labels → (n, L) ∈ stratTypingSeq S strat.strat G i →
      proveAux S G U n L Hyp = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k innerIH =>
      intro Hyp hk hHyp n L hLi hLlabels hmem
      by_cases hinHyp : (n, L) ∈ Hyp
      · exact proveAux_of_mem hinHyp
      have hLstratum : L ∈ S.stratum strat.strat i := by
        simp only [Schema.stratum, Finset.mem_filter]; exact ⟨hLlabels, hLi.le⟩
      have hLU : (n, L) ∈ U := by
        apply hU
        have h' := (stratTypingSeq_correct S strat hClosed G i).1 hmem
        simp only [Schema.univTyping, Schema.stratRestrict] at h'
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp h').1, hLlabels⟩
      have hSat : Satisfies G (stratTypingSeq S strat.strat G i) n (S.shapeDef L) :=
        (stratTypingSeq_correct S strat hClosed G i).2 n L hmem
      -- Any dep target of L already in `stratTypingSeq i` is confirmed by
      -- `proveAux`: same-stratum targets via `innerIH` (measure strictly
      -- decreases), strictly-lower-stratum ones via `outerIH` (stability
      -- carries `hHyp`'s invariant down to that stratum for free).
      have hrec : ∀ n' L', L' ∈ (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps →
          n' ∈ objsOf (neigh G n) → (n', L') ∈ stratTypingSeq S strat.strat G i →
          proveAux S G U n' L' (insert (n, L) Hyp) = true := by
        intro n' L' hL'deps hn' hp'mem
        have hL'stratumL : L' ∈ S.stratum strat.strat i :=
          Schema.stratum_self_contained S strat hClosed i L
            (by simp only [Schema.stratum, Finset.mem_filter]; exact ⟨hLlabels, hLi.le⟩) hL'deps
        have hL'labels : L' ∈ S.labels := (Finset.mem_filter.mp hL'stratumL).1
        have hL'le : strat.strat L' ≤ i := (Finset.mem_filter.mp hL'stratumL).2
        by_cases hp'Hyp : (n', L') ∈ insert (n, L) Hyp
        · exact proveAux_of_mem hp'Hyp
        · rcases eq_or_lt_of_le hL'le with heq | hlt
          · have hmemUHyp : (n, L) ∈ U \ Hyp := Finset.mem_sdiff.mpr ⟨hLU, hinHyp⟩
            have heqset : U \ insert (n, L) Hyp = (U \ Hyp).erase (n, L) := by
              ext p; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
            have hcard : (U \ insert (n, L) Hyp).card < k := by
              rw [heqset]; exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem hmemUHyp) hk
            have hHyp' : ∀ p ∈ insert (n, L) Hyp, p.2 ∈ S.stratum strat.strat i →
                p ∈ stratTypingSeq S strat.strat G i := by
              intro p hp hp2
              rcases Finset.mem_insert.mp hp with rfl | hpHyp
              · exact hmem
              · exact hHyp p hpHyp hp2
            exact innerIH (U \ insert (n, L) Hyp).card hcard (insert (n, L) Hyp) le_rfl hHyp'
              n' L' heq hL'labels hp'mem
          · have hp'memj : (n', L') ∈ stratTypingSeq S strat.strat G (strat.strat L') := by
              rw [← stratTypingSeq_restrictTo_stable S strat hClosed G hlt.le]
              exact Typing.mem_restrictTo.mpr
                ⟨hp'mem, Finset.mem_filter.mpr ⟨hL'labels, le_refl _⟩⟩
            have hHypj : ∀ p ∈ insert (n, L) Hyp, p.2 ∈ S.stratum strat.strat (strat.strat L') →
                p ∈ stratTypingSeq S strat.strat G (strat.strat L') := by
              intro p hp hp2
              rcases Finset.mem_insert.mp hp with rfl | hpHyp
              · exact absurd hp2 (by
                  simp only [Schema.stratum, Finset.mem_filter]; omega)
              · have hp2i : p.2 ∈ S.stratum strat.strat i := by
                  simp only [Schema.stratum, Finset.mem_filter] at hp2 ⊢
                  exact ⟨hp2.1, hp2.2.trans hlt.le⟩
                rw [← stratTypingSeq_restrictTo_stable S strat hClosed G hlt.le]
                exact Typing.mem_restrictTo.mpr ⟨hHyp p hpHyp hp2i, hp2⟩
            exact ((outerIH (strat.strat L') hlt) (insert (n, L) Hyp) hHypj n' L' rfl
              hL'labels).mpr hp'memj
      have hn'U : ∀ n' L', L' ∈ (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps →
          n' ∈ objsOf (neigh G n) → (n', L') ∈ U := by
        intro n' L' hL'deps hn'
        exact hU (Finset.mem_product.mpr ⟨objsOf_neigh_subset_nodes G n hn',
          (Finset.mem_filter.mp (Schema.stratum_self_contained S strat hClosed i L
            (by simp only [Schema.stratum, Finset.mem_filter]; exact ⟨hLlabels, hLi.le⟩)
            hL'deps)).1⟩)
      rw [proveAux_unfold hinHyp hLU]
      refine Satisfies.stratMono_depSet ?_ ?_ hSat
      · rintro ⟨n', L'⟩ hp hpin
        simp only [Finset.mem_product] at hp
        obtain ⟨hn', hL'pos⟩ := hp
        have htrue := hrec n' L' (Finset.mem_union_left _ hL'pos) hn' hpin
        by_cases hp'Hyp : (n', L') ∈ insert (n, L) Hyp
        · exact Finset.mem_union_right _ hp'Hyp
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
            ⟨Finset.mem_inter.mpr ⟨mem_depSet.mpr ⟨hn', Finset.mem_union_left _ hL'pos⟩,
              hn'U n' L' (Finset.mem_union_left _ hL'pos) hn'⟩, hp'Hyp⟩, htrue⟩)
      · rintro ⟨n', L'⟩ hp
        simp only [Finset.mem_product] at hp
        obtain ⟨hn', hL'neg⟩ := hp
        have hL'lt : strat.strat L' < i := hLi ▸ strat.neg_strict L hLlabels L' hL'neg
        have hL'labels : L' ∈ S.labels :=
          (Finset.mem_filter.mp (Schema.stratum_self_contained S strat hClosed i L
            (by simp only [Schema.stratum, Finset.mem_filter]; exact ⟨hLlabels, hLi.le⟩)
            (Finset.mem_union_right _ hL'neg))).1
        by_cases hp'Hyp : (n', L') ∈ insert (n, L) Hyp
        · have hmemTyping : (n', L') ∈ stratTypingSeq S strat.strat G i := by
            rcases Finset.mem_insert.mp hp'Hyp with heq | hpHyp
            · exfalso
              have hLeq : L' = L := (Prod.ext_iff.mp heq).2
              rw [hLeq] at hL'lt
              omega
            · exact hHyp (n', L') hpHyp (Finset.mem_filter.mpr ⟨hL'labels, hL'lt.le⟩)
          exact ⟨fun _ => Finset.mem_union_right _ hp'Hyp, fun _ => hmemTyping⟩
        · constructor
          · intro htyp
            have htrue := hrec n' L' (Finset.mem_union_right _ hL'neg) hn' htyp
            exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
              ⟨Finset.mem_inter.mpr ⟨mem_depSet.mpr ⟨hn', Finset.mem_union_right _ hL'neg⟩,
                hn'U n' L' (Finset.mem_union_right _ hL'neg) hn'⟩, hp'Hyp⟩, htrue⟩)
          · intro hdep
            rcases Finset.mem_union.mp hdep with hd | hh
            · have hp'memj : (n', L') ∈ stratTypingSeq S strat.strat G (strat.strat L') := by
                have hHypj : ∀ p ∈ insert (n, L) Hyp, p.2 ∈ S.stratum strat.strat (strat.strat L') →
                    p ∈ stratTypingSeq S strat.strat G (strat.strat L') := by
                  intro p hp hp2
                  rcases Finset.mem_insert.mp hp with rfl | hpHyp
                  · exact absurd hp2 (by simp only [Schema.stratum, Finset.mem_filter]; omega)
                  · have hp2i : p.2 ∈ S.stratum strat.strat i := by
                      simp only [Schema.stratum, Finset.mem_filter] at hp2 ⊢
                      exact ⟨hp2.1, hp2.2.trans hL'lt.le⟩
                    rw [← stratTypingSeq_restrictTo_stable S strat hClosed G hL'lt.le]
                    exact Typing.mem_restrictTo.mpr ⟨hHyp p hpHyp hp2i, hp2⟩
                exact ((outerIH (strat.strat L') hL'lt) (insert (n, L) Hyp) hHypj n' L' rfl
                  hL'labels).mp (Finset.mem_filter.mp hd).2
              rw [← stratTypingSeq_restrictTo_stable S strat hClosed G hL'lt.le] at hp'memj
              exact (Typing.mem_restrictTo.mp hp'memj).1
            · exact absurd hh hp'Hyp
  exact fun Hyp hHyp n L hLi hLlabels hmem =>
    key (U \ Hyp).card Hyp le_rfl hHyp n L hLi hLlabels hmem

/-- **Soundness**, at a fixed stratum `i`: `proveAux` confirming `(n, L)`
implies `(n, L) ∈ stratTypingSeq i`. The hard direction — `proveAux` is a
coinductive-style algorithm (trusting an ancestor already on the call
stack, to allow positive cycles), so relating it to `Typing4`'s
greatest-fixed-point characterization needs a genuine witness:
`T := stratTypingSeq i ∪ (support of the whole computation, restricted to
same-stratum content)` is shown to be a correct, agreeing typing, hence
`⊆ stratTypingSeq i` via `subset_maxTypingAgreeing`; since `(n, L)` is in
the support, this gives the result. The device that avoids circularity
when a descendant's dependency chain loops back to `(n, L)` itself (a
genuine positive cycle): `T` is fixed *once* from the outermost call and
threaded unchanged through the recursion (`key`'s `T`/`hSTsubT`/`hTneg`
arguments, closed over before the well-founded induction on `k` even
starts) — an in-progress element's membership in `T` is always immediate
(structural, `⊆ T` by hypothesis), never needing its `Satisfies` fact to
be re-established first. -/
theorem soundness_step (S : Schema) (strat : Stratification S) (hClosed : S.Closed) (G : Graph)
    (U : Finset NodeTypeAssoc) (hU : U = G.nodes ×ˢ S.labels) (i : ℕ)
    (outerIH : ∀ j < i, MainThmProp S strat G U j) :
    ∀ Hyp : Finset NodeTypeAssoc,
      (∀ p ∈ Hyp, p.2 ∈ S.stratum strat.strat i → p ∈ stratTypingSeq S strat.strat G i) →
      ∀ n L, strat.strat L = i → L ∈ S.labels → proveAux S G U n L Hyp = true →
      (n, L) ∈ stratTypingSeq S strat.strat G i := by
  have key : ∀ (T : Typing), stratTypingSeq S strat.strat G i ⊆ T →
      (∀ p : NodeTypeAssoc, strat.strat p.2 < i →
        (p ∈ T ↔ p ∈ stratTypingSeq S strat.strat G i)) →
      ∀ k : ℕ, ∀ Hyp : Finset NodeTypeAssoc, (U \ Hyp).card ≤ k →
      (∀ p ∈ Hyp, p.2 ∈ S.stratum strat.strat i → p ∈ T) →
      ∀ n L, strat.strat L = i → L ∈ S.labels → n ∈ G.nodes → (n, L) ∉ Hyp → (n, L) ∈ U →
      proveAux S G U n L Hyp = true →
      (proveSupport S G U n L Hyp).filter (fun q => strat.strat q.2 = i) ⊆ T →
      ∀ q ∈ (proveSupport S G U n L Hyp).filter (fun q => strat.strat q.2 = i),
        Satisfies G T q.1 (S.shapeDef q.2) := by
    intro T hSTsubT hTneg k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro Hyp hk hHyp n L hLi hLlabels hnnodes hinHyp hinU htrue hWisubT q hqWi
      have hnLT : (n, L) ∈ T :=
        hWisubT (Finset.mem_filter.mpr ⟨mem_proveSupport_self hinHyp hinU, hLi⟩)
      have hLstratum : L ∈ S.stratum strat.strat i := Finset.mem_filter.mpr ⟨hLlabels, hLi.le⟩
      -- Any dep target of L confirmed true lands in `T` — either already
      -- known (`hHyp`/`hnLT`), freshly confirmed same-stratum (structural
      -- membership in `T` via `hWisubT`), or strictly-lower-stratum
      -- (`outerIH` + stability + `hTneg`, exactly as in `completeness_step`).
      have hrecT : ∀ n' L', L' ∈ (S.shapeDef L).posDeps ∪ (S.shapeDef L).negDeps →
          n' ∈ objsOf (neigh G n) → proveAux S G U n' L' (insert (n, L) Hyp) = true →
          (n', L') ∈ T := by
        intro n' L' hL'deps hn' hp'true
        have hL'stratumL : L' ∈ S.stratum strat.strat i :=
          Schema.stratum_self_contained S strat hClosed i L hLstratum hL'deps
        have hL'labels : L' ∈ S.labels := (Finset.mem_filter.mp hL'stratumL).1
        have hL'le : strat.strat L' ≤ i := (Finset.mem_filter.mp hL'stratumL).2
        by_cases hp'Hyp : (n', L') ∈ insert (n, L) Hyp
        · rcases Finset.mem_insert.mp hp'Hyp with heq | hpHyp
          · simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact hnLT
          · exact hHyp (n', L') hpHyp hL'stratumL
        · rcases eq_or_lt_of_le hL'le with heq | hlt
          · have hn'nodes : n' ∈ G.nodes := objsOf_neigh_subset_nodes G n hn'
            have hn'U : (n', L') ∈ U := hU ▸ Finset.mem_product.mpr ⟨hn'nodes, hL'labels⟩
            have hcand : (n', L') ∈ (depSet S G n L ∩ U) \ insert (n, L) Hyp :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr
                ⟨mem_depSet.mpr ⟨hn', hL'deps⟩, hn'U⟩, hp'Hyp⟩
            have hdep : (n', L') ∈ proveDep S G U n L Hyp := Finset.mem_filter.mpr ⟨hcand, hp'true⟩
            exact hWisubT (Finset.mem_filter.mpr
              ⟨dep_subset_proveSupport hinHyp hinU hdep, heq⟩)
          · have hHypj : ∀ p ∈ insert (n, L) Hyp, p.2 ∈ S.stratum strat.strat (strat.strat L') →
                p ∈ stratTypingSeq S strat.strat G (strat.strat L') := by
              intro p hp hp2
              rcases Finset.mem_insert.mp hp with rfl | hpHyp
              · exact absurd hp2 (by simp only [Schema.stratum, Finset.mem_filter]; omega)
              · have hp2lt : strat.strat p.2 < i := by
                  simp only [Schema.stratum, Finset.mem_filter] at hp2; omega
                have hp2i : p.2 ∈ S.stratum strat.strat i :=
                  Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp2).1, hp2lt.le⟩
                have hpST : p ∈ stratTypingSeq S strat.strat G i :=
                  (hTneg p hp2lt).mp (hHyp p hpHyp hp2i)
                rw [← stratTypingSeq_restrictTo_stable S strat hClosed G hlt.le]
                exact Typing.mem_restrictTo.mpr ⟨hpST, hp2⟩
            have hp'memj : (n', L') ∈ stratTypingSeq S strat.strat G (strat.strat L') :=
              ((outerIH (strat.strat L') hlt) (insert (n, L) Hyp) hHypj n' L' rfl
                hL'labels).mp hp'true
            have hp'memi : (n', L') ∈ stratTypingSeq S strat.strat G i := by
              rw [← stratTypingSeq_restrictTo_stable S strat hClosed G hlt.le] at hp'memj
              exact (Typing.mem_restrictTo.mp hp'memj).1
            exact hSTsubT hp'memi
      have handleP : ∀ p ∈ proveDep S G U n L Hyp,
          ∀ q' ∈ proveSupport S G U p.1 p.2 (insert (n, L) Hyp), strat.strat q'.2 = i →
          Satisfies G T q'.1 (S.shapeDef q'.2) := by
        intro p hpDep q' hq'Sup hq'i
        obtain ⟨hpcand, hptrue⟩ := Finset.mem_filter.mp hpDep
        obtain ⟨hpdepSet, hpnotHyp⟩ := Finset.mem_sdiff.mp hpcand
        obtain ⟨hpdepSet', hpU⟩ := Finset.mem_inter.mp hpdepSet
        obtain ⟨hp1, hp2⟩ := mem_depSet.mp hpdepSet'
        have hpLstratum : p.2 ∈ S.stratum strat.strat i :=
          Schema.stratum_self_contained S strat hClosed i L hLstratum hp2
        have hpLlabels : p.2 ∈ S.labels := (Finset.mem_filter.mp hpLstratum).1
        have hpnodes : p.1 ∈ G.nodes := objsOf_neigh_subset_nodes G n hp1
        have hp2le : strat.strat p.2 ≤ i := (Finset.mem_filter.mp hpLstratum).2
        have hp2eq : strat.strat p.2 = i := by
          by_contra hne
          have hp2lt : strat.strat p.2 < i := lt_of_le_of_ne hp2le hne
          have hbound := (proveSupport_stratum_le S strat hClosed G U
            (U \ insert (n, L) Hyp).card (insert (n, L) Hyp) le_rfl p.1 p.2 hpLlabels hpnodes
            q' hq'Sup).1
          omega
        have hmemUHyp : (n, L) ∈ U \ Hyp := Finset.mem_sdiff.mpr ⟨hinU, hinHyp⟩
        have heqset : U \ insert (n, L) Hyp = (U \ Hyp).erase (n, L) := by
          ext r; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
        have hcard : (U \ insert (n, L) Hyp).card < k := by
          rw [heqset]; exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem hmemUHyp) hk
        have hHyp' : ∀ r ∈ insert (n, L) Hyp, r.2 ∈ S.stratum strat.strat i → r ∈ T := by
          intro r hr hr2
          rcases Finset.mem_insert.mp hr with rfl | hrHyp
          · exact hnLT
          · exact hHyp r hrHyp hr2
        have hWisubT' : (proveSupport S G U p.1 p.2 (insert (n, L) Hyp)).filter
            (fun r => strat.strat r.2 = i) ⊆ T := by
          intro r hr
          obtain ⟨hrmem, hri⟩ := Finset.mem_filter.mp hr
          exact hWisubT (Finset.mem_filter.mpr
            ⟨proveSupport_subset_of_mem_dep hinHyp hinU hpDep hrmem, hri⟩)
        exact ih (U \ insert (n, L) Hyp).card hcard (insert (n, L) Hyp) le_rfl hHyp' p.1 p.2 hp2eq
          hpLlabels hpnodes hpnotHyp hpU hptrue hWisubT' q' (Finset.mem_filter.mpr ⟨hq'Sup, hq'i⟩)
      rw [proveAux_unfold hinHyp hinU] at htrue
      rw [proveSupport_unfold hinHyp hinU] at hqWi
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
        at hqWi
      obtain ⟨hqcase, hqi⟩ := hqWi
      rcases hqcase with rfl | hqDep | ⟨p, hpDep, hqSup⟩
      · refine Satisfies.stratMono_depSet ?_ ?_ htrue
        · rintro ⟨n', L'⟩ hp hpin
          simp only [Finset.mem_product] at hp
          rcases Finset.mem_union.mp hpin with hd | hh
          · exact hrecT n' L' (Finset.mem_union_left _ hp.2) hp.1 (Finset.mem_filter.mp hd).2
          · rcases Finset.mem_insert.mp hh with heq | hpHyp
            · simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact hnLT
            · exact hHyp (n', L') hpHyp
                (Schema.stratum_self_contained S strat hClosed i L hLstratum
                  (Finset.mem_union_left _ hp.2))
        · rintro ⟨n', L'⟩ hp
          simp only [Finset.mem_product] at hp
          obtain ⟨hn', hL'neg⟩ := hp
          have hL'lt : strat.strat L' < i := hLi ▸ strat.neg_strict L hLlabels L' hL'neg
          have hL'labels : L' ∈ S.labels :=
            (Finset.mem_filter.mp
              (Schema.stratum_self_contained S strat hClosed i L hLstratum
                (Finset.mem_union_right _ hL'neg))).1
          constructor
          · intro hmem
            rcases Finset.mem_union.mp hmem with hd | hh
            · exact hrecT n' L' (Finset.mem_union_right _ hL'neg) hn' (Finset.mem_filter.mp hd).2
            · rcases Finset.mem_insert.mp hh with heq | hpHyp
              · simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact hnLT
              · exact hHyp (n', L') hpHyp (Finset.mem_filter.mpr ⟨hL'labels, hL'lt.le⟩)
          · intro hT
            have hST : (n', L') ∈ stratTypingSeq S strat.strat G i := (hTneg (n', L') hL'lt).mp hT
            by_cases hp'Hyp : (n', L') ∈ insert (n, L) Hyp
            · exact Finset.mem_union_right _ hp'Hyp
            · have hp'memj : (n', L') ∈ stratTypingSeq S strat.strat G (strat.strat L') := by
                rw [← stratTypingSeq_restrictTo_stable S strat hClosed G hL'lt.le]
                exact Typing.mem_restrictTo.mpr
                  ⟨hST, Finset.mem_filter.mpr ⟨hL'labels, le_refl _⟩⟩
              have hHypj : ∀ p ∈ insert (n, L) Hyp, p.2 ∈ S.stratum strat.strat (strat.strat L') →
                  p ∈ stratTypingSeq S strat.strat G (strat.strat L') := by
                intro p hp hp2
                rcases Finset.mem_insert.mp hp with rfl | hpHyp
                · exact absurd hp2 (by simp only [Schema.stratum, Finset.mem_filter]; omega)
                · have hp2lt : strat.strat p.2 < i := by
                    simp only [Schema.stratum, Finset.mem_filter] at hp2; omega
                  have hp2i : p.2 ∈ S.stratum strat.strat i :=
                    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp2).1, hp2lt.le⟩
                  have hpST : p ∈ stratTypingSeq S strat.strat G i :=
                    (hTneg p hp2lt).mp (hHyp p hpHyp hp2i)
                  rw [← stratTypingSeq_restrictTo_stable S strat hClosed G hL'lt.le]
                  exact Typing.mem_restrictTo.mpr ⟨hpST, hp2⟩
              have htr : proveAux S G U n' L' (insert (n, L) Hyp) = true :=
                ((outerIH (strat.strat L') hL'lt) (insert (n, L) Hyp) hHypj n' L' rfl
                  hL'labels).mpr hp'memj
              have hn'U : (n', L') ∈ U :=
                hU ▸ Finset.mem_product.mpr ⟨objsOf_neigh_subset_nodes G n hn', hL'labels⟩
              exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
                ⟨Finset.mem_inter.mpr
                  ⟨mem_depSet.mpr ⟨hn', Finset.mem_union_right _ hL'neg⟩, hn'U⟩, hp'Hyp⟩, htr⟩)
      · obtain ⟨hqcand, hqtrue⟩ := Finset.mem_filter.mp hqDep
        obtain ⟨_, hqnotHyp'⟩ := Finset.mem_sdiff.mp hqcand
        obtain ⟨_, hqU⟩ := Finset.mem_inter.mp (Finset.mem_sdiff.mp hqcand).1
        exact handleP q hqDep q (mem_proveSupport_self hqnotHyp' hqU) hqi
      · exact handleP p hpDep q hqSup hqi
  intro Hyp hHyp n L hLi hLlabels htrue
  by_cases hinHyp : (n, L) ∈ Hyp
  · exact hHyp (n, L) hinHyp (Finset.mem_filter.mpr ⟨hLlabels, hLi.le⟩)
  by_cases hinU : (n, L) ∈ U
  · have hnnodes : n ∈ G.nodes := (Finset.mem_product.mp (hU ▸ hinU)).1
    set T0 := stratTypingSeq S strat.strat G i ∪
      (proveSupport S G U n L Hyp).filter (fun q => strat.strat q.2 = i) with hT0def
    have hSTsubT0 : stratTypingSeq S strat.strat G i ⊆ T0 := Finset.subset_union_left
    have hTneg0 : ∀ p : NodeTypeAssoc, strat.strat p.2 < i →
        (p ∈ T0 ↔ p ∈ stratTypingSeq S strat.strat G i) := by
      intro p hplt
      constructor
      · intro h
        rcases Finset.mem_union.mp h with h1 | h2
        · exact h1
        · exact absurd (Finset.mem_filter.mp h2).2 (by omega)
      · exact fun h => Finset.mem_union_left _ h
    have hWisubT0 : (proveSupport S G U n L Hyp).filter (fun q => strat.strat q.2 = i) ⊆ T0 :=
      Finset.subset_union_right
    have hmemT0 : (n, L) ∈ T0 :=
      hWisubT0 (Finset.mem_filter.mpr ⟨mem_proveSupport_self hinHyp hinU, hLi⟩)
    obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by
      have := strat.mem_range L hLlabels; omega⟩
    have hCorrect : (S.stratRestrict strat.strat i).CorrectTyping G T0 := by
      intro n' L' hmem'
      rcases Finset.mem_union.mp hmem' with hmemST | hmemWi
      · have hL'stratum : L' ∈ S.stratum strat.strat i := by
          have h' := (stratTypingSeq_correct S strat hClosed G i).1 hmemST
          simp only [Schema.univTyping, Schema.stratRestrict] at h'
          exact (Finset.mem_product.mp h').2
        have hL'labels : L' ∈ S.labels := (Finset.mem_filter.mp hL'stratum).1
        have hL'le : strat.strat L' ≤ i := (Finset.mem_filter.mp hL'stratum).2
        have hSat' := (stratTypingSeq_correct S strat hClosed G i).2 n' L' hmemST
        refine Satisfies.stratMono_depSet ?_ ?_ hSat'
        · exact fun p hp hpin => Finset.mem_union_left _ hpin
        · rintro ⟨n'', L''⟩ hp
          simp only [Finset.mem_product] at hp
          have hlt : strat.strat L'' < strat.strat L' := strat.neg_strict L' hL'labels L'' hp.2
          exact (hTneg0 (n'', L'') (lt_of_lt_of_le hlt hL'le)).symm
      · exact key T0 hSTsubT0 hTneg0 (U \ Hyp).card Hyp le_rfl
          (fun p hp hp2 => hSTsubT0 (hHyp p hp hp2)) n L hLi hLlabels hnnodes
          hinHyp hinU htrue hWisubT0 (n', L') hmemWi
    have hSubUniv : T0 ⊆ (S.stratRestrict strat.strat i).univTyping G := by
      intro p hp
      rcases Finset.mem_union.mp hp with h1 | h2
      · have := (stratTypingSeq_correct S strat hClosed G i).1 h1
        simpa only [Schema.univTyping, Schema.stratRestrict] using this
      · obtain ⟨hpmem, hpi⟩ := Finset.mem_filter.mp h2
        have hbound := proveSupport_stratum_le S strat hClosed G U (U \ Hyp).card Hyp le_rfl n L
          hLlabels hnnodes p hpmem
        simp only [Schema.univTyping, Schema.stratRestrict]
        refine Finset.mem_product.mpr ⟨hbound.2.2, ?_⟩
        simp only [Schema.stratum, Finset.mem_filter]
        exact ⟨hbound.2.1, hpi.le⟩
    have hj_le : j ≤ i := by omega
    have hAgree : T0.restrictTo (S.stratum strat.strat j) =
        (stratTypingSeq S strat.strat G j).restrictTo (S.stratum strat.strat j) := by
      have step1 : T0.restrictTo (S.stratum strat.strat j) =
          (stratTypingSeq S strat.strat G i).restrictTo (S.stratum strat.strat j) := by
        apply Finset.ext
        rintro ⟨n', L'⟩
        simp only [Typing.mem_restrictTo, hT0def, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h2, hL'j⟩
          · exact ⟨h1, hL'j⟩
          · exfalso
            have hi : strat.strat L' = i := (Finset.mem_filter.mp h2).2
            simp only [Schema.stratum, Finset.mem_filter] at hL'j
            omega
        · rintro ⟨h1, hL'j⟩
          exact ⟨Or.inl h1, hL'j⟩
      rw [step1, stratTypingSeq_restrictTo_stable S strat hClosed G hj_le]
      apply Finset.ext
      rintro ⟨n', L'⟩
      simp only [Typing.mem_restrictTo]
      constructor
      · intro h
        have hp' := (stratTypingSeq_correct S strat hClosed G j).1 h
        simp only [Schema.univTyping, Schema.stratRestrict] at hp'
        exact ⟨h, (Finset.mem_product.mp hp').2⟩
      · exact fun h => h.1
    have hival : stratTypingSeq S strat.strat G i =
        maxTypingAgreeing (S.stratRestrict strat.strat i) G (S.stratum strat.strat j)
          (stratTypingSeq S strat.strat G j) := by
      subst hj; rfl
    have hsub := subset_maxTypingAgreeing hSubUniv hCorrect hAgree
    rw [← hival] at hsub
    exact hsub hmemT0
  · exfalso
    rw [proveAux.eq_1] at htrue
    simp [hinHyp, hinU] at htrue

/-- Combines `completeness_step` and `soundness_step`, at every stratum,
into `MainThmProp` holding everywhere: `proveAux` correctly decides
`stratTypingSeq i`-membership at stratum `i`, for any `Hyp` whose own
stratum-`≤ i` content is already known-correct. -/
theorem mainThm (S : Schema) (strat : Stratification S) (hClosed : S.Closed) (G : Graph)
    (U : Finset NodeTypeAssoc) (hU : U = G.nodes ×ˢ S.labels) :
    ∀ i : ℕ, MainThmProp S strat G U i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i outerIH =>
    intro Hyp hHyp n L hLi hLlabels
    exact ⟨soundness_step S strat hClosed G U hU i outerIH Hyp hHyp n L hLi hLlabels,
      completeness_step S strat hClosed G U (le_of_eq hU.symm) i outerIH Hyp hHyp n L hLi
        hLlabels⟩

/-- **Proposition 2** (§4.2): Algorithm 2 (`prove`) really does decide
`Typing(G, S, strat)` (Definition 4) — the correctness the paper only
asserts (its own proof sketch covers termination only). -/
theorem prove_correct (S : Schema) (strat : Stratification S) (hClosed : S.Closed) (G : Graph)
    (n : RDFNode) (L : ShapeLabel) (hLlabels : L ∈ S.labels) :
    prove S G n L = true ↔ (n, L) ∈ Typing4 G S strat := by
  have hmain := mainThm S strat hClosed G (G.nodes ×ˢ S.labels) rfl (strat.strat L) ∅ (by simp)
    n L rfl hLlabels
  have hstable := stratTypingSeq_restrictTo_stable S strat hClosed G (strat.mem_range L hLlabels).2
  show proveAux S G (G.nodes ×ˢ S.labels) n L ∅ = true ↔ (n, L) ∈ Typing4 G S strat
  rw [hmain]
  show (n, L) ∈ stratTypingSeq S strat.strat G (strat.strat L) ↔
    (n, L) ∈ stratTypingSeq S strat.strat G strat.k
  constructor
  · intro h
    have hr : (n, L) ∈ (stratTypingSeq S strat.strat G strat.k).restrictTo
        (S.stratum strat.strat (strat.strat L)) := by rw [hstable]; exact h
    exact (Typing.mem_restrictTo.mp hr).1
  · intro h
    rw [← hstable]
    exact Typing.mem_restrictTo.mpr ⟨h, Finset.mem_filter.mpr ⟨hLlabels, le_refl _⟩⟩

end ShexLean
