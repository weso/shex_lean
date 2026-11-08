import ShexLean.InductiveRDF.Graph

/-!
`ofGraph` and `toGraph` (`ShexLean.InductiveRDF.Graph`) are inverses:
`toGraph (ofGraph G) = G` for each `G`.

This fact is the reason why `TGraph` is an *alternative representation*
of RDF graphs, and not only data with a different structure. Each triple
of `G` is in the `pred` list or the `succ` list of exactly one context.
Thus, decomposition and reassembly lose no data.
-/

namespace ShexLean.InductiveRDF

open ShexLean (RDFNode IRI Triple Graph)

private theorem filterMap_some_map {α β} (l : List α) (h : α → β) :
    l.filterMap (fun a => some (h a)) = l.map h := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Membership in the `pred` part of the triples of one context, written
as a condition on `G` only. -/
theorem mem_context_pred_triples (n : Resource) (later : Finset Resource) (G : Graph) (t : Triple) :
    t ∈ (buildContext n later G).pred.filterMap
          (fun (src, lbl) => match lbl with
            | .iri p => some (⟨src, p, n⟩ : Triple) | _ => none) ↔
      t ∈ G ∧ t.obj = n ∧ (t.subj : RDFNode) ∈ later := by
  have hEq : (buildContext n later G).pred.filterMap
        (fun (src, lbl) => match lbl with
          | .iri p => some (⟨src, p, n⟩ : Triple) | _ => none) =
      (G.filter (fun t => t.obj = n ∧ (t.subj : RDFNode) ∈ later)).toList.map
        (fun t' => (⟨t'.subj, t'.pred, n⟩ : Triple)) := by
    show ((G.filter (fun t => t.obj = n ∧ (t.subj : RDFNode) ∈ later)).toList.map
          (fun t' => (t'.subj, RDFNode.iri t'.pred))).filterMap
          (fun (src, lbl) => match lbl with
            | .iri p => some (⟨src, p, n⟩ : Triple) | _ => none) =
        (G.filter (fun t => t.obj = n ∧ (t.subj : RDFNode) ∈ later)).toList.map
          (fun t' => (⟨t'.subj, t'.pred, n⟩ : Triple))
    rw [List.filterMap_map]
    exact filterMap_some_map _ _
  rw [hEq, List.mem_map]
  constructor
  · rintro ⟨t', ht', heq⟩
    have hmem := (Finset.mem_filter.mp (Finset.mem_toList.mp ht'))
    have hteq : (⟨t'.subj, t'.pred, n⟩ : Triple) = t' := by
      show (⟨t'.subj, t'.pred, n⟩ : Triple) = t'
      rw [← hmem.2.1]
    rw [← heq, hteq]
    exact hmem
  · rintro ⟨htG, htobj, htsubj⟩
    refine ⟨t, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨htG, htobj, htsubj⟩), ?_⟩
    show (⟨t.subj, t.pred, n⟩ : Triple) = t
    rw [← htobj]

/-- Membership in the `succ` part of the triples of one context, written
as a condition on `G` only.

If `t` is a member, `n.toSubject?` is always `some _`, because `n` must be
equal to the `Subject` of a real triple (`toSubject_eq_some_iff`). But
the statement must still use the `Option`. We know only that `n` is an
`RDFNode`. It can be a literal. For a literal, `succ` is always `[]`, and
the two sides below are `False`. -/
theorem mem_context_succ_triples (n : Resource) (later : Finset Resource) (G : Graph) (t : Triple) :
    t ∈ (buildContext n later G).succ.filterMap
          (fun (lbl, tgt) => match n.toSubject?, lbl with
            | some ns, .iri p => some (⟨ns, p, tgt⟩ : Triple) | _, _ => none) ↔
      t ∈ G ∧ (t.subj : RDFNode) = n ∧ (t.obj ∈ later ∨ t.obj = n) := by
  rcases hns : n.toSubject? with _ | ns0
  · have hnil : (buildContext n later G).succ.filterMap
        (fun (lbl, tgt) => match (none : Option Subject), lbl with
          | some ns, .iri p => some (⟨ns, p, tgt⟩ : Triple) | _, _ => none) = [] := by
      induction (buildContext n later G).succ with
      | nil => rfl
      | cons a l ih => simp [ih]
    rw [hnil]
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨-, htsubj, -⟩
    exact absurd (toSubject_eq_some_iff.mpr htsubj) (by rw [hns]; simp)
  · have hEq : (buildContext n later G).succ.filterMap
          (fun (lbl, tgt) => match (some ns0 : Option Subject), lbl with
            | some ns, .iri p => some (⟨ns, p, tgt⟩ : Triple) | _, _ => none) =
        (G.filter (fun t => (t.subj : RDFNode) = n ∧ (t.obj ∈ later ∨ t.obj = n))).toList.map
          (fun t' => (⟨ns0, t'.pred, t'.obj⟩ : Triple)) := by
      show ((G.filter (fun t => (t.subj : RDFNode) = n ∧ (t.obj ∈ later ∨ t.obj = n))).toList.map
            (fun t' => (RDFNode.iri t'.pred, t'.obj))).filterMap
            (fun (lbl, tgt) => match (some ns0 : Option Subject), lbl with
              | some ns, .iri p => some (⟨ns, p, tgt⟩ : Triple) | _, _ => none) =
          (G.filter (fun t => (t.subj : RDFNode) = n ∧ (t.obj ∈ later ∨ t.obj = n))).toList.map
            (fun t' => (⟨ns0, t'.pred, t'.obj⟩ : Triple))
      rw [List.filterMap_map]
      exact filterMap_some_map _ _
    rw [hEq, List.mem_map]
    have hnsn : (ns0 : RDFNode) = n := toSubject_eq_some_iff.mp hns
    constructor
    · rintro ⟨t', ht', heq⟩
      have hmem := (Finset.mem_filter.mp (Finset.mem_toList.mp ht'))
      have hteq : (⟨ns0, t'.pred, t'.obj⟩ : Triple) = t' := by
        show (⟨ns0, t'.pred, t'.obj⟩ : Triple) = t'
        have hns0 : ns0 = t'.subj := Subject.toNode_inj (hnsn.trans hmem.2.1.symm)
        rw [hns0]
      rw [← heq, hteq]
      exact hmem
    · rintro ⟨htG, htsubj, htobj⟩
      refine ⟨t, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨htG, htsubj, htobj⟩), ?_⟩
      show (⟨ns0, t.pred, t.obj⟩ : Triple) = t
      have hns0 : ns0 = t.subj := Subject.toNode_inj (hnsn.trans htsubj.symm)
      rw [hns0]

/-- Membership in the triples of one context, written as a condition on
`G` only. The context of `n` (relative to `later`) records `t` if and only
if one of these conditions is true:

* `t` is an edge *into* `n` from a node in `later`.
* `t` is an edge *out of* `n` to a node in `later`.
* `t` is a self-loop at `n`. -/
theorem mem_context_toTriples (n : Resource) (later : Finset Resource) (G : Graph) (t : Triple) :
    t ∈ (buildContext n later G).toTriples ↔
      (t ∈ G ∧ t.obj = n ∧ (t.subj : RDFNode) ∈ later) ∨
      (t ∈ G ∧ (t.subj : RDFNode) = n ∧ (t.obj ∈ later ∨ t.obj = n)) := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl ((mem_context_pred_triples n later G t).mp h)
    · exact Or.inr ((mem_context_succ_triples n later G t).mp h)
  · intro h
    apply List.mem_append.mpr
    rcases h with h | h
    · exact Or.inl ((mem_context_pred_triples n later G t).mpr h)
    · exact Or.inr ((mem_context_succ_triples n later G t).mpr h)

/-- The invariant of `buildFrom`. Decompose the nodes of `G` in the order
`ns` (with `ns.Nodup`), and then reassemble them. The result is exactly
the set of triples of `G` that have their two endpoints in `ns`.

`ofGraph` uses `ns := G.nodes.toList`. With this `ns`, the result is all
the triples of `G`, because the subject and the object of a triple are
always in `Graph.nodes`. Refer to `toGraph_ofGraph` below. -/
theorem mem_buildFrom_toTriples (ns : List Resource) (hnd : ns.Nodup) (G : Graph) (t : Triple) :
    t ∈ (buildFrom ns G).toTriples ↔
      t ∈ G ∧ (t.subj : RDFNode) ∈ ns.toFinset ∧ t.obj ∈ ns.toFinset := by
  induction ns with
  | nil => simp [buildFrom, TGraph.toTriples]
  | cons n rest ih =>
    have hrest : rest.Nodup := (List.nodup_cons.mp hnd).2
    have key : t ∈ (buildFrom (n :: rest) G).toTriples ↔
        ((t ∈ G ∧ t.obj = n ∧ (t.subj : RDFNode) ∈ rest.toFinset) ∨
          (t ∈ G ∧ (t.subj : RDFNode) = n ∧ (t.obj ∈ rest.toFinset ∨ t.obj = n))) ∨
        (t ∈ G ∧ (t.subj : RDFNode) ∈ rest.toFinset ∧ t.obj ∈ rest.toFinset) := by
      constructor
      · intro h
        rcases List.mem_append.mp h with h | h
        · exact Or.inl ((mem_context_toTriples n rest.toFinset G t).mp h)
        · exact Or.inr ((ih hrest).mp h)
      · intro h
        apply List.mem_append.mpr
        rcases h with h | h
        · exact Or.inl ((mem_context_toTriples n rest.toFinset G t).mpr h)
        · exact Or.inr ((ih hrest).mpr h)
    rw [key]
    simp only [List.mem_toFinset, List.mem_cons]
    constructor
    · rintro ((⟨htG, htobj, htsubj⟩ | ⟨htG, htsubj, htobj⟩) | ⟨htG, htsubj, htobj⟩)
      · exact ⟨htG, Or.inr htsubj, Or.inl htobj⟩
      · exact ⟨htG, Or.inl htsubj, htobj.symm⟩
      · exact ⟨htG, Or.inr htsubj, Or.inr htobj⟩
    · rintro ⟨htG, (htsubj | htsubj), (htobj | htobj)⟩
      · exact Or.inl (Or.inr ⟨htG, htsubj, Or.inr htobj⟩)
      · exact Or.inl (Or.inr ⟨htG, htsubj, Or.inl htobj⟩)
      · exact Or.inl (Or.inl ⟨htG, htobj, htsubj⟩)
      · exact Or.inr ⟨htG, htsubj, htobj⟩

/-- The two endpoints of each triple are nodes of the graph. -/
private theorem triple_endpoints_mem_nodes (G : Graph) {t : Triple} (ht : t ∈ G) :
    (t.subj : RDFNode) ∈ G.nodes ∧ t.obj ∈ G.nodes :=
  ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht),
   Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)⟩

/-- **Round trip of `ofGraph` and `toGraph`.** Decompose `G` into an
inductive triple graph, and then reassemble it. The result is exactly
`G`. The representation loses no data. -/
theorem toGraph_ofGraph (G : Graph) : toGraph (ofGraph G) = G := by
  ext t
  show t ∈ (buildFrom G.nodes.toList G).toTriples.toFinset ↔ t ∈ G
  rw [List.mem_toFinset, mem_buildFrom_toTriples G.nodes.toList (Finset.nodup_toList _) G]
  constructor
  · rintro ⟨htG, -, -⟩; exact htG
  · intro htG
    obtain ⟨hsubj, hobj⟩ := triple_endpoints_mem_nodes G htG
    exact ⟨htG, by simpa using hsubj, by simpa using hobj⟩

end ShexLean.InductiveRDF
