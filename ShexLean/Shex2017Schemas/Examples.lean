import ShexLean.Shex2017Schemas.Semantics

/-!
Example 2 / Example 3 from Boneva, Labra Gayo, Prud'hommeaux (2017), used as
a regression check that `RDF.lean`, `Typing.lean`, `Syntax.lean` and
`Semantics.lean` fit together as intended.

```
<IssueSh> → is:reportedBy @<Str> ; is:relatedTo @<IssueSh> [0;*]
<Str>     → xsd:string

<i1> is:reportedBy "Ren" ; is:relatedTo <i2> .
<i2> is:reportedBy "Bob" ; is:relatedTo <i1> .
```

> If `<i1>` has shape `<IssueSh>` then `<i2>` also has shape `<IssueSh>`. [...]
> `typing_1 = {(<i1>, <IssueSh>), (<i2>, <IssueSh>), ("Ren", <Str>), ("Bob", <Str>)}`
> [...] `typing_1` [is] correct.

`<Str>` is meant to accept every `xsd:string` literal; since a `ValueDescr`
here is an explicit finite `Finset`, we stand it for the two literals that
actually occur in `G₂`, which is enough to reproduce the paper's argument.
-/

namespace ShexLean.Examples

open ShexLean

-- Marked `@[reducible]` throughout so that `decide` (whose instance search
-- only unfolds reducible definitions) can see through them to the concrete
-- constructors underneath.
@[reducible] private def i1 : RDFNode := .iri "i1"
@[reducible] private def i2 : RDFNode := .iri "i2"
@[reducible] private def ren : RDFNode := .lit (.str "Ren")
@[reducible] private def bob : RDFNode := .lit (.str "Bob")

@[reducible] private def reportedBy : IRI := "is:reportedBy"
@[reducible] private def relatedTo : IRI := "is:relatedTo"

@[reducible] private def t1 : Triple := ⟨i1, reportedBy, ren⟩
@[reducible] private def t2 : Triple := ⟨i1, relatedTo, i2⟩
@[reducible] private def t3 : Triple := ⟨i2, reportedBy, bob⟩
@[reducible] private def t4 : Triple := ⟨i2, relatedTo, i1⟩

/-- The graph `G₂` from Example 2. -/
def G₂ : Graph := {t1, t2, t3, t4}

private def IssueSh : ShapeLabel := "IssueSh"
private def Str : ShapeLabel := "Str"

/-- `<IssueSh> → is:reportedBy @<Str> ; is:relatedTo @<IssueSh> [0;*]`. -/
private def issueShDef : ShapeExpr :=
  .neigDescr (.eachOf
    (.tPattern {reportedBy} Str)
    (.rep (.tPattern {relatedTo} IssueSh) 0 none))

/-- `<Str> → xsd:string`, stood in for by the two string literals of `G₂`. -/
private def strDef : ShapeExpr :=
  .valueDescr {.lit (.str "Ren"), .lit (.str "Bob")}

/-- The schema `S₁` from Example 2. -/
def S₁ : Schema where
  labels := {IssueSh, Str}
  shapeDef
    | "IssueSh" => issueShDef
    | _ => strDef

/-- `typing_1` from Example 3: the maximal (and, per the paper, correct)
typing of `G₂` by `S₁`. -/
def typing1 : Typing := {(i1, IssueSh), (i2, IssueSh), (ren, Str), (bob, Str)}

private theorem satisfies_str (n : RDFNode) (h : n = ren ∨ n = bob) :
    Satisfies G₂ typing1 n strDef := by
  rcases h with h | h <;> subst h <;> exact Or.inl (by decide)

theorem satisfies_issueSh_i1 : Satisfies G₂ typing1 i1 issueShDef := by
  show Matches G₂ typing1 (neigh G₂ i1) _
  have hneigh : neigh G₂ i1 = {t1, t2} := by decide
  rw [hneigh]
  refine ⟨{t1}, {t2}, ⟨?_, ?_⟩, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨i1, reportedBy, ren, by decide, by decide, by decide⟩
  · refine ⟨[{t2}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · intro m hm; cases hm
    · intro Ni hNi
      simp only [List.mem_singleton] at hNi
      subst hNi
      exact ⟨i1, relatedTo, i2, by decide, by decide, by decide⟩

theorem satisfies_issueSh_i2 : Satisfies G₂ typing1 i2 issueShDef := by
  show Matches G₂ typing1 (neigh G₂ i2) _
  have hneigh : neigh G₂ i2 = {t3, t4} := by decide
  rw [hneigh]
  refine ⟨{t3}, {t4}, ⟨?_, ?_⟩, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨i2, reportedBy, bob, by decide, by decide, by decide⟩
  · refine ⟨[{t4}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · intro m hm; cases hm
    · intro Ni hNi
      simp only [List.mem_singleton] at hNi
      subst hNi
      exact ⟨i2, relatedTo, i1, by decide, by decide, by decide⟩

/-- `typing1` is a correct typing of `G₂` by `S₁` (Definition 2): every
node-type association it contains is backed by a `⊢` derivation. -/
theorem typing1_correct :
    ∀ n L, (n, L) ∈ typing1 → Satisfies G₂ typing1 n (S₁.shapeDef L) := by
  intro n L hmem
  simp only [typing1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ <;> subst hn <;> subst hL
  · exact satisfies_issueSh_i1
  · exact satisfies_issueSh_i2
  · exact satisfies_str ren (Or.inl rfl)
  · exact satisfies_str bob (Or.inr rfl)

end ShexLean.Examples
