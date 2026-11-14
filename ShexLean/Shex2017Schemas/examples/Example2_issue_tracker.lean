import ShexLean.Shex2017Schemas.Semantics
import ShexLean.Shex2017Schemas.MaximalTyping
import ShexLean.Shex2017Schemas.Render
import Example

/-!
Example 2 from Boneva, Labra Gayo, Prud'hommeaux
(2017): the recursive schema `<IssueSh>`/`<Str>`.
We use it as a regression check.
It shows that `RDF.lean`, `Typing.lean`, `Syntax.lean`
and `Semantics.lean` work together correctly.

```
<IssueSh> → is:reportedBy @<Str> ; is:relatedTo @<IssueSh> [0;*]
<Str>     → xsd:string

<i1> is:reportedBy "Ren" ; is:relatedTo <i2> .
<i2> is:reportedBy "Bob" ; is:relatedTo <i1> .
```

> If `<i1>` has shape `<IssueSh>` then `<i2>` also has shape `<IssueSh>`. [...]
> `typing_1 = {(<i1>, <IssueSh>), (<i2>, <IssueSh>), ("Ren", <Str>), ("Bob", <Str>)}`
> [...] `typing_1` [is] correct.

`<Str>` must accept each `xsd:string` literal.
But here, a `ValueDescr` is an explicit finite `Finset`.
Thus, we replace it with the two literals that occur in `G₂`.
This is sufficient to do the argument of the paper again.

The correctness of `typing_1` is a claim of Example 3.
(Example 2 only gives `S₁` and `G₂`.)
We prove it here, near its schema and graph, because the other three typings
of Example 3 (`Example3_typings.lean`) use all the definitions in this file.
-/

namespace ShexLean.Examples

open ShexLean

-- These definitions are not `private`, because `Example3_typings.lean` uses all of them.
def i1 : Subject := .iri "i1"
def i2 : Subject := .iri "i2"
def ren : RDFNode := .lit (.str "Ren")
def bob : RDFNode := .lit (.str "Bob")

def reportedBy : IRI := "is:reportedBy"
def relatedTo : IRI := "is:relatedTo"

def t1 : Triple := ⟨i1, reportedBy, ren⟩
def t2 : Triple := ⟨i1, relatedTo, i2⟩
def t3 : Triple := ⟨i2, reportedBy, bob⟩
def t4 : Triple := ⟨i2, relatedTo, i1⟩

/-- The graph `G₂` from Example 2. -/
def G₂ : Graph := {t1, t2, t3, t4}

def IssueSh : Label := "IssueSh"
def Str : Label := "Str"

/-- `<IssueSh> → is:reportedBy @<Str> ; is:relatedTo @<IssueSh> [0;*]`. -/
def issueShDef : ShExpr :=
  .neigDescr (.eachOf
    (.tPattern {reportedBy} Str)
    (.rep (.tPattern {relatedTo} IssueSh) 0 none))

/-- `<Str> → xsd:string`.
The two string literals of `G₂` replace `xsd:string`. -/
def strDef : ShExpr :=
  .valueDescr {.lit (.str "Ren"), .lit (.str "Bob")}

/-- The schema `S₁` from Example 2. -/
def S₁ : Schema where
  labels := {IssueSh, Str}
  shapeDef
    | "IssueSh" => issueShDef
    | _ => strDef

/-- `typing_1` from Example 3: the maximal typing of `G₂` by `S₁`.
The paper says that it is correct. -/
def typing1 : Typing :=
  {((i1 : RDFNode), IssueSh), ((i2 : RDFNode), IssueSh), (ren, Str), (bob, Str)}

theorem satisfies_str (n : RDFNode) (h : n = ren ∨ n = bob) :
    Satisfies G₂ typing1 n strDef := by
  rcases h with h | h <;> subst h <;> exact Or.inl (by decide)

theorem satisfies_issueSh_i1 : Satisfies G₂ typing1 i1 issueShDef := by
  show Matches G₂ typing1 (neigh G₂ i1) _
  have hneigh : neigh G₂ i1 = {t1, t2} := by decide
  rw [hneigh]
  refine Matches.eachOf_of G₂ typing1 {t1} {t2}
    (Matches.tPattern_of G₂ typing1 i1 reportedBy ren) ?_
  exact Matches.rep_single_of G₂ typing1 {t2} (Matches.tPattern_of G₂ typing1 i1 relatedTo i2)

theorem satisfies_issueSh_i2 : Satisfies G₂ typing1 i2 issueShDef := by
  show Matches G₂ typing1 (neigh G₂ i2) _
  have hneigh : neigh G₂ i2 = {t3, t4} := by decide
  rw [hneigh]
  refine Matches.eachOf_of G₂ typing1 {t3} {t4}
    (Matches.tPattern_of G₂ typing1 i2 reportedBy bob) ?_
  exact Matches.rep_single_of G₂ typing1 {t4} (Matches.tPattern_of G₂ typing1 i2 relatedTo i1)

/-- `typing1` is a correct typing of `G₂` by `S₁` (Definition 2).
A `⊢` derivation supports each node-type association in it. -/
theorem typing1_correct : S₁.CorrTyping G₂ typing1 := by
  intro n L hmem
  simp only [typing1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ <;> subst hn <;> subst hL
  · exact satisfies_issueSh_i1
  · exact satisfies_issueSh_i2
  · exact satisfies_str ren (Or.inl rfl)
  · exact satisfies_str bob (Or.inr rfl)

end ShexLean.Examples

namespace Examples

open ShexLean.Examples (S₁ G₂ typing1)

/-- The `<IssueSh>`/`<Str>` example of Example 2.
`ShexLean.Schema.render` and `Graph.render` generate
`schemaText` and `graphText` from the real values `S₁` and `G₂`.
`typingText` contains a correctness result for `typing_1` that a `Decidable` instance computes.
It is not a "(correct)" that a person typed by hand. -/
def issueTracker : Example where
  name := "schemas2017-example2-issue-tracker"
  summary := "Recursive <IssueSh> schema, two issues reporting on each other."
  schemaText := ShexLean.Schema.render S₁
  graphText := ShexLean.Graph.render G₂
  typingText :=
    ShexLean.Typing.render typing1 ++
    s!"   (correct = {ShexLean.renderDecide (ShexLean.corrTyping_decidable S₁ G₂ typing1)})"

end Examples
