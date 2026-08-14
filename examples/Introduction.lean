import ShexLean.Semantics
import Example

/-!
The "Introductory Example" from §1 of Boneva, Labra Gayo, Prud'hommeaux
(2017), used as a second, larger regression check (alongside
`ShexLean.Examples`'s Example 2/3) that the pieces of the formalization fit
together.

```
<UserShape>      → foaf:name @<StringValue> ; foaf:mbox @<IRIValue> [0;1]
<ProgShape>      → ex:expertise @<IRIValue> [0;*] ; ex:experience @<ExpValueSet>
<ClientShape>    → ex:clientNbr @<IntValue> | ex:clientAffil @<AnythgShape>
<IssueShape>     → is:reportedBy @<ClientAndUser> ;
                    is:reproducedBy @<ProgShape> [1;5] ;
                    is:relatedTo @<IssueShape> [0;*]
<AnythgShape>    → IRI @<AnythgShape> [0;*]
<ClientAndUser>  → Def_Client ; IRI − {ex:clientNbr, ex:clientAffil} @<AnythgShape> [0;*]
                    AND
                    Def_User ; IRI − {foaf:name, foaf:mbox} @<AnythgShape> [0;*]
<StringValue>    → xsd:string
<IRIValue>       → IRI
<ExpValueSet>    → {ex:senior, ex:junior}
<IntValue>       → xsd:integer
```

where `Def_Client`/`Def_User` are the triple-expression bodies of
`<ClientShape>`/`<UserShape>` respectively, reused verbatim inside
`<ClientAndUser>`, and `−` is set difference.

```
ex:issue1 is:reportedBy ex:fatima ; is:reproducedBy ex:ren , ex:noa ;
          is:relatedTo ex:issue2 .
ex:issue2 is:reportedBy ex:emin ; is:reproducedBy ex:ren ;
          is:relatedTo ex:issue1 .
ex:fatima ex:clientNbr 1 ; foaf:name "Fatima Smith" .
ex:ren    ex:expertise ex:semweb ; ex:experience ex:senior .
ex:noa    ex:experience ex:junior .
ex:emin   ex:clientAffil "ABC" ; foaf:name "Emin V. Petrov" ;
          foaf:mbox <mailto:evp@example.org> .
```

> Nodes ex:issue1 and ex:issue2 have shape <IssueShape>; ex:fatima and
> ex:emin are <ClientAndUser>; ex:ren and ex:noa have shape <ProgShape>.

**Approximating `IRI` and set difference.** `Syntax.lean`'s `PropSet` is an
explicit `Finset IRI`, so it cannot literally express "any IRI" (used in
`<AnythgShape>`) or "any IRI except a finite exclusion list" (used in
`<ClientAndUser>`'s two branches). Exactly like the existing `Examples.lean`,
which stands in `xsd:string` with the two literals that actually occur in
`G₂`, here we stand in every such wildcard/difference `PropSet` with the
concrete finite set of predicates that actually occur in `G₀`
(`allPreds`, `clientLeftover`, `userLeftover` below). This is semantically
sufficient for `G₀`: in every derivation below, `<AnythgShape>` only ever
gets asked about a node whose neighbourhood in `G₀` is already empty (every
literal, and the one IRI leaf `mailto:evp@example.org`, which is never used
as a subject), so the exact contents of the approximated `IRI` wildcard
inside `<AnythgShape>`'s own definition never actually get exercised by any
proof — only membership of the *specific* predicate being matched matters,
and that is faithfully preserved by `allPreds \ {…}`.

**Why every leaf needs its own typing entry.** `Semantics.lean`'s
`te-tpattern` rule resolves a `TriplePattern`'s shape reference by consulting
`typing` directly (`typing.has obj L`), not by recursing into `Satisfies` on
`def(L)`. So to prove the typing below "correct" (Definition 2), it must
contain an entry not just for the six nodes the paper's prose names, but for
every `ValueDescr` leaf and every `<AnythgShape>`-typed "leftover" object
that any nested pattern resolves along the way — worked out by hand below.
-/

namespace Examples.Introduction

open ShexLean

-- Nodes, marked `@[reducible]` for `decide`, as in `ShexLean.Examples`.
@[reducible] private def issue1 : RDFNode := .iri "ex:issue1"
@[reducible] private def issue2 : RDFNode := .iri "ex:issue2"
@[reducible] private def fatima : RDFNode := .iri "ex:fatima"
@[reducible] private def ren    : RDFNode := .iri "ex:ren"
@[reducible] private def noa    : RDFNode := .iri "ex:noa"
@[reducible] private def emin   : RDFNode := .iri "ex:emin"
@[reducible] private def semweb : RDFNode := .iri "ex:semweb"
@[reducible] private def senior : RDFNode := .iri "ex:senior"
@[reducible] private def junior : RDFNode := .iri "ex:junior"
@[reducible] private def mbox   : RDFNode := .iri "mailto:evp@example.org"

@[reducible] private def lit1       : RDFNode := .lit (.int 1)
@[reducible] private def fatimaName : RDFNode := .lit (.str "Fatima Smith")
@[reducible] private def eminName   : RDFNode := .lit (.str "Emin V. Petrov")
@[reducible] private def eminAffil  : RDFNode := .lit (.str "ABC")

-- Predicates.
@[reducible] private def reportedBy   : IRI := "is:reportedBy"
@[reducible] private def reproducedBy : IRI := "is:reproducedBy"
@[reducible] private def relatedTo    : IRI := "is:relatedTo"
@[reducible] private def clientNbr    : IRI := "ex:clientNbr"
@[reducible] private def clientAffil  : IRI := "ex:clientAffil"
@[reducible] private def expertise    : IRI := "ex:expertise"
@[reducible] private def experience   : IRI := "ex:experience"
@[reducible] private def foafName     : IRI := "foaf:name"
@[reducible] private def foafMbox     : IRI := "foaf:mbox"

-- The 15 triples of `G₀`.
@[reducible] private def t1  : Triple := ⟨issue1, reportedBy, fatima⟩
@[reducible] private def t2  : Triple := ⟨issue1, reproducedBy, ren⟩
@[reducible] private def t3  : Triple := ⟨issue1, reproducedBy, noa⟩
@[reducible] private def t4  : Triple := ⟨issue1, relatedTo, issue2⟩
@[reducible] private def t5  : Triple := ⟨issue2, reportedBy, emin⟩
@[reducible] private def t6  : Triple := ⟨issue2, reproducedBy, ren⟩
@[reducible] private def t7  : Triple := ⟨issue2, relatedTo, issue1⟩
@[reducible] private def t8  : Triple := ⟨fatima, clientNbr, lit1⟩
@[reducible] private def t9  : Triple := ⟨fatima, foafName, fatimaName⟩
@[reducible] private def t10 : Triple := ⟨ren, expertise, semweb⟩
@[reducible] private def t11 : Triple := ⟨ren, experience, senior⟩
@[reducible] private def t12 : Triple := ⟨noa, experience, junior⟩
@[reducible] private def t13 : Triple := ⟨emin, clientAffil, eminAffil⟩
@[reducible] private def t14 : Triple := ⟨emin, foafName, eminName⟩
@[reducible] private def t15 : Triple := ⟨emin, foafMbox, mbox⟩

/-- The graph `G₀` from the Introduction. -/
def G₀ : Graph := {t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15}

-- Shape labels.
private def UserShape     : ShapeLabel := "UserShape"
private def ProgShape     : ShapeLabel := "ProgShape"
private def ClientShape   : ShapeLabel := "ClientShape"
private def IssueShape    : ShapeLabel := "IssueShape"
private def AnythgShape   : ShapeLabel := "AnythgShape"
private def ClientAndUser : ShapeLabel := "ClientAndUser"
private def StringValue   : ShapeLabel := "StringValue"
private def IRIValue      : ShapeLabel := "IRIValue"
private def ExpValueSet   : ShapeLabel := "ExpValueSet"
private def IntValue      : ShapeLabel := "IntValue"

/-- All predicates occurring in `G₀`, standing in for the unrestricted `IRI`
wildcard (see the module docstring). -/
private def allPreds : PropSet :=
  {reportedBy, reproducedBy, relatedTo, clientNbr, clientAffil, expertise,
    experience, foafName, foafMbox}

/-- Stands in for `IRI − {ex:clientNbr, ex:clientAffil}`. -/
private def clientLeftover : PropSet := allPreds \ {clientNbr, clientAffil}

/-- Stands in for `IRI − {foaf:name, foaf:mbox}`. -/
private def userLeftover : PropSet := allPreds \ {foafName, foafMbox}

/-- `Def_Client`: the triple-expression body of `<ClientShape>`. -/
private def clientTE : TripleExpr :=
  .someOf (.tPattern {clientNbr} IntValue) (.tPattern {clientAffil} AnythgShape)

/-- `Def_User`: the triple-expression body of `<UserShape>`. -/
private def userTE : TripleExpr :=
  .eachOf (.tPattern {foafName} StringValue) (.rep (.tPattern {foafMbox} IRIValue) 0 (some 1))

private def userShapeDef : ShapeExpr := .neigDescr userTE

private def progShapeDef : ShapeExpr :=
  .neigDescr (.eachOf (.rep (.tPattern {expertise} IRIValue) 0 none)
    (.tPattern {experience} ExpValueSet))

private def clientShapeDef : ShapeExpr := .neigDescr clientTE

private def issueShapeDef : ShapeExpr :=
  .neigDescr (.eachOf (.tPattern {reportedBy} ClientAndUser)
    (.eachOf (.rep (.tPattern {reproducedBy} ProgShape) 1 (some 5))
      (.rep (.tPattern {relatedTo} IssueShape) 0 none)))

private def anythgShapeDef : ShapeExpr :=
  .neigDescr (.rep (.tPattern allPreds AnythgShape) 0 none)

private def clientAndUserDef : ShapeExpr :=
  .and (.neigDescr (.eachOf clientTE (.rep (.tPattern clientLeftover AnythgShape) 0 none)))
       (.neigDescr (.eachOf userTE (.rep (.tPattern userLeftover AnythgShape) 0 none)))

private def stringValueDef : ShapeExpr :=
  .valueDescr {.lit (.str "Fatima Smith"), .lit (.str "Emin V. Petrov")}

private def iriValueDef : ShapeExpr :=
  .valueDescr {.iri "ex:semweb", .iri "mailto:evp@example.org"}

private def expValueSetDef : ShapeExpr :=
  .valueDescr {.iri "ex:senior", .iri "ex:junior"}

private def intValueDef : ShapeExpr :=
  .valueDescr {.lit (.int 1)}

/-- The schema `S₀` from the Introduction. -/
def S₀ : Schema where
  labels :=
    {UserShape, ProgShape, ClientShape, IssueShape, AnythgShape, ClientAndUser,
      StringValue, IRIValue, ExpValueSet, IntValue}
  shapeDef
    | "UserShape" => userShapeDef
    | "ProgShape" => progShapeDef
    | "ClientShape" => clientShapeDef
    | "IssueShape" => issueShapeDef
    | "AnythgShape" => anythgShapeDef
    | "ClientAndUser" => clientAndUserDef
    | "StringValue" => stringValueDef
    | "IRIValue" => iriValueDef
    | "ExpValueSet" => expValueSetDef
    | _ => intValueDef

/-- The typing of `G₀` by `S₀` described in the paper's prose, extended with
every leaf `ValueDescr`/`<AnythgShape>` association that a `⊢` derivation
needs along the way (see the module docstring). 18 associations in total. -/
def typing2 : Typing :=
  { (issue1, IssueShape), (issue2, IssueShape),
    (fatima, ClientAndUser), (emin, ClientAndUser),
    (ren, ProgShape), (noa, ProgShape),
    (lit1, IntValue), (lit1, AnythgShape),
    (eminAffil, AnythgShape),
    (fatimaName, StringValue), (fatimaName, AnythgShape),
    (eminName, StringValue), (eminName, AnythgShape),
    (mbox, IRIValue), (mbox, AnythgShape),
    (semweb, IRIValue),
    (senior, ExpValueSet),
    (junior, ExpValueSet) }

/-! ### Leaf lemmas -/

private theorem neigh_empty_satisfies_anythg (n : RDFNode) (h : neigh G₀ n = ∅) :
    Satisfies G₀ typing2 n anythgShapeDef := by
  show Matches G₀ typing2 (neigh G₀ n) _
  rw [h]
  refine ⟨[], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro m' hm'; cases hm'
  · intro Ni hNi; cases hNi

private theorem satisfies_stringValue (n : RDFNode) (h : n = fatimaName ∨ n = eminName) :
    Satisfies G₀ typing2 n stringValueDef := by
  rcases h with h | h <;> subst h <;> exact Or.inl (by decide)

private theorem satisfies_iriValue (n : RDFNode) (h : n = semweb ∨ n = mbox) :
    Satisfies G₀ typing2 n iriValueDef := by
  rcases h with h | h <;> subst h <;> exact Or.inl (by decide)

private theorem satisfies_expValueSet (n : RDFNode) (h : n = senior ∨ n = junior) :
    Satisfies G₀ typing2 n expValueSetDef := by
  rcases h with h | h <;> subst h <;> exact Or.inl (by decide)

private theorem satisfies_intValue : Satisfies G₀ typing2 lit1 intValueDef :=
  Or.inl (by decide)

private theorem neigh_lit1_empty : neigh G₀ lit1 = ∅ := by decide
private theorem neigh_eminAffil_empty : neigh G₀ eminAffil = ∅ := by decide
private theorem neigh_fatimaName_empty : neigh G₀ fatimaName = ∅ := by decide
private theorem neigh_eminName_empty : neigh G₀ eminName = ∅ := by decide
private theorem neigh_mbox_empty : neigh G₀ mbox = ∅ := by decide

/-! ### The six "real" nodes -/

theorem satisfies_progShape_ren : Satisfies G₀ typing2 ren progShapeDef := by
  show Matches G₀ typing2 (neigh G₀ ren) _
  have hneigh : neigh G₀ ren = {t10, t11} := by decide
  rw [hneigh]
  refine ⟨{t10}, {t11}, ⟨?_, ?_⟩, ?_, ?_⟩
  · decide
  · decide
  · refine ⟨[{t10}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · intro m' hm'; cases hm'
    · intro Ni hNi
      simp only [List.mem_singleton] at hNi
      subst hNi
      exact ⟨ren, expertise, semweb, by decide, by decide, by decide⟩
  · exact ⟨ren, experience, senior, by decide, by decide, by decide⟩

theorem satisfies_progShape_noa : Satisfies G₀ typing2 noa progShapeDef := by
  show Matches G₀ typing2 (neigh G₀ noa) _
  have hneigh : neigh G₀ noa = {t12} := by decide
  rw [hneigh]
  refine ⟨∅, {t12}, ⟨?_, ?_⟩, ?_, ?_⟩
  · decide
  · decide
  · refine ⟨[], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · intro m' hm'; cases hm'
    · intro Ni hNi; cases hNi
  · exact ⟨noa, experience, junior, by decide, by decide, by decide⟩

theorem satisfies_issueShape_issue1 : Satisfies G₀ typing2 issue1 issueShapeDef := by
  show Matches G₀ typing2 (neigh G₀ issue1) _
  have hneigh : neigh G₀ issue1 = {t1, t2, t3, t4} := by decide
  rw [hneigh]
  refine ⟨{t1}, {t2, t3, t4}, ⟨?_, ?_⟩, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨issue1, reportedBy, fatima, by decide, by decide, by decide⟩
  · refine ⟨{t2, t3}, {t4}, ⟨?_, ?_⟩, ?_, ?_⟩
    · decide
    · decide
    · refine ⟨[{t2}, {t3}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · intro m' hm'; cases hm'; decide
      · intro Ni hNi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hNi
        rcases hNi with hNi | hNi <;> subst hNi
        · exact ⟨issue1, reproducedBy, ren, by decide, by decide, by decide⟩
        · exact ⟨issue1, reproducedBy, noa, by decide, by decide, by decide⟩
    · refine ⟨[{t4}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · intro m' hm'; cases hm'
      · intro Ni hNi
        simp only [List.mem_singleton] at hNi
        subst hNi
        exact ⟨issue1, relatedTo, issue2, by decide, by decide, by decide⟩

theorem satisfies_issueShape_issue2 : Satisfies G₀ typing2 issue2 issueShapeDef := by
  show Matches G₀ typing2 (neigh G₀ issue2) _
  have hneigh : neigh G₀ issue2 = {t5, t6, t7} := by decide
  rw [hneigh]
  refine ⟨{t5}, {t6, t7}, ⟨?_, ?_⟩, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨issue2, reportedBy, emin, by decide, by decide, by decide⟩
  · refine ⟨{t6}, {t7}, ⟨?_, ?_⟩, ?_, ?_⟩
    · decide
    · decide
    · refine ⟨[{t6}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · intro m' hm'; cases hm'; decide
      · intro Ni hNi
        simp only [List.mem_singleton] at hNi
        subst hNi
        exact ⟨issue2, reproducedBy, ren, by decide, by decide, by decide⟩
    · refine ⟨[{t7}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · intro m' hm'; cases hm'
      · intro Ni hNi
        simp only [List.mem_singleton] at hNi
        subst hNi
        exact ⟨issue2, relatedTo, issue1, by decide, by decide, by decide⟩

theorem satisfies_clientAndUser_fatima : Satisfies G₀ typing2 fatima clientAndUserDef := by
  have hneigh : neigh G₀ fatima = {t8, t9} := by decide
  constructor
  · show Matches G₀ typing2 (neigh G₀ fatima) _
    rw [hneigh]
    refine ⟨{t8}, {t9}, ⟨?_, ?_⟩, ?_, ?_⟩
    · decide
    · decide
    · exact Or.inl ⟨fatima, clientNbr, lit1, by decide, by decide, by decide⟩
    · refine ⟨[{t9}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · intro m' hm'; cases hm'
      · intro Ni hNi
        simp only [List.mem_singleton] at hNi
        subst hNi
        exact ⟨fatima, foafName, fatimaName, by decide, by decide, by decide⟩
  · show Matches G₀ typing2 (neigh G₀ fatima) _
    rw [hneigh]
    refine ⟨{t9}, {t8}, ⟨?_, ?_⟩, ?_, ?_⟩
    · decide
    · decide
    · refine ⟨{t9}, ∅, ⟨?_, ?_⟩, ?_, ?_⟩
      · decide
      · decide
      · exact ⟨fatima, foafName, fatimaName, by decide, by decide, by decide⟩
      · refine ⟨[], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
        · decide
        · decide
        · decide
        · intro m' hm'; cases hm'; decide
        · intro Ni hNi; cases hNi
    · refine ⟨[{t8}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · intro m' hm'; cases hm'
      · intro Ni hNi
        simp only [List.mem_singleton] at hNi
        subst hNi
        exact ⟨fatima, clientNbr, lit1, by decide, by decide, by decide⟩

theorem satisfies_clientAndUser_emin : Satisfies G₀ typing2 emin clientAndUserDef := by
  have hneigh : neigh G₀ emin = {t13, t14, t15} := by decide
  constructor
  · show Matches G₀ typing2 (neigh G₀ emin) _
    rw [hneigh]
    refine ⟨{t13}, {t14, t15}, ⟨?_, ?_⟩, ?_, ?_⟩
    · decide
    · decide
    · exact Or.inr ⟨emin, clientAffil, eminAffil, by decide, by decide, by decide⟩
    · refine ⟨[{t14}, {t15}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · intro m' hm'; cases hm'
      · intro Ni hNi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hNi
        rcases hNi with hNi | hNi <;> subst hNi
        · exact ⟨emin, foafName, eminName, by decide, by decide, by decide⟩
        · exact ⟨emin, foafMbox, mbox, by decide, by decide, by decide⟩
  · show Matches G₀ typing2 (neigh G₀ emin) _
    rw [hneigh]
    refine ⟨{t14, t15}, {t13}, ⟨?_, ?_⟩, ?_, ?_⟩
    · decide
    · decide
    · refine ⟨{t14}, {t15}, ⟨?_, ?_⟩, ?_, ?_⟩
      · decide
      · decide
      · exact ⟨emin, foafName, eminName, by decide, by decide, by decide⟩
      · refine ⟨[{t15}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
        · decide
        · decide
        · decide
        · intro m' hm'; cases hm'; decide
        · intro Ni hNi
          simp only [List.mem_singleton] at hNi
          subst hNi
          exact ⟨emin, foafMbox, mbox, by decide, by decide, by decide⟩
    · refine ⟨[{t13}], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · intro m' hm'; cases hm'
      · intro Ni hNi
        simp only [List.mem_singleton] at hNi
        subst hNi
        exact ⟨emin, clientAffil, eminAffil, by decide, by decide, by decide⟩

/-- `typing2` is a correct typing of `G₀` by `S₀` (Definition 2). -/
theorem typing2_correct :
    ∀ n L, (n, L) ∈ typing2 → Satisfies G₀ typing2 n (S₀.shapeDef L) := by
  intro n L hmem
  simp only [typing2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with
      ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ |
      ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ |
      ⟨hn, hL⟩ | ⟨hn, hL⟩ <;>
    subst hn <;> subst hL
  · exact satisfies_issueShape_issue1
  · exact satisfies_issueShape_issue2
  · exact satisfies_clientAndUser_fatima
  · exact satisfies_clientAndUser_emin
  · exact satisfies_progShape_ren
  · exact satisfies_progShape_noa
  · exact satisfies_intValue
  · exact neigh_empty_satisfies_anythg lit1 neigh_lit1_empty
  · exact neigh_empty_satisfies_anythg eminAffil neigh_eminAffil_empty
  · exact satisfies_stringValue fatimaName (Or.inl rfl)
  · exact neigh_empty_satisfies_anythg fatimaName neigh_fatimaName_empty
  · exact satisfies_stringValue eminName (Or.inr rfl)
  · exact neigh_empty_satisfies_anythg eminName neigh_eminName_empty
  · exact satisfies_iriValue mbox (Or.inr rfl)
  · exact neigh_empty_satisfies_anythg mbox neigh_mbox_empty
  · exact satisfies_iriValue semweb (Or.inl rfl)
  · exact satisfies_expValueSet senior (Or.inl rfl)
  · exact satisfies_expValueSet junior (Or.inr rfl)

end Examples.Introduction

namespace Examples

/-- The Introduction's `S₀`/`G₀` example. -/
def introduction : Example where
  name := "introduction"
  summary := "The paper's §1 Introductory Example: users, programmers, clients and issues."
  schemaText :=
    "<UserShape>      → foaf:name @<StringValue> ; foaf:mbox @<IRIValue> [0;1]\n" ++
    "<ProgShape>      → ex:expertise @<IRIValue> [0;*] ; ex:experience @<ExpValueSet>\n" ++
    "<ClientShape>    → ex:clientNbr @<IntValue> | ex:clientAffil @<AnythgShape>\n" ++
    "<IssueShape>     → is:reportedBy @<ClientAndUser> ;\n" ++
    "                   is:reproducedBy @<ProgShape> [1;5] ;\n" ++
    "                   is:relatedTo @<IssueShape> [0;*]\n" ++
    "<AnythgShape>    → IRI @<AnythgShape> [0;*]\n" ++
    "<ClientAndUser>  → Def_Client ; IRI − {ex:clientNbr, ex:clientAffil} @<AnythgShape> [0;*]\n" ++
    "                   AND\n" ++
    "                   Def_User ; IRI − {foaf:name, foaf:mbox} @<AnythgShape> [0;*]\n" ++
    "<StringValue>    → xsd:string\n" ++
    "<IRIValue>       → IRI\n" ++
    "<ExpValueSet>    → {ex:senior, ex:junior}\n" ++
    "<IntValue>       → xsd:integer"
  graphText :=
    "ex:issue1 is:reportedBy ex:fatima ; is:reproducedBy ex:ren , ex:noa ;\n" ++
    "          is:relatedTo ex:issue2 .\n" ++
    "ex:issue2 is:reportedBy ex:emin ; is:reproducedBy ex:ren ;\n" ++
    "          is:relatedTo ex:issue1 .\n" ++
    "ex:fatima ex:clientNbr 1 ; foaf:name \"Fatima Smith\" .\n" ++
    "ex:ren    ex:expertise ex:semweb ; ex:experience ex:senior .\n" ++
    "ex:noa    ex:experience ex:junior .\n" ++
    "ex:emin   ex:clientAffil \"ABC\" ; foaf:name \"Emin V. Petrov\" ;\n" ++
    "          foaf:mbox <mailto:evp@example.org> ."
  typingText :=
    "ex:issue1, ex:issue2 : <IssueShape>\n" ++
    "ex:fatima, ex:emin   : <ClientAndUser>\n" ++
    "ex:ren, ex:noa       : <ProgShape>\n" ++
    "(plus leaf associations for nested ValueDescr/<AnythgShape> targets — " ++
    "see Introduction.typing2 for the full 18-pair typing proved correct.)"

end Examples
