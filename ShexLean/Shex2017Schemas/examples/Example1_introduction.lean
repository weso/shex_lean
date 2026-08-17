import ShexLean.Shex2017Schemas.Semantics
import ShexLean.Shex2017Schemas.Render
import Example

/-!
The "Introductory Example" (schema `S₀`) from §1 of Boneva, Labra Gayo,
Prud'hommeaux (2017) — the schema that the paper's own Example 1 (§2)
later names and discusses — used as a second, larger regression check
(alongside `ShexLean.Examples`'s Example 2/3) that the pieces of the
formalization fit together.

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
`t` directly (`t.has obj L`), not by recursing into `Satisfies` on
`def(L)`. So to prove the typing below "correct" (Definition 2), it must
contain an entry not just for the six nodes the paper's prose names, but for
every `ValueDescr` leaf and every `<AnythgShape>`-typed "leftover" object
that any nested pattern resolves along the way — worked out by hand below.
-/

namespace Examples.Introduction

open ShexLean

private def issue1 : Subject := .iri "ex:issue1"
private def issue2 : Subject := .iri "ex:issue2"
private def fatima : Subject := .iri "ex:fatima"
def ren    : Subject := .iri "ex:ren"
private def noa    : Subject := .iri "ex:noa"
private def emin   : Subject := .iri "ex:emin"
private def semweb : RDFNode := .iri "ex:semweb"
private def senior : RDFNode := .iri "ex:senior"
private def junior : RDFNode := .iri "ex:junior"
private def mbox   : RDFNode := .iri "mailto:evp@example.org"

private def lit1       : RDFNode := .lit (.int 1)
private def fatimaName : RDFNode := .lit (.str "Fatima Smith")
private def eminName   : RDFNode := .lit (.str "Emin V. Petrov")
private def eminAffil  : RDFNode := .lit (.str "ABC")

-- Predicates.
private def reportedBy   : IRI := "is:reportedBy"
private def reproducedBy : IRI := "is:reproducedBy"
private def relatedTo    : IRI := "is:relatedTo"
private def clientNbr    : IRI := "ex:clientNbr"
private def clientAffil  : IRI := "ex:clientAffil"
private def expertise    : IRI := "ex:expertise"
private def experience   : IRI := "ex:experience"
private def foafName     : IRI := "foaf:name"
private def foafMbox     : IRI := "foaf:mbox"

-- The 15 triples of `G₀`.
private def t1  : Triple := ⟨issue1, reportedBy, fatima⟩
private def t2  : Triple := ⟨issue1, reproducedBy, ren⟩
private def t3  : Triple := ⟨issue1, reproducedBy, noa⟩
private def t4  : Triple := ⟨issue1, relatedTo, issue2⟩
private def t5  : Triple := ⟨issue2, reportedBy, emin⟩
private def t6  : Triple := ⟨issue2, reproducedBy, ren⟩
private def t7  : Triple := ⟨issue2, relatedTo, issue1⟩
private def t8  : Triple := ⟨fatima, clientNbr, lit1⟩
private def t9  : Triple := ⟨fatima, foafName, fatimaName⟩
private def t10 : Triple := ⟨ren, expertise, semweb⟩
private def t11 : Triple := ⟨ren, experience, senior⟩
private def t12 : Triple := ⟨noa, experience, junior⟩
private def t13 : Triple := ⟨emin, clientAffil, eminAffil⟩
private def t14 : Triple := ⟨emin, foafName, eminName⟩
private def t15 : Triple := ⟨emin, foafMbox, mbox⟩

/-- The graph `G₀` from the Introduction. -/
def G₀ : Graph := {t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15}

-- Shape labels.
private def UserShape     : Label := "UserShape"
private def ProgShape     : Label := "ProgShape"
private def ClientShape   : Label := "ClientShape"
private def IssueShape    : Label := "IssueShape"
private def AnythgShape   : Label := "AnythgShape"
private def ClientAndUser : Label := "ClientAndUser"
private def StringValue   : Label := "StringValue"
private def IRIValue      : Label := "IRIValue"
private def ExpValueSet   : Label := "ExpValueSet"
private def IntValue      : Label := "IntValue"

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
private def clientTE : TExpr :=
  .someOf (.tPattern {clientNbr} IntValue) (.tPattern {clientAffil} AnythgShape)

/-- `Def_User`: the triple-expression body of `<UserShape>`. -/
private def userTE : TExpr :=
  .eachOf (.tPattern {foafName} StringValue) (.rep (.tPattern {foafMbox} IRIValue) 0 (some 1))

private def userShapeDef : ShExpr := .neigDescr userTE

def progShapeDef : ShExpr :=
  .neigDescr (.eachOf (.rep (.tPattern {expertise} IRIValue) 0 none)
    (.tPattern {experience} ExpValueSet))

private def clientShapeDef : ShExpr := .neigDescr clientTE

private def issueShapeDef : ShExpr :=
  .neigDescr (.eachOf (.tPattern {reportedBy} ClientAndUser)
    (.eachOf (.rep (.tPattern {reproducedBy} ProgShape) 1 (some 5))
      (.rep (.tPattern {relatedTo} IssueShape) 0 none)))

private def anythgShapeDef : ShExpr :=
  .neigDescr (.rep (.tPattern allPreds AnythgShape) 0 none)

private def clientAndUserDef : ShExpr :=
  .and (.neigDescr (.eachOf clientTE (.rep (.tPattern clientLeftover AnythgShape) 0 none)))
       (.neigDescr (.eachOf userTE (.rep (.tPattern userLeftover AnythgShape) 0 none)))

private def stringValueDef : ShExpr :=
  .valueDescr {.lit (.str "Fatima Smith"), .lit (.str "Emin V. Petrov")}

private def iriValueDef : ShExpr :=
  .valueDescr {.iri "ex:semweb", .iri "mailto:evp@example.org"}

private def expValueSetDef : ShExpr :=
  .valueDescr {.iri "ex:senior", .iri "ex:junior"}

private def intValueDef : ShExpr :=
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

/-- The typing of `G₀` by `S₀` described in the paper, extended with
every leaf `ValueDescr`/`<AnythgShape>` association that a `⊢` derivation
needs along the way (see the module docstring). 18 associations in total. -/
def typing2 : Typing :=
  { ((issue1 : RDFNode), IssueShape), ((issue2 : RDFNode), IssueShape),
    ((fatima : RDFNode), ClientAndUser), ((emin : RDFNode), ClientAndUser),
    ((ren : RDFNode), ProgShape), ((noa : RDFNode), ProgShape),
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
  exact Matches.rep_empty_of G₀ typing2

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
  refine Matches.eachOf_of G₀ typing2 {t10} {t11} ?_
    (Matches.tPattern_of G₀ typing2 ren experience senior)
  exact Matches.rep_single_of G₀ typing2 {t10} (Matches.tPattern_of G₀ typing2 ren expertise semweb)

theorem satisfies_progShape_noa : Satisfies G₀ typing2 noa progShapeDef := by
  show Matches G₀ typing2 (neigh G₀ noa) _
  have hneigh : neigh G₀ noa = {t12} := by decide
  rw [hneigh]
  refine Matches.eachOf_of G₀ typing2 ∅ {t12}
    (Matches.rep_empty_of G₀ typing2)
    (Matches.tPattern_of G₀ typing2 noa experience junior)

theorem satisfies_issueShape_issue1 : Satisfies G₀ typing2 issue1 issueShapeDef := by
  show Matches G₀ typing2 (neigh G₀ issue1) _
  have hneigh : neigh G₀ issue1 = {t1, t2, t3, t4} := by decide
  rw [hneigh]
  refine Matches.eachOf_of G₀ typing2 {t1} {t2, t3, t4}
    (Matches.tPattern_of G₀ typing2 issue1 reportedBy fatima) ?_
  refine Matches.eachOf_of G₀ typing2 {t2, t3} {t4} ?_ ?_
  · exact Matches.rep_of G₀ typing2 [{t2}, {t3}]
      (by intro Ni hNi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hNi
          rcases hNi with hNi | hNi <;> subst hNi
          · exact Matches.tPattern_of G₀ typing2 issue1 reproducedBy ren
          · exact Matches.tPattern_of G₀ typing2 issue1 reproducedBy noa)
  · exact Matches.rep_single_of G₀ typing2 {t4} (Matches.tPattern_of G₀ typing2 issue1 relatedTo issue2)

theorem satisfies_issueShape_issue2 : Satisfies G₀ typing2 issue2 issueShapeDef := by
  show Matches G₀ typing2 (neigh G₀ issue2) _
  have hneigh : neigh G₀ issue2 = {t5, t6, t7} := by decide
  rw [hneigh]
  refine Matches.eachOf_of G₀ typing2 {t5} {t6, t7}
    (Matches.tPattern_of G₀ typing2 issue2 reportedBy emin) ?_
  refine Matches.eachOf_of G₀ typing2 {t6} {t7} ?_ ?_
  · exact Matches.rep_single_of G₀ typing2 {t6} (Matches.tPattern_of G₀ typing2 issue2 reproducedBy ren)
  · exact Matches.rep_single_of G₀ typing2 {t7} (Matches.tPattern_of G₀ typing2 issue2 relatedTo issue1)

theorem satisfies_clientAndUser_fatima : Satisfies G₀ typing2 fatima clientAndUserDef := by
  have hneigh : neigh G₀ fatima = {t8, t9} := by decide
  constructor
  · show Matches G₀ typing2 (neigh G₀ fatima) _
    rw [hneigh]
    refine Matches.eachOf_of G₀ typing2 {t8} {t9}
      (Or.inl (Matches.tPattern_of G₀ typing2 fatima clientNbr lit1)) ?_
    exact Matches.rep_single_of G₀ typing2 {t9}
      (Matches.tPattern_of G₀ typing2 fatima foafName fatimaName)
  · show Matches G₀ typing2 (neigh G₀ fatima) _
    rw [hneigh]
    refine Matches.eachOf_of G₀ typing2 {t9} {t8} ?_ ?_
    · exact Matches.eachOf_of G₀ typing2 {t9} ∅
        (Matches.tPattern_of G₀ typing2 fatima foafName fatimaName)
        (Matches.rep_empty_of G₀ typing2)
    · exact Matches.rep_single_of G₀ typing2 {t8} (Matches.tPattern_of G₀ typing2 fatima clientNbr lit1)

theorem satisfies_clientAndUser_emin : Satisfies G₀ typing2 emin clientAndUserDef := by
  have hneigh : neigh G₀ emin = {t13, t14, t15} := by decide
  constructor
  · show Matches G₀ typing2 (neigh G₀ emin) _
    rw [hneigh]
    refine Matches.eachOf_of G₀ typing2 {t13} {t14, t15}
      (Or.inr (Matches.tPattern_of G₀ typing2 emin clientAffil eminAffil)) ?_
    exact Matches.rep_of G₀ typing2 [{t14}, {t15}]
      (by intro Ni hNi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hNi
          rcases hNi with hNi | hNi <;> subst hNi
          · exact Matches.tPattern_of G₀ typing2 emin foafName eminName
          · exact Matches.tPattern_of G₀ typing2 emin foafMbox mbox)
  · show Matches G₀ typing2 (neigh G₀ emin) _
    rw [hneigh]
    refine Matches.eachOf_of G₀ typing2 {t14, t15} {t13} ?_ ?_
    · exact Matches.eachOf_of G₀ typing2 {t14} {t15}
        (Matches.tPattern_of G₀ typing2 emin foafName eminName)
        (Matches.rep_single_of G₀ typing2 {t15} (Matches.tPattern_of G₀ typing2 emin foafMbox mbox))
    · exact Matches.rep_single_of G₀ typing2 {t13}
        (Matches.tPattern_of G₀ typing2 emin clientAffil eminAffil)

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

open Examples.Introduction (S₀ G₀ typing2)
open ShexLean (Schema.render Graph.render Typing.render renderDecide corrTyping_decidable)

/-- The Introduction's `S₀`/`G₀` example. `schemaText`/`graphText`/
`typingText` are all generated from the real `S₀`/`G₀`/`typing2` values —
`typing2`'s correctness verdict is a genuine (if slower — 18 associations,
several through nested `.rep`/`.eachOf`/`AND`) `Decidable` computation,
not a hand-typed "(correct)". -/
def introduction : Example where
  name := "schemas2017-example1-introduction"
  summary := "§1 Introductory Example: users, programmers, clients, issues."
  schemaText := Schema.render S₀
  graphText := Graph.render G₀
  typingText :=
    Typing.render typing2 ++
    s!"\n\n(correct = {renderDecide (corrTyping_decidable S₀ G₀ typing2)})"

end Examples
