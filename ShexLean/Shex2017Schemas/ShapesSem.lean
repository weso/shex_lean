import ShexLean.Shex2017Schemas.Lemma2

/-!
Definitions 5 and 6 (§3.3): the maximal correct typing of `G` by `S`, and
`SHAPES_SEM` itself — the statement this whole development has been
building towards since §3.1:

> SHAPES_SEM: node `n` in graph `G` has shape (or type) `L` from schema `S`

Both are one-line definitions in the paper, sitting directly on top of
Proposition 1 (`Typing(G, S, str)` is always a correct typing,
`ShexLean/Shex2017Schemas/Proposition1.lean`) and Lemma 2 (`Typing(G, S, str)` does not
depend on `str`, `ShexLean/Shex2017Schemas/Lemma2.lean`):

> Definition 5 (maximal correct typing). Let `S = (L, def)` be a schema and
> `G` be a graph. The maximal correct typing of `G` by `S` is denoted
> `Typing(G, S)` and is defined as `Typing(G, S, str)` for some
> stratification `str` of `S`.
>
> Definition 6 (shapes_sem). Let `S = (L, def)` be a schema and `G` be a
> graph. We say that node `n` (of `G`) has shape `L` (from `S`) if
> `(n, L) ∈ Typing(G, S)`.

The only work left to do here is to record that Definition 5 is
well-defined regardless of which stratification `Classical.choice` happens
to pick out of `S.StratNeg` (immediate from `lemma2`), and that
the resulting typing is indeed correct (immediate from `proposition1`).
-/

namespace ShexLean

/-- Definition 5 (maximal correct typing). `Typing(G, S)`: pick any
stratification witnessing `S.StratNeg` (its exact identity is
irrelevant by `maximalCorrTyping_eq_MTyping` below) and take
`Typing(G, S, str)` (Definition 4, `MTyping`). -/
noncomputable def Schema.maximalCorrTyping (S : Schema) (hStrat : S.StratNeg)
    (G : Graph) : Typing :=
  MTyping G S hStrat.some

/-- Definition 5 does not depend on which stratification is used to compute
it: `Typing(G, S)` agrees with `Typing(G, S, str)` for *every*
stratification `str` of `S`, not just the one `Classical.choice` happened
to pick. This is exactly Lemma 2. -/
theorem Schema.maximalCorrTyping_eq_MTyping (S : Schema) (hClosed : S.Closed)
    (hStrat : S.StratNeg) (G : Graph) (str : Strat S) :
    S.maximalCorrTyping hStrat G = MTyping G S str :=
  lemma2 S hClosed hStrat.some str G

/-- Definition 5's `Typing(G, S)` is a correct typing of `G` by `S`
(Definition 2). Immediate from Proposition 1 applied to whichever
stratification underlies `S.maximalCorrTyping`. -/
theorem Schema.maximalCorrTyping_correct (S : Schema) (hClosed : S.Closed)
    (hStrat : S.StratNeg) (G : Graph) :
    S.CorrTyping G (S.maximalCorrTyping hStrat G) :=
  proposition1 S hStrat.some hClosed G

/-- Definition 6 (`SHAPES_SEM`). Node `n` (of `G`) has shape `L` (from `S`)
iff `(n, L) ∈ Typing(G, S)`, i.e. `(n, L)` belongs to the maximal correct
t of `G` by `S` (Definition 5). -/
def Schema.ShapesSem (S : Schema) (hStrat : S.StratNeg)
    (G : Graph) (n : RDFNode) (L : Label) : Prop :=
  (n, L) ∈ S.maximalCorrTyping hStrat G

/-- `SHAPES_SEM` does not depend on which stratification witnesses
`S.StratNeg`: it can equivalently be tested against
`Typing(G, S, str)` for *any* stratification `str` of `S`. This is what
makes Definition 6 well-defined at all, and is exactly why Definitions 5
and 6 needed Lemma 2 first. -/
theorem Schema.shapesSem_iff_typing4 (S : Schema) (hClosed : S.Closed)
    (hStrat : S.StratNeg) (G : Graph) (n : RDFNode) (L : Label)
    (str : Strat S) :
    S.ShapesSem hStrat G n L ↔ (n, L) ∈ MTyping G S str := by
  unfold Schema.ShapesSem
  rw [S.maximalCorrTyping_eq_MTyping hClosed hStrat G str]

end ShexLean
