import ShexLean.Shex2017Schemas.Lemma2

/-!
Definitions 5 and 6 (§3.3):

* Definition 5: the maximal correct typing of `G` by `S`.
* Definition 6: `SHAPES_SEM`.
  This is the statement that all of the development since §3.1 prepares:

> SHAPES_SEM: node `n` in graph `G` has shape (or type) `L` from schema `S`

In the paper, each definition is one line.
Each definition uses two results directly:

* Proposition 1: `Typing(G, S, str)` is always a correct
  typing (`ShexLean/Shex2017Schemas/Proposition1.lean`).
* Lemma 2: `Typing(G, S, str)` does not depend on `str` (`ShexLean/Shex2017Schemas/Lemma2.lean`).

> Definition 5 (maximal correct typing). Let `S = (L, def)` be a schema and
> `G` be a graph. The maximal correct typing of `G` by `S` is denoted
> `Typing(G, S)` and is defined as `Typing(G, S, str)` for some
> stratification `str` of `S`.
>
> Definition 6 (shapes_sem). Let `S = (L, def)` be a schema and `G` be a
> graph. We say that node `n` (of `G`) has shape `L` (from `S`) if
> `(n, L) ∈ Typing(G, S)`.

This file must show only two facts:

* Definition 5 is well-defined.
  The result does not depend on the stratification
  that `Classical.choice` selects from `S.StratNeg`.
  This follows directly from `lemma2`.
* The typing of Definition 5 is correct.
  This follows directly from `proposition1`.
-/

namespace ShexLean

/-- Definition 5 (maximal correct typing).
`Typing(G, S)`: select a stratification that is a witness of `S.StratNeg`,
and then take `Typing(G, S, str)` (Definition 4, `MTyping`).
The selected stratification has no effect on the result (`maximalCorrTyping_eq_MTyping` below). -/
noncomputable def Schema.maximalCorrTyping (S : Schema) (hStrat : S.StratNeg)
    (G : Graph) : Typing :=
  MTyping G S hStrat.some

/-- Definition 5 does not depend on the stratification that computes it.
`Typing(G, S)` is equal to `Typing(G, S, str)` for
*each* stratification `str` of `S`, not only for
the stratification that `Classical.choice` selects.
This is exactly Lemma 2. -/
theorem Schema.maximalCorrTyping_eq_MTyping (S : Schema) (hClosed : S.Closed)
    (hStrat : S.StratNeg) (G : Graph) (str : Strat S) :
    S.maximalCorrTyping hStrat G = MTyping G S str :=
  lemma2 S hClosed hStrat.some str G

/-- `Typing(G, S)` of Definition 5 is a correct typing of `G` by `S` (Definition 2).
This follows directly from Proposition 1, applied to
the stratification that `S.maximalCorrTyping` uses. -/
theorem Schema.maximalCorrTyping_correct (S : Schema) (hClosed : S.Closed)
    (hStrat : S.StratNeg) (G : Graph) :
    S.CorrTyping G (S.maximalCorrTyping hStrat G) :=
  proposition1 S hStrat.some hClosed G

/-- Definition 6 (`SHAPES_SEM`).
The node `n` (of `G`) has the shape `L` (from `S`) if and only if `(n, L) ∈ Typing(G, S)`.
Thus, `(n, L)` is in the maximal correct typing of `G` by `S` (Definition 5). -/
def Schema.ShapesSem (S : Schema) (hStrat : S.StratNeg)
    (G : Graph) (n : RDFNode) (L : Label) : Prop :=
  (n, L) ∈ S.maximalCorrTyping hStrat G

/-- `SHAPES_SEM` does not depend on the stratification that is a witness of `S.StratNeg`.
You can test it with `Typing(G, S, str)` for *any*
stratification `str` of `S`, and get the same result.
This fact makes Definition 6 well-defined.
It is the reason why Definitions 5 and 6 need Lemma 2 first. -/
theorem Schema.shapesSem_iff_typing4 (S : Schema) (hClosed : S.Closed)
    (hStrat : S.StratNeg) (G : Graph) (n : RDFNode) (L : Label)
    (str : Strat S) :
    S.ShapesSem hStrat G n L ↔ (n, L) ∈ MTyping G S str := by
  unfold Schema.ShapesSem
  rw [S.maximalCorrTyping_eq_MTyping hClosed hStrat G str]

end ShexLean
