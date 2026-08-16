import ShexLean.InductiveRDF.Decidable
import ShexLean.Shex2017Schemas.examples.Example1_introduction
import ShexLean.Shex2017Schemas.examples.Example6_prove_motivation

/-!
Payoff for `Decidable.lean`'s `satisfies_decidable`/`matches_decidable`:
facts proved by hand elsewhere in this repo, re-derived here by nothing but
`native_decide`. Split out from `Decidable.lean` itself so that file stays
free of any `examples/` import (avoiding a cycle once example files import
it too, e.g. via the rendering layer built on top of it).

This file predates that rendering layer and was the original proof-of-
concept for the `@of_decide_eq_true` pattern below — it's since become the
*standard* way every worked example in this repo states its claims:
`ShexLean/Shex2017Schemas/Render.lean`'s `renderDecide` and
`ShexLean/Shex2025Inheritance/Render.lean`'s (reusing the same
`renderDecide`) apply the identical pattern across all 14
`Shex2017Schemas/examples/*.lean` + `Shex2025Inheritance/examples/*.lean`
files, so `schemaText`/`graphText`/`typingText` display genuinely computed
`true`/`false` verdicts rather than hand-transcribed prose. Kept as its own
small file rather than folded into an example, since its point is
specifically to show the same three-line pattern working — no `Example`
registration, no display text, just the bare re-derivations.
-/

/-! ### Example 7's `false` outcomes, `decide`d instead of proved

`S₃`'s shapes (`shapeDef_L1`/`L2`/`L3`/`Str`, `Example6_prove_motivation.lean`)
never use `.rep`, so `satisfies_decidable` applies to all of them — three
of Example 7's `false` outcomes (`Example7_trace.lean`'s
`n2_not_Str`/`four_not_Str`/`four_not_L2`, currently proved by hand via
`rw` + manual `Finset`/`Matches` construction) are re-derived here by
nothing but `native_decide`. -/

namespace Examples.ProveAlgorithmExample

open ShexLean ShexLean.InductiveRDF
open Examples.StratificationExample (S₃)

-- The `Decidable` instance is passed *explicitly* (via `@…`) rather than
-- through `haveI` + tactic `decide`/`native_decide`: `haveI` leaves a local
-- hypothesis in the proof term, and neither the kernel (`decide`) nor the
-- native compiler (`native_decide`) will reduce/compile through a local
-- variable — only a fully closed, ground instance term works.
example : ¬ Satisfies G₃ typing n2 (S₃.shapeDef Str) :=
  @of_decide_eq_true _
    (@instDecidableNot _ (satisfies_decidable G₃ typing n2 (S₃.shapeDef Str)))
    (by native_decide)

example : ¬ Satisfies G₃ typing four (S₃.shapeDef Str) :=
  @of_decide_eq_true _
    (@instDecidableNot _ (satisfies_decidable G₃ typing four (S₃.shapeDef Str)))
    (by native_decide)

example : ¬ Satisfies G₃ typing four (S₃.shapeDef L2) :=
  @of_decide_eq_true _
    (@instDecidableNot _ (satisfies_decidable G₃ typing four (S₃.shapeDef L2)))
    (by native_decide)

end Examples.ProveAlgorithmExample

/-! ### A genuine `.rep _ 0 none` case, `decide`d too

`Example1_introduction.lean`'s `progShapeDef` (`<ProgShape> →
ex:expertise @<IRIValue> [0;*] ; ex:experience @<ExpValueSet>`) has an
*unbounded* `.rep` — exactly the case `RepBound.lean`'s
`matches_rep_iff_bounded` was built for. `satisfies_progShape_ren` (proved
there by ~15 lines of manual `refine`/`decide` unpacking of the nested
`.eachOf`/`.rep` witnesses) is re-derived here by nothing but
`native_decide`. -/

namespace Examples.Introduction

open ShexLean ShexLean.InductiveRDF

example : Satisfies G₀ typing2 ren progShapeDef :=
  @of_decide_eq_true _ (satisfies_decidable G₀ typing2 ren progShapeDef) (by native_decide)

end Examples.Introduction
