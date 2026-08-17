import ShexLean.Shex2017Schemas.examples.Example6_prove_motivation
import ShexLean.Shex2017Schemas.Render
import Example

/-!
Example 7 from Boneva, Labra Gayo, Prud'hommeaux (2017) (§4.2): the full
execution trace of `prove(ex:n1, <L1>, [])` (Algorithm 2) on `G₃`/`S₃`
from Example 6 (`Example6_prove_motivation.lean`): the recursive calls
`prove(ex:n2,<L2>,_)`/`prove(ex:n3,<L3>,_)` return `true`, while
`prove(ex:n2,<Str>,_)`/`prove(4,<L2>,_)`/`prove(4,<Str>,_)` return `false`.

Algorithm 2's own recursive `prove` function isn't formalized/executable
here (per Example 6's own module docstring — the paper's algorithm and
the declarative `⊢`/`⊨` semantics, Fig. 2, are two different things,
related only by Proposition 2, which lives in a different, unported part
of the paper). But `⊢`/`⊨` themselves *are* now decidable
(`ShexLean.Shex2017Schemas.Decidable`), and Example 7's own trace is entirely
about the declarative semantics' verdict on each call, so this file
reproduces the trace's three `false` outcomes as theorems (as before, for
the record) *and* the `Example` below now computes all six outcomes —
`true`s included — via `native_decide`, rather than transcribing them from
the paper by hand.
-/

namespace Examples.ProveAlgorithmExample

open ShexLean
open Examples.StratificationExample (S₃)

/-! ### Example 7's negative trace facts

`prove(ex:n1, <L1>, [])`'s recursive calls that return `false`: `ex:n2` is
never typed `<Str>` (it's an IRI, and `<Str>`'s value set only contains a
placeholder string literal — see `StratificationExample`'s own module
docstring), and `4` has neither shape (it's not the placeholder string
literal either, and, being a literal, has no outgoing triples, so it can
never match `<L2>`'s own `ex:c @<L3>` neighbourhood description). -/

theorem n2_not_Str : ¬ Satisfies G₃ t n2 (S₃.shapeDef Str) := by
  rw [shapeDef_Str]
  rintro (h | h) <;> exact absurd h (by decide)

theorem four_not_Str : ¬ Satisfies G₃ t four (S₃.shapeDef Str) := by
  rw [shapeDef_Str]
  rintro (h | h) <;> exact absurd h (by decide)

theorem four_not_L2 : ¬ Satisfies G₃ t four (S₃.shapeDef L2) := by
  rw [shapeDef_L2]
  intro hsat
  have hmatch : Matches G₃ t (neigh G₃ four) _ :=
    (show Matches G₃ t (neigh G₃ four) _ from hsat)
  have hneigh : neigh G₃ four = (∅ : Finset Triple) := by decide
  rw [hneigh] at hmatch
  obtain ⟨subj, pred, obj, heq, -, -⟩ := hmatch
  exact absurd heq.symm (Finset.singleton_ne_empty _)

end Examples.ProveAlgorithmExample

namespace Examples

open Examples.ProveAlgorithmExample (G₃ t n1 n2 n3 four L1 L2 L3 Str)
open Examples.StratificationExample (S₃)
open ShexLean (Schema.render Graph.render renderDecide satisfies_decidable)

/-- Every line of the trace below is `renderDecide (satisfies_decidable …)`
— an actual `Decidable` computation of `Satisfies` at each call's node and
shape, not a value transcribed from the paper. -/
private def sat (n : ShexLean.RDFNode) (L : ShexLean.Label) : String :=
  renderDecide (satisfies_decidable G₃ t n (S₃.shapeDef L))

/-- Example 7: the execution trace of `prove(ex:n1, <L1>, [])` on `G₃`/`S₃`. -/
def proveAlgorithmTrace : Example where
  name := "schemas2017-example7-trace"
  summary := "Execution trace of prove(ex:n1,<L1>,[]) (Algorithm 2) on G₃/S₃."
  schemaText := Schema.render S₃
  graphText := Graph.render G₃
  typingText :=
    s!"prove(ex:n1, <L1>, [])                                            = {sat n1 L1}\n" ++
    s!"|-prove(ex:n2, <L2>, [(ex:n1,<L1>)])                                = {sat n2 L2}\n" ++
    s!"| |-prove(ex:n3, <L3>, [(ex:n1,<L1>),(ex:n2,<L2>)])                   = {sat n3 L3}\n" ++
    s!"|-prove(ex:n2, <Str>, [(ex:n1,<L1>)])                               = {sat n2 Str}\n" ++
    s!"|-prove(4, <L2>, [(ex:n1,<L1>)])                                    = {sat four L2}\n" ++
    s!"|-prove(4, <Str>, [(ex:n1,<L1>)])                                   = {sat four Str}\n\n" ++
    "dep(ex:n1,<L1>) pairs both of <L1>'s neighbours (ex:n2, 4) with both\n" ++
    "shape labels <L1> references (<L2>, <Str>), even though only one\n" ++
    "combination is actually meaningful — the algorithm's own imprecision,\n" ++
    "noted by the paper right after Example 7."

end Examples
