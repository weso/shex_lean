import ShexLean.Shex2017Schemas.examples.Example6_prove_motivation
import ShexLean.Shex2017Schemas.Render
import Example

/-!
Example 7 from Boneva, Labra Gayo, Prud'hommeaux (2017) (§4.2): the full
execution trace of `prove(ex:n1, <L1>, [])` (Algorithm 2) on `G₃` and `S₃`
from Example 6 (`Example6_prove_motivation.lean`).

* The recursive calls `prove(ex:n2,<L2>,_)` and `prove(ex:n3,<L3>,_)`
  return `true`.
* The recursive calls `prove(ex:n2,<Str>,_)`, `prove(4,<L2>,_)` and
  `prove(4,<Str>,_)` return `false`.

`Algorithm2.lean` formalizes `prove` and proves Proposition 2. But that
`prove` decides `⊢` with classical logic. Thus, it does not run. The
declarative semantics `⊢` and `⊨` (Fig. 2) are decidable
(`ShexLean.Shex2017Schemas.Decidable`). The trace of Example 7 is only
about the result of the declarative semantics for each call.

This file gives the three `false` results of the trace as theorems. The
`Example` below computes all six results, also the `true` results, with
`native_decide`. Nobody copied them from the paper by hand.
-/

namespace Examples.ProveAlgorithmExample

open ShexLean
open Examples.StratificationExample (S₃)

/-! ### The negative facts of the trace of Example 7

These are the recursive calls of `prove(ex:n1, <L1>, [])` that return
`false`:

* `ex:n2` never has the type `<Str>`. It is an IRI, and the value set of
  `<Str>` contains only a placeholder string literal. (Refer to the module
  docstring of `StratificationExample`.)
* `4` has neither shape. It is not the placeholder string literal. Also,
  it is a literal, so it has no outgoing triples. Thus, it can never match
  the neighbourhood description `ex:c @<L3>` of `<L2>`. -/

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

/-- Each line of the trace below is `renderDecide (satisfies_decidable …)`.
This is a `Decidable` computation of `Satisfies` at the node and the shape
of each call. It is not a value copied from the paper. -/
private def sat (n : ShexLean.RDFNode) (L : ShexLean.Label) : String :=
  renderDecide (satisfies_decidable G₃ t n (S₃.shapeDef L))

/-- Example 7: the execution trace of `prove(ex:n1, <L1>, [])` on `G₃` and
`S₃`. -/
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
