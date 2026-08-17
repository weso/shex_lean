import ShexLean.Shex2017Schemas.MaximalTyping
import ShexLean.Shex2017Schemas.examples.Example5_stratification
import ShexLean.Shex2017Schemas.Render
import Example

/-!
Example 6 from Boneva, Labra Gayo, Prud'hommeaux (2017) (§4.2). Example 6
introduces a new graph `G₃`, alongside `S₃` from Example 5
(`Examples.StratificationExample.S₃`), to motivate the `prove` algorithm
(Algorithm 2): does `ex:n1` have shape `<L1>`?

`Satisfies`/`Matches` are `Prop`s over infinite types (`RDFNode`, `IRI :=
String`), so Algorithm 2 itself was never literally executable via
`Satisfies`/`Matches` as *stated* (per `ShexLean.Shex2017Schemas.
Semantics`'s own module docstring) — but `ShexLean.Shex2017Schemas.Decidable`
now provides genuine, kernel-reducible `Decidable` instances for both,
bounding every existential to the finite graph/typing at hand. This file
proves Example 6's headline claim the traditional way, at the level of the
declarative semantics (`⊢`/`⊨`, Fig. 2): `typing = {(ex:n1,<L1>),
(ex:n2,<L2>), (ex:n3,<L3>)}` is a correct typing of `G₃` by `S₃`
(`typing_correct`) — and the `Example` at the bottom additionally *runs*
that same claim via `native_decide`, rather than only asserting it in
prose. Example 7's execution trace of `prove(ex:n1,<L1>,[])` on this same
`G₃`/`S₃` (`Example7_trace.lean`) reuses every definition here.
-/

namespace Examples.ProveAlgorithmExample

open ShexLean
open Examples.StratificationExample (S₃)

-- Not `private`: `Example7_trace.lean` reuses all of these.
def n1 : Subject := .iri "n1"
def n2 : Subject := .iri "n2"
def n3 : Subject := .iri "n3"
def four : RDFNode := .lit (.int 4)

def a : IRI := "ex:a"
def b : IRI := "ex:b"
def c : IRI := "ex:c"

def t1 : Triple := ⟨n1, a, n2⟩
def t2 : Triple := ⟨n1, b, four⟩
def t3 : Triple := ⟨n2, c, n3⟩
def t4 : Triple := ⟨n3, c, n2⟩

/-- `G₃` from Example 6. -/
def G₃ : Graph := {t1, t2, t3, t4}

-- The same shape-label aliases as `Examples.StratificationExample` (same
-- string values, so `S₃.shapeDef` — defined there against *its own*
-- `L1`/`L2`/`L3`/`Str` — unfolds against these identically).
def L1 : ShapeLabel := "L1"
def L2 : ShapeLabel := "L2"
def L3 : ShapeLabel := "L3"
def Str : ShapeLabel := "Str"

-- `rfl` (not `simp`) is needed here: `S₃.shapeDef`'s `if`-chain compares
-- against `Examples.StratificationExample`'s own (private, so not
-- nameable here) `L1`/`L2`/`L3`/`Str` constants. `rfl` unfolds through
-- private `abbrev` definitions via full definitional equality regardless
-- of accessibility, whereas `simp` needs each unfolded constant named
-- explicitly in its argument list.
theorem shapeDef_L1 :
    S₃.shapeDef L1 =
      .not (.neigDescr (.eachOf (.tPattern {a} L2) (.tPattern {b} Str))) := rfl

theorem shapeDef_L2 : S₃.shapeDef L2 = .neigDescr (.tPattern {c} L3) := rfl

theorem shapeDef_L3 : S₃.shapeDef L3 = .neigDescr (.tPattern {c} L2) := rfl

theorem shapeDef_Str : S₃.shapeDef Str = .valueDescr {.lit (.str "placeholder")} := rfl

/-- The typing witnessing `ex:n1 ⊢ <L1>` (Example 6's claim), reusing
`S₃`'s three cyclic labels. -/
def typing : Typing := {((n1 : RDFNode), L1), ((n2 : RDFNode), L2), ((n3 : RDFNode), L3)}

theorem satisfies_L2_n2 : Satisfies G₃ typing n2 (S₃.shapeDef L2) := by
  rw [shapeDef_L2]
  show Matches G₃ typing (neigh G₃ n2) _
  have hneigh : neigh G₃ n2 = {t3} := by decide
  rw [hneigh]
  exact ⟨n2, c, n3, rfl, by decide, by decide⟩

theorem satisfies_L3_n3 : Satisfies G₃ typing n3 (S₃.shapeDef L3) := by
  rw [shapeDef_L3]
  show Matches G₃ typing (neigh G₃ n3) _
  have hneigh : neigh G₃ n3 = {t4} := by decide
  rw [hneigh]
  exact ⟨n3, c, n2, rfl, by decide, by decide⟩

/-- `ex:n1 ⊢ <L1>` (Example 6's headline claim): `<L1> = NOT(ex:a @<L2> ;
ex:b @<Str>)`, and the `eachOf` fails because `n1`'s unique `ex:b`
neighbour, `4`, is never typed `<Str>` by `typing`. -/
theorem satisfies_L1_n1 : Satisfies G₃ typing n1 (S₃.shapeDef L1) := by
  rw [shapeDef_L1]
  show ¬ Satisfies G₃ typing n1 _
  intro hsat
  have hmatch : Matches G₃ typing (neigh G₃ n1) _ :=
    (show Matches G₃ typing (neigh G₃ n1) _ from hsat)
  have hneigh : neigh G₃ n1 = {t1, t2} := by decide
  rw [hneigh] at hmatch
  obtain ⟨N1, N2, ⟨-, hunion⟩, -, hN2⟩ := hmatch
  obtain ⟨subj, pred, obj, hN2eq, hpred, hty⟩ := hN2
  have hmemN2 : (⟨subj, pred, obj⟩ : Triple) ∈ ({t1, t2} : Finset Triple) := by
    rw [hunion]; exact Finset.mem_union_right _ (hN2eq ▸ Finset.mem_singleton_self _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmemN2
  have hpredEq : pred = b := by simpa using hpred
  rcases hmemN2 with heq | heq
  · have hpredEq2 : pred = a := by
      have : (⟨subj, pred, obj⟩ : Triple).pred = t1.pred := by rw [heq]
      simpa [t1] using this
    rw [hpredEq2] at hpredEq
    exact absurd hpredEq (by decide)
  · have hobjEq : obj = four := by
      have : (⟨subj, pred, obj⟩ : Triple).obj = t2.obj := by rw [heq]
      simpa [t2] using this
    rw [hobjEq] at hty
    exact absurd hty (by decide)

/-- `typing` is a correct typing of `G₃` by `S₃` (Definition 2). -/
theorem typing_correct : S₃.CorrectTyping G₃ typing := by
  intro n L hmem
  simp only [typing, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ <;> subst hn <;> subst hL
  · exact satisfies_L1_n1
  · exact satisfies_L2_n2
  · exact satisfies_L3_n3

end Examples.ProveAlgorithmExample

namespace Examples

open Examples.ProveAlgorithmExample (G₃ typing n1 L1)
open Examples.StratificationExample (S₃)
open ShexLean (Schema.render Graph.render Typing.render renderDecide correctTyping_decidable
  satisfies_decidable)

/-- Example 6: motivating `G₃` for Algorithm 2, showing `ex:n1` has shape
`<L1>` under `S₃`. `schemaText`/`graphText`/`typingText`'s correctness
verdict are generated from the real `S₃`/`G₃`/`typing` values; the
headline "`ex:n1` has shape `<L1>`" claim is a `native_decide`
computation of `Satisfies G₃ typing n1 (S₃.shapeDef L1)` itself, not
prose. -/
def proveAlgorithmMotivation : Example where
  name := "schemas2017-example6-prove-motivation"
  summary := "Motivating graph G₃ for Algorithm 2: ex:n1 has shape <L1> under S₃."
  schemaText := Schema.render S₃
  graphText := Graph.render G₃
  typingText :=
    s!"typing = {Typing.render typing}   " ++
      s!"(correct = {renderDecide (correctTyping_decidable S₃ G₃ typing)})\n\n" ++
    s!"ex:n1 has shape <L1> = " ++
      s!"{renderDecide (satisfies_decidable G₃ typing n1 (S₃.shapeDef L1))}"

end Examples
