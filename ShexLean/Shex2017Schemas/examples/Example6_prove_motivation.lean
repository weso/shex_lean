import ShexLean.Shex2017Schemas.MaximalTyping
import ShexLean.Shex2017Schemas.examples.Example5_stratification
import ShexLean.Shex2017Schemas.Render
import Example

/-!
Example 6 from Boneva, Labra Gayo, Prud'hommeaux (2017) (§4.2). Example 6
gives a new graph `G₃`, together with `S₃` from Example 5
(`Examples.StratificationExample.S₃`). It is the motivation for the
`prove` algorithm (Algorithm 2). The question is: does `ex:n1` have the
shape `<L1>`?

`Satisfies` and `Matches` are `Prop`s over infinite types (`RDFNode`, and
`IRI := String`). `ShexLean.Shex2017Schemas.Decidable` gives
kernel-reducible `Decidable` instances for the two relations. These
instances bound each existential to the finite graph and typing.

This file proves the main claim of Example 6 in the usual way, at the
level of the declarative semantics (`⊢` and `⊨`, Fig. 2). The claim is
that `t = {(ex:n1,<L1>), (ex:n2,<L2>), (ex:n3,<L3>)}` is a correct typing
of `G₃` by `S₃` (`typing_correct`). The `Example` at the end of the file
also computes this claim with `native_decide`.

Example 7 (`Example7_trace.lean`) gives the execution trace of
`prove(ex:n1,<L1>,[])` on the same `G₃` and `S₃`. It uses all the
definitions of this file.
-/

namespace Examples.ProveAlgorithmExample

open ShexLean
open Examples.StratificationExample (S₃)

-- These definitions are not `private`, because `Example7_trace.lean` uses all of them.
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

-- The same shape-label aliases as in `Examples.StratificationExample`. They have
-- the same string values. Thus, `S₃.shapeDef`, which uses the `L1`, `L2`, `L3`
-- and `Str` of that file, unfolds in the same way with these aliases.
def L1 : Label := "L1"
def L2 : Label := "L2"
def L3 : Label := "L3"
def Str : Label := "Str"

-- Use `rfl` here, not `simp`. The `if` chain of `S₃.shapeDef` compares with
-- the constants `L1`, `L2`, `L3` and `Str` of `Examples.StratificationExample`.
-- These constants are private, so this file cannot use their names. `rfl`
-- unfolds private `abbrev` definitions with full definitional equality, and
-- does not look at accessibility. `simp` needs the name of each unfolded
-- constant in its argument list.
theorem shapeDef_L1 :
    S₃.shapeDef L1 =
      .not (.neigDescr (.eachOf (.tPattern {a} L2) (.tPattern {b} Str))) := rfl

theorem shapeDef_L2 : S₃.shapeDef L2 = .neigDescr (.tPattern {c} L3) := rfl

theorem shapeDef_L3 : S₃.shapeDef L3 = .neigDescr (.tPattern {c} L2) := rfl

theorem shapeDef_Str : S₃.shapeDef Str = .valueDescr {.lit (.str "placeholder")} := rfl

/-- The `t` that is the witness of `ex:n1 ⊢ <L1>` (the claim of Example 6).
It uses the three cyclic labels of `S₃`. -/
def t : Typing := {((n1 : RDFNode), L1), ((n2 : RDFNode), L2), ((n3 : RDFNode), L3)}

theorem satisfies_L2_n2 : Satisfies G₃ t n2 (S₃.shapeDef L2) := by
  rw [shapeDef_L2]
  show Matches G₃ t (neigh G₃ n2) _
  have hneigh : neigh G₃ n2 = {t3} := by decide
  rw [hneigh]
  exact ⟨n2, c, n3, rfl, by decide, by decide⟩

theorem satisfies_L3_n3 : Satisfies G₃ t n3 (S₃.shapeDef L3) := by
  rw [shapeDef_L3]
  show Matches G₃ t (neigh G₃ n3) _
  have hneigh : neigh G₃ n3 = {t4} := by decide
  rw [hneigh]
  exact ⟨n3, c, n2, rfl, by decide, by decide⟩

/-- `ex:n1 ⊢ <L1>` (the main claim of Example 6).
`<L1> = NOT(ex:a @<L2> ; ex:b @<Str>)`. The `eachOf` fails, because `n1`
has only one `ex:b` neighbour, `4`, and `t` never gives the type `<Str>`
to `4`. -/
theorem satisfies_L1_n1 : Satisfies G₃ t n1 (S₃.shapeDef L1) := by
  rw [shapeDef_L1]
  show ¬ Satisfies G₃ t n1 _
  intro hsat
  have hmatch : Matches G₃ t (neigh G₃ n1) _ :=
    (show Matches G₃ t (neigh G₃ n1) _ from hsat)
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

/-- `t` is a correct typing of `G₃` by `S₃` (Definition 2). -/
theorem typing_correct : S₃.CorrTyping G₃ t := by
  intro n L hmem
  simp only [t, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨hn, hL⟩ | ⟨hn, hL⟩ | ⟨hn, hL⟩ <;> subst hn <;> subst hL
  · exact satisfies_L1_n1
  · exact satisfies_L2_n2
  · exact satisfies_L3_n3

end Examples.ProveAlgorithmExample

namespace Examples

open Examples.ProveAlgorithmExample (G₃ t n1 L1)
open Examples.StratificationExample (S₃)
open ShexLean (Schema.render Graph.render Typing.render renderDecide corrTyping_decidable
  satisfies_decidable)

/-- Example 6: the graph `G₃`, which is the motivation for Algorithm 2. It
shows that `ex:n1` has the shape `<L1>` with `S₃`.

* `schemaText`, `graphText` and the correctness result in `typingText` are
  generated from the real values `S₃`, `G₃` and `t`.
* The main claim "`ex:n1` has shape `<L1>`" is a `native_decide`
  computation of `Satisfies G₃ t n1 (S₃.shapeDef L1)`. It is not
  text. -/
def proveAlgorithmMotivation : Example where
  name := "schemas2017-example6-prove-motivation"
  summary := "Motivating graph G₃ for Algorithm 2: ex:n1 has shape <L1> with S₃."
  schemaText := Schema.render S₃
  graphText := Graph.render G₃
  typingText :=
    s!"t = {Typing.render t}   " ++
      s!"(correct = {renderDecide (corrTyping_decidable S₃ G₃ t)})\n\n" ++
    s!"ex:n1 has shape <L1> = " ++
      s!"{renderDecide (satisfies_decidable G₃ t n1 (S₃.shapeDef L1))}"

end Examples
