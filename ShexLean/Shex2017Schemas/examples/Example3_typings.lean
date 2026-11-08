import ShexLean.Shex2017Schemas.examples.Example2_issue_tracker
import ShexLean.Shex2017Schemas.Render
import Example

/-!
Example 3 from Boneva, Labra Gayo, Prud'hommeaux (2017): the four typings
of `G₂` by `S₁` from Example 2 (`ShexLean.Examples`,
`Example2_issue_tracker.lean`), and which of them are correct
(Definition 2).

Example 3 gives four typings of `G₂` by `S₁`, and tells which typings are
correct:

* `typing_1` is correct. (This is the claim of Example 2. We prove it in
  that file, because the other typings of Example 3 use all of its
  definitions.)
* `typing_2` is correct. The paper says this explicitly: "typing_1 and
  typing_2 are correct".
* `typing_3` is not correct. It gives the type `<IssueSh>` to `<i1>` and
  `<i2>`, but it does not give the type `<Str>` to `"Ren"` and `"Bob"`.
  The definition of `<IssueSh>` needs this.
* `typing_4` is correct.
-/

namespace ShexLean.Examples

open ShexLean

/-- `typing_2` from Example 3: only the two string literals have a
type. -/
def typing2 : Typing := {(ren, Str), (bob, Str)}

/-- `typing_2` is correct. It gives only `<Str>`, and the satisfaction of
`strDef` (`se-value-descr1`) does not depend on `t`. -/
theorem typing2_correct : S₁.CorrTyping G₂ typing2 := by
  intro n L hmem
  simp only [typing2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨hn, hL⟩ | ⟨hn, hL⟩ <;> subst hn <;> subst hL
  · exact satisfies_str ren (Or.inl rfl)
  · exact satisfies_str bob (Or.inr rfl)

/-- `typing_3` from Example 3: `<i1>` and `<i2>` have the type
`<IssueSh>`, but no string literal has the type `<Str>`. -/
def typing3 : Typing := {((i1 : RDFNode), IssueSh), ((i2 : RDFNode), IssueSh)}

/-- `typing_3` is *not* correct (the counterexample of Example 3).
`(<i1>, <IssueSh>) ∈ typing_3`. But `<i1>` has only one `is:reportedBy`
neighbour, `"Ren"`, and `"Ren"` does not have the type `<Str>` in
`typing_3`. Thus, the `is:reportedBy @<Str>` part of the each-of in
`issueShDef` can never match. -/
theorem typing3_not_correct : ¬ S₁.CorrTyping G₂ typing3 := by
  intro hcorrect
  have hsat : Satisfies G₂ typing3 i1 issueShDef :=
    hcorrect i1 IssueSh (by decide)
  have hmatch : Matches G₂ typing3 (neigh G₂ i1) _ :=
    (show Matches G₂ typing3 (neigh G₂ i1) _ from hsat)
  have hneigh : neigh G₂ i1 = {t1, t2} := by decide
  rw [hneigh] at hmatch
  obtain ⟨N1, N2, ⟨-, hunion⟩, hN1, -⟩ := hmatch
  obtain ⟨subj, pred, obj, hN1eq, hpred, hty⟩ := hN1
  have hmemN1 : (⟨subj, pred, obj⟩ : Triple) ∈ ({t1, t2} : Finset Triple) := by
    rw [hunion]; exact Finset.mem_union_left _ (hN1eq ▸ Finset.mem_singleton_self _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmemN1
  have hpredEq : pred = reportedBy := by simpa using hpred
  rcases hmemN1 with heq | heq
  · -- `⟨subj, pred, obj⟩ = t1 = ⟨i1, reportedBy, ren⟩`. Thus, `obj = ren`.
    have hobjEq : obj = ren := by
      have : (⟨subj, pred, obj⟩ : Triple).obj = t1.obj := by rw [heq]
      simpa [t1] using this
    rw [hobjEq] at hty
    exact absurd hty (by decide)
  · -- `⟨subj, pred, obj⟩ = t2 = ⟨i1, relatedTo, i2⟩`. This contradicts `pred = reportedBy`.
    have hpredEq2 : pred = relatedTo := by
      have : (⟨subj, pred, obj⟩ : Triple).pred = t2.pred := by rw [heq]
      simpa [t2] using this
    rw [hpredEq2] at hpredEq
    exact absurd hpredEq (by decide)

/-- `typing_4` from Example 3: the empty typing. It is trivially
correct. -/
def typing4 : Typing := ∅

theorem typing4_correct : S₁.CorrTyping G₂ typing4 := by
  intro n L hmem
  exact absurd hmem (Finset.notMem_empty _)

end ShexLean.Examples

namespace Examples

open ShexLean.Examples (S₁ G₂ typing1 typing2 typing3 typing4)
open ShexLean (Schema.render Graph.render Typing.render renderDecide corrTyping_decidable)

/-- The four typings of `G₂` by `S₁` from Example 3, and their
correctness. `schemaText` and `graphText` are generated from `S₁` and
`G₂`. Each of the four correctness results in `typingText` is a
`Decidable` computation. They are not a "(correct)" or a "(not correct)"
that a person typed by hand. -/
def exampleTypings : Example where
  name := "schemas2017-example3-typings"
  summary := "Four typings of G₂ by S₁ from Ex. 2, and which are correct (Def. 2)."
  schemaText := Schema.render S₁
  graphText := Graph.render G₂
  typingText :=
    let verdict (t : ShexLean.Typing) := renderDecide (corrTyping_decidable S₁ G₂ t)
    s!"typing_1 = {Typing.render typing1}   (correct = {verdict typing1})\n" ++
    s!"typing_2 = {Typing.render typing2}   (correct = {verdict typing2})\n" ++
    s!"typing_3 = {Typing.render typing3}   (correct = {verdict typing3})\n" ++
    s!"typing_4 = {Typing.render typing4}   (correct = {verdict typing4})\n\n" ++
    "typing_3 is not correct: it types <i1> as <IssueSh> without also typing\n" ++
    "its is:reportedBy neighbour \"Ren\" as <Str>, which <IssueSh>'s own\n" ++
    "definition requires."

end Examples
