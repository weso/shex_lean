# Writing style

The comments, docstrings, CLI descriptions and Markdown files of this
repository use a style based on Simplified Technical English
(ASD-STE100). The goal is text that is easy to read for all readers,
also for readers whose first language is not English.

Use these rules when you write or change a comment.

## Sentences

1. Write one topic in each sentence.
2. Keep sentences short: 20 words or fewer for instructions, and 25 words
   or fewer for descriptions. Formulas and Lean names do not count.
3. Keep paragraphs short: 6 sentences or fewer.
4. Use a list when you have three or more items, conditions or steps.
   Use a numbered list for steps in a sequence.
5. Use the active voice when possible ("`refine1` computes the typing",
   not "the typing is computed by `refine1`").
6. Use simple tenses. Use the present tense for facts about the code.
7. Write instructions in the imperative ("Use `rfl` here, not `simp`.").

## Words

1. Do not use contractions. Write "does not", not "doesn't".
2. Do not use Latin abbreviations. Write "for example", not "e.g.", and
   "thus", not "i.e.".
3. Write "if and only if" in prose. Keep "iff" only in quoted text and
   formulas.
4. Do not use a dash (`—`) to add a remark in a sentence. Write a new
   sentence, or use parentheses.
5. Do not use filler words such as "genuinely", "actually", "just",
   "simply", "really" or "literally" when they add no meaning.
6. Use one word for one meaning, and use the same word each time. For
   example, always write "typing" for a set of node-type associations,
   and "fuel" for the recursion bound.
7. Use "the X of Y", not long chains of possessives ("the definition of
   `x`", not "`x`'s own definition's body").

## Technical names

1. Put each Lean name, file path and formula in backticks.
2. Keep the notation of the papers (`⊨`, `τ_max(S,σ,G)`, `ext-te(x)`,
   rule numbers, Definition numbers).
3. When you refer to a file, give its full path from the project root,
   for example `ShexLean/Shex2025Inheritance/Semantics.lean`. In the
   `Shex2026InheritanceDisjunction/` copy, refer to the files of that
   directory, not to the 2025 files, unless you compare the two.

## Quotations

Do not change text that is quoted from a paper (lines that start with
`>`). Quotations keep the words of the authors.

## Structure of a docstring

1. The first sentence tells what the definition or theorem is.
2. The next sentences tell why it is necessary, or how the proof works.
3. Put implementation notes (performance, elaboration problems) last.
