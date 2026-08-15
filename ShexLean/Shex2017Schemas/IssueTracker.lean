import Example

/-!
Display data for `ShexLean.Examples`'s Example 2/3 (Boneva, Labra Gayo,
Prud'hommeaux 2017): the recursive `<IssueSh>`/`<Str>` schema, proved
correct there as `typing1_correct`. This file only carries the text shown by
the executable; the proof itself lives in `ShexLean/Shex2017Schemas/Examples.lean`.
-/

namespace Examples

/-- The `<IssueSh>`/`<Str>` example from Example 2/3. -/
def issueTracker : Example where
  name := "issue-tracker"
  summary := "Example 2/3: a recursive <IssueSh> schema over two issues that report on each other."
  schemaText :=
    "<IssueSh> → is:reportedBy @<Str> ; is:relatedTo @<IssueSh> [0;*]\n" ++
    "<Str>     → xsd:string"
  graphText :=
    "<i1> is:reportedBy \"Ren\" ; is:relatedTo <i2> .\n" ++
    "<i2> is:reportedBy \"Bob\" ; is:relatedTo <i1> ."
  typingText :=
    "{(<i1>, <IssueSh>), (<i2>, <IssueSh>), (\"Ren\", <Str>), (\"Bob\", <Str>)}"

end Examples
