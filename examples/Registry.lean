import ShexLean.Shex2017Schemas.IssueTracker
import ShexLean.Shex2017Schemas.Introduction
import ShexLean.Shex2017Schemas.NegationRecursion
import ShexLean.Shex2017Schemas.StratificationExample

/-!
The list of examples the `shex_lean` executable can `list`/`run`.
-/

namespace Examples

/-- All examples registered for the executable's `list`/`run` commands. -/
def all : List Example := [issueTracker, introduction, negationRecursion, stratificationExample]

/-- Look up a registered example by name. -/
def find? (name : String) : Option Example :=
  all.find? (·.name == name)

end Examples
