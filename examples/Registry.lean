import ShexLean.Shex2017Schemas.examples.Example1_introduction
import ShexLean.Shex2017Schemas.examples.Example2_issue_tracker
import ShexLean.Shex2017Schemas.examples.Example3_typings
import ShexLean.Shex2017Schemas.examples.Example4_negation_recursion
import ShexLean.Shex2017Schemas.examples.Example5_stratification
import ShexLean.Shex2017Schemas.examples.Example6_prove_motivation
import ShexLean.Shex2017Schemas.examples.Example7_trace
import ShexLean.Shex2025Inheritance.examples.Example1_figures
import ShexLean.Shex2025Inheritance.examples.Example2_extension_hierarchy
import ShexLean.Shex2025Inheritance.examples.Example3_triple_match
import ShexLean.Shex2025Inheritance.examples.Example4_closed_extra
import ShexLean.Shex2025Inheritance.examples.Example5_extends
import ShexLean.Shex2025Inheritance.examples.Example6_dependency_graph
import ShexLean.Shex2025Inheritance.examples.Example7_well_defined
import ShexLean.Shex2026InheritanceDisjunction.examples.Example1_coloured_circle

/-!
The list of examples the `shex_lean` executable can `list`/`run`.
-/

namespace Examples

/-- All examples registered for the executable's `list`/`run` commands,
ordered by paper and then by example number so the `list` output matches
the papers' own numbering. -/
def all : List Example :=
  [introduction, issueTracker, exampleTypings, negationRecursion, stratificationExample,
    proveAlgorithmMotivation, proveAlgorithmTrace,
    inheritance2025Figures, inheritance2025ExtensionHierarchy, inheritance2025TripleMatch,
    inheritance2025ClosedExtra, inheritance2025Extends, inheritance2025DependencyGraph,
    inheritance2025WellDefined,
    inheritanceDisjunctionColouredCircle]

/-- Look up a registered example by name. -/
def find? (name : String) : Option Example :=
  all.find? (·.name == name)

end Examples
