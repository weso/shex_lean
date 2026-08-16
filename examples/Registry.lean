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
import ShexLean.InductiveRDF.DecidablePayoff

/-!
The list of examples the `shex_lean` executable can `list`/`run`.

The `DecidablePayoff` import has no effect on `all`/`find?` below (it
registers no `Example`) — it's imported purely so `lake build` actually
type-checks its `native_decide` regression checks; nothing else in the
repo imports that file, and unlike `ProofRegistry.lean`'s entries (whose
source is read live from disk by *path*, never imported as a module),
plain unreferenced modules aren't reachable from any build target unless
something imports them somewhere.
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
    inheritance2025WellDefined]

/-- Look up a registered example by name. -/
def find? (name : String) : Option Example :=
  all.find? (·.name == name)

end Examples
