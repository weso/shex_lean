import ShexLean.Common.RDF

/-!
Helpers for disjoint unions of `Finset Triple`. These helpers do not
depend on a paper.

Both papers use them in the `⊨` relation (triple-expression matching),
for the `;` and `*` constructs:

* 2017: the rules te-each-of and te-repet
  (`ShexLean/Shex2017Schemas/Semantics.lean`).
* 2025: the equivalent rules of Table 1
  (`ShexLean/Shex2025Inheritance/Semantics.lean`).

These definitions were first in the 2017 `Semantics.lean`. They are now in
a separate file. Thus, the 2025 files do not have to import all of the
2017 `Semantics.lean` for two definitions.
-/

namespace ShexLean

/-- `N = N1 ⊎ N2`: `N1` and `N2` are disjoint, and their union is `N`.
This is the binary disjoint union of the rule te-each-of. -/
def DisjointUnion (N N1 N2 : Finset Triple) : Prop :=
  Disjoint N1 N2 ∧ N = N1 ∪ N2

/-- `N = N1 ⊎ ⋯ ⊎ Nk`: the sets in `Ns` are pairwise disjoint, and their
union is `N`. This is the `k`-ary disjoint union of the rule te-repet. -/
def DisjointUnionList (N : Finset Triple) (Ns : List (Finset Triple)) : Prop :=
  Ns.Pairwise Disjoint ∧ N = Ns.foldr (· ∪ ·) ∅

end ShexLean
