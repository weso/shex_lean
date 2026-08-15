import ShexLean.Common.RDF

/-!
Paper-independent disjoint-union helpers over `Finset Triple`, used by both
papers' `⊨` (triple-expression matching) relations for their `;`/`*`
constructs: 2017's Rules te-each-of/te-repet
(`ShexLean/Shex2017Schemas/Semantics.lean`) and 2025's analogous Table 1
rules (`ShexLean/Shex2025Inheritance/Semantics.lean`). Split out into its
own file (originally lived at the top of the 2017 `Semantics.lean`) once
the 2025 formalism needed it too, rather than having 2025 import all of
2017's `Semantics.lean` just for these two definitions.
-/

namespace ShexLean

/-- `N = N1 ⊎ N2`: `N1` and `N2` are disjoint and their union is `N`, the
binary disjoint union used in Rule te-each-of. -/
def DisjointUnion (N N1 N2 : Finset Triple) : Prop :=
  Disjoint N1 N2 ∧ N = N1 ∪ N2

/-- `N = N1 ⊎ ⋯ ⊎ Nk`: the sets listed in `Ns` are pairwise disjoint and their
union is `N`, the `k`-ary disjoint union used in Rule te-repet. -/
def DisjointUnionList (N : Finset Triple) (Ns : List (Finset Triple)) : Prop :=
  Ns.Pairwise Disjoint ∧ N = Ns.foldr (· ∪ ·) ∅

end ShexLean
