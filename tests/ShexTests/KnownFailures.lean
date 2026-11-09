/-!
The tests of the ShEx test suite where the result of the 2025 formalism is
different from the result that the test suite expects.

Each entry is a known difference: the runner reports it, but does not fail.
If a test of this list passes, the runner fails, so that you remove the
test from the list. Thus, the list always agrees with the formalism.
-/

namespace ShexTests

/-- The names of the tests, with the reason for the difference. -/
def knownFailures : List (String × String) := []

end ShexTests
