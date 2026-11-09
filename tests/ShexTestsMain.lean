import ShexTests

/-!
The runner of the test suite (`lake test`, or `lake exe shex_tests`).

Usage: `lake exe shex_tests [--verbose] [--group GROUP] [NAME_PART]`.

* With `--group structural` or `--group inheritance`, the runner runs only
  the tests of that group.
* With `NAME_PART`, the runner runs only the tests whose name contains it.
* With `--verbose`, it prints the result of each test.

The runner fails (exit code 1) if a test gives an unexpected result:

* A test that is not in `ShexTests.knownFailures` gives a result that is
  different from the expected result.
* A test that is in `ShexTests.knownFailures` gives the expected result.
-/

open ShexTests

def allTests : List TestCase := Structural.tests ++ Inheritance.tests

structure Counts where
  pass : Nat := 0
  known : Nat := 0
  unsupported : Nat := 0
  bad : Nat := 0

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let rec parse : List String → Option String × Option String
    | "--verbose" :: rest => parse rest
    | "--group" :: g :: rest => ((parse rest).1, some g)
    | x :: rest => (some x, (parse rest).2)
    | [] => (none, none)
  let (filter, group) := parse args
  let tests := allTests.filter fun t =>
    group.all (· == t.group) && filter.all fun f => (t.name.splitOn f).length > 1
  let mut counts : Std.HashMap String Counts := {}
  let mut problems : Array String := #[]
  for t in tests do
    if verbose then
      IO.print s!"[{t.group}] {t.name}: "
      (← IO.getStdout).flush
    let t0 ← IO.monoMsNow
    let known := knownFailures.lookup t.name
    let c := counts.getD t.group {}
    let outcome := run t
    let (c, msg) := match outcome, known with
      | .unsupported r, _ => ({ c with unsupported := c.unsupported + 1 }, s!"UNSUPPORTED ({r})")
      | .result b, none =>
          if b == t.expected then ({ c with pass := c.pass + 1 }, "pass")
          else ({ c with bad := c.bad + 1 }, s!"FAIL: the result is {b}, the expected result is {t.expected}")
      | .result b, some _ =>
          if b == t.expected then
            ({ c with bad := c.bad + 1 }, "FAIL: the test passes, but it is in knownFailures")
          else ({ c with known := c.known + 1 }, "known failure")
    counts := counts.insert t.group c
    if msg.startsWith "FAIL" then problems := problems.push s!"{t.name}: {msg}"
    if verbose then
      let ms := (← IO.monoMsNow) - t0
      IO.println s!"{msg} ({ms} ms)"
  for g in ["structural", "inheritance"] do
    let c := counts.getD g {}
    IO.println s!"{g}: {c.pass} pass, {c.known} known failures, {c.unsupported} unsupported, {c.bad} unexpected"
  for p in problems do IO.eprintln p
  return if problems.isEmpty then 0 else 1
