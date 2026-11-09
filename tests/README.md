# Tests

This directory contains the test suite of the project. It is separate from
the formalization:

* `lake build` does not build it.
* No file of `ShexLean/` or `examples/` imports it.

## Run the tests

```
lake test
```

`lake test` builds and runs `shex_tests`. You can also run it directly:

```
lake exe shex_tests                         # all the tests
lake exe shex_tests --group inheritance     # one group: structural or inheritance
lake exe shex_tests --verbose 1dotExtends   # the tests whose name contains 1dotExtends
```

The runner gives the number of tests that pass in each group. It fails
(exit code 1) if a test gives an unexpected result.

## What the tests check

The tests come from the validation tests of the ShEx test suite
(<https://github.com/shexSpec/shexTest>). Each test gives a schema, RDF
data, a focus node, a shape and the expected result: the focus node
conforms to the shape, or it does not conform.

The tests check the 2025 formalism (`ShexLean/Shex2025Inheritance/`). The
formalism contains the shape expressions of ShEx 2.1 and also `extends` and
`abstract`. Thus, one formalism covers the two groups of tests:

* `structural`: the tests with no `extends` and no `abstract` label.
* `inheritance`: the tests with `extends` or `abstract`.

For each test, the runner computes the maximal typing of the data by the
schema, and checks if it contains the focus node with the shape. To compute
the typing, it uses only the definitions and the decision procedures of the
formalism (`ShexTests/Harness.lean`):

* `satisfiesFuel_decidable` decides the satisfaction relation of
  Tables 1-3. At the fuel `S.X.card + 1`, this relation is `Satisfies`
  (`satisfies_iff_satisfiesFuel_card`).
* The typing is the result of the stratified refinement of Algorithm 1
  (§5 of the 2025 paper).

## The files

* `shexTest/`: the part of the ShEx test suite that the tests use
  (refer to `shexTest/NOTICE.md`). `shexTest/SKIPPED.md` lists the tests
  that the formalism cannot express, with the reason for each test.
* `tools/gen_shextest.py`: the generator. It reads the tests and writes
  them as Lean values. It reads the Turtle data with rudof
  (<https://rudof-project.github.io>).
* `ShexTests/Generated/Structural.lean`, `ShexTests/Generated/Inheritance.lean`:
  the generated tests. Do not edit them.
* `ShexTests/Harness.lean`: the validator.
* `ShexTests/KnownFailures.lean`: the tests where the formalism and the
  test suite give different results. At this time, the list is empty.
* `ShexTestsMain.lean`: the runner.

## Generate the tests again

Install the Python package of rudof, then run the generator:

```
pip install pyrudof
python3 tests/tools/gen_shextest.py
```

To use a newer version of the ShEx test suite, give the location of a
checkout of the test suite. The generator then copies the files that the
tests use into `shexTest/`:

```
git clone https://github.com/shexSpec/shexTest /tmp/shexTest
python3 tests/tools/gen_shextest.py --vendor /tmp/shexTest
```

## Work with the tests (TDD)

1. Before you change a definition of the formalism, run `lake test`. All the
   tests must pass.
2. If you add a feature to the formalism (for example, a new datatype of
   literals), change the generator so that it translates the tests that use
   the feature. Generate the tests again. The new tests fail, or they are
   not supported.
3. Change the formalism until the new tests pass.
4. If the formalism gives a different result from the test suite on
   purpose, add the test to `ShexTests/KnownFailures.lean`, with the reason.
   If a test of that list passes later, the runner fails. Then remove the
   test from the list.

## Limits

The generator skips a test that the formalism or the translation cannot
express (refer to `shexTest/SKIPPED.md`). The most frequent reasons are:

* `ShexLean/Common/RDF.lean` has only string literals and integer literals.
  Thus, the generator skips the tests with other datatypes or with
  language tags in the data.
* The formalism has no regular expressions (the `pattern` facet).
* The formalism has no imports, semantic actions, inverse triple
  constraints, shape references at the level of shape expressions or start
  shapes.
