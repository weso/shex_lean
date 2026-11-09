-- `tests/tools/gen_shextest.py` writes this file. Do not edit it.
import ShexTests.Harness

namespace ShexTests.Structural

open ShexTests
open ShexLean hiding Schema
open ShexLean.InheritanceCore hiding Schema

def t0000 : TestCase where
  name := "0_empty"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, .empty⟩))] }
  data := []
  focus := .iri "http://a.example/dummy"
  shape := "http://a.example/S1"
  expected := true

def t0001 : TestCase where
  name := "0_other"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, .empty⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0002 : TestCase where
  name := "0_otherbnode"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, .empty⟩))] }
  data := [⟨.bnode "abcd", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcd"
  shape := "http://a.example/S1"
  expected := true

def t0003 : TestCase where
  name := "1dot_fail-empty"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0004 : TestCase where
  name := "1dot-base_fail-empty"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0005 : TestCase where
  name := "1dot_fail-missing"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0006 : TestCase where
  name := "1dot-base_fail-missing"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0007 : TestCase where
  name := "1dot_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0008 : TestCase where
  name := "1dot-base_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0009 : TestCase where
  name := "1dotSemi_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0010 : TestCase where
  name := "1dotLNex_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0011 : TestCase where
  name := "1dotNS2_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0012 : TestCase where
  name := "1dotNS2SingleComment_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0013 : TestCase where
  name := "1dotLNexSingleComment_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0014 : TestCase where
  name := "1dotLNdefault_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0015 : TestCase where
  name := "1dotNSdefault_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0016 : TestCase where
  name := "1dotLNex-HYPHEN_MINUS_pass-noOthers"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1-" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1-", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0017 : TestCase where
  name := "1dot_pass-others_lexicallyEarlier"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p0", .iri "http://a.example/o0"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0018 : TestCase where
  name := "1dot_pass-others_lexicallyLater"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0019 : TestCase where
  name := "bnode1dot_fail-missing"
  group := "structural"
  schema :=
    { Y := ["#any", "_:S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("_:S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "_:S1"
  expected := false

def t0020 : TestCase where
  name := "bnode1dot_pass-others_lexicallyEarlier"
  group := "structural"
  schema :=
    { Y := ["#any", "_:S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("_:S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p0", .iri "http://a.example/o0"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "_:S1"
  expected := true

def t0021 : TestCase where
  name := "2intersectP1ValueSet_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1#2", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "a", VI.str "b", VI.str "c"]]))),
        ("http://a.example/S1#2", (.constraint (NC.all [NC.values [VI.str "b", VI.str "c"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.tc "http://a.example/p1" "http://a.example/S1#2"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0022 : TestCase where
  name := "2intersectP1ValueSet_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1#2", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "a", VI.str "b", VI.str "c"]]))),
        ("http://a.example/S1#2", (.constraint (NC.all [NC.values [VI.str "b", VI.str "c"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.tc "http://a.example/p1" "http://a.example/S1#2"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0023 : TestCase where
  name := "2intersectP1ValueSet_fail-Ld"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1#2", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "a", VI.str "b", VI.str "c"]]))),
        ("http://a.example/S1#2", (.constraint (NC.all [NC.values [VI.str "b", VI.str "c"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.tc "http://a.example/p1" "http://a.example/S1#2"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "d")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0024 : TestCase where
  name := "RecursionContingent_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/D#1", "http://a.example/D", "http://a.example/E#2", "http://a.example/E", "http://a.example/A#3", "http://a.example/A", "http://a.example/C#4", "http://a.example/C"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/D#1", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/D", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/predd" "http://a.example/D#1") (.seq (.choice (.star (.tc "http://a.example/test" "http://a.example/A")) (.star (.tc "http://a.example/test" "http://a.example/E"))) (.tc "http://a.example/test2" "http://a.example/C")))⟩)),
        ("http://a.example/E#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/E", (.ofShape ⟨false, none, (.tc "http://a.example/prede" "http://a.example/E#2")⟩)),
        ("http://a.example/A#3", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/A", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/subject" "http://a.example/C") (.tc "http://a.example/preda" "http://a.example/A#3"))⟩)),
        ("http://a.example/C#4", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/C", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/subject" "http://a.example/A") (.tc "http://a.example/predc" "http://a.example/C#4"))⟩))] }
  data := [⟨.iri "http://a.example/a", "http://a.example/prede", .lit (.str "final")⟩, ⟨.iri "http://a.example/a", "http://a.example/subject", .iri "http://a.example/c"⟩, ⟨.iri "http://a.example/c", "http://a.example/predc", .lit (.str "final")⟩, ⟨.iri "http://a.example/c", "http://a.example/subject", .iri "http://a.example/a"⟩, ⟨.iri "http://a.example/d", "http://a.example/predd", .lit (.str "final")⟩, ⟨.iri "http://a.example/d", "http://a.example/test", .iri "http://a.example/a"⟩, ⟨.iri "http://a.example/d", "http://a.example/test2", .iri "http://a.example/c"⟩]
  focus := .iri "http://a.example/d"
  shape := "http://a.example/D"
  expected := false

def t0025 : TestCase where
  name := "RecursionContingent_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/D#1", "http://a.example/D", "http://a.example/E#2", "http://a.example/E", "http://a.example/A#3", "http://a.example/A", "http://a.example/C#4", "http://a.example/C"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/D#1", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/D", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/predd" "http://a.example/D#1") (.seq (.choice (.star (.tc "http://a.example/test" "http://a.example/A")) (.star (.tc "http://a.example/test" "http://a.example/E"))) (.tc "http://a.example/test2" "http://a.example/C")))⟩)),
        ("http://a.example/E#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/E", (.ofShape ⟨false, none, (.tc "http://a.example/prede" "http://a.example/E#2")⟩)),
        ("http://a.example/A#3", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/A", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/subject" "http://a.example/C") (.tc "http://a.example/preda" "http://a.example/A#3"))⟩)),
        ("http://a.example/C#4", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/C", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/subject" "http://a.example/A") (.tc "http://a.example/predc" "http://a.example/C#4"))⟩))] }
  data := [⟨.iri "http://a.example/a", "http://a.example/preda", .lit (.str "final")⟩, ⟨.iri "http://a.example/a", "http://a.example/subject", .iri "http://a.example/c"⟩, ⟨.iri "http://a.example/c", "http://a.example/predc", .lit (.str "final")⟩, ⟨.iri "http://a.example/c", "http://a.example/subject", .iri "http://a.example/a"⟩, ⟨.iri "http://a.example/d", "http://a.example/predd", .lit (.str "final")⟩, ⟨.iri "http://a.example/d", "http://a.example/test", .iri "http://a.example/a"⟩, ⟨.iri "http://a.example/d", "http://a.example/test2", .iri "http://a.example/c"⟩]
  focus := .iri "http://a.example/d"
  shape := "http://a.example/D"
  expected := true

def t0026 : TestCase where
  name := "1NOTvsCard2_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.tc "http://a.example/p1" "http://a.example/S1#1"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0027 : TestCase where
  name := "1NOTvsCard2_fail-3arcs"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.tc "http://a.example/p1" "http://a.example/S1#1"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0028 : TestCase where
  name := "1NOTvsCard2Extra_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.tc "http://a.example/p1" "http://a.example/S1#1"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0029 : TestCase where
  name := "1Adot_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://www.w3.org/1999/02/22-rdf-syntax-ns#type", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0030 : TestCase where
  name := "1iri_pass-iri"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0031 : TestCase where
  name := "1iri_fail-bnode"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "ab"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0032 : TestCase where
  name := "1iri_fail-literal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0033 : TestCase where
  name := "1bnode_fail-iri"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0034 : TestCase where
  name := "1bnode_pass-bnode"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "ab"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0035 : TestCase where
  name := "1bnode_fail-literal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0036 : TestCase where
  name := "1literal_fail-iri"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0037 : TestCase where
  name := "1literal_fail-bnode"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "ab"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0038 : TestCase where
  name := "1literal_pass-literal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0039 : TestCase where
  name := "1nonliteral_pass-iri"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0040 : TestCase where
  name := "1focusnonLiteralLength-nonLiteralLength_fail-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.length 19]))),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isNonLiteral, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0041 : TestCase where
  name := "1focusnonLiteralLength-nonLiteralLength_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.length 19]))),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isNonLiteral, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0042 : TestCase where
  name := "1nonliteral_pass-bnode"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "ab"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0043 : TestCase where
  name := "1nonliteral_fail-literal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0044 : TestCase where
  name := "1datatype_missing"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.never]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0045 : TestCase where
  name := "1datatype_nonLiteral"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.never]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/dt1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0046 : TestCase where
  name := "1card2_fail0"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p1" "#any"))⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0047 : TestCase where
  name := "1card2_fail1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p1" "#any"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0048 : TestCase where
  name := "1card2_pass2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p1" "#any"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0049 : TestCase where
  name := "1card2_fail3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p1" "#any"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0050 : TestCase where
  name := "1card25_fail0"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.choice (.tc "http://a.example/p1" "#any") .empty)))))⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0051 : TestCase where
  name := "1card25_fail1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.choice (.tc "http://a.example/p1" "#any") .empty)))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0052 : TestCase where
  name := "1card25_pass2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.choice (.tc "http://a.example/p1" "#any") .empty)))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0053 : TestCase where
  name := "1card25_pass3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.choice (.tc "http://a.example/p1" "#any") .empty)))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0054 : TestCase where
  name := "1card25_pass4"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.choice (.tc "http://a.example/p1" "#any") .empty)))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "d")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0055 : TestCase where
  name := "1card25_pass5"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.choice (.tc "http://a.example/p1" "#any") .empty)))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "d")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "e")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0056 : TestCase where
  name := "1card25_fail6"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.seq (.choice (.tc "http://a.example/p1" "#any") .empty) (.choice (.tc "http://a.example/p1" "#any") .empty)))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "d")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "e")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "f")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0057 : TestCase where
  name := "1card2Star_fail0"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any"))))⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0058 : TestCase where
  name := "1card2Star_fail1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any"))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0059 : TestCase where
  name := "1card2Star_pass2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any"))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0060 : TestCase where
  name := "1card2Star_pass3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any"))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0061 : TestCase where
  name := "1card2Star_pass6"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any"))))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "d")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "e")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "f")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0062 : TestCase where
  name := "1cardOpt_pass0"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") .empty)⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0063 : TestCase where
  name := "1cardOpt_pass1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") .empty)⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0064 : TestCase where
  name := "1cardOpt_fail2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") .empty)⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0065 : TestCase where
  name := "1cardOpt_pass6"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") .empty)⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "d")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "e")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "f")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0066 : TestCase where
  name := "1cardPlus_fail0"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any")))⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0067 : TestCase where
  name := "1cardPlus_pass1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any")))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0068 : TestCase where
  name := "1cardPlus_pass2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any")))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0069 : TestCase where
  name := "1cardPlus_pass6"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any")))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "d")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "e")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "f")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0070 : TestCase where
  name := "1cardStar_pass0"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.star (.tc "http://a.example/p1" "#any"))⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0071 : TestCase where
  name := "1cardStar_pass1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.star (.tc "http://a.example/p1" "#any"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0072 : TestCase where
  name := "1cardStar_pass2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.star (.tc "http://a.example/p1" "#any"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0073 : TestCase where
  name := "1cardStar_pass6"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.star (.tc "http://a.example/p1" "#any"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "c")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "d")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "e")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "f")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0074 : TestCase where
  name := "1card0_pass0"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice .empty (.tc "http://a.example/p1" "#never"))⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0075 : TestCase where
  name := "1card0_pass-p2"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice .empty (.tc "http://a.example/p1" "#never"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0076 : TestCase where
  name := "1card0_fail1"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice .empty (.tc "http://a.example/p1" "#never"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0077 : TestCase where
  name := "1card1_fail0"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0078 : TestCase where
  name := "1card1_pass1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0079 : TestCase where
  name := "1card1_fail2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "b")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0080 : TestCase where
  name := "1literalPlus_Is1_Ip1_La,Io1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.star (.tc "http://a.example/p1" "http://a.example/S1#1")))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0081 : TestCase where
  name := "open2Eachdotclosecard0c1dot_pass-c1"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.choice .empty (.seq (.tc "http://a.example/a" "#never") (.tc "http://a.example/b" "#never"))) (.tc "http://a.example/c" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0082 : TestCase where
  name := "open2Eachdotclosecard0c1dot_fail-a1b1c1"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.choice .empty (.seq (.tc "http://a.example/a" "#never") (.tc "http://a.example/b" "#never"))) (.tc "http://a.example/c" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0083 : TestCase where
  name := "open2Eachdotclosecard0c1dot_fail-a1c1"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.choice .empty (.seq (.tc "http://a.example/a" "#never") (.tc "http://a.example/b" "#never"))) (.tc "http://a.example/c" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0084 : TestCase where
  name := "open2Eachdotclosecard0c1dot_fail-a2b2"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.choice .empty (.seq (.tc "http://a.example/a" "#never") (.tc "http://a.example/b" "#never"))) (.tc "http://a.example/c" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0085 : TestCase where
  name := "open2EachdotclosecardStar_pass0"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")))⟩))] }
  data := []
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0086 : TestCase where
  name := "open2EachdotclosecardStar_pass-c1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0087 : TestCase where
  name := "open2EachdotclosecardStar_pass-a2b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0088 : TestCase where
  name := "open2EachdotclosecardStar_fail-a1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0089 : TestCase where
  name := "open2EachdotclosecardOpt_pass-c1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty)⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0090 : TestCase where
  name := "open2EachdotclosecardOpt_fail-a2b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty)⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0091 : TestCase where
  name := "open2Eachdotclosecard02_pass-c1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty) (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0092 : TestCase where
  name := "open2Eachdotclosecard02_pass-a2b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty) (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0093 : TestCase where
  name := "open2Eachdotclosecard02_fail-a3b3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty) (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "3")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0094 : TestCase where
  name := "open2OnedotclosecardStar_pass-c1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.choice (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0095 : TestCase where
  name := "open2OnedotclosecardStar_pass-a2b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.choice (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0096 : TestCase where
  name := "open1dot1cardPlusclosecard2_pass-a2b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))) (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0097 : TestCase where
  name := "open1dot1cardPlusclosecard2_pass-a2b3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))) (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "3")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0098 : TestCase where
  name := "open1dot1cardPlusclosecard2_fail-a2b1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))) (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0099 : TestCase where
  name := "open1dot1cardPlusclosecard2_fail-a3b3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))) (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "3")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0100 : TestCase where
  name := "open1dot1cardPlusclosecard2_fail-a1b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))) (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.star (.tc "http://a.example/b" "#any")))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0101 : TestCase where
  name := "open1cardPlus1dotclosecard2_pass-a2b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.seq (.tc "http://a.example/a" "#any") (.star (.tc "http://a.example/a" "#any"))) (.tc "http://a.example/b" "#any")) (.seq (.seq (.tc "http://a.example/a" "#any") (.star (.tc "http://a.example/a" "#any"))) (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0102 : TestCase where
  name := "open1cardPlus1dotclosecard2_pass-a3b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.seq (.tc "http://a.example/a" "#any") (.star (.tc "http://a.example/a" "#any"))) (.tc "http://a.example/b" "#any")) (.seq (.seq (.tc "http://a.example/a" "#any") (.star (.tc "http://a.example/a" "#any"))) (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0103 : TestCase where
  name := "open1cardPlus1dotclosecard2_fail-a1b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.seq (.tc "http://a.example/a" "#any") (.star (.tc "http://a.example/a" "#any"))) (.tc "http://a.example/b" "#any")) (.seq (.seq (.tc "http://a.example/a" "#any") (.star (.tc "http://a.example/a" "#any"))) (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0104 : TestCase where
  name := "open1card21dotclosecardStar_pass-c1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/a" "#any")) (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0105 : TestCase where
  name := "open1card21dotclosecardStar_pass-a2b1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/a" "#any")) (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0106 : TestCase where
  name := "open1card21dotclosecardStar_pass-a4b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/a" "#any")) (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "4")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0107 : TestCase where
  name := "open1card21dotclosecardStar_fail-a1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/a" "#any")) (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0108 : TestCase where
  name := "open1card21dotclosecardStar_fail-a2b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/a" "#any")) (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0109 : TestCase where
  name := "open1card21dotclosecardStar_fail-a3b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/a" "#any")) (.tc "http://a.example/b" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0110 : TestCase where
  name := "open1card121cardOptclosecardStar_pass-a2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.seq (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/a" "#any") .empty)) (.choice (.tc "http://a.example/b" "#any") .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0111 : TestCase where
  name := "open1dot1cardOptclosecard12_pass-a1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) (.choice (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) .empty))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0112 : TestCase where
  name := "open1dot1cardOptclosecard12_pass-a2b1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) (.choice (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) .empty))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0113 : TestCase where
  name := "open1dot1cardOptclosecard12_pass-a2b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) (.choice (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) .empty))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0114 : TestCase where
  name := "open1dot1cardOptclosecard12_fail-a1b2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) (.choice (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) .empty))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0115 : TestCase where
  name := "open1dot1cardOptclosecard12_fail-a3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) (.choice (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) .empty))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0116 : TestCase where
  name := "open1dot1cardOptclosecard12_fail-b1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) (.choice (.seq (.tc "http://a.example/a" "#any") (.choice (.tc "http://a.example/b" "#any") .empty)) .empty))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/d", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0117 : TestCase where
  name := "openopen2Eachdotclosecard0c1dotclosecardStarc1dot_pass-d1a1"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.star (.seq (.choice .empty (.seq (.tc "http://a.example/b" "#never") (.tc "http://a.example/c" "#never"))) (.tc "http://a.example/d" "#any"))) (.tc "http://a.example/a" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/d", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0118 : TestCase where
  name := "openopen2Eachdotclosecard0c1dotclosecardStarc1dot_pass-a1"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.star (.seq (.choice .empty (.seq (.tc "http://a.example/b" "#never") (.tc "http://a.example/c" "#never"))) (.tc "http://a.example/d" "#any"))) (.tc "http://a.example/a" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0119 : TestCase where
  name := "openopen2Eachdotclosecard0c1dotclosecardStarc1dot_fail-b1c1d1"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.star (.seq (.choice .empty (.seq (.tc "http://a.example/b" "#never") (.tc "http://a.example/c" "#never"))) (.tc "http://a.example/d" "#any"))) (.tc "http://a.example/a" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/d", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0120 : TestCase where
  name := "openopen2Eachdotclosecard0c1dotclosecardStarc1dot_fail-b1c1d1a1"
  group := "structural"
  schema :=
    { Y := ["#any", "#never", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("#never", (.constraint NC.never)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.star (.seq (.choice .empty (.seq (.tc "http://a.example/b" "#never") (.tc "http://a.example/c" "#never"))) (.tc "http://a.example/d" "#any"))) (.tc "http://a.example/a" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/d", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0121 : TestCase where
  name := "openopen2EachdotclosecardOptc1dotclosecardStarc1dot_pass-a1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.star (.seq (.choice (.seq (.tc "http://a.example/b" "#any") (.tc "http://a.example/c" "#any")) .empty) (.tc "http://a.example/d" "#any"))) (.tc "http://a.example/a" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0122 : TestCase where
  name := "openopen2EachdotclosecardOptc1dotclosecardStarc1dot_pass-d1a1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.star (.seq (.choice (.seq (.tc "http://a.example/b" "#any") (.tc "http://a.example/c" "#any")) .empty) (.tc "http://a.example/d" "#any"))) (.tc "http://a.example/a" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/d", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0123 : TestCase where
  name := "openopen2EachdotclosecardOptc1dotclosecardStarc1dot_pass-b1c1d1a1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.star (.seq (.choice (.seq (.tc "http://a.example/b" "#any") (.tc "http://a.example/c" "#any")) .empty) (.tc "http://a.example/d" "#any"))) (.tc "http://a.example/a" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/d", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0124 : TestCase where
  name := "openopen2EachdotclosecardOptc1dotclosecardStarc1dot_fail-d1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.star (.seq (.choice (.seq (.tc "http://a.example/b" "#any") (.tc "http://a.example/c" "#any")) .empty) (.tc "http://a.example/d" "#any"))) (.tc "http://a.example/a" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/d", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0125 : TestCase where
  name := "openopen2EachdotclosecardOptc1dotclosecardStarc1dot_fail-b1d1a1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.star (.seq (.choice (.seq (.tc "http://a.example/b" "#any") (.tc "http://a.example/c" "#any")) .empty) (.tc "http://a.example/d" "#any"))) (.tc "http://a.example/a" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/d", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0126 : TestCase where
  name := "open2OnecardStarclosecardStar_pass-astr1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S#1", "http://a.example/S#2", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S#1", (.constraint (NC.all [NC.isInteger]))),
        ("http://a.example/S#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.choice (.star (.tc "http://a.example/a" "http://a.example/S#1")) (.star (.tc "http://a.example/a" "http://a.example/S#2"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "final")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0127 : TestCase where
  name := "open2OnecardStarclosecardStar_pass-astr1aint1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S#1", "http://a.example/S#2", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S#1", (.constraint (NC.all [NC.isInteger]))),
        ("http://a.example/S#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.choice (.star (.tc "http://a.example/a" "http://a.example/S#1")) (.star (.tc "http://a.example/a" "http://a.example/S#2"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.int 1)⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "final")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0128 : TestCase where
  name := "open2OnecardStarclosecardStar_pass-c1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S#1", "http://a.example/S#2", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S#1", (.constraint (NC.all [NC.isInteger]))),
        ("http://a.example/S#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.choice (.star (.tc "http://a.example/a" "http://a.example/S#1")) (.star (.tc "http://a.example/a" "http://a.example/S#2"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0129 : TestCase where
  name := "open2OnecardStarclosecardStar_fail-aI1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S#1", "http://a.example/S#2", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S#1", (.constraint (NC.all [NC.isInteger]))),
        ("http://a.example/S#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/S", (.ofShape ⟨false, none, (.star (.choice (.star (.tc "http://a.example/a" "http://a.example/S#1")) (.star (.tc "http://a.example/a" "http://a.example/S#2"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .iri "http://a.example/o"⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0130 : TestCase where
  name := "1dotRef1_referent,referrer"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "http://a.example/S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0131 : TestCase where
  name := "1dotRef1_referrer,referent"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "http://a.example/S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0132 : TestCase where
  name := "1dotRef1_missingReferent"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "http://a.example/S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0133 : TestCase where
  name := "1dotRef1_selfReference"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "http://a.example/S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n1"⟩, ⟨.iri "http://a.example/n1", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0134 : TestCase where
  name := "1dotRef1_missingSelfReference"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "http://a.example/S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n1"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0135 : TestCase where
  name := "1dotRef1_overReferrer"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "http://a.example/S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n3"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0136 : TestCase where
  name := "1dotRef1_overReferrer,overReferent"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "http://a.example/S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n3"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩, ⟨.iri "http://a.example/n3", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0137 : TestCase where
  name := "1dotRef1_overMatchesReferent"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "http://a.example/S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩, ⟨.iri "http://a.example/n3", "http://a.example/p1", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0138 : TestCase where
  name := "1refbnode1_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "_:S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "_:S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("_:S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0139 : TestCase where
  name := "1refbnode1_fail-g1-arc"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "_:S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "_:S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("_:S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p2", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0140 : TestCase where
  name := "1refbnode1_fail-g2-arc"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1", "#any", "_:S2"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "_:S2")⟩)),
        ("#any", (.constraint NC.any)),
        ("_:S2", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p1", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0141 : TestCase where
  name := "3circRefPlus1_pass-open"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1", "http://a.example/S2", "http://a.example/S3", "http://a.example/S4"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "http://a.example/S2") .empty))⟩)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p3" "http://a.example/S3")⟩)),
        ("http://a.example/S3", (.ofShape ⟨false, none, (.tc "http://a.example/p4" "http://a.example/S1")⟩)),
        ("http://a.example/S4", (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .lit (.str "X")⟩, ⟨.iri "http://a.example/n1", "http://a.example/p2", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p3", .iri "http://a.example/n3"⟩, ⟨.iri "http://a.example/n3", "http://a.example/p4", .iri "http://a.example/n5"⟩, ⟨.iri "http://a.example/n5", "http://a.example/p1", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0142 : TestCase where
  name := "3circRefPlus1_pass-recursiveData"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1", "http://a.example/S2", "http://a.example/S3", "http://a.example/S4"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "http://a.example/S2") .empty))⟩)),
        ("http://a.example/S2", (.ofShape ⟨false, none, (.tc "http://a.example/p3" "http://a.example/S3")⟩)),
        ("http://a.example/S3", (.ofShape ⟨false, none, (.tc "http://a.example/p4" "http://a.example/S1")⟩)),
        ("http://a.example/S4", (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .lit (.str "X")⟩, ⟨.iri "http://a.example/n1", "http://a.example/p2", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p3", .iri "http://a.example/n3"⟩, ⟨.iri "http://a.example/n3", "http://a.example/p4", .iri "http://a.example/n1"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0143 : TestCase where
  name := "1dotInline1_referrer,referent"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1#1", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0144 : TestCase where
  name := "1dotInline1_missingReferent"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1#1", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0145 : TestCase where
  name := "1dotInline1_selfReference"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1#1", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n1"⟩, ⟨.iri "http://a.example/n1", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0146 : TestCase where
  name := "1dotInline1_missingSelfReference"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1#1", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n1"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0147 : TestCase where
  name := "1dotInline1_overReferrer"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1#1", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n3"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0148 : TestCase where
  name := "1dotInline1_overReferrer,overReferent"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1#1", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n3"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩, ⟨.iri "http://a.example/n3", "http://a.example/p2", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0149 : TestCase where
  name := "1dotInline1_overMatchesReferent"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1#1", (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩, ⟨.iri "http://a.example/n3", "http://a.example/p1", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0150 : TestCase where
  name := "1val1IRIREF_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0151 : TestCase where
  name := "1val1IRIREF_v2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0152 : TestCase where
  name := "1val1IRIREF_v1v2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0153 : TestCase where
  name := "1val1STRING_LITERAL1_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "STRING_LITERAL1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "STRING_LITERAL1")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0154 : TestCase where
  name := "1val1STRING_LITERAL1_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "STRING_LITERAL1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "STRING_LITERAL1999")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0155 : TestCase where
  name := "1val1STRING_LITERAL1_fail-Iv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "STRING_LITERAL1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0156 : TestCase where
  name := "1val1STRING_LITERAL1_with_all_controls_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "\x00\x01\x02\x03\x04\x05\x06\x07\x08\t\x0b\x0c\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "\x00\x01\x02\x03\x04\x05\x06\x07\x08\t\x0b\x0c\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0157 : TestCase where
  name := "1val1STRING_LITERAL1_with_all_controls_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "\x00\x01\x02\x03\x04\x05\x06\x07\x08\t\x0b\x0c\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "\x00\x01\x02\x03\x04\x05\x06\x07\x08\t\x0b\x0c\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f999")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0158 : TestCase where
  name := "1val1STRING_LITERAL1_with_all_punctuation_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str " !\"#$%&'()/:;<=>?@[]^_`{|}~"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str " !\"#$%&'()/:;<=>?@[]^_`{|}~")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0159 : TestCase where
  name := "1val1STRING_LITERAL1_with_all_punctuation_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str " !\"#$%&'()/:;<=>?@[]^_`{|}~"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str " !\"#$%&'()/:;<=>?@[]^_`{|}~999")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0160 : TestCase where
  name := "1val1STRING_LITERAL1_with_ascii_boundaries_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "\x00\t\x0b\x0c\x0e&([]\x7f"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "\x00\t\x0b\x0c\x0e&([]\x7f")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0161 : TestCase where
  name := "1val1STRING_LITERAL1_with_ascii_boundaries_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "\x00\t\x0b\x0c\x0e&([]\x7f"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "\x00\t\x0b\x0c\x0e&([]\x7f999")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0162 : TestCase where
  name := "1val1STRING_LITERAL1_with_UTF8_boundaries_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "߿ࠀ࿿က쿿퀀퟿�𐀀𿿽񀀀󿿽􀀀􏿽"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "߿ࠀ࿿က쿿퀀퟿�𐀀𿿽񀀀󿿽􀀀􏿽")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0163 : TestCase where
  name := "1val1STRING_LITERAL1_with_UTF8_boundaries_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "߿ࠀ࿿က쿿퀀퟿�𐀀𿿽񀀀󿿽􀀀􏿽"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "߿ࠀ࿿က쿿퀀퟿�𐀀𿿽񀀀󿿽􀀀􏿽999")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0164 : TestCase where
  name := "1val1STRING_LITERAL1_with_ECHAR_escapes_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "\t\x08\n\x0d\x0c\\\"'a𝒸"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "\t\x08\n\x0d\x0c\\\"'a𝒸")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0165 : TestCase where
  name := "1val1STRING_LITERAL1_with_ECHAR_escapes_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "\t\x08\n\x0d\x0c\\\"'a𝒸"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "\t\x08\n\x0d\x0c\\\"'a𝒸999")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0166 : TestCase where
  name := "1val1INTEGER_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.int 0]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 0)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0167 : TestCase where
  name := "1val1DECIMAL_Lab"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0168 : TestCase where
  name := "1val1INTEGER_Lab"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.int 0]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0169 : TestCase where
  name := "1val1LANGTAG_Lab"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0170 : TestCase where
  name := "1val1IRIREFDatatype_Lab"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0171 : TestCase where
  name := "1val1true_ab"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0172 : TestCase where
  name := "1val1false_ab"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0173 : TestCase where
  name := "1datatypeLength_fail-missing"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0174 : TestCase where
  name := "1datatypeLength_fail-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 1234)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0175 : TestCase where
  name := "1datatypeLength_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 12345)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0176 : TestCase where
  name := "1datatypeLength_fail-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 123456)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0177 : TestCase where
  name := "1literalFractiondigits_pass-integer-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.isInteger]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 12345)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0178 : TestCase where
  name := "1literalFractiondigits_pass-xsd_integer-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.isInteger]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 12345)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0179 : TestCase where
  name := "1literalFractiondigits_fail-iri"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.isInteger]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/12345"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0180 : TestCase where
  name := "1literalFractiondigits_fail-bnode"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.isInteger]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "12345"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0181 : TestCase where
  name := "1literalTotaldigits_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.totalDigits 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 12345)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0182 : TestCase where
  name := "1literalTotaldigits_pass-xsd_integer-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.totalDigits 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 1234)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0183 : TestCase where
  name := "1literalTotaldigits_pass-integer-equalTrail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.totalDigits 6]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 123450)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0184 : TestCase where
  name := "1literalTotaldigits_fail-integer-longTrail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.totalDigits 6]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 1234560)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0185 : TestCase where
  name := "1literalTotaldigits_fail-iri"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.totalDigits 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/12345"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0186 : TestCase where
  name := "1literalTotaldigits_fail-bnode"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.totalDigits 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "12345"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0187 : TestCase where
  name := "1literalMinexclusiveINTEGER_fail-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0188 : TestCase where
  name := "1literalMinexclusiveINTEGER_pass-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0189 : TestCase where
  name := "1literalMinexclusiveINTEGER_pass-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0190 : TestCase where
  name := "1literalMininclusiveINTEGER_fail-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0191 : TestCase where
  name := "1literalMininclusiveINTEGER_pass-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0192 : TestCase where
  name := "1literalMininclusiveINTEGER_pass-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0193 : TestCase where
  name := "1literalMaxexclusiveINTEGER_pass-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0194 : TestCase where
  name := "1literalMaxexclusiveINTEGER_fail-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0195 : TestCase where
  name := "1literalMaxexclusiveINTEGER_fail-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0196 : TestCase where
  name := "1literalMaxinclusiveINTEGER_pass-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0197 : TestCase where
  name := "1literalMaxinclusiveINTEGER_pass-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0198 : TestCase where
  name := "1literalMaxinclusiveINTEGER_fail-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0199 : TestCase where
  name := "1integerMininclusiveINTEGER_fail-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0200 : TestCase where
  name := "1integerMininclusiveINTEGER_pass-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0201 : TestCase where
  name := "1integerMininclusiveINTEGER_pass-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0202 : TestCase where
  name := "1integerMininclusiveINTEGER_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0203 : TestCase where
  name := "1integerMininclusiveINTEGER_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0204 : TestCase where
  name := "1integerMininclusiveINTEGER_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0205 : TestCase where
  name := "1integerMininclusiveINTEGERLead_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0206 : TestCase where
  name := "1integerMininclusiveINTEGERLead_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0207 : TestCase where
  name := "1integerMininclusiveINTEGERLead_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0208 : TestCase where
  name := "1integerMininclusiveDECIMAL_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0209 : TestCase where
  name := "1integerMininclusiveDECIMALLeadTrail_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0210 : TestCase where
  name := "1integerMininclusiveDECIMALLeadTrail_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0211 : TestCase where
  name := "1integerMininclusiveDECIMALLeadTrail_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0212 : TestCase where
  name := "1integerMininclusiveDECIMALint_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0213 : TestCase where
  name := "1integerMininclusiveDECIMALint_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0214 : TestCase where
  name := "1integerMininclusiveDECIMALint_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0215 : TestCase where
  name := "1integerMininclusiveDECIMALintLeadTrail_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0216 : TestCase where
  name := "1integerMininclusiveDECIMALintLeadTrail_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0217 : TestCase where
  name := "1integerMininclusiveDECIMALintLeadTrail_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0218 : TestCase where
  name := "1integerMininclusiveDOUBLE_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0219 : TestCase where
  name := "1integerMininclusiveDOUBLELeadTrail_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0220 : TestCase where
  name := "1integerMininclusiveDOUBLELeadTrail_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0221 : TestCase where
  name := "1integerMininclusiveDOUBLELeadTrail_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0222 : TestCase where
  name := "1integerMininclusiveDOUBLEint_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0223 : TestCase where
  name := "1integerMininclusiveDOUBLEintLeadTrail_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0224 : TestCase where
  name := "1integerMininclusiveDOUBLEintLeadTrail_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0225 : TestCase where
  name := "1integerMininclusiveDOUBLEintLeadTrail_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0226 : TestCase where
  name := "1integerMininclusiveINTEGER_fail-string-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 5) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0227 : TestCase where
  name := "1integerMinexclusiveINTEGER_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0228 : TestCase where
  name := "1integerMinexclusiveINTEGER_fail-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0229 : TestCase where
  name := "1integerMinexclusiveINTEGER_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0230 : TestCase where
  name := "1integerMinexclusiveDECIMALint_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0231 : TestCase where
  name := "1integerMinexclusiveDECIMALint_fail-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0232 : TestCase where
  name := "1integerMinexclusiveDECIMALint_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0233 : TestCase where
  name := "1integerMinexclusiveDOUBLEint_fail-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0234 : TestCase where
  name := "1integerMinexclusiveDOUBLEint_fail-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0235 : TestCase where
  name := "1integerMinexclusiveDOUBLEint_pass-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween (some 6) none]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0236 : TestCase where
  name := "1integerMaxinclusiveINTEGER_pass-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0237 : TestCase where
  name := "1integerMaxinclusiveINTEGER_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0238 : TestCase where
  name := "1integerMaxinclusiveINTEGER_fail-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0239 : TestCase where
  name := "1integerMaxinclusiveDECIMALint_pass-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0240 : TestCase where
  name := "1integerMaxinclusiveDECIMALint_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0241 : TestCase where
  name := "1integerMaxinclusiveDECIMALint_fail-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0242 : TestCase where
  name := "1integerMaxinclusiveDOUBLEint_pass-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0243 : TestCase where
  name := "1integerMaxinclusiveDOUBLEint_pass-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0244 : TestCase where
  name := "1integerMaxinclusiveDOUBLEint_fail-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 5)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0245 : TestCase where
  name := "1integerMaxexclusiveINTEGER_pass-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0246 : TestCase where
  name := "1integerMaxexclusiveINTEGER_fail-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0247 : TestCase where
  name := "1integerMaxexclusiveINTEGER_fail-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0248 : TestCase where
  name := "1integerMaxexclusiveDECIMALint_pass-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0249 : TestCase where
  name := "1integerMaxexclusiveDECIMALint_fail-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0250 : TestCase where
  name := "1integerMaxexclusiveDECIMALint_fail-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0251 : TestCase where
  name := "1integerMaxexclusiveDOUBLEint_pass-integer-low"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 4)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0252 : TestCase where
  name := "1integerMaxexclusiveDOUBLEint_fail-integer-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 5)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0253 : TestCase where
  name := "1integerMaxexclusiveDOUBLEint_fail-integer-high"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isInteger, NC.intBetween none (some 4)]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 6)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0254 : TestCase where
  name := "1Length_fail-lit-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcd")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0255 : TestCase where
  name := "1Length_pass-lit-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcde")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0256 : TestCase where
  name := "1Length_fail-lit-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcdef")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0257 : TestCase where
  name := "1literalLength_fail-lit-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcd")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0258 : TestCase where
  name := "1literalLength_pass-lit-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcde")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0259 : TestCase where
  name := "1literalLength_fail-lit-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcdef")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0260 : TestCase where
  name := "1literalLength_fail-iri-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0261 : TestCase where
  name := "1literalLength_fail-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcde"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0262 : TestCase where
  name := "1iriLength_fail-iri-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0263 : TestCase where
  name := "1iriLength_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0264 : TestCase where
  name := "1iriLength_fail-iri-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0265 : TestCase where
  name := "1iriLength_fail-lit-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcde")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0266 : TestCase where
  name := "1iriLength_fail-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcde"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0267 : TestCase where
  name := "1bnodeLength_fail-bnode-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcd"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0268 : TestCase where
  name := "1bnodeLength_pass-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcde"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0269 : TestCase where
  name := "1bnodeLength_fail-bnode-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcdef"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0270 : TestCase where
  name := "1bnodeLength_fail-lit-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcde")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0271 : TestCase where
  name := "1bnodeLength_fail-iri-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.length 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0272 : TestCase where
  name := "1nonliteralLength_fail-iri-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0273 : TestCase where
  name := "1nonliteralLength_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0274 : TestCase where
  name := "1nonliteralLength_fail-iri-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0275 : TestCase where
  name := "1nonliteralLength_fail-lit-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcde")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0276 : TestCase where
  name := "1nonliteralLength_fail-bnode-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcd"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0277 : TestCase where
  name := "1nonliteralLength_pass-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcdefghijklmnopqrs"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0278 : TestCase where
  name := "1nonliteralLength_fail-bnode-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.length 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcdefghijklmnopqrst"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0279 : TestCase where
  name := "1literalMinlength_fail-lit-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcd")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0280 : TestCase where
  name := "1literalMinlength_pass-lit-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcde")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0281 : TestCase where
  name := "1literalMinlength_pass-lit-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcdef")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0282 : TestCase where
  name := "1iriMinlength_fail-iri-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.minLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0283 : TestCase where
  name := "1iriMinlength_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.minLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0284 : TestCase where
  name := "1iriMinlength_pass-iri-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.minLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0285 : TestCase where
  name := "1bnodeMinlength_fail-bnode-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcd"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0286 : TestCase where
  name := "1bnodeMinlength_pass-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcde"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0287 : TestCase where
  name := "1bnodeMinlength_pass-bnode-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcdef"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0288 : TestCase where
  name := "1nonliteralMinlength_fail-iri-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.minLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0289 : TestCase where
  name := "1nonliteralMinlength_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.minLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0290 : TestCase where
  name := "1nonliteralMinlength_pass-iri-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.minLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0291 : TestCase where
  name := "1nonliteralMinlength_fail-bnode-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.minLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcd"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0292 : TestCase where
  name := "1nonliteralMinlength_pass-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.minLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcdefghijklmnopqrs"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0293 : TestCase where
  name := "1nonliteralMinlength_pass-bnode-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.minLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcdefghijklmnopqrs"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0294 : TestCase where
  name := "1literalMaxlength_pass-lit-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.maxLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcd")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0295 : TestCase where
  name := "1literalMaxlength_pass-lit-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.maxLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcde")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0296 : TestCase where
  name := "1literalMaxlength_fail-lit-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isLiteral, NC.maxLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcdef")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0297 : TestCase where
  name := "1iriMaxlength_pass-iri-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.maxLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0298 : TestCase where
  name := "1iriMaxlength_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.maxLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0299 : TestCase where
  name := "1iriMaxlength_fail-iri-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isIri, NC.maxLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0300 : TestCase where
  name := "1bnodeMaxlength_pass-bnode-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.maxLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcd"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0301 : TestCase where
  name := "1bnodeMaxlength_pass-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.maxLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcde"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0302 : TestCase where
  name := "1bnodeMaxlength_fail-bnode-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isBNode, NC.maxLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcdef"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0303 : TestCase where
  name := "1nonliteralMaxlength_pass-iri-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.maxLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0304 : TestCase where
  name := "1nonliteralMaxlength_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.maxLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0305 : TestCase where
  name := "1nonliteralMaxlength_fail-iri-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.maxLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0306 : TestCase where
  name := "1nonliteralMaxlength_pass-bnode-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.maxLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcd"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0307 : TestCase where
  name := "1nonliteralMaxlength_pass-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.maxLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcdefghijklmnopqrs"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0308 : TestCase where
  name := "1nonliteralMaxlength_fail-bnode-long"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.isNonLiteral, NC.maxLength 19]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "abcdefghijklmnopqrst"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0309 : TestCase where
  name := "1val1dotMinusiri3_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange none [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0310 : TestCase where
  name := "1val1dotMinusiri3_v1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange none [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0311 : TestCase where
  name := "1val1dotMinusiri3_v2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange none [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0312 : TestCase where
  name := "1val1dotMinusiri3_v3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange none [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0313 : TestCase where
  name := "1val1refvsMinusiri3_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.constraint (NC.all [NC.values [VI.iriRange none [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/vs1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0314 : TestCase where
  name := "1val1refvsMinusiri3_v1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.constraint (NC.all [NC.values [VI.iriRange none [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/vs1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0315 : TestCase where
  name := "1val1refvsMinusiri3_v2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.constraint (NC.all [NC.values [VI.iriRange none [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/vs1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0316 : TestCase where
  name := "1val1refvsMinusiri3_v3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.constraint (NC.all [NC.values [VI.iriRange none [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/vs1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0317 : TestCase where
  name := "1val1dotMinusiriStem3_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange none [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0318 : TestCase where
  name := "1val1dotMinusiriStem3_v1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange none [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0319 : TestCase where
  name := "1val1dotMinusiriStem3_v2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange none [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0320 : TestCase where
  name := "1val1dotMinusiriStem3_v3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange none [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0321 : TestCase where
  name := "1val1dotMinusiriStem3_v1a"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange none [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0322 : TestCase where
  name := "1val1iri_passv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0323 : TestCase where
  name := "1val1iri_failv1a"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0324 : TestCase where
  name := "1val1iriStem_passv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriStem "http://a.example/v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0325 : TestCase where
  name := "1val1iriStem_passv1a"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriStem "http://a.example/v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0326 : TestCase where
  name := "1val1iriStem_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriStem "http://a.example/v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0327 : TestCase where
  name := "1val1iriStem_fail-literalIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriStem "http://a.example/v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "http://a.example/v1")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0328 : TestCase where
  name := "1val1iriStemMinusiri3_passIv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0329 : TestCase where
  name := "1val1iriStemMinusiri3_passIv4"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v4"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0330 : TestCase where
  name := "1val1iriStemMinusiri3_fail-literalIv4"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "http://a.example/v4")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0331 : TestCase where
  name := "1val1iriStemMinusiri3_v1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0332 : TestCase where
  name := "1val1iriStemMinusiri3_fail-literalIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "http://a.example/v1")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0333 : TestCase where
  name := "1val1iriStemMinusiri3_v2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0334 : TestCase where
  name := "1val1iriStemMinusiri3_v3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0335 : TestCase where
  name := "1val1iriStemMinusiri3_passIv1a"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0336 : TestCase where
  name := "1val1iriStemMinusiri3_fail-Ia"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0337 : TestCase where
  name := "1val1iriStemMinusiriStem3_passIv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0338 : TestCase where
  name := "1val1iriStemMinusiriStem3_passIv4"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v4"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0339 : TestCase where
  name := "1val1iriStemMinusiriStem3_v1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0340 : TestCase where
  name := "1val1iriStemMinusiriStem3_v2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0341 : TestCase where
  name := "1val1iriStemMinusiriStem3_v3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0342 : TestCase where
  name := "1val1iriStemMinusiriStem3_v1a"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iriRange (some "http://a.example/v") [(true, "http://a.example/v1"), (true, "http://a.example/v2"), (true, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1a"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0343 : TestCase where
  name := "1val1literal_passv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0344 : TestCase where
  name := "1val1literal_failv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.str "v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v1")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0345 : TestCase where
  name := "1val1literalStem_passv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litStem "v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v1")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0346 : TestCase where
  name := "1val1literalStem_passv1a"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litStem "v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v1a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0347 : TestCase where
  name := "1val1literalStem_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litStem "v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0348 : TestCase where
  name := "1val1literaliriStem_fail-Iv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litStem "http://a.example/v"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0349 : TestCase where
  name := "1val1literalStemMinusliteral3_passLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(false, "v1"), (false, "v2"), (false, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0350 : TestCase where
  name := "1val1literalStemMinusliteral3_passLv4"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(false, "v1"), (false, "v2"), (false, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v4")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0351 : TestCase where
  name := "1val1literaliriStemMinusliteraliri3_fail-Iv4"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v4"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0352 : TestCase where
  name := "1val1literalStemMinusliteral3_v1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(false, "v1"), (false, "v2"), (false, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v1")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0353 : TestCase where
  name := "1val1literaliriStemMinusliteraliri3_fail-Iv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "http://a.example/v") [(false, "http://a.example/v1"), (false, "http://a.example/v2"), (false, "http://a.example/v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0354 : TestCase where
  name := "1val1literalStemMinusliteral3_v2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(false, "v1"), (false, "v2"), (false, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v2")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0355 : TestCase where
  name := "1val1literalStemMinusliteral3_v3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(false, "v1"), (false, "v2"), (false, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v3")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0356 : TestCase where
  name := "1val1literalStemMinusliteral3_passLv1a"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(false, "v1"), (false, "v2"), (false, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v1a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0357 : TestCase where
  name := "1val1literalStemMinusliteralStem3_passLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(true, "v1"), (true, "v2"), (true, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0358 : TestCase where
  name := "1val1literalStemMinusliteralStem3_passLv4"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(true, "v1"), (true, "v2"), (true, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v4")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0359 : TestCase where
  name := "1val1literalStemMinusliteralStem3_v1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(true, "v1"), (true, "v2"), (true, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v1")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0360 : TestCase where
  name := "1val1literalStemMinusliteralStem3_v2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(true, "v1"), (true, "v2"), (true, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v2")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0361 : TestCase where
  name := "1val1literalStemMinusliteralStem3_v3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(true, "v1"), (true, "v2"), (true, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v3")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0362 : TestCase where
  name := "1val1literalStemMinusliteralStem3_v1a"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.litRange (some "v") [(true, "v1"), (true, "v2"), (true, "v3")]]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v1a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0363 : TestCase where
  name := "1val1language_fail-Iv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0364 : TestCase where
  name := "1val1emptylanguageStem_fail-literal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "ab")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0365 : TestCase where
  name := "1val1emptylanguageStem_fail-empty"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0366 : TestCase where
  name := "1val1emptylanguageStem_fail-integer"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.int 12345)⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0367 : TestCase where
  name := "1val1languageStem_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0368 : TestCase where
  name := "1val1languageStem_fail-Iv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0369 : TestCase where
  name := "1val1languageStemMinuslanguage3_fail-Iv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.none]]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0370 : TestCase where
  name := "1dotOne2dot_pass_p1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0371 : TestCase where
  name := "1dotOne2dot_pass_p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0372 : TestCase where
  name := "1dotOne2dot-oneOf_fail_p1p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0373 : TestCase where
  name := "1dotOne2dot-someOf_fail_p1p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0374 : TestCase where
  name := "open1dotOneopen2dotcloseclose_pass_p1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0375 : TestCase where
  name := "open1dotOneopen2dotcloseclose_pass_p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0376 : TestCase where
  name := "open1dotOneopen2dotcloseclose_fail_p1p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0377 : TestCase where
  name := "openopen1dotOne1dotclose1dotclose_pass_p1p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any")) (.tc "http://a.example/p3" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0378 : TestCase where
  name := "openopen1dotOne1dotclose1dotclose_pass_p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any")) (.tc "http://a.example/p3" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0379 : TestCase where
  name := "openopen1dotOne1dotclose1dotclose_fail_p1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any")) (.tc "http://a.example/p3" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0380 : TestCase where
  name := "openopen1dotOne1dotclose1dotclose_fail_p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any")) (.tc "http://a.example/p3" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0381 : TestCase where
  name := "openopen1dotOne1dotclose1dotclose_fail_p1p2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any")) (.tc "http://a.example/p3" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0382 : TestCase where
  name := "1val1vExprRefIRIREF1_fail-lit-short"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vc1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vc1", (.constraint (NC.all [NC.isLiteral, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/vc1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcd")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0383 : TestCase where
  name := "1val1vExprRefIRIREF1_pass-lit-equal"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vc1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vc1", (.constraint (NC.all [NC.isLiteral, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/vc1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcde")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0384 : TestCase where
  name := "1val1vExprRefbnode1_fail-lit-short"
  group := "structural"
  schema :=
    { Y := ["_:vc1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("_:vc1", (.constraint (NC.all [NC.isLiteral, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "_:vc1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcd")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0385 : TestCase where
  name := "1val1vExprRefbnode1_pass-lit-equal"
  group := "structural"
  schema :=
    { Y := ["_:vc1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("_:vc1", (.constraint (NC.all [NC.isLiteral, NC.minLength 5]))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "_:vc1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "abcde")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0386 : TestCase where
  name := "1dotShapeAND1dot3X_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩) (.and (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩) (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩))))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .lit (.str "X")⟩, ⟨.iri "http://a.example/n1", "http://a.example/p2", .lit (.str "X")⟩, ⟨.iri "http://a.example/n1", "http://a.example/p3", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0387 : TestCase where
  name := "1dotShapeAND1dot3X_fail"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩) (.and (.ofShape ⟨false, none, (.tc "http://a.example/p2" "#any")⟩) (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩))))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n2", "http://a.example/p2", .lit (.str "X")⟩, ⟨.iri "http://a.example/n2", "http://a.example/p3", .lit (.str "X")⟩, ⟨.iri "http://a.example/n2", "http://a.example/p4", .lit (.str "X")⟩]
  focus := .iri "http://a.example/n2"
  shape := "http://a.example/S1"
  expected := false

def t0388 : TestCase where
  name := "1NOTIRI_passLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.isIri])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0389 : TestCase where
  name := "1NOTIRI_failIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.isIri])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0390 : TestCase where
  name := "1NOTIRI_failempty"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.isIri])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0391 : TestCase where
  name := "1NOTNOTIRI_failLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.not (.constraint (NC.all [NC.isIri]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0392 : TestCase where
  name := "1NOTNOTIRI_passIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.not (.constraint (NC.all [NC.isIri]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0393 : TestCase where
  name := "1NOTvs_failIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0394 : TestCase where
  name := "1NOTvs_passIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0395 : TestCase where
  name := "1NOTvs_failempty"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0396 : TestCase where
  name := "1NOTNOTvs_passIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0397 : TestCase where
  name := "1NOTNOTvs_failIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0398 : TestCase where
  name := "1NOTdot_failIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.ofShape ⟨false, none, .empty⟩))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0399 : TestCase where
  name := "1NOTdot_failIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.ofShape ⟨false, none, .empty⟩))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0400 : TestCase where
  name := "1NOTdot_failempty"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.ofShape ⟨false, none, .empty⟩))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0401 : TestCase where
  name := "1NOTNOTdot_passIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.not (.ofShape ⟨false, none, .empty⟩)))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0402 : TestCase where
  name := "1NOTNOTdot_passIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.not (.ofShape ⟨false, none, .empty⟩)))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0403 : TestCase where
  name := "1_NOTliteral_ANDvs_passIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0404 : TestCase where
  name := "1_NOTliteral_ANDvs_failIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0405 : TestCase where
  name := "1_NOTliteral_ANDvs_failLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0406 : TestCase where
  name := "1NOT_literalANDvs__passIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.and (.constraint (NC.all [NC.isLiteral])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0407 : TestCase where
  name := "1NOT_literalANDvs__passLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.and (.constraint (NC.all [NC.isLiteral])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0408 : TestCase where
  name := "1NOTliteralANDvs_passIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0409 : TestCase where
  name := "1NOTliteralANDvs_failIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0410 : TestCase where
  name := "1NOTliteralANDvs_failLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0411 : TestCase where
  name := "1_NOTvs_ANDvs_failIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0412 : TestCase where
  name := "1_NOTvs_ANDvs_passIv2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0413 : TestCase where
  name := "1_NOTvs_ANDvs_failIv3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0414 : TestCase where
  name := "1NOT_vsANDvs__passIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.and (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0415 : TestCase where
  name := "1NOT_vsANDvs__passIv2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.and (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0416 : TestCase where
  name := "1NOT_vsANDvs__passIv3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.and (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0417 : TestCase where
  name := "1NOTvsANDvs_failIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0418 : TestCase where
  name := "1NOTvsANDvs_passIv2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0419 : TestCase where
  name := "1NOTvsANDvs_failIv3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.and (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0420 : TestCase where
  name := "1_NOTliteral_ORvs_passIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0421 : TestCase where
  name := "1_NOTliteral_ORvs_passIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0422 : TestCase where
  name := "1_NOTliteral_ORvs_failLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0423 : TestCase where
  name := "1NOT_literalORvs__failIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.or (.constraint (NC.all [NC.isLiteral])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0424 : TestCase where
  name := "1NOT_literalORvs__passIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.or (.constraint (NC.all [NC.isLiteral])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0425 : TestCase where
  name := "1NOT_literalORvs__failLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.or (.constraint (NC.all [NC.isLiteral])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0426 : TestCase where
  name := "1NOTliteralORvs_passIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0427 : TestCase where
  name := "1NOTliteralORvs_passIo1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0428 : TestCase where
  name := "1NOTliteralORvs_failLv"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.isLiteral]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "v")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0429 : TestCase where
  name := "1_NOTvs_ORvs_failIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0430 : TestCase where
  name := "1_NOTvs_ORvs_passIv2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0431 : TestCase where
  name := "1_NOTvs_ORvs_passIv3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0432 : TestCase where
  name := "1NOT_vsORvs__failIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.or (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0433 : TestCase where
  name := "1NOT_vsORvs__failIv2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.or (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0434 : TestCase where
  name := "1NOT_vsORvs__passIv3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.or (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]])) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]]))))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0435 : TestCase where
  name := "1NOTvsORvs_failIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0436 : TestCase where
  name := "1NOTvsORvs_passIv2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0437 : TestCase where
  name := "1NOTvsORvs_passIv3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.or (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1"]]))) (.constraint (NC.all [NC.values [VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0438 : TestCase where
  name := "NOT1NOTvs_passIv1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0439 : TestCase where
  name := "NOT1NOTvs_passIv2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0440 : TestCase where
  name := "NOT1NOTvs_failIv3"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.not (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2"]])))),
        ("http://a.example/S1", (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "http://a.example/S1#1")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v3"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0441 : TestCase where
  name := "open3Onedotclosecard2_fail-p1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0442 : TestCase where
  name := "open3Onedotclosecard2_pass-p1X2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0443 : TestCase where
  name := "open3Onedotclosecard2_fail-p1X3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0444 : TestCase where
  name := "open3Onedotclosecard2_fail-p1X4"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-3")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0445 : TestCase where
  name := "open3Onedotclosecard2_pass-p1p2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0446 : TestCase where
  name := "open3Onedotclosecard2_pass-p1p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0447 : TestCase where
  name := "open3Onedotclosecard2_pass-p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0448 : TestCase where
  name := "open3Onedotclosecard2_fail-p1p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0449 : TestCase where
  name := "open3Onedotclosecard23_fail-p1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0450 : TestCase where
  name := "open3Onedotclosecard23_pass-p1X2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0451 : TestCase where
  name := "open3Onedotclosecard23_pass-p1X3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0452 : TestCase where
  name := "open3Onedotclosecard23_fail-p1X4"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-3")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0453 : TestCase where
  name := "open3Onedotclosecard23_pass-p1p2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0454 : TestCase where
  name := "open3Onedotclosecard23_pass-p1p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0455 : TestCase where
  name := "open3Onedotclosecard23_pass-p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0456 : TestCase where
  name := "open3Onedotclosecard23_pass-p1p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0457 : TestCase where
  name := "open4Onedotclosecard23_fail-p1p2p3p4"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.choice (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any")))) (.seq (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.choice (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any")))) (.choice (.choice (.tc "http://a.example/p1" "#any") (.choice (.tc "http://a.example/p2" "#any") (.choice (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any")))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p4", .lit (.str "p4-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0458 : TestCase where
  name := "open3Eachdotclosecard23_pass-p1p2p3X3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.seq (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) (.choice (.seq (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any"))) .empty)))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-2")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := true

def t0459 : TestCase where
  name := "1dotClosed_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨true, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0460 : TestCase where
  name := "1dotClosed_fail_lower"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨true, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p0", .iri "http://a.example/o0"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0461 : TestCase where
  name := "1dotClosed_fail_higher"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨true, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0462 : TestCase where
  name := "1val1IRIREFExtra1_pass-iri1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0463 : TestCase where
  name := "1val1IRIREFExtra1_pass-iri2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0464 : TestCase where
  name := "1val1IRIREFExtra1Closed_pass-iri1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨true, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0465 : TestCase where
  name := "1val1IRIREFExtra1Closed_pass-iri2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨true, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0466 : TestCase where
  name := "1val1IRIREFExtra1Closed_fail-iri2_higher"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨true, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0467 : TestCase where
  name := "1val1IRIREFClosedExtra1_pass-iri1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨true, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0468 : TestCase where
  name := "1val1IRIREFClosedExtra1_pass-iri2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨true, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0469 : TestCase where
  name := "1val1IRIREFClosedExtra1_fail-iri2_higher"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨true, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0470 : TestCase where
  name := "1val2IRIREFExtra1_fail-iri2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1", VI.iri "http://a.example/o2"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0471 : TestCase where
  name := "1val2IRIREFPlusExtra1_pass-iri2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1", VI.iri "http://a.example/o2"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.star (.tc "http://a.example/p1" "http://a.example/S1#1")))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0472 : TestCase where
  name := "1val2IRIREFExtra1_pass-iri-bnode"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1", VI.iri "http://a.example/o2"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .bnode "o2"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0473 : TestCase where
  name := "1val1IRIREFExtra1p2_pass-iri1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p2"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0474 : TestCase where
  name := "1val1IRIREFExtra1p2_fail-iri2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p2"}), (.tc "http://a.example/p1" "http://a.example/S1#1")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0475 : TestCase where
  name := "1dotOne2dotExtra-someOf_pass_p1p2p3"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.choice (.tc "http://a.example/p1" "#any") (.seq (.tc "http://a.example/p2" "#any") (.tc "http://a.example/p3" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/p1", .lit (.str "p1-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p2", .lit (.str "p2-0")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/p3", .lit (.str "p3-0")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S1"
  expected := false

def t0476 : TestCase where
  name := "1val1IRIREFExtra1One_pass-iri1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.choice (.tc "http://a.example/p0" "#any") (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.choice (.tc "http://a.example/p2" "#any") .empty)))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0477 : TestCase where
  name := "1val1IRIREFExtra1One_pass-iri2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1#1", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.choice (.tc "http://a.example/p0" "#any") (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.choice (.tc "http://a.example/p2" "#any") .empty)))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0478 : TestCase where
  name := "1dotExtra1_pass-iri1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0479 : TestCase where
  name := "1dotExtra1_fail-iri2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1"}), (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0480 : TestCase where
  name := "3EachdotExtra3_pass-iri1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1#2", "http://a.example/S1#3", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1#2", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o2"]]))),
        ("http://a.example/S1#3", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o3"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1", "http://a.example/p2", "http://a.example/p3"}), (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.seq (.tc "http://a.example/p2" "http://a.example/S1#2") (.tc "http://a.example/p3" "http://a.example/S1#3")))⟩))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s", "http://a.example/p2", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s", "http://a.example/p3", .iri "http://a.example/o3"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := true

def t0481 : TestCase where
  name := "3Eachdot3Extra_pass-iri1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1#2", "http://a.example/S1#3", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1#2", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o2"]]))),
        ("http://a.example/S1#3", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o3"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1", "http://a.example/p2", "http://a.example/p3"}), (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.seq (.tc "http://a.example/p2" "http://a.example/S1#2") (.tc "http://a.example/p3" "http://a.example/S1#3")))⟩))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s", "http://a.example/p2", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s", "http://a.example/p3", .iri "http://a.example/o3"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := true

def t0482 : TestCase where
  name := "3EachdotExtra3NLex_pass-iri1"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1#2", "http://a.example/S1#3", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1#2", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o2"]]))),
        ("http://a.example/S1#3", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o3"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1", "http://a.example/p2", "http://a.example/p3"}), (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.seq (.tc "http://a.example/p2" "http://a.example/S1#2") (.tc "http://a.example/p3" "http://a.example/S1#3")))⟩))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s", "http://a.example/p2", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s", "http://a.example/p3", .iri "http://a.example/o3"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := true

def t0483 : TestCase where
  name := "3EachdotExtra3_pass-iri2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1#2", "http://a.example/S1#3", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1#2", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o2"]]))),
        ("http://a.example/S1#3", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o3"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1", "http://a.example/p2", "http://a.example/p3"}), (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.seq (.tc "http://a.example/p2" "http://a.example/S1#2") (.tc "http://a.example/p3" "http://a.example/S1#3")))⟩))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1a"⟩, ⟨.iri "http://a.example/s", "http://a.example/p2", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s", "http://a.example/p2", .iri "http://a.example/o2a"⟩, ⟨.iri "http://a.example/s", "http://a.example/p3", .iri "http://a.example/o3"⟩, ⟨.iri "http://a.example/s", "http://a.example/p3", .iri "http://a.example/o3a"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := true

def t0484 : TestCase where
  name := "3Eachdot3Extra_pass-iri2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1#2", "http://a.example/S1#3", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1#2", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o2"]]))),
        ("http://a.example/S1#3", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o3"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1", "http://a.example/p2", "http://a.example/p3"}), (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.seq (.tc "http://a.example/p2" "http://a.example/S1#2") (.tc "http://a.example/p3" "http://a.example/S1#3")))⟩))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1a"⟩, ⟨.iri "http://a.example/s", "http://a.example/p2", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s", "http://a.example/p2", .iri "http://a.example/o2a"⟩, ⟨.iri "http://a.example/s", "http://a.example/p3", .iri "http://a.example/o3"⟩, ⟨.iri "http://a.example/s", "http://a.example/p3", .iri "http://a.example/o3a"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := true

def t0485 : TestCase where
  name := "3EachdotExtra3NLex_pass-iri2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1#1", "http://a.example/S1#2", "http://a.example/S1#3", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1#1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o1"]]))),
        ("http://a.example/S1#2", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o2"]]))),
        ("http://a.example/S1#3", (.constraint (NC.all [NC.values [VI.iri "http://a.example/o3"]]))),
        ("http://a.example/S1", (.ofShape ⟨false, (some {"http://a.example/p1", "http://a.example/p2", "http://a.example/p3"}), (.seq (.tc "http://a.example/p1" "http://a.example/S1#1") (.seq (.tc "http://a.example/p2" "http://a.example/S1#2") (.tc "http://a.example/p3" "http://a.example/S1#3")))⟩))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1a"⟩, ⟨.iri "http://a.example/s", "http://a.example/p2", .iri "http://a.example/o2"⟩, ⟨.iri "http://a.example/s", "http://a.example/p2", .iri "http://a.example/o2a"⟩, ⟨.iri "http://a.example/s", "http://a.example/p3", .iri "http://a.example/o3"⟩, ⟨.iri "http://a.example/s", "http://a.example/p3", .iri "http://a.example/o3a"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := true

def t0486 : TestCase where
  name := "1dotAnnotIRIREF_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0487 : TestCase where
  name := "1dotAnnotIRIREF_missing"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0488 : TestCase where
  name := "1dotPlusAnnotIRIREF_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any")))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0489 : TestCase where
  name := "1dotAnnotAIRIREF_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0490 : TestCase where
  name := "1dotAnnotSTRING_LITERAL1_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0491 : TestCase where
  name := "1dotAnnot3_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0492 : TestCase where
  name := "1dotAnnot3_missing"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0493 : TestCase where
  name := "1dotShapeAnnotIRIREF_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0494 : TestCase where
  name := "1dotShapeAnnotIRIREF_missing"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0495 : TestCase where
  name := "1dotShapePlusAnnotIRIREF_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.star (.tc "http://a.example/p1" "#any")))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p1", .lit (.str "a")⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0496 : TestCase where
  name := "1dotShapeAnnotAIRIREF_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0497 : TestCase where
  name := "1dotShapeAnnotSTRING_LITERAL1_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0498 : TestCase where
  name := "2val1refvsAnnot_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S#1", "http://a.example/S", "http://a.example/NC"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S#1", (.constraint (NC.all [NC.values [VI.int 1, VI.int 5]]))),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "http://a.example/S#1") (.tc "http://a.example/p2" "http://a.example/NC"))⟩)),
        ("http://a.example/NC", (.constraint (NC.all [NC.values [VI.int 2, VI.int 6]])))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .lit (.int 1)⟩, ⟨.iri "http://a.example/n1", "http://a.example/p2", .lit (.int 2)⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S"
  expected := true

def t0499 : TestCase where
  name := "0focusIRI_other"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isIri])) (.ofShape ⟨false, none, .empty⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0500 : TestCase where
  name := "0focusIRI_other_fail-bnodeFocusLabel"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isIri])) (.ofShape ⟨false, none, .empty⟩)))] }
  data := [⟨.bnode "abcd", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcd"
  shape := "http://a.example/S1"
  expected := false

def t0501 : TestCase where
  name := "0focusIRI_empty"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isIri])) (.ofShape ⟨false, none, .empty⟩)))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0502 : TestCase where
  name := "0focusBNODE_empty_fail-iriFocusLabel"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isBNode])) (.ofShape ⟨false, none, .empty⟩)))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0503 : TestCase where
  name := "0focusBNODE_other_fail-iriFocusLabel"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isBNode])) (.ofShape ⟨false, none, .empty⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0504 : TestCase where
  name := "0focusBNODE_other"
  group := "structural"
  schema :=
    { Y := ["http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isBNode])) (.ofShape ⟨false, none, .empty⟩)))] }
  data := [⟨.bnode "abcd", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcd"
  shape := "http://a.example/S1"
  expected := true

def t0505 : TestCase where
  name := "1focusIRI_dot_fail-bnodeFocusLabel"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isIri])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcd", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcd"
  shape := "http://a.example/S1"
  expected := false

def t0506 : TestCase where
  name := "1focusIRI_dot_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isIri])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0507 : TestCase where
  name := "1focusBNODE_dot_fail-iriFocusLabel-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isBNode])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0508 : TestCase where
  name := "1focusBNODE_dot_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isBNode])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrs", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrs"
  shape := "http://a.example/S1"
  expected := true

def t0509 : TestCase where
  name := "1focusnonLiteral-dot_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isNonLiteral])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0510 : TestCase where
  name := "focusvs_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1"⟩]
  focus := .iri "http://a.example/v1"
  shape := "http://a.example/vs1"
  expected := true

def t0511 : TestCase where
  name := "focusvs_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/v1a"⟩]
  focus := .iri "http://a.example/v1a"
  shape := "http://a.example/vs1"
  expected := false

def t0512 : TestCase where
  name := "1focusvsANDdatatype_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.and (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])) (.constraint (NC.all [NC.never]))))] }
  data := []
  focus := .iri "http://a.example/v1"
  shape := "http://a.example/vs1"
  expected := false

def t0513 : TestCase where
  name := "1focusvsANDIRI_pass"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.and (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])) (.constraint (NC.all [NC.isIri]))))] }
  data := []
  focus := .iri "http://a.example/v1"
  shape := "http://a.example/vs1"
  expected := true

def t0514 : TestCase where
  name := "1focusvsANDIRI_fail"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.and (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])) (.constraint (NC.all [NC.isIri]))))] }
  data := []
  focus := .iri "http://a.example/v4"
  shape := "http://a.example/vs1"
  expected := false

def t0515 : TestCase where
  name := "1focusvsORdatatype_pass-val"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.or (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])) (.constraint (NC.all [NC.never]))))] }
  data := []
  focus := .iri "http://a.example/v1"
  shape := "http://a.example/vs1"
  expected := true

def t0516 : TestCase where
  name := "1focusvsORdatatype_fail-val"
  group := "structural"
  schema :=
    { Y := ["http://a.example/vs1"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/vs1", (.or (.constraint (NC.all [NC.values [VI.iri "http://a.example/v1", VI.iri "http://a.example/v2", VI.iri "http://a.example/v3"]])) (.constraint (NC.all [NC.never]))))] }
  data := []
  focus := .iri "http://a.example/v4"
  shape := "http://a.example/vs1"
  expected := false

def t0517 : TestCase where
  name := "1focusLength-dot_fail-iri-short"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := false

def t0518 : TestCase where
  name := "1focusLength-dot_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0519 : TestCase where
  name := "1focusLength-dot_fail-iri-long"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1a", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1a"
  shape := "http://a.example/S1"
  expected := false

def t0520 : TestCase where
  name := "1focusLength-dot_fail-bnode-short"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcd", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcd"
  shape := "http://a.example/S1"
  expected := false

def t0521 : TestCase where
  name := "1focusLength-dot_pass-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrs", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrs"
  shape := "http://a.example/S1"
  expected := true

def t0522 : TestCase where
  name := "1focusLength-dot_fail-bnode-long"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrst", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrst"
  shape := "http://a.example/S1"
  expected := false

def t0523 : TestCase where
  name := "1focusMinLength-dot_fail-iri-short"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.minLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := false

def t0524 : TestCase where
  name := "1focusMinLength-dot_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.minLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0525 : TestCase where
  name := "1focusMinLength-dot_pass-iri-long"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.minLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1a", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1a"
  shape := "http://a.example/S1"
  expected := true

def t0526 : TestCase where
  name := "1focusMinLength-dot_fail-bnode-short"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.minLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcd", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcd"
  shape := "http://a.example/S1"
  expected := false

def t0527 : TestCase where
  name := "1focusMinLength-dot_pass-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.minLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrs", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrs"
  shape := "http://a.example/S1"
  expected := true

def t0528 : TestCase where
  name := "1focusMinLength-dot_pass-bnode-long"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.minLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrst", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrst"
  shape := "http://a.example/S1"
  expected := true

def t0529 : TestCase where
  name := "1focusMaxLength-dot_pass-iri-short"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.maxLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := true

def t0530 : TestCase where
  name := "1focusMaxLength-dot_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.maxLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0531 : TestCase where
  name := "1focusMaxLength-dot_fail-iri-long"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.maxLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1a", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1a"
  shape := "http://a.example/S1"
  expected := false

def t0532 : TestCase where
  name := "1focusMaxLength-dot_pass-bnode-short"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.maxLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcd", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcd"
  shape := "http://a.example/S1"
  expected := true

def t0533 : TestCase where
  name := "1focusMaxLength-dot_pass-bnode-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.maxLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrs", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrs"
  shape := "http://a.example/S1"
  expected := true

def t0534 : TestCase where
  name := "1focusMaxLength-dot_fail-bnode-long"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.maxLength 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrst", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrst"
  shape := "http://a.example/S1"
  expected := false

def t0535 : TestCase where
  name := "1focusIRILength_dot_fail-bnodeFocusLabel-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isIri, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrs", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrs"
  shape := "http://a.example/S1"
  expected := false

def t0536 : TestCase where
  name := "1focusIRILength_dot_fail-short"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isIri, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s"
  shape := "http://a.example/S1"
  expected := false

def t0537 : TestCase where
  name := "1focusIRILength_dot_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isIri, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0538 : TestCase where
  name := "1focusIRILength_dot_fail-long"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isIri, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1a", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1a"
  shape := "http://a.example/S1"
  expected := false

def t0539 : TestCase where
  name := "1focusBNODELength_dot_fail-iriFocusLabel-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isBNode, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0540 : TestCase where
  name := "1focusBNODELength_dot_fail-short"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isBNode, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcd", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcd"
  shape := "http://a.example/S1"
  expected := false

def t0541 : TestCase where
  name := "1focusBNODELength_dot_pass"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isBNode, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrs", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrs"
  shape := "http://a.example/S1"
  expected := true

def t0542 : TestCase where
  name := "1focusBNODELength_dot_fail-long"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isBNode, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.bnode "abcdefghijklmnopqrst", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .bnode "abcdefghijklmnopqrst"
  shape := "http://a.example/S1"
  expected := false

def t0543 : TestCase where
  name := "1focusnonLiteralLength-dot_pass-iri-equal"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.constraint (NC.all [NC.isNonLiteral, NC.length 19])) (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0544 : TestCase where
  name := "NOT1dotOR2dot_pass-empty"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)))] }
  data := []
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0545 : TestCase where
  name := "NOT1dotOR2dot_pass-NoShape1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p2", .iri "http://a.example/n2"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0546 : TestCase where
  name := "NOT1dotOR2dot_pass-Shape2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n1", "http://a.example/p2", .iri "http://a.example/n3"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0547 : TestCase where
  name := "NOT1dotOR2dot_fail-Shape2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0548 : TestCase where
  name := "NOT1dotOR2dotX3_pass-empty"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any"))⟩)) (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p5" "#any") (.tc "http://a.example/p6" "#any"))⟩)))))] }
  data := []
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0549 : TestCase where
  name := "NOT1dotOR2dotX3_pass-NoShape1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any"))⟩)) (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p5" "#any") (.tc "http://a.example/p6" "#any"))⟩)))))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p2", .iri "http://a.example/n2"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0550 : TestCase where
  name := "NOT1dotOR2dotX3_pass-Shape2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any"))⟩)) (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p5" "#any") (.tc "http://a.example/p6" "#any"))⟩)))))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n1", "http://a.example/p2", .iri "http://a.example/n3"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0551 : TestCase where
  name := "NOT1dotOR2dotX3_fail-Shape2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any"))⟩)) (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p5" "#any") (.tc "http://a.example/p6" "#any"))⟩)))))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0552 : TestCase where
  name := "NOT1dotOR2dotX3AND1_fail-empty"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p5" "#any") (.tc "http://a.example/p6" "#any"))⟩)) (.or (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩) (.or (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩) (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)))))))] }
  data := []
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0553 : TestCase where
  name := "NOT1dotOR2dotX3AND1_fail-NoShape1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p5" "#any") (.tc "http://a.example/p6" "#any"))⟩)) (.or (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩) (.or (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩) (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)))))))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p2", .iri "http://a.example/n2"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0554 : TestCase where
  name := "NOT1dotOR2dotX3AND1_pass-Shape2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p5" "#any") (.tc "http://a.example/p6" "#any"))⟩)) (.or (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩) (.or (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩) (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)))))))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩, ⟨.iri "http://a.example/n1", "http://a.example/p2", .iri "http://a.example/n3"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := true

def t0555 : TestCase where
  name := "NOT1dotOR2dotX3AND1_fail-Shape2"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p3" "#any") (.tc "http://a.example/p4" "#any"))⟩)) (.and (.or (.not (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)) (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p5" "#any") (.tc "http://a.example/p6" "#any"))⟩)) (.or (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩) (.or (.ofShape ⟨false, none, (.tc "http://a.example/p3" "#any")⟩) (.ofShape ⟨false, none, (.tc "http://a.example/p5" "#any")⟩)))))))] }
  data := [⟨.iri "http://a.example/n1", "http://a.example/p1", .iri "http://a.example/n2"⟩]
  focus := .iri "http://a.example/n1"
  shape := "http://a.example/S1"
  expected := false

def t0556 : TestCase where
  name := "false-lead-excluding-value-shape"
  group := "structural"
  schema :=
    { Y := ["http://a.example.org/S#1", "#any", "http://a.example.org/S", "http://a.example.org/T1", "http://a.example.org/T2", "http://a.example.org/T3", "http://a.example.org/T4"],
      X := [],
      A := [],
      defs := [
        ("http://a.example.org/S#1", (.constraint (NC.all [NC.isInteger]))),
        ("#any", (.constraint NC.any)),
        ("http://a.example.org/S", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example.org/T1")) (.seq (.choice (.tc "http://a.example/a" "http://a.example.org/T2") (.tc "http://a.example/b" "http://a.example.org/S#1")) (.tc "http://a.example/b" "#any")))⟩)),
        ("http://a.example.org/T1", (.ofShape ⟨false, none, (.tc "http://a.example/b" "http://a.example.org/T3")⟩)),
        ("http://a.example.org/T2", (.ofShape ⟨false, none, (.tc "http://a.example/b" "http://a.example.org/T4")⟩)),
        ("http://a.example.org/T3", (.ofShape ⟨false, none, (.tc "http://a.example/c" "#any")⟩)),
        ("http://a.example.org/T4", (.ofShape ⟨false, none, (.tc "http://a.example/d" "#any")⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .iri "http://shextest.example/validation/x1"⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .iri "http://shextest.example/validation/x2"⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .iri "http://shextest.example/validation/x3"⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .iri "http://shextest.example/validation/x4"⟩, ⟨.iri "http://shextest.example/validation/x1", "http://a.example/b", .iri "http://shextest.example/validation/y1"⟩, ⟨.iri "http://shextest.example/validation/x2", "http://a.example/b", .iri "http://shextest.example/validation/y2"⟩, ⟨.iri "http://shextest.example/validation/x3", "http://a.example/b", .iri "http://shextest.example/validation/y3"⟩, ⟨.iri "http://shextest.example/validation/y1", "http://a.example/c", .lit (.int 1)⟩, ⟨.iri "http://shextest.example/validation/y2", "http://a.example/d", .lit (.int 2)⟩, ⟨.iri "http://shextest.example/validation/y3", "http://a.example/c", .lit (.int 3)⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example.org/S"
  expected := true

def t0557 : TestCase where
  name := "nPlus1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example.org/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example.org/S", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "#any")) (.seq (.choice (.seq (.tc "http://a.example/a" "#any") (.star (.tc "http://a.example/a" "#any"))) (.tc "http://a.example/a" "#any")) (.tc "http://a.example/a" "#any")))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.int 1)⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.int 3)⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example.org/S"
  expected := true

def t0558 : TestCase where
  name := "nPlus1-greedy-rewrite"
  group := "structural"
  schema :=
    { Y := ["http://a.example.org/S#1", "http://a.example.org/S#2", "http://a.example.org/S#3", "http://a.example.org/S#4", "http://a.example.org/S"],
      X := [],
      A := [],
      defs := [
        ("http://a.example.org/S#1", (.constraint (NC.all [NC.values [VI.int 1]]))),
        ("http://a.example.org/S#2", (.constraint (NC.all [NC.values [VI.int 2]]))),
        ("http://a.example.org/S#3", (.constraint (NC.all [NC.values [VI.int 3]]))),
        ("http://a.example.org/S#4", (.constraint (NC.all [NC.values [VI.int 4]]))),
        ("http://a.example.org/S", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/a" "http://a.example.org/S#1") (.seq (.choice (.seq (.tc "http://a.example/a" "http://a.example.org/S#2") (.star (.tc "http://a.example/a" "http://a.example.org/S#2"))) (.tc "http://a.example/a" "http://a.example.org/S#3")) (.star (.tc "http://a.example/a" "http://a.example.org/S#4"))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.int 1)⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.int 3)⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example.org/S"
  expected := true

def t0559 : TestCase where
  name := "skipped"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example.org/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example.org/S", (.ofShape ⟨false, none, (.seq (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty) (.tc "http://a.example/c" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.int 1)⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example.org/S"
  expected := true

def t0560 : TestCase where
  name := "open2Eachdotclosecard25c1dot"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.seq (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) (.seq (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) (.seq (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty) (.seq (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty) (.choice (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any")) .empty))))) (.tc "http://a.example/c" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0561 : TestCase where
  name := "2Eachdot"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/a" "#any") (.tc "http://a.example/b" "#any"))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/s0", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/s0", "http://a.example/b", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/s0"
  shape := "http://a.example/S"
  expected := true

def t0562 : TestCase where
  name := "PstarT"
  group := "structural"
  schema :=
    { Y := ["http://a.example/base/P", "http://a.example/base/T", "http://a.example/base/S1", "http://a.example/base/S2", "http://a.example/base/S3", "http://a.example/base/S4"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/base/P", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/p", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/T", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/t", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/S1", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.tc "http://a.example/a" "http://a.example/base/T"))⟩)),
        ("http://a.example/base/S2", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/a" "http://a.example/base/P") (.star (.tc "http://a.example/a" "http://a.example/base/T")))⟩)),
        ("http://a.example/base/S3", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.star (.tc "http://a.example/a" "http://a.example/base/T")))⟩)),
        ("http://a.example/base/S4", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "http://a.example/base/P") (.tc "http://a.example/a" "http://a.example/base/P")) (.seq (.tc "http://a.example/a" "http://a.example/base/T") (.tc "http://a.example/a" "http://a.example/base/T")))⟩))] }
  data := [⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/p"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt1"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt2"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/t"⟩]
  focus := .iri "http://a.example/base/n"
  shape := "http://a.example/base/S1"
  expected := true

def t0563 : TestCase where
  name := "PTstar"
  group := "structural"
  schema :=
    { Y := ["http://a.example/base/P", "http://a.example/base/T", "http://a.example/base/S1", "http://a.example/base/S2", "http://a.example/base/S3", "http://a.example/base/S4"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/base/P", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/p", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/T", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/t", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/S1", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.tc "http://a.example/a" "http://a.example/base/T"))⟩)),
        ("http://a.example/base/S2", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/a" "http://a.example/base/P") (.star (.tc "http://a.example/a" "http://a.example/base/T")))⟩)),
        ("http://a.example/base/S3", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.star (.tc "http://a.example/a" "http://a.example/base/T")))⟩)),
        ("http://a.example/base/S4", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "http://a.example/base/P") (.tc "http://a.example/a" "http://a.example/base/P")) (.seq (.tc "http://a.example/a" "http://a.example/base/T") (.tc "http://a.example/a" "http://a.example/base/T")))⟩))] }
  data := [⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/p"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt1"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt2"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/t"⟩]
  focus := .iri "http://a.example/base/n"
  shape := "http://a.example/base/S2"
  expected := true

def t0564 : TestCase where
  name := "PTstar-greedy-rewrite"
  group := "structural"
  schema :=
    { Y := ["http://a.example/base/P", "http://a.example/base/T", "http://a.example/base/S1", "http://a.example/base/S2", "http://a.example/base/S3", "http://a.example/base/S4"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/base/P", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/p", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/T", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/t", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/S1", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.tc "http://a.example/a" "http://a.example/base/T"))⟩)),
        ("http://a.example/base/S2", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/T")) (.tc "http://a.example/a" "http://a.example/base/P"))⟩)),
        ("http://a.example/base/S3", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.star (.tc "http://a.example/a" "http://a.example/base/T")))⟩)),
        ("http://a.example/base/S4", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "http://a.example/base/P") (.tc "http://a.example/a" "http://a.example/base/P")) (.seq (.tc "http://a.example/a" "http://a.example/base/T") (.tc "http://a.example/a" "http://a.example/base/T")))⟩))] }
  data := [⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/p"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt1"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt2"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/t"⟩]
  focus := .iri "http://a.example/base/n"
  shape := "http://a.example/base/S2"
  expected := true

def t0565 : TestCase where
  name := "PstarTstar"
  group := "structural"
  schema :=
    { Y := ["http://a.example/base/P", "http://a.example/base/T", "http://a.example/base/S1", "http://a.example/base/S2", "http://a.example/base/S3", "http://a.example/base/S4"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/base/P", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/p", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/T", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/t", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/S1", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.tc "http://a.example/a" "http://a.example/base/T"))⟩)),
        ("http://a.example/base/S2", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/a" "http://a.example/base/P") (.star (.tc "http://a.example/a" "http://a.example/base/T")))⟩)),
        ("http://a.example/base/S3", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.star (.tc "http://a.example/a" "http://a.example/base/T")))⟩)),
        ("http://a.example/base/S4", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "http://a.example/base/P") (.tc "http://a.example/a" "http://a.example/base/P")) (.seq (.tc "http://a.example/a" "http://a.example/base/T") (.tc "http://a.example/a" "http://a.example/base/T")))⟩))] }
  data := [⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/p"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt1"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt2"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/t"⟩]
  focus := .iri "http://a.example/base/n"
  shape := "http://a.example/base/S3"
  expected := true

def t0566 : TestCase where
  name := "P2T2"
  group := "structural"
  schema :=
    { Y := ["http://a.example/base/P", "http://a.example/base/T", "http://a.example/base/S1", "http://a.example/base/S2", "http://a.example/base/S3", "http://a.example/base/S4"],
      X := [],
      A := [],
      defs := [
        ("http://a.example/base/P", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/p", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/T", (.constraint (NC.all [NC.values [VI.iri "http://a.example/base/t", VI.iri "http://a.example/base/pt1", VI.iri "http://a.example/base/pt2"]]))),
        ("http://a.example/base/S1", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.tc "http://a.example/a" "http://a.example/base/T"))⟩)),
        ("http://a.example/base/S2", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/a" "http://a.example/base/P") (.star (.tc "http://a.example/a" "http://a.example/base/T")))⟩)),
        ("http://a.example/base/S3", (.ofShape ⟨false, none, (.seq (.star (.tc "http://a.example/a" "http://a.example/base/P")) (.star (.tc "http://a.example/a" "http://a.example/base/T")))⟩)),
        ("http://a.example/base/S4", (.ofShape ⟨false, none, (.seq (.seq (.tc "http://a.example/a" "http://a.example/base/P") (.tc "http://a.example/a" "http://a.example/base/P")) (.seq (.tc "http://a.example/a" "http://a.example/base/T") (.tc "http://a.example/a" "http://a.example/base/T")))⟩))] }
  data := [⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/p"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt1"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/pt2"⟩, ⟨.iri "http://a.example/base/n", "http://a.example/a", .iri "http://a.example/base/t"⟩]
  focus := .iri "http://a.example/base/n"
  shape := "http://a.example/base/S4"
  expected := true

def t0567 : TestCase where
  name := "8dot5a2b1c_pass-a5b2c1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.seq (.tc "http://a.example/b" "#any") (.tc "http://a.example/c" "#any"))))))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "4")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "5")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := true

def t0568 : TestCase where
  name := "8dot5a2b1c_fail-a5b1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.seq (.tc "http://a.example/b" "#any") (.tc "http://a.example/c" "#any"))))))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "4")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "5")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0569 : TestCase where
  name := "8dot5a2b1c_fail-a6b2c1"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/a" "#any") (.seq (.tc "http://a.example/b" "#any") (.seq (.tc "http://a.example/b" "#any") (.tc "http://a.example/c" "#any"))))))))⟩))] }
  data := [⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "3")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "4")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "5")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/a", .lit (.str "6")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "1")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/b", .lit (.str "2")⟩, ⟨.iri "http://shextest.example/validation/x", "http://a.example/c", .lit (.str "1")⟩]
  focus := .iri "http://shextest.example/validation/x"
  shape := "http://a.example/S"
  expected := false

def t0570 : TestCase where
  name := "1dot_fail-empty-err"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := []
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0571 : TestCase where
  name := "2dot_fail-empty-err"
  group := "structural"
  schema :=
    { Y := ["#any", "http://a.example/S1"],
      X := [],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ofShape ⟨false, none, (.seq (.tc "http://a.example/p1" "#any") (.tc "http://a.example/p2" "#any"))⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

/-- The structural tests. -/
def tests : List TestCase := [t0000, t0001, t0002, t0003, t0004, t0005, t0006, t0007, t0008, t0009, t0010, t0011, t0012, t0013, t0014, t0015, t0016, t0017, t0018, t0019, t0020, t0021, t0022, t0023, t0024, t0025, t0026, t0027, t0028, t0029, t0030, t0031, t0032, t0033, t0034, t0035, t0036, t0037, t0038, t0039, t0040, t0041, t0042, t0043, t0044, t0045, t0046, t0047, t0048, t0049, t0050, t0051, t0052, t0053, t0054, t0055, t0056, t0057, t0058, t0059, t0060, t0061, t0062, t0063, t0064, t0065, t0066, t0067, t0068, t0069, t0070, t0071, t0072, t0073, t0074, t0075, t0076, t0077, t0078, t0079, t0080, t0081, t0082, t0083, t0084, t0085, t0086, t0087, t0088, t0089, t0090, t0091, t0092, t0093, t0094, t0095, t0096, t0097, t0098, t0099, t0100, t0101, t0102, t0103, t0104, t0105, t0106, t0107, t0108, t0109, t0110, t0111, t0112, t0113, t0114, t0115, t0116, t0117, t0118, t0119, t0120, t0121, t0122, t0123, t0124, t0125, t0126, t0127, t0128, t0129, t0130, t0131, t0132, t0133, t0134, t0135, t0136, t0137, t0138, t0139, t0140, t0141, t0142, t0143, t0144, t0145, t0146, t0147, t0148, t0149, t0150, t0151, t0152, t0153, t0154, t0155, t0156, t0157, t0158, t0159, t0160, t0161, t0162, t0163, t0164, t0165, t0166, t0167, t0168, t0169, t0170, t0171, t0172, t0173, t0174, t0175, t0176, t0177, t0178, t0179, t0180, t0181, t0182, t0183, t0184, t0185, t0186, t0187, t0188, t0189, t0190, t0191, t0192, t0193, t0194, t0195, t0196, t0197, t0198, t0199, t0200, t0201, t0202, t0203, t0204, t0205, t0206, t0207, t0208, t0209, t0210, t0211, t0212, t0213, t0214, t0215, t0216, t0217, t0218, t0219, t0220, t0221, t0222, t0223, t0224, t0225, t0226, t0227, t0228, t0229, t0230, t0231, t0232, t0233, t0234, t0235, t0236, t0237, t0238, t0239, t0240, t0241, t0242, t0243, t0244, t0245, t0246, t0247, t0248, t0249, t0250, t0251, t0252, t0253, t0254, t0255, t0256, t0257, t0258, t0259, t0260, t0261, t0262, t0263, t0264, t0265, t0266, t0267, t0268, t0269, t0270, t0271, t0272, t0273, t0274, t0275, t0276, t0277, t0278, t0279, t0280, t0281, t0282, t0283, t0284, t0285, t0286, t0287, t0288, t0289, t0290, t0291, t0292, t0293, t0294, t0295, t0296, t0297, t0298, t0299, t0300, t0301, t0302, t0303, t0304, t0305, t0306, t0307, t0308, t0309, t0310, t0311, t0312, t0313, t0314, t0315, t0316, t0317, t0318, t0319, t0320, t0321, t0322, t0323, t0324, t0325, t0326, t0327, t0328, t0329, t0330, t0331, t0332, t0333, t0334, t0335, t0336, t0337, t0338, t0339, t0340, t0341, t0342, t0343, t0344, t0345, t0346, t0347, t0348, t0349, t0350, t0351, t0352, t0353, t0354, t0355, t0356, t0357, t0358, t0359, t0360, t0361, t0362, t0363, t0364, t0365, t0366, t0367, t0368, t0369, t0370, t0371, t0372, t0373, t0374, t0375, t0376, t0377, t0378, t0379, t0380, t0381, t0382, t0383, t0384, t0385, t0386, t0387, t0388, t0389, t0390, t0391, t0392, t0393, t0394, t0395, t0396, t0397, t0398, t0399, t0400, t0401, t0402, t0403, t0404, t0405, t0406, t0407, t0408, t0409, t0410, t0411, t0412, t0413, t0414, t0415, t0416, t0417, t0418, t0419, t0420, t0421, t0422, t0423, t0424, t0425, t0426, t0427, t0428, t0429, t0430, t0431, t0432, t0433, t0434, t0435, t0436, t0437, t0438, t0439, t0440, t0441, t0442, t0443, t0444, t0445, t0446, t0447, t0448, t0449, t0450, t0451, t0452, t0453, t0454, t0455, t0456, t0457, t0458, t0459, t0460, t0461, t0462, t0463, t0464, t0465, t0466, t0467, t0468, t0469, t0470, t0471, t0472, t0473, t0474, t0475, t0476, t0477, t0478, t0479, t0480, t0481, t0482, t0483, t0484, t0485, t0486, t0487, t0488, t0489, t0490, t0491, t0492, t0493, t0494, t0495, t0496, t0497, t0498, t0499, t0500, t0501, t0502, t0503, t0504, t0505, t0506, t0507, t0508, t0509, t0510, t0511, t0512, t0513, t0514, t0515, t0516, t0517, t0518, t0519, t0520, t0521, t0522, t0523, t0524, t0525, t0526, t0527, t0528, t0529, t0530, t0531, t0532, t0533, t0534, t0535, t0536, t0537, t0538, t0539, t0540, t0541, t0542, t0543, t0544, t0545, t0546, t0547, t0548, t0549, t0550, t0551, t0552, t0553, t0554, t0555, t0556, t0557, t0558, t0559, t0560, t0561, t0562, t0563, t0564, t0565, t0566, t0567, t0568, t0569, t0570, t0571]

end ShexTests.Structural
