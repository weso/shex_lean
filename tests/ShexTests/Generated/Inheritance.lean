-- `tests/tools/gen_shextest.py` writes this file. Do not edit it.
import ShexTests.Harness

namespace ShexTests.Inheritance

open ShexTests
open ShexLean hiding Schema
open ShexLean.InheritanceCore hiding Schema

def t0000 : TestCase where
  name := "1dot2SameExtends_pass"
  group := "inheritance"
  schema :=
    { Y := ["#any"],
      X := ["http://a.example/A", "http://a.example/B"],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/B", (.ext [] ⟨false, none, (.tc "http://a.example/p2" "#any")⟩)),
        ("http://a.example/A", (.ext ["http://a.example/B", "http://a.example/B"] ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/A"
  expected := true

def t0001 : TestCase where
  name := "extends-abstract-multi-empty_fail-Ref2ExtraP"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/IssueShape", "http://a.example/PersonShape#1", "http://a.example/PersonShape#2", "http://a.example/PersonShape#3", "http://a.example/PersonShape#4", "http://a.example/RepShape#5"],
      X := ["http://a.example/EmployeeShape", "http://a.example/PersonShape", "http://a.example/RepShape", "http://a.example/UserShape"],
      A := ["http://a.example/PersonShape", "http://a.example/RepShape"],
      defs := [
        ("http://a.example/IssueShape", (.ofShape ⟨true, none, (.seq (.tc "http://ex.example/#reportedBy" "http://a.example/PersonShape") (.choice (.tc "http://ex.example/#reproducedBy" "http://a.example/EmployeeShape") .empty))⟩)),
        ("http://a.example/PersonShape#1", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#3", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#4", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/PersonShape", (.ext [] ⟨false, none, (.seq (.choice (.tc "http://xmlns.com/foaf/name" "http://a.example/PersonShape#1") (.seq (.seq (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2") (.star (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2"))) (.tc "http://xmlns.com/foaf/familyName" "http://a.example/PersonShape#3"))) (.tc "http://xmlns.com/foaf/mbox" "http://a.example/PersonShape#4"))⟩)),
        ("http://a.example/UserShape", (.ext ["http://a.example/PersonShape"] ⟨true, none, (.tc "http://ex.example/#representative" "http://a.example/EmployeeShape")⟩)),
        ("http://a.example/RepShape#5", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/RepShape", (.ext [] ⟨false, none, (.seq (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5") (.star (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5")))⟩)),
        ("http://a.example/EmployeeShape", (.ext ["http://a.example/PersonShape", "http://a.example/RepShape"] ⟨true, none, .empty⟩))] }
  data := [⟨.iri "http://a.example/Issue1", "http://ex.example/#reportedBy", .iri "http://a.example/User2"⟩, ⟨.iri "http://a.example/Issue1", "http://ex.example/#reproducedBy", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/Thompson.J", "http://ex.example/#p", .lit (.int 1)⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/familyName", .lit (.str "Thompson")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joe")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joseph")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/mbox", .iri "mail:joe@example.org"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/phone", .iri "tel:+456"⟩, ⟨.iri "http://a.example/User2", "http://ex.example/#representative", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/familyName", .lit (.str "Smith")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/givenName", .lit (.str "Bob")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/mbox", .iri "mail:bob@example.org"⟩]
  focus := .iri "http://a.example/Issue1"
  shape := "http://a.example/IssueShape"
  expected := false

def t0002 : TestCase where
  name := "extends-abstract-multi-empty_fail-Ref1ExtraP"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/IssueShape", "http://a.example/PersonShape#1", "http://a.example/PersonShape#2", "http://a.example/PersonShape#3", "http://a.example/PersonShape#4", "http://a.example/RepShape#5"],
      X := ["http://a.example/EmployeeShape", "http://a.example/PersonShape", "http://a.example/RepShape", "http://a.example/UserShape"],
      A := ["http://a.example/PersonShape", "http://a.example/RepShape"],
      defs := [
        ("http://a.example/IssueShape", (.ofShape ⟨true, none, (.seq (.tc "http://ex.example/#reportedBy" "http://a.example/PersonShape") (.choice (.tc "http://ex.example/#reproducedBy" "http://a.example/EmployeeShape") .empty))⟩)),
        ("http://a.example/PersonShape#1", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#3", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#4", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/PersonShape", (.ext [] ⟨false, none, (.seq (.choice (.tc "http://xmlns.com/foaf/name" "http://a.example/PersonShape#1") (.seq (.seq (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2") (.star (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2"))) (.tc "http://xmlns.com/foaf/familyName" "http://a.example/PersonShape#3"))) (.tc "http://xmlns.com/foaf/mbox" "http://a.example/PersonShape#4"))⟩)),
        ("http://a.example/UserShape", (.ext ["http://a.example/PersonShape"] ⟨true, none, (.tc "http://ex.example/#representative" "http://a.example/EmployeeShape")⟩)),
        ("http://a.example/RepShape#5", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/RepShape", (.ext [] ⟨false, none, (.seq (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5") (.star (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5")))⟩)),
        ("http://a.example/EmployeeShape", (.ext ["http://a.example/PersonShape", "http://a.example/RepShape"] ⟨true, none, .empty⟩))] }
  data := [⟨.iri "http://a.example/Issue1", "http://ex.example/#reportedBy", .iri "http://a.example/User2"⟩, ⟨.iri "http://a.example/Issue1", "http://ex.example/#reproducedBy", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/familyName", .lit (.str "Thompson")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joe")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joseph")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/mbox", .iri "mail:joe@example.org"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/phone", .iri "tel:+456"⟩, ⟨.iri "http://a.example/User2", "http://ex.example/#p", .lit (.int 1)⟩, ⟨.iri "http://a.example/User2", "http://ex.example/#representative", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/familyName", .lit (.str "Smith")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/givenName", .lit (.str "Bob")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/mbox", .iri "mail:bob@example.org"⟩]
  focus := .iri "http://a.example/Issue1"
  shape := "http://a.example/IssueShape"
  expected := false

def t0003 : TestCase where
  name := "extends-abstract-multi-empty_fail-ReferrerExtraP"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/IssueShape", "http://a.example/PersonShape#1", "http://a.example/PersonShape#2", "http://a.example/PersonShape#3", "http://a.example/PersonShape#4", "http://a.example/RepShape#5"],
      X := ["http://a.example/EmployeeShape", "http://a.example/PersonShape", "http://a.example/RepShape", "http://a.example/UserShape"],
      A := ["http://a.example/PersonShape", "http://a.example/RepShape"],
      defs := [
        ("http://a.example/IssueShape", (.ofShape ⟨true, none, (.seq (.tc "http://ex.example/#reportedBy" "http://a.example/PersonShape") (.choice (.tc "http://ex.example/#reproducedBy" "http://a.example/EmployeeShape") .empty))⟩)),
        ("http://a.example/PersonShape#1", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#3", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#4", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/PersonShape", (.ext [] ⟨false, none, (.seq (.choice (.tc "http://xmlns.com/foaf/name" "http://a.example/PersonShape#1") (.seq (.seq (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2") (.star (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2"))) (.tc "http://xmlns.com/foaf/familyName" "http://a.example/PersonShape#3"))) (.tc "http://xmlns.com/foaf/mbox" "http://a.example/PersonShape#4"))⟩)),
        ("http://a.example/UserShape", (.ext ["http://a.example/PersonShape"] ⟨true, none, (.tc "http://ex.example/#representative" "http://a.example/EmployeeShape")⟩)),
        ("http://a.example/RepShape#5", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/RepShape", (.ext [] ⟨false, none, (.seq (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5") (.star (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5")))⟩)),
        ("http://a.example/EmployeeShape", (.ext ["http://a.example/PersonShape", "http://a.example/RepShape"] ⟨true, none, .empty⟩))] }
  data := [⟨.iri "http://a.example/Issue1", "http://ex.example/#p", .lit (.int 1)⟩, ⟨.iri "http://a.example/Issue1", "http://ex.example/#reportedBy", .iri "http://a.example/User2"⟩, ⟨.iri "http://a.example/Issue1", "http://ex.example/#reproducedBy", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/familyName", .lit (.str "Thompson")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joe")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joseph")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/mbox", .iri "mail:joe@example.org"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/phone", .iri "tel:+456"⟩, ⟨.iri "http://a.example/User2", "http://ex.example/#representative", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/familyName", .lit (.str "Smith")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/givenName", .lit (.str "Bob")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/mbox", .iri "mail:bob@example.org"⟩]
  focus := .iri "http://a.example/Issue1"
  shape := "http://a.example/IssueShape"
  expected := false

def t0004 : TestCase where
  name := "extends-abstract-multi-empty_fail-Ref1ExtraOR"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/IssueShape", "http://a.example/PersonShape#1", "http://a.example/PersonShape#2", "http://a.example/PersonShape#3", "http://a.example/PersonShape#4", "http://a.example/RepShape#5"],
      X := ["http://a.example/EmployeeShape", "http://a.example/PersonShape", "http://a.example/RepShape", "http://a.example/UserShape"],
      A := ["http://a.example/PersonShape", "http://a.example/RepShape"],
      defs := [
        ("http://a.example/IssueShape", (.ofShape ⟨true, none, (.seq (.tc "http://ex.example/#reportedBy" "http://a.example/PersonShape") (.choice (.tc "http://ex.example/#reproducedBy" "http://a.example/EmployeeShape") .empty))⟩)),
        ("http://a.example/PersonShape#1", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#3", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#4", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/PersonShape", (.ext [] ⟨false, none, (.seq (.choice (.tc "http://xmlns.com/foaf/name" "http://a.example/PersonShape#1") (.seq (.seq (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2") (.star (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2"))) (.tc "http://xmlns.com/foaf/familyName" "http://a.example/PersonShape#3"))) (.tc "http://xmlns.com/foaf/mbox" "http://a.example/PersonShape#4"))⟩)),
        ("http://a.example/UserShape", (.ext ["http://a.example/PersonShape"] ⟨true, none, (.tc "http://ex.example/#representative" "http://a.example/EmployeeShape")⟩)),
        ("http://a.example/RepShape#5", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/RepShape", (.ext [] ⟨false, none, (.seq (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5") (.star (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5")))⟩)),
        ("http://a.example/EmployeeShape", (.ext ["http://a.example/PersonShape", "http://a.example/RepShape"] ⟨true, none, .empty⟩))] }
  data := [⟨.iri "http://a.example/Issue1", "http://ex.example/#reportedBy", .iri "http://a.example/User2"⟩, ⟨.iri "http://a.example/Issue1", "http://ex.example/#reproducedBy", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/familyName", .lit (.str "Thompson")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joe")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joseph")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/mbox", .iri "mail:joe@example.org"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/phone", .iri "tel:+456"⟩, ⟨.iri "http://a.example/User2", "http://ex.example/#representative", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/familyName", .lit (.str "Smith")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/givenName", .lit (.str "Bob")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/mbox", .iri "mail:bob@example.org"⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/name", .lit (.str "Bob Smith")⟩]
  focus := .iri "http://a.example/Issue1"
  shape := "http://a.example/IssueShape"
  expected := false

def t0005 : TestCase where
  name := "extends-abstract-multi-empty_fail-missingRef2"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/IssueShape", "http://a.example/PersonShape#1", "http://a.example/PersonShape#2", "http://a.example/PersonShape#3", "http://a.example/PersonShape#4", "http://a.example/RepShape#5"],
      X := ["http://a.example/EmployeeShape", "http://a.example/PersonShape", "http://a.example/RepShape", "http://a.example/UserShape"],
      A := ["http://a.example/PersonShape", "http://a.example/RepShape"],
      defs := [
        ("http://a.example/IssueShape", (.ofShape ⟨true, none, (.seq (.tc "http://ex.example/#reportedBy" "http://a.example/PersonShape") (.choice (.tc "http://ex.example/#reproducedBy" "http://a.example/EmployeeShape") .empty))⟩)),
        ("http://a.example/PersonShape#1", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#3", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#4", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/PersonShape", (.ext [] ⟨false, none, (.seq (.choice (.tc "http://xmlns.com/foaf/name" "http://a.example/PersonShape#1") (.seq (.seq (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2") (.star (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2"))) (.tc "http://xmlns.com/foaf/familyName" "http://a.example/PersonShape#3"))) (.tc "http://xmlns.com/foaf/mbox" "http://a.example/PersonShape#4"))⟩)),
        ("http://a.example/UserShape", (.ext ["http://a.example/PersonShape"] ⟨true, none, (.tc "http://ex.example/#representative" "http://a.example/EmployeeShape")⟩)),
        ("http://a.example/RepShape#5", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/RepShape", (.ext [] ⟨false, none, (.seq (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5") (.star (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5")))⟩)),
        ("http://a.example/EmployeeShape", (.ext ["http://a.example/PersonShape", "http://a.example/RepShape"] ⟨true, none, .empty⟩))] }
  data := [⟨.iri "http://a.example/Issue1", "http://ex.example/#reproducedBy", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/familyName", .lit (.str "Thompson")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joe")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joseph")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/mbox", .iri "mail:joe@example.org"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/phone", .iri "tel:+456"⟩, ⟨.iri "http://a.example/User2", "http://ex.example/#representative", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/familyName", .lit (.str "Smith")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/givenName", .lit (.str "Bob")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/mbox", .iri "mail:bob@example.org"⟩]
  focus := .iri "http://a.example/Issue1"
  shape := "http://a.example/IssueShape"
  expected := false

def t0006 : TestCase where
  name := "extends-abstract-multi-empty_pass-missingOptRef1"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/IssueShape", "http://a.example/PersonShape#1", "http://a.example/PersonShape#2", "http://a.example/PersonShape#3", "http://a.example/PersonShape#4", "http://a.example/RepShape#5"],
      X := ["http://a.example/EmployeeShape", "http://a.example/PersonShape", "http://a.example/RepShape", "http://a.example/UserShape"],
      A := ["http://a.example/PersonShape", "http://a.example/RepShape"],
      defs := [
        ("http://a.example/IssueShape", (.ofShape ⟨true, none, (.seq (.tc "http://ex.example/#reportedBy" "http://a.example/PersonShape") (.choice (.tc "http://ex.example/#reproducedBy" "http://a.example/EmployeeShape") .empty))⟩)),
        ("http://a.example/PersonShape#1", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#3", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#4", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/PersonShape", (.ext [] ⟨false, none, (.seq (.choice (.tc "http://xmlns.com/foaf/name" "http://a.example/PersonShape#1") (.seq (.seq (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2") (.star (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2"))) (.tc "http://xmlns.com/foaf/familyName" "http://a.example/PersonShape#3"))) (.tc "http://xmlns.com/foaf/mbox" "http://a.example/PersonShape#4"))⟩)),
        ("http://a.example/UserShape", (.ext ["http://a.example/PersonShape"] ⟨true, none, (.tc "http://ex.example/#representative" "http://a.example/EmployeeShape")⟩)),
        ("http://a.example/RepShape#5", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/RepShape", (.ext [] ⟨false, none, (.seq (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5") (.star (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5")))⟩)),
        ("http://a.example/EmployeeShape", (.ext ["http://a.example/PersonShape", "http://a.example/RepShape"] ⟨true, none, .empty⟩))] }
  data := [⟨.iri "http://a.example/Issue1", "http://ex.example/#reportedBy", .iri "http://a.example/User2"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/familyName", .lit (.str "Thompson")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joe")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joseph")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/mbox", .iri "mail:joe@example.org"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/phone", .iri "tel:+456"⟩, ⟨.iri "http://a.example/User2", "http://ex.example/#representative", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/familyName", .lit (.str "Smith")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/givenName", .lit (.str "Bob")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/mbox", .iri "mail:bob@example.org"⟩]
  focus := .iri "http://a.example/Issue1"
  shape := "http://a.example/IssueShape"
  expected := true

def t0007 : TestCase where
  name := "extends-abstract-multi-empty_pass"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/IssueShape", "http://a.example/PersonShape#1", "http://a.example/PersonShape#2", "http://a.example/PersonShape#3", "http://a.example/PersonShape#4", "http://a.example/RepShape#5"],
      X := ["http://a.example/EmployeeShape", "http://a.example/PersonShape", "http://a.example/RepShape", "http://a.example/UserShape"],
      A := ["http://a.example/PersonShape", "http://a.example/RepShape"],
      defs := [
        ("http://a.example/IssueShape", (.ofShape ⟨true, none, (.seq (.tc "http://ex.example/#reportedBy" "http://a.example/PersonShape") (.choice (.tc "http://ex.example/#reproducedBy" "http://a.example/EmployeeShape") .empty))⟩)),
        ("http://a.example/PersonShape#1", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#2", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#3", (.constraint (NC.all [NC.isString]))),
        ("http://a.example/PersonShape#4", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/PersonShape", (.ext [] ⟨false, none, (.seq (.choice (.tc "http://xmlns.com/foaf/name" "http://a.example/PersonShape#1") (.seq (.seq (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2") (.star (.tc "http://xmlns.com/foaf/givenName" "http://a.example/PersonShape#2"))) (.tc "http://xmlns.com/foaf/familyName" "http://a.example/PersonShape#3"))) (.tc "http://xmlns.com/foaf/mbox" "http://a.example/PersonShape#4"))⟩)),
        ("http://a.example/UserShape", (.ext ["http://a.example/PersonShape"] ⟨true, none, (.tc "http://ex.example/#representative" "http://a.example/EmployeeShape")⟩)),
        ("http://a.example/RepShape#5", (.constraint (NC.all [NC.isIri]))),
        ("http://a.example/RepShape", (.ext [] ⟨false, none, (.seq (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5") (.star (.tc "http://xmlns.com/foaf/phone" "http://a.example/RepShape#5")))⟩)),
        ("http://a.example/EmployeeShape", (.ext ["http://a.example/PersonShape", "http://a.example/RepShape"] ⟨true, none, .empty⟩))] }
  data := [⟨.iri "http://a.example/Issue1", "http://ex.example/#reportedBy", .iri "http://a.example/User2"⟩, ⟨.iri "http://a.example/Issue1", "http://ex.example/#reproducedBy", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/familyName", .lit (.str "Thompson")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joe")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/givenName", .lit (.str "Joseph")⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/mbox", .iri "mail:joe@example.org"⟩, ⟨.iri "http://a.example/Thompson.J", "http://xmlns.com/foaf/phone", .iri "tel:+456"⟩, ⟨.iri "http://a.example/User2", "http://ex.example/#representative", .iri "http://a.example/Thompson.J"⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/familyName", .lit (.str "Smith")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/givenName", .lit (.str "Bob")⟩, ⟨.iri "http://a.example/User2", "http://xmlns.com/foaf/mbox", .iri "mail:bob@example.org"⟩]
  focus := .iri "http://a.example/Issue1"
  shape := "http://a.example/IssueShape"
  expected := true

def t0008 : TestCase where
  name := "1dotAbstract_fail-abstract"
  group := "inheritance"
  schema :=
    { Y := ["#any"],
      X := ["http://a.example/S1"],
      A := ["http://a.example/S1"],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ext [] ⟨false, none, (.tc "http://a.example/p1" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0009 : TestCase where
  name := "extends-closed-diamond_pass-bottom"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩]
  focus := .iri "http://a.example/pass-bottom"
  shape := "http://a.example/BOTTOM"
  expected := true

def t0010 : TestCase where
  name := "extends-closed-diamond_fail-no-G0"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩]
  focus := .iri "http://a.example/no-G0"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0011 : TestCase where
  name := "extends-closed-diamond_fail-no-G0-0"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩]
  focus := .iri "http://a.example/no-G0-0"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0012 : TestCase where
  name := "extends-closed-diamond_fail-no-G0-1"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩]
  focus := .iri "http://a.example/no-G0-1"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0013 : TestCase where
  name := "extends-closed-diamond_fail-no_BOTTOM"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩]
  focus := .iri "http://a.example/no_BOTTOM"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0014 : TestCase where
  name := "extends-closed-diamond_fail-two-G0s"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩]
  focus := .iri "http://a.example/two-G0s"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0015 : TestCase where
  name := "extends-closed-diamond_fail-two-G0-0s"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩]
  focus := .iri "http://a.example/two-G0-0s"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0016 : TestCase where
  name := "extends-closed-diamond_fail-two-BOTTOMS"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-1", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩]
  focus := .iri "http://a.example/two-BOTTOMS"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0017 : TestCase where
  name := "extends-closed-3diamond-split_pass-bottom"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-0-0#3", "http://a.example/G0_0-0#4", "http://a.example/BOTTOM#5"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-0-0#3", (.constraint (NC.all [NC.values [VI.str "G0-0-0A", VI.str "G0-0-0B", VI.str "G0-0-0C"]]))),
        ("http://a.example/G0-0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0-0#3")⟩)),
        ("http://a.example/G0_0-0#4", (.constraint (NC.all [NC.values [VI.str "G0_0-0A", VI.str "G0_0-0B", VI.str "G0_0-0C"]]))),
        ("http://a.example/G0_0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0_0-0#4")⟩)),
        ("http://a.example/BOTTOM#5", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#5")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩]
  focus := .iri "http://a.example/pass-bottom"
  shape := "http://a.example/BOTTOM"
  expected := true

def t0018 : TestCase where
  name := "extends-closed-3diamond-split_fail-no-G0-0"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-0-0#3", "http://a.example/G0_0-0#4", "http://a.example/BOTTOM#5"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-0-0#3", (.constraint (NC.all [NC.values [VI.str "G0-0-0A", VI.str "G0-0-0B", VI.str "G0-0-0C"]]))),
        ("http://a.example/G0-0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0-0#3")⟩)),
        ("http://a.example/G0_0-0#4", (.constraint (NC.all [NC.values [VI.str "G0_0-0A", VI.str "G0_0-0B", VI.str "G0_0-0C"]]))),
        ("http://a.example/G0_0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0_0-0#4")⟩)),
        ("http://a.example/BOTTOM#5", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#5")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩]
  focus := .iri "http://a.example/no-G0-0"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0019 : TestCase where
  name := "extends-closed-3diamond-split_fail-no-G0-0-0"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-0-0#3", "http://a.example/G0_0-0#4", "http://a.example/BOTTOM#5"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-0-0#3", (.constraint (NC.all [NC.values [VI.str "G0-0-0A", VI.str "G0-0-0B", VI.str "G0-0-0C"]]))),
        ("http://a.example/G0-0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0-0#3")⟩)),
        ("http://a.example/G0_0-0#4", (.constraint (NC.all [NC.values [VI.str "G0_0-0A", VI.str "G0_0-0B", VI.str "G0_0-0C"]]))),
        ("http://a.example/G0_0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0_0-0#4")⟩)),
        ("http://a.example/BOTTOM#5", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#5")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩]
  focus := .iri "http://a.example/no-G0-0-0"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0020 : TestCase where
  name := "extends-closed-3diamond-split_fail-no-G0_0-0"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-0-0#3", "http://a.example/G0_0-0#4", "http://a.example/BOTTOM#5"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-0-0#3", (.constraint (NC.all [NC.values [VI.str "G0-0-0A", VI.str "G0-0-0B", VI.str "G0-0-0C"]]))),
        ("http://a.example/G0-0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0-0#3")⟩)),
        ("http://a.example/G0_0-0#4", (.constraint (NC.all [NC.values [VI.str "G0_0-0A", VI.str "G0_0-0B", VI.str "G0_0-0C"]]))),
        ("http://a.example/G0_0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0_0-0#4")⟩)),
        ("http://a.example/BOTTOM#5", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#5")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩]
  focus := .iri "http://a.example/no-G0_0-0"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0021 : TestCase where
  name := "extends-closed-3diamond-split_fail-no_BOTTOM"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-0-0#3", "http://a.example/G0_0-0#4", "http://a.example/BOTTOM#5"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-0-0#3", (.constraint (NC.all [NC.values [VI.str "G0-0-0A", VI.str "G0-0-0B", VI.str "G0-0-0C"]]))),
        ("http://a.example/G0-0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0-0#3")⟩)),
        ("http://a.example/G0_0-0#4", (.constraint (NC.all [NC.values [VI.str "G0_0-0A", VI.str "G0_0-0B", VI.str "G0_0-0C"]]))),
        ("http://a.example/G0_0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0_0-0#4")⟩)),
        ("http://a.example/BOTTOM#5", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#5")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩]
  focus := .iri "http://a.example/no_BOTTOM"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0022 : TestCase where
  name := "extends-closed-3diamond-split_fail-two-G0s"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-0-0#3", "http://a.example/G0_0-0#4", "http://a.example/BOTTOM#5"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-0-0#3", (.constraint (NC.all [NC.values [VI.str "G0-0-0A", VI.str "G0-0-0B", VI.str "G0-0-0C"]]))),
        ("http://a.example/G0-0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0-0#3")⟩)),
        ("http://a.example/G0_0-0#4", (.constraint (NC.all [NC.values [VI.str "G0_0-0A", VI.str "G0_0-0B", VI.str "G0_0-0C"]]))),
        ("http://a.example/G0_0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0_0-0#4")⟩)),
        ("http://a.example/BOTTOM#5", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#5")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩]
  focus := .iri "http://a.example/two-G0s"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0023 : TestCase where
  name := "extends-closed-3diamond-split_fail-two-G0-0s"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-0-0#3", "http://a.example/G0_0-0#4", "http://a.example/BOTTOM#5"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-0-0#3", (.constraint (NC.all [NC.values [VI.str "G0-0-0A", VI.str "G0-0-0B", VI.str "G0-0-0C"]]))),
        ("http://a.example/G0-0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0-0#3")⟩)),
        ("http://a.example/G0_0-0#4", (.constraint (NC.all [NC.values [VI.str "G0_0-0A", VI.str "G0_0-0B", VI.str "G0_0-0C"]]))),
        ("http://a.example/G0_0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0_0-0#4")⟩)),
        ("http://a.example/BOTTOM#5", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#5")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩]
  focus := .iri "http://a.example/two-G0-0s"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0024 : TestCase where
  name := "extends-closed-3diamond-split_fail-two-BOTTOMS"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-0-0#3", "http://a.example/G0_0-0#4", "http://a.example/BOTTOM#5"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"],
      A := [],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-0-0#3", (.constraint (NC.all [NC.values [VI.str "G0-0-0A", VI.str "G0-0-0B", VI.str "G0-0-0C"]]))),
        ("http://a.example/G0-0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0-0#3")⟩)),
        ("http://a.example/G0_0-0#4", (.constraint (NC.all [NC.values [VI.str "G0_0-0A", VI.str "G0_0-0B", VI.str "G0_0-0C"]]))),
        ("http://a.example/G0_0-0", (.ext ["http://a.example/G0", "http://a.example/G0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0_0-0#4")⟩)),
        ("http://a.example/BOTTOM#5", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0", "http://a.example/G0-0-0", "http://a.example/G0_0-0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#5")⟩))] }
  data := [⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0-0-0", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0_0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no_BOTTOM", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/pass-bottom", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "BOTTOMB")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-BOTTOMS", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0-0B")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0-0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0B")⟩, ⟨.iri "http://a.example/two-G0s", "http://a.example/p", .lit (.str "G0_0-0A")⟩]
  focus := .iri "http://a.example/two-BOTTOMS"
  shape := "http://a.example/BOTTOM"
  expected := false

def t0025 : TestCase where
  name := "1dotExtendsBnode_pass"
  group := "inheritance"
  schema :=
    { Y := ["#any"],
      X := ["_:b", "http://a.example/S1"],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ext ["_:b"] ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)),
        ("_:b", (.ext [] ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩, ⟨.iri "http://a.example/s1", "http://a.example/p2", .iri "http://a.example/o2"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := true

def t0026 : TestCase where
  name := "1dotExtendsBnode_fail-p2"
  group := "inheritance"
  schema :=
    { Y := ["#any"],
      X := ["_:b", "http://a.example/S1"],
      A := [],
      defs := [
        ("#any", (.constraint NC.any)),
        ("http://a.example/S1", (.ext ["_:b"] ⟨false, none, (.tc "http://a.example/p1" "#any")⟩)),
        ("_:b", (.ext [] ⟨false, none, (.tc "http://a.example/p2" "#any")⟩))] }
  data := [⟨.iri "http://a.example/s1", "http://a.example/p1", .iri "http://a.example/o1"⟩]
  focus := .iri "http://a.example/s1"
  shape := "http://a.example/S1"
  expected := false

def t0027 : TestCase where
  name := "extends-abstract-closed-diamond_pass-via-G0-0"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := ["http://a.example/G0"],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/only-G0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0A")⟩]
  focus := .iri "http://a.example/via-G0-0"
  shape := "http://a.example/G0"
  expected := true

def t0028 : TestCase where
  name := "extends-abstract-closed-diamond_pass-via-G0-1"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := ["http://a.example/G0"],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/only-G0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0A")⟩]
  focus := .iri "http://a.example/via-G0-1"
  shape := "http://a.example/G0"
  expected := true

def t0029 : TestCase where
  name := "extends-abstract-closed-diamond_pass-via-BOTTOM"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := ["http://a.example/G0"],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/only-G0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0A")⟩]
  focus := .iri "http://a.example/via-BOTTOM"
  shape := "http://a.example/G0"
  expected := true

def t0030 : TestCase where
  name := "extends-abstract-closed-diamond_fail-only-G0"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := ["http://a.example/G0"],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/only-G0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0A")⟩]
  focus := .iri "http://a.example/only-G0"
  shape := "http://a.example/G0"
  expected := false

def t0031 : TestCase where
  name := "extends-abstract-closed-diamond_fail-no-G0"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := ["http://a.example/G0"],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/only-G0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0A")⟩]
  focus := .iri "http://a.example/no-G0"
  shape := "http://a.example/G0"
  expected := false

def t0032 : TestCase where
  name := "extends-abstract-closed-diamond_fail-no-BOTTOM"
  group := "inheritance"
  schema :=
    { Y := ["http://a.example/G0#1", "http://a.example/G0-0#2", "http://a.example/G0-1#3", "http://a.example/BOTTOM#4"],
      X := ["http://a.example/BOTTOM", "http://a.example/G0", "http://a.example/G0-0", "http://a.example/G0-1"],
      A := ["http://a.example/G0"],
      defs := [
        ("http://a.example/G0#1", (.constraint (NC.all [NC.values [VI.str "G0A", VI.str "G0B", VI.str "G0C"]]))),
        ("http://a.example/G0", (.ext [] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0#1")⟩)),
        ("http://a.example/G0-0#2", (.constraint (NC.all [NC.values [VI.str "G0-0A", VI.str "G0-0B", VI.str "G0-0C"]]))),
        ("http://a.example/G0-0", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-0#2")⟩)),
        ("http://a.example/G0-1#3", (.constraint (NC.all [NC.values [VI.str "G0-1A", VI.str "G0-1B", VI.str "G0-1C"]]))),
        ("http://a.example/G0-1", (.ext ["http://a.example/G0"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/G0-1#3")⟩)),
        ("http://a.example/BOTTOM#4", (.constraint (NC.all [NC.values [VI.str "BOTTOMA", VI.str "BOTTOMB", VI.str "BOTTOMC"]]))),
        ("http://a.example/BOTTOM", (.ext ["http://a.example/G0-0", "http://a.example/G0-1"] ⟨true, none, (.tc "http://a.example/p" "http://a.example/BOTTOM#4")⟩))] }
  data := [⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/no-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/no-G0", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/only-G0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "BOTTOMA")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-BOTTOM", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0-0A")⟩, ⟨.iri "http://a.example/via-G0-0", "http://a.example/p", .lit (.str "G0A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0-1A")⟩, ⟨.iri "http://a.example/via-G0-1", "http://a.example/p", .lit (.str "G0A")⟩]
  focus := .iri "http://a.example/no-BOTTOM"
  shape := "http://a.example/G0"
  expected := false

/-- The inheritance tests. -/
def tests : List TestCase := [t0000, t0001, t0002, t0003, t0004, t0005, t0006, t0007, t0008, t0009, t0010, t0011, t0012, t0013, t0014, t0015, t0016, t0017, t0018, t0019, t0020, t0021, t0022, t0023, t0024, t0025, t0026, t0027, t0028, t0029, t0030, t0031, t0032]

end ShexTests.Inheritance
