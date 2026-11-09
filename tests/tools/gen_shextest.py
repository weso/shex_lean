#!/usr/bin/env python3
"""The generator of the Lean test cases from the ShEx test suite.

The ShEx test suite (https://github.com/shexSpec/shexTest) gives each
validation test as a schema in ShExJ (JSON), data in Turtle, a focus node, a
shape label and an expected result. Lean cannot read Turtle. Thus, this
script reads the tests and writes them as Lean values:

    tests/ShexTests/Generated/Structural.lean
    tests/ShexTests/Generated/Inheritance.lean

It also writes `tests/shexTest/SKIPPED.md`: the tests that the 2025
formalism cannot express, with the reason for each test.

Usage:

    # Copy the files that the tests use from a checkout of shexTest into
    # tests/shexTest/ (do this when you update the test suite):
    python3 tests/tools/gen_shextest.py --vendor /path/to/shexTest

    # Generate the Lean files from tests/shexTest/:
    python3 tests/tools/gen_shextest.py

The script reads the Turtle data with rudof (https://rudof-project.github.io),
through its Python package: pip install pyrudof
"""

import argparse
import json
import os
import shutil
import re
import subprocess
import sys

import pyrudof

HERE = os.path.dirname(os.path.abspath(__file__))
TESTS = os.path.dirname(HERE)
SUITE = os.path.join(TESTS, "shexTest")
OUT = os.path.join(TESTS, "ShexTests", "Generated")

XSD = "http://www.w3.org/2001/XMLSchema#"
XSD_STRING = XSD + "string"
XSD_INTEGER = XSD + "integer"

INHERITANCE_TRAITS = {"Extends", "Abstract", "ExtendsDiamond", "MultiExtends"}
# Traits that the formalism or the translation does not support.
UNSUPPORTED_TRAITS = {
    "SemanticAction": "semantic actions",
    "ExternalSemanticAction": "semantic actions",
    "Import": "imports",
    "Include": "triple expression references",
    "ShapeMap": "shape maps",
    "Start": "the start shape",
    "ExternalShape": "external shapes",
    "Inverse": "inverse triple constraints",
}
MAX_CARD = 12
# The base IRI of the data files. The tests resolve relative IRIs in the
# data and in the focus node against the location of the data file.
BASE = "http://shextest.example/validation/"


class Unsupported(Exception):
    pass


# --- Lean syntax --------------------------------------------------------------

def lean_str(s):
    out = []
    for ch in s:
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif ord(ch) < 0x20 or ord(ch) == 0x7F:
            out.append("\\x%02x" % ord(ch))
        else:
            out.append(ch)
    return '"' + "".join(out) + '"'


def lean_list(items):
    return "[" + ", ".join(items) + "]"


def lean_int(k):
    return "(%d)" % k if k < 0 else "%d" % k


# --- RDF data -----------------------------------------------------------------

def canonical_int(lex):
    try:
        k = int(lex)
    except ValueError:
        return None
    return k if str(k) == lex else None


def lean_literal(lex, datatype, lang):
    """The Lean `Literal` of an RDF literal. Only `xsd:string` and canonical
    `xsd:integer` literals exist in `ShexLean/Common/RDF.lean`."""
    if lang:
        raise Unsupported("a literal with a language tag in the data")
    if datatype is None or datatype == XSD_STRING:
        return ".str " + lean_str(lex)
    if datatype == XSD_INTEGER:
        k = canonical_int(lex)
        if k is None:
            raise Unsupported("an xsd:integer literal that is not canonical in the data")
        return ".int " + lean_int(k)
    raise Unsupported("a literal with the datatype <%s> in the data" % datatype)


ESCAPES = {"t": "\t", "b": "\b", "n": "\n", "r": "\r", "f": "\f", '"': '"', "'": "'", "\\": "\\"}


def unescape(lex):
    """The value of a string of N-Triples, with its escape sequences."""
    out, i = [], 0
    while i < len(lex):
        ch = lex[i]
        if ch != "\\":
            out.append(ch)
            i += 1
        elif lex[i + 1] in "uU":
            n = 4 if lex[i + 1] == "u" else 8
            out.append(chr(int(lex[i + 2:i + 2 + n], 16)))
            i += 2 + n
        else:
            out.append(ESCAPES[lex[i + 1]])
            i += 2
    return "".join(out)


def parse_term(t):
    """A term as rudof gives it (N-Triples syntax), as a tuple:
    ("iri", iri), ("bnode", label) or ("lit", lexical form, datatype, lang)."""
    if t.startswith("<"):
        return ("iri", unescape(t[1:-1]))
    if t.startswith("_:"):
        return ("bnode", t[2:])
    m = re.fullmatch(r'"((?:[^"\\]|\\.)*)"(?:@([A-Za-z0-9-]+)|\^\^<([^>]*)>)?', t, re.S)
    if not m:
        raise Unsupported("an RDF term that the generator cannot read: %s" % t)
    return ("lit", unescape(m.group(1)), m.group(3), m.group(2))


def lean_term(t, names):
    if t[0] == "iri":
        return ".iri " + lean_str(t[1])
    if t[0] == "bnode":
        return ".bnode " + lean_str(names[t[1]])
    return ".lit (" + lean_literal(t[1], t[2], t[3]) + ")"


def lean_subject(t, names):
    if t[0] == "lit":
        raise Unsupported("a literal subject")
    return lean_term(t, names)


def read_data(path):
    """The triples of a Turtle file, read with rudof, in a stable order.

    rudof keeps the labels of the blank nodes of the file (`_:b1`). It gives
    a new random label to each anonymous blank node (`[]`). The generator
    renames these nodes `anon1`, `anon2`, ... in the order of their triples,
    so that the output does not change between two runs."""
    with open(path, encoding="utf-8") as f:
        text = f.read()
    r = pyrudof.Rudof(pyrudof.RudofConfig())
    try:
        r.read_data(path, pyrudof.RDFFormat.Turtle, base=BASE + os.path.basename(path),
                    reader_mode=pyrudof.ReaderMode.Strict)
    except Exception as ex:
        raise Unsupported("rudof cannot read the data (%s)" % type(ex).__name__)
    triples = [(parse_term(t.subject), parse_term(t.predicate), parse_term(t.object))
               for t in r.triples()]
    labelled = set(re.findall(r"_:([A-Za-z0-9_.-]+)", text))

    def key(tr):
        return repr(tuple(("bnode", "") if x[0] == "bnode" and x[1] not in labelled else x
                          for x in tr))
    names, k = {}, 0
    for tr in sorted(triples, key=key):
        for x in tr:
            if x[0] == "bnode" and x[1] not in names:
                if x[1] in labelled:
                    names[x[1]] = x[1]
                else:
                    k += 1
                    names[x[1]] = "anon%d" % k
    out = sorted((lean_subject(s, names), lean_str(p[1]), lean_term(o, names))
                 for s, p, o in triples)
    return ["⟨%s, %s, %s⟩" % tr for tr in out], names


def lean_focus(focus, data_file, names):
    from urllib.parse import urljoin
    if isinstance(focus, str):
        if focus.startswith("_:"):
            if focus[2:] not in names:
                raise Unsupported("a blank node focus that is not in the data")
            return ".bnode " + lean_str(focus[2:])
        return ".iri " + lean_str(urljoin(BASE + data_file, focus))
    if isinstance(focus, dict) and "@value" in focus:
        return ".lit (" + lean_literal(focus["@value"], focus.get("@type"), focus.get("@language")) + ")"
    raise Unsupported("a focus node that is not an IRI or a literal")


# --- Node constraints ---------------------------------------------------------

def nc_value(v):
    """One element of a value set, as a `ShexTests.VI` value."""
    if isinstance(v, str):
        return "VI.iri " + lean_str(v)
    t = v.get("type")
    if t is None or "value" in v:
        if "language" in v:
            return "VI.none"
        dt = v.get("type", XSD_STRING)
        if dt == XSD_STRING:
            return "VI.str " + lean_str(v["value"])
        if dt == XSD_INTEGER:
            k = canonical_int(v["value"])
            return "VI.int " + lean_int(k) if k is not None else "VI.none"
        return "VI.none"
    if t == "IriStem":
        return "VI.iriStem " + lean_str(v["stem"])
    if t == "LiteralStem":
        return "VI.litStem " + lean_str(v["stem"])
    if t in ("Language", "LanguageStem", "LanguageStemRange"):
        return "VI.none"
    if t in ("IriStemRange", "LiteralStemRange"):
        kind = "iri" if t == "IriStemRange" else "lit"
        stem = v["stem"]
        stem_l = "none" if isinstance(stem, dict) else "(some %s)" % lean_str(stem)
        excl = []
        for e in v.get("exclusions", []):
            if isinstance(e, str):
                excl.append(lean_str(e))
                excl_kind = "exact"
            else:
                excl.append(lean_str(e["stem"]))
                excl_kind = "stem"
            excl[-1] = "(%s, %s)" % ("true" if excl_kind == "stem" else "false", excl[-1])
        return "VI.%sRange %s %s" % (kind, stem_l, lean_list(excl))
    raise Unsupported("the value set item type %s" % t)


def bound_ints(nc):
    """Integer bounds for the numeric facets. The data has only integers."""
    from fractions import Fraction
    import math
    lo, hi = None, None
    for key in ("mininclusive", "minexclusive", "maxinclusive", "maxexclusive"):
        if key not in nc:
            continue
        try:
            v = Fraction(str(nc[key]))
        except ValueError:
            raise Unsupported("a numeric facet value that is not a decimal")
        if key == "mininclusive":
            b = math.ceil(v)
            lo = b if lo is None else max(lo, b)
        elif key == "minexclusive":
            b = math.floor(v) + 1
            lo = b if lo is None else max(lo, b)
        elif key == "maxinclusive":
            b = math.floor(v)
            hi = b if hi is None else min(hi, b)
        else:
            b = math.ceil(v) - 1
            hi = b if hi is None else min(hi, b)
    return lo, hi


def node_constraint(nc):
    """A Lean expression of type `RDFNode → Bool`."""
    parts = []
    nk = nc.get("nodeKind")
    if nk:
        parts.append({"iri": "NC.isIri", "bnode": "NC.isBNode", "literal": "NC.isLiteral",
                      "nonliteral": "NC.isNonLiteral"}[nk])
    dt = nc.get("datatype")
    if dt:
        if dt == XSD_STRING:
            parts.append("NC.isString")
        elif dt == XSD_INTEGER:
            parts.append("NC.isInteger")
        else:
            parts.append("NC.never")
    if "values" in nc:
        parts.append("NC.values " + lean_list([nc_value(v) for v in nc["values"]]))
    if "pattern" in nc:
        raise Unsupported("the pattern facet")
    for key, f in (("length", "NC.length"), ("minlength", "NC.minLength"),
                   ("maxlength", "NC.maxLength")):
        if key in nc:
            parts.append("%s %d" % (f, nc[key]))
    lo, hi = bound_ints(nc)
    if lo is not None or hi is not None:
        parts.append("NC.intBetween %s %s" % (
            "none" if lo is None else "(some %s)" % lean_int(lo),
            "none" if hi is None else "(some %s)" % lean_int(hi)))
    if "totaldigits" in nc:
        parts.append("NC.totalDigits %d" % nc["totaldigits"])
    if "fractiondigits" in nc:
        parts.append("NC.isInteger")
    if not parts:
        return "NC.any"
    return "NC.all " + lean_list(parts)


# --- Schemas ------------------------------------------------------------------

class SchemaBuilder:
    def __init__(self, schema):
        if schema.get("imports"):
            raise Unsupported("imports")
        if schema.get("startActs"):
            raise Unsupported("semantic actions")
        self.decls = {}
        self.abstract = set()
        for d in schema.get("shapes", []):
            if d.get("type") != "ShapeDecl":
                d = {"id": d["id"], "shapeExpr": d}
            if d.get("abstract"):
                self.abstract.add(d["id"])
            self.decls[d["id"]] = d["shapeExpr"]
        self.defs = {}      # label -> Lean CShape
        self.fresh = 0
        self.X = set(self.abstract)
        for label, se in self.decls.items():
            for t in self.extends_targets(se):
                self.X.add(t)
            if self.top_shape(se) is not None and self.top_shape(se).get("extends"):
                self.X.add(label)

    def extends_targets(self, se):
        if isinstance(se, str) or not isinstance(se, dict):
            return []
        out = list(se.get("extends", []))
        for sub in se.get("shapeExprs", []):
            out += self.extends_targets(sub)
        if "shapeExpr" in se:
            out += self.extends_targets(se["shapeExpr"])
        return out

    def top_shape(self, se):
        """The `Shape` of a definition `extends X h [and u]`, if there is one."""
        if isinstance(se, dict) and se.get("type") == "Shape":
            return se
        if isinstance(se, dict) and se.get("type") == "ShapeAnd":
            shapes = [s for s in se["shapeExprs"] if isinstance(s, dict) and s.get("type") == "Shape"]
            if len(shapes) == 1:
                return shapes[0]
        return None

    def new_label(self, base):
        self.fresh += 1
        return "%s#%d" % (base, self.fresh)

    def value_label(self, ve, base):
        if ve is None:
            if "#any" not in self.defs:
                self.defs["#any"] = "(.constraint NC.any)"
            return "#any"
        if isinstance(ve, str):
            if ve not in self.decls:
                raise Unsupported("a reference to an undefined shape")
            return ve
        label = self.new_label(base)
        self.defs[label] = self.shape_expr(ve, label)
        return label

    def triple_expr(self, te, base):
        if isinstance(te, str):
            raise Unsupported("triple expression references")
        if te.get("semActs"):
            raise Unsupported("semantic actions")
        t = te["type"]
        if t == "TripleConstraint":
            if te.get("inverse"):
                raise Unsupported("inverse triple constraints")
            e = "(.tc %s %s)" % (lean_str(te["predicate"]),
                                 lean_str(self.value_label(te.get("valueExpr"), base)))
        elif t in ("EachOf", "OneOf"):
            subs = [self.triple_expr(x, base) for x in te["expressions"]]
            op = ".seq" if t == "EachOf" else ".choice"
            e = subs[-1]
            for x in reversed(subs[:-1]):
                e = "(%s %s %s)" % (op, x, e)
        else:
            raise Unsupported("the triple expression type %s" % t)
        return self.cardinality(e, te.get("min", 1), te.get("max", 1))

    def cardinality(self, e, lo, hi):
        if lo == 1 and hi == 1:
            return e
        if hi == 0:
            # `e{0}` matches no triple. The predicates of `e` must stay in
            # `props(e)`: a triple with such a predicate is then not allowed.
            return "(.choice .empty %s)" % self.never(e)
        if hi != -1 and (hi < lo or hi > MAX_CARD) or lo > MAX_CARD:
            raise Unsupported("a cardinality larger than %d" % MAX_CARD)
        parts = [e] * lo
        if hi == -1:
            parts.append("(.star %s)" % e)
        else:
            parts += ["(.choice %s .empty)" % e] * (hi - lo)
        if not parts:
            return ".empty"
        out = parts[-1]
        for x in reversed(parts[:-1]):
            out = "(.seq %s %s)" % (x, out)
        return out

    def never(self, e):
        """`e` with each value label replaced by a label that no node has."""
        self.defs["#never"] = "(.constraint NC.never)"
        return re.sub(r'\(\.tc ("(?:[^"\\]|\\.)*") "(?:[^"\\]|\\.)*"\)', r'(.tc \1 "#never")', e)

    def shape(self, sh, base):
        if sh.get("semActs"):
            raise Unsupported("semantic actions")
        expr = sh.get("expression")
        te = ".empty" if expr is None else self.triple_expr(expr, base)
        extra = sh.get("extra")
        extra_l = "none" if not extra else "(some %s)" % ("{" + ", ".join(lean_str(p) for p in extra) + "}")
        closed = "true" if sh.get("closed") else "false"
        return "⟨%s, %s, %s⟩" % (closed, extra_l, te)

    def shape_expr(self, se, base):
        if isinstance(se, str):
            raise Unsupported("a shape reference as a shape expression")
        t = se["type"]
        if t == "Shape":
            h = self.shape(se, base)
            if se.get("extends"):
                return "(.ext %s %s)" % (lean_list([lean_str(x) for x in se["extends"]]), h)
            return "(.ofShape %s)" % h
        if t == "NodeConstraint":
            return "(.constraint (%s))" % node_constraint(se)
        if t in ("ShapeAnd", "ShapeOr"):
            subs = [self.shape_expr(x, base) for x in se["shapeExprs"]]
            op = ".and" if t == "ShapeAnd" else ".or"
            e = subs[-1]
            for x in reversed(subs[:-1]):
                e = "(%s %s %s)" % (op, x, e)
            return e
        if t == "ShapeNot":
            return "(.not %s)" % self.shape_expr(se["shapeExpr"], base)
        if t == "ShapeExternal":
            raise Unsupported("external shapes")
        raise Unsupported("the shape expression type %s" % t)

    def x_def(self, label, se):
        """`extends X h [and u]` for a label of `X` (Definition 2)."""
        top = self.top_shape(se)
        if top is None:
            raise Unsupported("an extendable label whose definition is not a shape")
        h = self.shape(top, label)
        e = "(.ext %s %s)" % (lean_list([lean_str(x) for x in top.get("extends", [])]), h)
        if se is top:
            return e
        rest = [self.shape_expr(x, label) for x in se["shapeExprs"] if x is not top]
        u = rest[-1]
        for x in reversed(rest[:-1]):
            u = "(.and %s %s)" % (x, u)
        return "(.and %s %s)" % (e, u)

    def build(self):
        for label, se in self.decls.items():
            if label in self.X:
                self.defs[label] = self.x_def(label, se)
            else:
                self.defs[label] = self.shape_expr(se, label)
        Y = [l for l in self.defs if l not in self.X]
        X = sorted(self.X)
        for x in X:
            if x not in self.decls:
                raise Unsupported("an extends target that is not defined")
        return {"Y": Y, "X": X, "A": sorted(self.abstract), "defs": self.defs}


def lean_schema(b):
    defs = ",\n        ".join("(%s, %s)" % (lean_str(l), d) for l, d in b["defs"].items())
    return ("{ Y := %s,\n      X := %s,\n      A := %s,\n      defs := [\n        %s] }" % (
        lean_list([lean_str(x) for x in b["Y"]]), lean_list([lean_str(x) for x in b["X"]]),
        lean_list([lean_str(x) for x in b["A"]]), defs))


def uses_inheritance(schema):
    text = json.dumps(schema)
    return '"extends"' in text or '"abstract": true' in text


# --- The manifest -------------------------------------------------------------

def schema_json_path(base, entry):
    shex = entry["action"]["schema"]
    return os.path.normpath(os.path.join(base, "validation", shex[:-len(".shex")] + ".json"))


def entries(base):
    with open(os.path.join(base, "validation", "manifest.jsonld")) as f:
        m = json.load(f)
    return m["@graph"][0]["entries"]


def translate(base, e):
    traits = set(e.get("trait", []))
    for t in sorted(traits):
        if t in UNSUPPORTED_TRAITS:
            raise Unsupported(UNSUPPORTED_TRAITS[t])
    a = e["action"]
    for key in ("map", "shapeExterns", "semActs"):
        if key in a:
            raise Unsupported({"map": "shape maps", "shapeExterns": "external shapes",
                               "semActs": "semantic actions"}[key])
    if "shape" not in a:
        raise Unsupported("the start shape")
    with open(schema_json_path(base, e)) as f:
        schema = json.load(f)
    builder = SchemaBuilder(schema)
    built = builder.build()
    if ":" not in a["shape"]:
        raise Unsupported("relative shape labels")
    if a["shape"] not in built["defs"]:
        raise Unsupported("a focus shape that is not defined")
    data, names = read_data(os.path.join(base, "validation", a["data"]))
    group = "inheritance" if traits & INHERITANCE_TRAITS or uses_inheritance(schema) else "structural"
    expected = "true" if e["@type"] == "sht:ValidationTest" else "false"
    text = ("def %s : TestCase where\n  name := %s\n  group := %s\n  schema :=\n    %s\n"
            "  data := %s\n  focus := %s\n  shape := %s\n  expected := %s\n") % (
        "@@NAME@@", lean_str(e["name"]), lean_str(group), lean_schema(built),
        lean_list(data), lean_focus(a["focus"], a["data"], names), lean_str(a["shape"]), expected)
    return group, text


def vendor(src):
    """Copy the manifest, the license and the files that the tests use."""
    if os.path.isdir(SUITE):
        shutil.rmtree(SUITE)
    os.makedirs(os.path.join(SUITE, "validation"))
    os.makedirs(os.path.join(SUITE, "schemas"))
    for name in ("LICENSE", "README.md"):
        shutil.copy(os.path.join(src, name), os.path.join(SUITE, name))
    shutil.copy(os.path.join(src, "validation", "manifest.jsonld"),
                os.path.join(SUITE, "validation", "manifest.jsonld"))
    for e in entries(src):
        a = e["action"]
        files = [os.path.join("validation", a["data"])] if "data" in a else []
        if "schema" in a:
            files.append(os.path.relpath(schema_json_path(src, e), src))
        for rel in files:
            p = os.path.join(src, rel)
            if os.path.isfile(p):
                shutil.copy(p, os.path.join(SUITE, rel))
    commit = subprocess.run(["git", "-C", src, "rev-parse", "HEAD"], capture_output=True,
                            text=True).stdout.strip()
    with open(os.path.join(SUITE, "VERSION"), "w") as f:
        f.write("https://github.com/shexSpec/shexTest commit %s\n" % commit)


def generate():
    os.makedirs(OUT, exist_ok=True)
    groups = {"structural": [], "inheritance": []}
    skipped = []
    for e in entries(SUITE):
        try:
            group, text = translate(SUITE, e)
            groups[group].append(text)
        except Unsupported as ex:
            skipped.append((e["name"], str(ex)))
        except FileNotFoundError as ex:
            skipped.append((e["name"], "a file is missing: %s" % os.path.basename(ex.filename)))
    for group, texts in groups.items():
        name = group.capitalize()
        with open(os.path.join(OUT, name + ".lean"), "w") as f:
            f.write("-- `tests/tools/gen_shextest.py` writes this file. Do not edit it.\n")
            f.write("import ShexTests.Harness\n\nnamespace ShexTests.%s\n\nopen ShexTests\n" % name)
            f.write("open ShexLean hiding Schema\nopen ShexLean.InheritanceCore hiding Schema\n\n")
            names = []
            for i, t in enumerate(texts):
                f.write(t.replace("@@NAME@@", "t%04d" % i, 1) + "\n")
                names.append("t%04d" % i)
            f.write("/-- The %s tests. -/\ndef tests : List TestCase := %s\n\nend ShexTests.%s\n"
                    % (group, lean_list(names), name))
    with open(os.path.join(SUITE, "SKIPPED.md"), "w") as f:
        f.write("# Skipped tests\n\n`tests/tools/gen_shextest.py` writes this file.\n"
                "The 2025 formalism, or the translation, cannot express these tests.\n\n")
        f.write("| Test | Reason |\n|---|---|\n")
        for n, r in skipped:
            f.write("| `%s` | %s |\n" % (n, r))
    print("structural: %d, inheritance: %d, skipped: %d" % (
        len(groups["structural"]), len(groups["inheritance"]), len(skipped)))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--vendor", metavar="SHEXTEST_DIR",
                    help="copy the files that the tests use from a checkout of shexTest")
    args = ap.parse_args()
    if args.vendor:
        vendor(args.vendor)
    generate()


if __name__ == "__main__":
    sys.exit(main())
