import ShexLean
import Registry
import ProofRegistry

private def usage : String :=
  "shex_lean: a Lean formalization of Shapes Schemas for RDF\n\n" ++
  "Usage:\n" ++
  "  shex_lean            List the available worked examples and proofs.\n" ++
  "  shex_lean list        List the available worked examples and proofs.\n" ++
  "  shex_lean run <name>  Print an example's schema/graph/typing, or a\n" ++
  "                        proof's Lean source.\n\n" ++
  "shex_lean run must be run from the project root (it reads proof source\n" ++
  "files by their path relative to it)."

private def paperLabel (name : String) : String :=
  if name.startsWith "schemas2017-" then "2017 — Semantics and Validation of Shapes Schemas for RDF"
  else "2025 — Shape Expressions with Inheritance"

/-- Print `items` (already paired with their display line) grouped under a
`2017`/`2025` sub-header per name prefix, skipping any paper with nothing
to show. -/
private def listGrouped (items : List (String × String)) : IO Unit := do
  for paper in ["schemas2017-", "inheritance2025-"] do
    let inPaper := items.filter (fun (name, _) => name.startsWith paper)
    if !inPaper.isEmpty then
      IO.println s!"  {paperLabel paper}:"
      for (name, line) in inPaper do
        IO.println s!"    {name} — {line}"

private def listAll : IO Unit := do
  IO.println usage
  IO.println ""
  IO.println "Examples:"
  listGrouped (Examples.all.map (fun e => (e.name, e.summary)))
  IO.println ""
  IO.println "Proofs:"
  listGrouped (Examples.proofs.map (fun p => (p.name, p.summary)))

/-- Print a proof's Lean source, read from `p.path` so it can never drift
from what `lake build` actually checks. -/
private def runProof (p : Examples.ProofItem) : IO Unit := do
  IO.println s!"{p.name} — {p.summary}\n"
  match ← (IO.FS.readFile p.path).toBaseIO with
  | .ok content =>
      IO.println s!"Lean source ({p.path}):\n"
      IO.println content
  | .error e =>
      IO.eprintln s!"Could not read {p.path}: {e}"
      IO.eprintln "(shex_lean run must be invoked from the project root.)"

private def runItem (name : String) : IO Unit := do
  match Examples.find? name with
  | some e => IO.println e.render
  | none =>
    match Examples.findProof? name with
    | some p => runProof p
    | none => do
      IO.eprintln s!"Unknown example or proof: {name}"
      IO.eprintln ""
      IO.eprintln usage

def main (args : List String) : IO Unit :=
  match args with
  | [] => listAll
  | ["list"] => listAll
  | ["run", name] => runItem name
  | _ => IO.eprintln usage
