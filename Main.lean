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
  "Run 'shex_lean run' from the project root. It reads the proof source\n" ++
  "files with paths that are relative to the project root."

private def paperLabel (name : String) : String :=
  if name.startsWith "schemas2017-" then "2017 — Semantics and Validation of Shapes Schemas for RDF"
  else if name.startsWith "inheritance2025-" then "2025 — Shape Expressions with Inheritance"
  else "2026 — Shape Expressions with Inheritance, disjunctive extends explored (§6)"

/-- Print each item in `items` under a sub-header for its paper. The name
prefix of each item (`schemas2017-`, `inheritance2025-` or
`inheritance2026-`) selects the paper. Each item already has its display
line. If a paper has no items, do not print its sub-header. -/
private def listGrouped (items : List (String × String)) : IO Unit := do
  for paper in ["schemas2017-", "inheritance2025-", "inheritance2026-"] do
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

/-- Print the Lean source of a proof. The function reads the source from
the file `p.path`. Thus, the text that it prints is always the same as the
text that `lake build` checks. -/
private def runProof (p : Examples.ProofItem) : IO Unit := do
  IO.println s!"{p.name} — {p.summary}\n"
  match ← (IO.FS.readFile p.path).toBaseIO with
  | .ok content =>
      IO.println s!"Lean source ({p.path}):\n"
      IO.println content
  | .error e =>
      IO.eprintln s!"Could not read {p.path}: {e}"
      IO.eprintln "(Run shex_lean run from the project root.)"

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
