import ShexLean
import Registry

private def usage : String :=
  "shex_lean: a Lean formalization of Shapes Schemas for RDF\n\n" ++
  "Usage:\n" ++
  "  shex_lean            List the available worked examples.\n" ++
  "  shex_lean list        List the available worked examples.\n" ++
  "  shex_lean run <name>  Print the schema/graph/typing of one example."

private def listExamples : IO Unit := do
  IO.println usage
  IO.println ""
  IO.println "Examples:"
  for e in Examples.all do
    IO.println s!"  {e.name} — {e.summary}"

private def runExample (name : String) : IO Unit := do
  match Examples.find? name with
  | some e => IO.println e.render
  | none => do
    IO.eprintln s!"Unknown example: {name}"
    IO.eprintln ""
    IO.eprintln usage

def main (args : List String) : IO Unit :=
  match args with
  | [] => listExamples
  | ["list"] => listExamples
  | ["run", name] => runExample name
  | _ => IO.eprintln usage
