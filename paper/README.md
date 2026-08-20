# Paper

LNCS-format paper about this repository's Lean formalization.

## Setup

This uses Springer's LNCS document class, which isn't included here (it's
Springer-licensed, not ours to redistribute). Before building:

1. Download the "Authors' instructions" package from Springer's own LNCS
   page (search "Springer LNCS Latex templates author instructions") or get
   `llncs.cls` + `splncs04.bst` from an Overleaf LNCS template.
2. Drop `llncs.cls` and `splncs04.bst` into this directory (they're
   gitignored — see the root `.gitignore`).

## Building

```sh
make            # builds main.pdf via latexmk
make watch      # rebuilds on file changes (latexmk -pvc)
make clean      # removes build artifacts
```

Requires `latexmk` and a LaTeX distribution (TeX Live/MacTeX) with
`biblatex`/`bibtex` support.

## Structure

- `main.tex` — top-level document, `\input`s the sections below.
- `introduction.tex`, `related_work.tex`, `rdf_lean.tex`, `shex_lean.tex`,
  `semantics_lean.tex`, `lemmas_lean.tex`, `algorithms_lean.tex`,
  `inheritance.tex`, `conclusions.tex` — paper sections.
- `references.bib` — bibliography, including the two papers this repo
  formalizes (`shex2017`, `shex2025`).
- `figures/` — figures referenced from the sections.
