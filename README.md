## Formalization of mathematical results in Lean

In this repository, we formalize some mathematical results using Lean 4 and Mathlib.

- `Hirsch-Analysis`: Formalization of some results from the book book *Éléments d'Analyse Fonctionnelle by Francis* Hirsch and Gilles Lacombe.
- `Cayley-Graph`: Formalization of the representation of finite groups as graphs.

#### Usage
To use the formalizations, you need to install [Lean](https://github.com/leanprover/lean4). Clone the repository, go in any of subdirectory and run `lake exe cache get` to get the dependencies. Then, you can run `lake build` to build the project. The generation of the html files uses [Alectryon](https://github.com/cpitclaudel/alectryon) and [LeanInk](https://github.com/leanprover/LeanInk/blob/main/LeanInk/Annotation/Alectryon.lean).