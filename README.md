# Lean Mini-Course

This repository contains the materials for the course **"Introduction to Mathematical Formalization in Lean"**, taught at [**Universidad Autónoma de Madrid**](https://matematicas.uam.es) (April 4 - 5, 2024).

## Tutorials and Exercises
For each of the course parts, I will present a tutorial and then give you some exercises to solve. I will also provide some tactic guides. All of the files can be tested online without installing Lean locally.

For each exercise session, click on the corresponding link below. You might have to wait for a minute or so until the server starts and the orange bars go away. Then, you can go ahead and replace each sorry by a valid proof.

Part 1: Basic Tactics.
The [Tutorial](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F1BasicTactics%2FLogicTutorial.lean), the [Exercises](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F1BasicTactics%2FLogicExercises.lean), and the [Tactic Guide](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F1BasicTactics%2FTactics.lean).


Part 2: More Tactics.
The [Tutorial](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F2MoreTactics%2FFunctionsTutorial.lean), the [Exercises](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F2MoreTactics%2FFunctionsExercises.lean), and the [Tactic Guide](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F2MoreTactics%2FFunctionsExercises.lean).

Part 3: Structures and classes.
We will discuss [Structures](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F2MoreTactics%2FFunctionsExercises.lean), [Classes](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F2MoreTactics%2FFunctionsExercises.lean), and examples from [Group Theory](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F2MoreTactics%2FFunctionsExercises.lean). See also the [Tactic Guide](https://raw.githubusercontent.com/mariainesdff/minicurso/master/Minicurso/3Structures/Tactics_3.lean).

Part 4: Using Mathlib.
I will introduce some techniques and resources for [using Mathlib](https://lean.math.hhu.de/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmariainesdff%2Fminicurso%2Fmaster%2FMinicurso%2F2MoreTactics%2FFunctionsExercises.lean) effectively.

## Installation Instructions
Lean 4 installation instructions can be found [here](https://leanprover-community.github.io/get_started.html).

If you have Lean 4 installed in your computer and you prefer to work with a local copy of this repository, first clone the repository using
```
git clone https://github.com/mariainesdff/minicurso
```

Then navigate to the `minicurso` directory and run `lake update` and `lake exe cache get` to get an updated version of the Mathlib cache.

Type `code .` to open the folder in `VS Code`.

## Other resources

1. [The Natural Number Game](https://adam.math.hhu.de/\#/g/hhu-adam/NNG4)
2. [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
3. [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
4. [Lean community webpage](https://leanprover-community.github.io/)
5. [Lean Zulip chat](https://leanprover.zulipchat.com/)

Copyright (C) 2024, María Inés de Frutos-Fernández
