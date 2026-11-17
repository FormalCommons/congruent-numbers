# Instructions for agents

This repository formalizes, in Lean 4, the plan at
<https://github.com/FormalCommons/congruent-numbers-plan>: the elementary
theory of the congruent number problem. It builds on
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) and Mathlib, at the
versions pinned in `lake-manifest.json`. Read the plan's pages for the
statements, the sources and the routes to a proof.

## Building

```sh
lake exe cache get      # Mathlib's compiled files; takes a minute
lake build --wfail      # also compiles the Tau Ceti files we import
```

`--wfail` makes every warning an error, as CI does, so a `sorry` fails the
build. The first build compiles the Tau Ceti files that the library imports,
which takes a minute or two. Before you push, `lake build --wfail` must
succeed.

## Layout

- The library is under `CongruentNumbers/`, in the namespace `CongruentNumbers`.
  Use one file per topic, such as `CongruentNumbers/Basic.lean` for the
  definition and `CongruentNumbers/Torsion.lean` for the torsion of $E_n$.
- `CongruentNumbers.lean` imports every file of the library. Add an import there
  for each new file.

## Rules

- **Use what exists.** Before you define or prove anything, search Tau Ceti
  (`.lake/packages/TauCeti/TauCeti/`) and Mathlib
  (`.lake/packages/mathlib/Mathlib/`) for it, and use what you find. The plan's
  "Lean status" lines name results that already exist. Do not reprove them.
- **State what the plan states.** A theorem that formalizes a milestone has
  the plan's hypotheses and conclusion, in the plan's generality. Weaker or
  different statements are not the milestone. Its docstring names the
  milestone, for example "This is the milestone *Torsion of E_n*".
- **No gaps.** No `sorry`, `admit`, new `axiom`, or `native_decide`.
- **Mathlib style.** Follow Mathlib's naming conventions and style. Every
  definition and every main theorem has a docstring, and every file starts
  with a module docstring that says what it contains.
- **Leave the setup alone.** Do not change `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain` or anything under `.github/`.
- **Keep pull requests focused.** One pull request does one issue. If an issue
  is too big for a pull request of a few hundred lines, split it into smaller
  issues instead.
