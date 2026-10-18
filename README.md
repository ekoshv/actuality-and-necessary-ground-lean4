# Verified conditional argument in Lean 4

This project formalizes the logical arguments of **From Mathematical Possibility to Actuality: A Modal-Existential Argument for a Necessary Ground of Concrete Reality**, subtitled *A Philosophical Reconstruction*, dated **20 September 2026**.

The original PDF was recovered from the user's Desktop and copied unchanged into `source/`. Its SHA-256 is:

```text
5e13210df5408b365746785757aa8494b53e96e4887115f16470f7445f06a0ea
```

The main deliverables are `ActualityGround.lean`, `compilation_output.txt`, and `REPORT.md`. `Audit.lean` checks the transitive axiom dependencies of every project theorem. The original PDF and its page-labelled text extraction are included for review.

## Reproduce

The project pins **Lean 4.19.0** and mathlib commit **c44e0c8ee63ca166450922a373c7409c5d26b00b** (mathlib tag `v4.19.0`). All transitive dependency revisions are in `lake-manifest.json`. Do not update the lockfile to reproduce this run.

With Git and [elan from the official Lean installation instructions](https://lean-lang.org/install/manual/) available, open this directory in a terminal and run:

```sh
lake exe cache get Mathlib.Data.Set.Basic
bash check.sh 2>&1 | tee compilation_output.txt
```

The first command fetches the mathlib import and its dependencies. See the [mathlib dependency instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency) for background. The ZIP omits downloaded dependencies and compiler binaries.

On Windows without Bash, run these checks directly in PowerShell:

```powershell
lake exe cache get Mathlib.Data.Set.Basic
lake env lean --version
lake env lean -DwarningAsError=true ActualityGround.lean
lake build
lake env lean -DwarningAsError=true Audit.lean
```

The delivered run used the official Linux Lean binary in WSL on this Windows machine. The project source and Lake lockfile are portable.

## Read the result correctly

Theorems quantify over a modal model and take the philosophical premises as arguments. They establish valid conditional implications. They do not prove that the actual universe satisfies PSR, contingency, or the prohibition on wholly contingent complete grounds. The conclusion concerns a necessarily obtaining **member of a complete ground**, with the exact scope explained in `REPORT.md`.
