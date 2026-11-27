# Linear Assemblies: conditional Lean formalization

Completed formalization of the mathematical results in **How Many Tiles Does
It Take to Build a Line in Expectation and with Confidence?**, Divya Bajaj,
Bin Fu, and Robert Schweller, November 26, 2026 draft (26 pages).

The project covers Theorems 1–8, Lemmas 1–12, Corollaries 9–10, the exact
one-pad recurrence and optimization formulas, and the extension to every
fixed number of pads at least two. `STATUS.md` maps the paper statements to
Lean declarations. “Complete” means complete within the conditional scope
and the explicit mathematical and algorithmic models described below.

## What is verified

- Concrete one-pad and two-pad tile constructions, with multiplicities,
  seed cost, exact compatibility, haltability, and expected length.
- The exact one-pad optimum and both logarithmic bounds, including the
  strict numerical constant 0.670, checked with exact integer arithmetic.
- Matching expected-length asymptotics for two-pad and flexible glues.
- All four parameterized concentration bounds, including exact mean,
  physical concatenation, independent-sum stopping law, and lower bounds
  that do not require a prescribed mean.
- The four tight fixed-accuracy regimes and the inert-pad extension.
- Costed optimization algorithms with exact-answer proofs and respective
  O(log² N) and O(log N log log N) bit-cost bounds.

## Conditional boundary

Standard external results are hypotheses, not global axioms or hidden proof
placeholders. The active contracts are finite absorbing-chain theory (E01),
subexponential equivalence and Bernstein's inequality (E03a/b), fast integer
multiplication (E04), and polynomial-time fixed-point logarithm approximation
(E08). The latter replaces the paper's illustrative log-series implementation
with a generic standard approximation theorem. All paper-specific premises,
constructions, recurrence arguments, exponent localization, exact comparisons,
and cost sums are proved here.

The computational results use an explicit binary-arithmetic cost model.
They do not certify Lean's own evaluator, a compiled executable's wall-clock
performance, or a Turing-machine implementation of the external routines.
See `ALGORITHMS.md` for the exact scope, and `ASSUMPTIONS.md` for source-checked
contracts and their uses. The model measures successful attachments; physical
waiting time from incompatible draws is outside the paper's objective.

## Reproduce the audit

Install Lean's `elan` toolchain manager, extract this directory, and run:

```sh
lake exe cache get
bash scripts/check.sh
```

Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned by the supplied toolchain
and manifest. Keep the manifest when rebuilding. The archive omits downloaded
dependencies and compiled caches, so initial setup requires network access.

`Audit.lean` prints foundational dependencies and the full external contract
fields. `verification/check.log` records the successful build and audit;
`verification/summary.json` gives machine-readable counts and scope.
`verification/SHA256SUMS` hashes the delivered source and documentation files.
There are no `sorry`, `admit`, custom global axioms, or native/unsafe proof
shortcuts in the delivered project.

The supporting checkpoint documents preserve detailed proof maps for the
constructions and probability bounds. `COMPLETION.md` describes the final
statement review and the deliberate alternative proof routes.
