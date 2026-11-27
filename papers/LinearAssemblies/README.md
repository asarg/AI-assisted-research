# Lean verification

**Status:** Complete conditional formalization of the results in *How Many Tiles Does It Take to Build a Line in Expectation and with Confidence?* by Divya Bajaj, Bin Fu, and Robert Schweller, for the November 26, 2026 draft.

The Lean project is in [lean-verification/](lean-verification/), which contains the sources, pinned dependencies, and instructions needed to reproduce the verification. Coverage includes Theorems 1–8, Lemmas 1–12, Corollaries 9–10, and the extension to any fixed number of pads at least two. The proofs assume explicitly stated standard external theorems; algorithmic bounds use the documented binary-arithmetic cost model.

## What is verified?

The formalization includes concrete tile constructions, exact expected lengths, tile multiplicities and seed cost, the exact one-pad minimum, concentration upper and lower bounds, and both one-pad optimization algorithms.

The principal declarations are listed below. All declaration names are relative to the `LinearAssemblies` namespace.

| Paper result | Principal Lean declarations | Source |
| --- | --- | --- |
| Theorem 1: one-pad upper bound | `OnePad.logarithmic_upper_bound` | [LogarithmicBounds.lean](lean-verification/LinearAssemblies/OnePad/LogarithmicBounds.lean) |
| Theorem 2: one-pad lower bound, including the constant 0.670 | `OnePad.logarithmic_lower_bound` | [ExponentialBound.lean](lean-verification/LinearAssemblies/OnePad/ExponentialBound.lean) |
| Theorem 3: exact one-pad characterization and minimum | `OnePad.exact_characterization`; `OnePad.minimum_tile_cost` | [Characterization.lean](lean-verification/LinearAssemblies/OnePad/Characterization.lean) |
| Theorem 4: general expected-length lower bound | `System.expected_length_lower_bound` | [ExpectedLowerBound.lean](lean-verification/LinearAssemblies/ExpectedLowerBound.lean) |
| Theorem 5: tight two-pad and flexible-glue bounds | `TwoPad.logarithmic_upper_bound`, together with Theorem 4 and the compatibility embedding | [UpperBound.lean](lean-verification/LinearAssemblies/TwoPad/UpperBound.lean), [Models.lean](lean-verification/LinearAssemblies/Models.lean) |
| Theorem 6: exact optimization in O(log² N) bit cost | `OnePad.Algorithms.theorem_six` | [Complexity.lean](lean-verification/LinearAssemblies/Algorithms/Complexity.lean) |
| Theorem 7: exact optimization in O(log N log log N) bit cost | `OnePad.Algorithms.theorem_seven` | [Complexity.lean](lean-verification/LinearAssemblies/Algorithms/Complexity.lean) |
| Theorem 8: parameterized concentration bounds | `onePad_concentrated_upper`; `twoPad_concentrated_upper`; `System.onePad_concentration_lower_bound`; `System.general_concentration_lower_bound` | [UpperBounds.lean](lean-verification/LinearAssemblies/UpperBounds.lean), [LowerBounds.lean](lean-verification/LinearAssemblies/LowerBounds.lean) |
| Corollary 9: polynomial coefficient bounds | `System.onePad_coefficient_bounds`; `System.general_coefficient_bounds` | [CoefficientBounds.lean](lean-verification/LinearAssemblies/CoefficientBounds.lean) |
| Corollary 10: tight fixed-accuracy regimes | `fixed_confidence_regimes`; `polynomial_confidence_regimes` | [Regimes.lean](lean-verification/LinearAssemblies/Regimes.lean) |
| Extension to every fixed number of pads at least two | `kPad_concentrated_upper`, together with the general lower bound | [PadEmbedding.lean](lean-verification/LinearAssemblies/PadEmbedding.lean) |

See [STATUS.md](lean-verification/STATUS.md) for the full mapping, including Lemmas 1–12, and [COMPLETION.md](lean-verification/COMPLETION.md) for the statement review and alternative proof routes.

### External assumptions and scope

The external results are explicit hypotheses in theorem statements. They are not introduced as custom global axioms, and no paper-specific theorem is assumed as an external fact.

| Contract | Assumed external result |
| --- | --- |
| E01 — `Probability.FiniteAbsorptionLaw` | Normalization, finite expectation, first-step equations, and uniqueness for finite absorbing chains. |
| E03a — `Probability.SubexponentialEquivalence` | The generic implication from a subexponential tail bound to an exponential-moment bound. |
| E03b — `Probability.BernsteinLaw` | Bernstein's inequality for independent discrete summands. |
| E04 — `Algorithms.Multiplication.Fast` | Exact integer multiplication with the stated O(b log(b+1)) bit-cost bound. |
| E08 — `Algorithms.Logarithm.Polynomial` | Fixed-point logarithm approximation with certified accuracy and polynomial cost in the requested precision. |

The exact contracts, references, and applicability conditions are recorded in [ASSUMPTIONS.md](lean-verification/ASSUMPTIONS.md). E08 provides a standard alternative to the paper's illustrative logarithm-series calculation; the required precision, quotient error, candidate-exponent interval, and exact comparisons are proved in the project.

There are no unfinished proof placeholders within this conditional scope. Proving the external contracts themselves is outside that scope. The runtime proofs concern costed algorithms in the model described in [ALGORITHMS.md](lean-verification/ALGORITHMS.md); they do not certify the execution speed of Lean's evaluator or a compiled machine-code implementation. As in the paper, assembly length counts successful attachments and excludes waiting time caused by incompatible draws.

## How to check

This README belongs at the repository root (`LinearAssemblies/`). The Lean project root is the `lean-verification/` subdirectory; it contains `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and the `LinearAssemblies/` source directory.

Prerequisites are Git, Python 3, Bash, and `elan`, the Lean toolchain manager, with its `lean` and `lake` commands available on your path. Initial dependency and toolchain setup requires network access. On Windows, run the commands in a compatible Bash environment, such as WSL.

From the repository root (`LinearAssemblies/`), run:

```sh
cd lean-verification
lake exe cache get
bash scripts/check.sh
```

After entering `lean-verification/`, `lake exe cache get` obtains the cached Mathlib build. The checking script then scans project sources for disallowed proof shortcuts, builds the Lean library, and runs the declaration and assumption audit. The script runs the following commands from the Lean project root:

```sh
python3 scripts/check_source.py
lake build
lake env lean Audit.lean
```

Keep `lean-toolchain` and `lake-manifest.json` unchanged to use the verified dependency versions. The project pins **Lean 4.19.0** and Mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**.

`Audit.lean` prints both foundational axiom dependencies and explicit external contracts. The latter are theorem hypotheses, so inspecting `#print axioms` alone is insufficient to identify the conditional assumptions.

## Directory guide

| Path | Purpose |
| --- | --- |
| [lean-verification/README.md](lean-verification/README.md) | Verification project overview and reproduction instructions. |
| [lean-verification/LinearAssemblies.lean](lean-verification/LinearAssemblies.lean) | Imports the complete verification library. |
| [lean-verification/LinearAssemblies/](lean-verification/LinearAssemblies/) | Models, constructions, probability arguments, bounds, and algorithms. |
| [lean-verification/Audit.lean](lean-verification/Audit.lean) | Principal declaration and assumption audit. |
| [lean-verification/scripts/check.sh](lean-verification/scripts/check.sh) | Reproducible source checks, build, and audit. |
| [lean-verification/STATUS.md](lean-verification/STATUS.md) | Detailed paper-to-proof mapping. |
| [lean-verification/ASSUMPTIONS.md](lean-verification/ASSUMPTIONS.md) | External theorem contracts and sources. |
| [lean-verification/ALGORITHMS.md](lean-verification/ALGORITHMS.md) | Optimization algorithms and the arithmetic cost model. |
| [lean-verification/verification/check.log](lean-verification/verification/check.log) | Recorded build and audit output. |
| [lean-verification/verification/summary.json](lean-verification/verification/summary.json) | Recorded release metadata and verification counts. |

## Last check

The recorded check is for release **`1.0.0-complete-conditional`**, completed on **November 26, 2026 at 22:02 CST** (`2026-11-27T04:02:44Z`).

- All local project build outputs were removed before rebuilding; the pinned dependency cache was retained.
- **86 proof modules** and **495 named theorem declarations**, including helper theorems.
- **153 principal declarations** inspected with `#print axioms`, with external hypotheses displayed separately.
- Build and audit succeeded with **zero warnings**.
- Source checks found no `sorry`, `admit`, custom global axioms, or native/unsafe proof shortcuts.
- The audited foundational dependencies were `Classical.choice`, `Quot.sound`, and `propext`.

The recorded counts describe the verified release, not a percentage measure of proof coverage. The evidence is in [verification/check.log](lean-verification/verification/check.log) and [verification/summary.json](lean-verification/verification/summary.json).
