# Verification status — completed conditional formalization

All paper results in the table are proved in the conditional model. E01,
E03a/b, E04 and E08 are explicit standard external hypotheses, as applicable.
The algorithmic statements use the explicit cost model in `ALGORITHMS.md`.
`COMPLETION.md` records statement matching and alternative proof routes.

## Paper-to-project map

| Paper component | Module / work | Current scope |
|---|---|---|
| Section 2, all models | `Models`, `TileGraph`, `Semantics`, probability modules | Finite entries and multiplicity, compatibility embeddings, interface bounds, successful-growth transition graph, stopping distribution, seed shift, reachable haltability verified. Finite mean and normalization conditional on E01. Physical failed-draw waiting time is outside the length model, as in the paper. |
| Definition 1 | `OnePad/Recurrence` | Original full recurrence verified; reduced recurrence is derived, not substituted as an assumption. |
| Lemma 1 | `CertifiedBlock`, `ResetCompiler`, `TileCompiler` | General reset update and deterministic first attachment verified via complete first-step certificates; expectation interpretation conditional on E01. |
| Theorem 1 | `PositiveDigits`, `OnePad/LogarithmicBounds` | Complete conditional concrete-system existence with exact expected length and displayed `3 log_3 N + 1` size bound, including N=1. |
| Lemma 2 | `PotentialBound`, `Characterization.mean_le_F` | Universal one-pad mean bound verified conditionally, including unreachable-state restriction and entry accounting. |
| Lemma 3; Theorem 2 | `OnePad/ExponentialBound` | Complete: exponential bound derived from the exact recurrence, plus the strict `3 log_3 N - 0.670` tile bound. The decimal constant is certified by exact integer arithmetic. |
| Theorem 3 | `Characterization.exact_characterization`, `minimum_tile_cost` | Complete conditional existence and optimality result for actual one-pad tile multisets over finite alphabets. Includes N=1 and the cost-12 example at N=100. |
| Lemma 4; Equation (18) | `OnePad/Recurrence` | Verified. |
| Equation (19) | `OnePad/ClosedForm` | Verified, including executable evaluator correctness. |
| Theorem 4 | `Probability/MeanCoefficientBound`, `ExpectedLowerBound` | Complete conditional lower bound for arbitrary compatibility, with explicit threshold N>=16 and constant 1/4. Derived directly from the verified transform; E05 is not used. |
| Theorem 5 | `DigitData`, `Presentation`, `TwoPad/Construction`, `Certificate`, `Realization` | Concrete shared-reset two-pad entries, exact compatibility rows, finite mean, haltability, exact tile count, and parameterized logarithmic cost are proved. Flexible upper construction follows at equal cost by the existing embedding. `Analysis/BaseChoice` and `TwoPad/UpperBound` now prove the chosen-base estimate and the displayed logarithmic upper bound with explicit constant 72 and threshold N>=16. |
| Theorem 6 | `Algorithms/Sequential`, `Complexity.theorem_six` | Complete: executable three-register costed scan, exact minimum, bounded fuel, intermediate bit lengths, O(log² N) cost in the explicit binary-arithmetic model. Tile interpretation conditional on E01. |
| Theorem 7 | `Algorithms/{Candidates,Approximation,Power,FastSearch,BitGrowth,Complexity}` | Complete from E01/E04/E08: fixed-point quotient error, seven-candidate exponent interval, exact selection, repeated squaring, geometric cost sum, approximation overhead, exact minimum, and O(log N log log N) cost in the explicit model. |
| Lemma 5 | `OnePad/BlockBound` | Positive ternary blocks have the sharp cost and uniform remaining-potential bound. Potential equals remaining mean conditionally on E01. |
| Lemma 6 | `TwoPad/Certificate`, `Realization` | Exact-mean block and global remaining-mean bound M+(b-2), hence <=2M when b-2<=M. The chosen base is proved to satisfy this premise and to give cost <=72*Phi(M) for every M>=1; `TwoPad.balanced_block_exists` packages the result. |
| Lemma 7 | `Probability/Tail` | Complete conditional generic finite-chain bound: Pr(T>4Mj)<=2^(-j) from uniform remaining mean <=2M. Markov and restart estimates are proved from series and transition equations. |
| Lemma 8 | `Probability/BlockConcentration`, `BernsteinBlocks`; `Concatenation/*` | Verified from E03a/E03b: actual block distributions, centered exponential tail, subexponential hypothesis application, scale summation, and universal concentration constant. Physical concatenation has the exact independent-sum convolution law. |
| Lemma 9 | `Forest/Functional`, `Roots`, `Expansion`, `Counts`, `PolynomialBounds`, `Representation`; `Probability/Transient`; `CoefficientBounds` | Verified without external hypotheses: both forest expansions, nonnegative integer coefficients, B(0)=H(0)>=1, degree bound, and sharp product bound. The exact determinant and Cramer matrices are identified. Specialized to reachable transient tile states. |
| Corollary 9 | `CoefficientBounds.general_coefficient_bounds`, `onePad_coefficient_bounds` | Verified for tile systems: degree <= m, B(1)<=2^m for one-pad and B(1)<=(2m)^m for arbitrary compatibility. No external hypotheses. |
| Section 6.2.1, transform identity | `Probability/Transform`, `TransformDerivative`, `RationalTransform` | Verified conditionally on E01: convergent stopping series, weighted first-step equations, positive real determinant evaluation, exact Cramer ratio, and termwise derivative. |
| Lemma 10 | `Forest/WeightedDegree`, `Probability/TransformBound`, `TiltedWindow`, `Confidence`; `Confidence`, `LowerBounds` | Verified conditionally on E01, including tilted window mass, alarm survival, Jensen calculation, explicit constants, degree and coefficient bounds, and small targets. |
| Lemma 11 | `Probability/Absorption`, `UniformChain`, `TileGraph` | Finite-chain atom bound verified and transferred to terminal tile length; exact time shift is explicit. No absorption assumption needed. |
| Lemma 12 | `Probability/Accuracy`, `Accuracy` | Tile-level bound verified with constant 1/24 for N>=4, plus the trivial small-N bound. Rounding identifies the attachment window with the relative-error event. No mean or external-theorem assumption needed. |
| Theorem 8, Eq. (25), (27) | `LowerBounds` | Complete conditional tile-level lower bounds for every N>=2, 0<eps,delta<=1/2, without a mean constraint. Explicit constants 1/36 (one-pad) and 1/72 (general compatibility). |
| Theorem 8, Eq. (24), (26) | `Concentration/*`, `UpperBounds` | Verified from E01/E03a/E03b for all N>=2, 0<eps,delta<=1/2: actual finite one-pad/two-pad/flexible systems, haltability, exact mean N, failure<=delta, and uniform R budgets. |
| Fixed kappa>=2 extension | `PadEmbedding.kPad_concentrated_upper`, general lower bounds | Complete: compatibility, cost, law, mean and concentration preserved by two active pads and inert extra positions. |
| Corollary 10 | `Regimes.fixed_confidence_regimes`, `polynomial_confidence_regimes` | Complete: all four tight regimes, positive constants and eventual quantifiers, with universal lower bounds and concrete upper witnesses. Conditional on E01/E03a/E03b. |

## Meaning of the probability model

`UniformGraph.stoppingMass k x` is the probability of exactly k successful
attachments before reaching a terminal interface, starting from x. In
particular, a terminal initial interface has mass one at k=0. Total length is
L=k+1. `System.expectedLength` sums `(k+1) * stoppingMass k`.

The chain used for the atom bound includes terminal interfaces as states that
absorb on a bookkeeping tick. Its absorption time is L, not the attachment
count T. `chain_mass_eq` and `attachmentWindow_eq_chain` explicitly prove the
index correspondence. The extra tick does not represent an extra tile.

The assumption E01 is applied only after restricting a general system to
reachable states or proving a compiler-generated potential forces haltability.
For Lemma 9, terminal outcomes are combined by exact list counts, and paths
through transient states are transferred from graph reachability. This step
and all forest proofs are independent of E01.

Convergence of the expectation series is established conditionally before its
interpretation as a mean is used. A bare real `tsum` is not treated as a proof
of finite expectation.

## Checks and scope

- Lean 4.19.0; Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- 86 proof modules, 495 named theorem declarations (including helpers).
- 153 main declarations checked with `#print axioms`; explicit external
  hypotheses are also displayed with `#check`.
- Successful build and audit on November 26, 2026 (America/Chicago), recorded
  in `verification/check.log`.
- No `sorry`, `admit`, custom global axioms, or unsafe/native evaluation
  shortcuts in project proof sources. Only the usual Lean/Mathlib foundations
  appear in the audited dependency lists.

Counts measure source coverage, not a percentage of the paper verified.
No paper-result proof is pending within the conditional scope. External
theorem proofs and low-level machine compilation are outside that scope.
