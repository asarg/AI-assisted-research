# Stopping transform and concentration lower bounds

All entries below are compiled. The lower-bound modules use only
E01, the standard finite absorbing-chain law. The new upper bounds also use E03a/E03b. Paper-specific steps are proved.

| Step | Module | Result |
|---|---|---|
| Stopping generating function | Probability/Transform | Summability, terminal value, weighted first-step and transient count equations |
| Differentiation | Probability/TransformDerivative | Uniform domination by the finite first moment; derivative of the actual stopping transform |
| Real polynomial evaluation | Forest/RealPolynomial | Nonnegative evaluations and positive denominators |
| Cramer identity | Probability/RationalTransform | Actual stopping transform equals H/B on x>=0 |
| Weighted polynomial degree | Forest/WeightedDegree | Degree upper bound and Jensen lower bound for log B(1) |
| Logarithmic derivative | Probability/TransformBound | Nonnegative H derivative yields the tilted-mean lower bound |
| Successful window | Probability/TiltedWindow | At least a third of tilted mass in the window; alarm survival at least delta |
| Polynomial confidence | Probability/Confidence | S/36 <= degree B and G/36 <= log B(1) |
| Tile transfer | Confidence | Reachable restriction, exact rounded length event, and coefficient charging |
| Final lower bounds | LowerBounds | Small targets, inversion of m log(2m), and accuracy/confidence combination |

The termwise derivative and Jensen application use proved Mathlib analysis,
not additional external hypotheses. The lower-bound proof uses E01 normalization
and finite first moment; it does not assume a prescribed mean N.

For N>=4 the intermediate tile bounds are S/36<=m, G/36<=m log 2 for one-pad,
and G/36<=m log(2m) for all compatibility rules. The final lower bounds include
all N>=2 and have constants 1/36 (one-pad) and 1/72 (general compatibility).
