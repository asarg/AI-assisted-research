# Quantitative bounds and shared-reset construction

| Result | Modules | Verified scope |
|---|---|---|
| Positive-base digits | PositiveDigits, DigitData | Every positive target, positive digits, prefix recurrence, digit-count bound |
| One-pad upper bound | OnePad/LogarithmicBounds | Exact mean, concrete finite system, C1(N)<=3 log_3 N+1 |
| One-pad lower bound | OnePad/ExponentialBound | Lemma 3 and strict C1(N)>3 log_3 N-0.670; exact arithmetic certifies the decimal |
| One-pad block | OnePad/BlockBound | Uniform remaining mean <=M and sharp ternary cost |
| Shared-entry compiler | Presentation | Actual finite entries, exposed-state decoder, compatibility sums, potential and mean transfer |
| Two-pad construction | TwoPad/Construction | Five entry families, OR compatibility rows, no double counting, exact charged cost |
| Two-pad mean | TwoPad/Certificate | Complete first-step equations and nonnegative potential, including the delay chain |
| Two-pad existence | TwoPad/Realization | All positive targets, all bases >=2, parameterized size, unique terminal, uniform remaining bound |
| Flexible construction | Models, TwoPad/Realization | Pair-encoding embedding preserves the same system and cost |
| General expected lower bound | Probability/MeanCoefficientBound, ExpectedLowerBound | Dominated convergence at zero, mean<=B(1), then explicit logarithmic lower bound |

The two-pad cost is first+2*count+2*(b-2)+1, where count is the number of digits
after the leading digit. Its uniform remaining potential is at most M+(b-2).
Unused delay entries are charged too. The chosen-base estimates are proved in checkpoint 06. The physical
concatenation proof is completed in checkpoint 07, including exact cost and law.

The mean lower bound uses only the existing E01 finite-chain contract, Mathlib
analysis, and the proved forest representation. It does not require a new
external assumption about two-pad or flexible tile complexity.

## Checkpoint 06 additions

`Analysis/BaseChoice` verifies b=max(2,ceil(sqrt(log(M+1)))) with b<=M+1
and uniform cost <=72*Phi(M). `TwoPad/UpperBound` packages Lemma 6 and
Theorem 5 with explicit constants, including all block targets M>=1.

`Probability/Tail` proves survival probabilities, Markov's inequality for the
convergent stopping series, restart contraction, and the geometric uniform
block tail. No E02 restart contract is needed for this result.
