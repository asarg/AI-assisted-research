# Completion and statement review

The conditional result formalization is complete for the supplied November
26 draft. All numbered mathematical results have corresponding checked
statements or stronger results in the project. The paper's open problems
MIN2 and MINf remain open; its sentence referring back to Theorem 7 in
Section 5 is not a separate theorem.

## Final work completed after checkpoint 07

- Exact complement between failure probability and the rounded success window.
- Embedding a two-pad system into any kappa>=2 positions, preserving cost,
  stopping distribution, mean and concentration.
- Corollary 10's fixed-failure and polynomial-failure regimes, with explicit
  positive lower and upper constants and eventual quantifiers.
- A costed sequential optimization algorithm and full invariant/cost proof.
- Rational approximation error, the seven-candidate exponent window, exact
  comparison search, repeated squaring, and the fast algorithm's cost proof.
- Tile-level minimum interpretation and logarithmic runtime statements for
  both algorithms, including N=1 correctness and small-target branches.

## Statement matching

Theorems 1–5 are realized as concrete system existence and universal lower
bounds. Theorem 3 explicitly proves the attained minimum. Theorems 6–7
return that same minimum as the value problem specifies. Theorem 8's upper
bounds have universal constants over N, epsilon and delta in the paper's
range; their systems have mean exactly N. Its lower bounds hold for all
compatible systems under the success-window constraint without requiring
that mean. The general lower bound includes fixed kappa-pad systems.

Corollary 10 uses `OnePadBounds` and `GeneralBounds`: a lower bound for every
feasible system plus an actual feasible witness below the upper bound. This
bounds the attained natural-valued minimum without adding a separate opaque
K(N,epsilon,delta) constant or assuming minimizers exist. Finite entries and
interfaces are explicit; allowing an arbitrary ambient label type does not
allow infinitely many used labels.

All models require reachable haltability, as stated in Section 2.1 of the
paper. Successful attachments determine the length. Terminal seed length is
one, and the bookkeeping tick used by the generic absorption bound is proved
to correspond to this seed shift. Probability and expectation series have
normalization and convergence hypotheses; a bare real-valued infinite sum is
not taken to establish finite expectation.

## Deliberate alternative proofs

- The general expected-length lower bound is proved directly from the forest
  transform instead of importing the earlier SICOMP lower bound.
- Forest expansions and restart bounds are proved internally.
- Concentration uses generic subexponential exponential moments and Bernstein
  rather than the paper's factorial-moment presentation.
- The fast optimizer obtains logarithm approximations from the generic E08
  theorem rather than implementing the illustrative series. The precision,
  quotient error, candidate localization and subsequent computations are
  still project proofs.
- Flexible-model upper bounds use the proved two-pad embedding; a second,
  standalone flexible implementation is unnecessary for the stated results.

## Completion boundary

External standard theorems remain explicit hypotheses by design. Their general
proofs are outside the agreed conditional task. Runtime verification is in the
explicit arithmetic cost model described in `ALGORITHMS.md`, not a certified
compiler or machine-code implementation. These are scope boundaries, not
unreported proof placeholders.

`STATUS.md` is the result map, `ASSUMPTIONS.md` is the assumption register, and
`verification/check.log` is the final build and axiom audit. No further work
is pending within this stated conditional result scope.
