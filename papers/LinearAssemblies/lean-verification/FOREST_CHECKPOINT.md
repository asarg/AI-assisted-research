# Checkpoint 03: forest representation and coefficient bounds

This checkpoint verifies Lemma 9 and Corollary 9, including the connection to
finite tile multisets. No new external hypothesis is needed for these results.
It does not yet prove the stopping-transform identity or Lemma 10.

## Exact mathematical objects

`Counts S` records natural-number degrees d_i, transient transition counts
 a_ij, and terminal counts b_i, with d_i = sum_j a_ij + b_i.
`System.absorptionCounts` constructs these from the reachable unfinished
interfaces of the existing tile model. Each compatible entry is counted once;
duplicated tile entries retain their multiplicity. All terminal outcomes are
combined into b_i.

`Counts.systemMatrix` is exactly the polynomial matrix `(1+X)D-A` over Z[X].
`Counts.B_eq_determinant` and `Counts.H_eq_cramer` identify B and H with the
paper's determinant and its column replacement. An unfinished initial state
is required when naming H; the seed-only case has no such state and will be
handled separately when connecting the stopping transform.

## Checked proof map

| Step | Main Lean declarations |
|---|---|
| A deterministic edge selection terminates or has a nonterminating component | `Forest.Terminates`, `Rooted`, `distance_drop` |
| Rooted selections have determinant 1 | `det_incidence_rooted`, using distance blocks in a triangular matrix |
| Other selections have determinant 0 | `det_incidence_not_rooted`, using the indicator of nonterminating states as a kernel vector |
| Denominator is a weighted forest sum | `det_laplacian_expansion`, `det_laplacian` |
| Redirect termination edges to s | `rooted_redirect_iff`, `redirected_eq_update`, `det_redirected_sub` |
| Numerator counts forests in which s reaches termination | `det_updateCol_termination` |
| Positive terminating paths yield a positive forest | `Counts.positive_forest`, using shortest-path ranks |
| Nonnegative coefficients and degree <= n | `Counts.B_nonneg`, `H_nonneg`, `B_degree` |
| B(0)=H(0)>=1 | `Counts.B_zero_eq_H_zero`, `B_zero_pos` |
| B(1) bounded by all edge selections | `Counts.B_one_le_product`, `B_one_le_product_twice` |
| Graph paths and entry counts survive terminal-state collapse | `UniformGraph.transientCounts`, `transient_haltable`, `transient_sum_degree_le` |
| Lemma 9 for tile systems | `System.tile_polynomial_representation` |
| Corollary 9 for tile systems | `System.general_coefficient_bounds`, `onePad_coefficient_bounds` |

Self loops are omitted from edge weights because their incidence rows are
zero. This is what gives the sharper factor `(2*d_i-a_ii)` before the simpler
`2*d_i` bound. Haltability is used to obtain a positive constant coefficient;
the degree and coefficient-sum upper bounds do not need haltability.

## Trust boundary

The new proofs use the standard Lean/Mathlib foundations only. They do not
assume a forest theorem, a nonnegative-coefficient theorem, Lemma 9 itself,
or the one-pad/richer-model coefficient bounds. The original E01 absorbing-chain
contract remains an explicit hypothesis of the earlier expected-length results,
but is not a hypothesis of the new forest or coefficient results.

`Audit.lean` checks foundational dependencies and prints the principal theorem
types, so the explicit hypotheses can also be reviewed. `scripts/check.sh`
runs the source-policy checks, build, and audit.

## Next dependency

Define the stopping transform from the already verified stopping masses, prove
its weighted first-step equations and convergence, and identify it with H/B.
Then prove the derivative and tilted-expectation bounds used in Lemma 10,
followed by the degree/coefficient-sum lower bounds and asymptotic conclusions.
All probability and analytic hypotheses must remain explicit and be checked
at application sites.
