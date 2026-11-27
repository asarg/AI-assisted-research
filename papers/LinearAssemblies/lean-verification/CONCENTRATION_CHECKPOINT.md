# Concrete concentration upper bounds

Checkpoint 07 completes the main inequalities (24) and (26) of Theorem 8.
All constants are uniform in N, epsilon, and delta; they depend only on the
universal constants in the explicit external probability theorems.

| Component | Main declaration | Verified content |
|---|---|---|
| Generic sequential law | `UniformGraph.sequential_mass` | Convolution from terminal and transition rows |
| Fresh labels | `onePadSeparation`, `twoPadSeparation` | Exact internal matches and no cross-block attachments |
| Concrete join | `Concatenation.certificate`, `system_mass`, `cost` | Potential, exact mean, full stopping law; no connector entry |
| Arbitrary sequences | `OnePadBlock.join_mass`, `TwoPadBlock.join_mass` | Iterated convolution; seed counted once |
| Centering | `BlockLaw.real_tail`, `centered_tail` | Continuous-threshold exponential tail, scale 32M |
| Lemma 8 | `block_concentration` | Standard E03 applicability and scale algebra |
| Balanced means | `balanced_sum`, `balanced_squares` | Sum N-1, maximum <=2N/r, squared sum <=2N^2/r |
| Parameter choice | `scaled_confidence`, `budget_eq_quota` | Failure <=delta with integer block count |
| Budgets | `probabilistic_log_budget`, `probabilistic_phi_budget` | Both R bounds, including the seed |
| Deterministic case | `deterministic_one`, `deterministic_two` | Point mass at exactly N total tiles |
| Final semantics | `onePad_concentrated_upper`, `twoPad_concentrated_upper` | Actual systems, exact mean and failure event, uniform cost |

The formal quota is ceil(log(2/delta)/epsilon^2), algebraically the paper's
ceil(epsilon^(-2) log(2/delta)); R is min(N,quota). The proof takes r=A*R
for a fixed integer A large enough. If r>N-1 it uses a deterministic path.
Otherwise R equals the quota and r positive balanced blocks suffice. This
minor rounding variation has the same uniform bounds and is proved directly.

E03a is a standard arbitrary-observable tail-to-exponential-moment equivalence;
E03b is a standard Bernstein inequality for independent discrete summands.
Their complete premises are visible in the theorem types and ASSUMPTIONS.md.
No tile-specific upper bound or independence assertion is assumed.
