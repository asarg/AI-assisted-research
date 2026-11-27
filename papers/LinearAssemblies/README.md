# How Many Tiles Does It Take to Build a Line in Expectation and with Confidence?

This project studies the tile complexity of one-dimensional probabilistic self-assembly: how many tile entries are needed to produce a line with expected length exactly $N$, and how that cost changes when the final length must also be close to $N$ with high probability. Tile complexity counts the seed and all tile multiplicities.

The paper gives an exact characterization of the minimum for one-pad systems and proves optimal expected-length bounds of $3\log_3 N + O(1)$ for one-pad systems and $\Theta(\log N / \log\log N)$ for two-pad systems and flexible glues. It also establishes accuracy and confidence bounds. For fixed relative accuracy and failure probability at most $N^{-c}$, where $c>0$ is fixed, the optimal costs are $\Theta(\log^2 N)$ for one-pad systems and $\Theta(\log^2 N / \log\log N)$ for two-pad systems and flexible glues. Two algorithms compute the exact one-pad minimum in $O(\log^2 N)$ and $O(\log N\log\log N)$ bit operations, respectively.

## Contributions

- **Human contributions:** The research and manuscript are credited collectively to Divya Bajaj, Bin Fu, and Robert Schweller.
- **AI contributions:** OpenAI's ChatGPT/Codex assisted with proof development and manuscript editing, generated and revised the Lean formalization and supporting formal arguments, ran compilation and assumption audits, and prepared the verification documentation. The formalization was developed through an interactive workflow with human direction and feedback.

## Files

- [LinearAssemblies_paper.pdf](LinearAssemblies_paper.pdf) — The research paper, including the model, constructions, proofs, and main theorems.
- [lean-verification/](lean-verification/) — The Lean project, supporting documentation, and recorded verification results. See the [Lean README](lean-verification/README.md) for setup and checking instructions.

## Current status

The paper and Lean verification project are available. The conditional formalization covers Theorems 1–8, Lemmas 1–12, Corollaries 9–10, and the extension to every fixed number of pads at least two in the November 26, 2026 draft. The [verification status](lean-verification/STATUS.md) maps the paper's statements to the Lean proofs.

The recorded Lean 4.19.0 build and audit completed successfully on November 26, 2026, with 86 proof modules, 495 named theorem declarations, and no proof placeholders or custom global axioms. See the [build log](lean-verification/verification/check.log) and [verification summary](lean-verification/verification/summary.json).

The verification is **conditional**: standard external probability and arithmetic theorems remain explicit hypotheses, documented in the [assumption register](lean-verification/ASSUMPTIONS.md). The runtime proofs use an explicit [binary-arithmetic cost model](lean-verification/ALGORITHMS.md), rather than certifying the performance of a compiled executable. No paper-result proof is pending within that stated conditional scope; proving the external contracts themselves is outside it. Polynomial-time algorithms for the exact two-pad and flexible-glue minimum-value problems remain open, as discussed in the paper.
