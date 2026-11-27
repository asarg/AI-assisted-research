# External-assumption register

This project verifies the November 26, 2026 draft of **How Many Tiles Does It
Take to Build a Line in Expectation and with Confidence?**, by Divya Bajaj,
Bin Fu, and Robert Schweller (26 pages).

## Verification policy

The proved conditional claims have the form `ExternalFacts -> PaperConclusion`.
External facts are explicit hypotheses with their full mathematical statements. Their premises must be discharged at each application. Standard
facts already proved in the pinned Mathlib version should be used directly.

No theorem from this paper may silently become an external assumption. In
particular, the exact one-pad characterization and Lemma 9 are project
proofs, not external assumptions. The flexible-glue expected-length lower bound and Lemma 10 are also project
proofs, with all paper-specific premises checked.

The completed project uses E01 for finite-chain semantics, E03a/E03b for
concentration, and E04/E08 for the fast optimization algorithm. All are explicit
theorem hypotheses. E03a is the generic
subexponential tail-to-exponential-moment equivalence; E03b is Bernstein's
inequality. No tile, reset, composition, or one-pad optimization claim appears in them.
The full forest expansion, restart bound, fresh-label compiler, and stopping-law
composition are project proofs. Standard determinant and analytic results
already in Mathlib are used without additional external contracts.

## Active contract: E01

For every finite uniform graph in which each state has a finite path to an
empty-outdegree state, `FiniteAbsorptionLaw` asserts:

1. `HasSum (fun k => stoppingMass k x) 1` for each initial state x.
2. Summability of `fun k : Nat => (k : Real) * stoppingMass k x`.
3. The expectation defined by that series satisfies the nonnegative first-step
   equations, with zero at terminal states.
4. Any nonnegative solution of those equations equals the expectation.

Source checked: Charles M. Grinstead and J. Laurie Snell, *Introduction to
Probability*, Section 11.2, Theorems 11.3–11.5, printed pages 417–420:
<https://chance.dartmouth.edu/teaching_aids/books_articles/probability_book/Chapter11.pdf>.
These give absorption with probability one, the invertible fundamental matrix,
and finite expected absorption times. The contract expresses these facts for
uniform transition lists; uniqueness follows from the stated invertibility.
This is a recorded specialization of those results, not a verbatim quotation
or a claim that this specialization has itself been formally proved here.

The graph, exact finite stopping probabilities, reachable restriction,
nonnegative compiler potentials, and proof of haltability are project proofs.
No tile budget, extremal recurrence, reset construction, or conclusion of
Theorems 1–8 occurs in E01. In particular, the lower bound is proved from the
first-step equations, not assumed as a Markov-chain fact.

`Audit.lean` prints the types of all four contract fields and the principal
conditional conclusions. Because E01 is a hypothesis rather than an axiom,
`#print axioms` alone will not display it; both kinds of inspection are required.

## Active contracts: E03a and E03b

Source checked: Roman Vershynin, *High-Dimensional Probability*, first edition,
Proposition 2.7.1 (a) implies (d), Definition 2.7.5, and Theorem 2.8.1,
printed pages 32–33 and 36–37:
<https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf>.

`Probability/SubexponentialExternal.lean` states both contracts in full.

- E03a (`SubexponentialEquivalence`) concerns an arbitrary normalized
  nonnegative discrete law p and observable X. A tail bound
  Pr(|X|>=u)<=2 exp(-u/K), for every u>=0, yields a summable exponential
  moment with E exp(|X|/(C K))<=2, for one universal C>=1.
- E03b (`BernsteinLaw`) concerns any finite list of normalized discrete laws.
  Every mean is a convergent `HasSum`; each centered exponential moment is
  summable and at most two at its positive asserted scale. For upper bounds
  V on the sum of squared scales and B on every scale, the independent-sum
  deviation is <=2 exp(-c min(t^2/V,t/B)), for one universal c>0.

The independent-sum law is explicitly defined by finite Cauchy convolutions;
this is the usual specialization of independence to discrete summands. It is
not a free assumption about the tile process. `Concatenation/Distribution`
and `Sequence` prove that the actual fresh-label tile process has exactly this
law, including when the final block is empty.

These are recorded discrete specializations of the cited standard facts.
Their general probability-theory proofs are intentionally outside the conditional
scope. The project proves the centered block tail with scale 32M, discharges
normalization and mean assumptions, and derives Lemma 8 with its universal
constant from these two generic hypotheses. This uses the equivalent
exponential-moment form instead of repeating the paper's factorial-moment route.
Theorem 8's balanced partition, parameter rounding, deterministic case, actual
mean, and tile budgets are all project proofs.

## Active arithmetic contracts: E04 and E08

`Algorithms/Arithmetic.lean` defines costed subroutine interfaces. The theorem
`Algorithms/Complexity.theorem_seven` takes implementations and proofs of
both contracts as explicit inputs. `theorem_six` needs neither contract.

E04 (`Multiplication.Fast`) asserts an exact product and an upper bound
C*(size(a)+size(b)+1)*log(size(a)+size(b)+2) on the routine's declared bit cost,
with C>=1. Source: David Harvey and Joris van der Hoeven, *Integer multiplication
in time O(n log n)*, Annals of Mathematics 193 (2021), 563–617:
<https://annals.math.princeton.edu/2021/193-2/p04>.
The published theorem is in the multitape Turing-machine model with binary
integers. Using the sum of operand widths instead of their maximum weakens
the bound, and padding plus a larger constant covers all small inputs.
The project proves exact repeated squaring and its geometric cost sum using
this generic interface; no power-of-three algorithm is assumed in E04.

E08 (`Logarithm.Polynomial`) asserts an unsigned fixed-point approximation:
`abs(run(x,p)/2^p - log x) <= 2^(-p)` for integers x>=2, and, for each fixed x,
a polynomial upper bound in p+1 on its bit cost. Source: Richard P. Brent,
*Fast Multiple-Precision Evaluation of Elementary Functions*, JACM 23 (1976),
242–251, Theorem 6.1 (printed p.249):
<https://maths-people.anu.edu.au/~brent/pd/rpb034.pdf>.
The source provides the stronger O(M(p) log p) evaluation bound on fixed
positive intervals. Additional precision, fixed-point rounding and adjusted
constants give the weaker stated absolute-error contract. Ordinary polynomial
integer arithmetic suffices for the polynomial consequence; it does not
require importing the paper's own optimizer or exponent localization.

This is an explicit alternative to the paper's illustrative truncated-series
calculation. The project proves the chosen precision, quotient error, output
bit lengths, exponent window, exact threshold selection, polynomial cost of
the approximation stage, and its domination by the main cost. E08 makes no
reference to beta, candidates, tile budgets, or MIN1.

As with the probability contracts, these are source-checked reformulations,
not internally proved external theorems. Cost counters represent implementations
satisfying the stated contracts. The elementary-operation envelopes and the
scope of the binary-arithmetic model are explained in `ALGORITHMS.md`; no
claim about a specific compiler or host-language runtime follows from them.

## External-fact register

| ID | Source / fact | Intended use | Applicability obligations |
|---|---|---|---|
| E01 — active | Grinstead–Snell, Section 11.2, Theorems 11.3–11.5 | Normalization, finite mean, first-step equations and uniqueness | Finite uniform transitions and reachable restriction are constructed; graph haltability is proved before each application. Higher moments/transforms are not included in the active contract. |
| E02 — not needed | Strong Markov / restart facts | Block tails and concatenation | Restart contraction and the concrete stopping-law convolution are proved directly. No E02 hypothesis. |
| E03a/b — active | Vershynin, Proposition 2.7.1 and Theorem 2.8.1 | Lemma 8 and concentration upper bounds | Explicit generic contracts above; actual block law, centered tail, normalization, mean, physical composition, and parameter substitution are proved. |
| E04 — active | Harvey--van der Hoeven integer multiplication, Annals of Mathematics 193(2), 2021, paper reference [8] | Theorem 7 bit complexity | Explicit product/cost contract; repeated squaring, operand widths and geometric cost sum are proved. |
| E05 — not needed | Chandran--Gopalkrishnan--Reif, SICOMP 41(4), 2012, paper reference [6], Sections 7.3--7.4 | Theorem 4 | The project now derives the expected-length lower bound directly for arbitrary compatibility from the verified forest transform. No E05 hypothesis is used. |
| E06 — no extra contract | Standard calculus identities in Mathlib | Transform differentiation and analytic bounds | Convergence, differentiability and positivity premises are discharged. E03a/b supply the recorded generic probability facts. |
| E07 — no extra contract | Standard finite-dimensional linear algebra | Cramer's rule and invertibility | Prefer Mathlib. The nonnegative coefficient and forest representation of Lemma 9 is now proved using Mathlib determinant algebra. No external E07 assumption is used. |
| E08 — active | Brent, JACM 23 (1976), Theorem 6.1 | Low-precision log approximation in Theorem 7 | Generic fixed-point contract; precision, quotient stability, encoding width and resulting candidate search are proved. |

E08 is an additional standard source used for an alternative proof of the
approximation step. Every active external source was checked before its
contract was introduced. The register does not license stronger variants.

## Audit requirements

1. All delivered proof modules must compile using the pinned toolchain.
2. No `sorry`, `admit`, or custom global `axiom` declarations in project proofs.
3. No native-decision shortcut relying on unchecked compilation for numerical
   examples; ordinary kernel-checked proofs are used.
4. `Audit.lean` reports the assumptions of the main proved declarations.
5. Explicit theorem hypotheses remain visible in theorem types. The audit of
   foundational axioms does not replace review of those hypotheses.
6. Unproved parts of the paper are recorded in `STATUS.md`, not represented by
   placeholder theorems with misleading names.
