# Verified optimization algorithms and cost model

The paper defines MIN1 as a **value problem**: for binary input N>=1, output
the minimum total tile-entry count C1(N). It does not require printing an
optimal tile multiset. The formal algorithms have this same output. Separate
construction and characterization proofs provide actual-system witnesses.

## Sequential algorithm (Theorem 6)

`Algorithms/Sequential.lean` implements a three-register scan. It starts with
F(2), F(1), F(0) and updates by the proved three-candidate recurrence. Small
targets are handled explicitly. Its fuel is bounded by three times the
binary length of the attachment target, plus five; it does not iterate up to
the numeric target.

`scan_spec` proves the register invariant, first-threshold answer, and charged
cost together. `F_at_stop` bounds every relevant recurrence value by 3M.
`sequentialLength` adds the seed to the output. Its cost satisfies the explicit
bound 2688*(size(N)+2)^2. `theorem_six` joins the tile-level minimum statement
with the eventual O(log² N) bound.

## Fast algorithm (Theorem 7)

1. For M=N-1>=7, form Y=2M+3 and its binary length B.
2. Request fixed-point approximations to log 2 and log 3 at precision
   p=size(B)+8 from the generic E08 routine. Their quotient approximates
   beta=log(2)/log(3) within 1/(4B).
3. Compute a=floor((B-1)*betaApprox). Check exponents in
   [max(0,a-5),a+1], at most seven candidates.
4. For each coefficient 23, 33, 47, use exact repeated-squaring powers and
   exact integer comparisons to select its least passing exponent.
5. Return one plus the minimum of 5+3q0, 6+3q1, 7+3q2.

`Candidates` proves the localization interval, including clipping at zero;
no approximate equality decides an integer threshold. `Approximation` proves
the quotient error and that fixed-point outputs use at most p+2 bits.
`FastSearch` implements the exact search and proves its answer equals the
original minimum-budget definition. Small N are handled by the verified scan.

`Power` supplies repeated squaring with only one recursive call per halving.
Its cost proof sums the geometrically decreasing operand sizes. `BitGrowth`
proves that any fixed polynomial in size(B) is eventually dominated by B, so
the approximation stage does not introduce an extra logarithmic factor.
`Complexity.fastLength_bit_cost` proves O(b log(b+1)) for b=size(N), and
`theorem_seven` proves the paper's O(log N log log N) form together with
optimality for actual tile systems.

## Meaning of “bit cost”

Each algorithm is a costed function returning (answer, charged operations).
Elementary additions, comparisons, constant shifts/multiplications, parity,
halving, copies and counter updates are charged linear envelopes in the
operand bit lengths. Fixed-point quotient/center work is charged a cubic
schoolbook envelope in size(B)+p+8. These conservative envelopes cover a
constant number of standard binary-arithmetic operations; they define the
abstract implementation model. They are not timings of the host-language
Nat or Rat operations.

General multiplication calls use the supplied routine's explicit `steps`
field. E04 asserts its exact product and the uniform bound
C*(size(a)+size(b)+1)*log(size(a)+size(b)+2). Logarithm calls similarly use
the supplied routine's cost; E08 asserts accuracy and a polynomial bound in
requested precision for each fixed integer argument. These routines are
external implementations with stated contracts, not formally verified machine
programs inside this archive.

Lean checks the functional answers, bit-length inequalities, loop/recursion
cost sums, candidate counts, precision transfer, eventual domination, and
asymptotic bounds in this model. Compilation from this model to a particular
Turing machine, hardware ISA, or Lean executable is outside the deliverable.
The artifact should not be described as a verified high-performance executable
or an unconditional bit-level implementation of Harvey--van der Hoeven/Brent.
