import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Size

set_option autoImplicit false

namespace LinearAssemblies.Algorithms

/-- An externally supplied binary integer multiplication routine and its
bit-operation count. Both fields are ordinary functions, usable by algorithms. -/
structure Multiplication where
  run : ℕ → ℕ → ℕ
  steps : ℕ → ℕ → ℕ

/-- E04: the standard fast multiplication theorem, in a costed subroutine
interface. The uniform bound absorbs finitely many small inputs. Width includes
one padding bit, so zero operands and logarithms at zero cause no exception.
Source: Harvey--van der Hoeven, Annals of Mathematics 193 (2021), 563--617,
Theorem 1.1, https://annals.math.princeton.edu/2021/193-2/p04 . -/
structure Multiplication.Fast (m : Multiplication) : Prop where
  correct : ∀ a b, m.run a b = a * b
  bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℕ,
    (m.steps a b : ℝ) ≤ C * (a.size + b.size + 1) * Real.log (a.size + b.size + 2)

/-- An external fixed-point logarithm routine: `run x p` is an unsigned
integer representing an approximation after division by `2^p`. -/
structure Logarithm where
  run : ℕ → ℕ → ℕ
  steps : ℕ → ℕ → ℕ

/-- E08: polynomial-time approximation of logarithms at fixed positive integer
arguments. This deliberately weak consequence of Brent's general elementary
function evaluation theorem also follows from geometric log series. It is
independent of tile systems, thresholds, and the one-pad algorithm.

Source: Brent, JACM 23 (1976), 242--251, Theorem 6.1 (printed p.249),
https://maths-people.anu.edu.au/~brent/pd/rpb034.pdf . Converting relative to
absolute error, rounding to unsigned fixed point, and absorbing extra precision
changes only the constants. We use this standard external theorem in place of
reimplementing the illustrative log-series evaluation in the paper.
-/
structure Logarithm.Polynomial (l : Logarithm) : Prop where
  accurate : ∀ x p : ℕ, 2 ≤ x →
    |(l.run x p : ℝ) / (2 : ℝ) ^ p - Real.log x| ≤ (2 : ℝ)⁻¹ ^ p
  bound : ∀ x : ℕ, 2 ≤ x → ∃ C d : ℕ, ∀ p : ℕ,
    l.steps x p ≤ C * (p + 1) ^ d

end LinearAssemblies.Algorithms
