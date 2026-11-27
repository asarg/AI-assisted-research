import LinearAssemblies.Forest.Representation
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false

namespace LinearAssemblies.Forest

open Polynomial

/-- Real evaluation preserves the integral coefficient certificates. -/
noncomputable def evalReal (x : ℝ) : ℤ[X] →+* ℝ :=
  eval₂RingHom (Int.castRingHom ℝ) x

@[simp] theorem evalReal_C (x : ℝ) (n : ℤ) : evalReal x (C n) = n := by
  simp [evalReal]
@[simp] theorem evalReal_X (x : ℝ) : evalReal x X = x := by
  simp [evalReal]

theorem evalReal_int (p : ℤ[X]) (n : ℤ) : evalReal (n : ℝ) p = p.eval n :=
  eval₂_at_apply (Int.castRingHom ℝ) n

@[simp] theorem evalReal_zero (p : ℤ[X]) : evalReal 0 p = ((p.eval 0 : ℤ) : ℝ) :=
  by simpa only [Int.cast_zero] using evalReal_int p 0
@[simp] theorem evalReal_one (p : ℤ[X]) : evalReal 1 p = ((p.eval 1 : ℤ) : ℝ) :=
  by simpa only [Int.cast_one] using evalReal_int p 1

theorem evalReal_sum (p : ℤ[X]) (x : ℝ) :
    evalReal x p = ∑ j ∈ Finset.range (p.natDegree + 1), (p.coeff j : ℝ) * x ^ j :=
  eval₂_eq_sum_range _ _

theorem evalReal_ge_constant {p : ℤ[X]} (hp : NonnegCoeffs p) (x : ℝ) (hx : 0 ≤ x) :
    ((p.eval 0 : ℤ) : ℝ) ≤ evalReal x p := by
  rw [evalReal_sum]
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range (p.natDegree + 1)) =>
      mul_nonneg (show (0 : ℝ) ≤ p.coeff j by exact_mod_cast hp j) (pow_nonneg hx j))
    (show 0 ∈ Finset.range (p.natDegree + 1) by simp)
  simpa [coeff_zero_eq_eval_zero] using h

theorem evalReal_nonneg {p : ℤ[X]} (hp : NonnegCoeffs p) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ evalReal x p := by
  have h0 : (0 : ℝ) ≤ p.eval 0 := by
    rw [← coeff_zero_eq_eval_zero]
    exact_mod_cast hp 0
  exact h0.trans (evalReal_ge_constant hp x hx)

theorem derivative_nonneg {p : ℤ[X]} (hp : NonnegCoeffs p) :
    NonnegCoeffs p.derivative := by
  intro j
  rw [coeff_derivative]
  exact mul_nonneg (hp (j + 1)) (by positivity)

theorem evalReal_hasDerivAt (p : ℤ[X]) (x : ℝ) :
    HasDerivAt (fun y => evalReal y p) (evalReal x p.derivative) x := by
  simpa only [evalReal, coe_eval₂RingHom, eval₂_eq_eval_map, derivative_map] using
    (p.map (Int.castRingHom ℝ)).hasDerivAt x

namespace Counts
variable {S : Type} [Fintype S] [DecidableEq S] (c : Counts S)

theorem B_real_pos (hh : c.Haltable) (x : ℝ) (hx : 0 ≤ x) : 0 < evalReal x c.B := by
  have h0 : (1 : ℝ) ≤ c.B.eval 0 := by exact_mod_cast c.B_zero_pos hh
  exact lt_of_lt_of_le (by linarith) (evalReal_ge_constant c.B_nonneg x hx)

theorem H_real_pos (hh : c.Haltable) (s : S) (x : ℝ) (hx : 0 ≤ x) :
    0 < evalReal x (c.H s) := by
  have h0 : (1 : ℝ) ≤ (c.H s).eval 0 := by
    rw [← c.B_zero_eq_H_zero s]
    exact_mod_cast c.B_zero_pos hh
  exact lt_of_lt_of_le (by linarith) (evalReal_ge_constant (c.H_nonneg s) x hx)

end Counts
end LinearAssemblies.Forest
