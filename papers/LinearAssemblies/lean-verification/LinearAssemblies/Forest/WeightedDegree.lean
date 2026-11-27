import LinearAssemblies.Forest.RealPolynomial
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false

namespace LinearAssemblies.Forest

open Polynomial

theorem evalReal_derivative_sum (p : ℤ[X]) (x : ℝ) :
    evalReal x p.derivative = ∑ j ∈ Finset.range (p.natDegree + 1),
      (p.coeff j : ℝ) * ((j : ℝ) * x ^ (j - 1)) := by
  have hd := HasDerivAt.sum (u := Finset.range (p.natDegree + 1))
    (fun j (_ : j ∈ Finset.range (p.natDegree + 1)) => (hasDerivAt_pow j x).const_mul (p.coeff j : ℝ))
  simp_rw [← evalReal_sum] at hd
  exact (evalReal_hasDerivAt p x).unique hd

theorem weighted_degree_sum (p : ℤ[X]) (x : ℝ) :
    x * evalReal x p.derivative = ∑ j ∈ Finset.range (p.natDegree + 1),
      (j : ℝ) * (p.coeff j : ℝ) * x ^ j := by
  rw [evalReal_derivative_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases j with
  | zero => simp
  | succ j => simp only [Nat.add_sub_cancel, pow_succ]; ring

theorem weighted_degree_le {p : ℤ[X]} (hp : NonnegCoeffs p) (x : ℝ) (hx : 0 ≤ x) :
    x * evalReal x p.derivative ≤ p.natDegree * evalReal x p := by
  rw [weighted_degree_sum, evalReal_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hj' : (j : ℝ) ≤ p.natDegree := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hn : (0 : ℝ) ≤ (p.coeff j : ℝ) * x ^ j :=
    mul_nonneg (by exact_mod_cast hp j) (pow_nonneg hx j)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hj' hn

/-- Jensen's inequality for the coefficient distribution, with all weights explicit. -/
theorem log_coeff_sum_bound {p : ℤ[X]} (hp : NonnegCoeffs p)
    (h0 : 1 ≤ p.eval 0) (x : ℝ) (hx : 0 < x) :
    (x * evalReal x p.derivative / evalReal x p) * Real.log x⁻¹ ≤
      Real.log (evalReal 1 p) := by
  let b := evalReal x p
  have hb : 1 ≤ b := (show (1 : ℝ) ≤ (p.eval 0 : ℤ) by exact_mod_cast h0).trans
    (evalReal_ge_constant hp x hx.le)
  have hb0 : 0 < b := by linarith
  let w : ℕ → ℝ := fun j => (p.coeff j : ℝ) * x ^ j / b
  have hw : ∀ j ∈ Finset.range (p.natDegree + 1), 0 ≤ w j := by
    intro j _
    exact div_nonneg (mul_nonneg (by exact_mod_cast hp j) (pow_nonneg hx.le j)) hb0.le
  have hs : ∑ j ∈ Finset.range (p.natDegree + 1), w j = 1 := by
    simp only [w, ← Finset.sum_div, ← evalReal_sum]
    exact div_self hb0.ne'
  have hj := convexOn_exp.map_sum_le hw hs
    (fun j (_ : j ∈ Finset.range (p.natDegree + 1)) =>
      Set.mem_univ ((j : ℝ) * Real.log x⁻¹))
  simp only [smul_eq_mul] at hj
  have he : (∑ j ∈ Finset.range (p.natDegree + 1), w j * ((j : ℝ) * Real.log x⁻¹)) =
      (x * evalReal x p.derivative / b) * Real.log x⁻¹ := by
    rw [weighted_degree_sum, Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [w]
    ring
  have hr : (∑ j ∈ Finset.range (p.natDegree + 1), w j * Real.exp ((j : ℝ) * Real.log x⁻¹)) =
      evalReal 1 p / b := by
    rw [evalReal_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hx)]
    dsimp [w]
    rw [inv_pow]
    field_simp [hx.ne']
    ring
  rw [he, hr] at hj
  have hnonneg : 0 ≤ evalReal 1 p := evalReal_nonneg hp 1 (by norm_num)
  have hdiv : evalReal 1 p / b ≤ evalReal 1 p := div_le_self hnonneg hb
  have ht := Real.log_le_log (Real.exp_pos _) (hj.trans hdiv)
  simpa only [Real.log_exp] using ht

end LinearAssemblies.Forest
