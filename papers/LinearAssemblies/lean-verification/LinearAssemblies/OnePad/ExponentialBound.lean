import LinearAssemblies.OnePad.Characterization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace LinearAssemblies.OnePad

/-- Integer-only form of Lemma 3, derived from the already proved exact closed form. -/
theorem F_cube_bound (r : ℕ) : (9 * (2 * F r + 3)) ^ 3 ≤ 23 ^ 3 * 3 ^ (r + 1) := by
  by_cases hr : r < 5
  · interval_cases r <;> norm_num [F, Finset.range_succ]
  · have hmod : (r - 5) % 3 < 3 := Nat.mod_lt _ (by omega)
    have hdiv := Nat.mod_add_div (r - 5) 3
    generalize hq : (r - 5) / 3 = q at *
    generalize hj : (r - 5) % 3 = j at *
    interval_cases j
    · have he : r = 3 * q + 5 := by omega
      rw [he, (closed_form_scaled q).1]
      rw [show 3 * q + 5 + 1 = q * 3 + 6 by omega, pow_add, pow_mul]
      ring_nf
      exact le_rfl
    · have he : r = 3 * q + 6 := by omega
      rw [he, (closed_form_scaled q).2.1]
      rw [show 3 * q + 6 + 1 = q * 3 + 7 by omega, pow_add, pow_mul]
      ring_nf
      omega
    · have he : r = 3 * q + 7 := by omega
      rw [he, (closed_form_scaled q).2.2]
      rw [show 3 * q + 7 + 1 = q * 3 + 8 by omega, pow_add, pow_mul]
      ring_nf
      omega

/-- Lemma 3 in the paper's real exponential notation. -/
theorem F_exponential_bound (r : ℕ) :
    (F r : ℝ) + 3 / 2 ≤ (23 / 18 : ℝ) * (3 : ℝ) ^ (((r : ℝ) + 1) / 3) := by
  have hi : ((9 : ℝ) * (2 * (F r : ℝ) + 3)) ^ 3 ≤ 23 ^ 3 * (3 : ℝ) ^ (r + 1) := by
    exact_mod_cast F_cube_bound r
  have he : ((3 : ℝ) ^ (((r : ℝ) + 1) / 3)) ^ (3 : ℕ) = (3 : ℝ) ^ (r + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num only [Nat.cast_ofNat]
    rw [div_mul_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_cast
  apply (pow_le_pow_iff_left₀ (by positivity)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) (by decide : (3 : ℕ) ≠ 0)).mp
  rw [mul_pow, he]
  nlinarith

set_option exponentiation.threshold 1000 in
/-- Certify the decimal constant using a finite integer comparison. -/
theorem logarithmic_constant_lt : 3 * Real.log (23 / 18 : ℝ) < (67 / 100 : ℝ) * Real.log 3 := by
  have hi : (23 : ℕ) ^ 300 < 18 ^ 300 * 3 ^ 67 := by norm_num
  have hr : (23 / 18 : ℝ) ^ 300 < (3 : ℝ) ^ 67 := by
    rw [div_pow]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 18 ^ (300 : ℕ))).mpr
    have hi' := hi
    rw [Nat.mul_comm] at hi'
    exact_mod_cast hi'
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < (23 / 18 : ℝ) ^ (300 : ℕ)) hr
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

/-- Theorem 2, for any positive real mean, hence in particular every integer target. -/
theorem logarithmic_lower_bound (ext : Probability.FiniteAbsorptionLaw)
    {α : Type} [DecidableEq α] (s : System (Option α)) (hh : s.Haltable onePad)
    (N : ℝ) (hN : 0 < N) (hmean : s.expectedLength onePad = N) :
    3 * Real.log N / Real.log 3 - 0.670 < (s.cost : ℝ) := by
  have hm := mean_le_F ext s hh
  rw [hmean] at hm
  have hi : ((9 : ℝ) * (2 * (F s.entryCount : ℝ) + 3)) ^ 3 ≤
      23 ^ 3 * (3 : ℝ) ^ s.cost := by
    exact_mod_cast F_cube_bound s.entryCount
  have hn : (18 : ℝ) * N < 9 * (2 * (F s.entryCount : ℝ) + 3) := by linarith
  have hcube : ((18 : ℝ) * N) ^ 3 < 23 ^ 3 * (3 : ℝ) ^ s.cost :=
    lt_of_lt_of_le (pow_lt_pow_left₀ hn (by positivity) (by decide : (3 : ℕ) ≠ 0)) hi
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < ((18 : ℝ) * N) ^ (3 : ℕ)) hcube
  rw [Real.log_pow, Real.log_mul (by norm_num) hN.ne',
    Real.log_mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hc := logarithmic_constant_lt
  rw [Real.log_div (by norm_num) (by norm_num)] at hc
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  apply (sub_lt_iff_lt_add).mpr
  apply (div_lt_iff₀ hlog3).mpr
  nlinarith

end LinearAssemblies.OnePad
