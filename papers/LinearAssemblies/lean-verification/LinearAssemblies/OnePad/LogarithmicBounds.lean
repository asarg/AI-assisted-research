import LinearAssemblies.PositiveDigits
import LinearAssemblies.OnePad.Characterization
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

namespace LinearAssemblies.OnePad

/-- A strengthened integer certificate for the ternary construction's cost. -/
theorem ternary_cost_cube (p : PositiveDigits) (hp : p.Valid 3) :
    8 * 3 ^ (p.reset 3).cost ≤ (2 * p.value 3 + 1) ^ 3 := by
  induction p with
  | single a =>
    have ha1 : 1 ≤ a := hp.1
    have ha3 : a ≤ 3 := hp.2
    interval_cases a <;> norm_num [PositiveDigits.reset, ResetProgram.cost, PositiveDigits.value]
  | snoc p a ih =>
    have h := ih hp.1
    have ha : 1 ≤ a := hp.2.1
    simp only [PositiveDigits.reset, ResetProgram.cost, PositiveDigits.value, pow_add]
    have hm := Nat.mul_le_mul_right 27 h
    have hcube := Nat.pow_le_pow_left (show 3 * (2 * p.value 3 + 1) ≤
      2 * (3 * p.value 3 + a) + 1 by omega) 3
    nlinarith

/-- Theorem 1's cost inequality for a compiled positive ternary word. -/
theorem ternary_cost_log (p : PositiveDigits) (hp : p.Valid 3) :
    ((p.reset 3).cost : ℝ) ≤ 3 * Real.log ((p.value 3 : ℝ) + 1) / Real.log 3 := by
  have hcube : (8 : ℝ) * 3 ^ (p.reset 3).cost ≤ (2 * (p.value 3 : ℝ) + 1) ^ 3 := by
    exact_mod_cast ternary_cost_cube p hp
  have hmean : (0 : ℝ) < p.value 3 := by exact_mod_cast p.value_pos 3 hp
  have hpow : (3 : ℝ) ^ (p.reset 3).cost ≤ ((p.value 3 : ℝ) + 1) ^ 3 := by nlinarith
  have hl := Real.log_le_log (pow_pos (by norm_num) _) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))).mpr hl

/-- Theorem 1, with a concrete tile system and its exact expected length. -/
theorem logarithmic_upper_bound (ext : Probability.FiniteAbsorptionLaw)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ m : ℕ, LengthRealizable m N ∧ (m : ℝ) ≤ 3 * Real.log N / Real.log 3 + 1 := by
  by_cases hN1 : N = 1
  · subst N
    have hz : minimumBudget 0 = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (minimumBudget_le_iff 0 0).mpr (by simp)
    refine ⟨1, ?_, by norm_num⟩
    simpa [recurrenceCost, hz] using (minimum_tile_cost ext 1 (by omega)).1
  · obtain ⟨p, hp, hv⟩ := PositiveDigits.represents 3 (N - 1) (by omega) (by omega)
    obtain ⟨b, hbval, hbcost⟩ := CertifiedBlock.compile_exists (p.reset 3) (p.reset_valid 3 hp)
    have hreal := block_realizes ext b
    have hval : b.value = N - 1 := by rw [hbval, p.reset_value, hv]
    rw [hval] at hreal
    refine ⟨b.cost + 1, (lengthRealizable_iff b.cost N hN).mpr hreal, ?_⟩
    have hc := ternary_cost_log p hp
    have he : (p.value 3 : ℝ) + 1 = N := by rw [hv]; exact_mod_cast Nat.sub_add_cancel hN
    rw [he, ← hbcost] at hc
    push_cast
    linarith

end LinearAssemblies.OnePad
