import LinearAssemblies.LowerBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

namespace LinearAssemblies

/-- The regularized growth function of Definition 2. -/
noncomputable def phi (x : ℝ) : ℝ := Real.log (1 + x) / Real.log (2 + Real.log (1 + x))

noncomputable def selectedBase (M : ℕ) : ℕ := max 2 (Nat.ceil (Real.sqrt (Real.log ((M : ℝ) + 1))))

theorem selectedBase_ge_two (M : ℕ) : 2 ≤ selectedBase M := le_max_left _ _

theorem selectedBase_le (M : ℕ) (hM : 1 ≤ M) : selectedBase M ≤ M + 1 := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ht : Real.log ((M : ℝ) + 1) ≤ M := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < (M : ℝ) + 1 by positivity)
  have hs : Real.sqrt (Real.log ((M : ℝ) + 1)) ≤ (M : ℝ) + 1 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  apply max_le (by omega)
  apply Nat.ceil_le.mpr
  simpa only [Nat.cast_add, Nat.cast_one] using hs

/-- A uniform bound, including small targets, for the paper's chosen base. -/
theorem selectedBase_cost (M : ℕ) (hM : 1 ≤ M) :
    3 * (selectedBase M : ℝ) + 2 * Real.log M / Real.log (selectedBase M) + 1 ≤
      72 * phi M := by
  let t := Real.log ((M : ℝ) + 1)
  let u := Real.sqrt t
  let D := Real.log (2 + t)
  let b := selectedBase M
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ht : (1 : ℝ) / 2 ≤ t := Probability.log_two_bounds.1.trans
    (Real.log_le_log (by norm_num) (by linarith))
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := Real.sqrt_pos.mpr ht0
  have hu2 : u ^ 2 = t := Real.sq_sqrt ht0.le
  have hD0 : 0 < D := Real.log_pos (by linarith)
  have hD3 : D ≤ 3 * t := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 2 + t by linarith)
    dsimp [D]
    linarith
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast selectedBase_ge_two M
  have hblog : 0 < Real.log b := Real.log_pos (by linarith)
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hMr
  have hlogM : Real.log M ≤ t := Real.log_le_log (by linarith) (by linarith)
  have htarget : phi M = t / D := by simp only [phi, t, D, add_comm]
  rw [htarget]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hD0).mpr
  by_cases hsmall : t ≤ 4
  · have hu : u ≤ 2 := by
      apply (Real.sqrt_le_left (by norm_num)).mpr
      norm_num
      exact hsmall
    have hceil : Nat.ceil u ≤ 2 := Nat.ceil_le.mpr (by exact hu)
    have hb : b = 2 := by dsimp [b, selectedBase]; exact max_eq_left hceil
    have hl2 := Probability.log_two_bounds.1
    have hterm : 2 * Real.log M / Real.log 2 ≤ 16 := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      linarith
    have hc : 3 * (b : ℝ) + 2 * Real.log M / Real.log b + 1 ≤ 23 := by
      rw [hb]; norm_num only [Nat.cast_ofNat]; linarith
    have hm := mul_le_mul_of_nonneg_right hc hD0.le
    nlinarith
  · have ht4 : 4 ≤ t := by linarith
    have hu : 2 ≤ u := by
      apply (Real.le_sqrt (by norm_num) ht0.le).mpr
      norm_num
      exact ht4
    have hceil0 : u ≤ (Nat.ceil u : ℝ) := Nat.le_ceil u
    have hceil2 : 2 ≤ Nat.ceil u := by exact_mod_cast (show (2 : ℝ) ≤ Nat.ceil u by linarith)
    have hb : b = Nat.ceil u := by dsimp [b, selectedBase]; exact max_eq_right hceil2
    have hbu : u ≤ (b : ℝ) := by rw [hb]; exact hceil0
    have hbu2 : (b : ℝ) ≤ 2 * u := by
      rw [hb]
      have hceil := Nat.ceil_lt_add_one hu0.le
      linarith
    have hlogt0 : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogu := Real.log_le_log hu0 hbu
    rw [Real.log_sqrt ht0.le] at hlogu
    have hDt : D ≤ 2 * Real.log t := by
      have h := Real.log_le_log (show 0 < 2 + t by linarith)
        (show 2 + t ≤ t ^ 2 by nlinarith)
      rw [Real.log_pow] at h
      norm_num only [Nat.cast_ofNat] at h
      exact h
    have hDb : D / Real.log b ≤ 4 := by
      apply (div_le_iff₀ hblog).mpr
      linarith
    have hDu : D ≤ 2 * u := by
      have hcomp := Real.log_le_log (show 0 < 2 + t by linarith)
        (show 2 + t ≤ 2 * t by linarith)
      rw [Real.log_mul (by norm_num) ht0.ne'] at hcomp
      have hlu := Real.log_le_sub_one_of_pos hu0
      rw [Real.log_sqrt ht0.le] at hlu
      linarith [Probability.log_two_bounds.2]
    have hbD : (b : ℝ) * D ≤ 4 * t := by
      have h := mul_le_mul hbu2 hDu hD0.le (show 0 ≤ 2 * u by positivity)
      nlinarith
    have hterm : (2 * Real.log M / Real.log b) * D ≤ 8 * t := by
      calc
        (2 * Real.log M / Real.log b) * D = 2 * Real.log M * (D / Real.log b) := by ring
        _ ≤ 2 * Real.log M * 4 := mul_le_mul_of_nonneg_left hDb (by positivity)
        _ ≤ 8 * t := by linarith
    nlinarith

end LinearAssemblies
