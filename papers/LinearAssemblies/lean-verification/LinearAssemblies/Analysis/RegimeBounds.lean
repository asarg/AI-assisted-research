import LinearAssemblies.Concentration.Budgets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace LinearAssemblies

theorem log_quotient_lower {N T : ℝ} (hN : 0 < N) (hT : 0 < T) (hTsq : T ^ 2 ≤ N) :
    Real.log N / 2 ≤ Real.log (1 + N / T) := by
  have h := Real.log_le_log (sq_pos_of_pos hT) hTsq
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have hq := Real.log_le_log (div_pos hN hT) (show N / T ≤ 1 + N / T by linarith)
  rw [Real.log_div hN.ne' hT.ne'] at hq
  linarith

theorem log_quotient_upper {N T : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hT : 1 ≤ T) :
    Real.log (1 + N / T) ≤ 2 * Real.log N := by
  have hTp : 0 < T := by linarith
  have hq : N / T ≤ N := (div_le_iff₀ hTp).2 (by nlinarith)
  have h := Real.log_le_log (by positivity : 0 < 1 + N / T)
    (show 1 + N / T ≤ 2 * N by linarith)
  rw [Real.log_mul (by norm_num) (by linarith : N ≠ 0)] at h
  linarith [Probability.log_two_bounds.2]

theorem phi_quotient_upper {N T : ℝ} (hN : 1 ≤ N) (hlog : 4 ≤ Real.log N)
    (hT : 1 ≤ T) (hTsq : T ^ 2 ≤ N) :
    phi (N / T) ≤ 4 * Real.log N / Real.log (Real.log N) := by
  have hNp : 0 < N := by linarith
  have hTp : 0 < T := by linarith
  have hlow := log_quotient_lower hNp hTp hTsq
  have hupp := log_quotient_upper hN (by linarith : 1 ≤ Real.log N) hT
  have hll : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  have hden : Real.log (Real.log N) / 2 ≤ Real.log (2 + Real.log (1 + N / T)) := by
    have hsq : Real.log N ≤ (2 + Real.log (1 + N / T)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (1 + N / T))]
    have h := Real.log_le_log (by linarith : 0 < Real.log N) hsq
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hd : 0 < Real.log (2 + Real.log (1 + N / T)) := lt_of_lt_of_le (by positivity) hden
  unfold phi
  calc
    _ ≤ (2 * Real.log N) / (Real.log (Real.log N) / 2) := by
      exact div_le_div₀ (by linarith) hupp (by positivity) hden
    _ = _ := by ring

theorem entropy_ratio_lower {N S : ℝ} (hN : 1 ≤ N) (hlog : 4 ≤ Real.log N)
    (hS : 1 / 2 ≤ S) (hSsq : S ^ 2 ≤ N) (hSlog : S ≤ (Real.log N) ^ 2 / 2) :
    S * Real.log N / (8 * Real.log (Real.log N)) ≤
      (S * Real.log (1 + N / S)) / Real.log (2 + S * Real.log (1 + N / S)) := by
  have hSp : 0 < S := by linarith
  have hNp : 0 < N := by linarith
  have hll : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  let G := S * Real.log (1 + N / S)
  have hGpos : 0 < G := mul_pos hSp (Real.log_pos (by have h := div_pos hNp hSp; linarith))
  have hGlow : S * Real.log N / 2 ≤ G := by
    have h := mul_le_mul_of_nonneg_left (log_quotient_lower hNp hSp hSsq) hSp.le
    dsimp [G]
    linarith
  have hGup : G ≤ (Real.log N) ^ 3 := by
    have hfrac : N / S ≤ 2 * N := (div_le_iff₀ hSp).2 (by nlinarith)
    have h := Real.log_le_log (by positivity : 0 < 1 + N / S)
      (show 1 + N / S ≤ 3 * N by linarith)
    rw [Real.log_mul (by norm_num) hNp.ne'] at h
    have hl3 : Real.log (3 : ℝ) ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      norm_num at h
      exact h
    have hfactor : Real.log (1 + N / S) ≤ 2 * Real.log N := by linarith
    have hmul := mul_le_mul_of_nonneg_left hfactor hSp.le
    have hs := mul_le_mul_of_nonneg_right hSlog (show 0 ≤ 2 * Real.log N by linarith)
    dsimp [G]
    nlinarith
  have hden : Real.log (2 + G) ≤ 4 * Real.log (Real.log N) := by
    have hu : 2 + G ≤ (Real.log N) ^ 4 := by
      have hu0 : 2 ≤ (Real.log N) ^ 3 := by nlinarith [sq_nonneg (Real.log N)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (pow_nonneg (show 0 ≤ Real.log N by linarith) 3)]
    have h := Real.log_le_log (by positivity : 0 < 2 + G) hu
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hdenpos : 0 < Real.log (2 + G) := Real.log_pos (by linarith)
  change _ ≤ G / Real.log (2 + G)
  calc
    _ = (S * Real.log N / 2) / (4 * Real.log (Real.log N)) := by ring
    _ ≤ G / Real.log (2 + G) := div_le_div₀ (by positivity) hGlow hdenpos hden

end LinearAssemblies
