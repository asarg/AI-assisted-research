import LinearAssemblies.Concentration.Parameters

set_option autoImplicit false

namespace LinearAssemblies.Concentration

theorem log_ratio_lower {N R : ℝ} (hR : 0 < R) (hRN : R ≤ N) :
    (1 : ℝ) / 2 ≤ Real.log (1 + N / R) := by
  have hx : 1 ≤ N / R := (one_le_div hR).2 hRN
  exact Probability.log_two_bounds.1.trans (Real.log_le_log (by norm_num) (by linarith))

theorem phi_ratio_lower {N R : ℝ} (hR : 0 < R) (hRN : R ≤ N) :
    (1 : ℝ) / 4 ≤ phi (N / R) :=
  phi_one_lower.trans (phi_mono (by norm_num) ((one_le_div hR).2 hRN))

theorem enlarged_ratio {A N R : ℝ} (hA : 1 ≤ A) (hR : 0 < R) (hN : 0 ≤ N) :
    2 * N / (A * R) ≤ 2 * (N / R) := by
  have hAR : R ≤ A * R := by nlinarith
  have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * N) hR hAR
  simpa only [mul_div_assoc] using h

theorem probabilistic_log_budget {A N R : ℝ} (hA : 1 ≤ A) (hR : 1 ≤ R) (hRN : R ≤ N) :
    1 + 3 / Real.log 3 * (A * R) * Real.log (1 + 2 * N / (A * R)) ≤
      (4 + 144 * A) * R * Real.log (1 + N / R) := by
  have hRp : 0 < R := by linarith
  have hN : 0 ≤ N := by linarith
  have hx : 0 ≤ N / R := by positivity
  have hl := log_ratio_lower hRp hRN
  have hlog : Real.log (1 + 2 * N / (A * R)) ≤ 2 * Real.log (1 + N / R) :=
    (Real.log_le_log (by positivity) (by linarith [enlarged_ratio hA hRp hN])).trans (log_one_add_double hx)
  have hlog0 : 0 ≤ Real.log (1 + 2 * N / (A * R)) := Real.log_nonneg (by
    have h : 0 ≤ 2 * N / (A * R) := by positivity
    linarith)
  have hl3 : (1 : ℝ) / 2 ≤ Real.log 3 := Probability.log_two_bounds.1.trans
    (Real.log_le_log (by norm_num) (by norm_num))
  have hc : 3 / Real.log 3 ≤ 6 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hstep : 3 / Real.log 3 * (A * R) * Real.log (1 + 2 * N / (A * R)) ≤
      12 * A * R * Real.log (1 + N / R) := by
    calc
      _ ≤ 6 * (A * R) * Real.log (1 + 2 * N / (A * R)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hlog0
      _ ≤ 6 * (A * R) * (2 * Real.log (1 + N / R)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  have hseed : 1 ≤ 2 * R * Real.log (1 + N / R) := by nlinarith
  have hbig : 0 ≤ A * R * Real.log (1 + N / R) := by positivity
  nlinarith

theorem probabilistic_phi_budget {A N R : ℝ} (hA : 1 ≤ A) (hR : 1 ≤ R) (hRN : R ≤ N) :
    1 + 72 * (A * R) * phi (2 * N / (A * R)) ≤
      (4 + 144 * A) * R * phi (N / R) := by
  have hRp : 0 < R := by linarith
  have hN : 0 ≤ N := by linarith
  have hx : 0 ≤ N / R := by positivity
  have hl := phi_ratio_lower hRp hRN
  have hphi : phi (2 * N / (A * R)) ≤ 2 * phi (N / R) :=
    (phi_mono (by positivity) (enlarged_ratio hA hRp hN)).trans (phi_double hx)
  have hstep := mul_le_mul_of_nonneg_left hphi (show 0 ≤ 72 * (A * R) by positivity)
  have hseed : 1 ≤ 4 * R * phi (N / R) := by nlinarith
  nlinarith

theorem deterministic_log_budget {A N R : ℝ} (hA : 1 ≤ A) (hR : 1 ≤ R) (hRN : R ≤ N)
    (hdet : N ≤ A * R) : N ≤ (4 + 144 * A) * R * Real.log (1 + N / R) := by
  have hl := log_ratio_lower (by linarith : 0 < R) hRN
  have hbase : A * R ≤ 2 * A * R * Real.log (1 + N / R) := by
    nlinarith [mul_le_mul_of_nonneg_left hl (show 0 ≤ A * R by positivity)]
  have hpos : 0 ≤ A * R * Real.log (1 + N / R) := by positivity
  have hpos' : 0 ≤ R * Real.log (1 + N / R) := by positivity
  nlinarith

theorem deterministic_phi_budget {A N R : ℝ} (hA : 1 ≤ A) (hR : 1 ≤ R) (hRN : R ≤ N)
    (hdet : N ≤ A * R) : N ≤ (4 + 144 * A) * R * phi (N / R) := by
  have hl := phi_ratio_lower (by linarith : 0 < R) hRN
  have hbase : A * R ≤ 4 * A * R * phi (N / R) := by
    nlinarith [mul_le_mul_of_nonneg_left hl (show 0 ≤ A * R by positivity)]
  have hpos : 0 ≤ A * R * phi (N / R) := by positivity
  have hpos' : 0 ≤ R * phi (N / R) := by positivity
  nlinarith

end LinearAssemblies.Concentration
