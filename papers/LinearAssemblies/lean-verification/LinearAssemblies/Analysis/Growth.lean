import LinearAssemblies.Analysis.BaseChoice

set_option autoImplicit false

namespace LinearAssemblies

theorem regular_log_ratio_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    s / Real.log (2 + s) ≤ t / Real.log (2 + t) := by
  have hsp : 0 < 2 + s := by linarith
  have htp : 0 < 2 + t := by linarith
  have hsl : 0 < Real.log (2 + s) := Real.log_pos (by linarith)
  have htl : 0 < Real.log (2 + t) := Real.log_pos (by linarith)
  have hdiff : Real.log (2 + t) - Real.log (2 + s) ≤ (t - s) / (2 + s) := by
    have h := Real.log_le_sub_one_of_pos (div_pos htp hsp)
    rw [Real.log_div htp.ne' hsp.ne'] at h
    convert h using 1
    field_simp
  have hbase : s / (2 + s) ≤ Real.log (2 + s) := by
    have h := Real.one_sub_inv_le_log_of_pos hsp
    have hh : s / (2 + s) ≤ 1 - (2 + s)⁻¹ := by
      apply (div_le_iff₀ hsp).2
      have he : (1 - (2 + s)⁻¹) * (2 + s) = 1 + s := by field_simp; ring
      rw [he]
      linarith
    exact hh.trans h
  have h1 := mul_le_mul_of_nonneg_left hdiff hs
  have h2 := mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr hst)
  have he : s * ((t - s) / (2 + s)) = (t - s) * (s / (2 + s)) := by ring
  rw [he] at h1
  apply (div_le_div_iff₀ hsl htl).2
  nlinarith

theorem phi_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : phi x ≤ phi y := by
  apply regular_log_ratio_mono
  · exact Real.log_nonneg (by linarith)
  · exact Real.log_le_log (by linarith) (by linarith)

theorem phi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ phi x := by
  unfold phi
  exact div_nonneg (Real.log_nonneg (by linarith))
    (Real.log_nonneg (by linarith [Real.log_nonneg (show 1 ≤ 1 + x by linarith)]))

theorem phi_pos {x : ℝ} (hx : 0 < x) : 0 < phi x := by
  unfold phi
  have h := Real.log_pos (show 1 < 1 + x by linarith)
  exact div_pos h (Real.log_pos (by linarith))

theorem log_one_add_double {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + 2 * x) ≤ 2 * Real.log (1 + x) := by
  have h := Real.log_le_log (by linarith : 0 < 1 + 2 * x)
    (show 1 + 2 * x ≤ (1 + x) ^ 2 by nlinarith [sq_nonneg x])
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem phi_double {x : ℝ} (hx : 0 ≤ x) : phi (2 * x) ≤ 2 * phi x := by
  have hl : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hd : 0 < Real.log (2 + Real.log (1 + x)) := Real.log_pos (by linarith)
  have ha : Real.log (1 + x) ≤ Real.log (1 + 2 * x) :=
    Real.log_le_log (by linarith) (by linarith)
  have hdd : Real.log (2 + Real.log (1 + x)) ≤ Real.log (2 + Real.log (1 + 2 * x)) :=
    Real.log_le_log (by linarith) (by linarith)
  unfold phi
  calc
    _ ≤ Real.log (1 + 2 * x) / Real.log (2 + Real.log (1 + x)) :=
      div_le_div_of_nonneg_left (hl.trans ha) hd hdd
    _ ≤ (2 * Real.log (1 + x)) / Real.log (2 + Real.log (1 + x)) :=
      div_le_div_of_nonneg_right (log_one_add_double hx) hd.le
    _ = _ := by ring

theorem phi_one_lower : (1 : ℝ) / 4 ≤ phi 1 := by
  have hl := Probability.log_two_bounds
  have hlog : Real.log (2 + Real.log 2) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 2 + Real.log 2 by linarith)
    linarith
  have hd : 0 < Real.log (2 + Real.log 2) := Real.log_pos (by linarith)
  unfold phi
  norm_num only [one_add_one_eq_two]
  apply (le_div_iff₀ hd).2
  linarith

end LinearAssemblies
