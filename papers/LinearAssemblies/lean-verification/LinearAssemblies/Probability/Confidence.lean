import LinearAssemblies.Probability.TiltedWindow

set_option autoImplicit false

namespace LinearAssemblies.Probability

open LinearAssemblies.Forest

noncomputable def confidenceScale (N δ : ℝ) : ℝ := min N (Real.log δ⁻¹)
noncomputable def confidenceEntropy (N δ : ℝ) : ℝ :=
  confidenceScale N δ * Real.log (1 + N / confidenceScale N δ)

theorem confidenceScale_pos (N δ : ℝ) (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < confidenceScale N δ := by
  unfold confidenceScale
  rw [Real.log_inv]
  exact lt_min hN (neg_pos.mpr (Real.log_neg hδ hδ1))

namespace UniformGraph

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

/-- Lemma 10's core polynomial bounds, with the explicit constants from the paper. -/
theorem confidence_polynomial_bounds (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (i : g.TransientState) (N δ : ℝ) (hN : 0 < N) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (E : Finset ℕ) (hgood : 1 - δ ≤ ∑ k ∈ E, g.stoppingMass k i.val)
    (hwindow : ∀ k ∈ E, N / 4 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * N) :
    confidenceScale N δ / 36 ≤ (g.transientCounts.B.natDegree : ℝ) ∧
    confidenceEntropy N δ / 36 ≤ Real.log (evalReal 1 g.transientCounts.B) := by
  let σ := confidenceScale N δ
  let x := σ / (2 * N)
  have hσ : 0 < σ := confidenceScale_pos N δ hN hδ (by linarith)
  have hσN : σ ≤ N := min_le_left _ _
  have hσlog : σ ≤ Real.log δ⁻¹ := min_le_right _ _
  have hx : 0 < x := div_pos hσ (by positivity)
  have hxhalf : x ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < 2 * N by positivity)).mpr
    linarith
  have hx1 : 0 < 1 + x := by linarith
  have hchoice : 2 * N * x = σ := by dsimp [x]; field_simp
  have hsurvive : ∀ k ∈ E, δ ≤ (1 + x)⁻¹ ^ k := by
    intro k hk
    exact alarm_survival N σ x δ hx.le hδ hσlog hchoice k (hwindow k hk).2
  have hmean := g.tiltedMean_lower ext hh x hx.le i.val E (N / 4) δ
    (by positivity) hδ.le hδ2 hgood (fun k hk => (hwindow k hk).1) hsurvive
  have hf : 2 * x / 3 ≤ x / (1 + x) := by
    apply (le_div_iff₀ hx1).mpr
    nlinarith
  have hμ : σ / 36 ≤ x * evalReal x g.transientCounts.B.derivative /
      evalReal x g.transientCounts.B := by
    calc
      σ / 36 = (2 * x / 3) * (N / 12) := by rw [← hchoice]; ring
      _ ≤ (x / (1 + x)) * (N / 12) := mul_le_mul_of_nonneg_right hf (by positivity)
      _ ≤ (x / (1 + x)) * (g.tiltedMoment x i.val / g.transform x i.val) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ ≤ _ := g.logarithmic_derivative_bound ext hh x hx i
  have hb := g.transientCounts.B_real_pos (g.transient_haltable hh) x hx.le
  constructor
  · exact hμ.trans ((div_le_iff₀ hb).mpr (weighted_degree_le g.transientCounts.B_nonneg x hx.le))
  · have hlog : 0 ≤ Real.log x⁻¹ := Real.log_nonneg
      ((one_le_inv₀ hx).mpr (by linarith))
    have hcompare : 1 + N / σ ≤ x⁻¹ := by
      dsimp [x]
      rw [inv_div]
      apply (le_div_iff₀ hσ).mpr
      field_simp
      nlinarith
    have hlogcompare := Real.log_le_log (show 0 < 1 + N / σ by positivity) hcompare
    calc
      confidenceEntropy N δ / 36 = (σ / 36) * Real.log (1 + N / σ) := by
        dsimp [confidenceEntropy, σ]; ring
      _ ≤ (σ / 36) * Real.log x⁻¹ := mul_le_mul_of_nonneg_left hlogcompare (by positivity)
      _ ≤ (x * evalReal x g.transientCounts.B.derivative / evalReal x g.transientCounts.B) *
          Real.log x⁻¹ := mul_le_mul_of_nonneg_right hμ hlog
      _ ≤ _ := log_coeff_sum_bound g.transientCounts.B_nonneg
        (g.transientCounts.B_zero_pos (g.transient_haltable hh)) x hx

end UniformGraph
end LinearAssemblies.Probability
