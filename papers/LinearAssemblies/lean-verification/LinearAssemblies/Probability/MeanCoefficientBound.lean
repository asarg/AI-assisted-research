import LinearAssemblies.Probability.TransformBound
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false

namespace LinearAssemblies.Probability

open Filter

/-- Dominated convergence at alarm parameter zero; the weights never exceed one. -/
theorem weighted_series_limit (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hs : Summable a) :
    Tendsto (fun x : ℝ => ∑' k : ℕ, a k * (1 + x)⁻¹ ^ k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑' k, a k)) := by
  apply tendsto_tsum_of_dominated_convergence hs
  · intro k
    have hc : ContinuousAt (fun x : ℝ => a k * (1 + x)⁻¹ ^ k) 0 := by
      fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx k
    have hx' : 0 < x := hx
    have hx1 : 0 < 1 + x := by linarith
    have hq : (1 + x)⁻¹ ≤ 1 := (inv_le_one₀ hx1).mpr (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha k) (by positivity))]
    exact mul_le_of_le_one_right (ha k) (pow_le_one₀ (inv_nonneg.mpr hx1.le) hq)

namespace UniformGraph

open LinearAssemblies.Forest

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

theorem transform_limit_zero (ext : FiniteAbsorptionLaw) (hh : g.Haltable) (i : S) :
    Tendsto (fun x => g.transform x i) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h := weighted_series_limit (fun k => g.stoppingMass k i)
    (fun k => g.stoppingMass_nonneg k i) (ext.normalized g hh i).summable
  rwa [(ext.normalized g hh i).tsum_eq] at h

theorem tiltedMoment_limit_zero (ext : FiniteAbsorptionLaw) (hh : g.Haltable) (i : S) :
    Tendsto (fun x => g.tiltedMoment x i) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g.expected i)) :=
  weighted_series_limit (fun k => (k : ℝ) * g.stoppingMass k i)
    (fun k => mul_nonneg (Nat.cast_nonneg k) (g.stoppingMass_nonneg k i)) (ext.finite_mean g hh i)

/-- The limiting logarithmic derivative controls the original, untilted mean. -/
theorem mean_le_derivative_zero (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (i : g.TransientState) :
    g.expected i.val ≤ evalReal 0 g.transientCounts.B.derivative / evalReal 0 g.transientCounts.B := by
  have hb := g.transientCounts.B_real_pos (g.transient_haltable hh) 0 le_rfl
  have hnum := (evalReal_hasDerivAt g.transientCounts.B.derivative 0).continuousAt.tendsto
  have hden := (evalReal_hasDerivAt g.transientCounts.B 0).continuousAt.tendsto
  have hright := (hnum.div hden hb.ne').mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hx1 : Tendsto (fun x : ℝ => 1 + x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using (continuous_const.add continuous_id).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
  have hleft := (g.tiltedMoment_limit_zero ext hh i.val).div
    (hx1.mul (g.transform_limit_zero ext hh i.val)) (by norm_num : (1 : ℝ) * 1 ≠ 0)
  simp only [mul_one, div_one] at hleft
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < x := hx
  have h := g.logarithmic_derivative_bound ext hh x hx' i
  have he : x * (g.tiltedMoment x i.val / ((1 + x) * g.transform x i.val)) ≤
      x * (evalReal x g.transientCounts.B.derivative / evalReal x g.transientCounts.B) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h
  exact (mul_le_mul_left hx').mp he

end UniformGraph
end LinearAssemblies.Probability

namespace LinearAssemblies.Forest

open Polynomial

theorem coeff_le_evalReal_one (p : ℤ[X]) (hp : NonnegCoeffs p) (j : ℕ) :
    (p.coeff j : ℝ) ≤ evalReal 1 p := by
  by_cases hj : j ≤ p.natDegree
  · rw [evalReal_sum]
    have hf : ∀ k ∈ Finset.range (p.natDegree + 1),
        0 ≤ (p.coeff k : ℝ) * (1 : ℝ) ^ k := by
      intro k _
      exact mul_nonneg (by exact_mod_cast hp k) (by positivity)
    have h := Finset.single_le_sum hf
      (show j ∈ Finset.range (p.natDegree + 1) by simp; omega)
    simpa using h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), Int.cast_zero]
    exact evalReal_nonneg hp 1 (by norm_num)

theorem derivative_zero_le_one (p : ℤ[X]) (hp : NonnegCoeffs p) :
    evalReal 0 p.derivative ≤ evalReal 1 p := by
  rw [evalReal_zero, ← coeff_zero_eq_eval_zero, coeff_derivative]
  simpa using coeff_le_evalReal_one p hp 1

end LinearAssemblies.Forest

namespace LinearAssemblies.Probability.UniformGraph

open LinearAssemblies.Forest

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

theorem mean_le_coeff_sum (ext : FiniteAbsorptionLaw) (hh : g.Haltable) (i : S) :
    g.expected i ≤ evalReal 1 g.transientCounts.B := by
  by_cases hi : g.out i = []
  · rw [(ext.first_step g hh).terminal i hi]
    exact evalReal_nonneg g.transientCounts.B_nonneg 1 (by norm_num)
  · have h := g.mean_le_derivative_zero ext hh ⟨i, hi⟩
    have hb : 1 ≤ evalReal 0 g.transientCounts.B := by
      rw [evalReal_zero]
      exact_mod_cast g.transientCounts.B_zero_pos (g.transient_haltable hh)
    have hn := evalReal_nonneg (derivative_nonneg g.transientCounts.B_nonneg) 0 le_rfl
    exact h.trans ((div_le_self hn hb).trans (derivative_zero_le_one _ g.transientCounts.B_nonneg))

end LinearAssemblies.Probability.UniformGraph
