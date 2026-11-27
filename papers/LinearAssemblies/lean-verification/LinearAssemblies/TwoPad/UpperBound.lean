import LinearAssemblies.TwoPad.Realization
import LinearAssemblies.Analysis.BaseChoice

set_option autoImplicit false

namespace LinearAssemblies.TwoPad

/-- Lemma 6: every target has a concrete two-pad block with O(Phi(M)) entries
and remaining mean at most 2M. The constant 72 is uniform, including M=1. -/
theorem balanced_block_exists (ext : Probability.FiniteAbsorptionLaw) (M : ℕ) (hM : 1 ≤ M) :
    ∃ d : DigitData (selectedBase M), d.value = M ∧
      (presentation d).system.Haltable twoPad ∧
      (presentation d).system.expectedLength twoPad = (M : ℝ) + 1 ∧
      ((presentation d).system.cost : ℝ) ≤ 72 * phi M ∧
      ∀ x, ((presentation d).system.toGraph twoPad).expected x ≤ 2 * (M : ℝ) := by
  have hb := selectedBase_ge_two M
  obtain ⟨d, hv, hh, he, hc, _⟩ := exact_construction ext (selectedBase M) M hb hM
  refine ⟨d, hv, hh, he, hc.trans (selectedBase_cost M hM), ?_⟩
  have hbase := selectedBase_le M hM
  have hbudget : selectedBase M - 2 ≤ d.value := by omega
  simpa only [hv] using block_remaining_bound d ext hb hbudget

/-- Theorem 5 with an explicit constant and threshold. The finite tile presentation
also gives a flexible-glue construction by treating interface pairs as single labels. -/
theorem logarithmic_upper_bound (ext : Probability.FiniteAbsorptionLaw)
    (N : ℕ) (hN : 16 ≤ N) :
    ∃ d : DigitData (selectedBase (N - 1)), d.value = N - 1 ∧
      (presentation d).system.Haltable twoPad ∧
      (presentation d).system.expectedLength twoPad = (N : ℝ) ∧
      ((presentation d).system.cost : ℝ) ≤ 72 * (Real.log N / Real.log (Real.log N)) := by
  have hN1 : 1 ≤ N := by omega
  have hM : 1 ≤ N - 1 := by omega
  obtain ⟨d, hv, hh, he, hc, _⟩ := balanced_block_exists ext (N - 1) hM
  have hshift : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast Nat.sub_add_cancel hN1
  have hlarge : (2 : ℝ) ≤ Real.log N := by
    have hpow : (2 : ℝ)^4 ≤ N := by norm_num; exact_mod_cast hN
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < (2 : ℝ)^4) hpow
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith [Probability.log_two_bounds.1]
  have hlpos : 0 < Real.log N := by linarith
  have hllpos : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  have hphi : phi (N - 1 : ℕ) ≤ Real.log N / Real.log (Real.log N) := by
    unfold phi
    rw [add_comm (1 : ℝ), hshift]
    apply div_le_div_of_nonneg_left hlpos.le hllpos
    exact Real.log_le_log hlpos (by linarith)
  refine ⟨d, hv, hh, by simpa only [hshift] using he, ?_⟩
  exact hc.trans (mul_le_mul_of_nonneg_left hphi (by norm_num))

end LinearAssemblies.TwoPad
