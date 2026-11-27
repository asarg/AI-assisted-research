import LinearAssemblies.CoefficientBounds
import LinearAssemblies.Probability.MeanCoefficientBound
import LinearAssemblies.LowerBounds

set_option autoImplicit false

namespace LinearAssemblies.System

open Probability Forest

variable {I : Type} [DecidableEq I] (s : System I)
variable (compat : I → I → Prop) [DecidableRel compat]

/-- The same integral forest polynomials bound the expected length for any compatibility rule. -/
theorem mean_growth_bound (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat) :
    s.expectedLength compat ≤ 1 + (2 * (s.cost : ℝ)) ^ s.cost := by
  let g := s.toGraph compat
  let gr := g.restrict s.initialState
  let i : g.ReachableState s.initialState := ⟨s.initialState, .refl⟩
  have hm := gr.mean_le_coeff_sum ext (g.restrict_haltable _ hh) i
  rw [UniformGraph.restrict_expected] at hm
  have hc : evalReal 1 (s.absorptionCounts compat).B ≤ (2 * (s.cost : ℝ)) ^ s.cost := by
    rw [evalReal_one]
    exact_mod_cast (s.general_coefficient_bounds compat).2
  rw [s.expectedLength_eq compat ext hh]
  exact add_le_add_left (hm.trans hc) 1

theorem log_mean_growth_bound (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat)
    (N : ℝ) (hN : 0 < N) (hmean : s.expectedLength compat = N) :
    Real.log N ≤ Real.log 2 + (s.cost : ℝ) * Real.log (2 * (s.cost : ℝ)) := by
  have hm : (1 : ℝ) ≤ s.cost := by exact_mod_cast (show 1 ≤ s.cost by simp [cost])
  have hb := s.mean_growth_bound compat ext hh
  rw [hmean] at hb
  have hpow : (1 : ℝ) ≤ (2 * (s.cost : ℝ)) ^ s.cost := one_le_pow₀ (by linarith)
  have hl := Real.log_le_log hN (show N ≤ 2 * (2 * (s.cost : ℝ)) ^ s.cost by linarith)
  rwa [Real.log_mul (by norm_num) (pow_ne_zero _ (by positivity)), Real.log_pow] at hl

/-- Theorem 4 with explicit threshold N>=16 and constant 1/4, for arbitrary compatibility.
This also proves the flexible-glue generalization directly, without a separate SICOMP assumption. -/
theorem expected_length_lower_bound (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat)
    (N : ℕ) (hN : 16 ≤ N) (hmean : s.expectedLength compat = (N : ℝ)) :
    Real.log N / (4 * Real.log (Real.log N)) ≤ (s.cost : ℝ) := by
  have hm : (1 : ℝ) ≤ s.cost := by exact_mod_cast (show 1 ≤ s.cost by simp [cost])
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlarge : (2 : ℝ) ≤ Real.log N := by
    have hpow : (2 : ℝ)^4 ≤ N := by norm_num; exact_mod_cast hN
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < (2 : ℝ)^4) hpow
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith [log_two_bounds.1]
  have hloglog : 1 / 2 ≤ Real.log (Real.log N) :=
    log_two_bounds.1.trans (Real.log_le_log (by norm_num) hlarge)
  have hpos : 0 < 4 * Real.log (Real.log N) := by linarith
  have hg := s.log_mean_growth_bound compat ext hh N hNpos hmean
  have hhalf : Real.log N / 2 ≤ (s.cost : ℝ) * Real.log (2 * (s.cost : ℝ)) := by
    linarith [log_two_bounds.2]
  apply (div_le_iff₀ hpos).mpr
  by_cases hsmall : Real.log N ≤ (s.cost : ℝ)
  · nlinarith
  · have hcomp : 2 * (s.cost : ℝ) ≤ (Real.log N)^2 := by nlinarith
    have hl := Real.log_le_log (show 0 < 2 * (s.cost : ℝ) by linarith) hcomp
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    have hp := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ s.cost by positivity)
    nlinarith

end LinearAssemblies.System
