import LinearAssemblies.Confidence

set_option autoImplicit false

namespace LinearAssemblies.Probability

theorem log_two_bounds : (1 : ℝ) / 2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h

theorem confidenceEntropy_bounds (N δ : ℝ) (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < confidenceEntropy N δ ∧ confidenceEntropy N δ ≤ N := by
  let σ := confidenceScale N δ
  have hs : 0 < σ := confidenceScale_pos N δ hN hδ hδ1
  have ht : 0 < N / σ := div_pos hN hs
  have hl : 0 < Real.log (1 + N / σ) := Real.log_pos (by linarith)
  constructor
  · exact mul_pos hs hl
  · have he := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (show 0 < 1 + N / σ by positivity)) hs.le
    change σ * Real.log (1 + N / σ) ≤ N
    have hcancel : σ * ((1 + N / σ) - 1) = N := by field_simp
    simpa only [hcancel] using he

theorem regularized_log_lower (G : ℝ) (hG : 0 ≤ G) : 1 / 2 ≤ Real.log (2 + G) :=
  log_two_bounds.1.trans (Real.log_le_log (by norm_num) (by linarith))

/-- Invert the coefficient bound with a uniform explicit constant. -/
theorem growth_inverse_bound (m G : ℝ) (hm : 1 ≤ m) (hG : 0 ≤ G)
    (hbound : G / 36 ≤ m * Real.log (2 * m)) :
    G / (72 * Real.log (2 + G)) ≤ m := by
  have hlog := regularized_log_lower G hG
  have hden : 0 < 72 * Real.log (2 + G) := by linarith
  apply (div_le_iff₀ hden).mpr
  by_cases hsmall : G ≤ m
  · nlinarith
  · have hbig : m < G := lt_of_not_ge hsmall
    have hcomp : 2 * m ≤ (2 + G) ^ 2 := by nlinarith
    have hlogs := Real.log_le_log (show 0 < 2 * m by linarith) hcomp
    rw [Real.log_pow] at hlogs
    norm_num only [Nat.cast_ofNat] at hlogs
    have hprod := mul_le_mul_of_nonneg_left hlogs (show 0 ≤ m by linarith)
    nlinarith

end LinearAssemblies.Probability

namespace LinearAssemblies.System

open Probability

variable {I : Type} [DecidableEq I] (s : System I)
variable (compat : I → I → Prop) [DecidableRel compat]

/-- Theorem 8, Eq. 27: one explicit constant works for all permitted parameters. -/
theorem general_concentration_lower_bound (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat)
    (N : ℕ) (eps δ : ℝ) (hN : 2 ≤ N) (heps : 0 < eps) (hepsHalf : eps ≤ 1 / 2)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hconf : 1 - δ ≤ s.attachmentWindow compat
      (FiniteChain.lowerEndpoint N eps) (FiniteChain.upperEndpoint N eps)) :
    max (confidenceScale N δ)
      (max (confidenceEntropy N δ / Real.log (2 + confidenceEntropy N δ))
        (min (N : ℝ) eps⁻¹)) / 72 ≤ (s.cost : ℝ) := by
  have hm : (1 : ℝ) ≤ s.cost := by exact_mod_cast (show 1 ≤ s.cost by simp [cost])
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hG := confidenceEntropy_bounds N δ hNr hδ (by linarith)
  have hl := regularized_log_lower (confidenceEntropy N δ) hG.1.le
  have hlpos : 0 < Real.log (2 + confidenceEntropy N δ) := by linarith
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 72)).mpr
  apply max_le
  · by_cases hN4 : 4 ≤ N
    · have hs := (s.general_confidence_bounds compat ext hh N eps δ
        hN4 heps hepsHalf hδ hδ2 hconf).1
      linarith
    · have hs : confidenceScale N δ ≤ (N : ℝ) := min_le_left _ _
      have hn : (N : ℝ) < 4 := by exact_mod_cast (show N < 4 by omega)
      linarith
  · apply max_le
    · by_cases hN4 : 4 ≤ N
      · have hc := (s.general_confidence_bounds compat ext hh N eps δ
          hN4 heps hepsHalf hδ hδ2 hconf).2
        have hi := growth_inverse_bound s.cost (confidenceEntropy N δ) hm hG.1.le hc
        have hden : 0 < 72 * Real.log (2 + confidenceEntropy N δ) := by positivity
        have hmult := (div_le_iff₀ hden).mp hi
        apply (div_le_iff₀ hlpos).mpr
        nlinarith
      · have hn : (N : ℝ) < 4 := by exact_mod_cast (show N < 4 by omega)
        apply (div_le_iff₀ hlpos).mpr
        nlinarith
    · have ha : min (N : ℝ) eps⁻¹ / 24 ≤ (s.cost : ℝ) := by
        by_cases hN4 : 4 ≤ N
        · exact s.accuracy_lower_bound compat N eps hN4 heps hepsHalf (by linarith)
        · exact s.accuracy_small_target N eps (by omega)
      linarith

/-- Theorem 8, Eq. 25: the one-pad lower bound, without any prescribed mean. -/
theorem onePad_concentration_lower_bound {α : Type} [DecidableEq α] (s : System (Option α))
    (ext : FiniteAbsorptionLaw) (hh : s.Haltable onePad)
    (N : ℕ) (eps δ : ℝ) (hN : 2 ≤ N) (heps : 0 < eps) (hepsHalf : eps ≤ 1 / 2)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hconf : 1 - δ ≤ s.attachmentWindow onePad
      (FiniteChain.lowerEndpoint N eps) (FiniteChain.upperEndpoint N eps)) :
    max (confidenceEntropy N δ) (min (N : ℝ) eps⁻¹) / 36 ≤ (s.cost : ℝ) := by
  have hm : (1 : ℝ) ≤ s.cost := by exact_mod_cast (show 1 ≤ s.cost by simp [cost])
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 36)).mpr
  apply max_le
  · by_cases hN4 : 4 ≤ N
    · have hc := (s.onePad_confidence_bounds ext hh N eps δ
        hN4 heps hepsHalf hδ hδ2 hconf).2
      have hl := mul_le_mul_of_nonneg_left log_two_bounds.2 (show (0 : ℝ) ≤ s.cost by positivity)
      linarith
    · have hn : (N : ℝ) < 4 := by exact_mod_cast (show N < 4 by omega)
      have hb := (confidenceEntropy_bounds N δ
        (by exact_mod_cast (show 0 < N by omega)) hδ (by linarith)).2
      linarith
  · have ha : min (N : ℝ) eps⁻¹ / 24 ≤ (s.cost : ℝ) := by
      by_cases hN4 : 4 ≤ N
      · exact s.accuracy_lower_bound onePad N eps hN4 heps hepsHalf (by linarith)
      · exact s.accuracy_small_target N eps (by omega)
    linarith

end LinearAssemblies.System
