import LinearAssemblies.CoefficientBounds
import LinearAssemblies.Accuracy
import LinearAssemblies.Probability.Confidence

set_option autoImplicit false

namespace LinearAssemblies.System

open Probability Forest

variable {I : Type} [DecidableEq I] (s : System I)
variable (compat : I → I → Prop) [DecidableRel compat]

theorem confidence_polynomial_bounds (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat)
    (N : ℕ) (eps δ : ℝ) (hN : 4 ≤ N) (heps : 0 < eps) (hepsHalf : eps ≤ 1 / 2)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hconf : 1 - δ ≤ s.attachmentWindow compat
      (FiniteChain.lowerEndpoint N eps) (FiniteChain.upperEndpoint N eps)) :
    confidenceScale N δ / 36 ≤ ((s.absorptionCounts compat).B.natDegree : ℝ) ∧
    confidenceEntropy N δ / 36 ≤ Real.log (evalReal 1 (s.absorptionCounts compat).B) := by
  let g := (s.toGraph compat).restrict s.initialState
  let i : (s.toGraph compat).ReachableState s.initialState := ⟨s.initialState, .refl⟩
  let E := Finset.Icc (FiniteChain.lowerEndpoint N eps) (FiniteChain.upperEndpoint N eps)
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hwindow : ∀ k ∈ E, (N : ℝ) / 4 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * N := by
    intro k hk
    have hw := (FiniteChain.mem_window_iff N k eps hN heps hepsHalf).mp hk
    rw [abs_le] at hw
    constructor <;> nlinarith
  have hg : 1 - δ ≤ ∑ k ∈ E, g.stoppingMass k i := by
    simpa only [g, i, UniformGraph.restrict_mass] using hconf
  have hi : g.out i ≠ [] := by
    intro hterminal
    have hz : ∀ k ∈ E, g.stoppingMass k i = 0 := by
      intro k hk
      have hk0 : k ≠ 0 := by
        intro hk0
        have hw := (hwindow k hk).1
        rw [hk0, Nat.cast_zero] at hw
        linarith
      cases k with
      | zero => exact (hk0 rfl).elim
      | succ k => simp [UniformGraph.stoppingMass, UniformGraph.degree, hterminal]
    have hzsum := Finset.sum_eq_zero hz
    rw [hzsum] at hg
    linarith
  exact g.confidence_polynomial_bounds ext
    ((s.toGraph compat).restrict_haltable s.initialState hh) ⟨i, hi⟩ N δ
    (by linarith) hδ hδ2 E hg hwindow

/-- The two numerical confidence inequalities for arbitrary tile compatibility. -/
theorem general_confidence_bounds (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat)
    (N : ℕ) (eps δ : ℝ) (hN : 4 ≤ N) (heps : 0 < eps) (hepsHalf : eps ≤ 1 / 2)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hconf : 1 - δ ≤ s.attachmentWindow compat
      (FiniteChain.lowerEndpoint N eps) (FiniteChain.upperEndpoint N eps)) :
    confidenceScale N δ / 36 ≤ (s.cost : ℝ) ∧
    confidenceEntropy N δ / 36 ≤ (s.cost : ℝ) * Real.log (2 * (s.cost : ℝ)) := by
  obtain ⟨hd, hl⟩ := s.confidence_polynomial_bounds compat ext hh N eps δ
    hN heps hepsHalf hδ hδ2 hconf
  obtain ⟨hdeg, hcoeff⟩ := s.general_coefficient_bounds compat
  refine ⟨hd.trans (by exact_mod_cast hdeg), hl.trans ?_⟩
  have hpos := (s.absorptionCounts compat).B_real_pos (s.absorptionCounts_haltable compat hh) 1
    (by norm_num)
  have hcoeff' : evalReal 1 (s.absorptionCounts compat).B ≤ (2 * (s.cost : ℝ)) ^ s.cost := by
    rw [evalReal_one]
    exact_mod_cast hcoeff
  simpa only [Real.log_pow] using Real.log_le_log hpos hcoeff'

/-- One-pad compatibility gives the stronger coefficient-sum inequality. -/
theorem onePad_confidence_bounds {α : Type} [DecidableEq α] (s : System (Option α))
    (ext : FiniteAbsorptionLaw) (hh : s.Haltable onePad)
    (N : ℕ) (eps δ : ℝ) (hN : 4 ≤ N) (heps : 0 < eps) (hepsHalf : eps ≤ 1 / 2)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hconf : 1 - δ ≤ s.attachmentWindow onePad
      (FiniteChain.lowerEndpoint N eps) (FiniteChain.upperEndpoint N eps)) :
    confidenceScale N δ / 36 ≤ (s.cost : ℝ) ∧
    confidenceEntropy N δ / 36 ≤ (s.cost : ℝ) * Real.log 2 := by
  obtain ⟨hd, hl⟩ := s.confidence_polynomial_bounds onePad ext hh N eps δ
    hN heps hepsHalf hδ hδ2 hconf
  obtain ⟨hdeg, hcoeff⟩ := s.onePad_coefficient_bounds
  refine ⟨hd.trans (by exact_mod_cast hdeg), hl.trans ?_⟩
  have hpos := (s.absorptionCounts onePad).B_real_pos (s.absorptionCounts_haltable onePad hh) 1
    (by norm_num)
  have hcoeff' : evalReal 1 (s.absorptionCounts onePad).B ≤ (2 : ℝ) ^ s.cost := by
    rw [evalReal_one]
    exact_mod_cast hcoeff
  simpa only [Real.log_pow] using Real.log_le_log hpos hcoeff'

end LinearAssemblies.System
