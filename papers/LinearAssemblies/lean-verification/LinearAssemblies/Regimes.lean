import LinearAssemblies.Analysis.RegimeParameters

set_option autoImplicit false

namespace LinearAssemblies

open Filter Probability Concentration

attribute [local instance] OnePadBlock.decLabel TwoPadBlock.decFirst TwoPadBlock.decSecond

/-- A lower bound for every feasible one-pad system, together with a matching witness upper bound.
This directly bounds the attained minimum tile complexity. -/
def OnePadBounds (N : ℕ) (ε δ lo hi : ℝ) : Prop :=
  (∀ (A : Type) (dec : DecidableEq A), letI := dec
    ∀ s : System (Option A), s.Concentrated onePad N ε δ → lo ≤ (s.cost : ℝ)) ∧
  ∃ b : OnePadBlock, b.block.p.system.Concentrated onePad N ε δ ∧ (b.block.cost : ℝ) ≤ hi

/-- A lower bound valid for every compatibility rule, and a two-pad/flexible witness.
Consequently both richer-model minimum complexities lie in the stated interval. -/
def GeneralBounds (N : ℕ) (ε δ lo hi : ℝ) : Prop :=
  (∀ (I : Type) (dec : DecidableEq I) (compat : I → I → Prop) (dr : DecidableRel compat),
    letI := dec; letI := dr
    ∀ s : System I, s.Concentrated compat N ε δ → lo ≤ (s.cost : ℝ)) ∧
  ∃ b : TwoPadBlock, b.block.p.system.Concentrated twoPad N ε δ ∧
    b.block.p.system.Concentrated (twoPadFlexibleRule b.First b.Second).binds N ε δ ∧
    (b.block.cost : ℝ) ≤ hi

theorem OnePadBounds.mono {N : ℕ} {ε δ lo hi lo' hi' : ℝ}
    (h : OnePadBounds N ε δ lo hi) (hl : lo' ≤ lo) (hu : hi ≤ hi') :
    OnePadBounds N ε δ lo' hi' := by
  refine ⟨fun A dec s hs => hl.trans (h.1 A dec s hs), ?_⟩
  obtain ⟨b, hb, hc⟩ := h.2
  exact ⟨b, hb, hc.trans hu⟩

theorem GeneralBounds.mono {N : ℕ} {ε δ lo hi lo' hi' : ℝ}
    (h : GeneralBounds N ε δ lo hi) (hl : lo' ≤ lo) (hu : hi ≤ hi') :
    GeneralBounds N ε δ lo' hi' := by
  refine ⟨fun I dec compat dr s hs => hl.trans (h.1 I dec compat dr s hs), ?_⟩
  obtain ⟨b, hb, hf, hc⟩ := h.2
  exact ⟨b, hb, hf, hc.trans hu⟩

theorem moderate_bounds (ext : FiniteAbsorptionLaw) (sub : SubexponentialEquivalence) (bern : BernsteinLaw) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (ε δ : ℝ), 4 ≤ N → 0 < ε → ε ≤ 1 / 2 →
      0 < δ → δ ≤ 1 / 2 →
      ModerateParameters N (budgetR N ε δ) (confidenceScale N δ) →
      OnePadBounds N ε δ (confidenceScale N δ * Real.log N / 72)
        (C * budgetR N ε δ * Real.log N) ∧
      GeneralBounds N ε δ (confidenceScale N δ * Real.log N / (576 * Real.log (Real.log N)))
        (C * budgetR N ε δ * Real.log N / Real.log (Real.log N)) := by
  classical
  obtain ⟨C1, hC1, hu1⟩ := onePad_concentrated_upper ext sub bern
  obtain ⟨C2, hC2, hu2⟩ := twoPad_concentrated_upper ext sub bern
  refine ⟨2 * C1 + 4 * C2, by positivity, ?_⟩
  intro N ε δ hN hε hε1 hδ hδ1 hm
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hS : 0 < confidenceScale N δ := by linarith [hm.s_positive]
  have hlog : 0 < Real.log N := by linarith [hm.log_size]
  have hll : 0 < Real.log (Real.log N) := Real.log_pos (by linarith [hm.log_size])
  have hG : confidenceScale N δ * Real.log N / 2 ≤ confidenceEntropy N δ := by
    have h := mul_le_mul_of_nonneg_left (log_quotient_lower hNp hS hm.s_square) hS.le
    unfold confidenceEntropy
    linarith
  constructor
  · constructor
    · intro A dec s hs
      letI := dec
      have hw := System.Concentrated.window s onePad ext N hN ε δ hε hε1 hs
      have hb := s.onePad_concentration_lower_bound ext hs.1 N ε δ (by omega) hε hε1 hδ hδ1 hw
      have hl := le_max_left (confidenceEntropy N δ) (min (N : ℝ) ε⁻¹)
      linarith
    · obtain ⟨b, hb, hc⟩ := hu1 N ε δ (by omega) hε hε1 hδ hδ1
      refine ⟨b, hb, hc.trans ?_⟩
      have hq := log_quotient_upper hm.size (by linarith [hm.log_size] : 1 ≤ Real.log N) hm.r_positive
      have hr : (0 : ℝ) ≤ budgetR N ε δ := Nat.cast_nonneg _
      have h := mul_le_mul_of_nonneg_left hq (show 0 ≤ C1 * budgetR N ε δ by positivity)
      nlinarith [mul_nonneg (show 0 ≤ C2 * budgetR N ε δ by positivity) hlog.le]
  · constructor
    · intro I dec compat dr s hs
      letI := dec
      letI := dr
      have hw := System.Concentrated.window s compat ext N hN ε δ hε hε1 hs
      have hb := s.general_concentration_lower_bound compat ext hs.1 N ε δ (by omega) hε hε1 hδ hδ1 hw
      have hl := (le_max_left (confidenceEntropy N δ / Real.log (2 + confidenceEntropy N δ))
        (min (N : ℝ) ε⁻¹)).trans (le_max_right (confidenceScale N δ) _)
      have hratio := entropy_ratio_lower hm.size hm.log_size hm.s_positive hm.s_square hm.s_log
      change confidenceScale N δ * Real.log N / (8 * Real.log (Real.log N)) ≤
        confidenceEntropy N δ / Real.log (2 + confidenceEntropy N δ) at hratio
      have h := div_le_div_of_nonneg_right (hratio.trans hl) (by norm_num : (0 : ℝ) ≤ 72)
      have he : (confidenceScale N δ * Real.log N / (8 * Real.log (Real.log N))) / 72 =
          confidenceScale N δ * Real.log N / (576 * Real.log (Real.log N)) := by ring
      rw [he] at h
      exact h.trans hb
    · obtain ⟨b, hb, hf, hc⟩ := hu2 N ε δ (by omega) hε hε1 hδ hδ1
      refine ⟨b, hb, hf, hc.trans ?_⟩
      have hp := phi_quotient_upper hm.size hm.log_size hm.r_positive hm.r_square
      have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ C2 * budgetR N ε δ by positivity)
      have hbase : C2 * budgetR N ε δ * (4 * Real.log N / Real.log (Real.log N)) ≤
          (2 * C1 + 4 * C2) * budgetR N ε δ * Real.log N / Real.log (Real.log N) := by
        apply (le_div_iff₀ hll).2
        field_simp
        nlinarith [mul_nonneg (show 0 ≤ C1 * budgetR N ε δ by positivity) hlog.le]
      exact h.trans hbase

/-- Corollary 10, fixed failure probability: both optimal costs have matching
positive-constant upper and lower bounds for all sufficiently large N. -/
theorem fixed_confidence_regimes (ext : FiniteAbsorptionLaw)
    (sub : SubexponentialEquivalence) (bern : BernsteinLaw)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ l1 l2 u : ℝ, 0 < l1 ∧ 0 < l2 ∧ 0 < u ∧
      ∀ᶠ N : ℕ in atTop,
        OnePadBounds N ε δ (l1 * Real.log N) (u * Real.log N) ∧
        GeneralBounds N ε δ (l2 * (Real.log N / Real.log (Real.log N)))
          (u * (Real.log N / Real.log (Real.log N))) := by
  obtain ⟨C, hC, hmain⟩ := moderate_bounds ext sub bern
  have hS : 0 < Real.log δ⁻¹ := by linarith [log_inverse_lower hδ hδ1]
  have hQ : (0 : ℝ) < quota ε δ := by exact_mod_cast (show 0 < quota ε δ by have h := quota_positive hε hδ hδ1; omega)
  refine ⟨Real.log δ⁻¹ / 72, Real.log δ⁻¹ / 576, C * quota ε δ,
    by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [fixed_parameters hε hδ hδ1] with N hn
  obtain ⟨hN, hm, hR, hscale⟩ := hn
  have hb := hmain N ε δ hN hε hε1 hδ hδ1 hm
  have hlog : 0 < Real.log N := by linarith [hm.log_size]
  have hll : 0 < Real.log (Real.log N) := Real.log_pos (by linarith [hm.log_size])
  have hupper := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR hC.le) hlog.le
  constructor
  · apply hb.1.mono
    · rw [hscale]
      exact le_of_eq (by ring)
    · convert hupper using 1
  · apply hb.2.mono
    · rw [hscale]
      exact le_of_eq (by ring)
    · have h := div_le_div_of_nonneg_right hupper hll.le
      convert h using 1; ring

/-- Corollary 10, polynomial failure probability: Theta(log^2 N) for one pad,
and Theta(log^2 N / log log N) for two pads and flexible glues. -/
theorem polynomial_confidence_regimes (ext : FiniteAbsorptionLaw)
    (sub : SubexponentialEquivalence) (bern : BernsteinLaw)
    (ε c : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hc : 0 < c) :
    ∃ l1 l2 u : ℝ, 0 < l1 ∧ 0 < l2 ∧ 0 < u ∧
      ∀ᶠ N : ℕ in atTop,
        OnePadBounds N ε ((N : ℝ) ^ (-c)) (l1 * (Real.log N) ^ 2) (u * (Real.log N) ^ 2) ∧
        GeneralBounds N ε ((N : ℝ) ^ (-c)) (l2 * ((Real.log N) ^ 2 / Real.log (Real.log N)))
          (u * ((Real.log N) ^ 2 / Real.log (Real.log N))) := by
  obtain ⟨C, hC, hmain⟩ := moderate_bounds ext sub bern
  let D := (1 + c) / ε ^ 2 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨c / 72, c / 576, C * D, by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [polynomial_parameters hε hc] with N hn
  obtain ⟨hN, hδ, hδ1, hm, hR, hscale⟩ := hn
  have hb := hmain N ε ((N : ℝ) ^ (-c)) hN hε hε1 hδ hδ1 hm
  have hlog : 0 < Real.log N := by linarith [hm.log_size]
  have hll : 0 < Real.log (Real.log N) := Real.log_pos (by linarith [hm.log_size])
  have hupper := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR hC.le) hlog.le
  constructor
  · apply hb.1.mono
    · rw [hscale]
      exact le_of_eq (by ring)
    · convert hupper using 1; dsimp [D]; ring
  · apply hb.2.mono
    · rw [hscale]
      exact le_of_eq (by ring)
    · have h := div_le_div_of_nonneg_right hupper hll.le
      convert h using 1; dsimp [D]; ring

end LinearAssemblies
