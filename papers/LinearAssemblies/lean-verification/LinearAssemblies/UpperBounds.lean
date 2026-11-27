import LinearAssemblies.Concentration.Semantics

set_option autoImplicit false

namespace LinearAssemblies

open Probability Concentration

attribute [local instance] OnePadBlock.decLabel TwoPadBlock.decFirst TwoPadBlock.decSecond

/-- Theorem 8, equation (24), with a uniform constant and the full concrete tile semantics. -/
theorem onePad_concentrated_upper (ext : FiniteAbsorptionLaw)
    (sub : SubexponentialEquivalence) (bern : BernsteinLaw) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (ε δ : ℝ), 2 ≤ N → 0 < ε → ε ≤ 1 / 2 →
      0 < δ → δ ≤ 1 / 2 → ∃ b : OnePadBlock,
      b.block.p.system.Concentrated onePad N ε δ ∧
      (b.block.cost : ℝ) ≤ C * budgetR N ε δ * Real.log (1 + (N : ℝ) / budgetR N ε δ) := by
  classical
  obtain ⟨a, ha, hconc⟩ := block_estimate sub bern
  obtain ⟨A, hA, hmult⟩ := choose_multiplier ha
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  refine ⟨4 + 144 * A, by positivity, ?_⟩
  intro N ε δ hN hε hε1 hδ hδ1
  let R := budgetR N ε δ
  have hR : 1 ≤ R := budget_positive (by omega) hε hδ hδ1
  have hRN : R ≤ N := budget_le N ε δ
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRNr : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : 1 ≤ N := by omega
  by_cases hr : A * R ≤ N - 1
  · have hrpos : 1 ≤ A * R := by nlinarith
    obtain ⟨b, hv, hc, hf⟩ := one_balanced ext ha hconc N (A * R) hN hrpos hr ε hε (by linarith)
    have he := scaled_confidence ha hε hδ hδ1 hmult (budget_eq_quota hA hr hNr1)
    refine ⟨b, b.block.concentrated ext N hNr1 ε δ hv (hf.trans he), ?_⟩
    apply hc.trans
    simpa only [Nat.cast_mul] using probabilistic_log_budget hAr hRr hRNr
  · obtain ⟨b, hv, hc, hm⟩ := deterministic_one (N - 1)
    have hf : deviation b.block.mass ((N - 1 : ℕ) : ℝ) (ε * N) = 0 := by
      rw [show b.block.mass = (fun n => if n = N - 1 then 1 else 0) by funext n; exact hm n]
      exact point_mass_deviation _ _ (mul_pos hε hNr)
    refine ⟨b, b.block.concentrated ext N hNr1 ε δ hv (hf.le.trans hδ.le), ?_⟩
    rw [hc, Nat.sub_add_cancel hNr1]
    apply deterministic_log_budget hAr hRr hRNr
    exact_mod_cast (show N ≤ A * R by omega)

/-- Theorem 8, equation (26): exact mean, prescribed confidence, and O(R Phi(N/R))
for actual two-pad entries. The identical rule is a flexible-glue implementation. -/
theorem twoPad_concentrated_upper (ext : FiniteAbsorptionLaw)
    (sub : SubexponentialEquivalence) (bern : BernsteinLaw) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (ε δ : ℝ), 2 ≤ N → 0 < ε → ε ≤ 1 / 2 →
      0 < δ → δ ≤ 1 / 2 → ∃ b : TwoPadBlock,
      b.block.p.system.Concentrated twoPad N ε δ ∧
      b.block.p.system.Concentrated (twoPadFlexibleRule b.First b.Second).binds N ε δ ∧
      (b.block.cost : ℝ) ≤ C * budgetR N ε δ * phi ((N : ℝ) / budgetR N ε δ) := by
  classical
  obtain ⟨a, ha, hconc⟩ := block_estimate sub bern
  obtain ⟨A, hA, hmult⟩ := choose_multiplier ha
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  refine ⟨4 + 144 * A, by positivity, ?_⟩
  intro N ε δ hN hε hε1 hδ hδ1
  let R := budgetR N ε δ
  have hR : 1 ≤ R := budget_positive (by omega) hε hδ hδ1
  have hRN : R ≤ N := budget_le N ε δ
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRNr : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : 1 ≤ N := by omega
  by_cases hr : A * R ≤ N - 1
  · have hrpos : 1 ≤ A * R := by nlinarith
    obtain ⟨b, hv, hc, hf⟩ := two_balanced ext ha hconc N (A * R) hN hrpos hr ε hε (by linarith)
    have he := scaled_confidence ha hε hδ hδ1 hmult (budget_eq_quota hA hr hNr1)
    have hgood := b.block.concentrated ext N hNr1 ε δ hv (hf.trans he)
    refine ⟨b, hgood, hgood, ?_⟩
    apply hc.trans
    simpa only [Nat.cast_mul] using probabilistic_phi_budget hAr hRr hRNr
  · obtain ⟨b, hv, hc, hm⟩ := deterministic_two (N - 1)
    have hf : deviation b.block.mass ((N - 1 : ℕ) : ℝ) (ε * N) = 0 := by
      rw [show b.block.mass = (fun n => if n = N - 1 then 1 else 0) by funext n; exact hm n]
      exact point_mass_deviation _ _ (mul_pos hε hNr)
    have hgood := b.block.concentrated ext N hNr1 ε δ hv (hf.le.trans hδ.le)
    refine ⟨b, hgood, hgood, ?_⟩
    rw [hc, Nat.sub_add_cancel hNr1]
    apply deterministic_phi_budget hAr hRr hRNr
    exact_mod_cast (show N ≤ A * R by omega)

end LinearAssemblies
