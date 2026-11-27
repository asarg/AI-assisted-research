import LinearAssemblies.TwoPad.Certificate

set_option autoImplicit false

namespace LinearAssemblies.TwoPad

variable {b : ℕ} (d : DigitData b)

theorem unique_terminal (hb : 2 ≤ b) (x : State d) :
    (presentation d).degree twoPad x = 0 ↔ x = terminal d := by
  rcases x with j | (i | j)
  · simp [degree_path, terminal]
  · rw [degree_digit d hb]
    simp only [terminal, Sum.inr.injEq, Sum.inl.injEq, Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega
  · simp [degree_delay, terminal]

theorem cost_log_bound (hb : 2 ≤ b) :
    ((presentation d).system.cost : ℝ) ≤
      3 * (b : ℝ) + 2 * Real.log d.value / Real.log b + 1 := by
  rw [tile_cost]
  have hf : (d.first : ℝ) ≤ b := by exact_mod_cast d.first_le
  have hd : ((b - 2 : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b 2
  have hc := d.count_log_bound hb
  push_cast
  rw [mul_div_assoc]
  linarith

/-- A concrete two-pad tile system for every positive attachment target and every base >=2. -/
theorem exact_construction (ext : Probability.FiniteAbsorptionLaw) (b M : ℕ)
    (hb : 2 ≤ b) (hM : 1 ≤ M) :
    ∃ d : DigitData b, d.value = M ∧
      (presentation d).system.Haltable twoPad ∧
      (presentation d).system.expectedLength twoPad = (M : ℝ) + 1 ∧
      ((presentation d).system.cost : ℝ) ≤
        3 * (b : ℝ) + 2 * Real.log M / Real.log b + 1 ∧
      ∀ x, ((presentation d).system.toGraph twoPad).expected x ≤ (M : ℝ) + (b - 2 : ℕ) := by
  obtain ⟨d, hv⟩ := DigitData.represents b M hb hM
  refine ⟨d, hv, (presentation d).system_haltable twoPad (certificate d hb), ?_, ?_, ?_⟩
  · simpa only [hv] using expectedLength d ext hb
  · simpa only [hv] using cost_log_bound d hb
  · have h := (presentation d).system_remaining_bound twoPad ext (certificate d hb)
      ((d.value : ℝ) + (b - 2 : ℕ)) (potential_bound d)
    simpa only [hv] using h

/-- Lemma 6's remaining-time premise for bases whose delay budget is at most M. -/
theorem block_remaining_bound (ext : Probability.FiniteAbsorptionLaw) (hb : 2 ≤ b)
    (hbudget : b - 2 ≤ d.value) :
    ∀ x, ((presentation d).system.toGraph twoPad).expected x ≤ 2 * (d.value : ℝ) := by
  have h := (presentation d).system_remaining_bound twoPad ext (certificate d hb)
    ((d.value : ℝ) + (b - 2 : ℕ)) (potential_bound d)
  have hb' : ((b - 2 : ℕ) : ℝ) ≤ d.value := by exact_mod_cast hbudget
  intro x
  have hx := h x
  linarith

/-- The same concrete entries are a flexible-glue system at exactly the same cost. -/
theorem flexible_mean (ext : Probability.FiniteAbsorptionLaw) (hb : 2 ≤ b) :
    (presentation d).system.expectedLength
      (twoPadFlexibleRule (FirstLabel d) (SecondLabel d)).binds = (d.value : ℝ) + 1 :=
  expectedLength d ext hb

end LinearAssemblies.TwoPad
