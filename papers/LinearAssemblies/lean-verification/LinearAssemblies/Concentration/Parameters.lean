import LinearAssemblies.Concentration.Blocks

set_option autoImplicit false

namespace LinearAssemblies.Concentration

noncomputable def quota (ε δ : ℝ) : ℕ := ⌈Real.log (2 / δ) / ε ^ 2⌉₊
noncomputable def budgetR (N : ℕ) (ε δ : ℝ) : ℕ := min N (quota ε δ)

theorem quota_positive {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    1 ≤ quota ε δ := by
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos ((one_lt_div hδ).2 (by linarith))
  exact Nat.ceil_pos.mpr (div_pos hlog (sq_pos_of_pos hε))

theorem quota_bound (ε δ : ℝ) (hε : 0 < ε) :
    Real.log (2 / δ) ≤ ε ^ 2 * (quota ε δ : ℝ) := by
  have h := Nat.le_ceil (Real.log (2 / δ) / ε ^ 2)
  exact (div_le_iff₀ (sq_pos_of_pos hε)).1 h |>.trans_eq (mul_comm _ _)

theorem budget_positive {N : ℕ} {ε δ : ℝ} (hN : 1 ≤ N)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) : 1 ≤ budgetR N ε δ :=
  le_min hN (quota_positive hε hδ hδ1)

theorem budget_le (N : ℕ) (ε δ : ℝ) : budgetR N ε δ ≤ N := min_le_left _ _

theorem budget_eq_quota {N A : ℕ} {ε δ : ℝ} (hA : 1 ≤ A)
    (hr : A * budgetR N ε δ ≤ N - 1) (hN : 1 ≤ N) : budgetR N ε δ = quota ε δ := by
  have hR : budgetR N ε δ ≤ A * budgetR N ε δ := by nlinarith
  unfold budgetR at *
  omega

theorem choose_multiplier {a : ℝ} (ha : 0 < a) :
    ∃ A : ℕ, 1 ≤ A ∧ 2 ≤ a * (A : ℝ) := by
  refine ⟨max 1 ⌈2 / a⌉₊, le_max_left _ _, ?_⟩
  have h1 : 2 / a ≤ (⌈2 / a⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈2 / a⌉₊ : ℝ) ≤ (max 1 ⌈2 / a⌉₊ : ℕ) := by exact_mod_cast le_max_right 1 ⌈2 / a⌉₊
  have h := (div_le_iff₀ ha).1 (h1.trans h2)
  linarith

theorem scaled_confidence {a ε δ : ℝ} {A R : ℕ}
    (ha : 0 < a) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hA : 2 ≤ a * (A : ℝ)) (hR : R = quota ε δ) :
    2 * Real.exp (-a * (ε ^ 2 * (A * R : ℕ) / 2)) ≤ δ := by
  have hl : 0 < Real.log (2 / δ) := Real.log_pos ((one_lt_div hδ).2 (by linarith))
  have hq := quota_bound ε δ hε
  rw [← hR] at hq
  have hr : Real.log (2 / δ) ≤ a * (ε ^ 2 * (A * R : ℕ) / 2) := by
    push_cast
    have hh := mul_le_mul_of_nonneg_left hq (mul_nonneg ha.le (Nat.cast_nonneg A))
    nlinarith [mul_le_mul_of_nonneg_right hA hl.le]
  calc
    _ ≤ 2 * Real.exp (-Real.log (2 / δ)) :=
      by simpa only [neg_mul] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hr)) (by norm_num : (0 : ℝ) ≤ 2)
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 / δ)]
      field_simp

theorem bernstein_balanced_exponent {N r ε : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ 2 * r / 2 ≤ min ((ε * N) ^ 2 / (2 * N ^ 2 / r)) ((ε * N) / (2 * N / r)) := by
  have hfirst : (ε * N) ^ 2 / (2 * N ^ 2 / r) = ε ^ 2 * r / 2 := by
    field_simp
    ring
  have hsecond : (ε * N) / (2 * N / r) = ε * r / 2 := by
    field_simp
    ring
  rw [hfirst, hsecond]
  apply le_min le_rfl
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsq hr.le]

end LinearAssemblies.Concentration
