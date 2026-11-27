import LinearAssemblies.Analysis.RegimeBounds
import LinearAssemblies.PadEmbedding

set_option autoImplicit false

namespace LinearAssemblies

open Filter Probability Concentration

/-- Sufficient numerical conditions for the fixed-regime comparisons. -/
structure ModerateParameters (N R S : ℝ) : Prop where
  size : 1 ≤ N
  log_size : 4 ≤ Real.log N
  r_positive : 1 ≤ R
  s_positive : 1 / 2 ≤ S
  r_square : R ^ 2 ≤ N
  s_square : S ^ 2 ≤ N
  s_log : S ≤ (Real.log N) ^ 2 / 2

theorem eventually_log_large (L : ℝ) : ∀ᶠ n : ℕ in atTop, L ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop L

theorem eventually_log_squared (K : ℝ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, K * (Real.log n) ^ 2 ≤ n := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show 0 < 1 / K by positivity)
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually h
  filter_upwards [hn] with n hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))), id_eq,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at hn
  have hm := mul_le_mul_of_nonneg_left hn hK.le
  have he : K * (1 / K * (n : ℝ)) = n := by field_simp
  simpa only [he] using hm

theorem log_inverse_lower {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (1 : ℝ) / 2 ≤ Real.log δ⁻¹ := by
  have hi : (2 : ℝ) ≤ δ⁻¹ := by
    have h : 2 ≤ 1 / δ := (le_div_iff₀ hδ).2 (by linarith)
    simpa only [one_div] using h
  exact log_two_bounds.1.trans (Real.log_le_log (by norm_num) hi)

theorem fixed_parameters {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧
      ModerateParameters N (budgetR N ε δ) (confidenceScale N δ) ∧
      (budgetR N ε δ : ℝ) ≤ quota ε δ ∧ confidenceScale N δ = Real.log δ⁻¹ := by
  let S := Real.log δ⁻¹
  let Q := (quota ε δ : ℝ)
  have hs := log_inverse_lower hδ hδ1
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ), eventually_log_large 4,
    eventually_log_large (2 * S), ht.eventually_ge_atTop S,
    ht.eventually_ge_atTop (S ^ 2), ht.eventually_ge_atTop (Q ^ 2)] with N hN hl hls hns hss hqq
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hscale : confidenceScale N δ = S := min_eq_right hns
  have hr : (1 : ℝ) ≤ budgetR N ε δ := by exact_mod_cast budget_positive (by omega) hε hδ hδ1
  have hrq : (budgetR N ε δ : ℝ) ≤ Q := by
    dsimp [budgetR, Q]
    exact_mod_cast (min_le_right N (quota ε δ))
  refine ⟨hN, ?_, hrq, hscale⟩
  rw [hscale]
  refine ⟨hN1, hl, hr, hs, ?_, hss, ?_⟩
  · nlinarith
  · dsimp [S] at *
    nlinarith [sq_nonneg (Real.log N - 1)]

theorem polynomial_delta_log {N c : ℝ} (hN : 0 < N) :
    Real.log (N ^ (-c))⁻¹ = c * Real.log N := by
  rw [Real.log_inv, Real.log_rpow hN]
  ring

theorem polynomial_delta_small {N c : ℝ} (hN : 0 < N) (hc : 0 < c)
    (hl : 1 / c ≤ Real.log N) : 0 < N ^ (-c) ∧ N ^ (-c) ≤ 1 / 2 := by
  refine ⟨Real.rpow_pos_of_pos hN _, ?_⟩
  have hmul : 1 ≤ c * Real.log N := by
    have h := (div_le_iff₀ hc).1 hl
    linarith
  rw [Real.rpow_def_of_pos hN]
  calc
    _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith [log_two_bounds.2])
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

theorem polynomial_quota_bound {N ε c : ℝ} (hN : 0 < N) (hε : 0 < ε) (hc : 0 < c)
    (hl : 1 ≤ Real.log N) :
    (quota ε (N ^ (-c)) : ℝ) ≤ ((1 + c) / ε ^ 2 + 1) * Real.log N := by
  have hd := Real.rpow_pos_of_pos hN (-c)
  have he : Real.log (2 / N ^ (-c)) = Real.log 2 + c * Real.log N := by
    rw [Real.log_div (by norm_num) hd.ne', Real.log_rpow hN]
    ring
  have harg : 0 ≤ Real.log (2 / N ^ (-c)) / ε ^ 2 := by rw [he]; positivity
  have hceil := (Nat.ceil_lt_add_one harg).le
  change (quota ε (N ^ (-c)) : ℝ) ≤ _ at hceil
  rw [he] at hceil
  have hnum : Real.log 2 + c * Real.log N ≤ (1 + c) * Real.log N := by
    linarith [log_two_bounds.2]
  have hdiv := div_le_div_of_nonneg_right hnum (sq_nonneg ε)
  have heq : (1 + c) * Real.log N / ε ^ 2 = ((1 + c) / ε ^ 2) * Real.log N := by ring
  rw [heq] at hdiv
  nlinarith

theorem polynomial_parameters {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ 0 < (N : ℝ) ^ (-c) ∧ (N : ℝ) ^ (-c) ≤ 1 / 2 ∧
      ModerateParameters N (budgetR N ε ((N : ℝ) ^ (-c))) (confidenceScale N ((N : ℝ) ^ (-c))) ∧
      (budgetR N ε ((N : ℝ) ^ (-c)) : ℝ) ≤ ((1 + c) / ε ^ 2 + 1) * Real.log N ∧
      confidenceScale N ((N : ℝ) ^ (-c)) = c * Real.log N := by
  let D := (1 + c) / ε ^ 2 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  filter_upwards [eventually_ge_atTop (4 : ℕ), eventually_log_large 4,
    eventually_log_large (2 * c), eventually_log_large (1 / c),
    eventually_log_squared (c ^ 2) (sq_pos_of_pos hc),
    eventually_log_squared (D ^ 2) (sq_pos_of_pos hD)] with N hN hl hlc hli hcs hds
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hd := polynomial_delta_small hNp hc hli
  have hs0 : (1 : ℝ) / 2 ≤ c * Real.log N := by
    have h := (div_le_iff₀ hc).1 hli
    linarith
  have hsN : c * Real.log N ≤ N := by nlinarith [sq_nonneg (c * Real.log N - 1)]
  have hs : confidenceScale N ((N : ℝ) ^ (-c)) = c * Real.log N := by
    unfold confidenceScale
    rw [polynomial_delta_log hNp, min_eq_right hsN]
  have hr1 : (1 : ℝ) ≤ budgetR N ε ((N : ℝ) ^ (-c)) := by
    exact_mod_cast budget_positive (by omega) hε hd.1 hd.2
  have hrD : (budgetR N ε ((N : ℝ) ^ (-c)) : ℝ) ≤ D * Real.log N := by
    have hrq : (budgetR N ε ((N : ℝ) ^ (-c)) : ℝ) ≤ quota ε ((N : ℝ) ^ (-c)) := by
      exact_mod_cast min_le_right N (quota ε ((N : ℝ) ^ (-c)))
    exact hrq.trans (polynomial_quota_bound hNp hε hc (by linarith))
  refine ⟨hN, hd.1, hd.2, ?_, hrD, hs⟩
  rw [hs]
  refine ⟨hN1, hl, hr1, hs0, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

end LinearAssemblies
