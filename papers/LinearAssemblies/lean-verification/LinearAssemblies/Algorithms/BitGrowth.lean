import LinearAssemblies.Algorithms.Approximation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace LinearAssemblies.OnePad.Algorithms

open Filter LinearAssemblies.Algorithms

theorem size_log_bound (n : ℕ) (hn : 1 ≤ n) :
    (n.size : ℝ) ≤ 2 * Real.log n + 1 := by
  have hs : 1 ≤ n.size := Nat.size_pos.2 (by omega)
  have hp : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.1 (by omega)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (n.size - 1))
    (show (2 : ℝ) ^ (n.size - 1) ≤ n by exact_mod_cast hp)
  rw [Real.log_pow, Nat.cast_sub hs, Nat.cast_one] at hlog
  have hsn : (1 : ℝ) ≤ n.size := by exact_mod_cast hs
  nlinarith [Probability.log_two_bounds.1]

theorem size_tendsto : Tendsto Nat.size atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (2 ^ k)] with n hn
  exact (Nat.lt_size.2 hn).le

theorem eventually_log_power (K : ℝ) (hK : 0 < K) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * (Real.log n) ^ d ≤ n := by
  have hh := (Real.isLittleO_pow_log_id_atTop (n := d)).bound (show 0 < 1 / K by positivity)
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually hh
  filter_upwards [hn, eventually_ge_atTop (1 : ℕ)] with n hn hsize
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hsize)
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hl d), id_eq,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at hn
  have hm := mul_le_mul_of_nonneg_left hn hK.le
  have he : K * (1 / K * (n : ℝ)) = n := by field_simp
  simpa only [he] using hm

/-- Any fixed polynomial in the bit length of B is eventually at most B. -/
theorem eventually_polynomial_size (C d : ℕ) :
    ∀ᶠ B : ℕ in atTop, C * (B.size + 9) ^ d ≤ B := by
  have hl : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_log_power (((C : ℝ) + 1) * 12 ^ d) (by positivity) d,
    hl, eventually_ge_atTop (1 : ℕ)] with B hlarge hlog hB
  have hs := size_log_bound B hB
  have hsz : (B.size : ℝ) + 9 ≤ 12 * Real.log B := by linarith
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ B.size + 9) hsz d
  rw [mul_pow] at hp
  have hc := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) C)
  have hnon : 0 ≤ 12 ^ d * (Real.log (B : ℝ)) ^ d := by positivity
  have hout : (C : ℝ) * ((B.size : ℝ) + 9) ^ d ≤ B := by nlinarith
  exact_mod_cast hout

theorem approximation_small (l : Logarithm) (hl : l.Polynomial) :
    ∀ᶠ B : ℕ in atTop, approximationCost l B ≤ B := by
  obtain ⟨C, d, hd⟩ := approximation_polynomial l hl
  filter_upwards [eventually_polynomial_size C d] with B hB
  exact (hd B).trans hB

theorem target_size_bound (M : ℕ) : (2 * M + 3).size ≤ M.size + 3 := by
  apply Nat.size_le.2
  have h := Nat.lt_size_self M
  rw [pow_add]
  norm_num
  omega

theorem target_size_tendsto : Tendsto (fun M : ℕ => (2 * M + 3).size) atTop atTop := by
  apply size_tendsto.comp
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop k] with M hM
  omega

end LinearAssemblies.OnePad.Algorithms
