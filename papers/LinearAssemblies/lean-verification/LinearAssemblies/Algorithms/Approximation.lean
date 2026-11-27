import LinearAssemblies.Algorithms.Arithmetic
import LinearAssemblies.Algorithms.Candidates
import LinearAssemblies.LowerBounds

set_option autoImplicit false

namespace LinearAssemblies.OnePad.Algorithms

open LinearAssemblies.Algorithms

def precision (B : ℕ) : ℕ := B.size + 8

def approximateBeta (l : Logarithm) (B : ℕ) : ℚ :=
  (l.run 2 (precision B) : ℚ) / l.run 3 (precision B)

/-- Cost of the two fixed-point calls, rational quotient encoding, and locating
the center. Schoolbook multiplication/division on O(log B)-bit integers is
covered by the cubic charge. The large threshold Y is not used here. -/
def approximationCost (l : Logarithm) (B : ℕ) : ℕ :=
  l.steps 2 (precision B) + l.steps 3 (precision B) + 128 * (B.size + precision B + 8) ^ 3

theorem precision_error (B : ℕ) (hB : 1 ≤ B) :
    (2 : ℝ)⁻¹ ^ precision B ≤ 1 / (256 * B) := by
  have hpow : (B : ℝ) ≤ (2 : ℝ) ^ B.size := by exact_mod_cast (Nat.lt_size_self B).le
  have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  rw [precision, inv_pow, pow_add]
  rw [show (2 : ℝ) ^ 8 = 256 by norm_num, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem approximateBeta_correct (l : Logarithm) (hl : l.Polynomial)
    (B : ℕ) (hB : 1 ≤ B) :
    |(approximateBeta l B : ℝ) - beta| ≤ 1 / (4 * B) := by
  let p := precision B
  let f := (l.run 2 p : ℝ) / (2 : ℝ) ^ p
  let g := (l.run 3 p : ℝ) / (2 : ℝ) ^ p
  let e := 1 / (256 * (B : ℝ))
  have hb : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hep : 0 < e := by dsimp [e]; positivity
  have he : e ≤ 1 / 256 := by
    dsimp [e]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hf : |f - Real.log 2| ≤ e := (hl.accurate 2 p (by omega)).trans (precision_error B hB)
  have hg : |g - Real.log 3| ≤ e := (hl.accurate 3 p (by omega)).trans (precision_error B hB)
  have hl2 := Probability.log_two_bounds
  have hl3 : (1 : ℝ) / 2 ≤ Real.log 3 ∧ Real.log 3 ≤ 2 := by
    constructor
    · exact hl2.1.trans (Real.log_le_log (by norm_num) (by norm_num))
    · exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans (by norm_num)
  have hgpos : 0 < g := by linarith [(abs_le.mp hg).1]
  have hgp : (1 : ℝ) / 4 ≤ g := by linarith [(abs_le.mp hg).1]
  have h3p : 0 < Real.log 3 := by linarith
  have hd : (1 : ℝ) / 8 ≤ g * Real.log 3 := by nlinarith
  have herr : |f * Real.log 3 - Real.log 2 * g| ≤ 3 * e := by
    have heq : f * Real.log 3 - Real.log 2 * g =
        (f - Real.log 2) * Real.log 3 + Real.log 2 * (Real.log 3 - g) := by ring
    rw [heq]
    calc
      _ ≤ |(f - Real.log 2) * Real.log 3| + |Real.log 2 * (Real.log 3 - g)| := abs_add _ _
      _ = |f - Real.log 2| * Real.log 3 + Real.log 2 * |g - Real.log 3| := by
        rw [abs_mul, abs_mul, abs_of_pos h3p, abs_of_nonneg (by linarith : 0 ≤ Real.log 2), abs_sub_comm g]
      _ ≤ e * Real.log 3 + Real.log 2 * e := by gcongr
      _ ≤ 3 * e := by nlinarith
  have hbound : |f / g - Real.log 2 / Real.log 3| ≤ 24 * e := by
    rw [div_sub_div _ _ hgpos.ne' h3p.ne', abs_div, abs_of_pos (mul_pos hgpos h3p)]
    apply (div_le_iff₀ (mul_pos hgpos h3p)).2
    rw [mul_comm g (Real.log 2)]
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 24 * e by positivity)
    nlinarith
  have heq : (approximateBeta l B : ℝ) = f / g := by
    dsimp [approximateBeta, f, g, p]
    push_cast
    field_simp
  rw [heq]
  apply hbound.trans
  dsimp [e]
  have hbp : (0 : ℝ) < B := by linarith
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 256 * B) (by positivity : (0 : ℝ) < 4 * B)).2
  nlinarith

/-- The fixed-point outputs really have O(p) bits, so the polynomial charge
does not conceal integers with exponentially many bits. -/
theorem approximation_output_size (l : Logarithm) (hl : l.Polynomial)
    (x p : ℕ) (hx : 2 ≤ x ∧ x ≤ 3) : (l.run x p).size ≤ p + 2 := by
  have ha := (abs_le.mp (hl.accurate x p hx.1)).2
  have hxlog : Real.log (x : ℝ) ≤ 2 := by
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hh := Real.log_le_sub_one_of_pos hxpos
    have hx3 : (x : ℝ) ≤ 3 := by exact_mod_cast hx.2
    linarith
  have he : (2 : ℝ)⁻¹ ^ p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr : (l.run x p : ℝ) ≤ 3 * (2 : ℝ) ^ p := by
    have hh : (l.run x p : ℝ) / (2 : ℝ) ^ p ≤ 3 := by linarith
    exact (div_le_iff₀ (by positivity)).1 hh
  have hn : l.run x p ≤ 3 * 2 ^ p := by exact_mod_cast hr
  apply Nat.size_le.2
  rw [pow_add]
  norm_num
  have hp : 0 < 2 ^ p := by positivity
  omega

theorem approximation_polynomial (l : Logarithm) (hl : l.Polynomial) :
    ∃ C d : ℕ, ∀ B : ℕ, approximationCost l B ≤ C * (B.size + 9) ^ d := by
  obtain ⟨C2, d2, h2⟩ := hl.bound 2 (by omega)
  obtain ⟨C3, d3, h3⟩ := hl.bound 3 (by omega)
  let d := max 3 (max d2 d3)
  refine ⟨C2 + C3 + 1024, d, ?_⟩
  intro B
  have hb : 1 ≤ B.size + 9 := by omega
  have h2' := (h2 (precision B)).trans (Nat.mul_le_mul_left C2 (Nat.pow_le_pow_right hb (show d2 ≤ d by dsimp [d]; omega)))
  have h3' := (h3 (precision B)).trans (Nat.mul_le_mul_left C3 (Nat.pow_le_pow_right hb (show d3 ≤ d by dsimp [d]; omega)))
  have he : B.size + precision B + 8 ≤ 2 * (B.size + 9) := by dsimp [precision]; omega
  have hcube := Nat.pow_le_pow_left he 3
  have hpow : (B.size + 9) ^ 3 ≤ (B.size + 9) ^ d := Nat.pow_le_pow_right hb (by dsimp [d]; omega)
  dsimp [approximationCost]
  have hc : 128 * (B.size + precision B + 8) ^ 3 ≤ 1024 * (B.size + 9) ^ d := by
    rw [mul_pow] at hcube
    norm_num at hcube
    omega
  exact (Nat.add_le_add (Nat.add_le_add h2' h3') hc).trans_eq (by ring)

end LinearAssemblies.OnePad.Algorithms
