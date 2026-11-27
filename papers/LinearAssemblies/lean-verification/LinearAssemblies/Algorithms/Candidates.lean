import LinearAssemblies.Algorithms.Sequential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

namespace LinearAssemblies.OnePad.Algorithms

noncomputable def beta : ℝ := Real.log 2 / Real.log 3

theorem beta_bounds : (1 : ℝ) / 2 < beta ∧ beta < 3 / 4 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl : Real.log (3 : ℝ) < Real.log (2 ^ 2) := Real.log_lt_log (by norm_num) (by norm_num)
  have hu : Real.log ((2 : ℝ) ^ 4) < Real.log (3 ^ 3) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at hl
  rw [Real.log_pow, Real.log_pow] at hu
  dsimp [beta]
  constructor
  · apply (lt_div_iff₀ h3).2
    norm_num at hl
    linarith
  · apply (div_lt_iff₀ h3).2
    norm_num at hu
    linarith

/-- The approximation is used only to compute a small integer window. -/
def center (B : ℕ) (β : ℚ) : ℕ := ⌊(B - 1 : ℕ) * β⌋₊

theorem center_spec (B : ℕ) (hB : 1 ≤ B) (β : ℚ)
    (hβ : |(β : ℝ) - beta| ≤ 1 / (4 * B)) :
    (0 : ℝ) ≤ β ∧ (β : ℝ) ≤ 1 ∧
    (center B β : ℝ) ≤ (B - 1 : ℕ) * (β : ℝ) ∧
    (B - 1 : ℕ) * (β : ℝ) < center B β + 1 ∧ center B β ≤ B := by
  have hb : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hsmall : 1 / (4 * (B : ℝ)) ≤ 1 / 4 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    linarith
  have hh := (abs_le.mp hβ)
  have hlo : (0 : ℝ) ≤ β := by linarith [beta_bounds.1]
  have hhi : (β : ℝ) ≤ 1 := by linarith [beta_bounds.2]
  have hq : (0 : ℚ) ≤ β := by exact_mod_cast hlo
  have hfloor := Nat.floor_le (show (0 : ℚ) ≤ (B - 1 : ℕ) * β by positivity)
  have hlt := Nat.lt_floor_add_one ((B - 1 : ℕ) * β)
  have hf : (center B β : ℝ) ≤ (B - 1 : ℕ) * (β : ℝ) := by exact_mod_cast hfloor
  have ht : (B - 1 : ℕ) * (β : ℝ) < center B β + 1 := by exact_mod_cast hlt
  refine ⟨hlo, hhi, hf, ht, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg (α := ℝ) (B - 1))
  have hsub : ((B - 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast Nat.sub_le B 1
  exact_mod_cast (hf.trans (by simpa using hmul) |>.trans hsub)

theorem log_window (Y B : ℕ) (hY : 0 < Y) (hB : 1 ≤ B)
    (hlo : 2 ^ (B - 1) ≤ Y) (hhi : Y < 2 ^ B)
    (β : ℚ) (hβ : |(β : ℝ) - beta| ≤ 1 / (4 * B)) :
    |Real.log Y / Real.log 3 - (B - 1 : ℕ) * (β : ℝ)| < 1 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpY : (0 : ℝ) < Y := by exact_mod_cast hY
  have hl : Real.log ((2 : ℝ) ^ (B - 1)) ≤ Real.log Y :=
    Real.log_le_log (by positivity) (by exact_mod_cast hlo)
  have hu : Real.log (Y : ℝ) < Real.log ((2 : ℝ) ^ B) :=
    Real.log_lt_log hpY (by exact_mod_cast hhi)
  rw [Real.log_pow] at hl hu
  have hl' : (B - 1 : ℕ) * beta ≤ Real.log Y / Real.log 3 := by
    dsimp [beta]
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right h3).2 hl
  have hu' : Real.log Y / Real.log 3 < (B : ℝ) * beta := by
    dsimp [beta]
    rw [← mul_div_assoc]
    exact (div_lt_div_iff_of_pos_right h3).2 hu
  have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hsub : ((B - 1 : ℕ) : ℝ) = B - 1 := by rw [Nat.cast_sub hB]; norm_num
  have herr := mul_le_mul_of_nonneg_left hβ (show (0 : ℝ) ≤ (B - 1 : ℕ) by positivity)
  have hquarter : (B - 1 : ℕ) * (1 / (4 * (B : ℝ))) < 1 / 4 := by
    rw [hsub, mul_one_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * B)).2
    nlinarith
  rw [abs_sub_lt_iff]
  rw [hsub] at hl' herr
  have hab := abs_le.mp hβ
  have hneg := mul_le_mul_of_nonneg_left hab.1 (show (0 : ℝ) ≤ B - 1 by linarith)
  have hpos := mul_le_mul_of_nonneg_left hab.2 (show (0 : ℝ) ≤ B - 1 by linarith)
  rw [hsub] at hquarter ⊢
  constructor <;> nlinarith [beta_bounds.2]

theorem threshold_window (Y c B : ℕ) (hc : 0 < c) (hcLo : 9 ≤ c) (hcHi : c ≤ 81)
    (hY : 0 < Y) (hB : 1 ≤ B) (hlo : 2 ^ (B - 1) ≤ Y) (hhi : Y < 2 ^ B)
    (β : ℚ) (hβ : |(β : ℝ) - beta| ≤ 1 / (4 * B)) :
    center B β - 5 ≤ thresholdExponent c Y hc ∧
      thresholdExponent c Y hc ≤ center B β + 1 := by
  let a := center B β
  let q := thresholdExponent c Y hc
  have hs := center_spec B hB β hβ
  have hw := abs_lt.mp (log_window Y B hY hB hlo hhi β hβ)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hYp : (0 : ℝ) < Y := by exact_mod_cast hY
  have hcp : (0 : ℝ) < c := by exact_mod_cast hc
  have hcl : 2 * Real.log 3 ≤ Real.log c := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 2) (show (3 : ℝ) ^ 2 ≤ c by exact_mod_cast hcLo)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hcu : Real.log c ≤ 4 * Real.log 3 := by
    have hh := Real.log_le_log hcp (show (c : ℝ) ≤ 3 ^ 4 by exact_mod_cast hcHi)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hrange : (a : ℝ) - 1 < Real.log Y / Real.log 3 ∧
      Real.log Y / Real.log 3 < (a : ℝ) + 2 := by
    dsimp [a]
    constructor <;> linarith [hs.2.2.1, hs.2.2.2.1]
  constructor
  · have hspec : (Y : ℝ) ≤ c * (3 : ℝ) ^ q := by exact_mod_cast thresholdExponent_spec c Y hc
    have hlog := Real.log_le_log hYp hspec
    rw [Real.log_mul hcp.ne' (by positivity), Real.log_pow] at hlog
    have hlow := (lt_div_iff₀ h3).1 hrange.1
    have hae : (a : ℝ) < q + 5 := by nlinarith
    have han : a < q + 5 := by exact_mod_cast hae
    change a - 5 ≤ q
    omega
  · apply thresholdExponent_le
    have hhigh := (div_lt_iff₀ h3).1 hrange.2
    have hlog : Real.log Y ≤ Real.log ((c : ℝ) * 3 ^ (a + 1)) := by
      rw [Real.log_mul hcp.ne' (by positivity), Real.log_pow, Nat.cast_add, Nat.cast_one]
      nlinarith
    have hle := (Real.log_le_log_iff hYp (by positivity)).1 hlog
    exact_mod_cast hle

/-- At most seven consecutive nonnegative exponents; duplicate clipped
negative candidates from the paper are represented only once. -/
def candidates (a : ℕ) : List ℕ := List.range' (a - 5) (a + 2 - (a - 5))

theorem candidates_mem (a q : ℕ) : q ∈ candidates a ↔ a - 5 ≤ q ∧ q ≤ a + 1 := by
  simp only [candidates, List.mem_range'_1]
  have hh : a - 5 ≤ a + 2 := by omega
  omega

theorem candidates_length (a : ℕ) : (candidates a).length ≤ 7 := by
  simp only [candidates, List.length_range']
  omega

/-- Exact threshold selection. A fallback is never used under the window
theorem's hypotheses. Only natural arithmetic decides these comparisons. -/
def select (c Y : ℕ) (qs : List ℕ) (fallback : ℕ) : ℕ :=
  qs.foldr (fun q best => if Y ≤ c * 3 ^ q then min q best else best) fallback

theorem select_correct (c Y : ℕ) (hc : 0 < c) (qs : List ℕ) (fallback : ℕ)
    (hfb : thresholdExponent c Y hc ≤ fallback)
    (hq : thresholdExponent c Y hc ∈ qs) : select c Y qs fallback = thresholdExponent c Y hc := by
  have hgeneral : ∀ (qs : List ℕ) (f : ℕ), thresholdExponent c Y hc ≤ f →
      thresholdExponent c Y hc ≤ select c Y qs f ∧
      (∀ q ∈ qs, Y ≤ c * 3 ^ q → select c Y qs f ≤ q) := by
    intro qs f hf
    induction qs with
    | nil => simp [select, hf]
    | cons q qs ih =>
      simp only [select, List.foldr_cons]
      change thresholdExponent c Y hc ≤ (if Y ≤ c * 3 ^ q then min q (select c Y qs f) else select c Y qs f) ∧ _
      split_ifs with h
      · refine ⟨le_min (thresholdExponent_le c Y q hc h) ih.1, ?_⟩
        intro k hk hkg
        rcases List.mem_cons.mp hk with rfl | hk
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (ih.2 k hk hkg)
      · refine ⟨ih.1, ?_⟩
        intro k hk hkg
        rcases List.mem_cons.mp hk with rfl | hk
        · exact (h hkg).elim
        · exact ih.2 k hk hkg
  have hh := hgeneral qs fallback hfb
  exact le_antisymm (hh.2 _ hq (thresholdExponent_spec c Y hc)) hh.1

end LinearAssemblies.OnePad.Algorithms
