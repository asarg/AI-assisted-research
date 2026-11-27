import LinearAssemblies.Algorithms.FastSearch
import LinearAssemblies.Algorithms.BitGrowth
import LinearAssemblies.OnePad.Characterization

set_option autoImplicit false

namespace LinearAssemblies.OnePad.Algorithms

open Filter LinearAssemblies.Algorithms

theorem fast_cost_raw (m : Multiplication) (hm : m.Fast) (l : Logarithm) (hl : l.Polynomial) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ M : ℕ, 7 ≤ M →
      ((fast m l M).2 : ℝ) ≤ approximationCost l (2 * M + 3).size +
        D * ((2 * M + 3).size + 1) * Real.log ((2 * M + 3).size + 2) := by
  obtain ⟨C, hC, hc⟩ := selection_cost m hm
  let D := 24 * C + 512
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro M hM
  let Y := 2 * M + 3
  let B := Y.size
  let β := approximateBeta l B
  let a := center B β
  have hB : 1 ≤ B := Nat.size_pos.2 (by dsimp [Y]; omega)
  have hβ := approximateBeta_correct l hl B hB
  have ha : a ≤ B := (center_spec B hB β hβ).2.2.2.2
  have hqs : ∀ q ∈ candidates a, q ≤ B + 1 := by
    intro q hq
    have hh := (candidates_mem a q).1 hq
    omega
  have hL : (1 : ℝ) / 2 ≤ Real.log ((B : ℝ) + 2) :=
    Probability.log_two_bounds.1.trans (Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) B; linarith))
  have hT : 0 ≤ C * (B + 1) * Real.log (B + 2) := by positivity
  have hsel : ∀ c : ℕ, c ≤ 81 → ((fastThreshold m c Y B β).2 : ℝ) ≤
      8 * (C * (B + 1) * Real.log (B + 2)) := by
    intro c hc81
    have hh := hc B c Y (a + 1) hc81 le_rfl (by omega) (candidates a) hqs
    have hlen : ((candidates a).length : ℝ) + 1 ≤ 8 := by exact_mod_cast (show (candidates a).length + 1 ≤ 8 by have := candidates_length a; omega)
    exact hh.trans (mul_le_mul_of_nonneg_right hlen hT)
  have h23 := hsel 23 (by omega)
  have h33 := hsel 33 (by omega)
  have h47 := hsel 47 (by omega)
  have hMS : M.size ≤ B := Nat.size_le_size (by dsimp [Y]; omega)
  have hover : (128 * (B + M.size + 1) : ℝ) ≤ 512 * (B + 1) * Real.log (B + 2) := by
    have hs : (M.size : ℝ) ≤ B := by exact_mod_cast hMS
    have hh := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 512 * (B + 1) by positivity)
    nlinarith
  rw [fast, if_neg (by omega : ¬M < 7)]
  change ((approximationCost l B + (fastThreshold m 23 Y B β).2 +
    (fastThreshold m 33 Y B β).2 + (fastThreshold m 47 Y B β).2 +
    128 * (B + M.size + 1) : ℕ) : ℝ) ≤ _
  push_cast
  change (approximationCost l B : ℝ) + (fastThreshold m 23 Y B β).2 +
    (fastThreshold m 33 Y B β).2 + (fastThreshold m 47 Y B β).2 +
    128 * ((B : ℝ) + M.size + 1) ≤ (approximationCost l B : ℝ) + D * (B + 1) * Real.log (B + 2)
  dsimp [D]
  nlinarith

theorem bit_budget_comparison (M : ℕ) :
    (((2 * M + 3).size : ℝ) + 1) * Real.log ((2 * M + 3).size + 2) ≤
      12 * ((M.size : ℝ) + 1) * Real.log (M.size + 2) := by
  have hb : ((2 * M + 3).size : ℝ) ≤ M.size + 3 := by exact_mod_cast target_size_bound M
  have hL : (1 : ℝ) / 2 ≤ Real.log ((M.size : ℝ) + 2) :=
    Probability.log_two_bounds.1.trans (Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) M.size; linarith))
  have hlog : Real.log ((2 * M + 3).size + 2 : ℝ) ≤ 3 * Real.log (M.size + 2) := by
    calc
      _ ≤ Real.log (4 * ((M.size : ℝ) + 2)) := Real.log_le_log (by positivity) (by have := Nat.cast_nonneg (α := ℝ) M.size; linarith)
      _ = 2 * Real.log 2 + Real.log ((M.size : ℝ) + 2) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
        congr 1
        have hh := Real.log_pow (2 : ℝ) 2
        norm_num at hh
        exact hh
      _ ≤ _ := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ M.size + 2 by have := Nat.cast_nonneg (α := ℝ) M.size; linarith)
        linarith
  calc
    _ ≤ (((2 * M + 3).size : ℝ) + 1) * (3 * Real.log (M.size + 2)) := by gcongr
    _ ≤ (4 * ((M.size : ℝ) + 1)) * (3 * Real.log (M.size + 2)) := by
      gcongr
      have := Nat.cast_nonneg (α := ℝ) M.size
      linarith
    _ = _ := by ring

/-- Theorem 7 in input-bit-length form. The approximation stage is absorbed
using its proved polynomial-in-log(b) bound, not treated as constant time. -/
theorem fast_cost_bitlength (m : Multiplication) (hm : m.Fast) (l : Logarithm) (hl : l.Polynomial) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      ((fast m l M).2 : ℝ) ≤ C * (M.size + 1) * Real.log (M.size + 2) := by
  obtain ⟨D, hD, hd⟩ := fast_cost_raw m hm l hl
  refine ⟨12 * D + 6, by positivity, ?_⟩
  filter_upwards [target_size_tendsto.eventually (approximation_small l hl),
    eventually_ge_atTop (7 : ℕ)] with M happ hM
  have hh := hd M hM
  have ha : (approximationCost l (2 * M + 3).size : ℝ) ≤ (2 * M + 3).size := by exact_mod_cast happ
  have hb : ((2 * M + 3).size : ℝ) ≤ M.size + 3 := by exact_mod_cast target_size_bound M
  have hL : (1 : ℝ) / 2 ≤ Real.log ((M.size : ℝ) + 2) :=
    Probability.log_two_bounds.1.trans (Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) M.size; linarith))
  have hmul := mul_le_mul_of_nonneg_left (bit_budget_comparison M) (show 0 ≤ D by linarith)
  have hsmall := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 6 * (M.size + 1) by positivity)
  have hn : (0 : ℝ) ≤ M.size := Nat.cast_nonneg _
  nlinarith

/-- Include the seed in the algorithm output and charge the final addition. -/
def sequentialLength (N : ℕ) : ℕ × ℕ :=
  let a := sequential (N - 1)
  (a.1 + 1, a.2 + 128 * (N.size + 2))

def fastLength (m : Multiplication) (l : Logarithm) (N : ℕ) : ℕ × ℕ :=
  let a := fast m l (N - 1)
  (a.1 + 1, a.2 + 128 * (N.size + 2))

theorem sequentialLength_correct (N : ℕ) : (sequentialLength N).1 = recurrenceCost N := by
  simp only [sequentialLength, sequential_correct, recurrenceCost, Nat.add_comm]

theorem fastLength_correct (m : Multiplication) (hm : m.Fast) (l : Logarithm) (hl : l.Polynomial)
    (N : ℕ) : (fastLength m l N).1 = recurrenceCost N := by
  simp only [fastLength, fast_correct m hm l hl, recurrenceCost, Nat.add_comm]

theorem sequentialLength_cost (N : ℕ) :
    (sequentialLength N).2 ≤ 2688 * (N.size + 2) ^ 2 := by
  have hh := sequential_cost (N - 1)
  have hs := Nat.size_le_size (Nat.sub_le N 1)
  have hp := Nat.pow_le_pow_left (show (N - 1).size + 2 ≤ N.size + 2 by omega) 2
  have hmul := Nat.mul_le_mul_left 2560 hp
  dsimp [sequentialLength]
  nlinarith

/-- Tile-level correctness: these are minimum total costs for actual systems. -/
theorem sequential_tile_minimum (ext : Probability.FiniteAbsorptionLaw) (N : ℕ) (hN : 1 ≤ N) :
    LengthRealizable (sequentialLength N).1 N ∧
      ∀ k, LengthRealizable k N → (sequentialLength N).1 ≤ k := by
  rw [sequentialLength_correct]
  exact minimum_tile_cost ext N hN

theorem fast_tile_minimum (ext : Probability.FiniteAbsorptionLaw)
    (m : Multiplication) (hm : m.Fast) (l : Logarithm) (hl : l.Polynomial)
    (N : ℕ) (hN : 1 ≤ N) :
    LengthRealizable (fastLength m l N).1 N ∧
      ∀ k, LengthRealizable k N → (fastLength m l N).1 ≤ k := by
  rw [fastLength_correct m hm l hl]
  exact minimum_tile_cost ext N hN

theorem sequential_log_cost : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    ((sequentialLength N).2 : ℝ) ≤ C * (Real.log N) ^ 2 := by
  refine ⟨67200, by norm_num, ?_⟩
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hl, eventually_ge_atTop (1 : ℕ)] with N hlog hN
  have hs := size_log_bound N hN
  have hc : ((sequentialLength N).2 : ℝ) ≤ 2688 * ((N.size : ℝ) + 2) ^ 2 := by
    exact_mod_cast sequentialLength_cost N
  have hb : (N.size : ℝ) + 2 ≤ 5 * Real.log N := by linarith
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N.size + 2) hb 2
  nlinarith

theorem fastLength_bit_cost (m : Multiplication) (hm : m.Fast) (l : Logarithm) (hl : l.Polynomial) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((fastLength m l N).2 : ℝ) ≤ C * (N.size + 1) * Real.log (N.size + 2) := by
  obtain ⟨C, hC, hc⟩ := fast_cost_bitlength m hm l hl
  have ht : Tendsto (fun N : ℕ => N - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (k + 1)] with N hN
    omega
  refine ⟨C + 512, by positivity, ?_⟩
  filter_upwards [ht.eventually hc] with N hN
  have hs : ((N - 1).size : ℝ) ≤ N.size := by exact_mod_cast Nat.size_le_size (Nat.sub_le N 1)
  have hlog : Real.log ((N - 1).size + 2 : ℝ) ≤ Real.log (N.size + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hmul : C * ((N - 1).size + 1) * Real.log ((N - 1).size + 2) ≤
      C * (N.size + 1) * Real.log (N.size + 2) := by
    apply mul_le_mul
    · gcongr
    · exact hlog
    · apply Real.log_nonneg
      have := Nat.cast_nonneg (α := ℝ) (N - 1).size
      linarith
    · positivity
  have hL : (1 : ℝ) / 2 ≤ Real.log ((N.size : ℝ) + 2) :=
    Probability.log_two_bounds.1.trans (Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) N.size; linarith))
  have hsmall := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 512 * (N.size + 1) by positivity)
  have hn : (0 : ℝ) ≤ N.size := Nat.cast_nonneg _
  simp only [fastLength, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem loglog_budget (N : ℕ) (hN : 1 ≤ N) (hlog : 4 ≤ Real.log (N : ℝ)) :
    ((N.size : ℝ) + 1) * Real.log (N.size + 2) ≤
      9 * Real.log N * Real.log (Real.log N) := by
  have hs := size_log_bound N hN
  have hll : Real.log 2 ≤ Real.log (Real.log (N : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hllp : 0 ≤ Real.log (Real.log (N : ℝ)) := by linarith [Probability.log_two_bounds.1]
  have hl : Real.log ((N.size : ℝ) + 2) ≤ 3 * Real.log (Real.log N) := by
    calc
      _ ≤ Real.log (4 * Real.log (N : ℝ)) := Real.log_le_log (by positivity) (by linarith)
      _ = 2 * Real.log 2 + Real.log (Real.log (N : ℝ)) := by
        rw [Real.log_mul (by norm_num) (by linarith)]
        congr 1
        have hh := Real.log_pow (2 : ℝ) 2
        norm_num at hh
        exact hh
      _ ≤ _ := by linarith
  calc
    _ ≤ ((N.size : ℝ) + 1) * (3 * Real.log (Real.log N)) := by gcongr
    _ ≤ (3 * Real.log N) * (3 * Real.log (Real.log N)) := by gcongr; linarith
    _ = _ := by ring

theorem fast_log_cost (m : Multiplication) (hm : m.Fast) (l : Logarithm) (hl : l.Polynomial) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((fastLength m l N).2 : ℝ) ≤ C * Real.log N * Real.log (Real.log N) := by
  obtain ⟨C, hC, hc⟩ := fastLength_bit_cost m hm l hl
  refine ⟨9 * C, by positivity, ?_⟩
  have hl4 : ∀ᶠ N : ℕ in atTop, 4 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  filter_upwards [hc, hl4, eventually_ge_atTop (1 : ℕ)] with N hcost hlog hN
  have hh := mul_le_mul_of_nonneg_left (loglog_budget N hN hlog) hC.le
  nlinarith

/-- Theorem 6: exact one-pad optimum and quadratic logarithmic bit cost. -/
theorem theorem_six (ext : Probability.FiniteAbsorptionLaw) :
    (∀ N : ℕ, 1 ≤ N → LengthRealizable (sequentialLength N).1 N ∧
      ∀ k, LengthRealizable k N → (sequentialLength N).1 ≤ k) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((sequentialLength N).2 : ℝ) ≤ C * (Real.log N) ^ 2 :=
  ⟨sequential_tile_minimum ext, sequential_log_cost⟩

/-- Theorem 7: exact one-pad optimum and quasi-linear logarithmic bit cost,
conditional on the two generic external arithmetic subroutine contracts. -/
theorem theorem_seven (ext : Probability.FiniteAbsorptionLaw)
    (m : Multiplication) (hm : m.Fast) (l : Logarithm) (hl : l.Polynomial) :
    (∀ N : ℕ, 1 ≤ N → LengthRealizable (fastLength m l N).1 N ∧
      ∀ k, LengthRealizable k N → (fastLength m l N).1 ≤ k) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((fastLength m l N).2 : ℝ) ≤ C * Real.log N * Real.log (Real.log N) :=
  ⟨fast_tile_minimum ext m hm l hl, fast_log_cost m hm l hl⟩

end LinearAssemblies.OnePad.Algorithms
