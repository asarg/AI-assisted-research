import LinearAssemblies.Algorithms.Approximation
import LinearAssemblies.Algorithms.Power

set_option autoImplicit false

namespace LinearAssemblies.OnePad.Algorithms

open LinearAssemblies.Algorithms

/-- Threshold search with the actual repeated-squaring subroutine. -/
def selectCosted (m : Multiplication) (c Y : ℕ) (fallback : ℕ) : List ℕ → ℕ × ℕ
  | [] => (fallback, 1)
  | q :: qs =>
    let p := power m q
    let t := selectCosted m c Y fallback qs
    (if Y ≤ c * p.1 then min q t.1 else t.1,
      p.2 + t.2 + 64 * (Y.size + c.size + p.1.size + q.size + fallback.size + 1))

theorem selectCosted_correct (m : Multiplication) (hm : m.Fast) (c Y f : ℕ) (qs : List ℕ) :
    (selectCosted m c Y f qs).1 = select c Y qs f := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [selectCosted, select, List.foldr_cons, power_correct m hm, ih]

theorem logarithm_scale (B : ℕ) :
    Real.log (5 * (B : ℝ) + 10) ≤ 4 * Real.log (B + 2) := by
  have h5 : Real.log (5 : ℝ) ≤ 3 * Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 5) (show (5 : ℝ) ≤ 2 ^ 3 by norm_num)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have h2 : Real.log 2 ≤ Real.log ((B : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) B; linarith)
  rw [show 5 * (B : ℝ) + 10 = 5 * (B + 2) by ring, Real.log_mul (by norm_num) (by positivity)]
  linarith

theorem selection_cost (m : Multiplication) (hm : m.Fast) :
    ∃ D : ℝ, 2 ≤ D ∧ ∀ B c Y f : ℕ, c ≤ 81 → Y.size ≤ B → f ≤ B + 1 →
      ∀ qs : List ℕ, (∀ q ∈ qs, q ≤ B + 1) →
        ((selectCosted m c Y f qs).2 : ℝ) ≤
          (qs.length + 1) * (D * (B + 1) * Real.log (B + 2)) := by
  obtain ⟨K, hK, hk⟩ := power_cost m hm
  let D := 12 * K + 4096
  have hD : 2 ≤ D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro B c Y f hc hY hf qs hqs
  have hL : (1 : ℝ) / 2 ≤ Real.log ((B : ℝ) + 2) :=
    Probability.log_two_bounds.1.trans (Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) B; linarith))
  have hT : 1 ≤ D * (B + 1) * Real.log (B + 2) := by
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ D * (B + 1) by positivity)
    have hDB : 0 ≤ D * (B : ℝ) := by positivity
    nlinarith
  induction qs with
  | nil => simpa only [selectCosted, List.length_nil, Nat.cast_zero, zero_add, one_mul, Nat.cast_one] using hT
  | cons q qs ih =>
    have hq := hqs q List.mem_cons_self
    have hi := ih (fun j hj => hqs j (List.mem_cons_of_mem _ hj))
    have hp := hk (B + 1) q hq
    have hlog := logarithm_scale B
    have hqR : (q : ℝ) ≤ B + 1 := by exact_mod_cast hq
    have hp' : ((power m q).2 : ℝ) ≤ 12 * K * (B + 1) * Real.log (B + 2) := by
      simp only [Nat.cast_add, Nat.cast_one] at hp
      have he : 5 * ((B : ℝ) + 1) + 5 = 5 * B + 10 := by ring
      rw [he] at hp
      calc
        _ ≤ K * (2 * q + 1) * (4 * Real.log (B + 2)) :=
          hp.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
        _ ≤ K * (3 * (B + 1)) * (4 * Real.log (B + 2)) := by gcongr; linarith
        _ = _ := by ring
    have hsP := size_power_three q
    have hsQ : q.size ≤ q := Nat.size_le.2 Nat.lt_two_pow_self
    have hsF : f.size ≤ f := Nat.size_le.2 Nat.lt_two_pow_self
    have hsC : c.size ≤ 7 := Nat.size_le.2 (by norm_num; omega)
    have hcharge : 64 * (Y.size + c.size + (3 ^ q).size + q.size + f.size + 1) ≤ 2048 * (B + 1) := by omega
    have hchargeR : (64 * (Y.size + c.size + (3 ^ q).size + q.size + f.size + 1) : ℝ) ≤ 2048 * (B + 1) := by exact_mod_cast hcharge
    have hchargeL : (64 * (Y.size + c.size + (3 ^ q).size + q.size + f.size + 1) : ℝ) ≤
        4096 * (B + 1) * Real.log (B + 2) := by
      have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
      nlinarith
    simp only [selectCosted, power_correct m hm, List.length_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [D] at *
    nlinarith

def fastThreshold (m : Multiplication) (c Y B : ℕ) (β : ℚ) : ℕ × ℕ :=
  let a := center B β
  selectCosted m c Y (a + 1) (candidates a)

theorem fastThreshold_correct (m : Multiplication) (hm : m.Fast)
    (c Y : ℕ) (hc : 0 < c) (hcLo : 9 ≤ c) (hcHi : c ≤ 81) (hY : 0 < Y)
    (β : ℚ) (hβ : |(β : ℝ) - beta| ≤ 1 / (4 * Y.size)) :
    (fastThreshold m c Y Y.size β).1 = thresholdExponent c Y hc := by
  have hB : 1 ≤ Y.size := Nat.size_pos.2 hY
  have hlow : 2 ^ (Y.size - 1) ≤ Y := Nat.lt_size.1 (by omega)
  have hw := threshold_window Y c Y.size hc hcLo hcHi hY hB hlow (Nat.lt_size_self Y) β hβ
  unfold fastThreshold
  rw [selectCosted_correct m hm]
  exact select_correct c Y hc _ _ hw.2 ((candidates_mem _ _).2 hw)

/-- Exact fast minimum-budget evaluator. Small targets use the certified scan;
large targets evaluate the three residue-class thresholds of Equation (20). -/
def fast (m : Multiplication) (l : Logarithm) (M : ℕ) : ℕ × ℕ :=
  if M < 7 then sequential M
  else
    let Y := 2 * M + 3
    let B := Y.size
    let β := approximateBeta l B
    let q0 := fastThreshold m 23 Y B β
    let q1 := fastThreshold m 33 Y B β
    let q2 := fastThreshold m 47 Y B β
    (min (5 + 3 * q0.1) (min (6 + 3 * q1.1) (7 + 3 * q2.1)),
      approximationCost l B + q0.2 + q1.2 + q2.2 + 128 * (B + M.size + 1))

theorem fast_correct (m : Multiplication) (hm : m.Fast) (l : Logarithm) (hl : l.Polynomial)
    (M : ℕ) : (fast m l M).1 = minimumBudget M := by
  unfold fast
  split_ifs with hM
  · exact sequential_correct M
  · have hY : 0 < 2 * M + 3 := by omega
    have hβ := approximateBeta_correct l hl (2 * M + 3).size (Nat.size_pos.2 hY)
    rw [minimumBudget_eq_threeCandidates M (by omega)]
    simp only [threeCandidateBudget, fastThreshold_correct m hm 23 _ (by omega) (by omega) (by omega) hY _ hβ,
      fastThreshold_correct m hm 33 _ (by omega) (by omega) (by omega) hY _ hβ,
      fastThreshold_correct m hm 47 _ (by omega) (by omega) (by omega) hY _ hβ]

end LinearAssemblies.OnePad.Algorithms
