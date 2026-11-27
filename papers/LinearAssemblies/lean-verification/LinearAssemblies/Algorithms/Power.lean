import LinearAssemblies.Algorithms.Arithmetic
import LinearAssemblies.LowerBounds

set_option autoImplicit false

namespace LinearAssemblies.Algorithms

/-- Repeated squaring, with one recursive call per halving. The extra linear
charge covers parity, halving, optional multiplication by 3, and copies. -/
def power (m : Multiplication) (q : ℕ) : ℕ × ℕ :=
  if q = 0 then (1, 1)
  else
    let p := power m (q / 2)
    let v := m.run p.1 p.1
    (if q % 2 = 0 then v else 3 * v,
      p.2 + m.steps p.1 p.1 + 64 * (q.size + p.1.size + 1))
termination_by q
decreasing_by omega

theorem power_correct (m : Multiplication) (hm : m.Fast) (q : ℕ) :
    (power m q).1 = 3 ^ q := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq : q = 0
    · rw [power, if_pos hq]
      simp [hq]
    · rw [power, if_neg hq]
      have hp := ih (q / 2) (by omega)
      dsimp only
      rw [hp, hm.correct, ← pow_add]
      split_ifs with hmod
      · congr 1
        omega
      · have hodd : q = q / 2 + q / 2 + 1 := by omega
        conv_rhs => rw [hodd, pow_succ]
        ring

theorem size_power_three (q : ℕ) : (3 ^ q).size ≤ 2 * q + 1 := by
  apply Nat.size_le.2
  have h : 3 ^ q ≤ 4 ^ q := Nat.pow_le_pow_left (by omega) _
  have he : 4 ^ q = 2 ^ (2 * q) := by rw [pow_mul]; norm_num
  rw [he] at h
  have hh : 2 ^ (2 * q) < 2 ^ (2 * q + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  exact h.trans_lt hh

/-- The geometric sum of operand sizes is bounded in the induction itself;
there is no extra logarithmic factor from the recursion depth. -/
theorem power_cost (m : Multiplication) (hm : m.Fast) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ Q q : ℕ, q ≤ Q →
      ((power m q).2 : ℝ) ≤ K * (2 * q + 1) * Real.log (5 * Q + 5) := by
  obtain ⟨C, hC, hc⟩ := hm.bound
  let K := 5 * C + 256
  have hK : 1 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro Q q hqQ
  have hL : 1 ≤ Real.log (5 * (Q : ℝ) + 5) := by
    have h4 : Real.log (4 : ℝ) ≤ Real.log (5 * (Q : ℝ) + 5) :=
      Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) Q; linarith)
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have := Real.log_pow (2 : ℝ) 2
      norm_num at this
      exact this
    rw [he] at h4
    linarith [Probability.log_two_bounds.1]
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq : q = 0
    · rw [power, if_pos hq]
      simp only [hq, Nat.cast_one, Nat.cast_zero, mul_zero, zero_add, mul_one]
      nlinarith
    · rw [power, if_neg hq]
      have hq1 : 1 ≤ q := by omega
      have hhalf : q / 2 < q := by omega
      have hrec := ih (q / 2) hhalf (by omega)
      have hp := power_correct m hm (q / 2)
      dsimp only
      rw [hp]
      have hs := size_power_three (q / 2)
      have hsq : q.size ≤ q := Nat.size_le.2 Nat.lt_two_pow_self
      have hw : (3 ^ (q / 2)).size + (3 ^ (q / 2)).size + 1 ≤ 5 * q := by omega
      have hwr : ((3 ^ (q / 2)).size : ℝ) + (3 ^ (q / 2)).size + 1 ≤ 5 * q := by exact_mod_cast hw
      have hlog : Real.log ((3 ^ (q / 2)).size + (3 ^ (q / 2)).size + 2 : ℝ) ≤
          Real.log (5 * (Q : ℝ) + 5) := by
        apply Real.log_le_log (by positivity)
        have hQ : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
        linarith
      have hmul := hc (3 ^ (q / 2)) (3 ^ (q / 2))
      have hmul' : (m.steps (3 ^ (q / 2)) (3 ^ (q / 2)) : ℝ) ≤
          5 * C * q * Real.log (5 * (Q : ℝ) + 5) := by
        calc
          _ ≤ C * ((3 ^ (q / 2)).size + (3 ^ (q / 2)).size + 1) * Real.log (5 * (Q : ℝ) + 5) :=
            hmul.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
          _ ≤ (C * (5 * q)) * Real.log (5 * (Q : ℝ) + 5) := by gcongr
          _ = _ := by ring
      have hlin : 64 * (q.size + (3 ^ (q / 2)).size + 1) ≤ 256 * q := by omega
      have hlinr : (64 * (q.size + (3 ^ (q / 2)).size + 1) : ℝ) ≤ 256 * q := by exact_mod_cast hlin
      have hhalfR : 2 * ((q / 2 : ℕ) : ℝ) ≤ q := by exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
      push_cast
      have hlinlog := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 256 * q by positivity)
      dsimp [K] at *
      nlinarith

end LinearAssemblies.Algorithms
