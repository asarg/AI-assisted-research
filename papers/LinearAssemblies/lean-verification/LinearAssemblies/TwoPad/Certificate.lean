import LinearAssemblies.TwoPad.Construction

set_option autoImplicit false

namespace LinearAssemblies.TwoPad

variable {b : ℕ} (d : DigitData b)

def potential : State d → ℝ
  | .inl j => (d.value : ℝ) - j.val
  | .inr (.inl i) => (d.value : ℝ) - d.prefixValue i.val
  | .inr (.inr j) => (d.value : ℝ) + (j.val + 1 : ℕ)

@[simp] theorem input_potential : potential d (input d) = d.value := by simp [input, potential]
@[simp] theorem terminal_potential : potential d (terminal d) = 0 := by
  simp [terminal, potential, DigitData.value]

theorem pathNext_potential (j : Fin d.first) :
    potential d (pathNext d j) = (d.value : ℝ) - j.val - 1 := by
  unfold pathNext
  split_ifs with hj
  · simp only [potential, Nat.cast_add, Nat.cast_one]; ring
  · have he : j.val + 1 = d.first := by omega
    have he' : (j.val : ℝ) + 1 = d.first := by exact_mod_cast he
    simp only [potential, Fin.val_zero, DigitData.prefixValue]
    linarith

@[simp] theorem afterFirst_potential : potential d (afterFirst d) = (d.value : ℝ) - 1 := by
  simpa [afterFirst] using pathNext_potential d ⟨0, d.first_pos⟩

theorem resetTarget_potential (i : Fin d.count) :
    potential d (resetTarget d i) = (d.value : ℝ) + d.digit i - 2 := by
  unfold resetTarget
  split_ifs with h1 h2
  · rw [afterFirst_potential, h1]; norm_num; ring
  · rw [input_potential, h2]; norm_num
  · have ha := d.digit_bounds i i.isLt
    have ha3 : 3 ≤ d.digit i := by omega
    simp only [potential, Nat.cast_add, Nat.cast_one, Nat.cast_sub ha3]
    norm_num
    ring

theorem delayNext_potential (j : Fin (b - 2)) :
    potential d (delayNext d j) = (d.value : ℝ) + j.val := by
  unfold delayNext
  split_ifs with hj
  · simp [input_potential, hj]
  · have hj1 : 1 ≤ j.val := by omega
    simp only [potential, Nat.sub_add_cancel hj1]

theorem degree_path (j : Fin d.first) : (presentation d).degree twoPad (.inl j) = 1 := by
  have h := row_sum d (fun _ => (1 : ℝ)) (.inl j)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

theorem degree_delay (j : Fin (b - 2)) : (presentation d).degree twoPad (.inr (.inr j)) = 1 := by
  have h := row_sum d (fun _ => (1 : ℝ)) (.inr (.inr j))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

theorem degree_digit (hb : 2 ≤ b) (i : Fin (d.count + 1)) :
    (presentation d).degree twoPad (.inr (.inl i)) = if i.val < d.count then b else 0 := by
  have h := row_sum d (fun _ => (1 : ℝ)) (.inr (.inl i))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  by_cases hi : i.val < d.count
  · rw [dif_pos hi] at h
    rw [if_pos hi]
    have hc : (presentation d).degree twoPad (.inr (.inl i)) = 1 + 1 + (b - 2) := by exact_mod_cast h
    omega
  · rw [dif_neg hi] at h
    rw [if_neg hi]
    exact_mod_cast h

/-- All first-step equations for the physical two-pad tile entries, including shared resets. -/
theorem certificate (hb : 2 ≤ b) : (presentation d).Certificate twoPad (potential d) := by
  have hb1 : 1 ≤ b := by omega
  constructor
  · intro x
    rcases x with j | (i | j)
    · have hm := d.first_le_value hb1
      have hj : (j.val : ℝ) ≤ d.value := by exact_mod_cast (show j.val ≤ d.value by omega)
      exact sub_nonneg.mpr hj
    · have hi := d.prefix_le_value hb1 i.val (by omega)
      exact sub_nonneg.mpr (by exact_mod_cast hi)
    · dsimp [potential]; positivity
  · intro x hx
    rcases x with j | (i | j)
    · rw [degree_path] at hx; omega
    · rw [degree_digit d hb] at hx
      have hi : i.val = d.count := by split_ifs at hx <;> omega
      simp only [potential, hi, DigitData.value, sub_self]
    · rw [degree_delay] at hx; omega
  · intro x
    change ((presentation d).degree twoPad x : ℝ) * potential d x =
      (presentation d).degree twoPad x +
      ∑ e ∈ (presentation d).choices twoPad x, potential d (target d e)
    rw [row_sum]
    rcases x with j | (i | j)
    · simp only []
      rw [degree_path, pathNext_potential]
      simp only [Nat.cast_one, one_mul, potential]
      ring
    · simp only [degree_digit d hb]
      by_cases hi : i.val < d.count
      · rw [if_pos hi, dif_pos hi, resetTarget_potential, afterFirst_potential]
        simp only [potential, Fin.val_succ, DigitData.prefixValue, Nat.cast_add, Nat.cast_mul,
          Nat.cast_sub hb, Nat.cast_ofNat]
        ring
      · rw [if_neg hi, dif_neg hi]
        simp
    · simp only []
      rw [degree_delay, delayNext_potential]
      simp only [Nat.cast_one, one_mul, potential, Nat.cast_add]
      ring

/-- Exact mean of the two-pad construction, seed included. -/
theorem expectedLength (ext : Probability.FiniteAbsorptionLaw) (hb : 2 ≤ b) :
    (presentation d).system.expectedLength twoPad = (d.value : ℝ) + 1 := by
  rw [(presentation d).system_mean twoPad ext (certificate d hb)]
  change 1 + potential d (input d) = _
  rw [input_potential]
  ring

/-- The delay path adds at most b-2 to the input mean, at every state. -/
theorem potential_bound (x : State d) :
    potential d x ≤ (d.value : ℝ) + (b - 2 : ℕ) := by
  rcases x with j | (i | j)
  · dsimp [potential]; have h : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ (b - 2 : ℕ) := Nat.cast_nonneg _
    linarith
  · dsimp [potential]; have h : (0 : ℝ) ≤ d.prefixValue i.val := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ (b - 2 : ℕ) := Nat.cast_nonneg _
    linarith
  · have h : j.val + 1 ≤ b - 2 := j.isLt
    exact add_le_add_left (by exact_mod_cast h) _

end LinearAssemblies.TwoPad
