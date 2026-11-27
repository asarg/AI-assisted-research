import LinearAssemblies.OnePad.ClosedForm
import Mathlib.Data.Nat.Find

set_option autoImplicit false

/-!
# Exact arithmetic threshold search

The functions in this module compute the minimum budget for the recurrence.
The conditional identification of `recurrenceCost` with actual tile complexity
is proved in `OnePad/Characterization.lean` (Theorem 3).
No running-time claim about these executable definitions is made here.
-/

namespace LinearAssemblies.OnePad

private theorem budget_exists (M : ℕ) : ∃ r, M ≤ fastF r :=
  ⟨M, by rw [fastF_eq_F]; exact self_le_F M⟩

/-- The least nonseed budget whose recurrence value reaches attachment target M. -/
def minimumBudget (M : ℕ) : ℕ := Nat.find (budget_exists M)

theorem minimumBudget_spec (M : ℕ) : M ≤ F (minimumBudget M) := by
  simpa only [minimumBudget, fastF_eq_F] using Nat.find_spec (budget_exists M)

theorem minimumBudget_le_iff (M r : ℕ) : minimumBudget M ≤ r ↔ M ≤ F r := by
  constructor
  · intro h
    exact le_trans (minimumBudget_spec M) (F_monotone h)
  · intro h
    exact Nat.find_min' (budget_exists M) (by simpa only [fastF_eq_F] using h)

theorem minimumBudget_minimal (M r : ℕ) (hr : r < minimumBudget M) : F r < M := by
  by_contra hn
  have h := (minimumBudget_le_iff M r).mpr (by omega)
  omega

/-- Total-cost formula; its tile interpretation is proved in `Characterization`. -/
def recurrenceCost (N : ℕ) : ℕ := 1 + minimumBudget (N - 1)

theorem self_lt_three_pow (q : ℕ) : q < 3 ^ q := by
  induction q with
  | zero => norm_num
  | succ q ih => rw [pow_succ]; omega

private theorem exponent_exists (c Y : ℕ) (hc : 0 < c) : ∃ q, Y ≤ c * 3 ^ q := by
  refine ⟨Y, ?_⟩
  have hp := self_lt_three_pow Y
  have hm := Nat.mul_le_mul_right (3 ^ Y) (show 1 ≤ c by omega)
  omega

/-- The least exponent for a coefficient threshold, as in Theorem 7. -/
def thresholdExponent (c Y : ℕ) (hc : 0 < c) : ℕ := Nat.find (exponent_exists c Y hc)

theorem thresholdExponent_spec (c Y : ℕ) (hc : 0 < c) :
    Y ≤ c * 3 ^ thresholdExponent c Y hc := Nat.find_spec (exponent_exists c Y hc)

theorem thresholdExponent_le (c Y q : ℕ) (hc : 0 < c) (h : Y ≤ c * 3 ^ q) :
    thresholdExponent c Y hc ≤ q := Nat.find_min' (exponent_exists c Y hc) h

/-- The three residue-class candidates of Equation (20), before adding the seed. -/
def threeCandidateBudget (M : ℕ) : ℕ :=
  min (5 + 3 * thresholdExponent 23 (2 * M + 3) (by omega))
    (min (6 + 3 * thresholdExponent 33 (2 * M + 3) (by omega))
      (7 + 3 * thresholdExponent 47 (2 * M + 3) (by omega)))

/-- Equation (20)'s arithmetic content, with attachment target `M = N - 1`. -/
theorem minimumBudget_eq_threeCandidates (M : ℕ) (hM : 7 ≤ M) :
    minimumBudget M = threeCandidateBudget M := by
  let q0 := thresholdExponent 23 (2 * M + 3) (by omega)
  let q1 := thresholdExponent 33 (2 * M + 3) (by omega)
  let q2 := thresholdExponent 47 (2 * M + 3) (by omega)
  have hq0 : 2 * M + 3 ≤ 23 * 3 ^ q0 := thresholdExponent_spec _ _ _
  have hq1 : 2 * M + 3 ≤ 33 * 3 ^ q1 := thresholdExponent_spec _ _ _
  have hq2 : 2 * M + 3 ≤ 47 * 3 ^ q2 := thresholdExponent_spec _ _ _
  have h0 : minimumBudget M ≤ 5 + 3 * q0 := by
    apply (minimumBudget_le_iff M _).mpr
    have he := (closed_form_scaled q0).1
    have hi : 5 + 3 * q0 = 3 * q0 + 5 := by omega
    rw [hi]
    omega
  have h1 : minimumBudget M ≤ 6 + 3 * q1 := by
    apply (minimumBudget_le_iff M _).mpr
    have he := (closed_form_scaled q1).2.1
    have hi : 6 + 3 * q1 = 3 * q1 + 6 := by omega
    rw [hi]
    omega
  have h2 : minimumBudget M ≤ 7 + 3 * q2 := by
    apply (minimumBudget_le_iff M _).mpr
    have he := (closed_form_scaled q2).2.2
    have hi : 7 + 3 * q2 = 3 * q2 + 7 := by omega
    rw [hi]
    omega
  change minimumBudget M = min (5 + 3 * q0) (min (6 + 3 * q1) (7 + 3 * q2))
  apply Nat.le_antisymm (le_min h0 (le_min h1 h2))
  let r := minimumBudget M
  have hr : M ≤ F r := minimumBudget_spec M
  have hr5 : 5 ≤ r := by
    by_contra hn
    have hm := F_monotone (show r ≤ 4 by omega)
    have hv : F 4 = 6 := by rw [← fastF_eq_F]; decide
    omega
  let q := (r - 5) / 3
  have hj : (r - 5) % 3 < 3 := Nat.mod_lt _ (by omega)
  have hd : (r - 5) % 3 + 3 * q = r - 5 := Nat.mod_add_div _ _
  generalize he : (r - 5) % 3 = j at *
  interval_cases j
  · have hi : r = 3 * q + 5 := by omega
    have hf := (closed_form_scaled q).1
    rw [hi] at hr
    have hq : q0 ≤ q := thresholdExponent_le _ _ q _ (by omega)
    exact le_trans (min_le_left _ _) (by change 5 + 3 * q0 ≤ r; omega)
  · have hi : r = 3 * q + 6 := by omega
    have hf := (closed_form_scaled q).2.1
    rw [hi] at hr
    have hq : q1 ≤ q := thresholdExponent_le _ _ q _ (by omega)
    exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
      (by change 6 + 3 * q1 ≤ r; omega)
  · have hi : r = 3 * q + 7 := by omega
    have hf := (closed_form_scaled q).2.2
    rw [hi] at hr
    have hq : q2 ≤ q := thresholdExponent_le _ _ q _ (by omega)
    exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (by change 7 + 3 * q2 ≤ r; omega)

theorem recurrenceCost_100 : recurrenceCost 100 = 12 := by
  have hlo : F 10 = 69 := by rw [← fastF_eq_F]; decide
  have hhi : F 11 = 102 := by rw [← fastF_eq_F]; decide
  have hu : minimumBudget 99 ≤ 11 := (minimumBudget_le_iff _ _).mpr (by omega)
  have hl : ¬minimumBudget 99 ≤ 10 := by
    intro h
    have hh := (minimumBudget_le_iff 99 10).mp h
    omega
  unfold recurrenceCost
  norm_num
  omega

end LinearAssemblies.OnePad
