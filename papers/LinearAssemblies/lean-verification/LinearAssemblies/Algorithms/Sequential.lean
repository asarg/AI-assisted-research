import LinearAssemblies.OnePad.ExactValue
import Mathlib.Data.Nat.Size

set_option autoImplicit false

/-!
# A costed three-register recurrence scan (Theorem 6)

The counter and three previous values are explicit. `scan` never evaluates the
recursive mathematical specification `F`. Its fuel is a proved binary-length
bound, not the (potentially enormous) numeric target. The charge is a linear
binary-arithmetic envelope for the constant-many additions, comparisons,
shifts, copies and counter updates in one iteration. It is a bit-cost model,
not a measurement of Lean's evaluator or a verified machine-code compiler.
-/

namespace LinearAssemblies.OnePad.Algorithms

def next (a b c : ℕ) : ℕ := max (a + 1) (max (2 * (b + 1)) (3 * (c + 1)))

def charge (M r a b c : ℕ) : ℕ :=
  64 * (1 + M.size + r.size + a.size + b.size + c.size)

/-- Result is (stopping index, charged bit operations). The final comparison
is charged too. All recursive calls use only three previous recurrence values. -/
def scan (M : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, r, a, b, c => (r, charge M r a b c)
  | fuel + 1, r, a, b, c =>
    if M ≤ a then (r, charge M r a b c)
    else
      let t := scan M fuel (r + 1) (next a b c) a b
      (t.1, charge M r a b c + t.2)

theorem next_spec (r : ℕ) (hr : 2 ≤ r) :
    next (F r) (F (r - 1)) (F (r - 2)) = F (r + 1) := by
  rw [recurrence_three (r + 1) (by omega)]
  simp only [next]
  congr 1

theorem binary_fuel (M : ℕ) : minimumBudget M ≤ 3 * M.size + 5 := by
  apply (minimumBudget_le_iff _ _).2
  have hp : 2 ^ M.size ≤ 3 ^ M.size := Nat.pow_le_pow_left (by omega) _
  have hm := Nat.lt_size_self M
  have hc := (closed_form_scaled M.size).1
  omega

theorem F_at_stop (M r : ℕ) (hr : r ≤ minimumBudget M) : F r ≤ 3 * M := by
  cases r with
  | zero => simp
  | succ r =>
    have hprev : F r < M := minimumBudget_minimal M r (by omega)
    rw [reduced_recurrence]
    apply Finset.sup_le
    intro d hd
    obtain ⟨hd1, hd3⟩ := Finset.mem_Icc.mp hd
    have hpre := F_monotone (show r + 1 - d ≤ r by omega)
    have hmul := Nat.mul_le_mul (show d ≤ 3 by omega) (show F (r + 1 - d) + 1 ≤ M by omega)
    exact hmul

theorem size_triple (M : ℕ) : (3 * M).size ≤ M.size + 2 := by
  apply Nat.size_le.2
  rw [pow_add]
  norm_num
  have h := Nat.lt_size_self M
  omega

theorem size_le_self (n : ℕ) : n.size ≤ n := by
  apply Nat.size_le.2
  exact Nat.lt_two_pow_self

theorem charge_bound (M r : ℕ) (hr : r ≤ minimumBudget M) :
    charge M r (F r) (F (r - 1)) (F (r - 2)) ≤ 640 * (M.size + 2) := by
  have hf := F_at_stop M r hr
  have hfm1 := F_monotone (show r - 1 ≤ r by omega)
  have hfm2 := F_monotone (show r - 2 ≤ r by omega)
  have hs0 := (Nat.size_le_size hf).trans (size_triple M)
  have hs1 := (Nat.size_le_size (hfm1.trans hf)).trans (size_triple M)
  have hs2 := (Nat.size_le_size (hfm2.trans hf)).trans (size_triple M)
  have hsr := (size_le_self r).trans (hr.trans (binary_fuel M))
  unfold charge
  omega

/-- Loop invariant simultaneously proves the answer and bounds its trace cost. -/
theorem scan_spec (M fuel r : ℕ) (hr : 2 ≤ r) (hrm : r ≤ minimumBudget M)
    (hfuel : minimumBudget M ≤ r + fuel) :
    (scan M fuel r (F r) (F (r - 1)) (F (r - 2))).1 = minimumBudget M ∧
    (scan M fuel r (F r) (F (r - 1)) (F (r - 2))).2 ≤
      (minimumBudget M - r + 1) * (640 * (M.size + 2)) := by
  induction fuel generalizing r with
  | zero =>
    have he : r = minimumBudget M := by omega
    simp only [scan, he, Nat.sub_self, zero_add, one_mul]
    exact ⟨trivial, charge_bound M _ (by omega)⟩
  | succ fuel ih =>
    simp only [scan]
    split_ifs with h
    · have he : r = minimumBudget M := le_antisymm hrm ((minimumBudget_le_iff M r).2 h)
      simp only [he, Nat.sub_self, zero_add, one_mul]
      exact ⟨trivial, charge_bound M _ (by omega)⟩
    · have hlt : r < minimumBudget M := Nat.lt_of_not_ge (fun hn => h ((minimumBudget_le_iff M r).1 hn))
      have hh := ih (r + 1) (by omega) (by omega) (by omega)
      rw [next_spec r hr]
      have h1 : r + 1 - 1 = r := by omega
      have h2 : r + 1 - 2 = r - 1 := by omega
      rw [h1, h2] at hh
      refine ⟨hh.1, ?_⟩
      have hc := charge_bound M r hrm
      have he : minimumBudget M - r + 1 = (minimumBudget M - (r + 1) + 1) + 1 := by omega
      rw [he, add_mul, one_mul]
      omega

/-- An executable minimum-budget algorithm with a certified cost counter. -/
def sequential (M : ℕ) : ℕ × ℕ :=
  if M ≤ 2 then (M, 128 * (M.size + 2))
  else scan M (3 * M.size + 5) 2 2 1 0

theorem sequential_correct (M : ℕ) : (sequential M).1 = minimumBudget M := by
  unfold sequential
  split_ifs with h
  · have hs : ∀ m : ℕ, m ≤ 2 → F m = m := by
      intro m hm
      interval_cases m <;> norm_num [F, Finset.range_succ]
    have hu : minimumBudget M ≤ M := (minimumBudget_le_iff M M).2 (by rw [hs M h])
    have hl := minimumBudget_spec M
    rw [hs _ (hu.trans h)] at hl
    exact le_antisymm hl hu
  · have hr : 2 ≤ minimumBudget M := by
      by_contra hn
      have ht := (minimumBudget_spec M).trans (F_monotone (show minimumBudget M ≤ 2 by omega))
      rw [initial_values.2.2.1] at ht
      omega
    have hh := (scan_spec M (3 * M.size + 5) 2 (by omega) hr (by have := binary_fuel M; omega)).1
    simpa only [initial_values.1, initial_values.2.1, initial_values.2.2.1] using hh

theorem sequential_cost (M : ℕ) :
    (sequential M).2 ≤ 2560 * (M.size + 2) ^ 2 := by
  unfold sequential
  split_ifs with h
  · simp only
    nlinarith
  · have hr : 2 ≤ minimumBudget M := by
      by_contra hn
      have ht := (minimumBudget_spec M).trans (F_monotone (show minimumBudget M ≤ 2 by omega))
      rw [initial_values.2.2.1] at ht
      omega
    have hh := (scan_spec M (3 * M.size + 5) 2 (by omega) hr (by have := binary_fuel M; omega)).2
    simp only [initial_values.1, initial_values.2.1, initial_values.2.2.1] at hh
    have hm := binary_fuel M
    have he : minimumBudget M - 2 + 1 ≤ 4 * (M.size + 2) := by omega
    have hb := Nat.mul_le_mul_right (640 * (M.size + 2)) he
    nlinarith

end LinearAssemblies.OnePad.Algorithms
