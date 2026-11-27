import LinearAssemblies.Analysis.Growth

set_option autoImplicit false

namespace LinearAssemblies

/-- A partition into positive means differing by at most one (when 1<=r<=M). -/
def balanced (M r : ℕ) : List ℕ :=
  List.replicate (M % r) (M / r + 1) ++ List.replicate (r - M % r) (M / r)

theorem balanced_length (M r : ℕ) (hr : 1 ≤ r) : (balanced M r).length = r := by
  have hmod := Nat.mod_lt M (by omega : 0 < r)
  simp [balanced]
  omega

theorem balanced_sum (M r : ℕ) (hr : 1 ≤ r) : (balanced M r).sum = M := by
  have hmod := Nat.mod_lt M (by omega : 0 < r)
  have hsub : (r - M % r) + M % r = r := Nat.sub_add_cancel hmod.le
  have hdiv := Nat.mod_add_div M r
  simp only [balanced, List.sum_append, List.sum_replicate, smul_eq_mul]
  nlinarith

theorem balanced_entries (M r : ℕ) (m : ℕ) (hm : m ∈ balanced M r) :
    m = M / r ∨ m = M / r + 1 := by
  simp only [balanced, List.mem_append, List.mem_replicate] at hm
  rcases hm with h | h
  · exact Or.inr h.2
  · exact Or.inl h.2

theorem balanced_positive (M r : ℕ) (hr : 1 ≤ r) (hrM : r ≤ M)
    (m : ℕ) (hm : m ∈ balanced M r) : 1 ≤ m := by
  have hd : 1 ≤ M / r := Nat.div_pos hrM (by omega)
  rcases balanced_entries M r m hm with h | h <;> omega

theorem balanced_bound (M r : ℕ) (hr : 1 ≤ r) (hrM : r ≤ M) (N : ℝ) (hMN : (M : ℝ) ≤ N)
    (m : ℕ) (hm : m ∈ balanced M r) : (m : ℝ) ≤ 2 * N / r := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hqr : ((M / r : ℕ) : ℝ) * r ≤ M := by exact_mod_cast Nat.div_mul_le_self M r
  have hrN : (r : ℝ) ≤ N := (by exact_mod_cast hrM : (r : ℝ) ≤ M).trans hMN
  have hmq : (m : ℝ) ≤ (M / r : ℕ) + 1 := by
    exact_mod_cast (show m ≤ M / r + 1 by rcases balanced_entries M r m hm with h | h <;> omega)
  apply (le_div_iff₀ hrp).2
  have hx := mul_le_mul_of_nonneg_right hmq hrp.le
  nlinarith

theorem balanced_squares (M r : ℕ) (hr : 1 ≤ r) (hrM : r ≤ M) (N : ℝ) (hMN : (M : ℝ) ≤ N) :
    ((balanced M r).map fun m : ℕ => (m : ℝ) ^ 2).sum ≤ 2 * N ^ 2 / r := by
  have hN : 0 ≤ N := (Nat.cast_nonneg M).trans hMN
  have hsum : ((balanced M r).map fun m : ℕ => (m : ℝ)).sum = M := by
    rw [← Nat.cast_list_sum, balanced_sum M r hr]
  calc
    _ ≤ ((balanced M r).map fun m : ℕ => (2 * N / r) * (m : ℝ)).sum := by
      apply List.sum_le_sum
      intro m hm
      nlinarith [mul_le_mul_of_nonneg_right (balanced_bound M r hr hrM N hMN m hm) (Nat.cast_nonneg (α := ℝ) m)]
    _ = (2 * N / r) * M := by rw [List.sum_map_mul_left, hsum]
    _ ≤ (2 * N / r) * N := mul_le_mul_of_nonneg_left hMN (by positivity)
    _ = _ := by ring

end LinearAssemblies
