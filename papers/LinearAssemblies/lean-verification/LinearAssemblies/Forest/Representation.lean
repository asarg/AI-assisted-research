import LinearAssemblies.Forest.PolynomialBounds

set_option autoImplicit false

namespace LinearAssemblies.Forest.Counts

open Polynomial

variable {S : Type} [Fintype S] [DecidableEq S] (c : Counts S)

theorem edgeWeight_sum (i : S) :
    (∑ t : Target S, c.edgeWeight i t) =
      C (c.degree i : ℤ) - C (c.transition i i : ℤ) + C (c.degree i : ℤ) * X := by
  have ha : C (c.degree i : ℤ) = (∑ j, C (c.transition i j : ℤ)) + C (c.terminal i : ℤ) := by
    have he : (c.degree i : ℤ) = (∑ j, (c.transition i j : ℤ)) + c.terminal i := by
      exact_mod_cast c.accounting i
    simpa only [map_add, map_sum] using congrArg (C : ℤ →+* ℤ[X]) he
  have hs : (∑ j, if i = j then (0 : ℤ[X]) else C (c.transition i j : ℤ)) =
      (∑ j, C (c.transition i j : ℤ)) - C (c.transition i i : ℤ) := by
    have he : ∀ j, (if i = j then (0 : ℤ[X]) else C (c.transition i j : ℤ)) =
        C (c.transition i j : ℤ) - if i = j then C (c.transition i j : ℤ) else 0 := by
      intro j; split_ifs <;> simp
    simp_rw [he]
    simp [Finset.sum_sub_distrib]
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, edgeWeight]
  rw [hs, ha]
  ring

/-- The paper's polynomial matrix `(1+X)D-A`. -/
noncomputable def systemMatrix : Matrix S S ℤ[X] := fun i j =>
  (if i = j then (1 + X) * C (c.degree i : ℤ) else 0) - C (c.transition i j : ℤ)

theorem laplacian_eq_systemMatrix : laplacian c.edgeWeight = c.systemMatrix := by
  funext i j
  rw [laplacian_entry]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, edgeWeight_sum]
    simp only [edgeWeight, systemMatrix, if_true, sub_zero]
    ring
  · simp [hij, edgeWeight, systemMatrix]

theorem B_eq_determinant : c.B = c.systemMatrix.det := by
  rw [B, laplacian_eq_systemMatrix]

theorem H_eq_cramer (s : S) :
    c.H s = (c.systemMatrix.updateCol s (fun i => C (c.terminal i : ℤ))).det := by
  rw [H, laplacian_eq_systemMatrix]

/-- Lemma 9, including integrality by the type of the two polynomials. -/
theorem nonnegative_integer_representation (hh : c.Haltable) (s : S) :
    NonnegCoeffs c.B ∧ NonnegCoeffs (c.H s) ∧
    c.B.eval 0 = (c.H s).eval 0 ∧ 1 ≤ c.B.eval 0 ∧
    c.B.natDegree ≤ Fintype.card S ∧
    c.B.eval 1 ≤ (∏ i, (2 * (c.degree i : ℤ) - c.transition i i)) ∧
    c.B.eval 1 ≤ (∏ i, 2 * (c.degree i : ℤ)) :=
  ⟨c.B_nonneg, c.H_nonneg s, c.B_zero_eq_H_zero s, c.B_zero_pos hh,
    c.B_degree, c.B_one_le_product, c.B_one_le_product_twice⟩

theorem twice_le_two_pow (d : ℕ) : 2 * d ≤ 2 ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    cases d with
    | zero => norm_num
    | succ k => rw [pow_succ]; nlinarith

/-- Corollary 9's one-pad bound, from disjoint charging of compatible entries. -/
theorem onePad_coefficient_bound (m : ℕ) (hcost : (∑ i, c.degree i) ≤ m) :
    c.B.eval 1 ≤ (2 : ℤ) ^ m := by
  calc
    c.B.eval 1 ≤ ∏ i, 2 * (c.degree i : ℤ) := c.B_one_le_product_twice
    _ ≤ ∏ i, (2 : ℤ) ^ c.degree i := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _; exact_mod_cast twice_le_two_pow (c.degree i)
    _ = (2 : ℤ) ^ (∑ i, c.degree i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (2 : ℤ) ^ m := pow_le_pow_right₀ (by norm_num) hcost

/-- Corollary 9's bound for arbitrary compatibility rules. -/
theorem general_coefficient_bound (m : ℕ) (hm : 1 ≤ m)
    (hcard : Fintype.card S ≤ m) (hdegree : ∀ i, c.degree i ≤ m) :
    c.B.eval 1 ≤ (2 * (m : ℤ)) ^ m := by
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  calc
    c.B.eval 1 ≤ ∏ i, 2 * (c.degree i : ℤ) := c.B_one_le_product_twice
    _ ≤ ∏ _i : S, 2 * (m : ℤ) := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdegree i) (by norm_num)
    _ = (2 * (m : ℤ)) ^ Fintype.card S := by simp
    _ ≤ (2 * (m : ℤ)) ^ m := pow_le_pow_right₀ (by omega) hcard

end LinearAssemblies.Forest.Counts
