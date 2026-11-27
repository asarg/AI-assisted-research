import LinearAssemblies.Forest.Counts
import LinearAssemblies.Forest.Expansion

set_option autoImplicit false

namespace LinearAssemblies.Forest

open Polynomial

def NonnegCoeffs (p : ℤ[X]) : Prop := ∀ k, 0 ≤ p.coeff k

theorem nonnegCoeffs_zero : NonnegCoeffs 0 := by intro k; simp
theorem nonnegCoeffs_one : NonnegCoeffs 1 := by intro k; simp only [coeff_one]; split_ifs <;> norm_num

theorem nonnegCoeffs_mul {p q : ℤ[X]} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p * q) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hp ij.1) (hq ij.2))

theorem nonnegCoeffs_sum {ι : Type} (s : Finset ι) (p : ι → ℤ[X])
    (hp : ∀ i ∈ s, NonnegCoeffs (p i)) : NonnegCoeffs (∑ i ∈ s, p i) := by
  intro k
  rw [finset_sum_coeff]
  exact Finset.sum_nonneg (fun i hi => hp i hi k)

theorem nonnegCoeffs_prod {ι : Type} (s : Finset ι) (p : ι → ℤ[X])
    (hp : ∀ i ∈ s, NonnegCoeffs (p i)) : NonnegCoeffs (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nonnegCoeffs_one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact nonnegCoeffs_mul (hp i (by simp)) (ih (fun j hj => hp j (by simp [hj])))

namespace Counts

variable {S : Type} [Fintype S] [DecidableEq S] (c : Counts S)

noncomputable def B : ℤ[X] := (laplacian c.edgeWeight).det
noncomputable def H (s : S) : ℤ[X] :=
  ((laplacian c.edgeWeight).updateCol s (fun i => C (c.terminal i : ℤ))).det

theorem B_eq_forest : c.B = forestSum c.edgeWeight := det_laplacian _
theorem H_eq_forest (s : S) : c.H s = terminationSum c.edgeWeight s := det_updateCol_termination _ _

theorem edgeWeight_nonneg (i : S) (t : Target S) : NonnegCoeffs (c.edgeWeight i t) := by
  intro k
  cases t with
  | inl j =>
    by_cases hi : i = j
    · simp [edgeWeight, hi]
    · simp only [edgeWeight, hi, if_false, coeff_C]; split_ifs <;> positivity
  | inr b =>
    cases b with
    | false => simp only [edgeWeight, coeff_C]; split_ifs <;> positivity
    | true => simp only [edgeWeight, coeff_C_mul, coeff_X]; split_ifs <;> positivity

theorem weight_nonneg (f : S → Target S) : NonnegCoeffs (weight c.edgeWeight f) :=
  nonnegCoeffs_prod _ _ (fun i _ => c.edgeWeight_nonneg i (f i))

theorem B_nonneg : NonnegCoeffs c.B := by
  classical
  rw [B_eq_forest]
  apply nonnegCoeffs_sum
  intro f _
  split_ifs
  · exact c.weight_nonneg f
  · exact nonnegCoeffs_zero

theorem H_nonneg (s : S) : NonnegCoeffs (c.H s) := by
  classical
  rw [H_eq_forest]
  apply nonnegCoeffs_sum
  intro f _
  split_ifs
  · exact c.weight_nonneg f
  · exact nonnegCoeffs_zero

theorem B_degree : c.B.natDegree ≤ Fintype.card S := by
  classical
  rw [B_eq_forest]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro f _
  split_ifs
  · calc
      (weight c.edgeWeight f).natDegree ≤ ∑ i, (c.edgeWeight i (f i)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : S, 1 := Finset.sum_le_sum (fun i _ => c.edgeWeight_degree i (f i))
      _ = Fintype.card S := by simp
  · simp

theorem weight_eval_nonneg (f : S → Target S) (x : ℤ) (hx : 0 ≤ x) :
    0 ≤ (weight c.edgeWeight f).eval x := by
  rw [weight, Polynomial.eval_prod]
  exact Finset.prod_nonneg (fun i _ => c.edgeWeight_eval_nonneg i (f i) x hx)

/-- Coefficient sum bound with self-loops subtracted, as in Lemma 9. -/
theorem B_one_le_product : c.B.eval 1 ≤ ∏ i, (2 * (c.degree i : ℤ) - c.transition i i) := by
  classical
  rw [B_eq_forest, forestSum, Polynomial.eval_finset_sum]
  calc
    (∑ f : S → Target S, (if Rooted (forget f) then weight c.edgeWeight f else 0).eval 1)
        ≤ ∑ f : S → Target S, (weight c.edgeWeight f).eval 1 := by
      apply Finset.sum_le_sum
      intro f _
      split_ifs <;> simp only [eval_zero, le_refl]
      exact c.weight_eval_nonneg f 1 (by norm_num)
    _ = ∏ i, ∑ t : Target S, (c.edgeWeight i t).eval 1 := by
      simp only [weight, Polynomial.eval_prod]
      exact (Fintype.prod_sum (fun (i : S) (t : Target S) => (c.edgeWeight i t).eval 1)).symm
    _ = ∏ i, (2 * (c.degree i : ℤ) - c.transition i i) := by simp_rw [edgeWeight_one_sum]

theorem B_one_le_product_twice : c.B.eval 1 ≤ ∏ i, 2 * (c.degree i : ℤ) := by
  apply le_trans c.B_one_le_product
  apply Finset.prod_le_prod
  · intro i _
    rw [← edgeWeight_one_sum]
    exact Finset.sum_nonneg (fun t _ => c.edgeWeight_eval_nonneg i t 1 (by norm_num))
  · intro i _
    have h : (0 : ℤ) ≤ c.transition i i := by positivity
    linarith

theorem weight_zero_of_alarm {f : S → Target S} {s : S} (hs : Leads f true s) :
    (weight c.edgeWeight f).eval 0 = 0 := by
  obtain ⟨i, hi⟩ := hs.has_root
  rw [weight, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi, edgeWeight]

/-- At zero alarm rate every nonzero forest contributes to H as well as B. -/
theorem B_zero_eq_H_zero (s : S) : c.B.eval 0 = (c.H s).eval 0 := by
  classical
  rw [B_eq_forest, H_eq_forest, forestSum, terminationSum,
    Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : Rooted (forget f)
  · rcases leads_of_terminates (hf s) with hs | hs
    · simp [hf, hs]
    · have hz := c.weight_zero_of_alarm hs
      by_cases ht : Leads f false s <;> simp [hf, ht, hz]
  · simp [hf]

/-- A shortest-path forest has a positive integer contribution at x=0. -/
theorem B_zero_pos (hh : c.Haltable) : 1 ≤ c.B.eval 0 := by
  classical
  obtain ⟨f, hf, ha, hb, hn⟩ := c.positive_forest hh
  have hp : 0 < (weight c.edgeWeight f).eval 0 := by
    rw [weight, Polynomial.eval_prod]
    apply Finset.prod_pos
    intro i _
    cases hi : f i with
    | inl j =>
      obtain ⟨hne, hpos⟩ := ha i j hi
      simpa [edgeWeight, hne] using (show (0 : ℤ) < c.transition i j by exact_mod_cast hpos)
    | inr b =>
      cases b with
      | false => simpa [edgeWeight] using (show (0 : ℤ) < c.terminal i by exact_mod_cast hb i hi)
      | true => exact False.elim (hn i hi)
  have hs : (weight c.edgeWeight f).eval 0 ≤ c.B.eval 0 := by
    rw [B_eq_forest, forestSum, Polynomial.eval_finset_sum]
    have hh' := Finset.single_le_sum (s := Finset.univ)
      (f := fun g : S → Target S => (if Rooted (forget g) then weight c.edgeWeight g else 0).eval 0)
      (fun g _ => by
        dsimp only
        split_ifs
        · exact c.weight_eval_nonneg g 0 le_rfl
        · simp) (Finset.mem_univ f)
    simpa [hf] using hh'
  omega

end Counts
end LinearAssemblies.Forest
