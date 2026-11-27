import LinearAssemblies.Forest.Roots

set_option autoImplicit false

namespace LinearAssemblies.Forest

variable {S R : Type} [Fintype S] [DecidableEq S] [CommRing R]

def edgeRow (i : S) (t : Target S) : S → R := incidence R (forget (fun _ => t)) i

/-- Weighted sum of edge-incidence rows; a self-loop contributes the zero row. -/
def laplacian (w : S → Target S → R) : Matrix S S R :=
  fun i j => ∑ t, w i t * edgeRow i t j

def weight (w : S → Target S → R) (f : S → Target S) : R := ∏ i, w i (f i)

theorem laplacian_entry (w : S → Target S → R) (i j : S) :
    laplacian w i j = (if i = j then ∑ t, w i t else 0) - w i (.inl j) := by
  simp only [laplacian, edgeRow, incidence, forget, Fintype.sum_sum_type, Fintype.sum_bool]
  by_cases h : i = j
  · subst j
    simp [mul_sub, Finset.sum_sub_distrib]
    ring
  · simp [h]

noncomputable def forestSum (w : S → Target S → R) : R := by
  classical
  exact ∑ f : S → Target S, if Rooted (forget f) then weight w f else 0

noncomputable def terminationSum (w : S → Target S → R) (s : S) : R := by
  classical
  exact ∑ f : S → Target S,
    if Rooted (forget f) ∧ Leads f false s then weight w f else 0

/-- Full multilinear row expansion, before the zero/one incidence determinant is used. -/
theorem det_laplacian_expansion (w : S → Target S → R) :
    (laplacian w).det = ∑ f : S → Target S, weight w f * (incidence R (forget f)).det := by
  have he : laplacian w = fun i => ∑ t, w i t • edgeRow i t := by
    ext i j
    simp [laplacian, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  change (Matrix.detRowAlternating.toMultilinearMap
    (fun i => ∑ t, w i t • edgeRow i t)) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro f _
  change (Matrix.of (fun i j => w i (f i) * incidence R (forget f) i j)).det = _
  exact Matrix.det_mul_column _ _

/-- The denominator's directed-forest expansion, proved without a matrix-tree axiom. -/
theorem det_laplacian (w : S → Target S → R) : (laplacian w).det = forestSum w := by
  classical
  rw [det_laplacian_expansion]
  simp only [forestSum, det_incidence]
  apply Finset.sum_congr rfl
  intro f _
  split_ifs <;> simp

def redirectedLaplacian (w : S → Target S → R) (s : S) : Matrix S S R :=
  fun i j => ∑ t, w i t * incidence R (redirect (fun _ => t) s) i j

theorem det_redirected_expansion (w : S → Target S → R) (s : S) :
    (redirectedLaplacian w s).det =
      ∑ f : S → Target S, weight w f * (incidence R (redirect f s)).det := by
  have he : redirectedLaplacian w s = fun i =>
      ∑ t, w i t • incidence R (redirect (fun _ => t) s) i := by
    ext i j
    simp [redirectedLaplacian, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  change (Matrix.detRowAlternating.toMultilinearMap
    (fun i => ∑ t, w i t • incidence R (redirect (fun _ => t) s) i)) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro f _
  change (Matrix.of (fun i j => w i (f i) * incidence R (redirect f s) i j)).det = _
  exact Matrix.det_mul_column _ _

/-- Redirecting termination edges subtracts their weights from column s. -/
theorem redirected_eq_update (w : S → Target S → R) (s : S) :
    redirectedLaplacian w s = (laplacian w).updateCol s
      (fun i => laplacian w i s - w i (.inr false)) := by
  ext i j
  simp only [redirectedLaplacian, laplacian, Fintype.sum_sum_type, Fintype.sum_bool,
    edgeRow, incidence, forget, redirect, Matrix.updateCol_apply]
  by_cases hj : j = s
  · subst j
    by_cases hi : i = s <;> simp [hi] <;> ring
  · have hs : s ≠ j := Ne.symm hj
    simp [hj, hs]

/-- The redirection determinant is B-H, directly by column linearity. -/
theorem det_redirected_sub (w : S → Target S → R) (s : S) :
    (redirectedLaplacian w s).det = (laplacian w).det -
      ((laplacian w).updateCol s (fun i => w i (.inr false))).det := by
  rw [redirected_eq_update]
  have he := Matrix.det_updateCol_add (laplacian w) s
    (fun i => laplacian w i s) (fun i => -w i (.inr false))
  have hn := Matrix.det_updateCol_smul (laplacian w) s (-1 : R) (fun i => w i (.inr false))
  rw [neg_one_smul, neg_one_mul] at hn
  change ((laplacian w).updateCol s (fun i => -w i (.inr false))).det =
    -((laplacian w).updateCol s (fun i => w i (.inr false))).det at hn
  rw [hn, Matrix.updateCol_eq_self] at he
  simpa only [sub_eq_add_neg] using he

/-- The numerator counts exactly the rooted forests in which s reaches termination. -/
theorem det_updateCol_termination (w : S → Target S → R) (s : S) :
    ((laplacian w).updateCol s (fun i => w i (.inr false))).det = terminationSum w s := by
  classical
  have hd := det_redirected_sub w s
  rw [det_laplacian_expansion, det_redirected_expansion] at hd
  have ht : (∑ f : S → Target S, weight w f * (incidence R (forget f)).det) -
      (∑ f : S → Target S, weight w f * (incidence R (redirect f s)).det) = terminationSum w s := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro f _
    rw [det_incidence, det_incidence]
    by_cases hf : Rooted (forget f)
    · rcases leads_of_terminates (hf s) with hs | hs
      · have hn : ¬Leads f true s := by
          intro hh
          have he := leads_unique hs hh
          cases he
        simp [rooted_redirect_iff, hf, hs, hn]
      · have hn : ¬Leads f false s := by
          intro hh
          have he := leads_unique hh hs
          cases he
        simp [rooted_redirect_iff, hf, hs, hn]
    · simp [rooted_redirect_iff, hf]
  linear_combination ht + hd

end LinearAssemblies.Forest
