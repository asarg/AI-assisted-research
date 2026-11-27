import LinearAssemblies.Probability.TransformDerivative
import LinearAssemblies.Forest.RealPolynomial

set_option autoImplicit false

namespace LinearAssemblies.Probability.UniformGraph

open LinearAssemblies.Forest

variable {S : Type} [Fintype S] [DecidableEq S]

theorem cramer_of_solution (M : Matrix S S ℝ) (v b : S → ℝ)
    (h : M.mulVec v = b) (s : S) : (M.updateCol s b).det = M.det * v s := by
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, ← h,
    Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec]
  rfl

variable (g : UniformGraph S)

theorem transform_matrix_equation (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (x : ℝ) (hx : 0 ≤ x) :
    (g.transientCounts.systemMatrix.map (evalReal x)).mulVec
      (fun i => g.transform x i.val) = fun i => (g.transientCounts.terminal i : ℝ) := by
  funext i
  have h := g.transform_count_equation ext hh x hx i
  change (∑ j, evalReal x (g.transientCounts.systemMatrix i j) * g.transform x j.val) = _
  simp only [Counts.systemMatrix, map_sub, map_mul, map_add, map_one, evalReal_X, evalReal_C]
  simp only [apply_ite (evalReal x), map_zero, sub_mul, Finset.sum_sub_distrib,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simpa only [map_mul, map_add, map_one, evalReal_X, evalReal_C, Int.cast_natCast] using h

/-- The forest polynomials represent the transform of the actual stopping law. -/
theorem transform_eq_ratio (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (x : ℝ) (hx : 0 ≤ x) (s : g.TransientState) :
    g.transform x s.val = evalReal x (g.transientCounts.H s) / evalReal x g.transientCounts.B := by
  have h := cramer_of_solution _ _ _ (g.transform_matrix_equation ext hh x hx) s
  have hb : evalReal x g.transientCounts.B =
      (g.transientCounts.systemMatrix.map (evalReal x)).det := by
    rw [Counts.B_eq_determinant, RingHom.map_det]
    rfl
  have ht : evalReal x (g.transientCounts.H s) =
      ((g.transientCounts.systemMatrix.map (evalReal x)).updateCol s
        (fun i => (g.transientCounts.terminal i : ℝ))).det := by
    rw [Counts.H_eq_cramer, RingHom.map_det]
    change ((g.transientCounts.systemMatrix.updateCol s
      (fun i => Polynomial.C (g.transientCounts.terminal i : ℤ))).map (evalReal x)).det = _
    rw [Matrix.map_updateCol]
    simp only [Function.comp_def, evalReal_C, Int.cast_natCast]
  rw [← hb, ← ht] at h
  exact (eq_div_iff (g.transientCounts.B_real_pos (g.transient_haltable hh) x hx).ne').mpr
    (by simpa [mul_comm] using h.symm)

theorem transform_pos (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (x : ℝ) (hx : 0 ≤ x) (s : S) : 0 < g.transform x s := by
  by_cases hs : g.out s = []
  · rw [g.transform_terminal x s hs]; norm_num
  · rw [g.transform_eq_ratio ext hh x hx ⟨s, hs⟩]
    exact div_pos (g.transientCounts.H_real_pos (g.transient_haltable hh) ⟨s, hs⟩ x hx)
      (g.transientCounts.B_real_pos (g.transient_haltable hh) x hx)

end LinearAssemblies.Probability.UniformGraph
