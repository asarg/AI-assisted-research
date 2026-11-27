import LinearAssemblies.Probability.External
import LinearAssemblies.Probability.Transient

set_option autoImplicit false

namespace LinearAssemblies.Probability.UniformGraph

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

noncomputable def pgf (q : ℝ) (i : S) : ℝ := ∑' k : ℕ, g.stoppingMass k i * q ^ k
noncomputable def transform (x : ℝ) (i : S) : ℝ := g.pgf (1 + x)⁻¹ i

theorem pgf_summable (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (i : S) :
    Summable (fun k : ℕ => g.stoppingMass k i * q ^ k) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (g.stoppingMass_nonneg k i) (pow_nonneg hq k))
    (fun k => mul_le_of_le_one_right (g.stoppingMass_nonneg k i) (pow_le_one₀ hq hq1))
    (ext.normalized g hh i).summable

theorem pgf_nonneg (q : ℝ) (hq : 0 ≤ q) (i : S) : 0 ≤ g.pgf q i :=
  tsum_nonneg (fun k => mul_nonneg (g.stoppingMass_nonneg k i) (pow_nonneg hq k))

omit [Fintype S] [DecidableEq S] in
theorem pgf_terminal (q : ℝ) (i : S) (hi : g.out i = []) : g.pgf q i = 1 := by
  have hm : ∀ k, g.stoppingMass k i = if k = 0 then 1 else 0 := by
    intro k
    cases k <;> simp [stoppingMass, degree, hi]
  unfold pgf
  rw [tsum_eq_single 0 (fun k hk => by simp [hm, hk])]
  simp [hm]

/-- Weighted first-step equation, proved from the exact stopping masses. -/
theorem pgf_first_step (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (i : S) (hi : g.out i ≠ []) :
    (g.degree i : ℝ) * g.pgf q i = q * ((g.out i).map (g.pgf q)).sum := by
  have hd : g.degree i ≠ 0 := ne_of_gt (List.length_pos_iff.mpr hi)
  have hd' : (g.degree i : ℝ) ≠ 0 := by exact_mod_cast hd
  have hs := g.pgf_summable ext hh q hq hq1 i
  have he : g.pgf q i = ∑' k : ℕ, g.stoppingMass (k + 1) i * q ^ (k + 1) := by
    simpa [pgf, stoppingMass, hd] using hs.tsum_eq_zero_add
  have heach : ∀ k : ℕ, g.stoppingMass (k + 1) i * q ^ (k + 1) =
      ∑ j : S, (q / g.degree i * (g.out i).count j) * (g.stoppingMass k j * q ^ k) := by
    intro k
    rw [stoppingMass, ← sum_count_mul, pow_succ]
    simp only [Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [heach] at he
  rw [Summable.tsum_finsetSum (fun j _ =>
    (g.pgf_summable ext hh q hq hq1 j).mul_left (q / g.degree i * (g.out i).count j))] at he
  simp only [tsum_mul_left] at he
  change g.pgf q i = ∑ j : S, (q / g.degree i * (g.out i).count j) * g.pgf q j at he
  rw [he, ← sum_count_mul, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp
  ring

theorem transform_first_step (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (x : ℝ) (hx : 0 ≤ x) (i : S) (hi : g.out i ≠ []) :
    (1 + x) * g.degree i * g.transform x i =
      ((g.out i).map (g.transform x)).sum := by
  have hx1 : 0 < 1 + x := by linarith
  have hq : (1 + x)⁻¹ ≤ 1 := (inv_le_one₀ hx1).mpr (by linarith)
  have he := g.pgf_first_step ext hh (1 + x)⁻¹ (inv_nonneg.mpr hx1.le) hq i hi
  change (g.degree i : ℝ) * g.transform x i = (1 + x)⁻¹ *
    ((g.out i).map (g.transform x)).sum at he
  calc
    (1 + x) * g.degree i * g.transform x i = (1 + x) * ((g.degree i : ℝ) * g.transform x i) := by ring
    _ = (1 + x) * ((1 + x)⁻¹ * ((g.out i).map (g.transform x)).sum) := by rw [he]
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hx1.ne', one_mul]

omit [Fintype S] [DecidableEq S] in
theorem transform_terminal (x : ℝ) (i : S) (hi : g.out i = []) : g.transform x i = 1 :=
  g.pgf_terminal _ i hi

theorem transient_sum (v : S → ℝ) (hv : ∀ i, g.out i = [] → v i = 1)
    (i : g.TransientState) :
    ((g.out i.val).map v).sum =
      (∑ j, (g.transientCounts.transition i j : ℝ) * v j.val) + g.transientCounts.terminal i := by
  rw [← sum_count_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => g.out j = [])]
  have ht : (∑ j : {j // g.out j = []}, ((g.out i.val).count j.val : ℝ) * v j.val) =
      g.transientCounts.terminal i := by
    have he : ∀ j : {j // g.out j = []}, v j.val = 1 := fun j => hv j.val j.property
    simp_rw [he, mul_one]
    exact_mod_cast count_subtype (fun j => g.out j = []) (g.out i.val)
  rw [ht]
  exact add_comm _ _

theorem transform_count_equation (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (x : ℝ) (hx : 0 ≤ x) (i : g.TransientState) :
    (1 + x) * g.transientCounts.degree i * g.transform x i.val -
      (∑ j, (g.transientCounts.transition i j : ℝ) * g.transform x j.val) =
      g.transientCounts.terminal i := by
  have h := g.transform_first_step ext hh x hx i.val i.property
  rw [g.transient_sum (g.transform x) (g.transform_terminal x) i] at h
  change (1 + x) * g.transientCounts.degree i * g.transform x i.val = _ at h
  linarith

end LinearAssemblies.Probability.UniformGraph
