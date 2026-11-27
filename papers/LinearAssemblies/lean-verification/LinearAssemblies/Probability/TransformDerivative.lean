import LinearAssemblies.Probability.Transform
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false

namespace LinearAssemblies.Probability.UniformGraph

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

noncomputable def tiltedMoment (x : ℝ) (i : S) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * g.stoppingMass k i * (1 + x)⁻¹ ^ k

theorem pgf_hasDerivAt (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (i : S) :
    HasDerivAt (fun q => g.pgf q i)
      (∑' k : ℕ, g.stoppingMass k i * ((k : ℝ) * q ^ (k - 1))) q := by
  have hd : ∀ k : ℕ, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun y => g.stoppingMass k i * y ^ k)
        (g.stoppingMass k i * ((k : ℝ) * y ^ (k - 1))) y := by
    intro k y _
    exact (hasDerivAt_pow k y).const_mul _
  have hb : ∀ k : ℕ, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      ‖g.stoppingMass k i * ((k : ℝ) * y ^ (k - 1))‖ ≤ (k : ℝ) * g.stoppingMass k i := by
    intro k y hy
    have hn := g.stoppingMass_nonneg k i
    have hp := pow_nonneg hy.1.le (k - 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := k - 1) hy.1.le hy.2.le)
      (show (0 : ℝ) ≤ (k : ℝ) * g.stoppingMass k i by positivity)
    nlinarith
  exact hasDerivAt_tsum_of_isPreconnected (ext.finite_mean g hh i)
    isOpen_Ioo (convex_Ioo (0 : ℝ) 1).isPreconnected hd hb
    ⟨hq, hq1⟩ (g.pgf_summable ext hh q hq.le hq1.le i) ⟨hq, hq1⟩

theorem transform_hasDerivAt (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (x : ℝ) (hx : 0 < x) (i : S) :
    HasDerivAt (fun x => g.transform x i) (-g.tiltedMoment x i / (1 + x)) x := by
  have hx1 : 0 < 1 + x := by linarith
  have hq : 0 < (1 + x)⁻¹ := inv_pos.mpr hx1
  have hq1 : (1 + x)⁻¹ < 1 := (inv_lt_one₀ hx1).mpr (by linarith)
  have hd := (g.pgf_hasDerivAt ext hh (1 + x)⁻¹ hq hq1 i).comp x
    (((hasDerivAt_id x).const_add 1).inv hx1.ne')
  change HasDerivAt (fun x => g.transform x i)
    ((∑' k : ℕ, g.stoppingMass k i * ((k : ℝ) * (1 + x)⁻¹ ^ (k - 1))) *
      (-(1 : ℝ) / (1 + x)^2)) x at hd
  convert hd using 1
  rw [← tsum_mul_right, tiltedMoment, neg_div, ← tsum_div_const, ← tsum_neg]
  apply tsum_congr
  intro k
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

end LinearAssemblies.Probability.UniformGraph
