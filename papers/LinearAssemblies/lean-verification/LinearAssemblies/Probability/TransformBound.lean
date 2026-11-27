import LinearAssemblies.Probability.RationalTransform
import LinearAssemblies.Forest.WeightedDegree
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

namespace LinearAssemblies.Probability.UniformGraph

open LinearAssemblies.Forest

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

/-- Nonnegative numerator coefficients turn the transform derivative into a degree lower bound. -/
theorem logarithmic_derivative_bound (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (x : ℝ) (hx : 0 < x) (s : g.TransientState) :
    x / (1 + x) * (g.tiltedMoment x s.val / g.transform x s.val) ≤
      x * evalReal x g.transientCounts.B.derivative / evalReal x g.transientCounts.B := by
  let c := g.transientCounts
  have hc := g.transient_haltable hh
  have hb := c.B_real_pos hc x hx.le
  have hn := c.H_real_pos hc s x hx.le
  have ht := g.transform_pos ext hh x hx.le s.val
  have hd := ((evalReal_hasDerivAt (c.H s) x).log hn.ne').sub
    ((evalReal_hasDerivAt c.B x).log hb.ne')
  have he : (fun y => Real.log (g.transform y s.val)) =ᶠ[nhds x]
      (fun y => Real.log (evalReal y (c.H s)) - Real.log (evalReal y c.B)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [g.transform_eq_ratio ext hh y hy.le s]
    exact Real.log_div (c.H_real_pos hc s y hy.le).ne' (c.B_real_pos hc y hy.le).ne'
  have hder := ((g.transform_hasDerivAt ext hh x hx s.val).log ht.ne').unique
    (hd.congr_of_eventuallyEq he)
  have hh' : 0 ≤ evalReal x (c.H s).derivative / evalReal x (c.H s) :=
    div_nonneg (evalReal_nonneg (derivative_nonneg (c.H_nonneg s)) x hx.le) hn.le
  have hi : g.tiltedMoment x s.val / (1 + x) / g.transform x s.val ≤
      evalReal x c.B.derivative / evalReal x c.B := by
    rw [neg_div, neg_div] at hder
    linarith
  have hm := mul_le_mul_of_nonneg_left hi hx.le
  convert hm using 1 <;> dsimp [c] <;> ring

end LinearAssemblies.Probability.UniformGraph
