import LinearAssemblies.Probability.TransformBound

set_option autoImplicit false

namespace LinearAssemblies.Probability.UniformGraph

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

theorem tiltedMoment_summable (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (x : ℝ) (hx : 0 ≤ x) (i : S) :
    Summable (fun k : ℕ => (k : ℝ) * g.stoppingMass k i * (1 + x)⁻¹ ^ k) := by
  have hx1 : 0 < 1 + x := by linarith
  have hq : (1 + x)⁻¹ ≤ 1 := (inv_le_one₀ hx1).mpr (by linarith)
  apply Summable.of_nonneg_of_le
    (fun k => by have := g.stoppingMass_nonneg k i; positivity)
    (fun k => mul_le_of_le_one_right
      (mul_nonneg (Nat.cast_nonneg k) (g.stoppingMass_nonneg k i))
      (pow_le_one₀ (inv_nonneg.mpr hx1.le) hq))
    (ext.finite_mean g hh i)

/-- At least a third of the tilted mass lies in the successful window. -/
theorem tiltedMean_lower (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (x : ℝ) (hx : 0 ≤ x) (i : S) (E : Finset ℕ)
    (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2)
    (hgood : 1 - δ ≤ ∑ k ∈ E, g.stoppingMass k i)
    (hwindow : ∀ k ∈ E, a ≤ (k : ℝ))
    (hsurvive : ∀ k ∈ E, δ ≤ (1 + x)⁻¹ ^ k) :
    a / 3 ≤ g.tiltedMoment x i / g.transform x i := by
  let p := fun k => g.stoppingMass k i
  let w := fun k : ℕ => (1 + x)⁻¹ ^ k
  let A := ∑ k ∈ E, p k * w k
  have hx1 : 0 < 1 + x := by linarith
  have hq : (1 + x)⁻¹ ≤ 1 := (inv_le_one₀ hx1).mpr (by linarith)
  have hw0 : ∀ k, 0 ≤ w k := fun k => pow_nonneg (inv_nonneg.mpr hx1.le) k
  have hw1 : ∀ k, w k ≤ 1 := fun _ => pow_le_one₀ (inv_nonneg.mpr hx1.le) hq
  have hp0 : ∀ k, 0 ≤ p k := fun k => g.stoppingMass_nonneg k i
  have hs := g.pgf_summable ext hh (1 + x)⁻¹ (inv_nonneg.mpr hx1.le) hq i
  have hp := (ext.normalized g hh i).summable
  have hA : δ / 2 ≤ A := by
    calc
      δ / 2 ≤ δ * (1 - δ) := by nlinarith
      _ ≤ δ * (∑ k ∈ E, p k) := mul_le_mul_of_nonneg_left hgood hδ
      _ ≤ A := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k hk
        simpa only [w, mul_comm] using mul_le_mul_of_nonneg_left (hsurvive k hk) (hp0 k)
  have hrem : (∑ k ∈ E, p k) - A ≤ 1 - g.transform x i := by
    have he := Summable.sum_le_tsum E
      (fun k (_ : k ∉ E) => sub_nonneg.mpr (mul_le_of_le_one_right (hp0 k) (hw1 k)))
      (hp.sub hs)
    rw [hp.tsum_sub hs, (ext.normalized g hh i).tsum_eq, Finset.sum_sub_distrib] at he
    exact he
  have hphi : g.transform x i ≤ 3 * A := by linarith
  have hmoment : a * A ≤ g.tiltedMoment x i := by
    calc
      a * A ≤ ∑ k ∈ E, (k : ℝ) * p k * w k := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k hk
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hwindow k hk)
          (mul_nonneg (hp0 k) (hw0 k))
      _ ≤ g.tiltedMoment x i := Summable.sum_le_tsum E
        (fun k _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (hp0 k)) (hw0 k))
        (g.tiltedMoment_summable ext hh x hx i)
  apply (le_div_iff₀ (g.transform_pos ext hh x hx i)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hphi ha]

end LinearAssemblies.Probability.UniformGraph

namespace LinearAssemblies.Probability

/-- The alarm choice gives survival at least δ throughout a window ending at 2N. -/
theorem alarm_survival (N σ x δ : ℝ) (hx : 0 ≤ x)
    (hδ : 0 < δ) (hσ : σ ≤ Real.log δ⁻¹) (hchoice : 2 * N * x = σ)
    (k : ℕ) (hk : (k : ℝ) ≤ 2 * N) : δ ≤ (1 + x)⁻¹ ^ k := by
  have hx1 : 0 < 1 + x := by linarith
  have hlog : Real.log (1 + x) ≤ x := by
    simpa using Real.log_le_sub_one_of_pos hx1
  have hprod : (k : ℝ) * Real.log (1 + x) ≤ σ := by
    calc
      (k : ℝ) * Real.log (1 + x) ≤ (k : ℝ) * x :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
      _ ≤ 2 * N * x := mul_le_mul_of_nonneg_right hk hx
      _ = σ := hchoice
  have he : Real.log δ ≤ (k : ℝ) * Real.log (1 + x)⁻¹ := by
    rw [Real.log_inv] at hσ ⊢
    linarith
  have he' := Real.exp_le_exp.mpr he
  rw [Real.exp_log hδ, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hx1)] at he'
  exact he'

end LinearAssemblies.Probability
