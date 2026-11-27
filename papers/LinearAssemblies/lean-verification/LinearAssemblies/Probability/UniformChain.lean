import LinearAssemblies.Probability.UniformGraph
import LinearAssemblies.Probability.Absorption

set_option autoImplicit false

namespace LinearAssemblies.Probability.UniformGraph

variable {S : Type} [Fintype S] [DecidableEq S]

theorem sum_count_mul (l : List S) (f : S → ℝ) :
    (∑ x, (l.count x : ℝ) * f x) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib,
      List.map_cons, List.sum_cons]
    rw [ih]
    simp [add_comm]

theorem sum_counts (l : List S) : (∑ x, (l.count x : ℝ)) = l.length := by
  simpa using sum_count_mul l (fun _ => (1 : ℝ))

/-- Terminal interfaces are represented by states that absorb on the next chain tick.
Thus chain absorption time is tile length `L`, and `chain.mass k` is `Pr(T=k)`. -/
noncomputable def toChain (g : UniformGraph S) : FiniteChain S where
  step x y := (g.out x).count y / (g.degree x : ℝ)
  stop x := if g.degree x = 0 then 1 else 0
  step_nonneg := by intros; positivity
  stop_nonneg := by intro x; split_ifs <;> norm_num
  row_le_one := by
    intro x
    by_cases hx : g.degree x = 0
    · simp [hx]
    · simp only [hx, if_false, zero_add, ← Finset.sum_div]
      rw [sum_counts]
      change (g.degree x : ℝ) / g.degree x ≤ 1
      have hn : (g.degree x : ℝ) ≠ 0 := by exact_mod_cast hx
      simp [hn]

/-- The chain representation preserves every finite stopping probability exactly. -/
theorem chain_mass_eq (g : UniformGraph S) (k : ℕ) (x : S) :
    g.toChain.mass k x = g.stoppingMass k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change (∑ y, ((g.out x).count y : ℝ) / g.degree x * g.toChain.mass k y) = _
    simp_rw [ih]
    rw [stoppingMass]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, sum_count_mul]

theorem stoppingMass_nonneg (g : UniformGraph S) (k : ℕ) (x : S) :
    0 ≤ g.stoppingMass k x := by
  rw [← chain_mass_eq]
  exact g.toChain.mass_nonneg k x

theorem stoppingMass_partial_sum_le_one (g : UniformGraph S) (k : ℕ) (x : S) :
    ∑ t ∈ Finset.range k, g.stoppingMass t x ≤ 1 := by
  simp_rw [← chain_mass_eq]
  exact g.toChain.partial_mass_le_one k x

end LinearAssemblies.Probability.UniformGraph
