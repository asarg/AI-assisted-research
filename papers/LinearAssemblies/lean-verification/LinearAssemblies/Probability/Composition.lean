import LinearAssemblies.Probability.External

set_option autoImplicit false

namespace LinearAssemblies.Probability.UniformGraph

variable {S T U : Type} [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U]

noncomputable def next (g : UniformGraph S) (f : S → ℝ) (i : S) : ℝ :=
  ∑ j, ((g.out i).count j : ℝ) / g.degree i * f j

theorem next_eq_list (g : UniformGraph S) (f : S → ℝ) (i : S) :
    g.next f i = ((g.out i).map f).sum / g.degree i := by
  simp only [next, div_mul_eq_mul_div, ← Finset.sum_div, sum_count_mul]

theorem mass_succ_eq_next (g : UniformGraph S) (n : ℕ) (i : S) :
    g.stoppingMass (n + 1) i = g.next (g.stoppingMass n) i := by
  rw [← g.chain_mass_eq, FiniteChain.mass]
  simp only [chain_mass_eq]
  rfl

omit [Fintype S] [DecidableEq S] in
theorem stoppingMass_terminal (g : UniformGraph S) (i : S) (hi : g.out i = []) (n : ℕ) :
    g.stoppingMass n i = if n = 0 then 1 else 0 := by
  cases n <;> simp [stoppingMass, degree, hi]

/-- State maps preserve stopping probabilities when they preserve terminality and each transition row. -/
structure Simulation (g : UniformGraph S) (h : UniformGraph T) (f : S → T) : Prop where
  terminal : ∀ i, h.out (f i) = [] ↔ g.out i = []
  row : ∀ i v, h.next v (f i) = g.next (v ∘ f) i

theorem simulation_mass (g : UniformGraph S) (h : UniformGraph T) (f : S → T)
    (hs : Simulation g h f) (n : ℕ) (i : S) :
    h.stoppingMass n (f i) = g.stoppingMass n i := by
  induction n generalizing i with
  | zero => simp only [stoppingMass, degree, List.length_eq_zero_iff, hs.terminal]
  | succ n ih =>
    rw [mass_succ_eq_next, hs.row, mass_succ_eq_next]
    simp only [next, Function.comp_def, ih]

def convolution (p q : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), p k * q (n - k)

omit [Fintype S] [DecidableEq S] in
theorem convolution_terminal (g : UniformGraph S) (i : S) (hi : g.out i = [])
    (q : ℕ → ℝ) (n : ℕ) : convolution (fun k => g.stoppingMass k i) q n = q n := by
  simp [convolution, g.stoppingMass_terminal i hi, ite_mul]

/-- The Cauchy convolution satisfies the same nonterminal first-step recurrence. -/
theorem convolution_step (g : UniformGraph S) (i : S) (hi : g.out i ≠ [])
    (q : ℕ → ℝ) (n : ℕ) :
    convolution (fun k => g.stoppingMass k i) q (n + 1) =
      g.next (fun j => convolution (fun k => g.stoppingMass k j) q n) i := by
  have hz : g.stoppingMass 0 i = 0 := by simp [stoppingMass, degree, List.length_eq_zero_iff, hi]
  unfold convolution
  rw [Finset.sum_range_succ']
  simp only [hz, zero_mul, add_zero, Nat.add_sub_add_right, mass_succ_eq_next, next]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Sequential blocks have the convolution of their stopping distributions.
The row hypotheses are later discharged by the concrete fresh-label compiler. -/
theorem sequential_mass (g : UniformGraph S) (h : UniformGraph T) (j : UniformGraph U)
    (exit : S) (start : T) (left : S → U) (right : T → U)
    (hexit : g.out exit = []) (hunique : ∀ x, g.out x = [] → x = exit)
    (hjoin : left exit = right start) (hright : Simulation h j right)
    (hleft_term : ∀ x, x ≠ exit → j.out (left x) ≠ [])
    (hleft_row : ∀ x, x ≠ exit → ∀ v, j.next v (left x) = g.next (v ∘ left) x)
    (n : ℕ) (x : S) :
    j.stoppingMass n (left x) =
      convolution (fun k => g.stoppingMass k x) (fun k => h.stoppingMass k start) n := by
  induction n generalizing x with
  | zero =>
    by_cases hx : x = exit
    · subst x
      rw [hjoin, simulation_mass h j right hright, convolution_terminal g exit hexit]
    · have hg : g.out x ≠ [] := fun he => hx (hunique x he)
      simp [convolution, stoppingMass, degree, List.length_eq_zero_iff, hg, hleft_term x hx]
  | succ n ih =>
    by_cases hx : x = exit
    · subst x
      rw [hjoin, simulation_mass h j right hright, convolution_terminal g exit hexit]
    · have hg : g.out x ≠ [] := fun he => hx (hunique x he)
      rw [mass_succ_eq_next, hleft_row x hx, convolution_step g x hg]
      simp only [next, Function.comp_def, ih]

end LinearAssemblies.Probability.UniformGraph
