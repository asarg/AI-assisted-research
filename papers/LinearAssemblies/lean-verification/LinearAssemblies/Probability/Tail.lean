import LinearAssemblies.Probability.External

set_option autoImplicit false

namespace LinearAssemblies.Probability.FiniteChain

variable {S : Type} [Fintype S] (c : FiniteChain S)

/-- Probability of surviving strictly beyond attachment index n for the graph chain. -/
def survival : ℕ → S → ℝ
  | 0, i => ∑ j, c.step i j
  | n + 1, i => ∑ j, c.step i j * survival n j

theorem survival_nonneg (n : ℕ) (i : S) : 0 ≤ c.survival n i := by
  induction n generalizing i with
  | zero => exact Finset.sum_nonneg (fun j _ => c.step_nonneg i j)
  | succ n ih => exact Finset.sum_nonneg (fun j _ => mul_nonneg (c.step_nonneg i j) (ih j))

theorem survival_le_one (n : ℕ) (i : S) : c.survival n i ≤ 1 := by
  induction n generalizing i with
  | zero => exact c.step_sum_le_one i
  | succ n ih =>
    calc
      c.survival (n + 1) i ≤ ∑ j, c.step i j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_of_le_one_right (c.step_nonneg i j) (ih j)
      _ ≤ 1 := c.step_sum_le_one i

theorem partial_mass_step (n : ℕ) (i : S) :
    (∑ k ∈ Finset.range (n + 1), c.mass k i) =
      c.stop i + ∑ j, c.step i j * (∑ k ∈ Finset.range n, c.mass k j) := by
  rw [Finset.sum_range_succ']
  simp only [mass]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  ring

theorem survival_add_partial (hrow : ∀ i, c.stop i + ∑ j, c.step i j = 1)
    (n : ℕ) (i : S) : c.survival n i + ∑ k ∈ Finset.range (n + 1), c.mass k i = 1 := by
  induction n generalizing i with
  | zero => simpa [survival, mass, add_comm] using hrow i
  | succ n ih =>
    rw [partial_mass_step, survival]
    have he : (∑ j, c.step i j * c.survival n j) +
        (∑ j, c.step i j * (∑ k ∈ Finset.range (n + 1), c.mass k j)) = ∑ j, c.step i j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_add, ih, mul_one]
    linarith [hrow i]

theorem survival_eq_tail (hrow : ∀ i, c.stop i + ∑ j, c.step i j = 1)
    (hnorm : ∀ i, HasSum (fun k => c.mass k i) 1) (n : ℕ) (i : S) :
    c.survival n i = ∑' k : ℕ, c.mass (k + (n + 1)) i := by
  have hs := (hnorm i).summable.sum_add_tsum_nat_add (n + 1)
  rw [(hnorm i).tsum_eq] at hs
  linarith [c.survival_add_partial hrow n i]

/-- Markov's inequality for the stopping count, proved directly from its convergent series. -/
theorem survival_markov (hrow : ∀ i, c.stop i + ∑ j, c.step i j = 1)
    (hnorm : ∀ i, HasSum (fun k => c.mass k i) 1)
    (hmean : ∀ i, Summable (fun k : ℕ => (k : ℝ) * c.mass k i)) (n : ℕ) (i : S) :
    ((n + 1 : ℕ) : ℝ) * c.survival n i ≤ ∑' k : ℕ, (k : ℝ) * c.mass k i := by
  rw [c.survival_eq_tail hrow hnorm, ← tsum_mul_left]
  have ht := (summable_nat_add_iff (n + 1)).mpr (hmean i)
  have hp := (summable_nat_add_iff (n + 1)).mpr (hnorm i).summable
  calc
    (∑' k : ℕ, ((n + 1 : ℕ) : ℝ) * c.mass (k + (n + 1)) i)
        ≤ ∑' k : ℕ, ((k + (n + 1) : ℕ) : ℝ) * c.mass (k + (n + 1)) i := by
      apply Summable.tsum_le_tsum
      · intro k
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_add_left (n + 1) k))
          (c.mass_nonneg _ i)
      · exact hp.mul_left _
      · exact ht
    _ ≤ ∑' k : ℕ, (k : ℝ) * c.mass k i := by
      have he := (hmean i).sum_add_tsum_nat_add (n + 1)
      have hn : 0 ≤ ∑ k ∈ Finset.range (n + 1), (k : ℝ) * c.mass k i :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg k) (c.mass_nonneg k i))
      linarith

/-- Restart contraction, obtained by iterating the positive transition operator. -/
theorem survival_shift_le (K : ℕ) (hK : 1 ≤ K) (a : ℝ)
    (hbound : ∀ i, c.survival (K - 1) i ≤ a) (n : ℕ) (i : S) :
    c.survival (n + K) i ≤ a * c.survival n i := by
  induction n generalizing i with
  | zero =>
    simp only [zero_add]
    rw [show K = (K - 1) + 1 by omega, survival]
    calc
      (∑ j, c.step i j * c.survival (K - 1) j) ≤ ∑ j, c.step i j * a :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hbound j) (c.step_nonneg i j))
      _ = a * c.survival 0 i := by rw [survival, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  | succ n ih =>
    rw [show n + 1 + K = (n + K) + 1 by omega, survival, survival, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left (ih j) (c.step_nonneg i j)

theorem survival_blocks (K : ℕ) (hK : 1 ≤ K) (a : ℝ) (ha : 0 ≤ a)
    (hbound : ∀ i, c.survival (K - 1) i ≤ a) (j : ℕ) (i : S) :
    c.survival (K * j) i ≤ a ^ j := by
  induction j with
  | zero => simpa using c.survival_le_one 0 i
  | succ j ih =>
    rw [Nat.mul_add, Nat.mul_one, pow_succ]
    calc
      c.survival (K * j + K) i ≤ a * c.survival (K * j) i :=
        c.survival_shift_le K hK a hbound _ i
      _ ≤ a * a ^ j := mul_le_mul_of_nonneg_left ih ha
      _ = a ^ j * a := mul_comm _ _

end LinearAssemblies.Probability.FiniteChain

namespace LinearAssemblies.Probability.UniformGraph

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

noncomputable def tail (n : ℕ) (i : S) : ℝ :=
  ∑' k : ℕ, g.stoppingMass (k + (n + 1)) i

theorem chain_row_total (i : S) : g.toChain.stop i + ∑ j, g.toChain.step i j = 1 := by
  by_cases hi : g.degree i = 0
  · simp [toChain, hi]
  · simp only [toChain, hi, if_false, zero_add, ← Finset.sum_div]
    rw [sum_counts]
    change (g.degree i : ℝ) / g.degree i = 1
    exact div_self (by exact_mod_cast hi)

theorem tail_eq_survival (ext : FiniteAbsorptionLaw) (hh : g.Haltable) (n : ℕ) (i : S) :
    g.tail n i = g.toChain.survival n i := by
  have hnorm : ∀ i, HasSum (fun k => g.toChain.mass k i) 1 := by
    intro i; simpa only [chain_mass_eq] using ext.normalized g hh i
  simpa only [chain_mass_eq] using (g.toChain.survival_eq_tail (g.chain_row_total) hnorm n i).symm

/-- Lemma 7, proved from the complete transition equations and finite mean.
No independent restart or Markov-inequality contract is assumed. -/
theorem uniform_block_tail (ext : FiniteAbsorptionLaw) (hh : g.Haltable)
    (M : ℕ) (hM : 1 ≤ M) (hmean : ∀ i, g.expected i ≤ 2 * (M : ℝ))
    (j : ℕ) (i : S) : g.tail (4 * M * j) i ≤ (1 / 2 : ℝ) ^ j := by
  have hnorm : ∀ i, HasSum (fun k => g.toChain.mass k i) 1 := by
    intro i; simpa only [chain_mass_eq] using ext.normalized g hh i
  have hsum : ∀ i, Summable (fun k : ℕ => (k : ℝ) * g.toChain.mass k i) := by
    intro i; simpa only [chain_mass_eq] using ext.finite_mean g hh i
  have hK : 1 ≤ 4 * M := by omega
  have hbound : ∀ i, g.toChain.survival (4 * M - 1) i ≤ (1 / 2 : ℝ) := by
    intro i
    have h := g.toChain.survival_markov g.chain_row_total hnorm hsum (4 * M - 1) i
    rw [Nat.sub_add_cancel hK] at h
    simp only [chain_mass_eq] at h
    change ((4 * M : ℕ) : ℝ) * g.toChain.survival (4 * M - 1) i ≤ g.expected i at h
    have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    apply (mul_le_mul_left (show (0 : ℝ) < (4 * M : ℕ) by exact_mod_cast (show 0 < 4 * M by omega))).mp
    push_cast at h ⊢
    linarith [hmean i]
  rw [g.tail_eq_survival ext hh]
  exact g.toChain.survival_blocks (4 * M) hK (1 / 2) (by norm_num) hbound j i

end LinearAssemblies.Probability.UniformGraph
