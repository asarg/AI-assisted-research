import LinearAssemblies.Probability.Composition
import LinearAssemblies.Probability.Tail

set_option autoImplicit false

namespace LinearAssemblies.Probability

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The stopping count of a sequence of independent discrete variables, defined by Cauchy convolution. -/
def independentSum : List (ℕ → ℝ) → ℕ → ℝ
  | [] => fun n => if n = 0 then 1 else 0
  | p :: ps => UniformGraph.convolution p (independentSum ps)

def eventMass (p : ℕ → ℝ) (P : ℕ → Prop) : ℝ :=
  ∑' n, if P n then p n else 0

def magnitudeTail (p : ℕ → ℝ) (X : ℕ → ℝ) (u : ℝ) : ℝ :=
  eventMass p (fun n => u ≤ |X n|)

def deviation (p : ℕ → ℝ) (μ t : ℝ) : ℝ :=
  eventMass p (fun n => t < |(n : ℝ) - μ|)

theorem event_summable (p : ℕ → ℝ) (hp : Summable p) (P : ℕ → Prop) :
    Summable (fun n => if P n then p n else 0) := by
  simpa only [Set.indicator, Set.mem_setOf_eq] using hp.indicator {n | P n}

theorem event_mono (p : ℕ → ℝ) (hn : ∀ n, 0 ≤ p n) (hs : Summable p)
    (P Q : ℕ → Prop) (hPQ : ∀ n, P n → Q n) : eventMass p P ≤ eventMass p Q := by
  apply Summable.tsum_le_tsum _ (event_summable p hs P) (event_summable p hs Q)
  intro n
  by_cases hP : P n
  · simp only [if_pos hP, if_pos (hPQ n hP), le_refl]
  · simp only [if_neg hP]; split_ifs <;> simp_all

theorem event_le_one (p : ℕ → ℝ) (hn : ∀ n, 0 ≤ p n) (hs : HasSum p 1)
    (P : ℕ → Prop) : eventMass p P ≤ 1 := by
  rw [← hs.tsum_eq]
  apply Summable.tsum_le_tsum _ (event_summable p hs.summable P) hs.summable
  intro n
  split_ifs <;> simp_all

theorem event_nat_tail (p : ℕ → ℝ) (hs : Summable p) (k : ℕ) :
    eventMass p (fun n => k < n) = ∑' n, p (n + (k + 1)) := by
  classical
  have hh := (event_summable p hs (fun n => k < n)).sum_add_tsum_nat_add (k + 1)
  have hz : (∑ n ∈ Finset.range (k + 1), @ite ℝ (k < n) (Classical.propDecidable (k < n)) (p n) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' := Finset.mem_range.mp hn
    simp only [if_neg (by omega : ¬k < n)]
  rw [hz, zero_add] at hh
  unfold eventMass
  rw [← hh]
  apply tsum_congr
  intro n
  simp only [if_pos (by omega : k < n + (k + 1))]

theorem event_complement (p : ℕ → ℝ) (hs : HasSum p 1) (P : ℕ → Prop) :
    eventMass p P + eventMass p (fun n => ¬P n) = 1 := by
  classical
  unfold eventMass
  rw [← (event_summable p hs.summable P).tsum_add (event_summable p hs.summable (fun n => ¬P n))]
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro n
  by_cases hn : P n <;> simp [hn]

theorem event_finset (p : ℕ → ℝ) (s : Finset ℕ) :
    eventMass p (fun n => n ∈ s) = ∑ n ∈ s, p n := by
  classical
  unfold eventMass
  dsimp only
  rw [tsum_eq_sum (s := s) (f := fun n => @ite ℝ (n ∈ s) (Classical.propDecidable (n ∈ s)) (p n) 0) (fun n hn => if_neg hn)]
  exact Finset.sum_congr rfl (fun n hn => if_pos hn)

end
end LinearAssemblies.Probability
