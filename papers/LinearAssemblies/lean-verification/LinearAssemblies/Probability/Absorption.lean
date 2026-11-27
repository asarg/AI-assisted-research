import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Absorption masses for finite substochastic chains

`mass k i` is the probability of absorption after exactly `k + 1` transitions
starting at transient state `i`. Defining masses by finite recursion avoids
assuming any general measure-theoretic Markov-chain theorem here.

Rows are allowed to have total mass at most one. Consequently the atom bound
does not require almost-sure absorption, and applies in particular to the
haltable chains in the paper.
-/

namespace LinearAssemblies.Probability

open Finset

structure FiniteChain (S : Type*) [Fintype S] where
  step : S → S → ℝ
  stop : S → ℝ
  step_nonneg : ∀ i j, 0 ≤ step i j
  stop_nonneg : ∀ i, 0 ≤ stop i
  row_le_one : ∀ i, stop i + ∑ j, step i j ≤ 1

namespace FiniteChain

variable {S : Type*} [Fintype S] (c : FiniteChain S)

def mass : ℕ → S → ℝ
  | 0, i => c.stop i
  | k + 1, i => ∑ j, c.step i j * mass k j

theorem mass_nonneg (k : ℕ) (i : S) : 0 ≤ c.mass k i := by
  induction k generalizing i with
  | zero => exact c.stop_nonneg i
  | succ k ih =>
    exact Finset.sum_nonneg fun j _ => mul_nonneg (c.step_nonneg i j) (ih j)

theorem step_sum_le_one (i : S) : ∑ j, c.step i j ≤ 1 := by
  have h := c.row_le_one i
  have hn := c.stop_nonneg i
  linarith

/-- The cumulative absorption mass is at most one at every finite horizon. -/
theorem partial_mass_le_one (k : ℕ) (i : S) :
    ∑ t ∈ Finset.range k, c.mass t i ≤ 1 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    have he : (∑ t ∈ Finset.range (k + 1), c.mass t i) =
        c.stop i + ∑ j, c.step i j * (∑ t ∈ Finset.range k, c.mass t j) := by
      rw [Finset.sum_range_succ']
      simp only [mass]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      ring
    rw [he]
    calc
      c.stop i + ∑ j, c.step i j * (∑ t ∈ Finset.range k, c.mass t j)
          ≤ c.stop i + ∑ j, c.step i j := by
        apply add_le_add_left
        apply Finset.sum_le_sum
        intro j _
        simpa using mul_le_mul_of_nonneg_left (ih j) (c.step_nonneg i j)
      _ ≤ 1 := c.row_le_one i

/-- Advancing time cannot exceed the sum of the remaining-time masses over all states. -/
theorem shifted_mass_le (t k : ℕ) (i : S) :
    c.mass (t + k) i ≤ ∑ j, c.mass k j := by
  classical
  induction t generalizing i with
  | zero =>
    simpa using Finset.single_le_sum (fun j _ => c.mass_nonneg k j) (Finset.mem_univ i)
  | succ t ih =>
    have he : t + 1 + k = (t + k) + 1 := by omega
    rw [he, mass]
    calc
      ∑ j, c.step i j * c.mass (t + k) j
          ≤ ∑ j, c.step i j * (∑ u, c.mass k u) := by
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (c.step_nonneg i j)
      _ = (∑ j, c.step i j) * (∑ u, c.mass k u) := by rw [Finset.sum_mul]
      _ ≤ ∑ u, c.mass k u := by
        have hn : 0 ≤ ∑ u, c.mass k u := Finset.sum_nonneg fun u _ => c.mass_nonneg k u
        simpa using mul_le_mul_of_nonneg_right (c.step_sum_le_one i) hn

/-- Lemma 11, with a zero-based index: `(k+1) Pr(T=k+1) ≤ card S`. -/
theorem atom_bound (k : ℕ) (i : S) :
    ((k + 1 : ℕ) : ℝ) * c.mass k i ≤ Fintype.card S := by
  have h : ∀ t ∈ Finset.range (k + 1), c.mass k i ≤ ∑ j, c.mass (k - t) j := by
    intro t ht
    have ht' : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have he : t + (k - t) = k := by omega
    simpa only [he] using c.shifted_mass_le t (k - t) i
  calc
    ((k + 1 : ℕ) : ℝ) * c.mass k i = ∑ t ∈ Finset.range (k + 1), c.mass k i := by simp
    _ ≤ ∑ t ∈ Finset.range (k + 1), ∑ j, c.mass (k - t) j := Finset.sum_le_sum h
    _ = ∑ j, ∑ t ∈ Finset.range (k + 1), c.mass (k - t) j := Finset.sum_comm
    _ = ∑ j, ∑ t ∈ Finset.range (k + 1), c.mass t j := by
      apply Finset.sum_congr rfl
      intro j _
      simpa using Finset.sum_range_reflect (fun t => c.mass t j) (k + 1)
    _ ≤ ∑ _j : S, (1 : ℝ) := Finset.sum_le_sum fun j _ => c.partial_mass_le_one (k + 1) j
    _ = (Fintype.card S : ℝ) := by simp

/-- The absorption mass at the paper's attachment count `T = k`. -/
def absorptionProbability (k : ℕ) (i : S) : ℝ :=
  match k with
  | 0 => 0
  | k + 1 => c.mass k i

/-- Lemma 11 in the paper's indexing convention. -/
theorem absorption_atom_bound (k : ℕ) (hk : 1 ≤ k) (i : S) :
    (k : ℝ) * c.absorptionProbability k i ≤ Fintype.card S := by
  cases k with
  | zero => omega
  | succ k => exact c.atom_bound k i

end FiniteChain
end LinearAssemblies.Probability
