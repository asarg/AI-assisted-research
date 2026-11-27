import LinearAssemblies.Forest.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false

namespace LinearAssemblies.Forest

variable (S : Type) [Fintype S]

/-- Integer attachment counts on transient states, with all terminal interfaces collapsed. -/
structure Counts where
  degree : S → ℕ
  transition : S → S → ℕ
  terminal : S → ℕ
  accounting : ∀ i, degree i = (∑ j, transition i j) + terminal i

namespace Counts

variable {S} (c : Counts S)

inductive Path : S → ℕ → Prop
  | stop {i : S} : 0 < c.terminal i → Path i 1
  | next {i j : S} {n : ℕ} : 0 < c.transition i j → Path j n → Path i (n + 1)

def Haltable : Prop := ∀ i, ∃ n, c.Path i n

def GoodChoice (rank : S → ℕ) (i : S) : Target S → Prop
  | .inl j => i ≠ j ∧ 0 < c.transition i j ∧ rank j < rank i
  | .inr false => 0 < c.terminal i
  | .inr true => False

/-- Shortest positive paths select a positive rooted forest with no alarm edges. -/
theorem positive_forest [DecidableEq S] (hh : c.Haltable) :
    ∃ f : S → Target S, Rooted (forget f) ∧
      (∀ i j, f i = .inl j → i ≠ j ∧ 0 < c.transition i j) ∧
      (∀ i, f i = .inr false → 0 < c.terminal i) ∧
      (∀ i, f i ≠ .inr true) := by
  classical
  let rank : S → ℕ := fun i => Nat.find (hh i)
  have first : ∀ i n, c.Path i n → n ≤ rank i → ∃ t, c.GoodChoice rank i t := by
    intro i n hp hmin
    cases hp with
    | stop hb => exact ⟨.inr false, hb⟩
    | @next i j n ha hp =>
      have hj : rank j ≤ n := Nat.find_min' (hh j) hp
      have hd : rank j < rank i := by omega
      have hne : i ≠ j := by intro he; subst j; exact lt_irrefl _ hd
      exact ⟨.inl j, hne, ha, hd⟩
  have hchoose : ∀ i, ∃ t, c.GoodChoice rank i t :=
    fun i => first i (rank i) (Nat.find_spec (hh i)) le_rfl
  let f := fun i => Classical.choose (hchoose i)
  have hf : ∀ i, c.GoodChoice rank i (f i) := fun i => Classical.choose_spec (hchoose i)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · apply rooted_of_rank (forget f) rank
    intro i j hij
    cases hi : f i with
    | inl k =>
      have he : k = j := by simpa [forget, hi] using hij
      subst k
      exact (show i ≠ j ∧ 0 < c.transition i j ∧ rank j < rank i by simpa [GoodChoice, hi] using hf i).2.2
    | inr b => simp [forget, hi] at hij
  · intro i j hij
    have hi := hf i
    rw [hij] at hi
    exact ⟨hi.1, hi.2.1⟩
  · intro i hi
    have hh' := hf i
    simp only [hi, GoodChoice] at hh'
    exact hh'
  · intro i hi
    have hh' := hf i
    simp only [hi, GoodChoice] at hh'

open Polynomial

variable [DecidableEq S]

/-- Self loops have zero incidence and are omitted from the outgoing-weight bound. -/
noncomputable def edgeWeight (i : S) : Target S → ℤ[X]
  | .inl j => if i = j then 0 else C (c.transition i j : ℤ)
  | .inr false => C (c.terminal i : ℤ)
  | .inr true => C (c.degree i : ℤ) * X

theorem edgeWeight_degree (i : S) (t : Target S) : (c.edgeWeight i t).natDegree ≤ 1 := by
  cases t with
  | inl j => by_cases h : i = j <;> simp [edgeWeight, h]
  | inr b =>
    cases b with
    | false => simp [edgeWeight]
    | true =>
      exact le_trans (Polynomial.natDegree_mul_le) (by simp)

theorem edgeWeight_eval_nonneg (i : S) (t : Target S) (x : ℤ) (hx : 0 ≤ x) :
    0 ≤ (c.edgeWeight i t).eval x := by
  cases t with
  | inl j => by_cases h : i = j <;> simp [edgeWeight, h]
  | inr b => cases b <;> simp [edgeWeight]; positivity

theorem edgeWeight_one_sum (i : S) :
    (∑ t : Target S, (c.edgeWeight i t).eval 1) = 2 * (c.degree i : ℤ) - c.transition i i := by
  have ha := c.accounting i
  have ha' : (c.degree i : ℤ) = (∑ j, (c.transition i j : ℤ)) + c.terminal i := by exact_mod_cast ha
  have hs : (∑ j, if i = j then (0 : ℤ) else (c.transition i j : ℤ)) =
      (∑ j, (c.transition i j : ℤ)) - c.transition i i := by
    have he : ∀ j, (if i = j then (0 : ℤ) else c.transition i j) =
        (c.transition i j : ℤ) - if i = j then c.transition i j else 0 := by
      intro j; split_ifs <;> simp
    simp_rw [he]
    simp [Finset.sum_sub_distrib]
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, edgeWeight,
    apply_ite, Polynomial.eval_zero, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, mul_one]
  rw [hs]
  linarith

end Counts
end LinearAssemblies.Forest
