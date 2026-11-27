import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option autoImplicit false

/-!
# The one-pad extremal recurrence

This module formalizes Definition 1 and Lemma 4 of the November 26 draft.
It is purely arithmetic: no external paper theorem is assumed.
Connecting this recurrence to actual assembly systems is a separate obligation.
-/

namespace LinearAssemblies.OnePad

/-- Definition 1, indexed by `i = d - 1` to make recursion explicit. -/
def F : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.range (n + 1)).sup fun i => (i + 1) * (F (n - i) + 1)
termination_by n => n
decreasing_by omega

@[simp] theorem F_zero : F 0 = 0 := by rw [F]

/-- Every admissible candidate is bounded by the defining maximum. -/
theorem candidate_le (r d : ℕ) (hd : 1 ≤ d) (hdr : d ≤ r) :
    d * (F (r - d) + 1) ≤ F r := by
  cases r with
  | zero => omega
  | succ n =>
    rw [F]
    have hm : d - 1 ∈ Finset.range (n + 1) := by simp; omega
    have h := Finset.le_sup (f := fun i => (i + 1) * (F (n - i) + 1)) hm
    have he : d - 1 + 1 = d := by omega
    have hs : n - (d - 1) = n + 1 - d := by omega
    simpa only [he, hs] using h

/-- A convenient upper-bound induction rule for the full recurrence. -/
theorem F_le (r b : ℕ)
    (h : ∀ d, 1 ≤ d → d ≤ r → d * (F (r - d) + 1) ≤ b) : F r ≤ b := by
  cases r with
  | zero => simp
  | succ n =>
    rw [F]
    apply Finset.sup_le
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    have hs : n + 1 - (i + 1) = n - i := by omega
    simpa only [hs] using h (i + 1) (by omega) (by omega)

theorem F_step (r : ℕ) : F r + 1 ≤ F (r + 1) := by
  simpa using candidate_le (r + 1) 1 (by omega) (by omega)

theorem F_strictMono : StrictMono F := by
  apply strictMono_nat_of_lt_succ
  intro r
  have h := F_step r
  omega

theorem F_monotone : Monotone F := F_strictMono.monotone

theorem self_le_F (r : ℕ) : r ≤ F r := by
  induction r with
  | zero => simp
  | succ r ih => have h := F_step r; omega

/-- Lemma 4's strict domination argument: every `d ≥ 4` loses to `d = 2`. -/
theorem large_candidate_lt (r d : ℕ) (hd : 4 ≤ d) (hdr : d ≤ r) :
    d * (F (r - d) + 1) < 2 * (F (r - 2) + 1) := by
  have h := candidate_le (r - 2) (d - 2) (by omega) (by omega)
  have hs : r - 2 - (d - 2) = r - d := by omega
  rw [hs] at h
  have hm := Nat.mul_le_mul_right (F (r - d) + 1)
    (show d ≤ 2 * (d - 2) by omega)
  have hm' : d * (F (r - d) + 1) ≤ 2 * ((d - 2) * (F (r - d) + 1)) := by
    simpa only [Nat.mul_assoc] using hm
  omega

/-- Every maximizer in Definition 1 satisfies `d ≤ 3` (Lemma 4). -/
theorem maximizing_degree_le_three (r d : ℕ) (_hd : 1 ≤ d) (hdr : d ≤ r)
    (hmax : F r = d * (F (r - d) + 1)) : d ≤ 3 := by
  by_contra hn
  have hlt := large_candidate_lt r d (by omega) hdr
  have hle := candidate_le r 2 (by omega) (by omega)
  omega

/-- Equation (18), using an inclusive interval for the admissible degrees. -/
theorem reduced_recurrence (r : ℕ) :
    F r = (Finset.Icc 1 (min 3 r)).sup (fun d => d * (F (r - d) + 1)) := by
  apply Nat.le_antisymm
  · apply F_le
    intro d hd hdr
    by_cases hsmall : d ≤ 3
    · exact Finset.le_sup (f := fun d => d * (F (r - d) + 1))
        (Finset.mem_Icc.mpr ⟨hd, le_min hsmall hdr⟩)
    · have hlt := large_candidate_lt r d (by omega) hdr
      have hm : 2 ∈ Finset.Icc 1 (min 3 r) := by simp; omega
      exact le_trans (Nat.le_of_lt hlt)
        (Finset.le_sup (f := fun d => d * (F (r - d) + 1)) hm)
  · apply Finset.sup_le
    intro d hd
    obtain ⟨hd, hdr⟩ := Finset.mem_Icc.mp hd
    exact candidate_le r d hd (le_trans hdr (min_le_right _ _))

/-- A three-candidate form convenient for the closed-form proof. -/
theorem recurrence_three (r : ℕ) (hr : 3 ≤ r) :
    F r = max (F (r - 1) + 1)
      (max (2 * (F (r - 2) + 1)) (3 * (F (r - 3) + 1))) := by
  apply Nat.le_antisymm
  · apply F_le
    intro d hd hdr
    by_cases hsmall : d ≤ 3
    · interval_cases d <;> simp
    · have hlt := large_candidate_lt r d (by omega) hdr
      exact le_trans (Nat.le_of_lt hlt) (le_trans (le_max_left _ _) (le_max_right _ _))
  · apply max_le
    · simpa using candidate_le r 1 (by omega) (by omega)
    · exact max_le (candidate_le r 2 (by omega) (by omega))
        (candidate_le r 3 (by omega) hr)

end LinearAssemblies.OnePad
