import LinearAssemblies.Probability.Absorption
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

/-!
# Accuracy from the absorption atom bound

The chain-level result proves the explicit constant `1/24` in Lemma 12 for
`N ≥ 4`. The seed contributes one tile: `L = T + 1`. The final tile-complexity
theorem is transferred to tile systems in `LinearAssemblies/Accuracy.lean`.
-/

namespace LinearAssemblies.Probability.FiniteChain

open Finset

variable {S : Type*} [Fintype S] (c : FiniteChain S)

theorem absorptionProbability_nonneg (k : ℕ) (i : S) :
    0 ≤ c.absorptionProbability k i := by
  cases k with
  | zero => simp [absorptionProbability]
  | succ k => exact c.mass_nonneg k i

def windowMass (a b : ℕ) (i : S) : ℝ :=
  ∑ k ∈ Finset.Icc a b, c.absorptionProbability k i

theorem window_bound (a b : ℕ) (ha : 1 ≤ a) (i : S) :
    (a : ℝ) * c.windowMass a b i ≤
      ((Finset.Icc a b).card : ℝ) * Fintype.card S := by
  unfold windowMass
  rw [Finset.mul_sum]
  calc
    ∑ k ∈ Finset.Icc a b, (a : ℝ) * c.absorptionProbability k i
        ≤ ∑ _k ∈ Finset.Icc a b, (Fintype.card S : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hak, _⟩ := Finset.mem_Icc.mp hk
      have hk1 : 1 ≤ k := by omega
      calc
        (a : ℝ) * c.absorptionProbability k i
            ≤ (k : ℝ) * c.absorptionProbability k i :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hak) (c.absorptionProbability_nonneg k i)
        _ ≤ Fintype.card S := c.absorption_atom_bound k hk1 i
    _ = ((Finset.Icc a b).card : ℝ) * Fintype.card S := by simp

/-- The explicit accuracy inequality, given the elementary endpoint bounds. -/
theorem accuracy_bound_of_window (N a b : ℕ) (eps : ℝ) (i : S)
    (hN : 4 ≤ N) (heps : 0 < eps)
    (ha : (N : ℝ) / 4 ≤ a)
    (hw : ((Finset.Icc a b).card : ℝ) ≤ 2 * eps * N + 1)
    (hmass : 1 / 2 ≤ c.windowMass a b i) :
    min (N : ℝ) (eps⁻¹) / 24 ≤ (Fintype.card S : ℝ) := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have ha1 : 1 ≤ a := by exact_mod_cast (show (1 : ℝ) ≤ a by linarith)
  have hab := c.window_bound a b ha1 i
  have hn : (0 : ℝ) ≤ Fintype.card S := by positivity
  have hx := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ a by positivity)
  have hy := mul_le_mul_of_nonneg_right hw hn
  have hcore : (N : ℝ) ≤ 8 * (2 * eps * N + 1) * Fintype.card S := by nlinarith
  by_cases hsmall : eps * N ≤ 1
  · have hh := mul_le_mul_of_nonneg_right hsmall hn
    have hc : (N : ℝ) / 24 ≤ Fintype.card S := by nlinarith
    exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) hc
  · have hlarge : 1 ≤ eps * N := by linarith
    have hh := mul_le_mul_of_nonneg_right hlarge hn
    have hmult : (N : ℝ) * 1 ≤ (N : ℝ) * (24 * eps * Fintype.card S) := by nlinarith
    have hc : (1 : ℝ) ≤ 24 * eps * Fintype.card S :=
      (mul_le_mul_left (show (0 : ℝ) < N by linarith)).mp hmult
    have he : eps⁻¹ / 24 ≤ (Fintype.card S : ℝ) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).mpr
      apply (inv_le_iff_one_le_mul₀ heps).mpr
      nlinarith
    exact le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) he

noncomputable def lowerEndpoint (N : ℕ) (eps : ℝ) : ℕ := Nat.ceil ((1 - eps) * N) - 1
noncomputable def upperEndpoint (N : ℕ) (eps : ℝ) : ℕ := Nat.floor ((1 + eps) * N) - 1

/-- The rounded interval is exactly the relative-error event for `L = T + 1`. -/
theorem mem_window_iff (N k : ℕ) (eps : ℝ) (hN : 4 ≤ N)
    (heps : 0 < eps) (hepsHalf : eps ≤ 1 / 2) :
    k ∈ Finset.Icc (lowerEndpoint N eps) (upperEndpoint N eps) ↔
      |((k : ℝ) + 1) - N| ≤ eps * N := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hceil := Nat.le_ceil ((1 - eps) * (N : ℝ))
  have hceil1 : 1 ≤ Nat.ceil ((1 - eps) * (N : ℝ)) := by
    exact_mod_cast (show (1 : ℝ) ≤ (Nat.ceil ((1 - eps) * (N : ℝ)) : ℝ) by nlinarith)
  have hfloorN : N ≤ Nat.floor ((1 + eps) * (N : ℝ)) := Nat.le_floor (by nlinarith)
  have hfloor1 : 1 ≤ Nat.floor ((1 + eps) * (N : ℝ)) := by omega
  have hhigh : (0 : ℝ) ≤ (1 + eps) * N := by positivity
  simp only [Finset.mem_Icc, lowerEndpoint, upperEndpoint, abs_le]
  constructor
  · rintro ⟨hl, hu⟩
    have hcl : Nat.ceil ((1 - eps) * (N : ℝ)) ≤ k + 1 := by omega
    have hfl : k + 1 ≤ Nat.floor ((1 + eps) * (N : ℝ)) := by omega
    have h1 := Nat.ceil_le.mp hcl
    have h2 := (Nat.le_floor_iff hhigh).mp hfl
    push_cast at h1 h2
    constructor <;> nlinarith
  · rintro ⟨hl, hu⟩
    have hcl : Nat.ceil ((1 - eps) * (N : ℝ)) ≤ k + 1 := by
      apply Nat.ceil_le.mpr
      push_cast
      nlinarith
    have hfl : k + 1 ≤ Nat.floor ((1 + eps) * (N : ℝ)) := by
      apply Nat.le_floor
      push_cast
      nlinarith
    constructor <;> omega

/-- Rounding and the seed offset give the endpoint estimates used in the paper. -/
theorem endpoint_bounds (N : ℕ) (eps : ℝ) (hN : 4 ≤ N)
    (heps : 0 < eps) (hepsHalf : eps ≤ 1 / 2) :
    (N : ℝ) / 4 ≤ lowerEndpoint N eps ∧
    ((Finset.Icc (lowerEndpoint N eps) (upperEndpoint N eps)).card : ℝ)
      ≤ 2 * eps * N + 1 := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hlow : (2 : ℝ) ≤ (1 - eps) * N := by nlinarith
  have hceil := Nat.le_ceil ((1 - eps) * (N : ℝ))
  have hceil1 : 1 ≤ Nat.ceil ((1 - eps) * (N : ℝ)) := by
    exact_mod_cast (show (1 : ℝ) ≤ (Nat.ceil ((1 - eps) * (N : ℝ)) : ℝ) by linarith)
  have hceilN : Nat.ceil ((1 - eps) * (N : ℝ)) ≤ N :=
    Nat.ceil_le.mpr (by nlinarith)
  have hfloorN : N ≤ Nat.floor ((1 + eps) * (N : ℝ)) := Nat.le_floor (by nlinarith)
  have hfloor1 : 1 ≤ Nat.floor ((1 + eps) * (N : ℝ)) := by omega
  have hfloor := Nat.floor_le (show (0 : ℝ) ≤ (1 + eps) * N by positivity)
  have ha : (lowerEndpoint N eps : ℝ) = (Nat.ceil ((1 - eps) * (N : ℝ)) : ℝ) - 1 := by
    simp only [lowerEndpoint, Nat.cast_sub hceil1, Nat.cast_one]
  have hb : (upperEndpoint N eps : ℝ) = (Nat.floor ((1 + eps) * (N : ℝ)) : ℝ) - 1 := by
    simp only [upperEndpoint, Nat.cast_sub hfloor1, Nat.cast_one]
  have hab : lowerEndpoint N eps ≤ upperEndpoint N eps + 1 := by
    unfold lowerEndpoint upperEndpoint
    omega
  constructor
  · rw [ha]
    nlinarith
  · rw [Nat.card_Icc, Nat.cast_sub hab, Nat.cast_add, Nat.cast_one, ha, hb]
    nlinarith

/-- Chain-level version of Lemma 12 with an explicit constant and no mean assumption. -/
theorem accuracy_lower_bound (N : ℕ) (eps : ℝ) (i : S)
    (hN : 4 ≤ N) (heps : 0 < eps) (hepsHalf : eps ≤ 1 / 2)
    (hconf : 1 / 2 ≤ c.windowMass (lowerEndpoint N eps) (upperEndpoint N eps) i) :
    min (N : ℝ) (eps⁻¹) / 24 ≤ (Fintype.card S : ℝ) := by
  obtain ⟨ha, hw⟩ := endpoint_bounds N eps hN heps hepsHalf
  exact c.accuracy_bound_of_window N _ _ eps i hN heps ha hw hconf

end LinearAssemblies.Probability.FiniteChain
