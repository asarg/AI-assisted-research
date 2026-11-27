import LinearAssemblies.PositiveDigits
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

namespace LinearAssemblies

/-- A finite positive digit word: one leading digit and `count` later digits.
Only indices below `count` are inspected by the tile construction. -/
structure DigitData (base : ℕ) where
  count : ℕ
  first : ℕ
  digit : ℕ → ℕ
  first_pos : 1 ≤ first
  first_le : first ≤ base
  digit_bounds : ∀ i < count, 1 ≤ digit i ∧ digit i ≤ base

namespace DigitData

variable {b : ℕ} (d : DigitData b)

def prefixValue : ℕ → ℕ
  | 0 => d.first
  | i + 1 => b * prefixValue i + d.digit i

def value : ℕ := d.prefixValue d.count

theorem prefix_mono (hb : 1 ≤ b) : Monotone d.prefixValue := by
  apply monotone_nat_of_le_succ
  intro i
  change d.prefixValue i ≤ b * d.prefixValue i + d.digit i
  nlinarith

theorem first_le_value (hb : 1 ≤ b) : d.first ≤ d.value :=
  d.prefix_mono hb (Nat.zero_le _)

theorem value_pos (hb : 1 ≤ b) : 0 < d.value := lt_of_lt_of_le d.first_pos (d.first_le_value hb)

theorem prefix_le_value (hb : 1 ≤ b) (i : ℕ) (hi : i ≤ d.count) :
    d.prefixValue i ≤ d.value := d.prefix_mono hb hi

def single (a : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) : DigitData b where
  count := 0
  first := a
  digit := fun _ => 1
  first_pos := ha
  first_le := hab
  digit_bounds := by omega

def append (a : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) : DigitData b where
  count := d.count + 1
  first := d.first
  digit := fun i => if i < d.count then d.digit i else a
  first_pos := d.first_pos
  first_le := d.first_le
  digit_bounds := by
    intro i hi
    split_ifs with h
    · exact d.digit_bounds i h
    · exact ⟨ha, hab⟩

theorem append_prefix (a : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (i : ℕ) (hi : i ≤ d.count) :
    (d.append a ha hab).prefixValue i = d.prefixValue i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i < d.count := by omega
    rw [prefixValue, prefixValue, ih (by omega)]
    simp only [append, if_pos hi']

theorem append_value (a : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (d.append a ha hab).value = b * d.value + a := by
  change (d.append a ha hab).prefixValue (d.count + 1) = _
  rw [prefixValue, d.append_prefix a ha hab d.count le_rfl]
  simp [append, value]

/-- The positive-digit algorithm provides finite data for every target attachment count. -/
theorem represents (b M : ℕ) (hb : 2 ≤ b) (hM : 0 < M) :
    ∃ d : DigitData b, d.value = M := by
  obtain ⟨p, hp, hv⟩ := PositiveDigits.represents b M hb hM
  suffices ∃ d : DigitData b, d.value = p.value b by simpa only [hv] using this
  clear hv
  induction p with
  | single a => exact ⟨single a hp.1 hp.2, rfl⟩
  | snoc p a ih =>
    obtain ⟨d, hd⟩ := ih hp.1
    refine ⟨d.append a hp.2.1 hp.2.2, ?_⟩
    rw [append_value, hd]
    rfl

theorem pow_le_prefix (i : ℕ) : b ^ i ≤ d.prefixValue i := by
  induction i with
  | zero => simpa [prefixValue] using d.first_pos
  | succ i ih =>
    rw [pow_succ, prefixValue]
    have h := Nat.mul_le_mul_left b ih
    nlinarith

theorem count_log_bound (hb : 2 ≤ b) :
    (d.count : ℝ) ≤ Real.log d.value / Real.log b := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hh : (b : ℝ) ^ d.count ≤ (d.value : ℝ) := by exact_mod_cast d.pow_le_prefix d.count
  have hl := Real.log_le_log (pow_pos hb0 _) hh
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos hb1)).mpr hl

end DigitData
end LinearAssemblies
