import LinearAssemblies.OnePad.ResetProgram

set_option autoImplicit false

namespace LinearAssemblies

/-- Nonempty positive-base digit words, built from most to least significant digit. -/
inductive PositiveDigits where
  | single (digit : ℕ)
  | snoc (previous : PositiveDigits) (digit : ℕ)
  deriving Repr

namespace PositiveDigits

def value (b : ℕ) : PositiveDigits → ℕ
  | .single a => a
  | .snoc p a => b * p.value b + a

def length : PositiveDigits → ℕ
  | .single _ => 1
  | .snoc p _ => p.length + 1

def Valid (b : ℕ) : PositiveDigits → Prop
  | .single a => 1 ≤ a ∧ a ≤ b
  | .snoc p a => p.Valid b ∧ 1 ≤ a ∧ a ≤ b

def reset (b : ℕ) : PositiveDigits → OnePad.ResetProgram
  | .single a => .path a
  | .snoc p a => .extend (p.reset b) b a

theorem value_pos (p : PositiveDigits) (b : ℕ) (hp : p.Valid b) : 0 < p.value b := by
  cases p <;> simp only [Valid, value] at * <;> omega

theorem length_pos (p : PositiveDigits) : 0 < p.length := by
  cases p <;> simp [length]

theorem reset_value (p : PositiveDigits) (b : ℕ) : (p.reset b).value = p.value b := by
  induction p <;> simp_all [reset, value, OnePad.ResetProgram.value]

theorem reset_valid (p : PositiveDigits) (b : ℕ) (hp : p.Valid b) : (p.reset b).Valid := by
  induction p with
  | single a => trivial
  | snoc p a ih =>
    exact ⟨ih hp.1, by rw [reset_value]; exact p.value_pos b hp.1, hp.2⟩

/-- Repeated positive remainders construct a digit word for every positive integer. -/
theorem represents (b M : ℕ) (hb : 2 ≤ b) (hM : 0 < M) :
    ∃ p : PositiveDigits, p.Valid b ∧ p.value b = M := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    by_cases hsmall : M ≤ b
    · exact ⟨.single M, ⟨hM, hsmall⟩, rfl⟩
    let h := (M - 1) / b
    let a := (M - 1) % b + 1
    have hh : 0 < h := (Nat.one_le_div_iff (by omega)).mpr (by omega)
    have hlt : h < M := by
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    obtain ⟨p, hp, hv⟩ := ih h hlt hh
    have hamod : (M - 1) % b < b := Nat.mod_lt _ (by omega)
    have ha : 1 ≤ a ∧ a ≤ b := by dsimp [a]; omega
    refine ⟨.snoc p a, ⟨hp, ha⟩, ?_⟩
    simp only [value, hv]
    have hdecomp := Nat.mod_add_div (M - 1) b
    dsimp [h, a]
    omega

/-- The prefix-size bound underlying the number of base-b digit stages. -/
theorem pow_length_le (p : PositiveDigits) (b : ℕ) (hp : p.Valid b) :
    b ^ (p.length - 1) ≤ p.value b := by
  induction p with
  | single a => simpa only [length, Nat.sub_self, pow_zero, value] using hp.1
  | snoc p a ih =>
    have hlen := p.length_pos
    have he : p.length = (p.length - 1) + 1 := by omega
    simp only [length, Nat.add_sub_cancel, value]
    rw [he, pow_succ]
    have hm := Nat.mul_le_mul_left b (ih hp.1)
    nlinarith

theorem reset_cost_le (p : PositiveDigits) (b : ℕ) (hp : p.Valid b) :
    (p.reset b).cost ≤ b * p.length := by
  induction p with
  | single a => simpa [reset, OnePad.ResetProgram.cost, length] using hp.2
  | snoc p a ih =>
    have h := ih hp.1
    simp only [reset, OnePad.ResetProgram.cost, length]
    nlinarith

end PositiveDigits
end LinearAssemblies
