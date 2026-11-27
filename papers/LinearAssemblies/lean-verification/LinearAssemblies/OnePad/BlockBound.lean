import LinearAssemblies.OnePad.LogarithmicBounds

set_option autoImplicit false

namespace LinearAssemblies.OnePad.CertifiedBlock

/-- Every interface has remaining mean bounded by the block's input mean. -/
def Bounded (b : CertifiedBlock) : Prop := ∀ x, b.potential x ≤ (b.value : ℝ)

theorem bounded_zero : zero.Bounded := by intro x; simp [zero]

theorem bounded_prepend (b : CertifiedBlock) (hb : b.Bounded) : (prepend b).Bounded := by
  intro x
  cases x with
  | none => simp [prepend]
  | some x =>
    have h := hb x
    change b.potential x ≤ ((b.value + 1 : ℕ) : ℝ)
    push_cast
    linarith

theorem bounded_path (n : ℕ) : (path n).Bounded := by
  induction n with
  | zero => exact bounded_zero
  | succ n ih => exact bounded_prepend _ ih

theorem bounded_extend (b : CertifiedBlock) (hb : b.Bounded) (d a : ℕ)
    (hv : 0 < b.value) (ha : 1 ≤ a) (had : a ≤ d) :
    (extend b d a hv ha had).Bounded := by
  intro x
  cases x with
  | none => change (0 : ℝ) ≤ ((d * b.value + a : ℕ) : ℝ); positivity
  | some x =>
    have h := add_le_add_right (hb x) (b.offset d a : ℝ)
    have he := (extend b d a hv ha had).input_value
    change b.potential b.input + b.offset d a = _ at he
    rw [b.input_value] at he
    exact h.trans_eq he

/-- The compiler also verifies the uniform remaining-time premise for concentration. -/
theorem compile_bounded_exists (p : ResetProgram) (hp : p.Valid) :
    ∃ b : CertifiedBlock, b.value = p.value ∧ b.cost = p.cost ∧ b.Bounded := by
  induction p with
  | path n => exact ⟨path n, path_value n, path_cost n, bounded_path n⟩
  | extend p d a ih =>
    obtain ⟨hp, hv, ha, had⟩ := hp
    obtain ⟨b, hb, hc, hbound⟩ := ih hp
    have hpos : 0 < b.value := by omega
    refine ⟨extend b d a hpos ha had, ?_, ?_, bounded_extend b hbound d a hpos ha had⟩
    · change d * b.value + a = d * p.value + a
      rw [hb]
    · rw [cost_extend]
      change b.cost + d = p.cost + d
      rw [hc]

theorem expected_eq_potential (ext : Probability.FiniteAbsorptionLaw) (b : CertifiedBlock) :
    letI := b.finite
    ∀ x, b.graph.expected x = b.potential x := by
  letI := b.finite
  exact ext.unique b.graph b.potential (b.graph.haltable_of_potential b.certificate) b.certificate

end LinearAssemblies.OnePad.CertifiedBlock

namespace LinearAssemblies.OnePad

/-- Lemma 5: an appendable one-pad block with the sharp size and remaining-mean bounds. -/
theorem onePad_block_exists (M : ℕ) (hM : 1 ≤ M) :
    ∃ b : CertifiedBlock, b.value = M ∧
      (b.cost : ℝ) ≤ 3 * Real.log ((M : ℝ) + 1) / Real.log 3 ∧ b.Bounded := by
  obtain ⟨p, hp, hv⟩ := PositiveDigits.represents 3 M (by omega) hM
  obtain ⟨b, hb, hc, hbound⟩ := CertifiedBlock.compile_bounded_exists (p.reset 3) (p.reset_valid 3 hp)
  have hval : b.value = M := by rw [hb, p.reset_value, hv]
  refine ⟨b, hval, ?_, hbound⟩
  rw [hc, ← hv]
  exact ternary_cost_log p hp

end LinearAssemblies.OnePad
