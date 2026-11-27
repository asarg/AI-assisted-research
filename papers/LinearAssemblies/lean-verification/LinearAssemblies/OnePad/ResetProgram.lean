import LinearAssemblies.OnePad.Recurrence

set_option autoImplicit false

/-!
# Arithmetic reset programs

This is the constructive arithmetic part of Theorem 3. A path has value and
cost equal to its length; extending by a degree-`d` stage with digit `a` changes
the value from `h` to `d*h+a` and adds `d` to the cost.

These syntax trees are NOT themselves tile systems. The compiler and its stochastic semantics are proved separately in
`ResetCompiler`, `TileCompiler`, and `Characterization`.
-/

namespace LinearAssemblies.OnePad

inductive ResetProgram where
  | path (length : ℕ)
  | extend (previous : ResetProgram) (degree digit : ℕ)
  deriving Repr

namespace ResetProgram

def value : ResetProgram → ℕ
  | .path n => n
  | .extend p d a => d * value p + a

def cost : ResetProgram → ℕ
  | .path n => n
  | .extend p d _ => cost p + d

/-- Positive prefixes preserve the forced first attachment used by the resets. -/
def Valid : ResetProgram → Prop
  | .path _ => True
  | .extend p d a => Valid p ∧ 0 < value p ∧ 1 ≤ a ∧ a ≤ d

/-- Every valid reset program satisfies the full extremal recurrence bound. -/
theorem value_le_F_cost (p : ResetProgram) (hp : p.Valid) : p.value ≤ F p.cost := by
  induction p with
  | path n => exact self_le_F n
  | extend p d a ih =>
    obtain ⟨hp, _, ha, had⟩ := hp
    have hprefix := ih hp
    have hrec := candidate_le (p.cost + d) d (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hrec
    have hm := Nat.mul_le_mul_left d hprefix
    change d * p.value + a ≤ F (p.cost + d)
    nlinarith

/-- Every integer in `[0,F(r)]` has a valid reset-program witness of cost at most `r`. -/
theorem all_values_attainable (r M : ℕ) (hM : M ≤ F r) :
    ∃ p : ResetProgram, p.Valid ∧ p.cost ≤ r ∧ p.value = M := by
  induction r using Nat.strong_induction_on generalizing M with
  | h r ih =>
    by_cases hsmall : M ≤ r
    · exact ⟨.path M, trivial, hsmall, rfl⟩
    have hr : 1 ≤ r := by
      by_contra hn
      have hr0 : r = 0 := by omega
      simp only [hr0, F_zero] at hM
      omega
    have hne : (Finset.Icc 1 (min 3 r)).Nonempty :=
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, le_min (by omega) hr⟩⟩
    obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup (Finset.Icc 1 (min 3 r)) hne
      (fun d => d * (F (r - d) + 1))
    rw [← reduced_recurrence r] at he
    obtain ⟨hd1, hdr⟩ := Finset.mem_Icc.mp hd
    have hdr' : d ≤ r := le_trans hdr (min_le_right _ _)
    have hrd : r - d < r := by omega
    let h := (M - 1) / d
    let a := (M - 1) % d + 1
    have hhpos : 1 ≤ h := by
      apply (Nat.one_le_div_iff (by omega)).mpr
      omega
    have hhbound : h ≤ F (r - d) := by
      have ht : M - 1 < (F (r - d) + 1) * d := by
        rw [Nat.mul_comm]
        omega
      have hlt := (Nat.div_lt_iff_lt_mul (show 0 < d by omega)).mpr ht
      omega
    have ha1 : 1 ≤ a := by dsimp [a]; omega
    have had : a ≤ d := by
      have hm := Nat.mod_lt (M - 1) (show 0 < d by omega)
      dsimp [a]
      omega
    have hvalue : d * h + a = M := by
      have hm := Nat.mod_add_div (M - 1) d
      dsimp [h, a]
      omega
    obtain ⟨p, hp, hcost, hpvalue⟩ := ih (r - d) hrd h hhbound
    refine ⟨.extend p d a, ?_, ?_, ?_⟩
    · exact ⟨hp, by omega, ha1, had⟩
    · change p.cost + d ≤ r
      omega
    · change d * p.value + a = M
      rwa [hpvalue]

/-- Exact arithmetic attainable interval for the reset-program grammar. -/
theorem attainable_iff (r M : ℕ) :
    (∃ p : ResetProgram, p.Valid ∧ p.cost ≤ r ∧ p.value = M) ↔ M ≤ F r := by
  constructor
  · rintro ⟨p, hp, hcost, rfl⟩
    exact le_trans (p.value_le_F_cost hp) (F_monotone hcost)
  · exact all_values_attainable r M

end ResetProgram
end LinearAssemblies.OnePad
