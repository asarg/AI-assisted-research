import LinearAssemblies.Concatenation.Blocks
import LinearAssemblies.Probability.DiscreteLaw

set_option autoImplicit false

namespace LinearAssemblies

attribute [local instance] Presentation.finiteState Presentation.finiteEntry
  OnePadBlock.decLabel TwoPadBlock.decFirst TwoPadBlock.decSecond

namespace OnePadBlock

theorem empty_mass (n : ℕ) : empty.block.mass n = if n = 0 then 1 else 0 := by
  classical
  apply Probability.UniformGraph.stoppingMass_terminal
  rw [← List.length_eq_zero_iff]
  change (OnePad.CertifiedBlock.zero.presentation.graph onePad).degree _ = 0
  rw [Presentation.graph_degree, OnePad.CertifiedBlock.presentation_degree]
  rfl

theorem join_mass (bs : List OnePadBlock) :
    (join bs).block.mass = Probability.independentSum (bs.map fun b => b.block.mass) := by
  classical
  induction bs with
  | nil => funext n; exact empty_mass n
  | cons b bs ih =>
    funext n
    change (b.block.append (join bs).block _).mass n = _
    rw [Appendable.append_mass, ih]
    rfl

theorem target_exists (M : ℕ) (hM : 1 ≤ M) :
    ∃ b : OnePadBlock, b.block.value = M ∧
      (b.block.cost : ℝ) - 1 ≤ 3 * Real.log ((M : ℝ) + 1) / Real.log 3 ∧
      ∀ x, b.block.potential x ≤ 2 * (M : ℝ) := by
  classical
  obtain ⟨b, hv, hc, hb⟩ := OnePad.onePad_block_exists M hM
  refine ⟨ofCertified b, hv, ?_, ?_⟩
  · change (b.presentation.system.cost : ℝ) - 1 ≤ _
    rw [OnePad.CertifiedBlock.presentation_cost]
    push_cast
    linarith
  · intro x
    have hx := hb x
    rw [hv] at hx
    change b.potential x ≤ _
    have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith

end OnePadBlock

namespace TwoPadBlock

theorem empty_mass (n : ℕ) : empty.block.mass n = if n = 0 then 1 else 0 := by
  classical
  change ((OnePadBlock.empty.block.p.map _ _).graph twoPad).stoppingMass n _ = _
  rw [Presentation.map_graph _ _ _ onePad_embedding]
  exact OnePadBlock.empty_mass n

theorem join_mass (bs : List TwoPadBlock) :
    (join bs).block.mass = Probability.independentSum (bs.map fun b => b.block.mass) := by
  classical
  induction bs with
  | nil => funext n; exact empty_mass n
  | cons b bs ih =>
    funext n
    change (b.block.append (join bs).block _).mass n = _
    rw [Appendable.append_mass, ih]
    rfl

theorem target_exists (M : ℕ) (hM : 1 ≤ M) :
    ∃ b : TwoPadBlock, b.block.value = M ∧
      (b.block.cost : ℝ) - 1 ≤ 72 * phi M ∧
      ∀ x, b.block.potential x ≤ 2 * (M : ℝ) := by
  classical
  have hb := selectedBase_ge_two M
  obtain ⟨d, hv⟩ := DigitData.represents (selectedBase M) M hb hM
  refine ⟨ofDigits d hb, hv, ?_, ?_⟩
  · have hc := TwoPad.cost_log_bound d hb
    rw [hv] at hc
    have hc' := hc.trans (selectedBase_cost M hM)
    change ((TwoPad.presentation d).system.cost : ℝ) - 1 ≤ _
    linarith
  · intro x
    have hx := TwoPad.potential_bound d x
    have hbase := selectedBase_le M hM
    have hbud : ((selectedBase M - 2 : ℕ) : ℝ) ≤ M := by exact_mod_cast (show selectedBase M - 2 ≤ M by omega)
    rw [hv] at hx
    change TwoPad.potential d x ≤ _
    linarith

end TwoPadBlock

end LinearAssemblies
