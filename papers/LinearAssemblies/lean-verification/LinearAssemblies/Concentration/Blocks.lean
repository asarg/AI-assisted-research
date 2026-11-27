import LinearAssemblies.Concatenation.Sequence
import LinearAssemblies.Probability.BernsteinBlocks
import LinearAssemblies.Analysis.BalancedPartition

set_option autoImplicit false

namespace LinearAssemblies.Concentration

attribute [local instance] OnePadBlock.decLabel TwoPadBlock.decFirst TwoPadBlock.decSecond

structure OneBlock where
  tiles : OnePadBlock
  positive : 1 ≤ tiles.block.value
  remaining : ∀ x, tiles.block.potential x ≤ 2 * (tiles.block.value : ℝ)
  budget : (tiles.block.cost : ℝ) - 1 ≤
    3 * Real.log ((tiles.block.value : ℝ) + 1) / Real.log 3

structure TwoBlock where
  tiles : TwoPadBlock
  positive : 1 ≤ tiles.block.value
  remaining : ∀ x, tiles.block.potential x ≤ 2 * (tiles.block.value : ℝ)
  budget : (tiles.block.cost : ℝ) - 1 ≤ 72 * phi tiles.block.value

noncomputable def OneBlock.law (ext : Probability.FiniteAbsorptionLaw) (b : OneBlock) :
    Probability.BlockLaw := b.tiles.block.blockLaw ext b.positive b.remaining

noncomputable def TwoBlock.law (ext : Probability.FiniteAbsorptionLaw) (b : TwoBlock) :
    Probability.BlockLaw := b.tiles.block.blockLaw ext b.positive b.remaining

theorem one_target (M : ℕ) (hM : 1 ≤ M) : ∃ b : OneBlock, b.tiles.block.value = M := by
  obtain ⟨b, hv, hc, hb⟩ := OnePadBlock.target_exists M hM
  refine ⟨⟨b, by omega, ?_, ?_⟩, hv⟩
  · simpa only [hv] using hb
  · simpa only [hv] using hc

theorem two_target (M : ℕ) (hM : 1 ≤ M) : ∃ b : TwoBlock, b.tiles.block.value = M := by
  obtain ⟨b, hv, hc, hb⟩ := TwoPadBlock.target_exists M hM
  refine ⟨⟨b, by omega, ?_, ?_⟩, hv⟩
  · simpa only [hv] using hb
  · simpa only [hv] using hc

theorem list_lift {A : Type*} (value : A → ℕ) (ms : List ℕ)
    (h : ∀ m ∈ ms, ∃ b : A, value b = m) : ∃ bs : List A, bs.map value = ms := by
  induction ms with
  | nil => exact ⟨[], rfl⟩
  | cons m ms ih =>
    obtain ⟨b, hb⟩ := h m (by simp)
    obtain ⟨bs, hbs⟩ := ih (fun m hm => h m (by simp [hm]))
    exact ⟨b :: bs, by simp [hb, hbs]⟩

theorem one_list (ms : List ℕ) (h : ∀ m ∈ ms, 1 ≤ m) :
    ∃ bs : List OneBlock, (bs.map fun b => b.tiles.block.value) = ms :=
  list_lift (fun b : OneBlock => b.tiles.block.value) ms (fun m hm => one_target m (h m hm))

theorem two_list (ms : List ℕ) (h : ∀ m ∈ ms, 1 ≤ m) :
    ∃ bs : List TwoBlock, (bs.map fun b => b.tiles.block.value) = ms :=
  list_lift (fun b : TwoBlock => b.tiles.block.value) ms (fun m hm => two_target m (h m hm))

theorem one_join_mass (ext : Probability.FiniteAbsorptionLaw) (bs : List OneBlock) :
    (OnePadBlock.join (bs.map OneBlock.tiles)).block.mass =
      Probability.independentSum ((bs.map (OneBlock.law ext)).map Probability.BlockLaw.mass) := by
  rw [OnePadBlock.join_mass]
  simp only [List.map_map]
  rfl

theorem two_join_mass (ext : Probability.FiniteAbsorptionLaw) (bs : List TwoBlock) :
    (TwoPadBlock.join (bs.map TwoBlock.tiles)).block.mass =
      Probability.independentSum ((bs.map (TwoBlock.law ext)).map Probability.BlockLaw.mass) := by
  rw [TwoPadBlock.join_mass]
  simp only [List.map_map]
  rfl

theorem one_join_budget (bs : List OneBlock) (U : ℝ)
    (hbound : ∀ b ∈ bs, (b.tiles.block.value : ℝ) ≤ U) :
    ((OnePadBlock.join (bs.map OneBlock.tiles)).block.cost : ℝ) ≤
      1 + 3 / Real.log 3 * bs.length * Real.log (1 + U) := by
  have hl : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  rw [OnePadBlock.join_cost, List.map_map]
  have hs : (bs.map fun b => (b.tiles.block.cost : ℝ) - 1).sum ≤
      (bs.map fun _ => (3 / Real.log 3) * Real.log (1 + U)).sum := by
    apply List.sum_le_sum
    intro b hb
    apply b.budget.trans
    have hlog : Real.log ((b.tiles.block.value : ℝ) + 1) ≤ Real.log (1 + U) :=
      Real.log_le_log (by positivity) (by linarith [hbound b hb])
    calc
      _ = (3 / Real.log 3) * Real.log ((b.tiles.block.value : ℝ) + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul] at hs
  dsimp only [Function.comp_def]
  nlinarith

theorem two_join_budget (bs : List TwoBlock) (U : ℝ)
    (hbound : ∀ b ∈ bs, (b.tiles.block.value : ℝ) ≤ U) :
    ((TwoPadBlock.join (bs.map TwoBlock.tiles)).block.cost : ℝ) ≤
      1 + 72 * bs.length * phi U := by
  rw [TwoPadBlock.join_cost, List.map_map]
  have hs : (bs.map fun b => (b.tiles.block.cost : ℝ) - 1).sum ≤
      (bs.map fun _ => 72 * phi U).sum := by
    apply List.sum_le_sum
    intro b hb
    exact b.budget.trans (mul_le_mul_of_nonneg_left
      (phi_mono (Nat.cast_nonneg _) (hbound b hb)) (by norm_num))
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul] at hs
  dsimp only [Function.comp_def]
  nlinarith

end LinearAssemblies.Concentration
