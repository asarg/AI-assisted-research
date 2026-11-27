import LinearAssemblies.Concentration.Deterministic

set_option autoImplicit false

namespace LinearAssemblies.Concentration

open Probability

attribute [local instance] OnePadBlock.decLabel TwoPadBlock.decFirst TwoPadBlock.decSecond

theorem one_balanced (ext : FiniteAbsorptionLaw) {a : ℝ} (ha : 0 < a) (hconc : BlockEstimate a)
    (N r : ℕ) (hN : 2 ≤ N) (hr : 1 ≤ r) (hrN : r ≤ N - 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ b : OnePadBlock, b.block.value = N - 1 ∧
      (b.block.cost : ℝ) ≤ 1 + 3 / Real.log 3 * r * Real.log (1 + 2 * N / r) ∧
      deviation b.block.mass ((N - 1 : ℕ) : ℝ) (ε * N) ≤ 2 * Real.exp (-a * (ε ^ 2 * r / 2)) := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hMN : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  obtain ⟨bs, hv⟩ := one_list (balanced (N - 1) r) (balanced_positive (N - 1) r hr hrN)
  have hlen : bs.length = r := by simpa only [List.length_map, balanced_length _ _ hr] using congrArg List.length hv
  have hbound : ∀ b ∈ bs, (b.tiles.block.value : ℝ) ≤ 2 * N / r := by
    intro b hb
    apply balanced_bound (N - 1) r hr hrN N hMN
    rw [← hv]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have hsum : ((bs.map (OneBlock.law ext)).map fun b => (b.mean : ℝ)).sum = (N - 1 : ℕ) := by
    calc
      _ = ((bs.map fun b => b.tiles.block.value).map (fun m : ℕ => (m : ℝ))).sum := by
        simp only [List.map_map]
        rfl
      _ = _ := by rw [hv, ← Nat.cast_list_sum, balanced_sum _ _ hr]
  have hsquares : ((bs.map (OneBlock.law ext)).map fun b => (b.mean : ℝ) ^ 2).sum ≤ 2 * (N : ℝ) ^ 2 / r := by
    calc
      _ = ((bs.map fun b => b.tiles.block.value).map (fun m : ℕ => (m : ℝ) ^ 2)).sum := by
        simp only [List.map_map]
        rfl
      _ ≤ _ := by
        rw [hv]
        exact balanced_squares (N - 1) r hr hrN N hMN
  have hm := hconc (bs.map (OneBlock.law ext)) (2 * (N : ℝ)^2 / r) (2 * N / r) (ε * N)
    (by positivity) (by positivity) (by positivity) hsquares
    (by intro b hb; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb; exact hbound x hx)
  rw [hsum, ← one_join_mass] at hm
  refine ⟨OnePadBlock.join (bs.map OneBlock.tiles), ?_, ?_, ?_⟩
  · rw [OnePadBlock.join_value, List.map_map]
    change (bs.map fun b => b.tiles.block.value).sum = _
    rw [hv, balanced_sum _ _ hr]
  · simpa only [hlen] using one_join_budget bs (2 * N / r) hbound
  · apply hm.trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
    have he := bernstein_balanced_exponent hNp hrp hε hε1
    nlinarith

theorem two_balanced (ext : FiniteAbsorptionLaw) {a : ℝ} (ha : 0 < a) (hconc : BlockEstimate a)
    (N r : ℕ) (hN : 2 ≤ N) (hr : 1 ≤ r) (hrN : r ≤ N - 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ b : TwoPadBlock, b.block.value = N - 1 ∧
      (b.block.cost : ℝ) ≤ 1 + 72 * r * phi (2 * N / r) ∧
      deviation b.block.mass ((N - 1 : ℕ) : ℝ) (ε * N) ≤ 2 * Real.exp (-a * (ε ^ 2 * r / 2)) := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hMN : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  obtain ⟨bs, hv⟩ := two_list (balanced (N - 1) r) (balanced_positive (N - 1) r hr hrN)
  have hlen : bs.length = r := by simpa only [List.length_map, balanced_length _ _ hr] using congrArg List.length hv
  have hbound : ∀ b ∈ bs, (b.tiles.block.value : ℝ) ≤ 2 * N / r := by
    intro b hb
    apply balanced_bound (N - 1) r hr hrN N hMN
    rw [← hv]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have hsum : ((bs.map (TwoBlock.law ext)).map fun b => (b.mean : ℝ)).sum = (N - 1 : ℕ) := by
    calc
      _ = ((bs.map fun b => b.tiles.block.value).map (fun m : ℕ => (m : ℝ))).sum := by
        simp only [List.map_map]
        rfl
      _ = _ := by rw [hv, ← Nat.cast_list_sum, balanced_sum _ _ hr]
  have hsquares : ((bs.map (TwoBlock.law ext)).map fun b => (b.mean : ℝ) ^ 2).sum ≤ 2 * (N : ℝ) ^ 2 / r := by
    calc
      _ = ((bs.map fun b => b.tiles.block.value).map (fun m : ℕ => (m : ℝ) ^ 2)).sum := by
        simp only [List.map_map]
        rfl
      _ ≤ _ := by
        rw [hv]
        exact balanced_squares (N - 1) r hr hrN N hMN
  have hm := hconc (bs.map (TwoBlock.law ext)) (2 * (N : ℝ)^2 / r) (2 * N / r) (ε * N)
    (by positivity) (by positivity) (by positivity) hsquares
    (by intro b hb; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb; exact hbound x hx)
  rw [hsum, ← two_join_mass] at hm
  refine ⟨TwoPadBlock.join (bs.map TwoBlock.tiles), ?_, ?_, ?_⟩
  · rw [TwoPadBlock.join_value, List.map_map]
    change (bs.map fun b => b.tiles.block.value).sum = _
    rw [hv, balanced_sum _ _ hr]
  · simpa only [hlen] using two_join_budget bs (2 * N / r) hbound
  · apply hm.trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
    have he := bernstein_balanced_exponent hNp hrp hε hε1
    nlinarith

end LinearAssemblies.Concentration
