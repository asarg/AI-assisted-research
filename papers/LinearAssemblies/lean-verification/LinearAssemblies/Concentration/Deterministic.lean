import LinearAssemblies.Concentration.Parameters

set_option autoImplicit false

namespace LinearAssemblies.OnePad.CertifiedBlock

open Probability

theorem prepend_some_mass (b : CertifiedBlock) (n : ℕ) (x : b.State) :
    (prepend b).graph.stoppingMass n (some x) = b.graph.stoppingMass n x := by
  induction n generalizing x with
  | zero => simp only [UniformGraph.stoppingMass, UniformGraph.degree, prepend, List.length_map]
  | succ n ih =>
    simp only [UniformGraph.stoppingMass, prepend, List.map_map, Function.comp_def,
      UniformGraph.degree, List.length_map]
    congr 1
    congr 1
    apply List.map_congr_left
    intro y _
    exact ih y

theorem path_mass (M n : ℕ) :
    (path M).graph.stoppingMass n (path M).input = if n = M then 1 else 0 := by
  induction M generalizing n with
  | zero => exact UniformGraph.stoppingMass_terminal zero.graph () rfl n
  | succ M ih =>
    cases n with
    | zero => simp [path, prepend, UniformGraph.stoppingMass, UniformGraph.degree]
    | succ n =>
      change (prepend (path M)).graph.stoppingMass (n + 1) none = _
      simp only [UniformGraph.stoppingMass, prepend, List.map_singleton,
        List.sum_singleton, UniformGraph.degree, List.length_singleton, Nat.cast_one, div_one]
      change (prepend (path M)).graph.stoppingMass n (some (path M).input) = _
      rw [prepend_some_mass, ih]
      simp only [Nat.add_left_inj]

end LinearAssemblies.OnePad.CertifiedBlock

namespace LinearAssemblies.Concentration

attribute [local instance] OnePadBlock.decLabel TwoPadBlock.decFirst TwoPadBlock.decSecond

theorem point_mass_deviation (M : ℕ) (t : ℝ) (ht : 0 < t) :
    Probability.deviation (fun n => if n = M then 1 else 0) (M : ℝ) t = 0 := by
  classical
  unfold Probability.deviation Probability.eventMass
  convert (tsum_zero : (∑' _ : ℕ, (0 : ℝ)) = 0) using 1
  apply tsum_congr
  intro n
  by_cases hn : n = M
  · subst n
    simp [if_pos, sub_self, abs_zero, not_lt.mpr ht.le]
  · simp [hn]

theorem deterministic_one (M : ℕ) : ∃ b : OnePadBlock,
    b.block.value = M ∧ b.block.cost = M + 1 ∧
    ∀ n, b.block.mass n = if n = M then 1 else 0 := by
  classical
  let p := OnePad.CertifiedBlock.path M
  refine ⟨OnePadBlock.ofCertified p, OnePad.CertifiedBlock.path_value M, ?_, ?_⟩
  · change p.presentation.system.cost = M + 1
    rw [OnePad.CertifiedBlock.presentation_cost, OnePad.CertifiedBlock.path_cost]
  · intro n
    change (p.presentation.graph onePad).stoppingMass n p.input = _
    rw [OnePad.CertifiedBlock.presentation_mass]
    exact OnePad.CertifiedBlock.path_mass M n

theorem deterministic_two (M : ℕ) : ∃ b : TwoPadBlock,
    b.block.value = M ∧ b.block.cost = M + 1 ∧
    ∀ n, b.block.mass n = if n = M then 1 else 0 := by
  classical
  obtain ⟨b, hv, hc, hm⟩ := deterministic_one M
  refine ⟨TwoPadBlock.ofOnePad b, hv, hc, ?_⟩
  intro n
  change ((b.block.p.map _ _).graph twoPad).stoppingMass n _ = _
  rw [Presentation.map_graph _ _ _ onePad_embedding]
  exact hm n

end LinearAssemblies.Concentration
