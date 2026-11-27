import LinearAssemblies.OnePad.TileCompiler
import LinearAssemblies.OnePad.PotentialBound
import LinearAssemblies.OnePad.ExactValue
import LinearAssemblies.Semantics

set_option autoImplicit false

namespace LinearAssemblies.OnePad

open LinearAssemblies.Probability

/-- Lemma 2: unrestricted one-pad lower bound, with only standard absorption facts assumed. -/
theorem mean_le_F (ext : FiniteAbsorptionLaw)
    {α : Type} [DecidableEq α] (s : System (Option α)) (hh : s.Haltable onePad) :
    s.expectedLength onePad ≤ 1 + (F s.entryCount : ℝ) := by
  let g := s.toGraph onePad
  let gr := g.restrict s.initialState
  let start : g.ReachableState s.initialState := ⟨s.initialState, Relation.ReflTransGen.refl⟩
  have hp : gr.Potential gr.expected := ext.first_step gr (g.restrict_haltable _ hh)
  have hb := potential_le_F_cost gr hp start
  have hc : gr.cost ≤ s.entryCount := le_trans (g.restrict_cost_le _) s.onePad_graph_cost_le
  have hf : (F gr.cost : ℝ) ≤ F s.entryCount := by exact_mod_cast F_monotone hc
  rw [s.expectedLength_eq onePad ext hh]
  have he : gr.expected start = g.expected s.initialState := g.restrict_expected _ start
  apply add_le_add_left
  change g.expected s.initialState ≤ (F s.entryCount : ℝ)
  rw [← he]
  exact le_trans hb hf

/-- A concrete finite alphabet and tile multiset realizing the requested mean and budget. -/
def Realizable (r M : ℕ) : Prop :=
  ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (s : System (Option α)),
    s.Haltable onePad ∧ s.entryCount ≤ r ∧ s.expectedLength onePad = (M : ℝ) + 1

/-- Feasibility stated using the paper's total tile cost and total expected length. -/
def LengthRealizable (m N : ℕ) : Prop :=
  ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (s : System (Option α)),
    s.Haltable onePad ∧ s.cost ≤ m ∧ s.expectedLength onePad = (N : ℝ)

theorem lengthRealizable_iff (r N : ℕ) (hN : 1 ≤ N) :
    LengthRealizable (r + 1) N ↔ Realizable r (N - 1) := by
  have he : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hN
  constructor
  · rintro ⟨α, hf, hd, s, hh, hc, hm⟩
    exact ⟨α, hf, hd, s, hh, by simpa [System.cost] using hc, by rw [he]; exact hm⟩
  · rintro ⟨α, hf, hd, s, hh, hc, hm⟩
    exact ⟨α, hf, hd, s, hh, by simpa [System.cost] using Nat.add_le_add_right hc 1,
      by rwa [he] at hm⟩

theorem block_realizes (ext : FiniteAbsorptionLaw) (b : CertifiedBlock) :
    Realizable b.cost b.value := by
  classical
  letI := b.finite
  let s := TileCompiler.system b.graph b.input
  have hp := TileCompiler.system_potential b.graph b.input b.certificate
  have hhg := (s.toGraph onePad).haltable_of_potential hp
  have hh : s.Haltable onePad := fun x _ => hhg x
  have hm := ext.unique (s.toGraph onePad) _ hhg hp s.initialState
  rw [TileCompiler.initial_potential, b.input_value] at hm
  refine ⟨b.State, b.finite, inferInstance, s, hh, ?_, ?_⟩
  · have hc := TileCompiler.system_cost b.graph b.input
    change s.entryCount + 1 = b.cost + 1 at hc
    omega
  · rw [s.expectedLength_eq onePad ext hh, hm, add_comm]

/-- Theorem 3: every and only integer attachment counts through F(r) are attainable. -/
theorem exact_characterization (ext : FiniteAbsorptionLaw) (r M : ℕ) :
    Realizable r M ↔ M ≤ F r := by
  constructor
  · rintro ⟨α, hf, hd, s, hh, hc, hm⟩
    letI := hf
    letI := hd
    have hb := mean_le_F ext s hh
    rw [hm] at hb
    have hm' : (M : ℝ) ≤ F s.entryCount := by linarith
    exact le_trans (by exact_mod_cast hm') (F_monotone hc)
  · intro hM
    obtain ⟨p, hp, hc, hv⟩ := ResetProgram.all_values_attainable r M hM
    obtain ⟨b, hbval, hbcost⟩ := CertifiedBlock.compile_exists p hp
    obtain ⟨α, hf, hd, s, hh, hsc, hsm⟩ := block_realizes ext b
    refine ⟨α, hf, hd, s, hh, ?_, ?_⟩
    · omega
    · simpa [hbval, hv] using hsm

/-- The arithmetic minimum is now identified with the minimum actual tile budget. -/
theorem minimumBudget_is_tile_minimum (ext : FiniteAbsorptionLaw) (M : ℕ) :
    Realizable (minimumBudget M) M ∧
    ∀ r, Realizable r M → minimumBudget M ≤ r := by
  refine ⟨(exact_characterization ext _ _).mpr (minimumBudget_spec M), ?_⟩
  intro r hr
  exact (minimumBudget_le_iff M r).mpr ((exact_characterization ext r M).mp hr)

/-- The seed-inclusive minimum formula for every positive integer target length. -/
theorem recurrenceCost_is_tile_minimum (ext : FiniteAbsorptionLaw) (N : ℕ) :
    Realizable (recurrenceCost N - 1) (N - 1) ∧
    ∀ r, Realizable r (N - 1) → recurrenceCost N ≤ r + 1 := by
  have h := minimumBudget_is_tile_minimum ext (N - 1)
  refine ⟨by simpa [recurrenceCost] using h.1, ?_⟩
  intro r hr
  have hh := h.2 r hr
  unfold recurrenceCost
  omega

/-- Theorem 3 in total-length/total-cost notation: existence and optimality of the formula. -/
theorem minimum_tile_cost (ext : FiniteAbsorptionLaw) (N : ℕ) (hN : 1 ≤ N) :
    LengthRealizable (recurrenceCost N) N ∧
    ∀ m, LengthRealizable m N → recurrenceCost N ≤ m := by
  have h := recurrenceCost_is_tile_minimum ext N
  have hpos : 1 ≤ recurrenceCost N := by simp [recurrenceCost]
  refine ⟨?_, ?_⟩
  · have ht := (lengthRealizable_iff (recurrenceCost N - 1) N hN).mpr h.1
    simpa only [Nat.sub_add_cancel hpos] using ht
  · intro m hm
    have hmpos : 1 ≤ m := by
      obtain ⟨α, hf, hd, s, hh, hc, he⟩ := hm
      have hs : 1 ≤ s.cost := by simp [System.cost]
      omega
    have ht : Realizable (m - 1) (N - 1) :=
      (lengthRealizable_iff (m - 1) N hN).mp (by simpa only [Nat.sub_add_cancel hmpos] using hm)
    have hb := h.2 (m - 1) ht
    simpa only [Nat.sub_add_cancel hmpos] using hb

theorem minimum_tile_cost_100 (ext : FiniteAbsorptionLaw) :
    LengthRealizable 12 100 ∧ ∀ m, LengthRealizable m 100 → 12 ≤ m := by
  simpa only [recurrenceCost_100] using minimum_tile_cost ext 100 (by omega)

/-- The worked N=100 example is a statement about tile systems, not just the recurrence. -/
theorem minimum_total_cost_100 (ext : FiniteAbsorptionLaw) :
    Realizable 11 99 ∧ ∀ r, Realizable r 99 → 12 ≤ r + 1 := by
  simpa only [recurrenceCost_100, show 100 - 1 = 99 by decide, show 12 - 1 = 11 by decide]
    using recurrenceCost_is_tile_minimum ext 100

end LinearAssemblies.OnePad
