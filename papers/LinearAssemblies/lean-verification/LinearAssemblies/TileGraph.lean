import LinearAssemblies.Models
import LinearAssemblies.Probability.UniformChain

set_option autoImplicit false

namespace LinearAssemblies.System

open LinearAssemblies.Probability

variable {I : Type} [DecidableEq I] (s : System I)
variable (compat : I → I → Prop) [DecidableRel compat]

/-- The finite states are exactly the potentially exposed labels, including terminals. -/
abbrev InterfaceState := ↥s.interfaces

/-- Successful tile attachments, with one list occurrence per charged entry. -/
noncomputable def toGraph : UniformGraph s.InterfaceState where
  out x := (s.choices compat x.val).toList.map fun i => ⟨(s.entries i).east, s.east_mem_interfaces i⟩

def initialState : s.InterfaceState := ⟨s.seedEast, s.seed_mem_interfaces⟩

theorem graph_degree (x : s.InterfaceState) :
    (s.toGraph compat).degree x = s.degree compat x.val := by
  simp [toGraph, UniformGraph.degree, degree]

theorem graph_card_le_cost : Fintype.card s.InterfaceState ≤ s.cost := by
  simpa [InterfaceState] using s.card_interfaces_le_cost

/-- One-pad labels cannot share an individual tile entry between source states. -/
theorem graph_cost_le_entries
    (hunique : ∀ x y w, compat x w → compat y w → x = y) :
    (s.toGraph compat).cost ≤ s.entryCount := by
  classical
  let C : s.InterfaceState → Finset (Fin s.entryCount) := fun x => s.choices compat x.val
  have hd : (Finset.univ : Finset s.InterfaceState).toSet.PairwiseDisjoint C := by
    intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro i hix hiy
    have hx := (Finset.mem_filter.mp hix).2
    have hy := (Finset.mem_filter.mp hiy).2
    apply hxy
    exact Subtype.ext (hunique _ _ _ hx hy)
  have hc := Finset.card_biUnion hd
  have hb : (Finset.univ.biUnion C).card ≤ s.entryCount := by
    simpa using Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion C))
  rw [hc] at hb
  simpa [UniformGraph.cost, graph_degree, degree, C] using hb

theorem onePad_graph_cost_le {α : Type} [DecidableEq α] (s : System (Option α)) :
    (s.toGraph onePad).cost ≤ s.entryCount := by
  apply s.graph_cost_le_entries onePad
  intro x y w hx hy
  exact hx.1.trans hy.1.symm

/-- Terminal-length distribution, including the seed and preserving zero-step stopping. -/
noncomputable def lengthProbability (L : ℕ) : ℝ :=
  match L with
  | 0 => 0
  | k + 1 => (s.toGraph compat).stoppingMass k s.initialState

/-- Transfer of the atom bound to the actual tile interface/entry model. -/
theorem length_atom_bound (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * s.lengthProbability compat (k + 1) ≤ s.cost := by
  have h := (s.toGraph compat).toChain.atom_bound k s.initialState
  rw [UniformGraph.chain_mass_eq] at h
  have hc : (Fintype.card s.InterfaceState : ℝ) ≤ s.cost := by exact_mod_cast s.graph_card_le_cost
  exact le_trans h hc

end LinearAssemblies.System
