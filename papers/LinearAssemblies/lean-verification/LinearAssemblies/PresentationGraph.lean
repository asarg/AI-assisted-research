import LinearAssemblies.Presentation
import LinearAssemblies.Probability.Composition

set_option autoImplicit false

namespace LinearAssemblies.Presentation

open Probability

attribute [local instance] Presentation.finiteState Presentation.finiteEntry

variable {I : Type} [DecidableEq I] (p : Presentation I)
variable (compat : I → I → Prop) [DecidableRel compat]

noncomputable def graph : UniformGraph p.State where
  out x := ((p.choices compat x).toList).map p.target

omit [DecidableEq I] in
theorem graph_degree (x : p.State) : (p.graph compat).degree x = p.degree compat x := by
  simp [UniformGraph.degree, graph, degree]

variable [DecidableEq p.State]

omit [DecidableEq I] in
theorem graph_next (f : p.State → ℝ) (x : p.State) :
    (p.graph compat).next f x =
      (∑ e ∈ p.choices compat x, f (p.target e)) / p.degree compat x := by
  rw [UniformGraph.next_eq_list, p.graph_degree compat]
  simp only [graph, List.map_map, Function.comp_def, Finset.sum_map_toList]

omit [DecidableEq I] [DecidableEq p.State] in
theorem graph_potential {h : p.State → ℝ} (hc : p.Certificate compat h) :
    (p.graph compat).Potential h := by
  constructor
  · exact hc.nonneg
  · intro x hx
    have he := congrArg List.length hx
    change (p.graph compat).degree x = 0 at he
    rw [p.graph_degree compat] at he
    exact hc.terminal x he
  · intro x
    rw [p.graph_degree compat]
    simp only [graph, List.map_map, Function.comp_def, Finset.sum_map_toList]
    exact hc.equation x

/-- Entry enumeration changes list order but preserves the complete stopping law. -/
theorem system_simulation : UniformGraph.Simulation (p.system.toGraph compat) (p.graph compat)
    (fun x => p.decode x.val) := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := p.interface_exposed x
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff]
    change (p.graph compat).degree (p.decode x.val) = 0 ↔ (p.system.toGraph compat).degree x = 0
    rw [p.graph_degree compat, System.graph_degree, hy, p.decode_expose, p.system_degree compat]
  · intro x v
    obtain ⟨y, hy⟩ := p.interface_exposed x
    rw [p.graph_next compat, UniformGraph.next_eq_list, System.graph_degree]
    simp only [System.toGraph, List.map_map, Function.comp_def, Finset.sum_map_toList]
    rw [hy, p.decode_expose, p.system_degree compat,
      p.choices_sum compat y (fun z => v (p.decode z))]
    simp only [p.decode_expose]

theorem system_mass (n : ℕ) (x : p.system.InterfaceState) :
    (p.system.toGraph compat).stoppingMass n x = (p.graph compat).stoppingMass n (p.decode x.val) :=
  ((p.system.toGraph compat).simulation_mass (p.graph compat) _ (p.system_simulation compat) n x).symm

end LinearAssemblies.Presentation
