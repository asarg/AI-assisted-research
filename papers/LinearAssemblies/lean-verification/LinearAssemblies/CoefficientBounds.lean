import LinearAssemblies.Semantics
import LinearAssemblies.Probability.Transient
import LinearAssemblies.Forest.Representation

set_option autoImplicit false

namespace LinearAssemblies.System

open LinearAssemblies.Probability LinearAssemblies.Forest

variable {I : Type} [DecidableEq I] (s : System I)
variable (compat : I → I → Prop) [DecidableRel compat]

/-- Exactly the reachable unfinished interfaces used in Section 6.2.1. -/
abbrev TransientState := ((s.toGraph compat).restrict s.initialState).TransientState

/-- Reachability restriction precedes removal/collapse of terminal interfaces. -/
noncomputable def absorptionCounts : Counts (s.TransientState compat) :=
  ((s.toGraph compat).restrict s.initialState).transientCounts

theorem transient_card_le_cost : Fintype.card (s.TransientState compat) ≤ s.cost := by
  have h1 := ((s.toGraph compat).restrict s.initialState).transient_card_le
  have h2 : Fintype.card ((s.toGraph compat).ReachableState s.initialState) ≤
      Fintype.card s.InterfaceState := Fintype.card_subtype_le _
  exact le_trans h1 (le_trans h2 s.graph_card_le_cost)

theorem absorptionCounts_degree_le (i : s.TransientState compat) :
    (s.absorptionCounts compat).degree i ≤ s.entryCount := by
  change ((s.toGraph compat).restrict s.initialState).transientCounts.degree i ≤ _
  rw [UniformGraph.transient_degree, UniformGraph.restrict_degree, graph_degree]
  exact s.degree_le_entryCount compat _

theorem absorptionCounts_haltable (hh : s.Haltable compat) :
    (s.absorptionCounts compat).Haltable :=
  ((s.toGraph compat).restrict s.initialState).transient_haltable
    ((s.toGraph compat).restrict_haltable s.initialState hh)

/-- Lemma 9 specialized to the actual tile model and its charged transition counts. -/
theorem tile_polynomial_representation (hh : s.Haltable compat) (start : s.TransientState compat) :
    let c := s.absorptionCounts compat
    NonnegCoeffs c.B ∧ NonnegCoeffs (c.H start) ∧
    c.B.eval 0 = (c.H start).eval 0 ∧ 1 ≤ c.B.eval 0 ∧
    c.B.natDegree ≤ Fintype.card (s.TransientState compat) ∧
    c.B.eval 1 ≤ (∏ i, (2 * (c.degree i : ℤ) - c.transition i i)) ∧
    c.B.eval 1 ≤ (∏ i, 2 * (c.degree i : ℤ)) :=
  (s.absorptionCounts compat).nonnegative_integer_representation
    (s.absorptionCounts_haltable compat hh) start

/-- Corollary 9: arbitrary compatibility, including two-pad and flexible rules. -/
theorem general_coefficient_bounds :
    (s.absorptionCounts compat).B.natDegree ≤ s.cost ∧
    (s.absorptionCounts compat).B.eval 1 ≤ (2 * (s.cost : ℤ)) ^ s.cost := by
  refine ⟨le_trans (s.absorptionCounts compat).B_degree (s.transient_card_le_cost compat), ?_⟩
  apply (s.absorptionCounts compat).general_coefficient_bound s.cost
    (by simp [cost]) (s.transient_card_le_cost compat)
  intro i
  exact le_trans (s.absorptionCounts_degree_le compat i) (by simp [cost])

theorem onePad_absorption_sum_le {α : Type} [DecidableEq α] (s : System (Option α)) :
    (∑ i, (s.absorptionCounts onePad).degree i) ≤ s.entryCount := by
  have h1 := ((s.toGraph onePad).restrict s.initialState).transient_sum_degree_le
  have h2 := (s.toGraph onePad).restrict_cost_le s.initialState
  exact le_trans h1 (le_trans h2 s.onePad_graph_cost_le)

/-- Corollary 9: one-pad systems have coefficient sum at most 2^m. -/
theorem onePad_coefficient_bounds {α : Type} [DecidableEq α] (s : System (Option α)) :
    (s.absorptionCounts onePad).B.natDegree ≤ s.cost ∧
    (s.absorptionCounts onePad).B.eval 1 ≤ (2 : ℤ) ^ s.cost := by
  refine ⟨le_trans (s.absorptionCounts onePad).B_degree (s.transient_card_le_cost onePad), ?_⟩
  exact (s.absorptionCounts onePad).onePad_coefficient_bound s.cost
    (le_trans s.onePad_absorption_sum_le (by simp [cost]))

end LinearAssemblies.System
