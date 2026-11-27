import LinearAssemblies.TileGraph
import LinearAssemblies.Probability.Accuracy

set_option autoImplicit false

namespace LinearAssemblies.System

open LinearAssemblies.Probability

variable {I : Type} [DecidableEq I] (s : System I)
variable (compat : I → I → Prop) [DecidableRel compat]

/-- Probability of a finite interval of successful attachment counts. -/
noncomputable def attachmentWindow (a b : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc a b, (s.toGraph compat).stoppingMass k s.initialState

/-- The chain bookkeeping tick is the seed: shift attachment windows exactly once. -/
theorem attachmentWindow_eq_chain (a b : ℕ) :
    s.attachmentWindow compat a b =
      (s.toGraph compat).toChain.windowMass (a + 1) (b + 1) s.initialState := by
  unfold attachmentWindow FiniteChain.windowMass
  apply Finset.sum_bij (fun k _ => k + 1)
  · intro k hk
    simp only [Finset.mem_Icc] at *
    omega
  · intro k hk j hj he
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j - 1, ?_, by omega⟩
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [FiniteChain.absorptionProbability, UniformGraph.chain_mass_eq]

/-- Lemma 12 transferred to tile systems, for N>=4, with explicit constant 1/24.
The rounded window equals `abs (L-N) <= eps*N` by `FiniteChain.mem_window_iff`.
No mean constraint or external theorem is needed. -/
theorem accuracy_lower_bound (N : ℕ) (eps : ℝ)
    (hN : 4 ≤ N) (heps : 0 < eps) (hepsHalf : eps ≤ 1 / 2)
    (hconf : 1 / 2 ≤ s.attachmentWindow compat
      (FiniteChain.lowerEndpoint N eps) (FiniteChain.upperEndpoint N eps)) :
    min (N : ℝ) (eps⁻¹) / 24 ≤ (s.cost : ℝ) := by
  obtain ⟨ha, hw⟩ := FiniteChain.endpoint_bounds N eps hN heps hepsHalf
  let a := FiniteChain.lowerEndpoint N eps
  let b := FiniteChain.upperEndpoint N eps
  have ha' : (N : ℝ) / 4 ≤ (a + 1 : ℕ) := by
    change (N : ℝ) / 4 ≤ a at ha
    push_cast
    linarith
  have hw' : ((Finset.Icc (a + 1) (b + 1)).card : ℝ) ≤ 2 * eps * N + 1 := by
    have hc : (Finset.Icc (a + 1) (b + 1)).card = (Finset.Icc a b).card := by
      simp only [Nat.card_Icc]
      omega
    rw [hc]
    exact hw
  rw [s.attachmentWindow_eq_chain compat] at hconf
  have hb := (s.toGraph compat).toChain.accuracy_bound_of_window N (a + 1) (b + 1)
    eps s.initialState hN heps ha' hw' hconf
  have hc : (Fintype.card s.InterfaceState : ℝ) ≤ s.cost := by
    exact_mod_cast s.graph_card_le_cost
  exact le_trans hb hc

omit [DecidableEq I] in
/-- Small targets need no concentration hypothesis for this numerical lower bound. -/
theorem accuracy_small_target (N : ℕ) (eps : ℝ) (hN : N < 4) :
    min (N : ℝ) (eps⁻¹) / 24 ≤ (s.cost : ℝ) := by
  have hn : (N : ℝ) < 4 := by exact_mod_cast hN
  have hc : (1 : ℝ) ≤ s.cost := by exact_mod_cast (show 1 ≤ s.cost by simp [cost])
  have hm := min_le_left (N : ℝ) eps⁻¹
  linarith

end LinearAssemblies.System
