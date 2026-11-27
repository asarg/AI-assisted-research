import LinearAssemblies.Concentration.Probabilistic
import LinearAssemblies.Concentration.Budgets

set_option autoImplicit false

namespace LinearAssemblies.System

variable {I : Type} [DecidableEq I] (s : System I)
variable (compat : I → I → Prop) [DecidableRel compat]

/-- Probability of the actual total tile length L falling outside the requested relative window. -/
noncomputable def failureProbability (N ε : ℝ) : ℝ :=
  Probability.eventMass (fun k => (s.toGraph compat).stoppingMass k s.initialState)
    (fun k => ε * N < |((k : ℝ) + 1) - N|)

def Concentrated (N ε δ : ℝ) : Prop :=
  s.Haltable compat ∧ s.expectedLength compat = N ∧ s.failureProbability compat N ε ≤ δ

theorem failure_add_window (ext : Probability.FiniteAbsorptionLaw) (hh : s.Haltable compat)
    (N : ℕ) (hN : 4 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    s.failureProbability compat N ε + s.attachmentWindow compat
      (Probability.FiniteChain.lowerEndpoint N ε) (Probability.FiniteChain.upperEndpoint N ε) = 1 := by
  classical
  have hn := s.normalized_stopping compat ext hh
  have he := Probability.event_complement
    (fun n => (s.toGraph compat).stoppingMass n s.initialState) hn
    (fun n => ε * N < |((n : ℝ) + 1) - N|)
  change s.failureProbability compat N ε + _ = 1 at he
  convert he using 1
  unfold attachmentWindow
  rw [← Probability.event_finset]
  apply congrArg (fun z : ℝ => s.failureProbability compat N ε + z)
  apply congrArg (Probability.eventMass (fun n => (s.toGraph compat).stoppingMass n s.initialState))
  funext n
  apply propext
  simp only [not_lt]
  exact Probability.FiniteChain.mem_window_iff N n ε hN hε hε1

theorem Concentrated.window (ext : Probability.FiniteAbsorptionLaw)
    (N : ℕ) (hN : 4 ≤ N) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hs : s.Concentrated compat N ε δ) :
    1 - δ ≤ s.attachmentWindow compat (Probability.FiniteChain.lowerEndpoint N ε)
      (Probability.FiniteChain.upperEndpoint N ε) := by
  have he := s.failure_add_window compat ext hs.1 N hN ε hε hε1
  linarith [hs.2.2]

end LinearAssemblies.System

namespace LinearAssemblies.Appendable

theorem failure_eq_deviation {I : Type} [DecidableEq I] {compat : I → I → Prop} [DecidableRel compat]
    (b : Appendable I compat) (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) :
    b.p.system.failureProbability compat N ε =
      Probability.deviation b.mass ((N - 1 : ℕ) : ℝ) (ε * N) := by
  classical
  unfold System.failureProbability Probability.deviation Probability.eventMass
  apply tsum_congr
  intro k
  have hshift : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast Nat.sub_add_cancel hN
  have he : ((k : ℝ) + 1) - N = (k : ℝ) - (N - 1 : ℕ) := by linarith
  dsimp only
  rw [he, b.system_mass]

theorem concentrated {I : Type} [DecidableEq I] {compat : I → I → Prop} [DecidableRel compat]
    (ext : Probability.FiniteAbsorptionLaw) (b : Appendable I compat)
    (N : ℕ) (hN : 1 ≤ N) (ε δ : ℝ) (hv : b.value = N - 1)
    (hf : Probability.deviation b.mass ((N - 1 : ℕ) : ℝ) (ε * N) ≤ δ) :
    b.p.system.Concentrated compat N ε δ := by
  refine ⟨b.p.system_haltable compat b.certificate, ?_, ?_⟩
  · rw [b.mean ext, hv]
    exact_mod_cast (show 1 + (N - 1) = N by omega)
  · rwa [failure_eq_deviation b N hN ε]

end LinearAssemblies.Appendable
