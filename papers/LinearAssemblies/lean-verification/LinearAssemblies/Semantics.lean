import LinearAssemblies.TileGraph
import LinearAssemblies.Probability.External

set_option autoImplicit false

namespace LinearAssemblies.System

open LinearAssemblies.Probability

variable {I : Type} [DecidableEq I] (s : System I)
variable (compat : I → I → Prop) [DecidableRel compat]

/-- The paper's haltability requirement is imposed only on reachable interfaces. -/
def Haltable : Prop := (s.toGraph compat).HaltableFrom s.initialState

/-- Sum of terminal length times its probability, with the seed included.
Use this together with haltability/finite-mean proofs; an arbitrary real `tsum`
does not by itself assert convergence. -/
noncomputable def expectedLength : ℝ :=
  ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (s.toGraph compat).stoppingMass k s.initialState

theorem normalized_stopping (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat) :
    HasSum (fun k => (s.toGraph compat).stoppingMass k s.initialState) 1 := by
  let g := s.toGraph compat
  let x : g.ReachableState s.initialState := ⟨s.initialState, Relation.ReflTransGen.refl⟩
  have h := ext.normalized (g.restrict s.initialState)
    (g.restrict_haltable s.initialState hh) x
  simpa only [UniformGraph.restrict_mass] using h

theorem summable_attachments (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat) :
    Summable (fun k : ℕ => (k : ℝ) * (s.toGraph compat).stoppingMass k s.initialState) := by
  let g := s.toGraph compat
  let x : g.ReachableState s.initialState := ⟨s.initialState, Relation.ReflTransGen.refl⟩
  have h := ext.finite_mean (g.restrict s.initialState)
    (g.restrict_haltable s.initialState hh) x
  simpa only [UniformGraph.restrict_mass] using h

theorem expectedLength_eq (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat) :
    s.expectedLength compat = 1 + (s.toGraph compat).expected s.initialState := by
  have hn := s.normalized_stopping compat ext hh
  have hm := s.summable_attachments compat ext hh
  simp only [expectedLength, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  rw [hm.tsum_add hn.summable, hn.tsum_eq]
  exact add_comm _ _

theorem summable_length (ext : FiniteAbsorptionLaw) (hh : s.Haltable compat) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      (s.toGraph compat).stoppingMass k s.initialState) := by
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
    (s.summable_attachments compat ext hh).add (s.normalized_stopping compat ext hh).summable

end LinearAssemblies.System
