import LinearAssemblies.OnePad.BlockBound
import LinearAssemblies.PresentationGraph

set_option autoImplicit false

namespace LinearAssemblies.OnePad.CertifiedBlock

attribute [local instance] CertifiedBlock.finite Presentation.finiteState

noncomputable def presentation (b : CertifiedBlock) : Presentation (Option b.State) where
  State := b.State
  Entry := TileCompiler.Edge b.graph
  finiteState := b.finite
  finiteEntry := inferInstance
  expose := some
  decode x := x.getD b.input
  decode_expose _ := rfl
  input := b.input
  west e := some e.1
  target e := (b.graph.out e.1).get e.2

theorem presentation_system (b : CertifiedBlock) :
    b.presentation.system = TileCompiler.system b.graph b.input := rfl

theorem presentation_cost (b : CertifiedBlock) : b.presentation.system.cost = b.cost + 1 :=
  TileCompiler.system_cost b.graph b.input

variable (b : CertifiedBlock) [DecidableEq b.State]

theorem presentation_degree (x : b.State) :
    b.presentation.degree onePad x = b.graph.degree x := by
  rw [← Presentation.system_degree]
  exact TileCompiler.system_degree b.graph b.input x

theorem presentation_certificate : b.presentation.Certificate onePad b.potential := by
  constructor
  · exact b.certificate.nonneg
  · intro x hx
    rw [presentation_degree] at hx
    exact b.certificate.terminal x (List.length_eq_zero_iff.mp hx)
  · intro x
    rw [presentation_degree]
    have he := b.certificate.equation x
    have hs := b.presentation.choices_sum onePad x (fun y => b.potential (y.getD b.input))
    have ht := TileCompiler.choices_sum b.graph b.input x
      (fun y => b.potential (y.getD b.input))
    rw [presentation_system] at hs
    change (∑ i ∈ (TileCompiler.system b.graph b.input).choices onePad (some x),
      b.potential (((TileCompiler.system b.graph b.input).entries i).east.getD b.input)) = _ at hs
    rw [ht] at hs
    simpa only [Option.getD_some, presentation] using he.trans (congrArg
      (fun z : ℝ => (b.graph.degree x : ℝ) + z) hs)

theorem presentation_terminal (x : b.State) :
    b.presentation.degree onePad x = 0 ↔ x = b.output := by
  rw [presentation_degree]
  simpa only [Probability.UniformGraph.degree, List.length_eq_zero_iff] using b.unique_terminal x

theorem presentation_choices_sum (x : b.State) (f : b.State → ℝ) :
    (∑ e ∈ b.presentation.choices onePad x, f (b.presentation.target e)) =
      ((b.graph.out x).map f).sum := by
  have hs := b.presentation.choices_sum onePad x (fun y => f (y.getD b.input))
  rw [presentation_system] at hs
  change (∑ i ∈ (TileCompiler.system b.graph b.input).choices onePad (some x),
    f (((TileCompiler.system b.graph b.input).entries i).east.getD b.input)) = _ at hs
  rw [TileCompiler.choices_sum b.graph b.input x (fun y => f (y.getD b.input))] at hs
  simpa only [Option.getD_some, presentation] using hs.symm

theorem presentation_mass (n : ℕ) (x : b.State) :
    (b.presentation.graph onePad).stoppingMass n x = b.graph.stoppingMass n x := by
  classical
  letI : DecidableEq b.presentation.State := inferInstanceAs (DecidableEq b.State)
  apply Probability.UniformGraph.simulation_mass b.graph (b.presentation.graph onePad) id
  constructor
  · intro y
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff]
    change (b.presentation.graph onePad).degree y = 0 ↔ b.graph.degree y = 0
    rw [Presentation.graph_degree, presentation_degree]
  · intro y v
    rw [Presentation.graph_next b.presentation onePad, Probability.UniformGraph.next_eq_list, presentation_degree,
      presentation_choices_sum]
    rfl

end LinearAssemblies.OnePad.CertifiedBlock
