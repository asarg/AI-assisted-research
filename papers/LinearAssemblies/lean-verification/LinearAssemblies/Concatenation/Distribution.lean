import LinearAssemblies.Concatenation.Certificate

set_option autoImplicit false

namespace LinearAssemblies.Concatenation

open Probability

attribute [local instance] Presentation.finiteState Presentation.finiteEntry

variable {I J K : Type} (p : Presentation I) (q : Presentation J)
variable {ci : I → I → Prop} {cj : J → J → Prop} {ck : K → K → Prop}
variable (sep : SeparatedInterfaces p q ci cj ck) (exit : p.State)
variable [DecidableRel ci] [DecidableRel cj] [DecidableRel ck]

omit [DecidableRel ci] in
theorem right_simulation [DecidableEq q.State] [DecidableEq (State p q exit)] :
    UniformGraph.Simulation (q.graph cj) ((presentation p q sep exit).graph ck) Sum.inr := by
  letI : DecidableEq (presentation p q sep exit).State := inferInstanceAs (DecidableEq (State p q exit))
  constructor
  · intro y
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff]
    change ((presentation p q sep exit).graph ck).degree (.inr y) = 0 ↔
      (q.graph cj).degree y = 0
    rw [Presentation.graph_degree, Presentation.graph_degree, right_degree]
  · intro y v
    rw [Presentation.graph_next (presentation p q sep exit) ck, Presentation.graph_next q cj, right_choices_sum, right_degree]
    rfl

theorem graph_mass [DecidableEq p.State] [DecidableEq q.State]
    [DecidableEq (State p q exit)]
    (hp : ∀ x, p.degree ci x = 0 ↔ x = exit) (n : ℕ) (x : p.State) :
    ((presentation p q sep exit).graph ck).stoppingMass n (leftState p q exit x) =
      UniformGraph.convolution (fun k => (p.graph ci).stoppingMass k x)
        (fun k => (q.graph cj).stoppingMass k q.input) n := by
  classical
  letI : DecidableEq (presentation p q sep exit).State := inferInstanceAs (DecidableEq (State p q exit))
  apply UniformGraph.sequential_mass (p.graph ci) (q.graph cj)
    ((presentation p q sep exit).graph ck) exit q.input
    (leftState p q exit) Sum.inr
  · rw [← List.length_eq_zero_iff]
    change (p.graph ci).degree exit = 0
    rw [Presentation.graph_degree]
    exact (hp exit).2 rfl
  · intro y hy
    apply (hp y).1
    have he := congrArg List.length hy
    change (p.graph ci).degree y = 0 at he
    rwa [Presentation.graph_degree] at he
  · simp [leftState]
  · exact right_simulation p q sep exit
  · intro y hy he
    have hz := congrArg List.length he
    change ((presentation p q sep exit).graph ck).degree (leftState p q exit y) = 0 at hz
    rw [Presentation.graph_degree] at hz
    simp only [leftState, dif_neg hy] at hz
    rw [left_degree] at hz
    exact hy ((hp y).1 hz)
  · intro y hy v
    simp only [leftState, dif_neg hy]
    rw [Presentation.graph_next (presentation p q sep exit) ck, Presentation.graph_next p ci, left_choices_sum, left_degree]
    rfl

theorem system_mass [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [DecidableEq p.State] [DecidableEq q.State] [DecidableEq (State p q exit)]
    (hp : ∀ x, p.degree ci x = 0 ↔ x = exit) (n : ℕ) :
    ((presentation p q sep exit).system.toGraph ck).stoppingMass n
        (presentation p q sep exit).system.initialState =
      UniformGraph.convolution
        (fun k => (p.system.toGraph ci).stoppingMass k p.system.initialState)
        (fun k => (q.system.toGraph cj).stoppingMass k q.system.initialState) n := by
  classical
  letI : DecidableEq (presentation p q sep exit).State := inferInstanceAs (DecidableEq (State p q exit))
  simp only [Presentation.system_mass (presentation p q sep exit) ck,
    Presentation.system_mass p ci, Presentation.system_mass q cj]
  simp only [System.initialState, Presentation.system, Presentation.decode_expose]
  exact graph_mass p q sep exit hp n p.input

end LinearAssemblies.Concatenation
