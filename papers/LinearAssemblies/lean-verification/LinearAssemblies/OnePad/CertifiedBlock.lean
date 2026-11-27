import LinearAssemblies.Probability.UniformGraph
import LinearAssemblies.OnePad.ResetProgram

set_option autoImplicit false

namespace LinearAssemblies.OnePad

open LinearAssemblies.Probability

/-- A finite uniform block with a checked nonnegative expectation potential. -/
structure CertifiedBlock where
  State : Type
  finite : Fintype State
  graph : UniformGraph State
  input : State
  output : State
  afterFirst : State
  value : ℕ
  potential : State → ℝ
  certificate : graph.Potential potential
  input_value : potential input = value
  unique_terminal : ∀ x, graph.out x = [] ↔ x = output
  first : 0 < value → graph.out input = [afterFirst]

namespace CertifiedBlock

def cost (b : CertifiedBlock) : ℕ := letI := b.finite; b.graph.cost

theorem output_value (b : CertifiedBlock) : b.potential b.output = 0 :=
  b.certificate.terminal _ ((b.unique_terminal _).mpr rfl)

theorem input_ne_output (b : CertifiedBlock) (hv : 0 < b.value) : b.input ≠ b.output := by
  intro he
  have hh := b.input_value
  rw [he, b.output_value] at hh
  have hvr : (0 : ℝ) < b.value := by exact_mod_cast hv
  linarith

theorem afterFirst_value (b : CertifiedBlock) (hv : 0 < b.value) :
    b.potential b.afterFirst = (b.value : ℝ) - 1 := by
  have hh := b.certificate.equation b.input
  have hf := b.first hv
  simp only [UniformGraph.degree, hf, List.length_singleton, Nat.cast_one,
    one_mul, List.map_singleton, List.sum_singleton] at hh
  rw [b.input_value] at hh
  linarith

def zero : CertifiedBlock where
  State := Unit
  finite := inferInstance
  graph := ⟨fun _ => []⟩
  input := ()
  output := ()
  afterFirst := ()
  value := 0
  potential := fun _ => 0
  certificate := ⟨by simp, by simp, by simp [UniformGraph.degree]⟩
  input_value := by simp
  unique_terminal := by intro x; cases x; simp
  first := by omega

/-- Add a deterministic first attachment, used to construct paths of arbitrary length. -/
def prepend (b : CertifiedBlock) : CertifiedBlock where
  State := Option b.State
  finite := letI := b.finite; inferInstance
  graph := ⟨fun x => match x with
    | none => [some b.input]
    | some x => (b.graph.out x).map some⟩
  input := none
  output := some b.output
  afterFirst := some b.input
  value := b.value + 1
  potential := fun x => match x with
    | none => (b.value : ℝ) + 1
    | some x => b.potential x
  certificate := by
    constructor
    · intro x; cases x <;> simp only
      · positivity
      · exact b.certificate.nonneg _
    · intro x hx
      cases x with
      | none => simp at hx
      | some x =>
        have hh : b.graph.out x = [] := by simpa using hx
        exact b.certificate.terminal x hh
    · intro x
      cases x with
      | none => simp [UniformGraph.degree, b.input_value, add_comm]
      | some x => simpa [UniformGraph.degree, List.map_map, Function.comp_def] using b.certificate.equation x
  input_value := by simp
  unique_terminal := by
    intro x
    cases x with
    | none => simp
    | some x => simpa using b.unique_terminal x
  first := by simp

@[simp] theorem cost_zero : zero.cost = 0 := by simp [cost, zero, UniformGraph.cost, UniformGraph.degree]

@[simp] theorem cost_prepend (b : CertifiedBlock) : (prepend b).cost = b.cost + 1 := by
  letI := b.finite
  simp [cost, prepend, UniformGraph.cost, UniformGraph.degree, Fintype.sum_option, Nat.add_comm]

def path : ℕ → CertifiedBlock
  | 0 => zero
  | n + 1 => prepend (path n)

@[simp] theorem path_value (n : ℕ) : (path n).value = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [path, prepend, ih]

@[simp] theorem path_cost (n : ℕ) : (path n).cost = n := by
  induction n with
  | zero => exact cost_zero
  | succ n ih => simp [path, ih]

end CertifiedBlock
end LinearAssemblies.OnePad
