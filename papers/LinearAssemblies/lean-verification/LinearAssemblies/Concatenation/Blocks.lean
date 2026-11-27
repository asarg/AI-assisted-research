import LinearAssemblies.Concatenation.FreshLabels
import LinearAssemblies.OnePad.Presentation
import LinearAssemblies.TwoPad.UpperBound
import LinearAssemblies.PresentationMap

set_option autoImplicit false

namespace LinearAssemblies

noncomputable section

local instance (priority := low) (P : Prop) : Decidable P := Classical.propDecidable P
local instance (priority := low) (A : Type) : DecidableEq A := Classical.decEq A
attribute [local instance] Presentation.finiteState Presentation.finiteEntry

/-- An appendable block carries its concrete entries and a complete first-step proof. -/
structure Appendable (I : Type) (compat : I → I → Prop) [DecidableRel compat] where
  p : Presentation I
  output : p.State
  value : ℕ
  potential : p.State → ℝ
  certificate : p.Certificate compat potential
  input_value : potential p.input = value
  unique_terminal : ∀ x, p.degree compat x = 0 ↔ x = output

namespace Appendable

variable {I J K : Type} {ci : I → I → Prop} {cj : J → J → Prop} {ck : K → K → Prop}
variable [DecidableRel ci] [DecidableRel cj] [DecidableRel ck]

noncomputable def mass (b : Appendable I ci) (n : ℕ) : ℝ := (b.p.graph ci).stoppingMass n b.p.input

noncomputable def cost (b : Appendable I ci) : ℕ := b.p.system.cost

theorem normalized (ext : Probability.FiniteAbsorptionLaw) (b : Appendable I ci) :
    HasSum b.mass 1 :=
  ext.normalized _ ((b.p.graph ci).haltable_of_potential
    (b.p.graph_potential ci b.certificate)) b.p.input

theorem mean [DecidableEq I] (ext : Probability.FiniteAbsorptionLaw) (b : Appendable I ci) :
    b.p.system.expectedLength ci = 1 + (b.value : ℝ) := by
  rw [b.p.system_mean ci ext b.certificate, b.input_value]

theorem system_mass [DecidableEq I] (b : Appendable I ci) (n : ℕ) :
    (b.p.system.toGraph ci).stoppingMass n b.p.system.initialState = b.mass n := by
  rw [b.p.system_mass ci]
  simp only [System.initialState, Presentation.system, Presentation.decode_expose, mass]

noncomputable def append (b : Appendable I ci) (c : Appendable J cj)
    (sep : SeparatedInterfaces b.p c.p ci cj ck) : Appendable K ck where
  p := Concatenation.presentation b.p c.p sep b.output
  output := Sum.inr c.output
  value := b.value + c.value
  potential := Concatenation.potential b.p c.p b.output b.potential c.potential
  certificate := Concatenation.certificate b.p c.p sep b.output b.certificate c.certificate
    ((b.unique_terminal b.output).2 rfl) (fun x => (b.unique_terminal x).1)
  input_value := by
    change Concatenation.potential b.p c.p b.output b.potential c.potential
      (Concatenation.leftState b.p c.p b.output b.p.input) = _
    rw [Concatenation.potential_left _ _ _ _ _
      (b.certificate.terminal b.output ((b.unique_terminal _).2 rfl)), b.input_value, c.input_value]
    norm_cast
  unique_terminal := Concatenation.unique_terminal b.p c.p sep b.output c.output
    b.unique_terminal c.unique_terminal

theorem append_cost (b : Appendable I ci) (c : Appendable J cj)
    (sep : SeparatedInterfaces b.p c.p ci cj ck) :
    (b.append c sep).cost + 1 = b.cost + c.cost :=
  Concatenation.cost b.p c.p sep b.output

theorem append_mass (b : Appendable I ci) (c : Appendable J cj)
    (sep : SeparatedInterfaces b.p c.p ci cj ck) (n : ℕ) :
    (b.append c sep).mass n = Probability.UniformGraph.convolution b.mass c.mass n :=
  Concatenation.graph_mass b.p c.p sep b.output b.unique_terminal n b.p.input

end Appendable

structure OnePadBlock where
  Label : Type
  decLabel : DecidableEq Label
  block : letI := decLabel; Appendable (Option Label) onePad
  nonnull : ∀ x, block.p.expose x ≠ none

attribute [local instance] OnePadBlock.decLabel

/-- Two disjoint alphabets are tracked explicitly under concatenation. -/
structure TwoPadBlock where
  First : Type
  Second : Type
  decFirst : DecidableEq First
  decSecond : DecidableEq Second
  block : letI := decFirst; letI := decSecond; Appendable (Option First × Option Second) twoPad
  nonnull : ∀ x, block.p.expose x ≠ (none, none)

attribute [local instance] TwoPadBlock.decFirst TwoPadBlock.decSecond

namespace OnePadBlock

noncomputable def ofCertified (b : OnePad.CertifiedBlock) : OnePadBlock where
  Label := b.State
  decLabel := Classical.decEq _
  block := {
    p := b.presentation
    output := b.output
    value := b.value
    potential := b.potential
    certificate := b.presentation_certificate
    input_value := b.input_value
    unique_terminal := b.presentation_terminal }
  nonnull _ := Option.some_ne_none _

noncomputable def append (b c : OnePadBlock) : OnePadBlock where
  Label := b.Label ⊕ c.Label
  decLabel := inferInstance
  block := b.block.append c.block (Concatenation.onePadSeparation b.block.p c.block.p b.nonnull)
  nonnull := Concatenation.onePad_expose_nonnull b.block.p c.block.p b.nonnull c.nonnull b.block.output

noncomputable def empty : OnePadBlock := ofCertified OnePad.CertifiedBlock.zero

noncomputable def join : List OnePadBlock → OnePadBlock
  | [] => empty
  | b :: bs => b.append (join bs)

theorem empty_value : empty.block.value = 0 := rfl
theorem empty_cost : empty.block.cost = 1 := by
  change OnePad.CertifiedBlock.zero.presentation.system.cost = 1
  rw [OnePad.CertifiedBlock.presentation_cost]
  rfl

theorem join_value (bs : List OnePadBlock) : (join bs).block.value = (bs.map fun b => b.block.value).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => change b.block.value + (join bs).block.value = _; simp [ih]

theorem join_cost (bs : List OnePadBlock) :
    ((join bs).block.cost : ℝ) = 1 + (bs.map fun b => (b.block.cost : ℝ) - 1).sum := by
  induction bs with
  | nil => simp only [join, empty_cost, Nat.cast_one, List.map_nil, List.sum_nil, add_zero]
  | cons b bs ih =>
    have hc := Appendable.append_cost b.block (join bs).block
      (Concatenation.onePadSeparation b.block.p (join bs).block.p b.nonnull)
    change (join (b :: bs)).block.cost + 1 = b.block.cost + (join bs).block.cost at hc
    have hr : ((join (b :: bs)).block.cost : ℝ) + 1 = b.block.cost + (join bs).block.cost := by
      exact_mod_cast hc
    simp only [List.map_cons, List.sum_cons]
    linarith

end OnePadBlock

namespace TwoPadBlock

noncomputable def ofOnePad (b : OnePadBlock) : TwoPadBlock where
  First := b.Label
  Second := Unit
  decFirst := b.decLabel
  decSecond := inferInstance
  block := {
    p := b.block.p.map (fun x => (x, (none : Option Unit))) (fun _ _ h => congrArg Prod.fst h)
    output := b.block.output
    value := b.block.value
    potential := b.block.potential
    certificate := b.block.p.map_certificate _ _ onePad_embedding b.block.certificate
    input_value := b.block.input_value
    unique_terminal := by
      intro x
      rw [Presentation.map_degree _ _ _ onePad_embedding]
      exact b.block.unique_terminal x }
  nonnull := by
    intro x h
    exact b.nonnull x (congrArg Prod.fst h)

noncomputable def ofDigits {b : ℕ} (d : DigitData b) (hb : 2 ≤ b) : TwoPadBlock where
  First := TwoPad.FirstLabel d
  Second := TwoPad.SecondLabel d
  decFirst := inferInstance
  decSecond := inferInstance
  block := {
    p := TwoPad.presentation d
    output := TwoPad.terminal d
    value := d.value
    potential := TwoPad.potential d
    certificate := TwoPad.certificate d hb
    input_value := TwoPad.input_potential d
    unique_terminal := TwoPad.unique_terminal d hb }
  nonnull := by
    intro x
    rcases x with j | (i | j)
    · simp [TwoPad.presentation, TwoPad.expose]
    · simp [TwoPad.presentation, TwoPad.expose]
    · simp [TwoPad.presentation, TwoPad.expose]

noncomputable def append (b c : TwoPadBlock) : TwoPadBlock where
  First := b.First ⊕ c.First
  Second := b.Second ⊕ c.Second
  decFirst := inferInstance
  decSecond := inferInstance
  block := b.block.append c.block (Concatenation.twoPadSeparation b.block.p c.block.p b.nonnull)
  nonnull := Concatenation.twoPad_expose_nonnull b.block.p c.block.p b.nonnull c.nonnull b.block.output

noncomputable def empty : TwoPadBlock := ofOnePad OnePadBlock.empty

noncomputable def join : List TwoPadBlock → TwoPadBlock
  | [] => empty
  | b :: bs => b.append (join bs)

theorem empty_value : empty.block.value = 0 := rfl
theorem empty_cost : empty.block.cost = 1 := OnePadBlock.empty_cost

theorem join_value (bs : List TwoPadBlock) : (join bs).block.value = (bs.map fun b => b.block.value).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => change b.block.value + (join bs).block.value = _; simp [ih]

theorem join_cost (bs : List TwoPadBlock) :
    ((join bs).block.cost : ℝ) = 1 + (bs.map fun b => (b.block.cost : ℝ) - 1).sum := by
  induction bs with
  | nil => simp only [join, empty_cost, Nat.cast_one, List.map_nil, List.sum_nil, add_zero]
  | cons b bs ih =>
    have hc := Appendable.append_cost b.block (join bs).block
      (Concatenation.twoPadSeparation b.block.p (join bs).block.p b.nonnull)
    change (join (b :: bs)).block.cost + 1 = b.block.cost + (join bs).block.cost at hc
    have hr : ((join (b :: bs)).block.cost : ℝ) + 1 = b.block.cost + (join bs).block.cost := by
      exact_mod_cast hc
    simp only [List.map_cons, List.sum_cons]
    linarith

end TwoPadBlock

end

end LinearAssemblies
