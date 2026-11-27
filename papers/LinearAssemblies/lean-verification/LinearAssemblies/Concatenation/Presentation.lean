import LinearAssemblies.PresentationGraph

set_option autoImplicit false

namespace LinearAssemblies

/-- Fresh-label maps preserve each block's rule and exclude all cross-block matches. -/
structure SeparatedInterfaces {I J K : Type} (p : Presentation I) (q : Presentation J)
    (ci : I → I → Prop) (cj : J → J → Prop) (ck : K → K → Prop) where
  left : I → K
  right : J → K
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  left_rule : ∀ x y, ck (left x) (left y) ↔ ci x y
  right_rule : ∀ x y, ck (right x) (right y) ↔ cj x y
  cross_left : ∀ x y, ¬ ck (left x) (right y)
  cross_right : ∀ x y, ¬ ck (right x) (left y)
  exposed_disjoint : ∀ x y, left (p.expose x) ≠ right (q.expose y)

namespace Concatenation

attribute [local instance] Presentation.finiteState Presentation.finiteEntry

variable {I J K : Type}
variable (p : Presentation I) (q : Presentation J)
variable {ci : I → I → Prop} {cj : J → J → Prop} {ck : K → K → Prop}
variable (sep : SeparatedInterfaces p q ci cj ck) (exit : p.State)

abbrev State := {x : p.State // x ≠ exit} ⊕ q.State

noncomputable def leftState (x : p.State) : State p q exit := by
  classical
  exact if hx : x = exit then .inr q.input else .inl ⟨x, hx⟩

def expose : State p q exit → K
  | .inl x => sep.left (p.expose x.val)
  | .inr y => sep.right (q.expose y)

theorem expose_injective : Function.Injective (expose p q sep exit) := by
  intro x y he
  rcases x with x | x <;> rcases y with y | y
  · have h := sep.left_injective he
    have hv := congrArg p.decode h
    simp only [p.decode_expose] at hv
    exact congrArg Sum.inl (Subtype.ext hv)
  · exact (sep.exposed_disjoint x.val y he).elim
  · exact (sep.exposed_disjoint y.val x he.symm).elim
  · have h := sep.right_injective he
    have hv := congrArg q.decode h
    simp only [q.decode_expose] at hv
    exact congrArg Sum.inr hv

noncomputable def presentation : Presentation K := by
  classical
  letI : Nonempty (State p q exit) := ⟨.inr q.input⟩
  exact {
    State := State p q exit
    Entry := p.Entry ⊕ q.Entry
    finiteState := inferInstance
    finiteEntry := inferInstance
    expose := expose p q sep exit
    decode := Function.invFun (expose p q sep exit)
    decode_expose := Function.leftInverse_invFun (expose_injective p q sep exit)
    input := leftState p q exit p.input
    west := fun e => match e with
      | .inl e => sep.left (p.west e)
      | .inr e => sep.right (q.west e)
    target := fun e => match e with
      | .inl e => leftState p q exit (p.target e)
      | .inr e => .inr (q.target e) }

/-- No connector entry is added; the seed is counted only once. -/
theorem cost : (presentation p q sep exit).system.cost + 1 = p.system.cost + q.system.cost := by
  simp [presentation, Presentation.system, System.cost, Fintype.card_sum]
  omega

variable [DecidableRel ci] [DecidableRel cj] [DecidableRel ck]

omit [DecidableRel cj] in
theorem left_choices_sum (x : {x : p.State // x ≠ exit}) (f : State p q exit → ℝ) :
    (∑ e ∈ (presentation p q sep exit).choices ck (.inl x),
      f ((presentation p q sep exit).target e)) =
      ∑ e ∈ p.choices ci x.val, f (leftState p q exit (p.target e)) := by
  classical
  simp only [Presentation.choices, Finset.sum_filter, presentation, Fintype.sum_sum_type,
    expose, sep.left_rule, sep.cross_left, if_false, Finset.sum_const_zero, add_zero]

omit [DecidableRel ci] in
theorem right_choices_sum (y : q.State) (f : State p q exit → ℝ) :
    (∑ e ∈ (presentation p q sep exit).choices ck (.inr y),
      f ((presentation p q sep exit).target e)) =
      ∑ e ∈ q.choices cj y, f (.inr (q.target e)) := by
  classical
  simp only [Presentation.choices, Finset.sum_filter, presentation, Fintype.sum_sum_type,
    expose, sep.right_rule, sep.cross_right, if_false, Finset.sum_const_zero, zero_add]

omit [DecidableRel cj] in
theorem left_degree (x : {x : p.State // x ≠ exit}) :
    (presentation p q sep exit).degree ck (.inl x) = p.degree ci x.val := by
  have h := left_choices_sum p q sep exit x (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

omit [DecidableRel ci] in
theorem right_degree (y : q.State) :
    (presentation p q sep exit).degree ck (.inr y) = q.degree cj y := by
  have h := right_choices_sum p q sep exit y (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

end Concatenation
end LinearAssemblies
