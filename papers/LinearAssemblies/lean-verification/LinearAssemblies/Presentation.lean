import LinearAssemblies.Semantics

set_option autoImplicit false

namespace LinearAssemblies

/-- A finite tile presentation separates shared paid entries from their exposed states.
The decoder is only required to invert the exposed-state encoding. -/
structure Presentation (I : Type) where
  State : Type
  Entry : Type
  finiteState : Fintype State
  finiteEntry : Fintype Entry
  expose : State → I
  decode : I → State
  decode_expose : ∀ x, decode (expose x) = x
  input : State
  west : Entry → I
  target : Entry → State

namespace Presentation

variable {I : Type} [DecidableEq I] (p : Presentation I)
variable (compat : I → I → Prop) [DecidableRel compat]

noncomputable def enumeration : Fin (letI := p.finiteEntry; Fintype.card p.Entry) ≃ p.Entry :=
  letI := p.finiteEntry
  (Fintype.equivFin p.Entry).symm

noncomputable def system : System I where
  entryCount := letI := p.finiteEntry; Fintype.card p.Entry
  entries e := ⟨p.west (p.enumeration e), p.expose (p.target (p.enumeration e))⟩
  seedEast := p.expose p.input

noncomputable def choices (x : p.State) : Finset p.Entry :=
  letI := p.finiteEntry
  Finset.univ.filter fun e => compat (p.expose x) (p.west e)

noncomputable def degree (x : p.State) : ℕ := (p.choices compat x).card

/-- A full first-step certificate in terms of the actual shared tile entries. -/
structure Certificate (h : p.State → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ h x
  terminal : ∀ x, p.degree compat x = 0 → h x = 0
  equation : ∀ x, (p.degree compat x : ℝ) * h x = p.degree compat x +
    ∑ e ∈ p.choices compat x, h (p.target e)

omit [DecidableEq I] in
theorem choices_sum (x : p.State) (f : I → ℝ) :
    (∑ e ∈ p.system.choices compat (p.expose x), f (p.system.entries e).east) =
      ∑ e ∈ p.choices compat x, f (p.expose (p.target e)) := by
  letI := p.finiteEntry
  simp only [System.choices, choices, Finset.sum_filter, system]
  exact Fintype.sum_equiv p.enumeration _ _ (by intro e; rfl)

omit [DecidableEq I] in
theorem system_degree (x : p.State) : p.system.degree compat (p.expose x) = p.degree compat x := by
  have h := p.choices_sum compat x (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

theorem interface_exposed (x : p.system.InterfaceState) : ∃ y, x.val = p.expose y := by
  have hx := x.property
  simp only [System.interfaces, system, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and] at hx
  rcases hx with hx | ⟨e, he⟩
  · exact ⟨p.input, hx⟩
  · exact ⟨p.target (p.enumeration e), he.symm⟩

noncomputable def liftPotential (h : p.State → ℝ) (x : p.system.InterfaceState) : ℝ :=
  h (p.decode x.val)

theorem system_potential {h : p.State → ℝ} (hc : p.Certificate compat h) :
    (p.system.toGraph compat).Potential (p.liftPotential h) := by
  constructor
  · intro x; exact hc.nonneg _
  · intro x hx
    obtain ⟨y, hy⟩ := p.interface_exposed x
    have hd := congrArg List.length hx
    change (p.system.toGraph compat).degree x = 0 at hd
    rw [System.graph_degree, hy, p.system_degree compat] at hd
    simpa only [liftPotential, hy, p.decode_expose] using hc.terminal y hd
  · intro x
    obtain ⟨y, hy⟩ := p.interface_exposed x
    rw [System.graph_degree, hy, p.system_degree compat]
    simp only [System.toGraph, List.map_map, liftPotential, Function.comp_def]
    rw [Finset.sum_map_toList]
    change (p.degree compat y : ℝ) * h (p.decode x.val) = p.degree compat y +
      ∑ e ∈ p.system.choices compat x.val, h (p.decode (p.system.entries e).east)
    rw [hy, p.choices_sum compat y (fun z => h (p.decode z))]
    simp only [p.decode_expose]
    exact hc.equation y

theorem system_haltable {h : p.State → ℝ} (hc : p.Certificate compat h) :
    p.system.Haltable compat := by
  have hh := (p.system.toGraph compat).haltable_of_potential (p.system_potential compat hc)
  exact fun x _ => hh x

theorem system_mean (ext : Probability.FiniteAbsorptionLaw) {h : p.State → ℝ}
    (hc : p.Certificate compat h) : p.system.expectedLength compat = 1 + h p.input := by
  have hp := p.system_potential compat hc
  have hh := (p.system.toGraph compat).haltable_of_potential hp
  rw [p.system.expectedLength_eq compat ext (p.system_haltable compat hc),
    ext.unique _ _ hh hp]
  simp only [liftPotential, System.initialState, system, p.decode_expose]

theorem system_remaining_bound (ext : Probability.FiniteAbsorptionLaw) {h : p.State → ℝ}
    (hc : p.Certificate compat h) (M : ℝ) (hM : ∀ x, h x ≤ M) :
    ∀ x, (p.system.toGraph compat).expected x ≤ M := by
  have hp := p.system_potential compat hc
  have hh := (p.system.toGraph compat).haltable_of_potential hp
  intro x
  rw [ext.unique _ _ hh hp]
  exact hM _

end Presentation
end LinearAssemblies
