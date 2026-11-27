import LinearAssemblies.PresentationGraph

set_option autoImplicit false

namespace LinearAssemblies.Presentation

attribute [local instance] Presentation.finiteState Presentation.finiteEntry

variable {I J : Type} (p : Presentation I) (f : I → J) (hf : Function.Injective f)

noncomputable def map : Presentation J := by
  classical
  letI : Nonempty I := ⟨p.expose p.input⟩
  exact {
    State := p.State
    Entry := p.Entry
    finiteState := p.finiteState
    finiteEntry := p.finiteEntry
    expose x := f (p.expose x)
    decode y := p.decode (Function.invFun f y)
    decode_expose x := by rw [Function.leftInverse_invFun hf, p.decode_expose]
    input := p.input
    west e := f (p.west e)
    target := p.target }

theorem map_cost : (p.map f hf).system.cost = p.system.cost := rfl

variable {ci : I → I → Prop} {cj : J → J → Prop}
variable [DecidableRel ci] [DecidableRel cj]
variable (hr : ∀ x y, cj (f x) (f y) ↔ ci x y)
include hr

theorem map_choices (x : p.State) : (p.map f hf).choices cj x = p.choices ci x := by
  classical
  ext e
  simp only [choices, map, Finset.mem_filter, Finset.mem_univ, true_and, hr]

theorem map_degree (x : p.State) : (p.map f hf).degree cj x = p.degree ci x := by
  simp only [degree, map_choices p f hf hr]

theorem map_certificate {h : p.State → ℝ} (hc : p.Certificate ci h) :
    (p.map f hf).Certificate cj h := by
  constructor
  · exact hc.nonneg
  · intro x hx
    rw [map_degree p f hf hr] at hx
    exact hc.terminal x hx
  · intro x
    rw [map_degree p f hf hr, map_choices p f hf hr]
    exact hc.equation x

theorem map_graph : (p.map f hf).graph cj = p.graph ci := by
  unfold graph
  congr 1
  funext x
  rw [map_choices p f hf hr]
  rfl

end LinearAssemblies.Presentation
