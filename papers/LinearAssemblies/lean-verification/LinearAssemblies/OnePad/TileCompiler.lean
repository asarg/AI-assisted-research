import LinearAssemblies.TileGraph
import LinearAssemblies.OnePad.ResetCompiler
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace LinearAssemblies.OnePad

open LinearAssemblies.Probability

namespace TileCompiler

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

/-- Each occurrence in an outgoing list is a separate paid tile entry. -/
abbrev Edge := Σ x : S, Fin (g.degree x)

noncomputable def enumeration : Fin (Fintype.card (Edge g)) ≃ Edge g :=
  (Fintype.equivFin (Edge g)).symm

/-- Assign one nonnull glue per graph vertex and one tile per directed occurrence. -/
noncomputable def system (start : S) : System (Option S) where
  entryCount := Fintype.card (Edge g)
  entries i := let e := (enumeration g) i
    ⟨some e.1, some ((g.out e.1).get e.2)⟩
  seedEast := some start

omit [DecidableEq S] in
theorem system_cost (start : S) : (system g start).cost = g.cost + 1 := by
  simp [System.cost, system, UniformGraph.cost, Edge, Fintype.card_sigma]

omit [Fintype S] [DecidableEq S] in
theorem sum_get (l : List S) (f : S → ℝ) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← Fin.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- Exact accounting of every legal attachment, including duplicates. -/
theorem choices_sum (start x : S) (f : Option S → ℝ) :
    (∑ i ∈ (system g start).choices onePad (some x), f ((system g start).entries i).east) =
    ((g.out x).map (fun y => f (some y))).sum := by
  classical
  simp only [System.choices, Finset.sum_filter, system, onePad,
    Option.some.injEq, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
  rw [Fintype.sum_equiv ((enumeration g))
    (fun i => if x = ((enumeration g) i).1 then f (some ((g.out ((enumeration g) i).1).get
      ((enumeration g) i).2)) else 0)
    (fun e : Edge g => if x = e.1 then f (some ((g.out e.1).get e.2)) else 0)
    (by intro i; rfl)]
  rw [Fintype.sum_sigma]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact sum_get (g.out x) (fun y => f (some y))

theorem system_degree (start x : S) : (system g start).degree onePad (some x) = g.degree x := by
  have h := choices_sum g start x (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, List.map_const', List.sum_replicate] at h
  exact_mod_cast h

theorem interface_some (start : S) (x : (system g start).InterfaceState) :
    ∃ y, x.val = some y := by
  have hx := x.property
  simp only [System.interfaces, system, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and] at hx
  rcases hx with hx | ⟨i, hi⟩
  · exact ⟨start, hx⟩
  · exact ⟨_, hi.symm⟩

noncomputable def liftPotential (start : S) (h : S → ℝ)
    (x : (system g start).InterfaceState) : ℝ := h (x.val.getD start)

/-- Compilation preserves the full nonnegative first-step certificate. -/
theorem system_potential (start : S) {h : S → ℝ} (hp : g.Potential h) :
    ((system g start).toGraph onePad).Potential (liftPotential g start h) := by
  constructor
  · intro x; exact hp.nonneg _
  · intro x hx
    obtain ⟨y, hy⟩ := interface_some g start x
    have hz : g.degree y = 0 := by
      have hh := congrArg List.length hx
      change ((system g start).toGraph onePad).degree x = 0 at hh
      simpa [System.graph_degree, hy, system_degree] using hh
    have he : g.out y = [] := List.length_eq_zero_iff.mp hz
    simpa [liftPotential, hy] using hp.terminal y he
  · intro x
    obtain ⟨y, hy⟩ := interface_some g start x
    rw [System.graph_degree, hy, system_degree]
    simp only [System.toGraph, List.map_map, liftPotential, Function.comp_def]
    rw [Finset.sum_map_toList]
    change (g.degree y : ℝ) * h (x.val.getD start) =
      (g.degree y : ℝ) + ∑ i ∈ (system g start).choices onePad x.val,
        h (((system g start).entries i).east.getD start)
    rw [hy, choices_sum g start y (fun z => h (z.getD start))]
    simpa using hp.equation y

theorem initial_potential (start : S) (h : S → ℝ) :
    liftPotential g start h (system g start).initialState = h start := rfl

end TileCompiler
end LinearAssemblies.OnePad
