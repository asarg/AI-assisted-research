import LinearAssemblies.Probability.UniformGraph

set_option autoImplicit false

namespace LinearAssemblies.Probability.UniformGraph

variable {S : Type} (g : UniformGraph S)

/-- Only states reachable from the actual seed must have a path to a terminal. -/
def HaltableFrom (start : S) : Prop :=
  ∀ x, g.Reaches start x → ∃ y, g.Reaches x y ∧ g.out y = []

abbrev ReachableState (start : S) := {x : S // g.Reaches start x}

noncomputable instance [Fintype S] (start : S) : Fintype (g.ReachableState start) :=
  Fintype.ofFinite _

def restrict (start : S) : UniformGraph (g.ReachableState start) where
  out x := (g.out x.val).attach.map fun y => ⟨y.val, x.property.tail y.property⟩

theorem restrict_degree (start : S) (x : g.ReachableState start) :
    (g.restrict start).degree x = g.degree x.val := by
  simp [degree, restrict]

theorem restrict_map (start : S) (f : S → ℝ) (x : g.ReachableState start) :
    ((g.restrict start).out x).map (fun y => f y.val) = (g.out x.val).map f := by
  change ((g.out x.val).attach.map _).map _ = _
  rw [List.map_map]
  change (g.out x.val).attach.map (f ∘ Subtype.val) = _
  rw [← List.map_map, List.attach_map_subtype_val]

theorem restrict_mass (start : S) (k : ℕ) (x : g.ReachableState start) :
    (g.restrict start).stoppingMass k x = g.stoppingMass k x.val := by
  induction k generalizing x with
  | zero => simp [stoppingMass, restrict_degree]
  | succ k ih =>
    rw [stoppingMass, stoppingMass, restrict_degree]
    congr 1
    simp_rw [ih]
    rw [restrict_map]

theorem restrict_expected (start : S) (x : g.ReachableState start) :
    (g.restrict start).expected x = g.expected x.val := by
  simp only [expected, restrict_mass]

theorem restrict_cost_le [Fintype S] (start : S) : (g.restrict start).cost ≤ g.cost := by
  classical
  simp only [cost, restrict_degree]
  rw [← Finset.sum_subtype (Finset.univ.filter (g.Reaches start)) (by simp) g.degree]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem restrict_reaches (start : S) (x y : g.ReachableState start)
    (h : g.Reaches x.val y.val) : (g.restrict start).Reaches x y := by
  have aux : ∀ {a b : S} (hab : g.Reaches a b), ∀ (ha : g.Reaches start a),
      (g.restrict start).Reaches ⟨a, ha⟩ ⟨b, ha.trans hab⟩ := by
    intro a b hab
    induction hab with
    | refl => intro ha; exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      intro ha
      apply (ih ha).tail
      exact List.mem_map.mpr ⟨⟨c, hbc⟩, by simp, rfl⟩
  exact aux h x.property

theorem restrict_haltable (start : S) (hh : g.HaltableFrom start) :
    (g.restrict start).Haltable := by
  intro x
  obtain ⟨y, hxy, hy⟩ := hh x.val x.property
  refine ⟨⟨y, x.property.trans hxy⟩, g.restrict_reaches start x _ hxy, ?_⟩
  simp [restrict, hy]

end LinearAssemblies.Probability.UniformGraph
