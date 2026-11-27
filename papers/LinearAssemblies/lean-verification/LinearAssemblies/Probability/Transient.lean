import LinearAssemblies.Probability.UniformGraph
import LinearAssemblies.Forest.Counts

set_option autoImplicit false

namespace LinearAssemblies.Probability.UniformGraph

open LinearAssemblies.Forest

variable {S : Type} [Fintype S] [DecidableEq S] (g : UniformGraph S)

abbrev TransientState := {i : S // g.out i ≠ []}

theorem count_subtype (p : S → Prop) [DecidablePred p] (l : List S) :
    (∑ i : {x // p x}, l.count i.val) = (l.filter p).length := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) (fun i => l.count i)]
  calc
    (∑ i ∈ Finset.univ.filter p, l.count i) =
        ∑ i ∈ Finset.univ.filter p, (l.filter p).count i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hp := (Finset.mem_filter.mp hi).2
      exact (List.count_filter (by simpa using hp)).symm
    _ = (l.filter p).length := by
      have hh := Multiset.sum_count_eq_card (s := Finset.univ.filter p)
        (m := (l.filter p : Multiset S)) (by
          intro i hi
          have hp : p i := by simpa using (List.mem_filter.mp hi).2
          simp [hp])
      simpa only [Multiset.coe_count, Multiset.coe_card] using hh

/-- Counts at unfinished interfaces, with all terminal outcomes combined. -/
def transientCounts : Counts g.TransientState where
  degree i := g.degree i.val
  transition i j := (g.out i.val).count j.val
  terminal i := ((g.out i.val).filter (fun j => g.out j = [])).length
  accounting := by
    intro i
    rw [count_subtype]
    have hh := List.length_eq_countP_add_countP (fun j => decide (g.out j ≠ [])) (l := g.out i.val)
    simpa [degree, List.countP_eq_length_filter] using hh

theorem transient_degree (i : g.TransientState) : g.transientCounts.degree i = g.degree i.val := rfl

theorem transient_degree_pos (i : g.TransientState) : 0 < g.transientCounts.degree i :=
  List.length_pos_iff.mpr i.property

theorem transient_card_le : Fintype.card g.TransientState ≤ Fintype.card S :=
  Fintype.card_subtype_le _

theorem transient_sum_degree_le : (∑ i, g.transientCounts.degree i) ≤ g.cost := by
  classical
  change (∑ i : g.TransientState, g.degree i.val) ≤ ∑ i : S, g.degree i
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => g.out i ≠ [])) (by simp) g.degree]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem transient_terminal_pos {i : g.TransientState} {j : S}
    (hij : j ∈ g.out i.val) (hj : g.out j = []) : 0 < g.transientCounts.terminal i := by
  apply List.length_pos_iff_exists_mem.mpr
  exact ⟨j, List.mem_filter.mpr ⟨hij, by simpa using hj⟩⟩

theorem transient_transition_pos {i j : g.TransientState} (hij : j.val ∈ g.out i.val) :
    0 < g.transientCounts.transition i j := List.count_pos_iff.mpr hij

/-- Every positive graph path becomes a positive-count transient path. -/
theorem transient_path {x y : S} (hxy : g.Reaches x y) (hy : g.out y = []) :
    ∀ hx : g.out x ≠ [], ∃ n, g.transientCounts.Path ⟨x, hx⟩ n := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => intro hx; exact False.elim (hx hy)
  | @head x j hxj hxy ih =>
    intro hx
    by_cases hj : g.out j = []
    · exact ⟨1, Counts.Path.stop (g.transient_terminal_pos hxj hj)⟩
    · obtain ⟨n, hn⟩ := ih hj
      exact ⟨n + 1, Counts.Path.next (g.transient_transition_pos hxj) hn⟩

theorem transient_haltable (hh : g.Haltable) : g.transientCounts.Haltable := by
  intro i
  obtain ⟨y, hiy, hy⟩ := hh i.val
  exact g.transient_path hiy hy i.property

end LinearAssemblies.Probability.UniformGraph
