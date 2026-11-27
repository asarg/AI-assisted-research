import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

namespace LinearAssemblies.Probability

/-- A finite-state uniform transition system. Repeated successors are separate choices. -/
structure UniformGraph (S : Type) where
  out : S → List S

namespace UniformGraph

variable {S : Type} (g : UniformGraph S)

def degree (x : S) : ℕ := (g.out x).length

def cost [Fintype S] : ℕ := ∑ x, g.degree x

/-- Exact stopping distribution: a terminal starting state stops at time zero. -/
noncomputable def stoppingMass : ℕ → S → ℝ
  | 0, x => if g.degree x = 0 then 1 else 0
  | k + 1, x => ((g.out x).map (fun y => stoppingMass k y)).sum / g.degree x

/-- Expected successful attachments. Finiteness is a separate proof obligation. -/
noncomputable def expected (x : S) : ℝ := ∑' k : ℕ, (k : ℝ) * g.stoppingMass k x

/-- Finite paths follow positive uniform transition choices. -/
def Reaches (x y : S) : Prop := Relation.ReflTransGen (fun x y => y ∈ g.out x) x y

def Haltable : Prop := ∀ x, ∃ y, g.Reaches x y ∧ g.out y = []

/-- The nonnegative first-step equations, including the terminal boundary. -/
structure Potential (h : S → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ h x
  terminal : ∀ x, g.out x = [] → h x = 0
  equation : ∀ x, (g.degree x : ℝ) * h x =
    (g.degree x : ℝ) + ((g.out x).map h).sum

theorem sum_map_nonneg (l : List S) (f : S → ℝ) (hf : ∀ x ∈ l, 0 ≤ f x) :
    0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (hf x (by simp)) (ih (fun y hy => hf y (by simp [hy])))

theorem member_le_sum (l : List S) (f : S → ℝ) (hf : ∀ x ∈ l, 0 ≤ f x)
    (x : S) (hx : x ∈ l) : f x ≤ (l.map f).sum := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.map_cons, List.sum_cons]
    rcases hx with rfl | hx
    · exact le_add_of_nonneg_right (sum_map_nonneg ys f (fun z hz => hf z (by simp [hz])))
    · have h := ih (fun z hz => hf z (by simp [hz])) hx
      have hn := hf y (by simp)
      linarith

theorem constant_le_sum (l : List S) (f : S → ℝ) (a : ℝ)
    (hf : ∀ x ∈ l, a ≤ f x) : (l.length : ℝ) * a ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hh := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
    nlinarith

theorem exists_drop {h : S → ℝ} (hp : g.Potential h) (x : S) (hx : g.out x ≠ []) :
    ∃ y ∈ g.out x, h y < h x := by
  by_contra hn
  push_neg at hn
  have hs := constant_le_sum (g.out x) h (h x) hn
  have he := hp.equation x
  have hd : 0 < g.degree x := List.length_pos_iff.mpr hx
  have hd' : (0 : ℝ) < g.degree x := by exact_mod_cast hd
  change (g.degree x : ℝ) * h x ≤ _ at hs
  linarith

theorem sum_deficit {h : S → ℝ} (hp : g.Potential h) (H : ℝ) (x : S) :
    ((g.out x).map (fun y => H - h y)).sum = (g.degree x : ℝ) * (H - h x + 1) := by
  have he := hp.equation x
  have hs : ∀ l : List S, (l.map (fun y => H - h y)).sum =
      (l.length : ℝ) * H - (l.map h).sum := by
    intro l
    induction l with
    | nil => simp
    | cons y ys ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]; rw [ih]; ring
  rw [hs]
  change (g.degree x : ℝ) * H - _ = _
  nlinarith

theorem deficit_step {h : S → ℝ} (hp : g.Potential h) (H : ℝ)
    (hmax : ∀ y, h y ≤ H) (x y : S) (hy : y ∈ g.out x) :
    H - h y ≤ (g.degree x : ℝ) * (H - h x + 1) := by
  rw [← g.sum_deficit hp H x]
  exact member_le_sum _ _ (fun z _ => sub_nonneg.mpr (hmax z)) y hy

/-- A nonnegative first-step potential forces graph haltability. -/
theorem haltable_of_potential [Fintype S] {h : S → ℝ} (hp : g.Potential h) : g.Haltable := by
  classical
  intro x
  let R := Finset.univ.filter (g.Reaches x)
  have hx : x ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ x, Relation.ReflTransGen.refl⟩
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image R h ⟨x, hx⟩
  have hxy : g.Reaches x y := (Finset.mem_filter.mp hy).2
  refine ⟨y, hxy, ?_⟩
  by_cases hn : g.out y = []
  · exact hn
  exfalso
  obtain ⟨z, hz, hlt⟩ := g.exists_drop hp y hn
  have hxz : g.Reaches x z := hxy.tail hz
  have hzR : z ∈ R := by simp [R, hxz]
  have hh := hmin z hzR
  linarith

end UniformGraph
end LinearAssemblies.Probability
