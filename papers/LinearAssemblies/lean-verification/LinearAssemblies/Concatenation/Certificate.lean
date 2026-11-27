import LinearAssemblies.Concatenation.Presentation

set_option autoImplicit false

namespace LinearAssemblies.Concatenation

attribute [local instance] Presentation.finiteState Presentation.finiteEntry

variable {I J K : Type} (p : Presentation I) (q : Presentation J)
variable {ci : I → I → Prop} {cj : J → J → Prop} {ck : K → K → Prop}
variable (sep : SeparatedInterfaces p q ci cj ck) (exit : p.State)

def potential (a : p.State → ℝ) (b : q.State → ℝ) : State p q exit → ℝ
  | .inl x => a x.val + b q.input
  | .inr y => b y

theorem potential_left (a : p.State → ℝ) (b : q.State → ℝ) (ha : a exit = 0)
    (x : p.State) : potential p q exit a b (leftState p q exit x) = a x + b q.input := by
  classical
  by_cases hx : x = exit
  · subst x; simp [leftState, potential, ha]
  · simp [leftState, potential, hx]

variable [DecidableRel ci] [DecidableRel cj] [DecidableRel ck]

theorem certificate {a : p.State → ℝ} {b : q.State → ℝ}
    (ha : p.Certificate ci a) (hb : q.Certificate cj b)
    (hexit : p.degree ci exit = 0) (hunique : ∀ x, p.degree ci x = 0 → x = exit) :
    (presentation p q sep exit).Certificate ck (potential p q exit a b) := by
  classical
  have haz := ha.terminal exit hexit
  constructor
  · intro x
    rcases x with x | y
    · exact add_nonneg (ha.nonneg x.val) (hb.nonneg q.input)
    · exact hb.nonneg y
  · intro x hx
    rcases x with x | y
    · rw [left_degree] at hx
      exact (x.property (hunique x.val hx)).elim
    · rw [right_degree] at hx
      exact hb.terminal y hx
  · intro x
    rcases x with x | y
    · rw [left_degree, left_choices_sum]
      simp only [potential_left p q exit a b haz, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul]
      change (p.degree ci x.val : ℝ) * (a x.val + b q.input) = _
      change _ = p.degree ci x.val +
        ((∑ e ∈ p.choices ci x.val, a (p.target e)) + p.degree ci x.val * b q.input)
      nlinarith [ha.equation x.val]
    · rw [right_degree, right_choices_sum]
      exact hb.equation y

theorem unique_terminal (out : q.State)
    (hp : ∀ x, p.degree ci x = 0 ↔ x = exit)
    (hq : ∀ y, q.degree cj y = 0 ↔ y = out) (x : State p q exit) :
    (presentation p q sep exit).degree ck x = 0 ↔ x = .inr out := by
  classical
  rcases x with x | y
  · rw [left_degree, hp]
    simp [x.property]
  · rw [right_degree, hq]
    simp

theorem mean [DecidableEq K] (ext : Probability.FiniteAbsorptionLaw)
    {a : p.State → ℝ} {b : q.State → ℝ}
    (ha : p.Certificate ci a) (hb : q.Certificate cj b)
    (hexit : p.degree ci exit = 0) (hunique : ∀ x, p.degree ci x = 0 → x = exit) :
    (presentation p q sep exit).system.expectedLength ck = 1 + a p.input + b q.input := by
  rw [Presentation.system_mean _ _ ext (certificate p q sep exit ha hb hexit hunique)]
  change 1 + potential p q exit a b (leftState p q exit p.input) = _
  rw [potential_left p q exit a b (ha.terminal exit hexit)]
  ring

end LinearAssemblies.Concatenation
