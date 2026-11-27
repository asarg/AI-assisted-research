import LinearAssemblies.Probability.SubexponentialExternal
import LinearAssemblies.LowerBounds
import LinearAssemblies.Concatenation.Blocks

set_option autoImplicit false

namespace LinearAssemblies.Probability

/-- The properties of an individual block needed for the concentration argument. -/
structure BlockLaw where
  mass : ℕ → ℝ
  mean : ℕ
  positive : 1 ≤ mean
  nonneg : ∀ n, 0 ≤ mass n
  normalized : HasSum mass 1
  expected : HasSum (fun n : ℕ => (n : ℝ) * mass n) (mean : ℝ)
  geometric : ∀ j : ℕ, (∑' n, mass (n + (4 * mean * j + 1))) ≤ (1 / 2 : ℝ) ^ j

namespace BlockLaw

theorem real_tail (b : BlockLaw) (u : ℝ) (hu : 0 ≤ u) :
    magnitudeTail b.mass (fun n => (n : ℝ)) u ≤ 2 * Real.exp (-u / (16 * b.mean)) := by
  classical
  have hM : (0 : ℝ) < b.mean := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one b.positive)
  by_cases hz : u = 0
  · subst u
    simpa only [neg_zero, zero_div, Real.exp_zero, mul_one] using
      (event_le_one b.mass b.nonneg b.normalized (fun n => (0 : ℝ) ≤ |(n : ℝ)|)).trans (by norm_num : (1 : ℝ) ≤ 2)
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
  let j := ⌊u / (8 * b.mean)⌋₊
  have hj : (j : ℝ) ≤ u / (8 * b.mean) := Nat.floor_le (by positivity)
  have hj' : u / (8 * b.mean) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hju : (4 * b.mean * j : ℕ) < u := by
    have ha := (le_div_iff₀ (by positivity : 0 < 8 * (b.mean : ℝ))).mp hj
    push_cast
    nlinarith
  have htail : magnitudeTail b.mass (fun n => (n : ℝ)) u ≤
      ∑' n, b.mass (n + (4 * b.mean * j + 1)) := by
    rw [← event_nat_tail b.mass b.normalized.summable]
    apply event_mono b.mass b.nonneg b.normalized.summable
    intro n hn
    have hn' : u ≤ (n : ℝ) := by simpa only [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hn
    exact_mod_cast hju.trans_le hn'
  have hexp : (1 / 2 : ℝ) ^ j = Real.exp (-(j : ℝ) * Real.log 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div, inv_pow]
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfrac : u / (16 * (b.mean : ℝ)) ≤ (u / (8 * b.mean)) * Real.log 2 := by
    have hlog := mul_le_mul_of_nonneg_left log_two_bounds.1 (show 0 ≤ u / (8 * (b.mean : ℝ)) by positivity)
    convert hlog using 1; ring
  have hpow : (1 / 2 : ℝ) ^ j ≤ 2 * Real.exp (-u / (16 * b.mean)) := by
    rw [hexp]
    calc
      Real.exp (-(j : ℝ) * Real.log 2) ≤ Real.exp (Real.log 2 + -u / (16 * b.mean)) := by
        apply Real.exp_le_exp.mpr
        have hh := (mul_lt_mul_of_pos_right hj' hl).le
        rw [neg_div]
        nlinarith
      _ = 2 * Real.exp (-u / (16 * b.mean)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact htail.trans ((b.geometric j).trans hpow)

theorem centered_tail (b : BlockLaw) (u : ℝ) (hu : 0 ≤ u) :
    magnitudeTail b.mass (fun n => (n : ℝ) - b.mean) u ≤
      2 * Real.exp (-u / (32 * b.mean)) := by
  classical
  have hM : (0 : ℝ) < b.mean := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one b.positive)
  by_cases hsmall : u ≤ 2 * b.mean
  · have hratio : u / (32 * (b.mean : ℝ)) ≤ Real.log 2 := by
      have hr : u / (32 * (b.mean : ℝ)) ≤ 1 / 16 := by
        apply (div_le_iff₀ (by positivity)).2
        linarith
      linarith [log_two_bounds.1]
    have he : 1 ≤ 2 * Real.exp (-u / (32 * (b.mean : ℝ))) := by
      calc
        1 = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (Real.log 2 + -u / (32 * b.mean)) := by
          apply Real.exp_le_exp.mpr
          rw [neg_div]
          linarith
        _ = 2 * Real.exp (-u / (32 * b.mean)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (event_le_one b.mass b.nonneg b.normalized _).trans he
  · have hm : magnitudeTail b.mass (fun n => (n : ℝ) - b.mean) u ≤
        magnitudeTail b.mass (fun n => (n : ℝ)) u := by
      apply event_mono b.mass b.nonneg b.normalized.summable
      intro n hn
      dsimp only at hn ⊢
      rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
      rcases (le_abs.mp hn) with h | h
      · linarith
      · have hn0 := Nat.cast_nonneg (α := ℝ) n
        linarith
    apply hm.trans ((b.real_tail u hu).trans _)
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
    have hd : u / (32 * (b.mean : ℝ)) ≤ u / (16 * (b.mean : ℝ)) :=
      div_le_div_of_nonneg_left hu (by positivity) (by linarith)
    simpa only [neg_div] using neg_le_neg hd

end BlockLaw

end LinearAssemblies.Probability

namespace LinearAssemblies.Appendable

attribute [local instance] Presentation.finiteState Presentation.finiteEntry

noncomputable def blockLaw {I : Type} {compat : I → I → Prop} [DecidableRel compat]
    (ext : Probability.FiniteAbsorptionLaw) (b : Appendable I compat)
    (hpos : 1 ≤ b.value) (hbound : ∀ x, b.potential x ≤ 2 * (b.value : ℝ)) :
    Probability.BlockLaw := by
  classical
  have hp := b.p.graph_potential compat b.certificate
  have hh := (b.p.graph compat).haltable_of_potential hp
  have he := ext.unique (b.p.graph compat) b.potential hh hp
  exact {
    mass := b.mass
    mean := b.value
    positive := hpos
    nonneg n := (b.p.graph compat).stoppingMass_nonneg n b.p.input
    normalized := b.normalized ext
    expected := by
      have hs := (ext.finite_mean (b.p.graph compat) hh b.p.input).hasSum
      change HasSum (fun n : ℕ => (n : ℝ) * b.mass n) ((b.p.graph compat).expected b.p.input) at hs
      simpa only [he, b.input_value] using hs
    geometric j := by
      have hx := (b.p.graph compat).uniform_block_tail ext hh b.value hpos
        (fun x => (he x).trans_le (hbound x)) j b.p.input
      simpa only [mass, Probability.UniformGraph.tail, Nat.add_assoc] using hx }

end LinearAssemblies.Appendable
