import LinearAssemblies.Probability.BlockConcentration

set_option autoImplicit false

namespace LinearAssemblies.Probability

def BlockEstimate (a : ℝ) : Prop := ∀ (bs : List BlockLaw) (V B t : ℝ),
  0 < V → 0 < B → 0 < t →
  (bs.map fun b => (b.mean : ℝ) ^ 2).sum ≤ V →
  (∀ b ∈ bs, (b.mean : ℝ) ≤ B) →
  deviation (independentSum (bs.map BlockLaw.mass)) (bs.map fun b => (b.mean : ℝ)).sum t ≤
    2 * Real.exp (-a * min (t ^ 2 / V) (t / B))

/-- Lemma 8, with arbitrary upper bounds for the sum of squared means and the largest mean.
All block-specific premises are discharged; the hypotheses are only the two generic E03 facts. -/
theorem block_concentration (sub : SubexponentialEquivalence) (bern : BernsteinLaw) :
    ∃ a : ℝ, 0 < a ∧ ∀ (bs : List BlockLaw) (V B t : ℝ),
      0 < V → 0 < B → 0 < t →
      (bs.map fun b => (b.mean : ℝ) ^ 2).sum ≤ V →
      (∀ b ∈ bs, (b.mean : ℝ) ≤ B) →
      deviation (independentSum (bs.map BlockLaw.mass)) (bs.map fun b => (b.mean : ℝ)).sum t ≤
        2 * Real.exp (-a * min (t ^ 2 / V) (t / B)) := by
  classical
  obtain ⟨C, hC, hsub⟩ := sub
  obtain ⟨c, hc, hbern⟩ := bern
  let D : ℝ := 32 * C
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hDp : 0 < D := by linarith
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hDp
  refine ⟨c / D ^ 2, div_pos hc hD2, ?_⟩
  intro bs V B t hV hB ht hsum hmax
  let input : BlockLaw → BernsteinInput := fun b => ⟨b.mass, b.mean, D * b.mean⟩
  have hvalid : ∀ b : BlockLaw, (input b).Valid := by
    intro b
    have hM : (0 : ℝ) < b.mean := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one b.positive)
    have hh := hsub b.mass (fun n => (n : ℝ) - b.mean) (32 * b.mean)
      b.nonneg b.normalized (by positivity) b.centered_tail
    have hscale : C * (32 * (b.mean : ℝ)) = D * b.mean := by dsimp [D]; ring
    rw [hscale] at hh
    exact ⟨b.nonneg, b.normalized, b.expected, mul_pos hDp hM, hh.1, hh.2⟩
  have hsum' : ((bs.map input).map fun b => b.scale ^ 2).sum ≤ D ^ 2 * V := by
    simp only [List.map_map, input, Function.comp_def, mul_pow]
    rw [List.sum_map_mul_left]
    exact mul_le_mul_of_nonneg_left hsum hD2.le
  have hmax' : ∀ b ∈ bs.map input, b.scale ≤ D * B := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact mul_le_mul_of_nonneg_left (hmax x hx) hDp.le
  have hmain := hbern (bs.map input) (D ^ 2 * V) (D * B) t
    (by intro b hb; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb; exact hvalid x)
    (mul_pos hD2 hV) (mul_pos hDp hB) ht hsum' hmax'
  simp only [List.map_map, input, Function.comp_def] at hmain
  apply hmain.trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  let m := min (t ^ 2 / V) (t / B)
  have hm1 : m ≤ t ^ 2 / V := min_le_left _ _
  have hm2 : m ≤ t / B := min_le_right _ _
  have hscaled : m / D ^ 2 ≤ min (t ^ 2 / (D ^ 2 * V)) (t / (D * B)) := by
    apply le_min
    · have h := div_le_div_of_nonneg_right hm1 hD2.le
      convert h using 1; ring
    · calc
        m / D ^ 2 ≤ (t / B) / D ^ 2 := div_le_div_of_nonneg_right hm2 hD2.le
        _ ≤ (t / B) / D := div_le_div_of_nonneg_left (by positivity) hDp (by nlinarith)
        _ = t / (D * B) := by ring
  have he := mul_le_mul_of_nonneg_left hscaled hc.le
  change -c * min (t ^ 2 / (D ^ 2 * V)) (t / (D * B)) ≤ -(c / D ^ 2) * m
  have hr : c * (m / D ^ 2) = (c / D ^ 2) * m := by ring
  rw [hr] at he
  linarith

theorem block_estimate (sub : SubexponentialEquivalence) (bern : BernsteinLaw) :
    ∃ a : ℝ, 0 < a ∧ BlockEstimate a := block_concentration sub bern

end LinearAssemblies.Probability
