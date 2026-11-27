import LinearAssemblies.OnePad.Recurrence
import LinearAssemblies.Probability.UniformGraph

set_option autoImplicit false

namespace LinearAssemblies.OnePad

open LinearAssemblies.Probability

variable {S : Type} [Fintype S] (g : UniformGraph S)

omit [Fintype S] in
/-- The paper's strictly descending path argument, without constructing the path as data. -/
private theorem descend_bound [DecidableEq S] {h : S → ℝ} (hp : g.Potential h)
    (H : ℝ) (hmax : ∀ y, h y ≤ H) (R : Finset S) :
    ∀ (a : ℕ) (x : S), x ∈ R →
      (∀ z, z ∉ R → h x ≤ h z) → H - h x ≤ F a →
      H ≤ (F (a + ∑ y ∈ R, g.degree y) : ℝ) := by
  induction' R using Finset.strongInductionOn with R ih
  intro a x hx hout hcur
  by_cases ht : g.out x = []
  · have hz := hp.terminal x ht
    have hm : F a ≤ F (a + ∑ y ∈ R, g.degree y) := F_monotone (by omega)
    have hm' : (F a : ℝ) ≤ F (a + ∑ y ∈ R, g.degree y) := by exact_mod_cast hm
    linarith
  · obtain ⟨y, hyout, hylt⟩ := g.exists_drop hp x ht
    have hyR : y ∈ R := by
      by_contra hn
      have hh := hout y hn
      linarith
    have hyx : y ≠ x := by intro he; subst y; linarith
    have hyerase : y ∈ R.erase x := Finset.mem_erase.mpr ⟨hyx, hyR⟩
    have hout' : ∀ z, z ∉ R.erase x → h y ≤ h z := by
      intro z hz
      by_cases he : z = x
      · subst z; linarith
      · have hzR : z ∉ R := by simpa [Finset.mem_erase, he] using hz
        have hh := hout z hzR
        linarith
    have hd : 1 ≤ g.degree x := List.length_pos_iff.mpr ht
    have hstep := g.deficit_step hp H hmax x y hyout
    have hm := mul_le_mul_of_nonneg_left (add_le_add_right hcur 1)
      (show (0 : ℝ) ≤ g.degree x by positivity)
    have hc := candidate_le (a + g.degree x) (g.degree x) hd (by omega)
    simp only [Nat.add_sub_cancel] at hc
    have hc' : (g.degree x : ℝ) * ((F a : ℝ) + 1) ≤ F (a + g.degree x) := by
      exact_mod_cast hc
    have hcur' : H - h y ≤ (F (a + g.degree x) : ℝ) := le_trans hstep (le_trans hm hc')
    have hs := Finset.sum_erase_add R g.degree hx
    have hi := ih (R.erase x) (Finset.erase_ssubset hx) (a + g.degree x) y hyerase hout' hcur'
    have he : a + g.degree x + ∑ z ∈ R.erase x, g.degree z = a + ∑ z ∈ R, g.degree z := by omega
    simpa only [he] using hi

/-- Lemma 2's finite-graph core: every first-step potential is at most `F(total entries)`. -/
theorem potential_le_F_cost {h : S → ℝ} (hp : g.Potential h) (start : S) :
    h start ≤ (F g.cost : ℝ) := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image Finset.univ h ⟨start, Finset.mem_univ start⟩
  have hmax : ∀ y, h y ≤ h x := fun y => hx y (Finset.mem_univ y)
  have hh := descend_bound g hp (h x) hmax Finset.univ 0 x (Finset.mem_univ x)
    (by simp) (by simp)
  have hbound : h x ≤ (F g.cost : ℝ) := by simpa [UniformGraph.cost] using hh
  exact le_trans (hmax start) hbound

end LinearAssemblies.OnePad
