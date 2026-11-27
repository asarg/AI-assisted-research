import LinearAssemblies.UpperBounds

set_option autoImplicit false

namespace LinearAssemblies

/-- The fixed-kappa model: a match at any nonnull pad permits one attachment. -/
def kPad {κ : ℕ} {A : Type} (x y : Fin κ → Option A) : Prop := ∃ i, onePad (x i) (y i)

instance {κ : ℕ} {A : Type} [DecidableEq A] : DecidableRel (@kPad κ A) :=
  fun x y => inferInstanceAs (Decidable (∃ i, onePad (x i) (y i)))

def twoToPads {κ : ℕ} {A B : Type} (x : Option A × Option B) (i : Fin κ) : Option (A ⊕ B) :=
  if i.val = 0 then Concatenation.tagLeft x.1
  else if i.val = 1 then Concatenation.tagRight x.2 else none

theorem twoToPads_rule {κ : ℕ} {A B : Type} (hκ : 2 ≤ κ)
    (x y : Option A × Option B) : kPad (@twoToPads κ A B x) (twoToPads y) ↔ twoPad x y := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases h0 : i.val = 0
    · left
      simpa only [twoToPads, if_pos h0, Concatenation.tagLeft_rule] using hi
    · by_cases h1 : i.val = 1
      · right
        simpa only [twoToPads, if_neg h0, if_pos h1, Concatenation.tagRight_rule] using hi
      · simp only [twoToPads, if_neg h0, if_neg h1, onePad_null] at hi
  · intro h
    rcases h with h | h
    · refine ⟨⟨0, by omega⟩, ?_⟩
      simpa [twoToPads, Concatenation.tagLeft_rule] using h
    · refine ⟨⟨1, by omega⟩, ?_⟩
      simpa [twoToPads, Concatenation.tagRight_rule] using h

theorem twoToPads_injective {κ : ℕ} {A B : Type} (hκ : 2 ≤ κ) :
    Function.Injective (@twoToPads κ A B) := by
  intro x y h
  have h0 := congrFun h (⟨0, by omega⟩ : Fin κ)
  have h1 := congrFun h (⟨1, by omega⟩ : Fin κ)
  simp only [twoToPads, if_pos rfl] at h0
  simp only [twoToPads, show (1 : ℕ) ≠ 0 by omega, if_false, if_pos rfl] at h1
  exact Prod.ext (Concatenation.tagLeft_injective h0) (Concatenation.tagRight_injective h1)

namespace Appendable

variable {I J : Type} {ci : I → I → Prop} {cj : J → J → Prop}
variable [DecidableRel ci] [DecidableRel cj]

noncomputable def map (b : Appendable I ci) (f : I → J) (hf : Function.Injective f)
    (hr : ∀ x y, cj (f x) (f y) ↔ ci x y) : Appendable J cj where
  p := b.p.map f hf
  output := b.output
  value := b.value
  potential := b.potential
  certificate := b.p.map_certificate f hf hr b.certificate
  input_value := b.input_value
  unique_terminal x := by rw [Presentation.map_degree _ _ _ hr]; exact b.unique_terminal x

theorem map_cost (b : Appendable I ci) (f : I → J) (hf : Function.Injective f)
    (hr : ∀ x y, cj (f x) (f y) ↔ ci x y) : (b.map f hf hr).cost = b.cost := rfl

theorem map_mass (b : Appendable I ci) (f : I → J) (hf : Function.Injective f)
    (hr : ∀ x y, cj (f x) (f y) ↔ ci x y) : (b.map f hf hr).mass = b.mass := by
  unfold mass
  change (fun n => ((b.p.map f hf).graph cj).stoppingMass n _) = _
  rw [Presentation.map_graph _ _ _ hr]
  rfl

theorem map_concentrated [DecidableEq I] [DecidableEq J]
    (ext : Probability.FiniteAbsorptionLaw) (b : Appendable I ci)
    (f : I → J) (hf : Function.Injective f) (hr : ∀ x y, cj (f x) (f y) ↔ ci x y)
    (N ε δ : ℝ) (hs : b.p.system.Concentrated ci N ε δ) :
    (b.map f hf hr).p.system.Concentrated cj N ε δ := by
  refine ⟨(b.map f hf hr).p.system_haltable cj (b.map f hf hr).certificate, ?_, ?_⟩
  · rw [(b.map f hf hr).mean ext]
    exact (b.mean ext).symm.trans hs.2.1
  · have he : (b.map f hf hr).p.system.failureProbability cj N ε =
        b.p.system.failureProbability ci N ε := by
      unfold System.failureProbability
      congr 1
      funext n
      rw [(b.map f hf hr).system_mass, b.system_mass, map_mass]
    rw [he]
    exact hs.2.2

end Appendable

/-- Theorem 8's upper bound for every fixed number of pads kappa>=2.
Only two positions are active; all additional pads are null. -/
theorem kPad_concentrated_upper (ext : Probability.FiniteAbsorptionLaw)
    (sub : Probability.SubexponentialEquivalence) (bern : Probability.BernsteinLaw) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ N : ℕ) (ε δ : ℝ), 2 ≤ κ → 2 ≤ N → 0 < ε → ε ≤ 1 / 2 →
      0 < δ → δ ≤ 1 / 2 → ∃ (A : Type) (dec : DecidableEq A),
      letI := dec
      ∃ s : System (Fin κ → Option A), s.Concentrated kPad N ε δ ∧
        (s.cost : ℝ) ≤ C * Concentration.budgetR N ε δ * phi ((N : ℝ) / Concentration.budgetR N ε δ) := by
  classical
  obtain ⟨C, hC, hc⟩ := twoPad_concentrated_upper ext sub bern
  refine ⟨C, hC, ?_⟩
  intro κ N ε δ hκ hN hε hε1 hδ hδ1
  obtain ⟨b, hb, _, hcost⟩ := hc N ε δ hN hε hε1 hδ hδ1
  letI := b.decFirst
  letI := b.decSecond
  let q := b.block.map (@twoToPads κ b.First b.Second) (twoToPads_injective hκ) (twoToPads_rule hκ)
  refine ⟨b.First ⊕ b.Second, inferInstance, q.p.system, ?_, hcost⟩
  exact b.block.map_concentrated ext _ _ _ N ε δ hb

end LinearAssemblies
