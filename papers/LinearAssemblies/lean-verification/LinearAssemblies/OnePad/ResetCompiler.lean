import LinearAssemblies.OnePad.CertifiedBlock

set_option autoImplicit false

namespace LinearAssemblies.OnePad.CertifiedBlock

open LinearAssemblies.Probability

noncomputable def stageGraph (b : CertifiedBlock) (d a : ℕ) : UniformGraph (Option b.State) := by
  classical
  exact ⟨fun x => match x with
    | none => []
    | some x => if x = b.output then
        [none] ++ List.replicate (a - 1) (some b.input) ++ List.replicate (d - a) (some b.afterFirst)
      else (b.graph.out x).map some⟩

def offset (b : CertifiedBlock) (d a : ℕ) : ℕ := (d - 1) * b.value + a

def stagePotential (b : CertifiedBlock) (d a : ℕ) : Option b.State → ℝ
  | none => 0
  | some x => b.potential x + b.offset d a

theorem stage_degree (b : CertifiedBlock) [DecidableEq b.State] (d a : ℕ) (ha : 1 ≤ a) (had : a ≤ d) (x : b.State) :
    (stageGraph b d a).degree (some x) = if x = b.output then d else b.graph.degree x := by
  classical
  by_cases hx : x = b.output
  · simp [stageGraph, UniformGraph.degree, hx]
    omega
  · simp [stageGraph, UniformGraph.degree, hx]

theorem stage_unique_terminal (b : CertifiedBlock) (d a : ℕ) (x : Option b.State) :
    (stageGraph b d a).out x = [] ↔ x = none := by
  classical
  cases x with
  | none => simp [stageGraph]
  | some x =>
    by_cases hx : x = b.output
    · simp [stageGraph, hx]
    · simp [stageGraph, hx, b.unique_terminal x]

theorem stage_certificate (b : CertifiedBlock) (d a : ℕ) (hv : 0 < b.value)
    (ha : 1 ≤ a) (had : a ≤ d) : (stageGraph b d a).Potential (stagePotential b d a) := by
  classical
  have hd : 1 ≤ d := by omega
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; norm_num
  have ha1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub ha]; norm_num
  have hda : ((d - a : ℕ) : ℝ) = (d : ℝ) - a := by rw [Nat.cast_sub had]
  have hoff : (b.offset d a : ℝ) = ((d : ℝ) - 1) * b.value + a := by
    simp [offset, Nat.cast_add, Nat.cast_mul, hd1]
  constructor
  · intro x; cases x with
    | none => simp [stagePotential]
    | some x => exact add_nonneg (b.certificate.nonneg x) (by positivity)
  · intro x hx
    have he := (stage_unique_terminal b d a x).mp hx
    subst x
    rfl
  · intro x
    cases x with
    | none => simp [stageGraph, stagePotential, UniformGraph.degree]
    | some x =>
      rw [stage_degree b d a ha had x]
      by_cases hx : x = b.output
      · subst x
        simp only [ite_true, stagePotential, b.output_value, zero_add]
        simp [stageGraph, List.map_append, List.map_replicate, List.sum_append,
          List.sum_replicate, stagePotential, b.input_value, b.afterFirst_value hv,
          nsmul_eq_mul, ha1, hda]
        nlinarith
      · simp only [hx, if_false, stageGraph, stagePotential, List.map_map, Function.comp_def]
        have he := b.certificate.equation x
        have hadd : ∀ l : List b.State,
            (l.map (fun y => b.potential y + (b.offset d a : ℝ))).sum =
              (l.map b.potential).sum + l.length * (b.offset d a : ℝ) := by
          intro l
          induction l with
          | nil => simp
          | cons y ys ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
              Nat.cast_add, Nat.cast_one]; rw [ih]; ring
        rw [hadd]
        change _ = _ + (_ + (b.graph.degree x : ℝ) * _)
        nlinarith

noncomputable def extend (b : CertifiedBlock) (d a : ℕ) (hv : 0 < b.value)
    (ha : 1 ≤ a) (had : a ≤ d) : CertifiedBlock where
  State := Option b.State
  finite := letI := b.finite; inferInstance
  graph := stageGraph b d a
  input := some b.input
  output := none
  afterFirst := some b.afterFirst
  value := d * b.value + a
  potential := stagePotential b d a
  certificate := stage_certificate b d a hv ha had
  input_value := by
    have hd : 1 ≤ d := by omega
    have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; norm_num
    simp [stagePotential, b.input_value, offset, Nat.cast_add, Nat.cast_mul, hd1]
    ring
  unique_terminal := stage_unique_terminal b d a
  first := by
    classical
    intro _
    simp [stageGraph, b.input_ne_output hv, b.first hv]

theorem cost_extend (b : CertifiedBlock) (d a : ℕ) (hv : 0 < b.value)
    (ha : 1 ≤ a) (had : a ≤ d) : (extend b d a hv ha had).cost = b.cost + d := by
  classical
  letI := b.finite
  change (stageGraph b d a).cost = b.graph.cost + d
  simp only [UniformGraph.cost, Fintype.sum_option]
  have hn : (stageGraph b d a).degree none = 0 := by simp [stageGraph, UniformGraph.degree]
  rw [hn, zero_add]
  simp_rw [stage_degree b d a ha had]
  have ht : b.graph.degree b.output = 0 := by
    simp [UniformGraph.degree, (b.unique_terminal _).mpr rfl]
  have hi : ∀ x : b.State, (if x = b.output then d else b.graph.degree x) =
      b.graph.degree x + if x = b.output then d else 0 := by
    intro x
    by_cases hx : x = b.output <;> simp [hx, ht]
  simp_rw [hi]
  simp [Finset.sum_add_distrib]

/-- Every valid arithmetic reset program compiles to a finite certified transition block. -/
theorem compile_exists (p : ResetProgram) (hp : p.Valid) :
    ∃ b : CertifiedBlock, b.value = p.value ∧ b.cost = p.cost := by
  induction p with
  | path n => exact ⟨path n, path_value n, path_cost n⟩
  | extend p d a ih =>
    obtain ⟨hp, hv, ha, had⟩ := hp
    obtain ⟨b, hb, hc⟩ := ih hp
    have hpos : 0 < b.value := by omega
    refine ⟨extend b d a hpos ha had, ?_, ?_⟩
    · change d * b.value + a = d * p.value + a
      rw [hb]
    · rw [cost_extend]
      change b.cost + d = p.cost + d
      rw [hc]

end LinearAssemblies.OnePad.CertifiedBlock
