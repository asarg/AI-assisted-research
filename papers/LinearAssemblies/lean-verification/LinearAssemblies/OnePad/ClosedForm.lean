import LinearAssemblies.OnePad.Recurrence

set_option autoImplicit false

/-!
# Closed form for the full extremal recurrence

Equation (19) is first proved without division or subtraction:
`2 * F (3*q + 5 + j) + 3 = c_j * 3^q`.
This keeps the natural-number boundary conditions explicit.
-/

namespace LinearAssemblies.OnePad

theorem initial_values :
    F 0 = 0 ∧ F 1 = 1 ∧ F 2 = 2 ∧ F 3 = 4 ∧
    F 4 = 6 ∧ F 5 = 10 ∧ F 6 = 15 ∧ F 7 = 22 := by
  norm_num [F, Finset.range_succ]

/-- The three simultaneous residue classes in Equation (19). -/
theorem closed_form_scaled (q : ℕ) :
    (2 * F (3 * q + 5) + 3 = 23 * 3 ^ q) ∧
    (2 * F (3 * q + 6) + 3 = 33 * 3 ^ q) ∧
    (2 * F (3 * q + 7) + 3 = 47 * 3 ^ q) := by
  induction q with
  | zero => norm_num [F, Finset.range_succ]
  | succ q ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hp : 1 ≤ 3 ^ q := Nat.one_le_pow q 3 (by omega)
    have h8 := recurrence_three (3 * q + 8) (by omega)
    have h9 := recurrence_three (3 * q + 9) (by omega)
    have h10 := recurrence_three (3 * q + 10) (by omega)
    have h85 : 3 * q + 8 - 3 = 3 * q + 5 := by omega
    have h86 : 3 * q + 8 - 2 = 3 * q + 6 := by omega
    have h87 : 3 * q + 8 - 1 = 3 * q + 7 := by omega
    have h96 : 3 * q + 9 - 3 = 3 * q + 6 := by omega
    have h97 : 3 * q + 9 - 2 = 3 * q + 7 := by omega
    have h98 : 3 * q + 9 - 1 = 3 * q + 8 := by omega
    have h107 : 3 * q + 10 - 3 = 3 * q + 7 := by omega
    have h108 : 3 * q + 10 - 2 = 3 * q + 8 := by omega
    have h109 : 3 * q + 10 - 1 = 3 * q + 9 := by omega
    rw [h85, h86, h87] at h8
    rw [h96, h97, h98] at h9
    rw [h107, h108, h109] at h10
    have e8 : 2 * F (3 * q + 8) + 3 = 69 * 3 ^ q := by omega
    have e9 : 2 * F (3 * q + 9) + 3 = 99 * 3 ^ q := by omega
    have e10 : 2 * F (3 * q + 10) + 3 = 141 * 3 ^ q := by omega
    have s5 : 3 * (q + 1) + 5 = 3 * q + 8 := by omega
    have s6 : 3 * (q + 1) + 6 = 3 * q + 9 := by omega
    have s7 : 3 * (q + 1) + 7 = 3 * q + 10 := by omega
    simp only [Nat.succ_eq_add_one, s5, s6, s7, pow_succ]
    omega

theorem closed_form_zero (q : ℕ) : F (3 * q + 5) = (23 * 3 ^ q - 3) / 2 := by
  have h := (closed_form_scaled q).1
  omega

theorem closed_form_one (q : ℕ) : F (3 * q + 6) = (33 * 3 ^ q - 3) / 2 := by
  have h := (closed_form_scaled q).2.1
  omega

theorem closed_form_two (q : ℕ) : F (3 * q + 7) = (47 * 3 ^ q - 3) / 2 := by
  have h := (closed_form_scaled q).2.2
  omega

/-- A directly executable evaluation function, with constant-many cases. -/
def fastF (r : ℕ) : ℕ :=
  if r < 5 then
    match r with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | _ => 6
  else
    let q := (r - 5) / 3
    let c := match (r - 5) % 3 with
      | 0 => 23
      | 1 => 33
      | _ => 47
    (c * 3 ^ q - 3) / 2

/-- The implementation agrees with the original unrestricted recurrence. -/
theorem fastF_eq_F (r : ℕ) : fastF r = F r := by
  unfold fastF
  split_ifs with hr
  · interval_cases r <;> norm_num [F, Finset.range_succ]
  · have hmod : (r - 5) % 3 < 3 := Nat.mod_lt _ (by omega)
    have hdiv := Nat.mod_add_div (r - 5) 3
    have hr5 : 5 ≤ r := by omega
    generalize hq : (r - 5) / 3 = q at *
    generalize hj : (r - 5) % 3 = j at *
    interval_cases j
    · have he : r = 3 * q + 5 := by omega
      simpa only [he] using (closed_form_zero q).symm
    · have he : r = 3 * q + 6 := by omega
      simpa only [he] using (closed_form_one q).symm
    · have he : r = 3 * q + 7 := by omega
      simpa only [he] using (closed_form_two q).symm

example : fastF 10 = 69 := by decide
example : fastF 11 = 102 := by decide

end LinearAssemblies.OnePad
