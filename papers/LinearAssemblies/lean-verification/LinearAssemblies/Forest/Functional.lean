import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

set_option autoImplicit false

namespace LinearAssemblies.Forest

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A choice of one edge per state, with `none` meaning an absorbing root. -/
def step (f : S → Option S) : Option S → Option S
  | none => none
  | some i => f i

def Terminates (f : S → Option S) (i : S) : Prop :=
  ∃ k : ℕ, (step f)^[k] (some i) = none

def Rooted (f : S → Option S) : Prop := ∀ i, Terminates f i

omit [Fintype S] [DecidableEq S] in
/-- A strictly decreasing natural rank certifies that all selected paths terminate. -/
theorem rooted_of_rank (f : S → Option S) (rank : S → ℕ)
    (hr : ∀ i j, f i = some j → rank j < rank i) : Rooted f := by
  have aux : ∀ n, ∀ i, rank i = n → Terminates f i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      cases hf : f i with
      | none => exact ⟨1, by simp [step, hf]⟩
      | some j =>
        obtain ⟨k, hk⟩ := ih (rank j) (by simpa [hi] using hr i j hf) j rfl
        exact ⟨k + 1, by simpa [Function.iterate_succ_apply, step, hf] using hk⟩
  intro i
  exact aux (rank i) i rfl

omit [Fintype S] [DecidableEq S] in
theorem terminates_of_none {f : S → Option S} {i : S} (hi : f i = none) :
    Terminates f i := ⟨1, by simpa [step] using hi⟩

omit [Fintype S] [DecidableEq S] in
theorem terminates_next {f : S → Option S} {i j : S} (hij : f i = some j) :
    Terminates f i ↔ Terminates f j := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp at hk
    | succ k => exact ⟨k, by simpa [Function.iterate_succ_apply, step, hij] using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by simpa [Function.iterate_succ_apply, step, hij] using hk⟩

noncomputable def distance (f : S → Option S) (hf : Rooted f) (i : S) : ℕ :=
  Nat.find (hf i)

omit [Fintype S] in
theorem distance_drop {f : S → Option S} (hf : Rooted f) {i j : S} (hij : f i = some j) :
    distance f hf j < distance f hf i := by
  have hs := Nat.find_spec (hf i)
  have hz : distance f hf i ≠ 0 := by
    intro h
    change (step f)^[distance f hf i] (some i) = none at hs
    rw [h] at hs
    simp at hs
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
  have hs' : (step f)^[k] (some j) = none := by
    change (step f)^[distance f hf i] (some i) = none at hs
    simpa [hk, Function.iterate_succ_apply, step, hij] using hs
  have hle : distance f hf j ≤ k := Nat.find_min' (hf j) hs'
  omega

/-- The unweighted row vector contributed by the chosen outgoing edge. -/
def incidence (R : Type) [CommRing R] (f : S → Option S) : Matrix S S R :=
  fun i j => (if i = j then 1 else 0) - if f i = some j then 1 else 0

theorem incidence_mulVec {R : Type} [CommRing R] (f : S → Option S) (v : S → R) (i : S) :
    (incidence R f).mulVec v i = v i - (match f i with | none => 0 | some j => v j) := by
  unfold Matrix.mulVec dotProduct incidence
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  cases hi : f i with
  | none => simp [hi]
  | some j => simp [hi]

/-- Acyclic choices have determinant one, using distance-to-root blocks. -/
theorem det_incidence_rooted {R : Type} [CommRing R] (f : S → Option S) (hf : Rooted f) :
    (incidence R f).det = 1 := by
  let rank := distance f hf
  have ht : (incidence R f).transpose.BlockTriangular rank := by
    intro i j hij
    have hne : j ≠ i := by intro h; subst j; exact (lt_irrefl _ hij)
    have hn : f j ≠ some i := by
      intro he
      have hh := distance_drop hf he
      change rank i < rank j at hh
      omega
    simp [Matrix.transpose_apply, incidence, hne, hn]
  rw [← Matrix.det_transpose, ht.det]
  have hb : ∀ k, (incidence R f).transpose.toSquareBlock rank k = 1 := by
    intro k
    ext i j
    have hn : f j.val ≠ some i.val := by
      intro he
      have hh := distance_drop hf he
      change rank i.val < rank j.val at hh
      rw [i.property, j.property] at hh
      exact lt_irrefl k hh
    simp [Matrix.toSquareBlock_def, Matrix.toSquareBlockProp, Matrix.submatrix,
      Matrix.transpose_apply, incidence, hn, Matrix.one_apply, Subtype.ext_iff, eq_comm]
  simp_rw [hb, Matrix.det_one]
  simp

/-- Cyclic choices have determinant zero. The indicator of nonterminating states
is an explicit nonzero kernel vector, so this works over any commutative ring. -/
theorem det_incidence_not_rooted {R : Type} [CommRing R] (f : S → Option S) (hf : ¬Rooted f) :
    (incidence R f).det = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hf
  let v : S → R := fun j => if Terminates f j then 0 else 1
  have hv : (incidence R f).mulVec v = 0 := by
    ext j
    rw [incidence_mulVec]
    cases hj : f j with
    | none => simp [hj, v, terminates_of_none hj]
    | some k => simp [hj, v, terminates_next hj]
  have hh : (incidence R f).det • v = 0 := by
    calc
      (incidence R f).det • v = ((incidence R f).adjugate * incidence R f).mulVec v := by
        rw [Matrix.adjugate_mul, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hh' := congrFun hh i
  simpa [v, hi] using hh'

/-- Each edge selection contributes precisely zero or one to the determinant. -/
theorem det_incidence {R : Type} [CommRing R] (f : S → Option S) [Decidable (Rooted f)] :
    (incidence R f).det = if Rooted f then 1 else 0 := by
  classical
  split_ifs with hf
  · exact det_incidence_rooted f hf
  · exact det_incidence_not_rooted f hf

end LinearAssemblies.Forest
