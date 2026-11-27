import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Tile entries and compatibility

Nonseed entries are indexed by `Fin entryCount`. Distinct indices may carry
identical tiles. Hence multiplicities are charged and sampled separately.
The seed is represented by its east interface; its inert west side never
participates in growth. This module describes successful attachments only.
-/

namespace LinearAssemblies

structure Tile (Interface : Type*) where
  west : Interface
  east : Interface
  deriving DecidableEq

structure System (Interface : Type*) where
  entryCount : ℕ
  entries : Fin entryCount → Tile Interface
  seedEast : Interface

namespace System

variable {I J : Type*}

def cost (s : System I) : ℕ := s.entryCount + 1

def map (s : System I) (f : I → J) : System J where
  entryCount := s.entryCount
  entries i := ⟨f (s.entries i).west, f (s.entries i).east⟩
  seedEast := f s.seedEast

@[simp] theorem cost_map (s : System I) (f : I → J) : (s.map f).cost = s.cost := rfl

variable [DecidableEq I]

/-- Every potentially exposed interface is the seed's east side or an entry's east side. -/
def interfaces (s : System I) : Finset I :=
  insert s.seedEast (Finset.univ.image fun i => (s.entries i).east)

theorem seed_mem_interfaces (s : System I) : s.seedEast ∈ s.interfaces := by
  simp [interfaces]

theorem east_mem_interfaces (s : System I) (i : Fin s.entryCount) :
    (s.entries i).east ∈ s.interfaces := by
  simp only [interfaces, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, rfl⟩

/-- The finite interface bound used in Corollary 9, before removing terminal states. -/
theorem card_interfaces_le_cost (s : System I) : s.interfaces.card ≤ s.cost := by
  calc
    s.interfaces.card ≤ (Finset.univ.image fun i => (s.entries i).east).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (Finset.univ : Finset (Fin s.entryCount)).card + 1 :=
      Nat.add_le_add_right (Finset.card_image_le) 1
    _ = s.cost := by simp [cost]

variable (compat : I → I → Prop) [DecidableRel compat]

def choices (s : System I) (x : I) : Finset (Fin s.entryCount) :=
  Finset.univ.filter fun i => compat x (s.entries i).west

def degree (s : System I) (x : I) : ℕ := (s.choices compat x).card

omit [DecidableEq I] in
theorem degree_le_entryCount (s : System I) (x : I) :
    s.degree compat x ≤ s.entryCount := by
  simpa [degree] using Finset.card_le_card (Finset.filter_subset
    (fun i => compat x (s.entries i).west) (Finset.univ : Finset (Fin s.entryCount)))

def unfinishedInterfaces (s : System I) : Finset I :=
  s.interfaces.filter fun x => 0 < s.degree compat x

theorem card_unfinished_le_cost (s : System I) :
    (s.unfinishedInterfaces compat).card ≤ s.cost :=
  le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (s.card_interfaces_le_cost)

/-- Conditional probability of the next successful entry. Duplicates retain separate indices. -/
def entryProbability (s : System I) (x : I) (i : Fin s.entryCount) : ℚ :=
  if i ∈ s.choices compat x then 1 / (s.degree compat x : ℚ) else 0

omit [DecidableEq I] in
theorem entryProbability_nonneg (s : System I) (x : I) (i : Fin s.entryCount) :
    0 ≤ s.entryProbability compat x i := by
  unfold entryProbability
  split_ifs <;> positivity

omit [DecidableEq I] in
theorem entryProbability_sum (s : System I) (x : I) (hx : 0 < s.degree compat x) :
    ∑ i ∈ s.choices compat x, s.entryProbability compat x i = 1 := by
  have hn : (s.degree compat x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  simp only [entryProbability, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
    nsmul_eq_mul]
  change (s.degree compat x : ℚ) * (1 / (s.degree compat x : ℚ)) = 1
  field_simp

end System

/-- A nonnull matching label is the one-pad rule. -/
def onePad {α : Type*} (x y : Option α) : Prop := x = y ∧ x ≠ none

/-- One matching nonnull position suffices; matching twice still selects the entry once. -/
def twoPad {α β : Type*} (x y : Option α × Option β) : Prop :=
  onePad x.1 y.1 ∨ onePad x.2 y.2

instance {α : Type*} [DecidableEq α] : DecidableRel (@onePad α) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _ ∧ _ ≠ none))

instance {α β : Type*} [DecidableEq α] [DecidableEq β] : DecidableRel (@twoPad α β) :=
  fun _ _ => inferInstanceAs (Decidable (onePad _ _ ∨ onePad _ _))

theorem onePad_symmetric {α : Type*} : Symmetric (@onePad α) := by
  rintro x y ⟨hxy, hx⟩
  subst y
  exact ⟨rfl, hx⟩

theorem twoPad_symmetric {α β : Type*} : Symmetric (@twoPad α β) := by
  intro x y h
  exact h.elim (fun h => Or.inl (onePad_symmetric h))
    (fun h => Or.inr (onePad_symmetric h))

@[simp] theorem onePad_null {α : Type*} (x : Option α) : ¬ onePad none x := by
  simp [onePad]

@[simp] theorem twoPad_null {α β : Type*} (x : Option α × Option β) :
    ¬ twoPad (none, none) x := by simp [twoPad]

/-- The one-pad to two-pad embedding preserves compatibility exactly. -/
theorem onePad_embedding {α : Type*} (x y : Option α) :
    @twoPad α Unit (x, none) (y, none) ↔ onePad x y := by
  simp [twoPad, onePad]

structure FlexibleRule (I : Type*) where
  null : I
  binds : I → I → Prop
  symmetric : Symmetric binds
  inert : ∀ x, ¬ binds null x

/-- Pair labels can be treated as single flexible labels at unchanged tile cost. -/
def twoPadFlexibleRule (α β : Type*) : FlexibleRule (Option α × Option β) where
  null := (none, none)
  binds := twoPad
  symmetric := twoPad_symmetric
  inert := twoPad_null

instance {α β : Type*} [DecidableEq α] [DecidableEq β] :
    DecidableRel (twoPadFlexibleRule α β).binds :=
  inferInstanceAs (DecidableRel (@twoPad α β))

end LinearAssemblies
