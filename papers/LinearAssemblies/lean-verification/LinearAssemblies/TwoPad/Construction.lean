import LinearAssemblies.DigitData
import LinearAssemblies.Presentation

set_option autoImplicit false

namespace LinearAssemblies.TwoPad

variable {b : ℕ} (d : DigitData b)

abbrev State := Fin d.first ⊕ (Fin (d.count + 1) ⊕ Fin (b - 2))
abbrev Entry := Fin d.first ⊕ (Fin d.count ⊕ (Fin d.count ⊕ (Fin (b - 2) ⊕ Fin (b - 2))))
abbrev FirstLabel := (Fin d.first ⊕ Unit) ⊕ Fin (b - 2)
abbrev SecondLabel := Fin (d.count + 1) ⊕ Fin (b - 2)
abbrev Interface := Option (FirstLabel d) × Option (SecondLabel d)

def input : State d := .inl ⟨0, d.first_pos⟩
def terminal : State d := .inr (.inl (Fin.last d.count))

def expose : State d → Interface d
  | .inl j => (some (.inl (.inl j)), none)
  | .inr (.inl i) =>
      (if i.val < d.count then some (.inl (.inr ())) else none, some (.inl i))
  | .inr (.inr j) => (some (.inr j), none)

def decode : Interface d → State d
  | (some (.inl (.inl j)), _) => .inl j
  | (some (.inr j), _) => .inr (.inr j)
  | (_, some (.inl i)) => .inr (.inl i)
  | _ => input d

theorem decode_expose (x : State d) : decode d (expose d x) = x := by
  rcases x with j | (i | j)
  · rfl
  · by_cases hi : i.val < d.count <;> simp [expose, decode, hi]
  · rfl

def pathNext (j : Fin d.first) : State d :=
  if hj : j.val + 1 < d.first then .inl ⟨j.val + 1, hj⟩ else .inr (.inl 0)

def afterFirst : State d := pathNext d ⟨0, d.first_pos⟩

def resetTarget (i : Fin d.count) : State d :=
  if h1 : d.digit i = 1 then afterFirst d
  else if h2 : d.digit i = 2 then input d
  else .inr (.inr ⟨d.digit i - 3, by have h := d.digit_bounds i i.isLt; omega⟩)

def delayNext (j : Fin (b - 2)) : State d :=
  if hj : j.val = 0 then input d
  else .inr (.inr ⟨j.val - 1, by omega⟩)

def west : Entry d → Interface d
  | .inl j => expose d (.inl j)
  | .inr (.inl i) => (none, some (.inl i.castSucc))
  | .inr (.inr (.inl i)) => (none, some (.inl i.castSucc))
  | .inr (.inr (.inr (.inl j))) => (some (.inl (.inr ())), some (.inr j))
  | .inr (.inr (.inr (.inr j))) => expose d (.inr (.inr j))

def target : Entry d → State d
  | .inl j => pathNext d j
  | .inr (.inl i) => .inr (.inl i.succ)
  | .inr (.inr (.inl i)) => resetTarget d i
  | .inr (.inr (.inr (.inl _))) => afterFirst d
  | .inr (.inr (.inr (.inr j))) => delayNext d j

def presentation : Presentation (Interface d) where
  State := State d
  Entry := Entry d
  finiteState := inferInstance
  finiteEntry := inferInstance
  expose := expose d
  decode := decode d
  decode_expose := decode_expose d
  input := input d
  west := west d
  target := target d

/-- Each shared reset entry is charged once, irrespective of how many interfaces use it. -/
theorem tile_cost : (presentation d).system.cost = d.first + 2 * d.count + 2 * (b - 2) + 1 := by
  simp [Presentation.system, System.cost, presentation, Entry, Fintype.card_sum]
  ring

/-- The exact compatible-entry row at a path, unfinished digit, terminal, or delay state. -/
theorem row_sum (f : State d → ℝ) (x : State d) :
    (∑ e ∈ (presentation d).choices twoPad x, f (target d e)) =
      match x with
      | .inl j => f (pathNext d j)
      | .inr (.inl i) =>
          if hi : i.val < d.count then
            f (.inr (.inl (⟨i.val, hi⟩ : Fin d.count).succ)) +
            f (resetTarget d ⟨i.val, hi⟩) + (b - 2 : ℕ) * f (afterFirst d)
          else 0
      | .inr (.inr j) => f (delayNext d j) := by
  classical
  simp only [Presentation.choices, Finset.sum_filter, presentation, Fintype.sum_sum_type]
  rcases x with j | (i | j)
  · simp [west, expose, twoPad, onePad, target]
  · induction i using Fin.lastCases with
    | last =>
      have hn : ∀ i : Fin d.count, d.count ≠ i.val := fun i => by omega
      simp [west, expose, twoPad, onePad, target, Fin.ext_iff, hn]
    | cast i => simp [west, expose, twoPad, onePad, target, i.isLt, add_assoc]
  · simp [west, expose, twoPad, onePad, target]

end LinearAssemblies.TwoPad
