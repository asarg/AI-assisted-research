import LinearAssemblies.Concatenation.Distribution

set_option autoImplicit false

namespace LinearAssemblies.Concatenation

def tagLeft {A B : Type} : Option A → Option (A ⊕ B) := Option.map Sum.inl
def tagRight {A B : Type} : Option B → Option (A ⊕ B) := Option.map Sum.inr

theorem tagLeft_injective {A B : Type} : Function.Injective (@tagLeft A B) := by
  intro x y h
  cases x <;> cases y <;> simp_all [tagLeft]

theorem tagRight_injective {A B : Type} : Function.Injective (@tagRight A B) := by
  intro x y h
  cases x <;> cases y <;> simp_all [tagRight]

theorem tagLeft_rule {A B : Type} (x y : Option A) :
    onePad (@tagLeft A B x) (tagLeft y) ↔ onePad x y := by
  cases x <;> cases y <;> simp [tagLeft, onePad]

theorem tagRight_rule {A B : Type} (x y : Option B) :
    onePad (@tagRight A B x) (tagRight y) ↔ onePad x y := by
  cases x <;> cases y <;> simp [tagRight, onePad]

theorem tag_cross {A B : Type} (x : Option A) (y : Option B) :
    ¬ onePad (tagLeft x) (tagRight y) := by
  cases x <;> cases y <;> simp [tagLeft, tagRight, onePad]

theorem tag_eq_iff {A B : Type} (x : Option A) (y : Option B) :
    tagLeft x = tagRight y ↔ x = none ∧ y = none := by
  cases x <;> cases y <;> simp [tagLeft, tagRight]

def onePadSeparation {A B : Type} (p : Presentation (Option A)) (q : Presentation (Option B))
    (hp : ∀ x, p.expose x ≠ none) :
    SeparatedInterfaces p q onePad onePad (@onePad (A ⊕ B)) where
  left := tagLeft
  right := tagRight
  left_injective := tagLeft_injective
  right_injective := tagRight_injective
  left_rule := tagLeft_rule
  right_rule := tagRight_rule
  cross_left := tag_cross
  cross_right x y h := tag_cross y x (onePad_symmetric h)
  exposed_disjoint x _ h := hp x ((tag_eq_iff _ _).1 h).1

def pairLeft {A B C D : Type} (x : Option A × Option B) : Option (A ⊕ C) × Option (B ⊕ D) :=
  (tagLeft x.1, tagLeft x.2)

def pairRight {A B C D : Type} (y : Option C × Option D) : Option (A ⊕ C) × Option (B ⊕ D) :=
  (tagRight y.1, tagRight y.2)

def twoPadSeparation {A B C D : Type}
    (p : Presentation (Option A × Option B)) (q : Presentation (Option C × Option D))
    (hp : ∀ x, p.expose x ≠ (none, none)) :
    SeparatedInterfaces p q twoPad twoPad (@twoPad (A ⊕ C) (B ⊕ D)) where
  left := pairLeft
  right := pairRight
  left_injective := by
    intro x y h
    exact Prod.ext (tagLeft_injective (congrArg Prod.fst h))
      (tagLeft_injective (congrArg Prod.snd h))
  right_injective := by
    intro x y h
    exact Prod.ext (tagRight_injective (congrArg Prod.fst h))
      (tagRight_injective (congrArg Prod.snd h))
  left_rule := by intro x y; simp [twoPad, pairLeft, tagLeft_rule]
  right_rule := by intro x y; simp [twoPad, pairRight, tagRight_rule]
  cross_left := by intro x y; simp [twoPad, pairLeft, pairRight, tag_cross]
  cross_right := by
    intro x y h
    have hh := twoPad_symmetric h
    simp [twoPad, pairLeft, pairRight, tag_cross] at hh
  exposed_disjoint := by
    intro x y h
    apply hp x
    exact Prod.ext ((tag_eq_iff _ _).1 (congrArg Prod.fst h)).1
      ((tag_eq_iff _ _).1 (congrArg Prod.snd h)).1

theorem onePad_expose_nonnull {A B : Type} (p : Presentation (Option A))
    (q : Presentation (Option B)) (hp : ∀ x, p.expose x ≠ none)
    (hq : ∀ x, q.expose x ≠ none) (exit : p.State)
    (x : State p q exit) :
    (presentation p q (onePadSeparation p q hp) exit).expose x ≠ none := by
  rcases x with x | y
  · have h := hp x.val
    cases he : p.expose x.val <;> simp_all [presentation, expose, onePadSeparation, tagLeft]
  · have h := hq y
    cases he : q.expose y <;> simp_all [presentation, expose, onePadSeparation, tagRight]

theorem twoPad_expose_nonnull {A B C D : Type}
    (p : Presentation (Option A × Option B)) (q : Presentation (Option C × Option D))
    (hp : ∀ x, p.expose x ≠ (none, none)) (hq : ∀ x, q.expose x ≠ (none, none))
    (exit : p.State) (x : State p q exit) :
    (presentation p q (twoPadSeparation p q hp) exit).expose x ≠ (none, none) := by
  rcases x with x | y
  · intro h
    apply hp x.val
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change tagLeft (p.expose x.val).1 = none at h1
    change tagLeft (p.expose x.val).2 = none at h2
    simp only [tagLeft, Option.map_eq_none_iff] at h1 h2
    exact Prod.ext h1 h2
  · intro h
    apply hq y
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change tagRight (q.expose y).1 = none at h1
    change tagRight (q.expose y).2 = none at h2
    simp only [tagRight, Option.map_eq_none_iff] at h1 h2
    exact Prod.ext h1 h2

end LinearAssemblies.Concatenation
