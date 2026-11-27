import LinearAssemblies.Forest.Functional

set_option autoImplicit false

namespace LinearAssemblies.Forest

variable {S : Type}

/-- `false` is termination and `true` is the alarm. -/
abbrev Target (S : Type) := S ⊕ Bool

def forget (f : S → Target S) (i : S) : Option S :=
  match f i with | .inl j => some j | .inr _ => none

inductive Leads (f : S → Target S) (b : Bool) : S → Prop
  | root {i : S} : f i = .inr b → Leads f b i
  | next {i j : S} : f i = .inl j → Leads f b j → Leads f b i

theorem Leads.has_root {f : S → Target S} {b : Bool} {i : S} (h : Leads f b i) :
    ∃ j, f j = .inr b := by
  induction h with
  | @root i hi => exact ⟨i, hi⟩
  | next _ _ ih => exact ih

theorem leads_terminates {f : S → Target S} {b : Bool} {i : S} (h : Leads f b i) :
    Terminates (forget f) i := by
  induction h with
  | root hi => exact terminates_of_none (by simp [forget, hi])
  | next hi _ ih => exact (terminates_next (by simp [forget, hi])).mpr ih

theorem leads_of_terminates {f : S → Target S} {i : S} (h : Terminates (forget f) i) :
    Leads f false i ∨ Leads f true i := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing i with
  | zero => simp at hk
  | succ k ih =>
    cases hi : f i with
    | inl j =>
      have hj : (step (forget f))^[k] (some j) = none := by
        simpa [Function.iterate_succ_apply, step, forget, hi] using hk
      exact (ih hj).imp (Leads.next hi) (Leads.next hi)
    | inr b =>
      cases b with
      | false => exact Or.inl (Leads.root hi)
      | true => exact Or.inr (Leads.root hi)

theorem leads_unique {f : S → Target S} {b c : Bool} {i : S}
    (hb : Leads f b i) (hc : Leads f c i) : b = c := by
  induction hb with
  | root hi =>
    cases hc with
    | root hi' => exact Sum.inr.inj (hi.symm.trans hi')
    | next hi' _ => simp [hi] at hi'
  | next hi hj ih =>
    cases hc with
    | root hi' => simp [hi] at hi'
    | next hi' hj' =>
      have he := Sum.inl.inj (hi.symm.trans hi')
      subst he
      exact ih hj'

/-- Redirect all termination edges to s; alarm edges remain absorbing. -/
def redirect (f : S → Target S) (s i : S) : Option S :=
  match f i with
  | .inl j => some j
  | .inr false => some s
  | .inr true => none

theorem terminates_forget_of_redirect {f : S → Target S} {s i : S}
    (h : Terminates (redirect f s) i) : Terminates (forget f) i := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing i with
  | zero => simp at hk
  | succ k ih =>
    cases hi : f i with
    | inl j =>
      have hj : (step (redirect f s))^[k] (some j) = none := by
        simpa [Function.iterate_succ_apply, step, redirect, hi] using hk
      exact (terminates_next (by simp [forget, hi])).mpr (ih hj)
    | inr b => exact terminates_of_none (by simp [forget, hi])

theorem alarm_terminates_redirect {f : S → Target S} {s i : S} (h : Leads f true i) :
    Terminates (redirect f s) i := by
  induction h with
  | root hi => exact terminates_of_none (by simp [redirect, hi])
  | next hi _ ih => exact (terminates_next (by simp [redirect, hi])).mpr ih

theorem termination_redirect {f : S → Target S} {s i : S} (h : Leads f false i)
    (hs : Terminates (redirect f s) s) : Terminates (redirect f s) i := by
  induction h with
  | root hi => exact (terminates_next (by simp [redirect, hi])).mpr hs
  | next hi _ ih => exact (terminates_next (by simp [redirect, hi])).mpr ih

theorem rooted_redirect_iff [DecidableEq S] (f : S → Target S) (s : S) :
    Rooted (redirect f s) ↔ Rooted (forget f) ∧ Leads f true s := by
  constructor
  · intro hr
    have hf : Rooted (forget f) := fun i => terminates_forget_of_redirect (hr i)
    refine ⟨hf, ?_⟩
    rcases leads_of_terminates (hf s) with hs | hs
    · have hlt : ∀ {i}, Leads f false i → distance (redirect f s) hr s < distance (redirect f s) hr i := by
        intro i hi
        induction hi with
        | root hi => exact distance_drop hr (by simp [redirect, hi])
        | next hi _ ih => exact lt_trans ih (distance_drop hr (by simp [redirect, hi]))
      exact False.elim (lt_irrefl _ (hlt hs))
    · exact hs
  · rintro ⟨hf, hs⟩ i
    have hss : Terminates (redirect f s) s := alarm_terminates_redirect hs
    rcases leads_of_terminates (hf i) with hi | hi
    · exact termination_redirect hi hss
    · exact alarm_terminates_redirect hi

end LinearAssemblies.Forest
