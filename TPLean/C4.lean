import TPLean.C3

section
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4
end

section exercise_1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro x; exact (h x).left
    · intro x; exact (h x).right
  · intro ⟨hp, hq⟩
    intro x
    exact ⟨hp x, hq x⟩
      
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h hp x
  exact (h x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro
  | .inl hp, x => exact .inl (hp x)
  | .inr hq, x => exact .inr (hq x)

end exercise_1

section exercise_2

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := by
  intro x
  apply Iff.intro
  · intro h; exact (h x)
  · intro hr _; exact hr

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  · intro h
    match Classical.em r with
    | .inl hr => exact .inr hr
    | .inr hnr =>
      apply Or.inl
      intro x
      match h x with
      | .inl hp => exact hp
      | .inr hr => contradiction
  · intro
    | .inl hp => intro x; exact .inl (hp x)
    | .inr hr => intro x; exact .inr hr
    
    
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  · intro h hr x
    exact h x hr
  · intro h x hr
    exact h hr x

end exercise_2

section exercise_3

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have := h barber
  exact (not_iff_neg _ this)

end exercise_3

