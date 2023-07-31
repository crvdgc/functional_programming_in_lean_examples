variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  case mp =>
    intro h
    exact ⟨h.right, h.left⟩
  case mpr =>
    intro h
    exact ⟨h.right, h.left⟩

example : p ∨ q ↔ q ∨ p := by
  constructor
  case mp =>
    intro h
    cases h
    case inl h =>
      exact Or.inr h
    case inr h =>
      exact Or.inl h
  case mpr =>
    intro h
    cases h
    case inl h =>
      exact Or.inr h
    case inr h =>
      exact Or.inl h

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, hq, hr⟩
  · intro ⟨hp, hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  · intro
    | .inl (.inl hp) => exact .inl hp
    | .inl (.inr hq) => exact .inr (.inl hq)
    | .inr hr  => exact .inr (.inr hr)
  · intro
    | .inl hp => exact .inl (.inl hp)
    | .inr (.inl hq) =>  exact .inl (.inr hq)
    | .inr (.inr hr) => exact .inr hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro
    | ⟨hp, .inl hq⟩ =>
      apply Or.inl
      exact ⟨hp, hq⟩
    | ⟨hp, .inr hr⟩ =>
      apply Or.inr
      exact ⟨hp, hr⟩
  · intro
    | .inl ⟨hp, hq⟩ => exact ⟨hp, .inl hq⟩
    | .inr ⟨hp, hr⟩ => exact ⟨hp, .inr hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
