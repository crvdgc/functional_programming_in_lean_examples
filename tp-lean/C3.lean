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

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro
    | .inl hp => exact ⟨.inl hp, .inl hp⟩
    | .inr ⟨hq, hr⟩ => exact ⟨.inr hq, .inr hr⟩
  · intro
    | ⟨.inl hp, _⟩ | ⟨_, .inl hp⟩ => exact .inl hp
    | ⟨.inr hq, .inr hr⟩ => exact .inr ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  · intro h ⟨p, q⟩
    exact h p q
  · intro h p q
    exact h ⟨p, q⟩

theorem or_implies : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro p
      exact h (.inl p)
    · intro q
      exact h (.inr q)
  · intro ⟨hp, hq⟩
    intro
    | .inl p => exact hp p
    | .inr q => exact hq q

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := or_implies p q r

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_implies p q False

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro
  | .inl hnp => intro ⟨hp, _⟩; contradiction
  | .inr hnq => intro ⟨_, hq⟩; contradiction

example : ¬(p ∧ ¬p) := by intro ⟨hp, hnp⟩; contradiction

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩ hpq
  have : q := hpq hp
  contradiction

example : ¬p → (p → q) := by
  intro hnp hp
  have : False := hnp hp
  exact False.elim this

example : (¬p ∨ q) → (p → q) := by
  intro
  | .inl hnp =>
    intro hp
    exact False.elim (hnp hp)
  | .inr hq =>
    intro
    exact hq

example : p ∨ False ↔ p := by
  apply Iff.intro
  · intro
    | .inl hp => exact hp
    | .inr hcontra => exact False.elim hcontra
  · intro
    apply Or.inl
    assumption

example : p ∧ False ↔ False := by
  apply Iff.intro
  · intro ⟨_, hcontra⟩; exact hcontra
  · intro hcontra; exact False.elim hcontra

example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  apply hnq
  exact (hpq hp)
