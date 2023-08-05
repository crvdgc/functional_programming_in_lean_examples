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

section exercise_4

def even (n : Nat) : Prop := ∃ k, n = 2 * k

example : even 2 := by
  simp [even]
  exists 1

def prime (n : Nat) : Prop := ∀ m : Nat, m < n → n % m = 0 → m = 1

def infinitely_many_primes : Prop := ∀ m, prime m → ∃ n, n > m ∧ prime n

def Fermat_prime (n : Nat) : Prop := prime (2 ^ (2 ^ n) + 1)

def infinitely_many_Fermat_primes : Prop := ∀ m, Fermat_prime m → ∃ n, n > m ∧ Fermat_prime n

def goldbach_conjecture : Prop := ∀ a, a > 2 ∧ even a → ∃ b c, prime b ∧ prime c ∧ a = b + c

def odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

example : odd 3 := by
  simp [even]
  exists 1

def Goldbach's_weak_conjecture : Prop :=
  ∀ x, x > 7 ∧ odd x →
  ∃ a b c, odd a ∧ prime a ∧ odd b ∧ prime b ∧ odd c ∧ prime c ∧
  x = a + b + c

def Fermat's_last_theorem : Prop :=
  ∀ n, n > 2 →
  ¬∃ (a b c : Nat), a ^ n = b ^ n + c ^ n

end exercise_4

section exercise_5

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r := by
  intro ⟨_, hr⟩
  exact hr

example (a : α) : r → (∃ _x : α, r) := by
  intro hr
  exact ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  · intro ⟨x, hp, hr⟩
    exact ⟨⟨x, hp⟩, hr⟩
  · intro ⟨⟨x, hp⟩, hr⟩
    exact ⟨x, hp, hr⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  · intro
    | ⟨x, .inl hp⟩ => exact .inl ⟨x, hp⟩
    | ⟨x, .inr hq⟩ => exact .inr ⟨x, hq⟩
  · intro
    | .inl ⟨x, hp⟩ => exact ⟨x, .inl hp⟩
    | .inr ⟨x, hq⟩ => exact ⟨x, .inr hq⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  · intro hp ⟨x, hnp⟩
    exact hnp (hp x)
  · intro hnnp x
    apply Classical.byContradiction
    intro hnp
    apply False.elim
    apply hnnp
    exact ⟨x, hnp⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  · intro ⟨x, hp⟩ hnp
    have : ¬ p x := hnp x
    contradiction
  · intro h
    apply Classical.byContradiction
    intro hnp
    apply h
    intro x hp
    apply hnp
    exact ⟨x, hp⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  · intro hnp x hp
    apply hnp
    exact ⟨x, hp⟩
  · intro hnp ⟨x, hp⟩
    exact hnp x hp

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  · intro hp
    apply Classical.byContradiction
    intro hnnp
    apply hp
    intro x
    apply Classical.byContradiction
    intro hnp
    apply hnnp
    exact ⟨x, hnp⟩
  · intro ⟨x, hnp⟩ hp
    exact hnp (hp x)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  · intro hpr ⟨x, hp⟩
    exact hpr x hp
  · intro hpr x hp
    apply hpr
    exact ⟨x, hp⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  · intro ⟨x, hpr⟩ hp
    apply hpr
    exact (hp x)
  · intro hpr
    apply Classical.byCases (p := ∀ x, p x)
    · intro hp
      exists a
      intro _
      apply hpr
      exact hp
    · intro hnp
      apply Classical.byContradiction
      intro hnpr
      apply hnp
      intro x
      apply Classical.byContradiction
      intro hnpx
      apply hnpr
      exists x
      intro hpx
      contradiction

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  · intro ⟨x, hrp⟩ hr
    exists x
    exact hrp hr
  · intro hrp
    apply Classical.byCases (p := r)
    · intro hr
      have ⟨x, hp⟩ := hrp hr
      exists x
      intro _
      exact hp
    · intro hnr
      exists a
      intro hr
      contradiction

end exercise_5
