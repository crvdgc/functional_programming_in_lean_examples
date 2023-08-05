example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (apply And.intro) <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

