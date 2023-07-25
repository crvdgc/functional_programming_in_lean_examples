def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1

theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption

theorem plusR_succ_left (m n : Nat) : Nat.plusR (m + 1) n = Nat.plusR m n + 1 := by
  induction n with
  | zero => simp [Nat.plusR]
  | succ m ihm => simp [Nat.plusR]; assumption

theorem plusR_succ_left' (m n : Nat) : Nat.plusR (m + 1) n = Nat.plusR m n + 1 := by
  induction n <;> simp [Nat.plusR] <;> assumption

theorem List.append_assoc' (xs ys zs : List α) : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by
  induction xs <;> simp [List.append] <;> assumption

 
 
