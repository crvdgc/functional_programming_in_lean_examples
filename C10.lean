import mathlib

def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1

def Tail.length : List α → Nat :=
  let rec go acc
    | [] => acc
    | _ :: xs => go (acc + 1) xs
  go 0

def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

def Tail.factorial : Nat → Nat :=
  let rec go acc
    | 0 => acc
    | n + 1 => go (acc * (n + 1)) n
  go 1

#eval Tail.factorial 5

def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs

def Tail.filter (p : α → Bool) : List α → List α :=
  let rec go acc
    | [] => acc
    | x :: xs =>
      if p x then
        go (x :: acc) xs
      else
        go acc xs
   go []

#eval [1, 2, 3].filter  (· > 1)

def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverse : List α → List α :=
  let rec go acc
    | [] => acc
    | x :: xs => go (x :: acc) xs
  go []

theorem non_tail_reverse_go_acc (xs : List α) : (acc : List α) →
  Tail.reverse.go acc xs = NonTail.reverse xs ++ acc := by
  induction xs <;> simp [NonTail.reverse, Tail.reverse, Tail.reverse.go]
  case cons x xs ih =>
    intro acc
    rw [ih (x :: acc)]
    simp [List.append_assoc]

theorem non_tail_reverse_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
  funext α xs
  cases xs <;> simp [NonTail.reverse, Tail.reverse, Tail.reverse.go]
  case cons => simp [non_tail_reverse_go_acc]

theorem non_tail_factorial_go_acc (x : Nat) : (acc : Nat) →
  Tail.factorial.go acc x = NonTail.factorial x * acc := by
  induction x <;> simp [NonTail.factorial, Tail.factorial, Tail.factorial.go]
  case succ x ih =>
    intro acc
    rw [ih]
    simp [←Nat.mul_assoc, Nat.mul_comm]

theorem non_tail_factorial_eq_tail_factorial : NonTail.factorial = Tail.factorial := by
  funext x
  cases x <;> simp [NonTail.factorial, Tail.factorial]
  case succ x =>
    rw [non_tail_factorial_go_acc]
    simp [Nat.add_succ, NonTail.factorial]

def Array.forM_helper [Monad m] (i : Nat) (arr : Array α) (f : α → m PUnit) : m PUnit :=
  if inBounds : i < arr.size then do
    f arr[i]
    forM_helper (i + 1) arr f
  else
    pure ()
termination_by Array.forM_helper i arr _ => arr.size - i

def Array.forM' [Monad m] : Array α → (α → m PUnit) → m PUnit :=
  Array.forM_helper 0

instance : ForM m (Array α) α where
  forM := Array.forM'

def Array.map' (f : α → β) (arr : Array α) : Array β := Id.run do
  let mut acc := Array.empty
  for x in arr do
    acc := acc.push (f x)
  return acc

def Array.find' (arr : Array α) (p : α → Bool) : Option (Nat × α) := Id.run do
  for x in arr, i in [0:arr.size] do
    if p x then
      return .some (i, x)
  return .none

#eval #[1, 2, 3].find' (· > 1)

def Array.reverse' (arr : Array α) : Array α := Id.run do
  let mut res := Array.empty
  for h : i in [:arr.size] do
    have : arr.size - (i + 1) < arr.size := by
       apply Nat.sub_lt_of_pos_le (i + 1) arr.size (Nat.succ_pos i)
       exact (Membership.mem.upper h)
    res := res.push arr[arr.size - i - 1]
  return res

#eval #[1, 2, 3].reverse'

theorem Nat.zero_lt_succ' : (n : Nat) → 0 < n + 1 := Nat.zero_lt_succ

theorem Nat.zero_le' : (n : Nat) → 0 <= n := Nat.zero_le

theorem Nat.succ_sub_succ' : (n k : Nat) → (n + 1) - (k + 1) = n - k := Nat.succ_sub_succ

theorem Nat.not_eq_zero_of_lt' (n k : Nat) : k < n → n ≠ 0 := Nat.not_eq_zero_of_lt

theorem Nat.sub_self' : (n : Nat) → n - n = 0 := Nat.sub_self

theorem Nat.lt_of_succ_lt' : (n k : Nat) → n + 1 < k → n < k := by
  intros n k h
  rw [Nat.add_one] at h
  exact Nat.lt_of_succ_lt h

