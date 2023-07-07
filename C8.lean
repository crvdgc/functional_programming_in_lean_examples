inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
  deriving Repr

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

def oregonianPeaks : Vect String 3 :=
  .cons "Mount Hood" <|
  .cons  "Mount Jefferson" <|
  .cons  "South Sister" .nil

def danishPeaks : Vect String 3 :=
  .cons "Møllehøj" <|
  .cons "Yding Skovhøj" <|
  .cons "Ejer Bavnehøj" .nil

#eval Vect.zip oregonianPeaks danishPeaks

def Vect.map (f : α → β) : Vect α n → Vect β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (map f xs)

def Vect.zipWith (f : α → β → γ) : Vect α n → Vect β n → Vect γ n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (f x y) (zipWith f xs ys)

def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
    let (xs, ys) := unzip xys
    (.cons x xs, .cons y ys)

def Vect.snoc : Vect α n → α → Vect α (n + 1)
  | .nil, v => .cons v .nil
  | .cons x xs, v => .cons x (snoc xs v)

#eval Vect.snoc (.cons "snowy" .nil) "peaks"

def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => snoc (reverse xs) x

#eval Vect.reverse oregonianPeaks

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, xs => xs
  | n + 1, .cons _ xs => drop n xs

#eval danishPeaks.drop 2

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, _ => .nil
  | n + 1, .cons x xs => .cons x (take n xs)

#eval danishPeaks.take 2
