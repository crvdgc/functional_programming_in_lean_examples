structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

def volume : RectangularPrism → Float :=
  fun x => x.height * x.width * x.depth

structure Segment where
  p1 : Float
  p2 : Float

-- def length (s : Segment) : Float :=
--   Float.abs (s.p1 - s.p2)

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

def head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y

-- #eval [].head? (α := Nat)

-- #check ("hello", 5)

def fives : String × Int := ("five", 5)

def PetName : Type := String ⊕ String

def last {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [x] => some x
  | _ :: xs => last xs
  
example : last [1, 2, 3] = some 3 := rfl

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | x :: xs => if predicate x then some x else List.findFirst? xs predicate

def even (x : Nat) : Bool :=
  match x with
  | 0 => true
  | (Nat.succ x) => not (even x)

example : List.findFirst? [1, 2, 3] even = some 2 := rfl

def Prod.swap {α β : Type} (p : α × β) : β × α :=
  (p.snd, p.fst)

def distr_prod_sum (x : α × (β ⊕ γ)) : α × β ⊕ α × γ :=
  match x.snd with
  | Sum.inl beta =>  Sum.inl (x.fst,beta) 
  | Sum.inr gamma => Sum.inr (x.fst, gamma)

def sum_of_2_mul : Bool × α → α ⊕ α :=
  fun
  | (false, x) => Sum.inl x
  | (true, x) => Sum.inr x

def mk_pair : α → β → α × β := (· , ·)
