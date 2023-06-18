structure Pos where
  succ ::
  pred : Nat

instance : ToString Pos where
  toString a := toString (a.pred + 1)

#eval toString (Pos.succ 0)
#eval toString (Pos.succ 1)

instance : Add Pos where
  add a b := Pos.succ (a.pred + b.pred + 1)

#eval (Pos.succ 0 + Pos.succ 1)

instance : Mul Pos where
  mul a b := Pos.succ (a.pred * b.pred + a.pred + b.pred)

#eval (Pos.succ 0 * Pos.succ 20)
#eval (Pos.succ 2 * Pos.succ 4)

instance : OfNat Pos (Nat.succ n) where
  ofNat := Pos.succ n

#eval (2 : Pos)

structure Even where
  double ::
  half : Nat

instance : ToString Even where
  toString x := toString (2 * x.half)

#eval (Even.double 0)
#eval (Even.double 1)

instance : Add Even where
  add a b := Even.double (a.half + b.half)

#eval (Even.double 2 + Even.double 3)

instance : Mul Even where
  mul a b := Even.double (2 * a.half * b.half)

#eval (Even.double 1 * Even.double 2)
#eval (Even.double 0 * Even.double 2)

instance : OfNat Even Nat.zero where
  ofNat := Even.double 0

instance [OfNat Even n] : OfNat Even (Nat.succ (Nat.succ n)) where
  ofNat := Even.double (Nat.succ (OfNat.ofNat n : Even).half)

#eval (0 : Even)
#eval (2 : Even)
-- #eval (100 : Even)
-- #eval (254 : Even)

#check HAdd.hAdd 5

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

#eval PPoint.mk 1.0 2

instance [HMul α α α]: HMul (PPoint α) α (PPoint α) where
  hMul p c := { x := p.x * c, y := p.y * c }

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr, BEq

def NonEmptyList.ofList {α : Type}
  | [] => none
  | x :: xs => some ({ head := x, tail := xs } : NonEmptyList α)

#eval NonEmptyList.ofList [1, 2, 3]

def NonEmptyList.toList {α : Type} (ne : NonEmptyList α) := ne.head :: ne.tail

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ne :=
    match xs with
    | [] => ne
    | x :: xs => { head := x, tail := xs ++ NonEmptyList.toList ne }

#eval [1,2,3] ++ NonEmptyList.mk 4 [5, 6]
#eval ([] : List Nat) ++ NonEmptyList.mk 4 [5, 6]
#eval [1,2,3] ++ NonEmptyList.mk 4 []

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.map (f : α → β)
    | BinTree.leaf => BinTree.leaf
    | BinTree.branch left x right =>
      BinTree.branch (BinTree.map f left) (f x) (BinTree.map f right)

instance : Functor BinTree where
  map := BinTree.map
