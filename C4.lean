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
