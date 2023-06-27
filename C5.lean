inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op
deriving Repr

inductive Arith where
  | plus
  | minus
  | times
  | div
deriving Repr

open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))

-- #eval fourteenDivided

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int): Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2

def evaluateM' [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 => do
    let v1 ← evaluateM applySpecial e1
    let v2 ← evaluateM applySpecial e2
    applyPrim applySpecial p v1 v2

def evaluateM'' [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 => do
    applyPrim applySpecial p (← evaluateM applySpecial e1) (← evaluateM applySpecial e2)

def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.cons (x : α) (xs : Many α) : Many α :=
  Many.more x (fun () => xs)

def Many.one (x : α) : Many α := Many.cons x Many.none

def Many.union : Many α → Many α → Many α
  | none, ys => ys
  | more x xs, ys => Many.cons x (Many.union (xs ()) ys)

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.cons x (Many.fromList xs)

def Many.toList : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).toList

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
 | none, _ => Many.none
 | more x xs, f => (f x).union (bind (xs ()) f)

instance : Monad Many where
 pure := Many.one
 bind := Many.bind

theorem many_union_none_eq : Many.union x Many.none = x := by
  induction x with
  | none => rfl
  | more x xs ih =>
    unfold Many.union
    unfold Many.cons
    simp
    rw [ih]

theorem many_none_union_eq : Many.union Many.none x = x := by
  unfold Many.union
  rfl

theorem many_bind_none_eq_none : Many.bind Many.none f = Many.none := by
  unfold Many.bind
  rfl

theorem many_monad_identity_left : Many.bind (Many.one v) f = f v := by
  unfold Many.one
  unfold Many.bind
  unfold Many.cons
  simp
  unfold Many.bind
  rw [many_union_none_eq]

theorem many_moand_identity_right : Many.bind x Many.one = x := by
  induction x with
  | none => rw [many_bind_none_eq_none]
  | more x xs ih =>
    unfold Many.bind
    unfold Many.union
    unfold Many.one
    unfold Many.cons
    simp
    rw [many_none_union_eq]
    unfold Many.one at ih
    unfold Many.cons at ih
    rw [ih]

theorem many_bind_more : Many.bind (Many.more x xs) f = (f x).union (Many.bind (xs ()) f) := by
  rfl

theorem many_union_more : Many.union (Many.more x xs) ys = Many.more x (fun () => Many.union (xs ()) ys) := by
  rfl

#eval (Many.bind (Many.union (Many.one 1) (Many.fromList [1, 2, 3])) Many.one).toList
#eval let f := Many.one; (Many.union (Many.bind (Many.one 1) f) (Many.bind (Many.fromList [1, 2, 3]) f)).toList

theorem many_union_assoc : Many.union (Many.union xs ys) zs = Many.union xs (Many.union ys zs) := by
  induction xs with
  | none => rfl
  | more x xs ih =>
    repeat rw [many_union_more]
    rw [ih]

theorem many_bind_union_distr : Many.bind (Many.union xs ys) f = Many.union (Many.bind xs f) (Many.bind ys f) := by
  induction xs with
  | none => rfl
  | more x xs ih =>
    rw [many_bind_more]
    rw [many_union_more]
    rw [many_bind_more]
    rw [ih]
    rw [many_union_assoc]

theorem many_monad_assoc : Many.bind (Many.bind v f) g = Many.bind v (fun x => Many.bind (f x) g) := by
  induction v with
  | none =>
    repeat rw [many_bind_none_eq_none]
  | more x xs ih =>
    repeat rw [many_bind_more]
    rw [many_bind_union_distr]
    rw [ih]

def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env

theorem reader_monad_identity_left : Reader.bind (Reader.pure v) f = f v := by rfl

theorem reader_monad_identity_right : Reader.bind mv Reader.pure = mv := by rfl

theorem reader_monad_assoc :
  Reader.bind (Reader.bind mv f) g =
  Reader.bind mv (fun v => Reader.bind (f v) g) := by rfl

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}

inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α


def applyTraced : ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int :=
  λ (ToTrace.trace prim) x y =>
  let evalEmpty : Prim Empty → Int → Int → Int
    | Prim.plus, x, y => x + y
    | Prim.minus, x, y => x - y
    | Prim.times, x, y => x * y
  { log := [(prim, x, y)], val :=  evalEmpty prim x y }


deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim

open Expr Prim ToTrace in
#eval evaluateM applyTraced (prim (other (trace times)) (prim (other (trace plus)) (const 1) (const 2)) (prim (other (trace minus)) (const 3) (const 4)))

