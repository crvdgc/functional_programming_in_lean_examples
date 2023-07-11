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

inductive Finite where
  | empty : Finite
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite
  | option : Finite → Finite

abbrev Finite.asType : Finite → Type
  | .empty => Empty
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr t1 t2 => asType t1 → asType t2
  | .option t => Option t.asType

def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse

mutual
  def Finite.functions (t : Finite) (results : List α) : List (t.asType → α) :=
    match t with
      | .empty => []
      | .unit =>
        results.map fun r =>
          fun () => r
      | .bool =>
        (results.product results).map fun (r1, r2) =>
          fun
            | true => r1
            | false => r2
      | .pair t1 t2 =>
        let f1s := t1.functions <| t2.functions results
        f1s.map fun f =>
          fun (x, y) =>
            f x y
      | .arr t1 t2 =>
        let args := t1.enumerate
        let base :=
          results.map fun r =>
            fun _ => r
        args.foldr
          (fun arg rest =>
            (t2.functions rest).map fun more =>
              fun f => more (f arg) f)
          base
      | .option t =>
        let fs := t.functions results
        (results.product fs).map fun (r, f) =>
          fun
            | .none => r
            | .some v => f v
  
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
    | .empty => []
    | .unit => [()]
    | .bool => [true, false]
    | .pair t1 t2 => t1.enumerate.product t2.enumerate
    | .arr t1 t2 => t1.functions t2.enumerate
    | .option t => .none :: t.enumerate.map .some
end

def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .empty => true
  | .unit => true
  | .bool => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr t1 t2 =>
    t1.enumerate.all fun arg => beq t2 (x arg) (y arg)
  | .option t =>
    match x, y with
    | .none, .none => true
    | .some x, .some y => beq t x y
    | _, _ => false

def Finite.to_string (t : Finite) (x : t.asType) : String :=
  match t with
  | .empty => "impossible"
  | .unit => "()"
  | .bool => if x then "true" else "false"
  | .pair t1 t2 =>
    let (x1, x2) := x
    let s1 := t1.to_string x1
    let s2 := t2.to_string x2
    s!"({s1}, {s2})"
  | .arr t1 t2 =>
    let rows :=
      let args := t1.enumerate
      let values := args.map x
      List.zipWith (s!"{·} ↦ {·}") (args.map t1.to_string) (values.map t2.to_string)
    String.intercalate "\n" rows
  | .option t =>
    match x with
    | .none => "none"
    | .some v => s!"some {t.to_string v}"

#eval Finite.to_string .unit ()
#eval IO.println (Finite.to_string (.arr .bool .bool) not)

def Finite.print_all (code : Finite) : IO Unit :=
  for f in Finite.enumerate code do
    IO.println "---"
    IO.println (Finite.to_string code f)

#eval Finite.print_all (.arr .bool .bool)

#eval Finite.print_all (.arr (.option .bool) .bool)

