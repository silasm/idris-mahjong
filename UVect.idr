module UVect

mutual
  data UVect : Nat -> Type -> Type where
    UNil  : {a : Type} -> UVect Z a
    UCons : {a : Type} -> (xin : a) -> (xsin : UVect n a) ->
            NotElem xin xsin -> UVect (S n) a

  data NotElem : a -> UVect n a -> Type where
    NotInEmpty : {x : a} -> NotElem x UNil
    NotInUCons : {x,y : a} -> {xs : UVect n a} -> {auto p : NotElem y xs} ->
                 NotElem x xs -> (x = y -> _|_) -> NotElem x (UCons y xs p)

-- end mutual
data Elem  : a -> UVect n a -> Type where
  Here  : {x : a} -> {xs : UVect n a} -> {p : NotElem x xs} ->
          Elem x (UCons x xs p)
  There : {x,y : a} -> {xs : UVect n a} -> {p : NotElem y xs} ->
          Elem x xs -> Elem x (UCons y xs p)

elemImpliesNotNotElem : {a : Type} -> {x : a} -> {n : Nat} -> {xs : UVect n a} ->
                        Elem x xs -> Not (NotElem x xs)
elemImpliesNotNotElem Here = 

-- Homogeneous equality
Eq : a -> a -> Type
Eq x y = x = y

using (a : Type, n : Nat)
  notElem   : (DecEq a) => (x : a) -> (xs : UVect n a) -> Dec (NotElem x xs)
  notElem x UNil = Yes NotInEmpty
  notElem x (UCons y ys _) with (decEq x y)
    notElem x (UCons x ys _) | (Yes refl) = No ?rhs
    notElem x (UCons y ys p) | (No  neq) with (notElem x ys)
      | (Yes q) = NotInUCons q neq
      | (No cont) = cont
{--
  maybeGrow : (DecEq a)  =>
              (x : a) -> (xs : UVect n a) -> { p : Dec (NotElem x xs) } ->
              Maybe (l ** l `Eq` UCons {n=n} {a=a} x xs _)
  maybeGrow x UNil {p=p} = Just (UCons x UNil p ** refl)
  maybeGrow x (UCons y xs q) {p=p} with (decEq x y)
    maybeGrow x (UCons x xs q) | (Yes refl) impossible
    maybeGrow x (UCons y xs q) | (No  cont) = Just 

total
uvectInjective1 : {a : Type} -> {x, y : a} -> {xs, ys : UVect n a} ->
                  UCons x xs p = UCons y ys q -> x = y
uvectInjective1 {x=x} {y=x} {xs=xs} {ys=xs} refl = refl

instance DecEq a => DecEq (UVect n a) where
  decEq UNil UNil = Yes refl
  decEq (UCons x xs p) (UCons y ys q) with (decEq x y, decEq xs ys)
    decEq (UCons x xs p) (UCons x ys q)   | Yes refl with (decEq xs ys)
      decEq (UCons x xs p) (UCons x xs q) | Yes refl | Yes refl = Yes refl
      decEq (UCons x xs p) (UCons x ys q) | Yes refl | No  neq  = No (neq . uvectInjective2)
    decEq (UCons x xs p) (UCons y ys q)   | No  neq             = No (neq . uvectInjective1)
    | (_) = No ?prfNo
--}
