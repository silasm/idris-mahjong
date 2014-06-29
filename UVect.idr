module UVect

-- declaring totality causes an error with `noEmptyElem` and
-- `neitherHereNorThere` where they pattern match on Here. To make matters more
-- confusing, this isn't caught by --total --warnpartial, but /is/ caught by
-- %default total or requiring the individual functions be total

-- %default total

-- implementation of unique vectors; i.e. vectors such that each element
-- in the vector is unique up to propositional equality.

mutual
  -- Constructions are augmented with proof that x is not already in xs
  data UVect : Nat -> Type -> Type where
    Nil  : UVect Z a
    (::) : (x : a) -> (xs : UVect n a) -> Not (Elem x xs) -> UVect (S n) a

  -- requires an additional implicit showing that the `y :: xs' proof
  -- was valid to begin with
  data Elem : a -> UVect n a -> Type where
    Here  : {x : a} -> {xs : UVect n a} -> {p : Not (Elem x xs)} ->
            Elem x ((x :: xs) p)
    There : {x,y : a} -> {xs : UVect n a} -> {p : Not (Elem y xs)} ->
            Elem x xs -> Elem x ((y :: xs) p)
-- end mutual

-- Copied from upstream Data.Vect
-- Nothing can be in an empty UVect
noEmptyElem : {x : a} -> UVect.Elem x [] -> _|_
noEmptyElem Here impossible
noEmptyElem (There _) impossible

-- Copied from upstream Data.Vect
-- An item not in the head and not in the tail is not in the UVect at all
neitherHereNorThere : {x, y : a} -> {xs : UVect n a} ->
                      {auto p : Not (Elem y xs)} -> Not (x = y) ->
                      Not (Elem x xs) -> Not (Elem x ((y :: xs) p))
neitherHereNorThere xneqy xninxs Here = xneqy refl
neitherHereNorThere xneqy xninxs (There xinxs) = xninxs xinxs

-- Whether or not x is an element of UVect xs is decidable if equality of x is
-- decidable
decElem : (DecEq a) => (x : a) -> (xs : UVect n a) -> Dec (Elem x xs)
decElem x [] = No noEmptyElem
decElem x ((y :: xs) p) with (decEq x y)
  decElem x ((x :: xs) p) | (Yes refl) = Yes Here
  decElem x ((y :: xs) p) | (No   neq) with (decElem x xs)
    | (No nel)  = No (neitherHereNorThere neq nel)
    | (Yes el) = Yes (There el)


-- Constructs x onto xs iff xs does not already contain x
using (a : Type, n : Nat)
  maybeGrow : (DecEq a) => (x : a) -> (xs : UVect n a) ->
              Either (UVect n a) (UVect (S n) a)
  maybeGrow x xs with (decElem x xs)
    | (No nel) = Right ((x :: xs) nel)
    | (Yes el) = Left  xs
