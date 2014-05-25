module Inspect

data Inspect : a -> Type where
  wi : {A : Type} -> (x : A) -> (y : A) -> (x = y) -> Inspect x
  
inspect : {A : Type} -> (x : A) -> Inspect x
inspect x = wi x _ refl

example : (l : List Bool) -> if (length l == Z) then (S (length l) = 1) else ((S (length l) > 1) = True)
example l with (inspect (length l))
  | (wi (length l) y prf) with (y)
    | Z = ?cz
    | (S n) = ?cs