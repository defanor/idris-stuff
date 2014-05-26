module Inspect

data Inspect : a -> Type where
  wi : {A : Type} -> (x : A) -> (y : A) -> (eq: x = y) -> Inspect x
  
inspect : {A : Type} -> (x : A) -> Inspect x
inspect x = wi x _ refl

match : {A : Type} -> {x : A} -> (y : A) -> {eq : x = y} -> Inspect x
match y {eq} = wi _ y eq

total example : (l : List Bool) -> if (length l == Z) then (S (length l) = (S Z)) else ((S (length l) > (S Z)) = True)
example l with (inspect (length l))
  | match Z {eq=eq} = (rewrite eq in ?refl_here)
  | match (S n) = ?cs
