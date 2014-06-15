-- a simplified `reverse` function, to make it easier to prove that
-- reverse (reverse v) = v

%default total
%hide Prelude.Vect.reverse

snoc : {n : Nat} -> {a : Type} -> (x : a) -> Vect n a -> Vect (S n) a
snoc x [] = [x]
snoc x (y :: xs) = (y :: snoc x xs)

reverse : {n : Nat} -> Vect n a -> Vect n a
reverse [] = []
reverse (x :: xs) = (snoc x (reverse xs))

reverse_snoc : {a : Type} -> {n : Nat} -> (x : a) -> (v : Vect n a) -> reverse (snoc x v) = x :: reverse v
reverse_snoc x [] = refl
reverse_snoc x (y :: xs) = rewrite (reverse_snoc x xs) in refl

double_reverse : (v : Vect n a) -> reverse (reverse v) = v
double_reverse [] = refl
double_reverse (x :: xs) = rewrite (reverse_snoc x (reverse xs)) in
  rewrite (double_reverse xs) in refl
