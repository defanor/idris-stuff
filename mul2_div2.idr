-- division by 2 and multiplication by 2

%default total


div2 : Nat -> Nat
div2 Z = 0
div2 (S Z) = 0
div2 (S (S k)) = div2' (S k)
  where -- a hack for totality checker
    div2' : Nat -> Nat
    div2' Z = 0
    div2' (S n) = S (div2 n)

div2_zero : (k : Nat) -> (lte k (S Z) = True) -> div2 k = Z
div2_zero Z prf = refl
div2_zero (S Z) prf = refl
div2_zero (S (S k)) prf = (FalseElim (trueNotFalse (sym prf)))

mul2 : Nat -> Nat
mul2 Z = 0
mul2 (S k) = (S (S (mul2 k)))

mul2_n_zero : (n : Nat) -> (mul2 n = Z) -> n = Z
mul2_n_zero Z prf = refl
mul2_n_zero (S k) prf = FalseElim $ OnotS (sym prf)

mul2_zero_n : (n : Nat) -> n = Z -> mul2 n = Z
mul2_zero_n n prf = rewrite prf in refl

mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k

even_inv : (n : Nat) -> (even (S n) = not (even n))
even_inv Z = refl
even_inv (S Z) = refl
even_inv (S (S k)) = (even_inv k)

mul2_even : (n : Nat) -> even (mul2 n) = True
mul2_even Z = refl
mul2_even (S k) = (mul2_even k)

mul2_not_odd : (n : Nat) -> odd (mul2 n) = False
mul2_not_odd Z = refl
mul2_not_odd (S k) = (mul2_not_odd k)

div2_mul2_n_eq_n : (n : Nat) -> div2 (mul2 n) = n
div2_mul2_n_eq_n Z = refl
div2_mul2_n_eq_n (S k) = cong {f=S} $ div2_mul2_n_eq_n k

div2_S_mul2_n_eq_n : (n : Nat) -> div2 (S (mul2 n)) = n
div2_S_mul2_n_eq_n Z = refl
div2_S_mul2_n_eq_n (S k) = cong {f=S} $ div2_S_mul2_n_eq_n k

mul2_div2_even : (n : Nat) -> (even n = True) -> mul2 (div2 n) = n
mul2_div2_even Z prf = refl
mul2_div2_even (S Z) prf = (FalseElim (trueNotFalse (sym prf)))
mul2_div2_even (S (S k)) prf = cong {f=S} $ cong {f=S} (mul2_div2_even k prf)

mul2_div2_eq : (n, m : Nat) -> (even m = True) -> (n = div2 m) -> mul2 n = m
mul2_div2_eq n m evp eqp = rewrite eqp in (mul2_div2_even m evp)

div2_S_even : (n : Nat) -> (even n = True) -> div2 (S n) = div2 n
div2_S_even Z prf = refl
div2_S_even (S Z) prf = (FalseElim (trueNotFalse (sym prf)))
div2_S_even (S (S k)) prf = cong {f=S} (div2_S_even k prf)
