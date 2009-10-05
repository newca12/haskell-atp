
* Signature

> module ATP.Poly
>   ( Poly
>   , add
>   , sub
>   , neg
>   , mul
>   , div
>   , pow
>   , var
>   , cmul
>   , atom
>   , coefficients
>   , degree
>   , polynate
>   , phead
>   , headconst
>   , behead
>   , isConstant
>   )
> where

* Imports

> import Prelude hiding (div)
> import qualified ATP.Util.Lib as Lib
> import ATP.FormulaSyn
> import qualified ATP.Order as Order
> import qualified ATP.Cooper as Cooper
> import ATP.Cooper(zero, one)

* Polynomials

> type Poly = Term

* Arithmetic

> add :: Vars -> Poly -> Poly -> Poly
> add vars pol1 pol2 = 
>   case (pol1, pol2) of 
>     (Fn "+" [c, Fn "*" [Var x, p]], Fn "+" [d, Fn "*" [Var y, q]]) -> 
>       if Order.earlier vars x y then polyLadd vars pol2 pol1
>       else if Order.earlier vars y x then polyLadd vars pol1 pol2
>       else let e = add vars c d
>                r = add vars p q in
>            if r == zero then e else Fn "+" [e, Fn "*" [Var x, r]]
>     (_, Fn "+" _) -> polyLadd vars pol1 pol2
>     (Fn "+" _, _) -> polyLadd vars pol2 pol1
>     _ -> Cooper.numeral2 (+) pol1 pol2

> polyLadd :: Vars -> Poly -> Poly -> Poly
> polyLadd vars pol1 (Fn "+" [d, Fn "*" [Var y, q]]) =
>   Fn "+" [add vars pol1 d, Fn "*" [Var y, q]]
> polyLadd _ _ _ = error "Impossible"

> neg :: Poly -> Poly
> neg (Fn "+" [c, Fn "*" [Var x, p]]) =
>   Fn "+" [neg c, Fn "*" [Var x, neg p]]
> neg n = Cooper.numeral1 (\x -> - x) n

> sub :: Vars -> Poly -> Poly -> Poly
> sub vars p q = add vars p (neg q)

> mul :: Vars -> Poly -> Poly -> Poly
> mul vars pol1 pol2 = 
>   case (pol1, pol2) of 
>     (Fn "+" [_, Fn "*" [Var x, _]], Fn "+" [_, Fn "*" [Var y, _]]) -> 
>       if Order.earlier vars x y then polyLmul vars pol2 pol1
>       else polyLmul vars pol1 pol2
>     (Fn "0" [], _) -> zero
>     (_, Fn "+" _) -> polyLmul vars pol1 pol2
>     (Fn "+" _, _) -> polyLmul vars pol2 pol1
>     _ -> Cooper.numeral2 (*) pol1 pol2

> polyLmul :: Vars -> Poly -> Poly -> Poly
> polyLmul vars pol1 (Fn "+" [d, Fn "*" [Var y, q]]) =
>   Fn "+" [add vars (mul vars pol1 d) (Fn "+" [zero, Fn "*" [Var y, mul vars pol1 q]])]
> polyLmul _ _ _ = error "Impossible"

> pow :: Vars -> Poly -> Int -> Poly
> pow vars p n = Lib.funpow n (mul vars p) one

> div :: Vars -> Poly -> Poly -> Poly
> div vars p q = mul vars p (Cooper.numeral1 (/ (1::Rational)) q)

> var :: Var -> Poly
> var x = Fn "+" [zero, Fn "*" [Var x, one]]

> polynate :: Vars -> Poly -> Poly
> polynate vars tm = case tm of
>   Var x -> var x
>   Fn "-" [t] -> neg (polynate vars t)
>   Fn "+" [s, t] -> add vars (polynate vars s) (polynate vars t)
>   Fn "-" [s, t] -> sub vars (polynate vars s) (polynate vars t)
>   Fn "*" [s, t] -> mul vars (polynate vars s) (polynate vars t)
>   Fn "/" [s, t] -> div vars (polynate vars s) (polynate vars t)
>   Fn "^" [p, Fn n []] -> pow vars (polynate vars p) (read n)
>   _ -> if Cooper.isNumeral tm then tm else error "lint: unknown term"

> atom :: Vars -> Formula -> Formula
> atom vars (Atom (R a [s, t])) = Atom(R a [polynate vars (Fn "-" [s, t]), zero])
> atom _ _ = error "polyatom: not an atom"

XXX, Is the lack of an "otherwise" clause OK below?

> coefficients :: Vars -> Poly -> [Poly]
> coefficients vars fm = case fm of
>   Fn "+" [c, Fn "*" [Var x, q]] | x == head vars -> c:coefficients vars q
>   _ -> [fm]

> degree :: Vars -> Poly -> Int
> degree vars p = length(coefficients vars p) - 1

> isConstant :: Vars -> Poly -> Bool
> isConstant vars p = degree vars p == 0

> phead :: Vars -> Poly -> Poly
> phead vars p = last(coefficients vars p)

> behead :: Vars -> Poly -> Poly
> behead vars t = case t of
>   Fn "+" [c, Fn "*" [Var x, p]] | x == head vars -> 
>     let p' = behead vars p in
>     if p' == zero then c else c + Var x * p'
>   _ -> zero

> cmul :: Rational -> Poly -> Poly
> cmul k p = case p of
>   Fn "+" [c, Fn "*" [Var x, q]] -> cmul k c + Var x * cmul k q
>   _ -> Cooper.numeral1 (k *) p

> headconst :: Poly -> Rational
> headconst p = case p of
>   Fn "+" [_, Fn "*" [Var _, q]] -> headconst q
>   Fn _ [] -> Cooper.destNumeral p
>   _ -> error "Impossible"

