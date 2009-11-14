
* Signature

> module ATP.Poly
>   ( isRational
>   , rational1
>   , rational2
>   , destRational
>   , Poly
>   , zero
>   , one
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
>   , monic
>   , pdivide
>   , diff
>   )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude hiding (div)
> import qualified ATP.Cooper as Cooper
> import ATP.FormulaSyn
> import qualified ATP.Order as Order
> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.Print as PP
> import qualified Data.List as List
> import qualified Ratio

* Rationals

> isRational :: Term -> Bool
> isRational (Num _) = True
> isRational _ = False

> destRational :: Term -> Rational
> destRational (Num r) = r
> destRational _ = __IMPOSSIBLE__ 

> rational1 :: (Rational -> Rational) -> Term -> Term
> rational1 fn = Num . fn . destRational

> rational2 :: (Rational -> Rational -> Rational) -> Term -> Term -> Term
> rational2 fn m n = Num $ fn (destRational m) (destRational n)

* Polynomials

> type Poly = Term

* Arithmetic

Note that in Harrison's code he uses the OCaml Num module.  Num.num is an
odd type, since it combines integers and rationals.  Operations like
lcm applied to ratios raise exceptions.  Not very pretty...
We need explicit casts between Integer and Rational.

> zero :: Term
> zero = Num 0

> one :: Term
> one = Num 1

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
>     _ -> rational2 (+) pol1 pol2

> polyLadd :: Vars -> Poly -> Poly -> Poly
> polyLadd vars pol1 (Fn "+" [d, Fn "*" [Var y, q]]) =
>   Fn "+" [add vars pol1 d, Fn "*" [Var y, q]]
> polyLadd _ _ _ = __IMPOSSIBLE__ 

> neg :: Poly -> Poly
> neg (Fn "+" [c, Fn "*" [Var x, p]]) = 
>   Fn "+" [neg c, Fn "*" [Var x, neg p]]
> neg n = rational1 (\x -> - x) n

> sub :: Vars -> Poly -> Poly -> Poly
> sub vars p q = add vars p (neg q)

> mul :: Vars -> Poly -> Poly -> Poly
> mul vars pol1 pol2 = 
>   case (pol1, pol2) of 
>     (Num 0, _) -> zero
>     (_, Num 0) -> zero
>     (Fn "+" [_, Fn "*" [Var x, _]], Fn "+" [_, Fn "*" [Var y, _]]) -> 
>       if Order.earlier vars x y then polyLmul vars pol2 pol1
>       else polyLmul vars pol1 pol2
>     (_, Fn "+" _) -> polyLmul vars pol1 pol2
>     (Fn "+" _, _) -> polyLmul vars pol2 pol1
>     _ -> rational2 (*) pol1 pol2

> polyLmul :: Vars -> Poly -> Poly -> Poly
> polyLmul vars pol1 (Fn "+" [d, Fn "*" [Var y, q]]) =
>   add vars (mul vars pol1 d) (Fn "+" [zero, Fn "*" [Var y, mul vars pol1 q]])
> polyLmul _ _ t = error' $ PP.text "polyLmul:" <+> PP.vcat [ PP.pPrint t 
>                                                           , PP.text $ show t ]

> pow :: Vars -> Poly -> Int -> Poly
> pow vars p n = Lib.funpow n (mul vars p) one

Divide by a constant.

> div :: Vars -> Poly -> Poly -> Poly
> div vars p q = mul vars p (rational1 ((1::Rational) /) q)

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
>   Fn "^" [p, Num n] -> 
>     if Ratio.denominator n == 1 then pow vars (polynate vars p) (fromIntegral $ Ratio.numerator n)
>     else error $ "not an integer power: " ++ show n
>   _ -> if Cooper.isInteger tm then tm else error "lint: unknown term"

> atom :: Vars -> Formula -> Formula
> atom vars (Atom (R a [s, t])) = Atom(R a [polynate vars (Fn "-" [s, t]), zero])
> atom _ a = error' $ PP.text "polyatom: not an atom" <+> PP.pPrint a

let x = atom ["w", "x", "y", "z"] [$form| ((w + x)^4 + (w + y)^4 + (w + z)^4 + (x + y)^4 + (x + z)^4 + (y + z)^4 + (w - x)^4 + (w - y)^4 + (w - z)^4 + (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 = (w^2 + x^2 + y^2 + z^2)^2 |]
PP.pPrint x

> coefficients :: Vars -> Poly -> [Poly]
> coefficients vars fm = case fm of
>   Fn "+" [c, Fn "*" [Var x, q]] 
>    | x == head vars -> c : coefficients vars q
>   _ -> [fm]

> degree :: Vars -> Poly -> Int
> degree vars p = length (coefficients vars p) - 1

> isConstant :: Vars -> Poly -> Bool
> isConstant vars p = degree vars p == 0

> phead :: Vars -> Poly -> Poly
> phead vars p = last $ coefficients vars p

> behead :: Vars -> Poly -> Poly
> behead vars t = case t of
>   Fn "+" [c, Fn "*" [Var x, p]] | x == head vars -> 
>     let p' = behead vars p in
>     if p' == zero then c else c + Var x * p'
>   _ -> zero

> cmul :: Rational -> Poly -> Poly
> cmul k p = case p of
>   Fn "+" [c, Fn "*" [Var x, q]] -> cmul k c + Var x * cmul k q
>   _ -> rational1 (k *) p

> headconst :: Poly -> Rational
> headconst p = case p of
>   Fn "+" [_, Fn "*" [Var _, q]] -> headconst q
>   Num r -> r
>   _ -> __IMPOSSIBLE__ 

> monic :: Term -> (Term, Bool)
> monic p = 
>   let h = headconst p 
>       res = if h == 0 then (p, False) else (cmul (1 / h) p, h < 0)
>   in res
>      -- trace' "monic" (PP.pPrint (p, res)) $ res

Pseudo-division

> pdivide :: Vars -> Poly -> Poly -> (Int, Poly)
> pdivide vars s1 p1 = divAux (phead vars p1) (degree vars p1) p1 0 s1
>  where 
>   shift1 x p = Fn "+" [zero, Fn "*" [Var x, p]]
>   divAux a n p k s = 
>     if s == zero then (k, s) else
>     let b = phead vars s
>         m = degree vars s 
>     in if m < n then (k, s) else
>     let p' = Lib.funpow (m - n) (shift1 $ head vars) p in
>     if a == b then divAux a n p k (sub vars s p')
>     else divAux a n p (k + 1) (sub vars (mul vars a s) (mul vars b p'))

Differentiation

> diffn :: Term -> Integer -> Term -> Term
> diffn x n p = 
>   let n' :: Rational = fromInteger n in
>   case p of 
>     Fn "+" [c, Fn "*" [y, q]] 
>      | y == x -> Fn "+" [cmul n' c, Fn "*" [x, diffn x (n+1) q]]
>      | otherwise -> cmul n' p
>     _ -> cmul n' p

> diff, diff' :: Vars -> Term -> Term
> diff = tracef2 "diff" diff'
> diff' vars p = case p of
>   Fn "+" [_c, Fn "*" [Var x, q]] 
>    | x == head vars -> diffn (Var x) 1 q
>    | otherwise -> zero
>   _ -> zero
