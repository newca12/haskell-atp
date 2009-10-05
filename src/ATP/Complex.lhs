
> module Complex
>   where

> import Prelude 
> import qualified Lib
> import qualified List()
> import qualified Char()
> import qualified ListSet()
> import qualified Formulas as F
> import Formulas(Var, Vars, Formula(..))
> import qualified Fol
> import Fol(Term(..), Fol(..))
> import qualified Order
> import qualified Cooper
> import Cooper(zero, one)

> polyAdd :: Vars -> Term -> Term -> Term
> polyAdd vars pol1 pol2 = 
>   case (pol1, pol2) of 
>     (Fn "+" [c, Fn "*" [Var x, p]], Fn "+" [d, Fn "*" [Var y, q]]) -> 
>       if Order.earlier vars x y then polyLadd vars pol2 pol1
>       else if Order.earlier vars y x then polyLadd vars pol1 pol2
>       else let e = polyAdd vars c d
>                r = polyAdd vars p q in
>            if r == zero then e else Fn "+" [e, Fn "*" [Var x, r]]
>     (_, Fn "+" _) -> polyLadd vars pol1 pol2
>     (Fn "+" _, _) -> polyLadd vars pol2 pol1
>     _ -> Cooper.numeral2 (+) pol1 pol2

> polyLadd :: Vars -> Term -> Term -> Term
> polyLadd vars pol1 (Fn "+" [d, Fn "*" [Var y, q]]) =
>   Fn "+" [polyAdd vars pol1 d, Fn "*" [Var y, q]]
> polyLadd _ _ _ = error "Impossible"

> polyNeg :: Term -> Term
> polyNeg (Fn "+" [c, Fn "*" [Var x, p]]) =
>   Fn "+" [polyNeg c, Fn "*" [Var x, polyNeg p]]
> polyNeg n = Cooper.numeral1 (\x -> - x) n

> polySub :: Vars -> Term -> Term -> Term
> polySub vars p q = polyAdd vars p (polyNeg q)

> polyMul :: Vars -> Term -> Term -> Term
> polyMul vars pol1 pol2 = 
>   case (pol1, pol2) of 
>     (Fn "+" [_, Fn "*" [Var x, _]], Fn "+" [_, Fn "*" [Var y, _]]) -> 
>       if Order.earlier vars x y then polyLmul vars pol2 pol1
>       else polyLmul vars pol1 pol2
>     (Fn "0" [], _) -> zero
>     (_, Fn "+" _) -> polyLmul vars pol1 pol2
>     (Fn "+" _, _) -> polyLmul vars pol2 pol1
>     _ -> Cooper.numeral2 (*) pol1 pol2

> polyLmul :: Vars -> Term -> Term -> Term
> polyLmul vars pol1 (Fn "+" [d, Fn "*" [Var y, q]]) =
>   Fn "+" [polyAdd vars (polyMul vars pol1 d) (Fn "+" [zero, Fn "*" [Var y, polyMul vars pol1 q]])]
> polyLmul _ _ _ = error "Impossible"

> polyPow :: Vars -> Term -> Int -> Term
> polyPow vars p n = Lib.funpow n (polyMul vars p) one

> polyDiv :: Vars -> Term -> Term -> Term
> polyDiv vars p q = polyMul vars p (Cooper.numeral1 (/ (1::Rational)) q)

> polyVar :: Var -> Term
> polyVar x = Fn "+" [zero, Fn "*" [Var x, one]]

> polynate :: Vars -> Term -> Term
> polynate vars tm = case tm of
>   Var x -> polyVar x
>   Fn "-" [t] -> polyNeg (polynate vars t)
>   Fn "+" [s, t] -> polyAdd vars (polynate vars s) (polynate vars t)
>   Fn "-" [s, t] -> polySub vars (polynate vars s) (polynate vars t)
>   Fn "*" [s, t] -> polyMul vars (polynate vars s) (polynate vars t)
>   Fn "/" [s, t] -> polyDiv vars (polynate vars s) (polynate vars t)
>   Fn "^" [p, Fn n []] -> polyPow vars (polynate vars p) (read n)
>   _ -> if Cooper.isNumeral tm then tm else error "lint: unknown term"

> polyAtom :: Vars -> Formula Fol -> Formula Fol
> polyAtom vars (Atom (R a [s, t])) = Atom(R a [polynate vars (Fn "-" [s, t]), zero])
> polyAtom _ _ = error "polyatom: not an atom"

XXX, Is the lack of an "otherwise" clause OK below?

> coefficients :: Vars -> Term -> [Term]
> coefficients vars fm = case fm of
>   Fn "+" [c, Fn "*" [Var x, q]] | x == head vars -> c:coefficients vars q
>   _ -> [fm]

> degree :: Vars -> Term -> Int
> degree vars p = length(coefficients vars p) - 1

> isConstant :: Vars -> Term -> Bool
> isConstant vars p = degree vars p == 0

> phead :: Vars -> Term -> Term
> phead vars p = last(coefficients vars p)

> behead :: Vars -> Term -> Term
> behead vars t = case t of
>   Fn "+" [c, Fn "*" [Var x, p]] | x == head vars -> 
>     let p' = behead vars p in
>     if p' == zero then c else c + Var x * p'
>   _ -> zero

> polyCmul :: Rational -> Term -> Term
> polyCmul k p = case p of
>   Fn "+" [c, Fn "*" [Var x, q]] -> polyCmul k c + Var x * polyCmul k q
>   _ -> Cooper.numeral1 (k *) p

> headconst :: Term -> Rational
> headconst p = case p of
>   Fn "+" [_, Fn "*" [Var _, q]] -> headconst q
>   Fn _ [] -> Cooper.destNumeral p
>   _ -> error "Impossible"

