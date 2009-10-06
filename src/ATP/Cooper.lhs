
* Signature

> module ATP.Cooper
>   ( zero
>   , one
>   , isNumeral
>   , numeral1
>   , numeral2
>   , destNumeral
>   , integerQelim
>   , naturalQelim
>   )
> where

* Imports

> import Prelude 
> import qualified Data.Char as Char
> import qualified Data.List as List
> import qualified Ratio
> import Ratio ((%))

> import ATP.Util.Parse (parse)
> import qualified ATP.Util.ListSet as Set
> import ATP.FormulaSyn
> import qualified ATP.Formula as F
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Qelim as Qelim
> import qualified ATP.Order as Order

* Cooper

> zero :: Term
> zero = fromInteger 0

> one :: Term
> one = fromInteger 1

> termInteger :: Integer -> Term
> termInteger n = Fn (show n) []

> rati :: Rational -> Integer
> rati x = if Ratio.denominator x == 1 
>          then toInteger (Ratio.numerator x)
>       else error ("not integral: " ++ show x)

> irat :: Integer -> Rational
> irat x = x % 1

> destNumeral :: Term -> Rational
> destNumeral (Fn ns []) = parse ns
> destNumeral t = error ("destNumeral: " ++ show t)

> isNumeral :: Term -> Bool
> isNumeral (Fn ns []) | head ns == '-' = List.all Char.isDigit (tail ns)
>                      | otherwise = List.all Char.isDigit ns
> isNumeral _ = False

> numeral1 :: (Rational -> Rational) -> Term -> Term
> numeral1 fn = flip Fn [] . show . fn . destNumeral

> numeral2 :: (Rational -> Rational -> Rational) -> Term -> Term -> Term
> numeral2 fn m n = Fn (show $ fn (destNumeral m) (destNumeral n)) []

> linearCmul :: Rational -> Term -> Term
> linearCmul n tm = if n == 0 then zero else 
>                   case tm of 
>                     Fn "+" [Fn "*" [c, x], r] -> 
>                       numeral1 ((*) n) c * x + linearCmul n r
>                     k -> numeral1 ((*) n) k

> linearAdd :: Vars -> Term -> Term -> Term
> linearAdd vars tm1 tm2 =
>   case (tm1, tm2) of 
>     (Fn "+" [Fn "*" [c1, Var x1], r1], 
>      Fn "+" [Fn "*" [c2, Var x2], r2]) ->
>        if x1 == x2 then
>          let c = numeral2 (+) c1 c2 in
>          if c == zero then linearAdd vars r1 r2
>          else c * Var x1 + linearAdd vars r1 r2
>        else if Order.earlier vars x1 x2 then
>          c1 * Var x1 + linearAdd vars r1 tm2
>        else
>          c2 * Var x2 + linearAdd vars tm1 r2
>     (Fn "+" [Fn "*" [c1, Var x1], r1], k2) ->
>       c1 * Var x1 + linearAdd vars r1 k2
>     (k1, Fn "+" [Fn "*" [c2, Var x2], r2]) ->
>        c2 * Var x2 + linearAdd vars k1 r2
>     _ -> numeral2 (+) tm1 tm2

> linearNeg :: Term -> Term
> linearNeg = linearCmul (-1)

> linearSub :: Vars -> Term -> Term -> Term
> linearSub vars tm1 tm2 = linearAdd vars tm1 (linearNeg tm2)

> linearMul :: Term -> Term -> Term
> linearMul tm1 tm2 = 
>   if isNumeral tm1 then linearCmul (destNumeral tm1) tm2
>   else if isNumeral tm2 then linearCmul (destNumeral tm2) tm1
>   else error ("linearMul: nonlinearity: (" ++ show tm1 ++ ", " ++ show tm2 ++ ")")

> lint :: Vars -> Term -> Term
> lint vars tm =
>   case tm of
>    Var(_) -> one * tm + zero
>    Fn "-" [t] -> linearNeg (lint vars t)
>    Fn "+" [s, t] -> linearAdd vars (lint vars s) (lint vars t)
>    Fn "-" [s, t] -> linearSub vars (lint vars s) (lint vars t)
>    Fn "*" [s, t] -> linearMul (lint vars s) (lint vars t)
>    _ -> if isNumeral tm then tm else error "lint: unknown term"

> mkatom :: Vars -> Pred -> Term -> Formula 
> mkatom vars p t = Atom (R p [zero, lint vars t])

> linform :: Vars -> Formula -> Formula 
> linform vars fm =
>  case fm of
>    Atom(R "divides" [c, t]) ->
>      Atom(R "divides" [numeral1 abs c, lint vars t])
>    Atom(R "=" [s, t]) -> mkatom vars "=" (t - s)
>    Atom(R "<" [s, t]) -> mkatom vars "<" (t - s)
>    Atom(R ">" [s, t]) -> mkatom vars "<" (s - t)
>    Atom(R "<=" [s, t]) -> mkatom vars "<" (t + one - s)
>    Atom(R ">=" [s, t]) -> mkatom vars "<" (s + one - t)
>    _ -> fm 

> posineq :: Formula -> Formula 
> posineq fm =
>   case fm of
>     Not(Atom(R "<" [Fn "0" [], t])) ->
>       Atom(R "<" [zero, linearSub [] one t])
>     _ -> fm
    
> formlcm :: Term -> Formula -> Integer
> formlcm x (Atom(R _ [_, Fn "+" [Fn "*" [c, y], _]])) | y == x =
>   abs $ rati $ destNumeral c
> formlcm x (Not(p)) = formlcm x p
> formlcm x (And p q) = lcm (formlcm x p) (formlcm x q)
> formlcm x (Or p q) = lcm (formlcm x p) (formlcm x q)   
> formlcm _ _ = 1

> adjustcoeff :: Term -> Integer -> Formula -> Formula 
> adjustcoeff x l fm = 
>  case fm of
>    Atom(R p [d, Fn "+" [Fn "*" [c, y], z]]) | y == x ->
>      let m = l `div` (rati $ destNumeral c)
>          n = if p == "<" then abs m else m
>          xtm = fromInteger (m `div` n) * x in
>      Atom(R p [linearCmul (toRational $ abs m) d, xtm + linearCmul (irat n) z])
>    Not p -> Not(adjustcoeff x l p)
>    And p q -> adjustcoeff x l p ∧ adjustcoeff x l q
>    Or p q -> adjustcoeff x l p ∨ adjustcoeff x l q
>    _ -> fm

> unitycoeff :: Term -> Formula -> Formula 
> unitycoeff x fm = 
>   let l = formlcm x fm
>       fm' = adjustcoeff x l fm in
>   if l == 1 then fm' else
>   let xp = one * x + zero in
>   Atom (R "divides" [fromInteger l, xp]) ∧ adjustcoeff x l fm

> minusinf :: Term -> Formula -> Formula 
> minusinf x fm =
>  case fm of
>    Atom(R "=" [Fn "0" [], Fn "+" [Fn "*" [Fn "1" [], y], _]]) | y == x -> Bot
>    Atom(R "<" [Fn "0" [], Fn "+" [Fn "*" [pm1, y], _]]) | y == x -> 
>      if pm1 == one then Bot else Top
>    Not(p) -> Not(minusinf x p)
>    And p q -> minusinf x p ∧ minusinf x q
>    Or p q -> minusinf x p ∨ minusinf x q
>    _ -> fm

> divlcm :: Term -> Formula -> Integer
> divlcm x fm =
>  case fm of
>    Atom(R "divides" [d, Fn "+" [Fn "*" [_, y], _]]) | y == x ->
>      rati $ destNumeral d
>    Not p -> divlcm x p
>    And p q -> lcm (divlcm x p) (divlcm x q)
>    Or p q -> lcm (divlcm x p) (divlcm x q)
>    _ -> 1

> bset :: Term -> Formula -> [Term]
> bset x fm =
>   case fm of 
>     Not(Atom (R "=" [Fn "0" [], Fn "+" [Fn "*" [Fn "1" [], y], a]])) | y == x -> 
>       [linearNeg a]
>     Atom(R "=" [Fn "0" [], Fn "+" [Fn "*"[Fn "1" [], y], a]]) | y == x ->
>       [linearNeg(linearAdd [] a one)]
>     Atom(R "<" [Fn "0" [], Fn "+" [Fn "*" [Fn "1" [], y], a]]) | y == x -> 
>       [linearNeg a]
>     Not p -> bset x p
>     And p q -> Set.union (bset x p) (bset x q)
>     Or p q -> Set.union (bset x p) (bset x q)
>     _ -> []

> linrep :: Vars -> Term -> Term -> Formula -> Formula 
> linrep vars x t fm =
>  case fm of
>    Atom(R p [d, Fn "+" [Fn "*" [c,y],a]]) | y == x ->
>      let ct = linearCmul (destNumeral c) t in
>        Atom(R p [d, linearAdd vars ct a])
>    Not p -> Not(linrep vars x t p)
>    And p q -> linrep vars x t p ∧ linrep vars x t q
>    Or p q -> linrep vars x t p ∨ linrep vars x t q
>    _ -> fm

> cooper :: Vars -> Formula -> Formula 
> cooper vars (Ex x0 p0) =
>   let x = Var x0
>       p = unitycoeff x p0
>       p_inf = Skolem.simplify (minusinf x p) 
>       bs = bset x p
>       js = [1 .. divlcm x p]
>       p_element j b =
>         linrep vars x (linearAdd vars b (termInteger j)) p 
>       stage j = F.listDisj
>         (linrep vars x (termInteger j) p_inf :
>          map (p_element j) bs) in
>   F.listDisj (map stage js)
> cooper _ _ = error "cooper: not an existential formula"

> operations :: [(Pred, Integer -> Integer -> Bool)]
> operations = [("=",(==)), 
>               ("<",(<)),
>               (">",(>)), 
>               ("<=",(<=)), 
>               (">=",(>=)),
>               ("divides", \x y -> y `mod` x == 0)]

> evalc :: Formula -> Formula 
> evalc = F.onatoms
>  (\at@(R p [s, t]) -> case List.lookup p operations of
>                         Just op -> if isNumeral s && isNumeral t then 
>                                      if op (rati $ destNumeral s) (rati $ destNumeral t) then Top else Bot
>                                    else Atom at
>                         Nothing -> Atom at)

> integerQelim :: Formula -> Formula 
> integerQelim = 
>  Skolem.simplify . evalc .
>     Qelim.lift linform (Qelim.cnnf posineq . evalc) cooper

> relativize :: (Var -> Formula) -> Formula -> Formula 
> relativize r fm =
>  case fm of
>    Not p -> (¬) $ relativize r p
>    And p q -> relativize r p ∧ relativize r q
>    Or p q -> relativize r p ∨ relativize r q
>    Imp p q -> relativize r p ⊃ relativize r q
>    Iff p q -> relativize r p ⇔ relativize r q
>    All x p -> (¥) x (r x ⊃ relativize r p)
>    Ex x p -> (∃) x (r x ∧ relativize r p)
>    _ -> fm

> naturalQelim :: Formula -> Formula 
> naturalQelim = integerQelim . relativize (\x -> zero ≤ Var x)
