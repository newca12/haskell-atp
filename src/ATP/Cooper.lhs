
* Signature

> module ATP.Cooper
>   ( zero
>   , one
>   , isNumeral
>   , numeral1
>   , numeral2
>   , evalc
>   , destNumeral
>   , integerQelim
>   , naturalQelim
>   )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Order as Order
> import qualified ATP.Qelim as Qelim
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Util.ListSet as Set
> import qualified Data.Char as Char
> import qualified Data.List as List

* Numerals

> zero :: Term
> zero = fromInteger 0

> one :: Term
> one = fromInteger 1

> mkNumeral :: Integer -> Term
> mkNumeral n = Fn (show n) []

> isNumeral :: Term -> Bool
> isNumeral (Fn ns []) = case ns of 
>   '-':ns' -> List.all Char.isDigit ns'
>   _ -> List.all Char.isDigit ns
> isNumeral _ = False

> destNumeral :: Term -> Integer
> destNumeral (Fn ns []) = read ns
> destNumeral _ = __IMPOSSIBLE__ 

> numeral1 :: (Integer -> Integer) -> Term -> Term
> numeral1 fn = mkNumeral . fn . destNumeral

> numeral2 :: (Integer -> Integer -> Integer) -> Term -> Term -> Term
> numeral2 fn m n = mkNumeral $ fn (destNumeral m) (destNumeral n)

* Arithmetic on canonical terms

> linearCmul :: Integer -> Term -> Term
> linearCmul 0 _ = zero
> linearCmul n tm = case tm of 
>   [$term| $c * $x + $r |] -> numeral1 ((*) n) c * x + linearCmul n r
>   k -> numeral1 ((*) n) k

> linearAdd :: Vars -> Term -> Term -> Term
> linearAdd vars tm1 tm2 =
>   case (tm1, tm2) of 
>     ([$term| $c1 * ^x1 + $r1 |], [$term| $c2 * ^x2 + $r2|]) -> 
>        if x1 == x2 then
>          let c = numeral2 (+) c1 c2 in
>          if c == zero then linearAdd vars r1 r2
>          else c * Var x1 + linearAdd vars r1 r2
>        else if Order.earlier vars x1 x2 then
>          c1 * Var x1 + linearAdd vars r1 tm2
>        else
>          c2 * Var x2 + linearAdd vars tm1 r2
>     ([$term| $c1 * ^x1 + $r1 |], _) -> c1 * Var x1 + linearAdd vars r1 tm2
>     (_, [$term| $c2 * ^x2 + $r2 |]) -> c2 * Var x2 + linearAdd vars tm1 r2
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

* Canonization

Terms

> lint :: Vars -> Term -> Term
> lint vars tm =
>   case tm of
>    [$term| ^_ |] -> one * tm + zero
>    [$term| - $t |] -> linearNeg (lint vars t)
>    [$term| $s + $t |] -> linearAdd vars (lint vars s) (lint vars t)
>    [$term| $s - $t |] -> linearSub vars (lint vars s) (lint vars t)
>    [$term| $s * $t |] -> linearMul (lint vars s) (lint vars t)
>    _ -> if isNumeral tm then tm else error $ "lint: unknown term: " ++ show tm

Atoms 

> mkatom :: Vars -> Pred -> Term -> Formula 
> mkatom vars p t = Atom (R p [zero, lint vars t])

> linform :: Vars -> Formula -> Formula 
> linform vars fm =
>  case fm of
>    Atom(R "divides" [c, t]) -> Atom(R "divides" [numeral1 abs c, lint vars t])
>    [$form| $s = $t |] -> mkatom vars "=" (t - s)
>    [$form| $s < $t |] -> mkatom vars "<" (t - s)
>    [$form| $s > $t |] -> mkatom vars "<" (s - t)
>    [$form| $s ≤ $t |] -> mkatom vars "<" (t + one - s)
>    [$form| $s ≥ $t |] -> mkatom vars "<" (s + one - t)
>    _ -> fm 

Eliminate negated inequalities.

> posineq :: Formula -> Formula 
> posineq fm = case fm of
>   [$form| ¬ (0 < $t) |] -> zero ≺ linearSub [] one t
>   _ -> fm

Find the LCM of the coefficients of x

> formlcm :: Term -> Formula -> Integer
> formlcm x f = case f of
>   Atom(R _ [_, [$term| $c * $y + _ |]]) | x == y -> abs $ destNumeral c
>   Not p -> formlcm x p
>   And p q -> lcm (formlcm x p) (formlcm x q)
>   Or p q -> lcm (formlcm x p) (formlcm x q)   
>   _ -> 1

> adjustcoeff :: Term -> Integer -> Formula -> Formula 
> adjustcoeff x l fm = 
>  case fm of
>    Atom (R p [d, [$term| $c * $y + $z |]]) | y == x ->
>      let m = l `div` destNumeral c
>          n = if p == "<" then abs m else m
>          xtm = fromInteger (m `div` n) * x in
>      Atom(R p [linearCmul (abs m) d, xtm + linearCmul n z])
>    Not p -> (¬) $ adjustcoeff x l p
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
>    [$form| 0 = 1 * $y + _ |] | x == y -> (⊥)
>    [$form| 0 < 1 * $y + _ |] | x == y -> (⊥)
>    [$form| 0 < _ * $y + _ |] | x == y -> (⊤)
>    [$form| ¬ $p |] -> (¬) $ minusinf x p
>    [$form| $p ∧ $q |] -> minusinf x p ∧ minusinf x q
>    [$form| $p ∨ $q |] -> minusinf x p ∨ minusinf x q
>    _ -> fm

> divlcm :: Term -> Formula -> Integer
> divlcm x fm =
>  case fm of
>    Atom (R "divides" [d, [$term| _ * $y + _ |]]) | x == y ->
>      destNumeral d
>    Not p -> divlcm x p
>    And p q -> lcm (divlcm x p) (divlcm x q)
>    Or p q -> lcm (divlcm x p) (divlcm x q)
>    _ -> 1

> bset :: Term -> Formula -> [Term]
> bset x fm = case fm of 
>   [$form| ¬ (0 = 1 * $y + $a) |] | x == y -> [linearNeg a]
>   [$form| 0 = 1 * $y + $a |] | x == y -> [linearNeg $ linearAdd [] a one]
>   [$form| 0 < 1 * $y + $a |] | x == y -> [linearNeg a]
>   [$form| ¬ $p |] -> bset x p
>   [$form| $p ∧ $q |] -> Set.union (bset x p) (bset x q)
>   [$form| $p ∨ $q |] -> Set.union (bset x p) (bset x q)
>   _ -> []

> linrep :: Vars -> Term -> Term -> Formula -> Formula 
> linrep vars x t fm =
>  case fm of
>    Atom(R p [d, [$term| $c * $y + $a |]]) | x == y ->
>      let ct = linearCmul (destNumeral c) t in
>      Atom $ R p [d, linearAdd vars ct a]
>    Not p -> (¬) $ linrep vars x t p
>    And p q -> linrep vars x t p ∧ linrep vars x t q
>    Or p q -> linrep vars x t p ∨ linrep vars x t q
>    _ -> fm

> cooper :: Vars -> Formula -> Formula 
> cooper vars (Ex x0 p0) =
>   let x = Var x0
>       p = unitycoeff x p0
>       p_inf = Skolem.simplify $ minusinf x p
>       bs = bset x p
>       js = [1 .. divlcm x p]
>       p_element j b = linrep vars x (linearAdd vars b (mkNumeral j)) p
>       stage j = F.listDisj
>         (linrep vars x (mkNumeral j) p_inf :
>          map (p_element j) bs) 
>   in F.listDisj (map stage js)
> cooper _ _ = error "cooper: not an existential formula"

> operations :: [(Pred, Integer -> Integer -> Bool)]
> operations = [ ("=",(==))
>              , ("<",(<))
>              , (">",(>)) 
>              , ("<=",(<=))
>              , ("≤",(<=)) 
>              , (">=",(>=))
>              , ("≥",(>=))
>              , ("divides", \x y -> y `mod` x == 0)
>              ]

> evalc :: Formula -> Formula 
> evalc = F.onatoms atfn 
>  where 
>   atfn (at@(R p [s, t])) = case List.lookup p operations of
>     Just op -> 
>       if isNumeral s && isNumeral t then 
>         if op (destNumeral s) (destNumeral t) then (⊤) else (⊥)
>       else Atom at
>     Nothing -> Atom at
>   atfn _ = __IMPOSSIBLE__ 

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
