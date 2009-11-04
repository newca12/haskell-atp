
| Dense linear orders

* Signature 

> module ATP.DLO
>   ( qelim
>   , valid
>     -- * Hidden
>   , lfn
>   , dloBasic
>   , afn
>   )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude
> import qualified ATP.DP as DP
> import ATP.FormulaSyn
> import qualified ATP.Formula as F
> import qualified ATP.FOL as FOL
> import qualified ATP.Equal as Equal
> import qualified ATP.Prop as Prop
> import qualified ATP.Qelim as Qelim
> import qualified ATP.Util.Lib as Lib
> import ATP.Util.Lib ((⟾))
> import ATP.Util.ListSet ((\\))
> import qualified ATP.Util.Parse as P
> import qualified Data.Char as Char
> import qualified Data.List as List

* Dense linear orders

> lfn :: Formula -> Formula 
> lfn [$form| ¬ ($s < $t) |] = [$form| $s = $t ∨ $t < $s |]
> lfn [$form| ¬ ($s = $t) |] = [$form| $s < $t ∨ $t < $s |]
> lfn fm = fm

> dloBasic :: Formula -> Formula 
> dloBasic (Ex x p) = 
>   let x' = Var x 
>       cjs = F.conjuncts p \\ [ x' ≡ x' ] 
>       left (Atom (R "<" [l, _])) = l
>       left _ = __IMPOSSIBLE__ 
>       right (Atom (R "<" [_, r])) = r
>       right _ = __IMPOSSIBLE__ 
>   in case List.find Equal.isEq cjs of
>     Just eqn -> let (s, t) = Equal.destEq eqn
>                     y = if s == x' then t else s in
>                 F.listConj $ map (FOL.apply $ x ⟾ y) (cjs \\ [eqn])
>     Nothing -> if elem (x' ≺ x') cjs then Bot else
>                let (lefts, rights) = List.partition (\a -> right a == x') cjs 
>                    ls = map left lefts
>                    rs = map right rights in
>                F.listConj (Lib.allPairs (≺) ls rs)
> dloBasic _ = error "dloBasic" 

> afn :: Vars -> Formula -> Formula 
> afn _ [$form| $s ≤ $t |] = [$form| ¬ ($t < $s) |]
> afn _ [$form| $s ≥ $t |] = [$form| ¬ ($s < $t) |]
> afn _ [$form| $s > $t |] = [$form| $t ≺ $s |]
> afn _ fm = fm

> qelim :: Formula -> Formula 
> qelim = Qelim.lift afn (Prop.dnf . Qelim.cnnf lfn) (const dloBasic)

* Validity

> destNumeral :: Term -> Rational
> destNumeral (Fn ns []) = P.parse ns
> destNumeral t = error ("destNumeral: " ++ show t)

> isNumeral :: Term -> Bool
> isNumeral (Fn ns []) | head ns == '-' = List.all Char.isDigit (tail ns)
>                      | otherwise = List.all Char.isDigit ns
> isNumeral _ = False

> reduce :: Formula -> Formula
> reduce f@(Atom (R p [s,t])) | isNumeral s && isNumeral t = 
>   let s' = destNumeral s
>       t' = destNumeral t
>   in case p of 
>        "=" -> if s' == t' then Top else Bot 
>        "<" -> if s' < t' then Top else Bot 
>        _ -> f
> reduce (And p q) = And (reduce p) (reduce q)
> reduce (Imp p q) = Imp (reduce p) (reduce q)
> reduce (Iff p q) = Iff (reduce p) (reduce q)
> reduce (Or p q) = Or (reduce p) (reduce q)
> reduce (Not p) = Not (reduce p)
> reduce f = f

> valid :: Formula -> Bool
> valid = DP.dplltaut . reduce . qelim . FOL.generalize
