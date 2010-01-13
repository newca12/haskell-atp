
| Dense linear orders

* Signature 

> module ATP.Dlo
>   ( qelim
>   , valid
>     -- * Hidden
>   , lfn
>   , dloBasic
>   , afn
>   )
> where

* Imports

#include "../undefined.h" 

> import ATP.Util.Prelude
> import qualified ATP.Dp as Dp
> import ATP.FormulaSyn
> import qualified ATP.Formula as F
> import qualified ATP.Fol as Fol
> import qualified ATP.Equal as Equal
> import qualified ATP.Prop as Prop
> import qualified ATP.Qelim as Qelim
> import ATP.Util.Lib ((⟾))
> import qualified ATP.Util.List as List
> import ATP.Util.ListSet ((\\))
> import qualified ATP.Util.Parse as P
> import qualified Data.Char as Char

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
>                 F.listConj $ map (Fol.apply $ x ⟾ y) (cjs \\ [eqn])
>     Nothing -> if elem (x' ≺ x') cjs then Bot else
>                let (lefts, rights) = List.partition (\a -> right a == x') cjs 
>                    ls = map left lefts
>                    rs = map right rights in
>                F.listConj (List.allPairs (≺) ls rs)
> dloBasic _ = error "dloBasic" 

Here we deviate slightly from Harrison and allow integer constants in
the atomic formulas.

> afn :: Vars -> Formula -> Formula 
> afn xs f = case f of 
>   [$form| $s ≤ $t |] -> afn xs [$form| ¬ ($t < $s) |]
>   [$form| $s ≥ $t |] -> afn xs [$form| ¬ ($s < $t) |]
>   [$form| $s > $t |] -> afn xs [$form| $t ≺ $s |]
>   [$form| $n < $m |] -> case (n, m) of 
>     (Num n', Num m') -> if n' < m' then (⊤) else (⊥)
>     _ -> f
>   [$form| ¬ ($n < $m) |] -> case (n, m) of 
>     (Num n', Num m') -> if n' > m' then (⊤) else (⊥)
>     _ -> f
>   _ -> f

> qelim :: Formula ->Formula 
> qelim = Qelim.lift afn (Prop.dnf . Qelim.cnnf lfn) (const dloBasic)

* Validity

> destNumeral :: Term -> Rational
> destNumeral (Fn ns []) = P.parse ns
> destNumeral _ = __IMPOSSIBLE__ 

> isNumeral :: Term -> Bool
> isNumeral (Fn ns []) 
>   | head ns == '-' = List.all Char.isDigit (tail ns)
>   | otherwise = List.all Char.isDigit ns
> isNumeral _ = False

> reduce :: Formula -> Formula
> reduce f@(Atom (R p [s,t])) | isNumeral s && isNumeral t = 
>   let s' = destNumeral s
>       t' = destNumeral t
>   in case p of 
>        "=" -> if s' == t' then Top else Bot 
>        "<" -> if s' < t' then Top else Bot 
>        _ -> f
> reduce [$form| $p ∧ $q |] = reduce p ∧ reduce q
> reduce [$form| $p ⊃ $q |] = reduce p ⊃ reduce q
> reduce [$form| $p ⇔ $q |] = reduce p ⇔ reduce q
> reduce [$form| $p ∨ $q |] = reduce p ∨ reduce q
> reduce [$form| ¬ $p |] = (¬) (reduce p)
> reduce f = f

> valid :: Formula -> Bool
> valid = Dp.dplltaut . reduce . qelim . Fol.generalize
