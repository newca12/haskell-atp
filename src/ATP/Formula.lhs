
* Signature

> module ATP.Formula 
>   ( onatoms, overatoms, atomUnion
>   , opp, negative, positive
>   , conjuncts, disjuncts
>   , listConj, listDisj
>   , listForall, listExists
>   , destImp, unIff
>   ) 
> where

* Imports

> import Prelude hiding ((-))
> import qualified Data.List as List
> import ATP.FormulaSyn

* Combinators

Map

> onatoms :: (Rel -> Formula) -> Formula -> Formula
> onatoms f fm =
>   case fm of 
>     [$form| true |] -> [$form| true |] 
>     [$form| false |] -> [$form| false |] 
>     [$form| ^a |] -> f a
>     [$form| ~ $p |] -> [$form| ¬ $p' |]
>       where p' = onatoms f p
>     [$form| $p ∨ $q |] -> [$form| $p' ∨ $q' |] 
>       where p' = onatoms f p
>             q' = onatoms f q
>     [$form| $p ∧ $q |] -> [$form| $p' ∧ $q' |] 
>       where p' = onatoms f p
>             q' = onatoms f q
>     [$form| $p ⊃ $q |] -> [$form| $p' ⊃ $q' |] 
>       where p' = onatoms f p
>             q' = onatoms f q
>     [$form| $p ⇔ $q |] -> [$form| $p' ⇔ $q' |] 
>       where p' = onatoms f p
>             q' = onatoms f q
>     [$form| forall $x. $p |] -> [$form| ∀ $x. $p' |]
>       where p' = onatoms f p
>     [$form| exists $x. $p |] -> [$form| ∃ $x. $p' |]
>       where p' = onatoms f p

Fmd

> overatoms :: (Rel -> a -> a) -> Formula -> a -> a
> overatoms f fm b = 
>   case fm of 
>     [$form| ^a |] -> f a b
>     [$form| ~ $p |] -> over1 p
>     [$form| $p ∨ $q |] -> over2 p q
>     [$form| $p ∧ $q |] -> over2 p q
>     [$form| $p ⊃ $q |] -> over2 p q
>     [$form| $p ⇔ $q |] -> over2 p q
>     [$form| ∀ _. $p |] -> over1 p
>     [$form| ∃ _. $p |] -> over1 p
>     _ -> b
>     where over1 p = overatoms f p b
>           over2 p q = overatoms f p (overatoms f q b)

Collect atoms

> atomUnion :: Eq b => (Rel -> [b]) -> Formula -> [b]
> atomUnion f fm = List.nub (overatoms (\h t -> f(h) ++ t) fm [])

* Util

Make a big conjunction(disjunction resp.) from a list
listConj [a,b,c] --> a & b & c 

> listConj :: [Formula] -> Formula
> listConj [] = Top
> listConj l = foldr1 And l

> listDisj :: [Formula] -> Formula
> listDisj [] = Bot
> listDisj l = foldr1 Or l

Make a big forall (exists resp.) from a list
listForall [x,y,z] <<P(x,y,z)>> --> <<forall x y z. P(x,y,z)>>

> listForall :: Vars -> Formula -> Formula
> listForall xs b = foldr All b xs

> listExists :: Vars -> Formula -> Formula
> listExists xs b = foldr Ex b xs

> destImp :: Formula -> (Formula, Formula)
> destImp [$form| $a ⊃ $b |] = (a, b)
> destImp _ = error "destImp"

Opposite of a formula (Harrison's 'negate')

(Note that Harrison's term 'negate' is not usable because it's used by
the Prelude.)

> opp :: Formula -> Formula
> opp [$form| ¬ $p |] = p 
> opp [$form| $p |] = [$form| ~ $p |]

Sign of a formula

> negative :: Formula -> Bool
> negative [$form| ¬ _ |] = True
> negative _ = False

> positive :: Formula -> Bool
> positive = not . negative

Split into conjuncts 

> conjuncts :: Formula -> [Formula]
> conjuncts [$form| $p ∧ $q |] = conjuncts p ++ conjuncts q
> conjuncts fm = [fm]

Split into disjuncts

> disjuncts :: Formula -> [Formula]
> disjuncts [$form| $p ∨ $q |] = disjuncts p ++ disjuncts q
> disjuncts fm = [fm]

Remove occurrences of ⇔ 

> unIff :: Formula -> Formula
> unIff fm = case fm of
>   [$form| $p ⇔ $q |] -> (p' ⊃ q') ∧ (q' ⊃ p')
>     where p' = unIff p
>           q' = unIff q 
>   [$form| ~ $p |] -> Not (unIff p)
>   [$form| $p ∨ $q |] -> unIff p ∨ unIff q
>   [$form| $p ∧ $q |] -> unIff p ∧ unIff q
>   [$form| $p ⊃ $q |] -> unIff p ⊃ unIff q
>   [$form| ∀ $x. $p |] -> (¥) x (unIff p)
>   [$form| ∃ $x. $p |] -> (∃) x (unIff p)
>   _ -> fm
