
> module Formula ( onatoms, overatoms, atomUnion
>                , opp, negative, positive
>                , conjuncts, disjuncts
>                , listConj, listDisj
>                , listForall, listExists
>                , destImp, unIff
>                , (/\), (\/), (<=>), (==>)
>                ) 

> where

> import Prelude hiding ((-))
> import qualified Data.List as List
> import FormulaSyn

> infixr 8 /\
> infixr 7 \/
> infixr 6 ==>
> infixr 5 <=>

-- -----------------------------------------------------------------------------
--  Infix ops                                                                   
-- -----------------------------------------------------------------------------

> (/\) :: Formula -> Formula -> Formula 
> (/\) = And

> (\/) :: Formula -> Formula -> Formula 
> (\/) = Or

> (==>) :: Formula -> Formula -> Formula 
> (==>) = Imp

> (<=>) :: Formula -> Formula -> Formula 
> (<=>) = Iff

-- -----------------------------------------------------------------------------
--  Combinators                                                                 
-- -----------------------------------------------------------------------------

Map

> onatoms :: (Rel -> Formula) -> Formula -> Formula
> onatoms f fm =
>   case fm of 
>     [$fol| true |] -> [$fol| true |] 
>     [$fol| false |] -> [$fol| false |] 
>     [$fol| ^a |] -> f a
>     [$fol| ~ $p |] -> [$fol| ~ $p' |]
>       where p' = onatoms f p
>     [$fol| $p \/ $q |] -> [$fol| $p' \/ $q' |] 
>       where p' = onatoms f p
>             q' = onatoms f q
>     [$fol| $p /\ $q |] -> [$fol| $p' /\ $q' |] 
>       where p' = onatoms f p
>             q' = onatoms f q
>     [$fol| $p ==> $q |] -> [$fol| $p' ==> $q' |] 
>       where p' = onatoms f p
>             q' = onatoms f q
>     [$fol| $p <=> $q |] -> [$fol| $p' <=> $q' |] 
>       where p' = onatoms f p
>             q' = onatoms f q
>     [$fol| forall $x. $p |] -> [$fol| forall $x. $p' |]
>       where p' = onatoms f p
>     [$fol| exists $x. $p |] -> [$fol| exists $x. $p' |]
>       where p' = onatoms f p

Fold

> overatoms :: (Rel -> a -> a) -> Formula -> a -> a
> overatoms f fm b = 
>   case fm of 
>     [$fol| ^a |] -> f a b
>     [$fol| ~ $p |] -> over1 p
>     [$fol| $p \/ $q |] -> over2 p q
>     [$fol| $p /\ $q |] -> over2 p q
>     [$fol| $p ==> $q |] -> over2 p q
>     [$fol| $p <=> $q |] -> over2 p q
>     [$fol| forall $x. $p |] -> over1 p
>     [$fol| exists $x. $p |] -> over1 p
>     _ -> b
>     where over1 p = overatoms f p b
>           over2 p q = overatoms f p (overatoms f q b)

Collect atoms

> atomUnion :: Eq b => (Rel -> [b]) -> Formula -> [b]
> atomUnion f fm = List.nub (overatoms (\h t -> f(h) ++ t) fm [])

-- -----------------------------------------------------------------------------
--  Util                                                                        
-- -----------------------------------------------------------------------------

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
> destImp [$fol| $a ==> $b |] = (a, b)
> destImp _ = error "destImp"

Opposite of a formula (Harrison's 'negate')

(Note that Harrison's term 'negate' is not usable because it's used by
the Prelude.)

> opp :: Formula -> Formula
> opp [$fol| ~ $p |] = p 
> opp [$fol| $p |] = [$fol| ~ $p |]

Sign of a formula

> negative :: Formula -> Bool
> negative [$fol| ~ $p |] = True
> negative _ = False

> positive :: Formula -> Bool
> positive = not . negative

Split into conjuncts 

> conjuncts :: Formula -> [Formula]
> conjuncts [$fol| $p /\ $q |] = conjuncts p ++ conjuncts q
> conjuncts fm = [fm]

Split into disjuncts

> disjuncts :: Formula -> [Formula]
> disjuncts [$fol| $p \/ $q |] = disjuncts p ++ disjuncts q
> disjuncts fm = [fm]

Remove occurrences of <=> 

> unIff :: Formula -> Formula
> unIff fm = case fm of
>   [$fol| $p <=> $q |] -> (p' ==> q') /\ (q' ==> p')
>     where p' = unIff p
>           q' = unIff q 
>   [$fol| ~ $p |] -> Not (unIff p)
>   [$fol| $p \/ $q |] -> unIff p \/ unIff q
>   [$fol| $p /\ $q |] -> unIff p /\ unIff q
>   [$fol| $p ==> $q |] -> unIff p ==> unIff q
>   [$fol| forall $x. $p |] -> All x (unIff p)
>   [$fol| exists $x. $p |] -> Ex x (unIff p)
>   _ -> fm
