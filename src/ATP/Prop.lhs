
Propositional Logic.  Atomic propositions are simply
propositional variables.

> module Prop ( eval
>             , atoms
>             , apply
>             , distrib
>             , simplify
>             , simplify1
>             , truthtable
>             , unsatisfiable
>             , satisfiable
>             , dualize
>             , trivial
>             , tautology
>             , occurrences
>             , subsume
>             , nnf
>             , nenf
>             , simpcnf
>             , cnf
>             , purednf
>             , simpdnf
>             , dnf
>             ) where

> import Prelude 
> import qualified Data.List as List
> import qualified Data.Map as Map
> import Data.Map(Map)
> import qualified Text.PrettyPrint.HughesPJClass as PP
> import Text.PrettyPrint.HughesPJClass ( ($+$) )

> import qualified Lib 
> import qualified ListSet
> import FormulaSyn
> import qualified Formula as F

Propositions

> apply :: Map Rel Formula -> Formula -> Formula
> apply env = F.onatoms (\p -> case Map.lookup p env of 
>                                Just p' -> p'
>                                Nothing -> Atom p)

Evaluate a formula in a mapping of variables to truth values.

> eval :: Formula -> (Rel -> Bool) -> Bool
> eval fm v = case fm of
>   [$fol| true |]      -> True
>   [$fol| false |]     -> False
>   [$fol| ^a |]        -> v a
>   [$fol| ~ $p |]      -> not (eval p v)
>   [$fol| $p /\ $q |]  -> eval p v && eval q v
>   [$fol| $p \/ $q |]  -> eval p v || eval q v
>   [$fol| $p ==> $q |] -> not (eval p v) || (eval q v)
>   [$fol| $p <=> $q |] -> eval p v == eval q v
>   _ -> error "quantifier in prop eval"

Return all atoms in a formula.

> atoms :: Formula -> [Rel]
> atoms = List.sort . F.atomUnion (\x -> [x]) 

Valuation combinator.  

A valuation is a mapping from atoms to truth values.

> onallvaluations :: Eq a => ((a -> Bool) -> b) -> (b -> b -> b) 
>                      -> (a -> Bool) -> [a] -> b
> onallvaluations subfn comb v pvs = case pvs of
>   [] -> subfn v
>   p:ps -> let v' t q = if q == p then t else v q in
>           comb (onallvaluations subfn comb (v' False) ps)
>                (onallvaluations subfn comb (v' True) ps)
> 

Truthtables.

> truthtable :: Formula -> String
> truthtable fm = PP.render (truthtableDoc fm)
>     where
>     truthtableDoc fm' =
>         let pvs = atoms fm' 
>             width = foldr (max . length . show) 5 pvs + 1 
>             fixw s = s ++ replicate (width - length s) ' ' 
>             truthstring p = fixw (if p then "true" else "false") 
>             separator = replicate (width * length pvs + 9) '-' 
>             row v =
>                 let lis = map (truthstring . v) pvs 
>                     ans = truthstring(eval fm' v) in
>                     [lis ++ [ans]]
>             rows = onallvaluations row (++) (const False) pvs
>             rowStr r = let (lis, ans) = splitAt (length r - 1) r in
>                            (foldr (++) ("| " ++ head ans) lis)
>         in
>         PP.empty $+$
>         PP.text (foldr (\s t -> fixw(show s) ++ t) "| formula" pvs) $+$
>         PP.empty $+$
>         PP.text separator $+$
>         PP.empty $+$
>         PP.vcat (map (PP.text . rowStr) rows) $+$
>         PP.text separator $+$
>         PP.empty 

Tautologies

> tautology :: Formula -> Bool
> tautology fm = onallvaluations (eval fm) (&&) (const False) (atoms fm)

Satisfiability

> unsatisfiable :: Formula -> Bool
> unsatisfiable = tautology . Not 

> satisfiable :: Formula -> Bool
> satisfiable = not . unsatisfiable 

Duality

> dualize :: Formula -> Formula 
> dualize = Not . subdualize

> subdualize :: Formula -> Formula 
> subdualize fm = case fm of
>   [$fol| false |] -> [$fol| true |]
>   [$fol| true |] -> [$fol| false |]
>   [$fol| ^_ |] -> fm
>   [$fol| ~ $p |] -> [$fol| ~ $p' |]
>     where p' = subdualize p
>   [$fol| $p /\ $q |] -> [$fol| $p' \/ $q' |]
>     where p' = subdualize p
>           q' = subdualize q
>   [$fol| $p \/ $q |] -> [$fol| $p' /\ $q' |]
>     where p' = subdualize p
>           q' = subdualize q
>   _ -> error "Formula involves connectives ==> and <=>"

Simplification

> simplify :: Formula -> Formula
> simplify fm = case fm of
>   [$fol| ~ $p |] -> simplify1 [$fol| ~ $p' |]
>     where p' = simplify p
>   [$fol| $p /\ $q |] -> simplify1 [$fol| $p' /\ $q' |]
>     where p' = simplify p
>           q' = simplify q
>   [$fol| $p \/ $q |] -> simplify1 [$fol| $p' \/ $q' |]
>     where p' = simplify p
>           q' = simplify q
>   [$fol| $p ==> $q |] -> simplify1 [$fol| $p' ==> $q' |]
>     where p' = simplify p
>           q' = simplify q
>   [$fol| $p <=> $q |] -> simplify1 [$fol| $p' <=> $q' |]
>     where p' = simplify p
>           q' = simplify q
>   _ -> fm

> simplify1 :: Formula -> Formula
> simplify1 fm = case fm of
>   [$fol| ~ false |] -> [$fol| true |]
>   [$fol| ~ true |] -> [$fol| false |]
>   [$fol| false /\ _ |] -> [$fol| false |]
>   [$fol| _ /\ false |] -> [$fol| false |]
>   [$fol| true /\ $q |] -> q
>   [$fol| $p /\ true |] -> p
>   [$fol| false \/ $q |] -> q
>   [$fol| $p \/ false |] -> p
>   [$fol| true \/ _ |] -> [$fol| true |]
>   [$fol| _ \/ true |] -> [$fol| true |]
>   [$fol| false ==> _ |] -> [$fol| true |]
>   [$fol| $p ==> false |] ->  [$fol| ~ $p |]
>   [$fol| true ==> $q |] -> q
>   [$fol| _ ==> true |] ->  [$fol| true |]
>   [$fol| false <=> $q |] -> [$fol| ~ $q |]
>   [$fol| $p <=> false |] -> [$fol| ~ $p |]
>   [$fol| true <=> $q |] -> q
>   [$fol| $p <=> true |] -> p
>   _ -> fm

Negation normal form

> nnf :: Formula -> Formula
> nnf = nnf' . simplify

> nnf' :: Formula -> Formula
> nnf' fm = case fm of 
>   [$fol| $p /\ $q |] -> [$fol| $p' /\ $q' |]
>     where p' = nnf' p 
>           q' = nnf' q
>   [$fol| $p \/ $q |] -> [$fol| $p' \/ $q' |]
>     where p' = nnf' p 
>           q' = nnf' q
>   [$fol| $p ==> $q |] -> [$fol| ~ $p' \/ $q' |]
>     where p' = nnf' [$fol| ~ $p |]
>           q' = nnf' q
>   [$fol| $p <=> $q |] -> [$fol| $p' /\ $q' \/ $p'' /\ $q'' |]
>     where p' = nnf' p
>           q' = nnf' q
>           p'' = nnf' [$fol| ~ $p |]
>           q'' = nnf' [$fol| ~ $q |]
>   [$fol| ~ ~ $p |] -> nnf' p
>   [$fol| ~ ($p /\ $q) |] -> [$fol| $p' \/ $q' |]
>     where p' = nnf' [$fol| ~ $p |]
>           q' = nnf' [$fol| ~ $q |]
>   [$fol| ~ ($p \/ $q) |] -> [$fol| $p' /\ $q' |]
>     where p' = nnf' [$fol| ~ $p |]
>           q' = nnf' [$fol| ~ $q |]
>   [$fol| ~ ($p ==> $q) |] -> [$fol| $p' /\ $q' |]
>     where p' = nnf' p
>           q' = nnf' [$fol| ~ $q |]
>   [$fol| ~ ($p <=> $q) |] -> [$fol| $p' /\ $q'' \/ $p'' /\ $q' |]
>     where p' = nnf' p
>           q' = nnf' q
>           p'' = nnf' [$fol| ~ $p |]
>           q'' = nnf' [$fol| ~ $q |]
>   _ -> fm

> nenf :: Formula -> Formula
> nenf = nenf' . simplify 

> nenf' :: Formula -> Formula
> nenf' fm = case fm of 
>   [$fol| ~~$p |] -> nenf' p
>   [$fol| ~($p /\ $q) |] -> [$fol| $p' \/ $q' |] 
>     where p' = nenf' [$fol| ~ $p |]
>           q' = nenf' [$fol| ~ $q |]
>   [$fol| ~($p \/ $q) |] -> [$fol| $p' /\ $q' |] 
>     where p' = nenf' [$fol| ~ $p |]
>           q' = nenf' [$fol| ~ $q |]
>   [$fol| ~($p ==> $q) |] -> [$fol| $p' /\ $q' |] 
>     where p' = nenf' p
>           q' = nenf' [$fol| ~ $q |]
>   [$fol| ~($p <=> $q) |] -> [$fol| $p' <=> $q' |] 
>     where p' = nenf' p
>           q' = nenf' [$fol| ~ $q |]
>   [$fol| $p /\ $q |] -> [$fol| $p' /\ $q' |] 
>     where p' = nenf' p
>           q' = nenf' q
>   [$fol| $p \/ $q |] -> [$fol| $p' \/ $q' |] 
>     where p' = nenf' p
>           q' = nenf' q
>   [$fol| $p ==> $q |] -> [$fol| $p' \/ $q' |] 
>     where p' = nenf' [$fol| ~ $p |]
>           q' = nenf' q
>   [$fol| $p <=> $q |] -> [$fol| $p' <=> $q' |] 
>     where p' = nenf' p
>           q' = nenf' q
>   _ -> fm

Positive and negative occurrances of atoms

> occurrences :: Rel -> Formula -> (Bool, Bool)
> occurrences x fm = case fm of
>   [$fol| ^y |] -> (x == y, False)
>   [$fol| ~ $p |] -> (neg, pos)
>     where (pos, neg) = occurrences x p 
>   [$fol| $p /\ $q |] -> (pos1 || pos2, neg1 || neg2)
>     where (pos1, neg1) = occurrences x p
>           (pos2, neg2) = occurrences x q 
>   [$fol| $p \/ $q |] -> (pos1 || pos2, neg1 || neg2)
>     where (pos1, neg1) = occurrences x p
>           (pos2, neg2) = occurrences x q 
>   [$fol| $p ==> $q |] -> (neg1 || pos2, pos1 || neg2)
>     where (pos1, neg1) = occurrences x p
>           (pos2, neg2) = occurrences x q 
>   [$fol| $p <=> $q |] -> if pos1 || pos2 || neg1 || neg2 
>                           then (True, True) else (False, False)
>     where (pos1, neg1) = occurrences x p
>           (pos2, neg2) = occurrences x q 
>   _ -> (False, False)

Distribute clauses 

> distrib :: [[Formula]] -> [[Formula]] -> [[Formula]]
> distrib = Lib.allPairs ListSet.union 

Subsumption

> subsume :: [[Formula]] -> [[Formula]]
> subsume cls =
>   filter (\cl -> not(any (\cl' -> ListSet.psubset cl' cl) cls)) cls

Disjunctive normal form

> dnf :: Formula -> Formula 
> dnf = F.listDisj . map F.listConj . simpdnf

> simpdnf :: Formula -> [[Formula]]
> simpdnf Bot = []
> simpdnf Top = [[]]
> simpdnf fm = (subsume . filter (not.trivial) . purednf . nnf) fm

> purednf :: Formula -> [[Formula]]
> purednf fm = case fm of
>   And p q -> distrib (purednf p) (purednf q)
>   Or p q -> ListSet.union (purednf p) (purednf q)
>   _ -> [[fm]]

> trivial :: [Formula] -> Bool
> trivial lits =
>     let (pos, neg) = List.partition F.positive lits in
>     ListSet.intersect pos (map F.opp neg) /= []

Conjunctive normal form

> cnf :: Formula -> Formula
> cnf = F.listConj . map F.listDisj . simpcnf 

> simpcnf :: Formula -> [[Formula]]
> simpcnf Bot = [[]]
> simpcnf Top = []
> simpcnf fm = 
>   let cjs = filter (not . trivial) (purecnf $ nnf fm) in
>   filter (\c -> not $ any (\c' -> ListSet.psubset c' c) cjs) cjs             

> purecnf :: Formula -> [[Formula]]
> purecnf = map (map F.opp) . (purednf . nnf . Not)

nnf [$prop| p <=> (q <=> r) |]
cnf [$prop| p <=> (q <=> r) |]
dnf [$prop| p <=> (q <=> r) |]


