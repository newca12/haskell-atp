
Propositional Logic.  Atomic propositions are simply
propositional variables.

* Signature

> module ATP.Prop 
>   ( eval
>   , atoms
>   , apply
>   , distrib
>   , simplify
>   , simplify1
>   , truthtable
>   , unsatisfiable
>   , satisfiable
>   , dualize
>   , trivial
>   , tautology
>   , occurrences
>   , subsume
>   , nnf
>   , nenf
>   , simpcnf
>   , cnf
>   , purednf
>   , simpdnf
>   , dnf
>   ) 
> where

* Imports

> import Prelude 
> import qualified Data.List as List
> import qualified Data.Map as Map
> import Data.Map(Map)

> import qualified ATP.Util.Print as PP
> import ATP.Util.Print ( ($+$) )
> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.ListSet as Set
> import ATP.FormulaSyn 
> import qualified ATP.Formula as F

Propositions

> apply :: Map Rel Formula -> Formula -> Formula
> apply env = F.onatoms (\p -> case Map.lookup p env of 
>                                Just p' -> p'
>                                Nothing -> Atom p)

Evaluate a formula in a mapping of variables to truth values.

> eval :: Formula -> (Rel -> Bool) -> Bool
> eval fm v = case fm of
>   [$form| true |]      -> True
>   [$form| false |]     -> False
>   [$form| ^a |]        -> v a
>   [$form| ¬ $p |]      -> not (eval p v)
>   [$form| $p ∧ $q |]  -> eval p v && eval q v
>   [$form| $p ∨ $q |]  -> eval p v || eval q v
>   [$form| $p ⊃ $q |] -> not (eval p v) || (eval q v)
>   [$form| $p ⇔ $q |] -> eval p v == eval q v
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
>             truthstring p = fixw (if p then "⊤" else "⊥") 
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
>   [$form| false |] -> [$form| true |]
>   [$form| true |] -> [$form| false |]
>   [$form| ^_ |] -> fm
>   [$form| ¬ $p |] -> [$form| ¬ $p' |]
>     where p' = subdualize p
>   [$form| $p ∧ $q |] -> [$form| $p' ∨ $q' |]
>     where p' = subdualize p
>           q' = subdualize q
>   [$form| $p ∨ $q |] -> [$form| $p' ∧ $q' |]
>     where p' = subdualize p
>           q' = subdualize q
>   _ -> error "Formula involves connectives ⊃ and ⇔"

Simplification

> simplify :: Formula -> Formula
> simplify fm = case fm of
>   [$form| ¬ $p |] -> simplify1 [$form| ¬ $p' |]
>     where p' = simplify p
>   [$form| $p ∧ $q |] -> simplify1 [$form| $p' ∧ $q' |]
>     where p' = simplify p
>           q' = simplify q
>   [$form| $p ∨ $q |] -> simplify1 [$form| $p' ∨ $q' |]
>     where p' = simplify p
>           q' = simplify q
>   [$form| $p ⊃ $q |] -> simplify1 [$form| $p' ⊃ $q' |]
>     where p' = simplify p
>           q' = simplify q
>   [$form| $p ⇔ $q |] -> simplify1 [$form| $p' ⇔ $q' |]
>     where p' = simplify p
>           q' = simplify q
>   _ -> fm

> simplify1 :: Formula -> Formula
> simplify1 fm = case fm of
>   [$form| ¬ false |] -> [$form| true |]
>   [$form| ¬ true |] -> [$form| false |]
>   [$form| false ∧ _ |] -> [$form| false |]
>   [$form| _ ∧ false |] -> [$form| false |]
>   [$form| true ∧ $q |] -> q
>   [$form| $p ∧ true |] -> p
>   [$form| false ∨ $q |] -> q
>   [$form| $p ∨ false |] -> p
>   [$form| true ∨ _ |] -> [$form| true |]
>   [$form| _ ∨ true |] -> [$form| true |]
>   [$form| false ⊃ _ |] -> [$form| true |]
>   [$form| $p ⊃ false |] ->  [$form| ¬ $p |]
>   [$form| true ⊃ $q |] -> q
>   [$form| _ ⊃ true |] ->  [$form| true |]
>   [$form| false ⇔ $q |] -> [$form| ¬ $q |]
>   [$form| $p ⇔ false |] -> [$form| ¬ $p |]
>   [$form| true ⇔ $q |] -> q
>   [$form| $p ⇔ true |] -> p
>   _ -> fm

Negation normal form

> nnf :: Formula -> Formula
> nnf = nnf' . simplify

> nnf' :: Formula -> Formula
> nnf' fm = case fm of 
>   [$form| $p ∧ $q |] -> [$form| $p' ∧ $q' |]
>     where p' = nnf' p 
>           q' = nnf' q
>   [$form| $p ∨ $q |] -> [$form| $p' ∨ $q' |]
>     where p' = nnf' p 
>           q' = nnf' q
>   [$form| $p ⊃ $q |] -> [$form| $np' ∨ $q' |]
>     where np' = nnf' [$form| ¬ $p |]
>           q' = nnf' q
>   [$form| $p ⇔ $q |] -> [$form| $p' ∧ $q' ∨ $p'' ∧ $q'' |]
>     where p' = nnf' p
>           q' = nnf' q
>           p'' = nnf' [$form| ¬ $p |]
>           q'' = nnf' [$form| ¬ $q |]
>   [$form| ¬ ¬ $p |] -> nnf' p
>   [$form| ¬ ($p ∧ $q) |] -> [$form| $p' ∨ $q' |]
>     where p' = nnf' [$form| ¬ $p |]
>           q' = nnf' [$form| ¬ $q |]
>   [$form| ¬ ($p ∨ $q) |] -> [$form| $p' ∧ $q' |]
>     where p' = nnf' [$form| ¬ $p |]
>           q' = nnf' [$form| ¬ $q |]
>   [$form| ¬ ($p ⊃ $q) |] -> [$form| $p' ∧ $q' |]
>     where p' = nnf' p
>           q' = nnf' [$form| ¬ $q |]
>   [$form| ¬ ($p ⇔ $q) |] -> [$form| $p' ∧ $q'' ∨ $p'' ∧ $q' |]
>     where p' = nnf' p
>           q' = nnf' q
>           p'' = nnf' [$form| ¬ $p |]
>           q'' = nnf' [$form| ¬ $q |]
>   _ -> fm

> nenf :: Formula -> Formula
> nenf = nenf' . simplify 

> nenf' :: Formula -> Formula
> nenf' fm = case fm of 
>   [$form| ¬¬$p |] -> nenf' p
>   [$form| ¬($p ∧ $q) |] -> [$form| $p' ∨ $q' |] 
>     where p' = nenf' [$form| ¬ $p |]
>           q' = nenf' [$form| ¬ $q |]
>   [$form| ¬($p ∨ $q) |] -> [$form| $p' ∧ $q' |] 
>     where p' = nenf' [$form| ¬ $p |]
>           q' = nenf' [$form| ¬ $q |]
>   [$form| ¬($p ⊃ $q) |] -> [$form| $p' ∧ $q' |] 
>     where p' = nenf' p
>           q' = nenf' [$form| ¬ $q |]
>   [$form| ¬($p ⇔ $q) |] -> [$form| $p' ⇔ $q' |] 
>     where p' = nenf' p
>           q' = nenf' [$form| ¬ $q |]
>   [$form| $p ∧ $q |] -> [$form| $p' ∧ $q' |] 
>     where p' = nenf' p
>           q' = nenf' q
>   [$form| $p ∨ $q |] -> [$form| $p' ∨ $q' |] 
>     where p' = nenf' p
>           q' = nenf' q
>   [$form| $p ⊃ $q |] -> [$form| $p' ∨ $q' |] 
>     where p' = nenf' [$form| ¬ $p |]
>           q' = nenf' q
>   [$form| $p ⇔ $q |] -> [$form| $p' ⇔ $q' |] 
>     where p' = nenf' p
>           q' = nenf' q
>   _ -> fm

Positive and negative occurrances of atoms

> occurrences :: Rel -> Formula -> (Bool, Bool)
> occurrences x fm = case fm of
>   [$form| ^y |] -> (x == y, False)
>   [$form| ¬ $p |] -> (neg, pos)
>     where (pos, neg) = occurrences x p 
>   [$form| $p ∧ $q |] -> (pos1 || pos2, neg1 || neg2)
>     where (pos1, neg1) = occurrences x p
>           (pos2, neg2) = occurrences x q 
>   [$form| $p ∨ $q |] -> (pos1 || pos2, neg1 || neg2)
>     where (pos1, neg1) = occurrences x p
>           (pos2, neg2) = occurrences x q 
>   [$form| $p ⊃ $q |] -> (neg1 || pos2, pos1 || neg2)
>     where (pos1, neg1) = occurrences x p
>           (pos2, neg2) = occurrences x q 
>   [$form| $p ⇔ $q |] -> if pos1 || pos2 || neg1 || neg2 
>                           then (True, True) else (False, False)
>     where (pos1, neg1) = occurrences x p
>           (pos2, neg2) = occurrences x q 
>   _ -> (False, False)

Distribute clauses 

> distrib :: [[Formula]] -> [[Formula]] -> [[Formula]]
> distrib = Lib.allPairs Set.union 

Subsumption

> subsume :: [[Formula]] -> [[Formula]]
> subsume cls =
>   filter (\cl -> not(any (\cl' -> Set.psubset cl' cl) cls)) cls

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
>   Or p q -> Set.union (purednf p) (purednf q)
>   _ -> [[fm]]

> trivial :: [Formula] -> Bool
> trivial lits =
>     let (pos, neg) = List.partition F.positive lits in
>     Set.intersect pos (map F.opp neg) /= []

Conjunctive normal form

> cnf :: Formula -> Formula
> cnf = F.listConj . map F.listDisj . simpcnf 

> simpcnf :: Formula -> [[Formula]]
> simpcnf Bot = [[]]
> simpcnf Top = []
> simpcnf fm = 
>   let cjs = filter (not . trivial) (purecnf $ nnf fm) in
>   filter (\c -> not $ any (\c' -> Set.psubset c' c) cjs) cjs             

> purecnf :: Formula -> [[Formula]]
> purecnf = map (map F.opp) . (purednf . nnf . Not)

nnf [$form| p ⇔ (q ⇔ r) |]
cnf [$form| p ⇔ (q ⇔ r) |]
dnf [$form| p ⇔ (q ⇔ r) |]


