
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
>   , onallvaluations
>   , dual
>   , truthtable
>   , unsatisfiable
>   , satisfiable
>   , trivial
>   , tautology
>   , occurrences
>   , subsume
>   , nnf
>   , nenf
>   , simpcnf
>   , cnf
>   , purecnf
>   , purednf
>   , simpdnf
>   , dnf
>     -- * Testing
>   , forms
>   , tests
>   ) 
> where

* Imports

> import ATP.Util.Prelude
> import qualified ATP.Formula as F
> import ATP.FormulaSyn 
> import qualified ATP.Util.List as List
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet ((∪))
> import qualified ATP.Util.Print as PP
> import qualified Control.Monad as M
> import qualified Data.Map as Map
> import Data.Map(Map)
> import qualified Test.QuickCheck as Q
> import Test.QuickCheck (Gen, Property)

* Propositions

> class Apply a where
>   apply :: Map Rel Formula -> a -> a

> instance Apply Formula where
>   apply env = F.onatoms (\p -> case Map.lookup p env of 
>                                  Just p' -> p'
>                                  Nothing -> Atom p)

Evaluate a formula in a mapping of variables to truth values.

> eval :: Formula -> (Rel -> Bool) -> Bool
> eval fm v = case fm of
>   [$form| ⊤ |] -> True
>   [$form| ⊥ |] -> False
>   [$form| ^a |] -> v a
>   [$form| ¬ $p |] -> not (eval p v)
>   [$form| $p ∧ $q |] -> eval p v && eval q v
>   [$form| $p ∨ $q |] -> eval p v || eval q v
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
>  where
>   truthtableDoc fm' =
>     let pvs = atoms fm' 
>         width = foldr (max . length . show) 5 pvs + 1 
>         fixw s = s ++ replicate (width - length s) ' ' 
>         truthstring p = fixw (if p then "⊤" else "⊥") 
>         separator = replicate (width * length pvs + 9) '-' 
>         row v =
>             let lis = map (truthstring . v) pvs 
>                 ans = truthstring(eval fm' v) in
>                 [lis ++ [ans]]
>         rows = onallvaluations row (++) (const False) pvs
>         rowStr r = let (lis, ans) = splitAt (length r - 1) r in
>                        (foldr (++) ("| " ++ head ans) lis)
>     in PP.vcat [ PP.text (foldr (\s t -> fixw(show s) ++ t) "| formula" pvs) 
>                , PP.empty 
>                , PP.text separator
>                , PP.empty 
>                , PP.vcat (map (PP.text . rowStr) rows) 
>                , PP.text separator
>                ]

Tautologies

> tautology :: Formula -> Bool
> tautology fm = onallvaluations (eval fm) (&&) (const False) (atoms fm)

Satisfiability

> unsatisfiable :: Formula -> Bool
> unsatisfiable = tautology . Not 

> satisfiable :: Formula -> Bool
> satisfiable = not . unsatisfiable 

Duality

> dual :: Formula -> Formula 
> dual fm = case fm of
>   [$form| ⊥ |] -> (⊤)
>   [$form| ⊤ |] -> (⊥)
>   [$form| ^_ |] -> fm
>   [$form| ¬ $p |] -> (¬) $ dual p
>   [$form| $p ∧ $q |] -> p' ∨ q'
>     where p' = dual p
>           q' = dual q
>   [$form| $p ∨ $q |] -> p' ∧ q'
>     where p' = dual p
>           q' = dual q
>   _ -> error "Formula involves connectives ⊃ and ⇔"

Simplification

> simplify :: Formula -> Formula
> simplify fm = case fm of
>   [$form| ¬ $p |] -> simplify1 $ (¬) p'
>     where p' = simplify p
>   [$form| $p ∧ $q |] -> simplify1 $ p' ∧ q'
>     where p' = simplify p
>           q' = simplify q
>   [$form| $p ∨ $q |] -> simplify1 $ p' ∨ q' 
>     where p' = simplify p
>           q' = simplify q
>   [$form| $p ⊃ $q |] -> simplify1 $ p' ⊃ q'
>     where p' = simplify p
>           q' = simplify q
>   [$form| $p ⇔ $q |] -> simplify1 $ p' ⇔ q' 
>     where p' = simplify p
>           q' = simplify q
>   _ -> fm

The order of the following clauses makes a big difference.

> simplify1 :: Formula -> Formula
> simplify1 fm = case fm of
>   [$form| ¬ ⊥ |] -> (⊤)
>   [$form| ¬ ⊤ |] -> (⊥)
>   [$form| ¬ ¬ $p |] -> p
>   [$form| ⊥ ∧ _ |] -> (⊥)
>   [$form| _ ∧ ⊥ |] -> (⊥)
>   [$form| ⊤ ∧ $q |] -> q
>   [$form| $p ∧ ⊤ |] -> p
>   [$form| ⊥ ∨ $q |] -> q
>   [$form| $p ∨ ⊥ |] -> p
>   [$form| ⊤ ∨ _ |] -> (⊤)
>   [$form| _ ∨ ⊤ |] -> (⊤)
>   [$form| ⊥ ⊃ _ |] -> (⊤)
>   [$form| _ ⊃ ⊤ |] ->  (⊤)
>   [$form| ⊤ ⊃ $q |] -> q
>   [$form| $p ⊃ ⊥ |] -> (¬) p
>   [$form| ⊤ ⇔ $q |] -> q
>   [$form| $p ⇔ ⊤ |] -> p
>   [$form| ⊥ ⇔ ⊥ |] -> (⊤)
>   [$form| ⊥ ⇔ $q |] -> (¬) q
>   [$form| $p ⇔ ⊥ |] -> (¬) p
>   _ -> fm

Negation normal form

> nnf :: Formula -> Formula
> nnf = nnf' . simplify

> nnf' :: Formula -> Formula
> nnf' fm = case fm of 
>   [$form| $p ∧ $q |] -> p' ∧ q'
>     where p' = nnf' p 
>           q' = nnf' q
>   [$form| $p ∨ $q |] -> p' ∨ q'
>     where p' = nnf' p 
>           q' = nnf' q
>   [$form| $p ⊃ $q |] -> np' ∨ q'
>     where np' = nnf' $ (¬) p
>           q' = nnf' q
>   [$form| $p ⇔ $q |] -> p' ∧ q' ∨ p'' ∧ q''
>     where p' = nnf' p
>           q' = nnf' q
>           p'' = nnf' $ (¬) p
>           q'' = nnf' $ (¬) q
>   [$form| ¬ ¬ $p |] -> nnf' p
>   [$form| ¬ ($p ∧ $q) |] -> p' ∨ q'
>     where p' = nnf' $ (¬) p
>           q' = nnf' $ (¬) q 
>   [$form| ¬ ($p ∨ $q) |] -> p' ∧ q'
>     where p' = nnf' $ (¬) p
>           q' = nnf' $ (¬) q
>   [$form| ¬ ($p ⊃ $q) |] -> p' ∧ q'
>     where p' = nnf' p
>           q' = nnf' $ (¬) q
>   [$form| ¬ ($p ⇔ $q) |] -> p' ∧ q'' ∨ p'' ∧ q' 
>     where p' = nnf' p
>           q' = nnf' q
>           p'' = nnf' $ (¬) p
>           q'' = nnf' $ (¬) q
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
> distrib = List.allPairs Set.union 

Subsumption

> subsume :: [[Formula]] -> [[Formula]]
> subsume cls =
>   filter (\cl -> not(any (\cl' -> Set.psubset cl' cl) cls)) cls

Disjunctive normal form

> dnf :: Formula -> Formula 
> dnf f = --trace' "dnf: in" (pPrint f) $ 
>   let f' = (F.listDisj . map F.listConj . simpdnf) f in
>   --trace' "dnf: out" (pPrint f') $ f'
>   f'

> simpdnf :: Formula -> [[Formula]]
> simpdnf Bot = []
> simpdnf Top = [[]]
> simpdnf fm = (subsume . filter (not.trivial) . purednf . nnf) fm

> purednf :: Formula -> [[Formula]]
> purednf fm = case fm of
>   And p q -> distrib (purednf p) (purednf q)
>   Or p q -> purednf p ∪ purednf q
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

* Tests

A small number of propositional variables

> props :: Int -> Gen Rel
> props n = fmap (\i -> R ("p" ++ show i) []) $ Q.choose (0, n)

Formulas with a maximum size.

> forms :: Int -> Gen Formula
> forms 0 = Q.oneof [ fmap Atom (props 10), return Top, return Bot ]
> forms n 
>  | n > 0 = Q.oneof [ forms (n-1)
>                    , M.liftM Not fms
>                    , M.liftM2 And fms fms 
>                    , M.liftM2 Or fms fms 
>                    , M.liftM2 Imp fms fms 
>                    , M.liftM2 Iff fms fms 
>                    ]
>  | otherwise = error "Impossible" 
>  where fms = forms $ n - 1

> prop_nnf_correct :: Property
> prop_nnf_correct = Q.label "nnf_correct" $
>   Q.forAll (forms 5) $ \f -> tautology (f ⇔ nnf f)

> prop_cnf_correct :: Property
> prop_cnf_correct = Q.label "cnf_correct" $
>   Q.forAll (forms 5) $ \f -> tautology (f ⇔ cnf f)

> prop_dnf_correct :: Property
> prop_dnf_correct = Q.label "dnf_correct" $
>   Q.forAll (forms 5) $ \f -> tautology (f ⇔ dnf f)

> tests :: IO ()
> tests = do 
>   Q.quickCheck prop_nnf_correct
>   Q.quickCheck prop_cnf_correct
>   Q.quickCheck prop_dnf_correct
