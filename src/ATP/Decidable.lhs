
* Signature

> module ATP.Decidable
>   ( aedecide
>   , allPossibleSyllogisms
>   , allValidSyllogisms
>   , allPossibleSyllogisms'
>   , allValidSyllogisms'
>   , premiss_A
>   , premiss_E
>   , premiss_I
>   , premiss_O
>   , anglicizePremiss
>   , anglicizeSyllogism
>   , miniscope
>   , wang
>   , decideFinite
>   , decideFmp
>   , decideMonadic
>   )
> where

* Imports

> import ATP.Util.Prelude 
> import qualified ATP.DP as DP
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.FOL as FOL
> import qualified ATP.Herbrand as Herbrand
> import qualified ATP.Meson as Meson
> import qualified ATP.Prop as Prop
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.ListSet as Set
> import qualified Data.List as List
> import qualified Data.Map as Map

* Decidable Problems

> aedecide :: Formula -> Bool
> aedecide fm = 
>   let sfm = Skolem.skolemize (Not fm)
>       fvs = FOL.fv sfm
>       (cnsts, funcs) = List.partition (\(_, ar) -> ar == 0) (FOL.functions sfm) in
>   if funcs /= [] then error "Not in AE fragment" else
>   let consts = if cnsts == [] then [("c", 0)] else cnsts
>       cntms = map (\(c, _) -> Fn c []) consts
>       alltups = Herbrand.groundtuples cntms [] 0 (length fvs)
>       cjs = Prop.simpcnf sfm
>       grounds = map (\tup -> Set.image  
>                                (Set.image (FOL.apply (Map.fromList $ zip fvs tup)))
>                                cjs) alltups in
>   not $ DP.dpll $ Set.unions grounds

> separate :: Var -> [Formula] -> Formula
> separate x cjs = 
>   let (yes, no) = List.partition (elem x . FOL.fv) cjs in
>   if yes == [] then F.listConj no
>   else if no == [] then Ex x (F.listConj yes)
>   else And (Ex x (F.listConj yes)) (F.listConj no)

> pushquant :: Var -> Formula -> Formula
> pushquant x p = 
>   if not (List.elem x (FOL.fv p)) then p else
>   let djs = Prop.purednf (Prop.nnf p) in
>   F.listDisj (map (separate x) djs)

> miniscope :: Formula -> Formula
> miniscope fm = case fm of
>   Not p -> Not(miniscope p)
>   And p q -> And (miniscope p) (miniscope q)
>   Or p q -> Or (miniscope p) (miniscope q) 
>   All x p -> Not (pushquant x (Not (miniscope p)))
>   Ex x p -> pushquant x (miniscope p)
>   _ -> fm

> wang :: Formula -> Bool
> wang = aedecide . miniscope . Prop.nnf . Prop.simplify

> atom :: Pred -> Var -> Formula
> atom p x = Atom (R p [Var x])

> premiss_A :: (Pred, Pred) -> Formula 
> premiss_A (p, q) = All "x" (Imp (atom p "x") (atom q "x"))

> premiss_E :: (Pred, Pred) -> Formula 
> premiss_E (p, q) = All "x" (Imp (atom p "x") (Not (atom q "x")))

> premiss_I :: (Pred, Pred) -> Formula 
> premiss_I (p, q) = Ex "x" (And (atom p "x") (atom q "x"))

> premiss_O :: (Pred, Pred) -> Formula 
> premiss_O (p, q) = Ex "x" (And (atom p "x") (Not (atom q "x")))

> anglicizePremiss :: Formula -> String
> anglicizePremiss fm = 
>   case fm of 
>    All _ (Imp (Atom(R p _)) (Atom(R q _))) -> "all " ++ p ++ " are " ++ q
>    All _ (Imp (Atom(R p _)) (Not(Atom(R q _)))) -> "no " ++ p ++ " are " ++ q
>    Ex _ (And (Atom(R p _)) (Atom(R q _))) -> "some " ++ p ++ " are " ++ q
>    Ex _ (And (Atom(R p _)) (Not(Atom(R q _)))) -> "some " ++ p ++ " are not " ++ q
>    _ -> error "Impossible" 

> anglicizeSyllogism :: Formula -> String
> anglicizeSyllogism (Imp (And t1 t2) t3) =
>  "If " ++ anglicizePremiss t1 ++ " and " ++ anglicizePremiss t2 ++
>  ", then " ++ anglicizePremiss t3
> anglicizeSyllogism _ = error "Impossible" 

> allPossibleSyllogisms :: [Formula]
> allPossibleSyllogisms =
>  let sylltypes = [premiss_A, premiss_E, premiss_I, premiss_O] 
>      prems1 = Lib.allPairs id sylltypes [("M","P"), ("P","M")]
>      prems2 = Lib.allPairs id sylltypes [("S","M"), ("M","S")]
>      prems3 = Lib.allPairs id sylltypes [("S","P")] in
>  Lib.allPairs Imp (Lib.allPairs And prems1 prems2) prems3

> allValidSyllogisms :: [Formula]
> allValidSyllogisms = List.filter aedecide allPossibleSyllogisms

> allPossibleSyllogisms' :: [Formula]
> allPossibleSyllogisms' =
>  let p = [$form| (∃ x. P(x)) ∧ (∃ x. M(x)) ∧ (∃ x. S(x)) |] in
>  map (Imp p) allPossibleSyllogisms

> allValidSyllogisms' :: [Formula]
> allValidSyllogisms' = List.filter aedecide allPossibleSyllogisms'

> alltuples :: Int -> [a] -> [[a]]
> alltuples n l = 
>   if n == 0 then [[]] else
>   let tups = alltuples (n-1) l in
>   Lib.allPairs (:) l tups

> valmod :: Eq a => a -> b -> (a -> b) -> a -> b
> valmod a y f x = if x == a then y else f x

> undef :: a -> b
> undef _ = error "Undefined"

> allmappings :: Eq a => [a] -> [b] -> [a -> b]
> allmappings dom ran = foldr (\p -> Lib.allPairs (valmod p) ran) [undef] dom

> alldepmappings :: Eq a => [(a, b)] -> (b -> [c]) -> [a -> c]
> alldepmappings dom ran =
>   foldr (\(p,n) -> Lib.allPairs (valmod p) (ran n)) [undef] dom

> allfunctions :: Eq a => [a] -> Int -> [[a] -> a]
> allfunctions dom n = allmappings (alltuples n dom) dom

> allpredicates :: Eq a =>  [a] -> Int -> [[a] -> Bool]
> allpredicates dom n = allmappings (alltuples n dom) [False, True]

> decideFinite :: Int -> Formula -> Bool
> decideFinite n fm =
>   let funcs = FOL.functions fm
>       preds = FOL.predicates fm
>       dom = [1 .. n]
>       fints = alldepmappings funcs (allfunctions dom)
>       pints = alldepmappings preds (allpredicates dom)
>       interps = Lib.allPairs (\f p -> (dom, f, p)) fints pints
>       fm' = FOL.generalize fm in
>   List.all (\md -> FOL.holds md Map.empty fm') interps

> limmeson :: Int -> Formula -> Maybe (Env, Int, Int)
> limmeson n fm = 
>   let cls = Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm
>       rules = List.concat (map Meson.contrapositives cls) in
>   Meson.mexpand rules [] Bot Just (Map.empty, n, 0)

> limitedMeson :: Int -> Formula -> Maybe [(Env, Int, Int)]
> limitedMeson n fm =
>   let fm1 = Skolem.askolemize(Not(FOL.generalize fm)) in
>   mapM (limmeson n . F.listConj) (Prop.simpdnf fm1)

> decideFmp :: Formula -> Bool
> decideFmp fm =
>   let test n = case limitedMeson n fm of
>                  Just _ -> True
>                  Nothing -> if decideFinite n fm then test (n+1) else False in
>   test 1

> decideMonadic :: Formula -> Bool
> decideMonadic fm =
>   let funcs = FOL.functions fm 
>       preds = FOL.predicates fm 
>       (monadic, other) = List.partition (\(_, ar) -> ar == 1) preds in
>   if funcs /= [] || List.any (\(_, ar) -> ar > 1) other 
>   then error "Not in the monadic subset" else
>   let n = 2 `Lib.pow` (length monadic) in
>   decideFinite n fm

