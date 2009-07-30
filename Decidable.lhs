
> module Decidable ( aedecide
>                  , allPossibleSyllogisms
>                  , allValidSyllogisms
>                  , allPossibleSyllogisms'
>                  , allValidSyllogisms'
>                  , premiss_A
>                  , premiss_E
>                  , premiss_I
>                  , premiss_O
>                  , anglicizePremiss
>                  , anglicizeSyllogism
>                  , miniscope
>                  , wang
>                  , decideFinite
>                  , decideFmp
>                  , decideMonadic
>                  )
>   where

> import Prelude 
> import qualified Lib
> import qualified List
> import qualified ListSet
> import qualified Data.Map as Map
> import qualified Formulas as F
> import Formulas(Formula(..), Var, Sym)
> import qualified Prop
> import qualified Fol
> import Fol(Fol(R), Term(..), Env)
> import qualified Herbrand
> import qualified Dp
> import qualified Skolem
> import qualified Meson

> aedecide :: Formula Fol -> Bool
> aedecide fm = 
>   let sfm = Skolem.skolemize (Not fm)
>       fvs = Fol.fv sfm
>       (cnsts, funcs) = List.partition (\(_, ar) -> ar == 0) (Fol.functions sfm) in
>   if funcs /= [] then error "Not in AE fragment" else
>   let consts = if cnsts == [] then [("c", 0)] else cnsts
>       cntms = map (\(c, _) -> Fn c []) consts
>       alltuples = Herbrand.groundtuples cntms [] 0 (length fvs)
>       cjs = Prop.simpcnf sfm
>       grounds = map (\tup -> ListSet.image  
>                                (ListSet.image (Fol.apply (Map.fromList $ zip fvs tup)))
>                                cjs) alltuples in
>   not $ Dp.dpll $ ListSet.unions grounds

> separate :: Var -> [Formula Fol] -> Formula Fol
> separate x cjs = 
>   let (yes, no) = List.partition (elem x . Fol.fv) cjs in
>   if yes == [] then F.listConj no
>   else if no == [] then Exists x (F.listConj yes)
>   else And (Exists x (F.listConj yes)) (F.listConj no)

> pushquant :: Var -> Formula Fol -> Formula Fol
> pushquant x p = 
>   if not (List.elem x (Fol.fv p)) then p else
>   let djs = Prop.purednf (Prop.nnf p) in
>   F.listDisj (map (separate x) djs)

> miniscope :: Formula Fol -> Formula Fol
> miniscope fm = case fm of
>   Not p -> Not(miniscope p)
>   And p q -> And (miniscope p) (miniscope q)
>   Or p q -> Or (miniscope p) (miniscope q) 
>   Forall x p -> Not (pushquant x (Not (miniscope p)))
>   Exists x p -> pushquant x (miniscope p)
>   _ -> fm

> wang :: Formula Fol -> Bool
> wang = aedecide . miniscope . Prop.nnf . Prop.simplify

> atom :: Sym -> Var -> Formula Fol
> atom p x = Atom (R p [Var x])

> premiss_A :: (Sym, Sym) -> Formula Fol 
> premiss_A (p, q) = Forall "x" (Imp (atom p "x") (atom q "x"))

> premiss_E :: (Sym, Sym) -> Formula Fol 
> premiss_E (p, q) = Forall "x" (Imp (atom p "x") (Not (atom q "x")))

> premiss_I :: (Sym, Sym) -> Formula Fol 
> premiss_I (p, q) = Exists "x" (And (atom p "x") (atom q "x"))

> premiss_O :: (Sym, Sym) -> Formula Fol 
> premiss_O (p, q) = Exists "x" (And (atom p "x") (Not (atom q "x")))

> anglicizePremiss :: Formula Fol -> String
> anglicizePremiss fm = 
>   case fm of 
>    Forall _ (Imp (Atom(R p _)) (Atom(R q _))) -> "all " ++ p ++ " are " ++ q
>    Forall _ (Imp (Atom(R p _)) (Not(Atom(R q _)))) -> "no " ++ p ++ " are " ++ q
>    Exists _ (And (Atom(R p _)) (Atom(R q _))) -> "some " ++ p ++ " are " ++ q
>    Exists _ (And (Atom(R p _)) (Not(Atom(R q _)))) -> "some " ++ p ++ " are not " ++ q
>    _ -> error "Impossible" 

> anglicizeSyllogism :: Formula Fol -> String
> anglicizeSyllogism (Imp (And t1 t2) t3) =
>  "If " ++ anglicizePremiss t1 ++ " and " ++ anglicizePremiss t2 ++
>  ", then " ++ anglicizePremiss t3
> anglicizeSyllogism _ = error "Impossible" 

> allPossibleSyllogisms :: [Formula Fol]
> allPossibleSyllogisms =
>  let sylltypes = [premiss_A, premiss_E, premiss_I, premiss_O] 
>      prems1 = Lib.allPairs id sylltypes [("M","P"), ("P","M")]
>      prems2 = Lib.allPairs id sylltypes [("S","M"), ("M","S")]
>      prems3 = Lib.allPairs id sylltypes [("S","P")] in
>  Lib.allPairs Imp (Lib.allPairs And prems1 prems2) prems3

> allValidSyllogisms :: [Formula Fol]
> allValidSyllogisms = List.filter aedecide allPossibleSyllogisms

> allPossibleSyllogisms' :: [Formula Fol]
> allPossibleSyllogisms' =
>  let p = Fol.parse "<<(exists x. P(x)) /\\ (exists x. M(x)) /\\ (exists x. S(x))>>" in
>  map (Imp p) allPossibleSyllogisms

> allValidSyllogisms' :: [Formula Fol]
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

> decideFinite :: Int -> Formula Fol -> Bool
> decideFinite n fm =
>   let funcs = Fol.functions fm
>       preds = Fol.predicates fm
>       dom = [1 .. n]
>       fints = alldepmappings funcs (allfunctions dom)
>       pints = alldepmappings preds (allpredicates dom)
>       interps = Lib.allPairs (\f p -> (dom, f, p)) fints pints
>       fm' = Fol.generalize fm in
>   List.all (\md -> Fol.holds md Map.empty fm') interps

> limmeson :: Int -> Formula Fol -> Maybe (Env, Int, Int)
> limmeson n fm = 
>   let cls = Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm
>       rules = List.concat (map Meson.contrapositives cls) in
>   Meson.mexpand rules [] Bot Just (Map.empty, n, 0)

> limitedMeson :: Int -> Formula Fol -> Maybe [(Env, Int, Int)]
> limitedMeson n fm =
>   let fm1 = Skolem.askolemize(Not(Fol.generalize fm)) in
>   mapM (limmeson n . F.listConj) (Prop.simpdnf fm1)

> decideFmp :: Formula Fol -> Bool
> decideFmp fm =
>   let test n = case limitedMeson n fm of
>                  Just _ -> True
>                  Nothing -> if decideFinite n fm then test (n+1) else False in
>   test 1

> decideMonadic :: Formula Fol -> Bool
> decideMonadic fm =
>   let funcs = Fol.functions fm 
>       preds = Fol.predicates fm 
>       (monadic, other) = List.partition (\(_, ar) -> ar == 1) preds in
>   if funcs /= [] || List.any (\(_, ar) -> ar > 1) other 
>   then error "Not in the monadic subset" else
>   let n = 2 `Lib.pow` (length monadic) in
>   decideFinite n fm

