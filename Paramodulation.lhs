
> module Paramodulation ( paramodulation
>                       )
>   where

> import Prelude 
> import qualified List
> import qualified Text.Printf as T
> import qualified Completion
> import qualified Prop
> import qualified Skolem
> import Fol(Fol(R), Term(..), Env)
> import Formulas(Formula(..), Clause, Clauses)
> import qualified Formulas
> import ListSet( (\\) )
> import qualified ListSet
> import qualified Equal
> import qualified Fol
> import qualified Resolution

> overlap1 :: (Term, Term) -> Formula Fol -> (Env -> Formula Fol -> a) -> [a]
> overlap1 lr fm rfn =
>   case fm of
>     Atom (R f args) -> Completion.listcases (Completion.overlaps lr)
>                        (\i a -> rfn i (Atom (R f a))) args []
>     Not p -> overlap1 lr p (\i p -> rfn i (Not p))
>     _ -> error "Impossible" 

> overlapc :: (Term, Term) -> Clause Fol -> (Env -> Clause Fol -> a) 
>             -> [a] -> [a]
> overlapc lr cl rfn acc = Completion.listcases (overlap1 lr) rfn cl acc     

> paramodulate :: Clause Fol -> Clause Fol -> Clauses Fol
> paramodulate pcl ocl =
>   foldr (\eq -> let pcl' = pcl \\ [eq]
>                     (l, r) = Equal.destEq eq
>                     rfn i ocl' = ListSet.image (Fol.apply i) (pcl' ++ ocl') in
>                 overlapc (l, r) ocl rfn . overlapc (r, l) ocl rfn)
>          [] (List.filter Equal.isEq pcl)

> paraClauses :: Clause Fol -> Clause Fol -> Clauses Fol
> paraClauses cls1 cls2 = 
>   let cls1' = Resolution.rename "x" cls1
>       cls2' = Resolution.rename "y" cls2 in
>   paramodulate cls1' cls2' ++ paramodulate cls2' cls1'

> paraloop :: ([Clause Fol], [Clause Fol]) -> IO Bool
> paraloop (_, []) = error "No proof found"
> paraloop (used, unused@(cls:ros)) = 
>   do T.printf (show (length used) ++ " used; " ++ show (length unused) ++ " unused.\n")
>      let used' = ListSet.insert cls used
>          news = List.concat (map (Resolution.resolveClauses cls) used')
>                 ++ List.concat (map (paraClauses cls) used') in
>        if elem [] news then return True
>        else paraloop(used', foldr (Resolution.incorporate cls) ros news) 

> pureParamodulation :: Formula Fol -> IO Bool
> pureParamodulation fm = 
>   paraloop ([], [Equal.mkEq (Var "x") (Var "x")] :
>             Prop.simpcnf(Skolem.specialize(Skolem.pnf fm)))

> paramodulation :: Formula Fol -> IO [Bool]
> paramodulation fm = 
>   let fm1 = Skolem.askolemize(Not(Fol.generalize fm)) in
>   mapM (pureParamodulation . Formulas.listConj) (Prop.simpdnf fm1)
