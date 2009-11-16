
* Signature

> module ATP.Paramodulation
>   ( paramodulation )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude
> import qualified ATP.Completion as Completion
> import qualified ATP.Equal as Equal
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Prop as Prop
> import qualified ATP.Resolution as Resolution
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))
> import qualified ATP.Util.Log as Log
> import ATP.Util.Log(Log)
> import qualified Data.List as List

* Paramodulation

> overlap1 :: (Term, Term) -> Formula -> (Env -> Formula -> a) -> [a]
> overlap1 lr fm rfn =
>   case fm of
>     Atom (R f args) -> Completion.listcases (Completion.overlaps lr)
>                        (\i a -> rfn i (Atom (R f a))) args []
>     Not p -> overlap1 lr p (\i p' -> rfn i (Not p'))
>     _ -> __IMPOSSIBLE__ 

> overlapc :: (Term, Term) -> Clause -> (Env -> Clause -> a) 
>             -> [a] -> [a]
> overlapc lr cl rfn acc = Completion.listcases (overlap1 lr) rfn cl acc     

> paramodulate :: Clause -> Clause -> Clauses
> paramodulate pcl ocl =
>   foldr (\eq -> let pcl' = pcl \\ [eq]
>                     (l, r) = Equal.destEq eq
>                     rfn i ocl' = Set.image (Fol.apply i) (pcl' ++ ocl') in
>                 overlapc (l, r) ocl rfn . overlapc (r, l) ocl rfn)
>          [] (List.filter Equal.isEq pcl)

> paraClauses :: Clause -> Clause -> Clauses
> paraClauses cls1 cls2 = 
>   let cls1' = Resolution.rename "x" cls1
>       cls2' = Resolution.rename "y" cls2 in
>   paramodulate cls1' cls2' ++ paramodulate cls2' cls1'

> paraloop :: Log m => ([Clause], [Clause]) -> m Bool
> paraloop (_, []) = error "No proof found"
> paraloop (used, unused@(cls:ros)) = 
>   do Log.putStrLn (show (length used) ++ " used; " ++ show (length unused) ++ " unused.")
>      let used' = Set.insert cls used
>          news = List.concat (map (Resolution.resolveClauses cls) used')
>                 ++ List.concat (map (paraClauses cls) used') in
>        if elem [] news then return True
>        else paraloop(used', foldr (Resolution.incorporate cls) ros news) 

> pureParamodulation :: Log m => Formula -> m Bool
> pureParamodulation fm = 
>   paraloop ([], [Equal.mkEq (Var "x") (Var "x")] :
>             Prop.simpcnf(Skolem.specialize(Skolem.pnf fm)))

> paramodulation :: Log m => Formula -> m [Bool]
> paramodulation fm = 
>   let fm1 = Skolem.askolemize $ Not $ Fol.generalize fm in
>   mapM (pureParamodulation . F.listConj) (Prop.simpdnf fm1)
