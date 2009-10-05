
* Signature

> module ATP.Paramodulation
>   ( paramodulation )
> where

* Imports

> import Prelude 
> import qualified System.IO.UTF8 as S
> import qualified Data.List as List

> import qualified ATP.Completion as Completion
> import qualified ATP.Prop as Prop
> import qualified ATP.Skolem as Skolem
> import ATP.FormulaSyn
> import qualified ATP.Formula as F
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))
> import qualified ATP.Equal as Equal
> import qualified ATP.FOL as FOL
> import qualified ATP.Resolution as Resolution

* Paramodulation

> overlap1 :: (Term, Term) -> Formula -> (Env -> Formula -> a) -> [a]
> overlap1 lr fm rfn =
>   case fm of
>     Atom (R f args) -> Completion.listcases (Completion.overlaps lr)
>                        (\i a -> rfn i (Atom (R f a))) args []
>     Not p -> overlap1 lr p (\i p -> rfn i (Not p))
>     _ -> error "Impossible" 

> overlapc :: (Term, Term) -> Clause -> (Env -> Clause -> a) 
>             -> [a] -> [a]
> overlapc lr cl rfn acc = Completion.listcases (overlap1 lr) rfn cl acc     

> paramodulate :: Clause -> Clause -> Clauses
> paramodulate pcl ocl =
>   foldr (\eq -> let pcl' = pcl \\ [eq]
>                     (l, r) = Equal.destEq eq
>                     rfn i ocl' = Set.image (FOL.apply i) (pcl' ++ ocl') in
>                 overlapc (l, r) ocl rfn . overlapc (r, l) ocl rfn)
>          [] (List.filter Equal.isEq pcl)

> paraClauses :: Clause -> Clause -> Clauses
> paraClauses cls1 cls2 = 
>   let cls1' = Resolution.rename "x" cls1
>       cls2' = Resolution.rename "y" cls2 in
>   paramodulate cls1' cls2' ++ paramodulate cls2' cls1'

> paraloop :: ([Clause], [Clause]) -> IO Bool
> paraloop (_, []) = error "No proof found"
> paraloop (used, unused@(cls:ros)) = 
>   do S.putStrLn (show (length used) ++ " used; " ++ show (length unused) ++ " unused.\n")
>      let used' = Set.insert cls used
>          news = List.concat (map (Resolution.resolveClauses cls) used')
>                 ++ List.concat (map (paraClauses cls) used') in
>        if elem [] news then return True
>        else paraloop(used', foldr (Resolution.incorporate cls) ros news) 

> pureParamodulation :: Formula -> IO Bool
> pureParamodulation fm = 
>   paraloop ([], [Equal.mkEq (Var "x") (Var "x")] :
>             Prop.simpcnf(Skolem.specialize(Skolem.pnf fm)))

> paramodulation :: Formula -> IO [Bool]
> paramodulation fm = 
>   let fm1 = Skolem.askolemize(Not(FOL.generalize fm)) in
>   mapM (pureParamodulation . F.listConj) (Prop.simpdnf fm1)
