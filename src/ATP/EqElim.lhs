
> module EqElim ( replace
>               , modifyS
>               , modifyT
>               , modifyE
>               , brand
>               , bmeson
>               ) 
>   where

> import Prelude 
> import qualified Maybe
> import qualified List
> import qualified Lib
> import Formulas(Clause, Clauses, Formula(..), Vars)
> import qualified Formulas
> import qualified Equal
> import ListSet( (\\) )
> import qualified ListSet 
> import Fol(Fol(R), Term(..))
> import qualified Fol
> import Data.Map(Map)
> import qualified Data.Map as Map
> import qualified Prop
> import qualified Skolem
> import qualified Tableaux
> import qualified Meson


> modifyS :: Clause Fol -> Clauses Fol
> modifyS cl = case List.find Equal.isEq cl of
>                Nothing -> [cl]
>                Just eq1 -> 
>                  let (s, t) = Equal.destEq eq1 
>                      eq2 = Equal.mkEq t s
>                      sub = modifyS (cl \\ [eq1]) in
>                  map (ListSet.insert eq1) sub ++ map (ListSet.insert eq2) sub

> modifyT :: Clause Fol -> Clause Fol
> modifyT [] = []
> modifyT (p:ps) = if Equal.isEq p then
>                    let (s, t) = Equal.destEq p 
>                        ps' = modifyT ps
>                        w = Var (Fol.variant "w" (Fol.fv (p:ps'))) in
>                    Not(Equal.mkEq t w) : Equal.mkEq s w : ps'
>                  else p : modifyT ps

> findNestNonvar :: Term -> Maybe Term
> findNestNonvar (Var _) = Nothing 
> findNestNonvar (Fn _ args) = List.find (not . Fol.isVar) args

> findNvSubterm :: Formula Fol -> Maybe Term
> findNvSubterm (Not p) = findNvSubterm p
> findNvSubterm (Atom (R "=" st)) = Lib.findApply findNestNonvar st
> findNvSubterm (Atom (R _ args)) = List.find (not . Fol.isVar) args
> findNvSubterm _ = error "Impossible" 

> replacet :: Map Term Term -> Term -> Term
> replacet rfn tm = case Map.lookup tm rfn of
>                     Just tm' -> tm'
>                     Nothing -> case tm of
>                                  Var _ -> tm
>                                  Fn f args -> Fn f (map (replacet rfn) args)

> replace :: Map Term Term -> Formula Fol -> Formula Fol
> replace rfn = Fol.onformula (replacet rfn)

> emodify :: Vars -> Clause Fol -> Clause Fol
> emodify fvs cls = 
>   case Lib.findApply findNvSubterm cls of
>     Nothing -> cls
>     Just t -> let w = Fol.variant "w" fvs 
>                   cls' = map (replace (Map.singleton t (Var w))) cls in
>               emodify (w : fvs) (Not(Equal.mkEq t (Var w)) : cls')

> modifyE :: Clause Fol -> Clause Fol
> modifyE cls = emodify (Fol.fv cls) cls

> brand :: Clauses Fol -> Clauses Fol
> brand cls = 
>   let cls1 = map modifyE cls
>       cls2 = ListSet.unions (map modifyS cls1) in
>   [Equal.mkEq (Var "x") (Var "x")] : map modifyT cls2

> bpuremeson :: Formula Fol -> IO Int
> bpuremeson fm = 
>   let cls = brand(Prop.simpcnf (Skolem.specialize (Skolem.pnf fm)))
>       rules = List.concat (map Meson.contrapositives cls) in
>   Tableaux.deepen (\n -> do Meson.mexpand rules [] Bot Just (Map.empty, n, 0)
>                             return n) 0

> bmeson :: Formula Fol -> IO [Int]
> bmeson fm = 
>   let fm1 = Skolem.askolemize (Not (Fol.generalize fm)) in
>   mapM (bpuremeson . Formulas.listConj) (Prop.simpdnf fm1)
