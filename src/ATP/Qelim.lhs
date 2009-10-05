
> module Qelim ( cnnf
>              , liftQelim
>              , qelimDLO 
>              )
>   where

> import Prelude 
> import qualified Lib
> import Lib((|=>))
> import qualified List
> import qualified ListSet
> import ListSet( (\\) )
> import qualified Formulas as F
> import Formulas(Formula(..), Var, Vars)
> import qualified Fol
> import Fol(Fol(R), Term(..))
> import qualified Skolem
> import qualified Decidable
> import qualified Equal
> import qualified Prop

> qelim :: (Formula Fol -> Formula Fol) -> Var -> Formula Fol -> Formula Fol 
> qelim bfn x p = 
>   let cjs = F.conjuncts p 
>       (ycjs, ncjs) = List.partition (List.elem x . Fol.fv) cjs in
>   if ycjs == [] then p else
>   let q = bfn (Exists x (F.listConj ycjs)) in
>   foldr And q ncjs

> liftQelim :: (Vars -> Formula Fol -> Formula Fol) 
>               -> (Formula Fol -> Formula Fol) 
>               -> (Vars -> Formula Fol -> Formula Fol) 
>               -> Formula Fol -> Formula Fol 
> liftQelim afn nfn qfn fm = Skolem.simplify (qelift (Fol.fv fm) (Decidable.miniscope fm))
>   where qelift vars fm = 
>           case fm of
>             Atom _ -> afn vars fm
>             Not p -> Not $ qelift vars p
>             And p q -> And (qelift vars p) (qelift vars q)
>             Or p q -> Or (qelift vars p) (qelift vars q)
>             Imp p q -> Imp (qelift vars p) (qelift vars q)
>             Iff p q -> Iff (qelift vars p) (qelift vars q)
>             Forall x p -> Not (qelift vars (Exists x (Not p)))
>             Exists x p -> let djs = F.disjuncts $ nfn $ qelift (x:vars) p in
>                           F.listDisj (map (qelim (qfn vars) x) djs)
>             _ -> fm 

> cnnf :: (Formula Fol -> Formula Fol) -> Formula Fol -> Formula Fol 
> cnnf lfn = Skolem.simplify . cnnf' . Skolem.simplify
>   where cnnf' (And p q) = And (cnnf' p) (cnnf' q)
>         cnnf' (Or p q) = Or (cnnf' p) (cnnf' q)
>         cnnf' (Imp p q) = Or (cnnf' (Not p)) (cnnf' q)
>         cnnf' (Iff p q) = Or (And (cnnf' p) (cnnf' q)) (And (cnnf' (Not p)) (cnnf' (Not q))) 
>         cnnf' (Not (Not p)) = cnnf' p              
>         cnnf' (Not (And p q)) = Or (cnnf' (Not p)) (cnnf' (Not q))
>         cnnf' (Not (Or (And p q) (And p' r))) | p' == F.opp p =
>           Or (cnnf' (And p (Not q))) (cnnf' (And p' (Not r)))
>         cnnf' (Not (Or p q)) = And (cnnf' (Not p)) (cnnf' (Not q))
>         cnnf' (Not (Imp p q)) = And (cnnf' p) (cnnf' (Not q))
>         cnnf' (Not (Iff p q)) = Or (And (cnnf' p) (cnnf' (Not q))) (And (cnnf' (Not p)) (cnnf' q))  
>         cnnf' fm = lfn fm

> lfn_dlo :: Formula Fol -> Formula Fol 
> lfn_dlo (Not(Atom(R "<" [s,t]))) = Or (Atom(R "=" [s,t])) (Atom (R "<" [t,s]))
> lfn_dlo (Not(Atom(R "=" [s,t]))) = Or (Atom(R "<" [s,t])) (Atom (R "<" [t,s]))
> lfn_dlo fm = fm

> dloBasic :: Formula Fol -> Formula Fol 
> dloBasic (Exists x p) = 
>   let vx = Var x 
>       cjs = F.conjuncts p \\ [Equal.mkEq vx vx] in
>   case List.find Equal.isEq cjs of
>     Just eqn -> let (s, t) = Equal.destEq eqn
>                     y = if s == vx then t else s in
>                 F.listConj (map (Fol.apply (x |=> y)) (cjs \\ [eqn]))
>     Nothing -> if elem (Atom (R "<" [vx, vx])) cjs then Bot else
>                let (lefts, rights) = List.partition (\(Atom (R "<" [_, t])) -> t == vx) cjs 
>                    ls = map (\(Atom (R "<" [l, _])) -> l) lefts
>                    rs = map (\(Atom (R "<" [_, r])) -> r) rights in
>                F.listConj (Lib.allPairs (\l r -> Atom (R "<" [l, r])) ls rs)
> dloBasic _ = error "dloBasic"               

> afn_dlo :: Vars -> Formula Fol -> Formula Fol 
> afn_dlo _ (Atom (R "<=" [s,t])) = Not(Atom(R "<" [t,s]))
> afn_dlo _ (Atom (R ">=" [s,t])) = Not(Atom(R "<" [s,t]))
> afn_dlo _ (Atom (R ">" [s,t])) = Atom(R "<" [t,s])
> afn_dlo _ fm = fm

> qelimDLO :: Formula Fol -> Formula Fol 
> qelimDLO = liftQelim afn_dlo (Prop.dnf . cnnf lfn_dlo) (const dloBasic)
