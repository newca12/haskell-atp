
Knuth-Bendix completion.

* Signature

> module ATP.Completion
>   ( overlaps
>   , listcases
>   , complete
>   , completeAndSimplify
>   , criticalPairs
>   , normalizeAndOrient
>   )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude
> import qualified ATP.Fol as Fol
> import qualified ATP.Equal as Equal
> import ATP.FormulaSyn
> import qualified ATP.Order as Order
> import qualified ATP.Rewrite as Rewrite
> import qualified ATP.Unif as Unif
> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))
> import qualified ATP.Util.Print as PP
> import qualified Data.List as List
> import qualified Data.Map as Map
> import qualified Data.Maybe as Maybe

* Completion

> renamePair :: (Formula, Formula) -> (Formula, Formula) 
> renamePair (fm1, fm2) = 
>   let fvs1 = Fol.fv fm1
>       fvs2 = Fol.fv fm2
>       (nms1, nms2) = splitAt (length fvs1) 
>          (map (Var . ("x" ++) . show) [0 .. length fvs1 + length fvs2 - 1]) 
>   in ( Fol.apply (Map.fromList (zip fvs1 nms1)) fm1, 
>        Fol.apply (Map.fromList (zip fvs2 nms2)) fm2 )

> listcases :: (a -> (Env -> a -> b) -> [c]) -> (Env -> [a] -> b) -> [a] -> [c] -> [c]
> listcases _ _ [] acc = acc
> listcases fn rfn (h:t) acc = 
>   fn h (\i h' -> rfn i (h':t)) ++ 
>   listcases fn (\i t' -> rfn i (h:t')) t acc

> overlaps :: (Term, Term) -> Term -> (Env -> Term -> a) -> [a]
> overlaps (l,r) tm rfn = 
>   case tm of
>     Var _ -> []
>     Fn f args -> 
>       listcases (overlaps (l,r)) (\i a -> rfn i (Fn f a)) args $
>          case Unif.fullunify [(l, tm)] of
>            Nothing -> []
>            Just env -> [rfn env r]

> crit1 :: Formula -> Formula -> [Formula]
> crit1 (Atom (R "=" [l1, r1])) (Atom (R "=" [l2, r2])) = 
>   overlaps (l1, r1) l2 (\i t -> Fol.apply i (Equal.mkEq t r2))
> crit1 _ _ = __IMPOSSIBLE__ 

> criticalPairs :: Formula -> Formula -> [Formula]
> criticalPairs fma fmb = 
>   let (fm1, fm2) = renamePair (fma, fmb) in
>   if fma == fmb then crit1 fm1 fm2
>   else Set.union (crit1 fm1 fm2) (crit1 fm2 fm1)

> normalizeAndOrient :: (Term -> Term -> Bool) -> [Formula] -> Formula -> Maybe (Term, Term)
> normalizeAndOrient ord eqs (Atom (R "=" [s, t])) =
>   let s' = Rewrite.rewrite eqs s 
>       t' = Rewrite.rewrite eqs t in
>   if ord s' t' then Just (s', t') 
>   else if ord t' s' then Just (t', s')
>   else Nothing 
> normalizeAndOrient _ _ _ = __IMPOSSIBLE__ 

> status :: ([Formula], [Formula], [Formula]) -> [Formula] -> IO ()
> status (eqs, def, crs) eqs0 = 
>   if eqs == eqs0 && not (length crs `mod` 1000 == 0) then return () else
>   do PP.putStrLn $ PP.hsep [ PP.int (length eqs), PP.text "equations and"
>                            , PP.int (length crs), PP.text "pending critical pairs +"
>                            , PP.int (length def), PP.text "deferred" ]

> complete :: (Term -> Term -> Bool) -> ([Formula], [Formula], [Formula]) -> IO (Maybe [Formula])
> complete ord (eqs, def, crits) =
>   case crits of
>     eq:ocrits -> 
>       let trip = case normalizeAndOrient ord eqs eq of
>                    Nothing -> (eqs, eq:def, ocrits)
>                    Just (s', t') -> if s' == t' then (eqs, def, ocrits) else
>                                     let eq' = Equal.mkEq s' t' 
>                                         eqs' = eq':eqs in
>                                     (eqs', def, ocrits ++ (concat (map (criticalPairs eq') eqs'))) in
>           do status trip eqs
>              complete ord trip
>     [] -> if def == [] then return (Just eqs) else 
>           case List.find (Maybe.isJust . normalizeAndOrient ord eqs) def of
>             Nothing -> return Nothing
>             Just e -> complete ord (eqs, def \\ [e], [e])

> interreduce :: [Formula] -> [Formula] -> [Formula]
> interreduce dun (Atom (R "=" [l, r]) : oeqs) = 
>   let dun' = if Rewrite.rewrite (dun ++ oeqs) l /= l then dun
>              else Equal.mkEq l (Rewrite.rewrite (dun ++ oeqs) r) : dun in
>   interreduce dun' oeqs
> interreduce dun _ = reverse dun

> completeAndSimplify :: Vars -> [Formula] -> IO (Maybe [Formula])
> completeAndSimplify wts eqs =
>   let ord = Order.lpoGe (Order.weight wts)
>       eqs' = map (\e -> case normalizeAndOrient ord [] e of 
>                           Just (l, r) -> Equal.mkEq l r
>                           Nothing -> error "Can't orient equation") eqs in
>   do eqs'' <- complete ord (eqs', [], Set.unions(Lib.allPairs criticalPairs eqs' eqs'))
>      case eqs'' of
>        Just eqs''' -> return $ Just (interreduce [] eqs''')
>        Nothing -> return Nothing

-- FIXME: 
-- > example = criticalPairs eq eq
-- >   where eq = Fol.parse "f(f(x)) = g(x)"

-- > example2 = do Just eqs' <- complete ord (eqs, [], ListSet.unions (Lib.allPairs criticalPairs eqs eqs))
-- >               return eqs'
-- >            where eqs = map parse ["1 * x = x", "i(x) * x = 1", "(x * y) * z = x * y * z"]
-- >                  ord = Order.lpoGe (Order.weight ["1", "*", "i"])
-- >                  parse = Fol.parse

-- > example3 = do eqs' <- example2
-- >               return (Rewrite.rewrite eqs' tm)
-- >   where parse = Fol.parseTerm
-- >         tm = parse "i(x * i(x)) * (i(i((y * z) * u) * y) * i(u))"
