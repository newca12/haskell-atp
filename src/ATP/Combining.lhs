
The Nelson-Oppen method.

* Signature

> module ATP.Combining
>   ( slowNelop
>   , intLang
>   , dloLang
>   , nelop
>   , nelopInt
>   , nelopDlo
>   , addDefault
>   )
> where

* Imports

#include "undefined.h"

> import ATP.Util.Prelude 
> import qualified ATP.Cong as Cong
> import qualified ATP.Cooper as Cooper
> import qualified ATP.DefCnf as Cnf
> import qualified ATP.Dlo as Dlo
> import qualified ATP.Equal as Equal
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Prop as Prop
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Util.Debug as Debug
> import qualified ATP.Util.Lib as Lib
> import ATP.Util.Lib((⟾))
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))
--> import qualified Control.Exception as Exn
> import qualified Data.List as List
> import qualified Data.Maybe as Maybe

* Nelson-Oppen

> type Lang = ( (Func, Int) -> Bool, (Pred, Int) -> Bool, Formula -> Bool )

> intLang :: Lang
> intLang = (fdesc, pdesc, elim)
>   where fdesc (s, n) = n == 0 && Cooper.isNumeral (Fn s []) || elem (s, n) funcs
>         pdesc sn = elem sn preds
>         elim fm = Cooper.integerQelim(Fol.generalize fm) == Top
>         funcs = [("-", 1::Int), ("+", 2), ("-", 2), ("*", 2)]
>         preds = [("<=", 2::Int), ("≤", 2), ("<", 2), (">=", 2), ("≥", 2), (">", 2)]

> dloLang :: Lang
> dloLang = (fdesc, pdesc, Dlo.valid)
>   where fdesc (s, n) = n == 0 && Cooper.isNumeral (Fn s [])
>         pdesc sn = elem sn preds
>         preds = [("<=", 2::Int), ("≤", 2), ("<", 2), (">=", 2), ("≥", 2), (">", 2)]

> addDefault :: [Lang] -> [Lang]
> addDefault langs = langs ++ [ ( \sn -> not (List.any (\(f, _, _) -> f sn) langs)
>                               , \sn -> sn == ("=", 2)
>                               , Cong.ccvalid) ]

> chooseLang :: [Lang] -> Formula -> Maybe Lang
> chooseLang langs fm =
>   case fm of
>     Atom(R "=" [Fn f args, _]) -> 
>       List.find (\(fn,_,_) -> fn(f,length args)) langs
>     Atom(R "=" [_, Fn f args]) ->
>       List.find (\(fn,_,_) -> fn(f,length args)) langs
>     Atom(R p args) ->
>       List.find (\(_,pr,_) -> pr(p,length args)) langs
>     _ -> Debug.impossible

> listify :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c 
> listify f l cont = 
>   case l of 
>     [] -> cont []
>     h:t -> f h (\h' -> listify f t (\t' -> cont (h':t')))

> homot :: Lang -> Term -> (Term -> Int -> [Formula] -> c) -> Int -> [Formula] -> c
> homot (fn, pr, dp) tm cont n defs = 
>   case tm of 
>     Var _ -> cont tm n defs
>     Fn f args -> 
>       if fn(f, length args) 
>       then listify (homot (fn, pr, dp)) args (\a -> cont (Fn f a)) n defs
>       else cont (Var ("v_" ++ show n)) (n+1) (Var ("v_" ++ show n) ≡ tm : defs)

> homol :: [Lang] -> Formula -> (Formula -> Int -> [Formula] -> a) -> Int -> [Formula] -> a
> homol langs fm cont n defs =
>   case fm of 
>     Not f -> homol langs f (\p -> cont (Not p)) n defs
>     Atom (R p args) -> 
>       let lang = case chooseLang langs fm of 
>                    Just l -> l 
>                    Nothing -> __IMPOSSIBLE__ in
>       listify (homot lang) args (\a -> cont (Atom (R p a))) n defs
>     _ -> error "homol: not a literal"

> homo :: [Lang] -> [Formula] -> ([Formula] -> Int 
>         -> [Formula] -> a) -> Int -> [Formula] -> a
> homo langs fms cont = 
>   listify (homol langs) fms
>           (\dun n defs -> if defs == [] then cont dun n defs
>                           else homo langs defs (\res -> cont (dun ++ res)) n [])

> homogenize :: [Lang] -> [Formula] -> [Formula]
> homogenize langs fms = 
>   let n = 1 + foldr (Cnf.maxVarIndex "v_") 0 (Fol.fv fms) 
>   in homo langs fms (\res _ _ -> res) n []

> belongs :: Lang -> Formula -> Bool
> belongs (fn, pr, _) fm = 
>   List.all fn (Fol.functions fm) &&
>   List.all pr (Fol.predicates fm \\ [("=", 2)])

> langpartition :: [Lang] -> [Formula] -> [[Formula]]
> langpartition langs fms = 
>   case langs of
>     [] -> if fms == [] then [] else error "langpartition"
>     l:ls -> let (fms1, fms2) = List.partition (belongs l) fms in
>             fms1 : langpartition ls fms2

> arreq :: Vars -> [Formula]
> arreq l =
>   case l of 
>     v1:v2:rest -> Var v1 ≡ Var v2 : arreq (v2 : rest)
>     _ -> []

> arrangement :: [Vars] -> [Formula]
> arrangement part = 
>   foldr (Set.union . arreq) 
>     (map (\(v,w) -> Var v ≠ Var w) (Lib.distinctPairs (map head part))) 
>     part

> destDef :: Formula -> Maybe (Var, Term)
> destDef fm = 
>   case fm of 
>     Atom (R "=" [Var x, t]) | not(elem x (Fol.fv t)) -> Just (x, t)
>     Atom (R "=" [t, Var x]) | not(elem x (Fol.fv t)) -> Just (x, t)
>     _ -> Nothing 

> redeqs :: Clause -> Clause
> redeqs eqs = 
>   case List.find (Maybe.isJust . destDef) eqs of
>     Just eq -> let (x, t) = case destDef eq of 
>                               Just xt -> xt 
>                               Nothing -> __IMPOSSIBLE__ in
>                redeqs (map (Fol.apply (x ⟾ t)) (eqs \\ [eq]))
>     Nothing -> eqs

> trydps :: [(Lang, Clause)] -> Clause -> Bool
> trydps ldseps fms =
>   List.any (\((_, _, dp), fms0) -> dp $ Not $ F.listConj $ redeqs $ fms0 ++ fms)
>            ldseps

> allpartitions :: Ord a => [a] -> [[[a]]]
> allpartitions = foldr (\h y -> foldr (allinsertions h) [] y) [[]] 
>   where allinsertions x l acc = 
>           foldr (\p acc' -> ((x:p) : (l \\ [p])) : acc') (([x]:l):acc) l

> slowNelopRefute :: [Var] -> [(Lang, Clause)] -> Bool
> slowNelopRefute vars ldseps = 
>   List.all (trydps ldseps . arrangement) (allpartitions vars)

> slowNelop1 :: [Lang] -> Clause -> Bool
> slowNelop1 langs fms0 = 
>   let fms = homogenize langs fms0 
>       seps = langpartition langs fms
>       fvlist = map (Set.unions . map Fol.fv) seps
>       vars = List.filter (\x -> length (List.filter (elem x) fvlist) >= 2)
>                          (Set.unions fvlist) in
>   slowNelopRefute vars (zip langs seps)

> slowNelop :: [Lang] -> Formula -> Bool
> slowNelop langs fm = List.all (slowNelop1 langs) (Prop.simpdnf $ Skolem.simplify $ Not fm)

> findasubset :: ([a] -> Maybe b) -> Int -> [a] -> Maybe b
> findasubset p 0 _ = p []
> findasubset _ _ [] = Nothing
> findasubset p m (h:t) = 
>   case findasubset (p . (h:)) (m-1) t of
>     Just x -> Just x
>     Nothing -> findasubset p m t

> findsubset :: ([a] -> Bool) -> [a] -> Maybe [a]
> findsubset p l = 
>   Lib.findApply (\n -> findasubset (\x -> if p x then Just x else Nothing) n l)
>             [0 .. length l]
>                    

> nelopRefute :: [Formula] -> [(Lang, Clause)] -> Bool
> nelopRefute eqs ldseps = 
>   case findsubset (trydps ldseps . map F.opp) eqs of
>     Nothing -> False
>     Just dj -> List.all (\eq -> nelopRefute (eqs \\ [eq])
>                                 (map (\(dps, es) -> (dps, eq:es)) ldseps)) dj

> nelop1 :: [Lang] -> Clause -> Bool
> nelop1 langs fms0 = 
>   let fms = homogenize langs fms0 
>       seps = langpartition langs fms
>       fvlist = map (Set.unions . map Fol.fv) seps
>       vars = List.filter (\x -> length (List.filter (elem x) fvlist) >= 2)
>                          (Set.unions fvlist) 
>       eqs = map (\(a,b) -> Equal.mkEq (Var a) (Var b)) (Lib.distinctPairs vars) in
>   nelopRefute eqs (zip langs seps)

> nelop :: [Lang] -> Formula -> Bool
> nelop langs fm = List.all (nelop1 langs) (Prop.simpdnf $ Skolem.simplify $ Not fm)

-- > nelop :: [Lang] -> Formula -> Bool
-- > nelop langs fm = Debug.impossible

-- > nelop :: [Lang] -> Formula -> Bool
-- > nelop langs fm = Exn.assert False undefined

-- > nelop :: [Lang] -> Formula -> Bool
-- > nelop langs fm = Exn.assert False True

-- > nelop :: [Lang] -> Formula -> Bool
-- > nelop langs fm = __IMPOSSIBLE__

> nelopInt :: Formula -> Bool
> nelopInt = nelop (addDefault [intLang])

> nelopDlo :: Formula -> Bool
> nelopDlo = nelop (addDefault [dloLang])

let langs = addDefault [intLang]
let fm :: Formula = ATP.Util.Parse.parse "1 = 1"
