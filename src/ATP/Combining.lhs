
> module Combining ( slowNelop
>                  , nelop
>                  , intLang
>                  , addDefault
>                  )
>   where

> import Prelude 
> import qualified List
> import qualified Maybe
> import qualified ListSet
> import ListSet((\\))
> import qualified Lib
> import Lib((|=>))
> import qualified Formulas as F
> import Formulas(Formula(..), Clause, Vars, Var, Sym)
> import qualified Fol
> import Fol(Fol(R), Term(..))
> import qualified Skolem
> import qualified Cooper
> import qualified Cong
> import qualified Equal
> import qualified DefCnf
> import qualified Prop

> type Lang = ( (Sym, Int) -> Bool, (Sym, Int) -> Bool, Formula Fol -> Bool )

> intLang :: Lang
> intLang = (fdesc, pdesc, elim)
>   where fdesc (s, n) = n == 0 && Cooper.isNumeral (Fn s []) || elem (s, n) funcs
>         pdesc sn = elem sn preds
>         elim fm = Cooper.integerQelim(Fol.generalize fm) == Top
>         funcs = [("-", 1::Int), ("+", 2), ("-", 2), ("*", 2)]
>         preds = [("<=", 2::Int), ("<", 2), (">=", 2), (">", 2)]

> addDefault :: [Lang] -> [Lang]
> addDefault langs = langs ++ [(\sn -> not (List.any (\(f, _, _) -> f sn) langs),
>                               \sn -> sn == ("=", 2), 
>                               Cong.ccvalid)]

> chooseLang :: [Lang] -> Formula Fol -> Maybe Lang
> chooseLang langs fm =
>   case fm of
>     Atom(R "=" [Fn f args, _]) -> 
>       List.find (\(fn,_,_) -> fn(f,length args)) langs
>     Atom(R "=" [_, Fn f args]) ->
>       List.find (\(fn,_,_) -> fn(f,length args)) langs
>     Atom(R p args) ->
>       List.find (\(_,pr,_) -> pr(p,length args)) langs
>     _ -> error "Impossible" 

> listify :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c 
> listify f l cont = 
>   case l of 
>     [] -> cont []
>     h:t -> f h (\h' -> listify f t (\t' -> cont (h':t')))

> homot :: Lang -> Term -> (Term -> Int -> [Formula Fol] -> c) -> Int -> [Formula Fol] -> c
> homot (fn, pr, dp) tm cont n defs = 
>   case tm of 
>     Var _ -> cont tm n defs
>     Fn f args -> if fn(f, length args) 
>                    then listify (homot (fn, pr, dp)) args (\a -> cont (Fn f a)) n defs
>                  else cont (Var ("v_" ++ show n)) (n+1) ( (Equal.mkEq (Var ("v_" ++ show n)) tm) : defs)

> homol :: [Lang] -> Formula Fol -> (Formula Fol -> Int -> [Formula Fol] -> a) -> Int -> [Formula Fol] -> a
> homol langs fm cont n defs =
>   case fm of 
>     Not f -> homol langs f (\p -> cont (Not p)) n defs
>     Atom (R p args) -> 
>       let lang = case chooseLang langs fm of 
>                    Just l -> l 
>                    Nothing -> error "Impossible" in
>       listify (homot lang) args (\a -> cont (Atom (R p a))) n defs
>     _ -> error "homol: not a literal"

> homo :: [Lang] -> [Formula Fol] -> ([Formula Fol] -> Int 
>         -> [Formula Fol] -> a) -> Int -> [Formula Fol] -> a
> homo langs fms cont = 
>   listify (homol langs) fms
>           (\dun n defs -> if defs == [] then cont dun n defs
>                           else homo langs defs (\res -> cont (dun ++ res)) n [])

> homogenize :: [Lang] -> [Formula Fol] -> [Formula Fol]
> homogenize langs fms = 
>   let fvs = ListSet.unions (map Fol.fv fms) 
>       n = 1 + foldr (DefCnf.maxVarIndex "v_") 0 fvs in
>   homo langs fms (\res _ _ -> res) n []

> belongs :: Lang -> Formula Fol -> Bool
> belongs (fn, pr, _) fm = 
>   List.all fn (Fol.functions fm) &&
>   List.all pr (Fol.predicates fm \\ [("=", 2)])

> langpartition :: [Lang] -> [Formula Fol] -> [[Formula Fol]]
> langpartition langs fms = 
>   case langs of
>     [] -> if fms == [] then [] else error "langpartition"
>     l:ls -> let (fms1, fms2) = List.partition (belongs l) fms in
>             fms1 : langpartition ls fms2

> arreq :: Vars -> [Formula Fol]
> arreq l =
>   case l of 
>     v1:v2:rest -> Equal.mkEq (Var v1) (Var v2) : arreq (v2 : rest)
>     _ -> []

> arrangement :: [Vars] -> [Formula Fol]
> arrangement part = 
>   foldr (ListSet.union . arreq) 
>     (map (\(v,w) -> Not(Equal.mkEq (Var v) (Var w))) (Lib.distinctPairs (map head part))) 
>     part

> destDef :: Formula Fol -> Maybe (Var, Term)
> destDef fm = 
>   case fm of 
>     Atom (R "=" [Var x, t]) | not(elem x (Fol.fv t)) -> Just (x, t)
>     Atom (R "=" [t, Var x]) | not(elem x (Fol.fv t)) -> Just (x, t)
>     _ -> Nothing 

> redeqs :: Clause Fol -> Clause Fol
> redeqs eqs = 
>   case List.find (Maybe.isJust . destDef) eqs of
>     Just eq -> let (x, t) = case destDef eq of 
>                               Just xt -> xt 
>                               Nothing -> error "Impossible" in
>                redeqs (map (Fol.apply (x |=> t)) (eqs \\ [eq]))
>     Nothing -> eqs

> trydps :: [(Lang, Clause Fol)] -> Clause Fol -> Bool
> trydps ldseps fms =
>   List.any (\((_, _, dp), fms0) -> dp $ Not $ F.listConj $ redeqs $ fms0 ++ fms)
>            ldseps

> allpartitions :: Ord a => [a] -> [[[a]]]
> allpartitions l = foldr (\h y -> foldr (allinsertions h) [] y) [[]] l
>   where allinsertions x l acc = 
>           foldr (\p acc -> ((x:p):(l \\ [p])):acc) (([x]:l):acc) l

> slowNelopRefute :: [Var] -> [(Lang, Clause Fol)] -> Bool
> slowNelopRefute vars ldseps = 
>   List.all (trydps ldseps . arrangement) (allpartitions vars)

> slowNelop1 :: [Lang] -> Clause Fol -> Bool
> slowNelop1 langs fms0 = 
>   let fms = homogenize langs fms0 
>       seps = langpartition langs fms
>       fvlist = map (ListSet.unions . map Fol.fv) seps
>       vars = List.filter (\x -> length (List.filter (elem x) fvlist) >= 2)
>                          (ListSet.unions fvlist) in
>   slowNelopRefute vars (zip langs seps)

> slowNelop :: [Lang] -> Formula Fol -> Bool
> slowNelop langs fm = List.all (slowNelop1 langs) (Prop.simpdnf $ Skolem.simplify $ Not fm)

> findasubset :: ([a] -> Maybe b) -> Int -> [a] -> Maybe b
> findasubset p 0 _ = p []
> findasubset _ _ [] = Nothing
> findasubset p m (h:t) = case findasubset (p . (h:)) (m-1) t of
>                           Just x -> Just x
>                           Nothing -> findasubset p m t

> findsubset :: ([a] -> Bool) -> [a] -> Maybe [a]
> findsubset p l = 
>   Lib.findApply (\n -> findasubset (\x -> if p x then Just x else Nothing) n l)
>             [0 .. length l]
>                    

> nelopRefute :: [Formula Fol] -> [(Lang, Clause Fol)] -> Bool
> nelopRefute eqs ldseps = 
>   case findsubset (trydps ldseps . map F.opp) eqs of
>     Nothing -> False
>     Just dj -> List.all (\eq -> nelopRefute (eqs \\ [eq])
>                                 (map (\(dps, es) -> (dps, eq:es)) ldseps)) dj

> nelop1 :: [Lang] -> Clause Fol -> Bool
> nelop1 langs fms0 = 
>   let fms = homogenize langs fms0 
>       seps = langpartition langs fms
>       fvlist = map (ListSet.unions . map Fol.fv) seps
>       vars = List.filter (\x -> length (List.filter (elem x) fvlist) >= 2)
>                          (ListSet.unions fvlist) 
>       eqs = map (\(a,b) -> Equal.mkEq (Var a) (Var b)) (Lib.distinctPairs vars) in
>   nelopRefute eqs (zip langs seps)

> nelop :: [Lang] -> Formula Fol -> Bool
> nelop langs fm = List.all (nelop1 langs) (Prop.simpdnf $ Skolem.simplify $ Not fm)

