
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

To combine decision procedures for theories T1, . . . Tn (with
axiomatizations using pairwise disjoint sets of function and predicate
symbols), the Nelson-Oppen method doesn't need any special knowledge
about the implementation of those procedures, but just the procedures
themselves and some characterization of their languages. In order to
permit languages with 5.13 Combining decision procedures 435 an
infinite signature (e.g. all numerals n), we will characterize the
language by discriminator functions on functions and predicates,
rather than lists of them. All the information is packaged up into a
triple. For example, the following is the information needed by the
Nelson-Oppen for the theory of reals with multiplication:

> type Lang = ( (Func, Int) -> Bool, (Pred, Int) -> Bool, Formula -> Bool )

> dloLang :: Lang
> dloLang = (fdesc, pdesc, Dlo.valid)
>   where fdesc (s, n) = n == 0 && Cooper.isInteger (Fn s [])
>         pdesc sn = elem sn preds
>         preds = [("<=", 2::Int), ("≤", 2), ("<", 2), (">=", 2), ("≥", 2), (">", 2)]

Almost identical is the corresponding information for the linear theory of
integers, decided by Cooper's method. Note that we still include multiplication
(though not exponentiation) in the language though its application
is strictly limited; this can be considered just the acceptance of syntactic
sugar rather than an expansion of the language.

> intLang :: Lang
> intLang = (fdesc, pdesc, elim)
>   where fdesc (s, n) = n == 0 && Cooper.isInteger (Fn s []) || elem (s, n) funcs
>         pdesc sn = elem sn preds
>         elim fm = Cooper.integerQelim(Fol.generalize fm) == Top
>         funcs = [("-", 1::Int), ("+", 2), ("-", 2), ("*", 2)]
>         preds = [("<=", 2::Int), ("≤", 2), ("<", 2), (">=", 2), ("≥", 2), (">", 2)]

We might also want to use congruence closure or some other decision
procedure for functions and predicates that are not interpreted by any of the
specified theories. The following takes an explicit list of languages langs
and adds on another one that treats all other functions as uninterpreted
and handles equality as the only predicate using congruence closure. This
could be extended to treat other predicates as uninterpreted, either by direct
extension of congruence closure to the level of formulas or by using exercise
3 of chapter 4.

> addDefault :: [Lang] -> [Lang]
> addDefault langs = langs ++ [ ( \sn -> not (List.any (\(f, _, _) -> f sn) langs)
>                               , \sn -> sn == ("=", 2)
>                               , Cong.ccvalid) ]

The Nelson-Oppen method starts by assuming the negation of the formula
to be proved, reducing it to DNF, and attempting to refute each
disjunct.  We will simply retain the original free variables in the
formula in the negated form, for convenience of implementation, but
note that logically all the `variables' below should be considered as
Skolem constants. In the running example, we have just one disjunct
that we need to refute: 

u + 1 = v ∧ f(u) + 1 = u - 1 ∧ f(v - 1) - 1 = v + 1 

The next step is to introduce new variables for subformulas in
such a way that we arrive at an equisatisfiable conjunction of
literals, each of which except for equality uses symbols from only a
single theory, a procedure known as homogenization or
purification. For our example we might get: 

u+1 = v ∧ v1+1 = u-1 ∧ v2-1 = v+1 ∧ v2 = f(v3) ∧ v1 = f(u) ∧ v3 = v-1 

This introduction of fresh
`variables' is satisfiability-preserving, since they are really
constants. To implement the transformation, we wish to choose given
each atom a language for it based on a `topmost' predicate or function
symbol. Note that in the case of an equation there may be a choice of
which topmost function symbol to choose, e.g. for f(x) = y + 1. Note
also that in the case of an equation between variables we need a
language including the equality symbol in our list (e.g. the one
incorporated by add_default).

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

Once we have fixed on a language for a literal, the topmost subterms not in
that language are replaced by new variables, with their `definitions' adjoined
as new equations, which may themselves be homogenized later. To handle
the recursion replacing non-homogeneous subterms, we use a continuationpassing
style where the continuation handles the replacement within the
current context and accumulates the new definitions. The following general
function maps a continuation-based operator over a list, modifying the list
elements successively:

> listify :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c 
> listify f l cont = 
>   case l of 
>     [] -> cont []
>     h:t -> f h (\h' -> listify f t (\t' -> cont (h':t')))

The continuations take as arguments the new term, the current variable
index and the list of new definitions. The following homogenizes a
term, given a language with its function and predicate discriminators
fn and pr.  In the case of a variable, we apply the continuation to
the current state. In the case of a function in the language, we keep
it but recursively modify the arguments, while for a function not in
the language, we replace it with a new variable vn, with n picked at
the outset to avoid existing variables:

> homot :: Lang -> Term -> (Term -> Int -> [Formula] -> c) -> Int -> [Formula] -> c
> homot (fn, pr, dp) tm cont n defs = 
>   case tm of 
>     Var _ -> cont tm n defs
>     Num _ -> cont tm n defs
>     Fn f args -> 
>       if fn(f, length args) 
>       then listify (homot (fn, pr, dp)) args (\a -> cont (Fn f a)) n defs
>       else cont (Var ("v_" ++ show n)) (n+1) (Var ("v_" ++ show n) ≡ tm : defs)

Homogenizing a literal is similar, using homot to deal with the arguments
of predicates.

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

This only covers a single pass of homogenization, and the new definitional
equations may also have non-homogeneous subterms on their right-hand
sides, so we need to pass those along for another iteration as long as there
are any pending definitions:

> homo :: [Lang] -> [Formula] -> ([Formula] -> Int 
>         -> [Formula] -> a) -> Int -> [Formula] -> a
> homo langs fms cont = 
>   listify (homol langs) fms
>           (\dun n defs -> if defs == [] then cont dun n defs
>                           else homo langs defs (\res -> cont (dun ++ res)) n [])

The overall procedure just picks the appropriate variable index to start
with:

> homogenize :: [Lang] -> [Formula] -> [Formula]
> homogenize langs fms = 
>   let n = 1 + foldr (Cnf.maxVarIndex "v_") 0 (Fol.fv fms) 
>   in homo langs fms (\res _ _ -> res) n []

The next step is to partition the homogenized literals into those in the
various languages. The following tells us whether a formula belongs to a
given language, allowing equality in all languages:

> belongs :: Lang -> Formula -> Bool
> belongs (fn, pr, _) fm = 
>   List.all fn (Fol.functions fm) &&
>   List.all pr (Fol.predicates fm \\ [("=", 2)])

and using that, the following partitions up literals according to a list of
languages:

> langpartition :: [Lang] -> [Formula] -> [[Formula]]
> langpartition langs fms = 
>   case langs of
>     [] -> if fms == [] then [] else error "langpartition"
>     l:ls -> let (fms1, fms2) = List.partition (belongs l) fms in
>             fms1 : langpartition ls fms2

* Interpolants

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
