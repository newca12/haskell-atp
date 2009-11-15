
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
> import qualified ATP.Util.List as List
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))
> import qualified ATP.Util.Print as PP
> import qualified Data.Map as Map
> import qualified Data.Maybe as Maybe

* Completion

We now turn to implementation. As with resolution, we start with the
tedious business of preparing for unication by renaming variables. For simplicity,
we replace the variables in two given formulas by schematic variables
of the form x_n:

> renamePair :: (Formula, Formula) -> (Formula, Formula) 
> renamePair (fm1, fm2) = 
>   let fvs1 = Fol.fv fm1
>       fvs2 = Fol.fv fm2
>       (nms1, nms2) = splitAt (length fvs1) 
>          (map (Var . ("x" ++) . show) [0 .. length fvs1 + length fvs2 - 1]) 
>   in ( Fol.apply (Map.fromList (zip fvs1 nms1)) fm1, 
>        Fol.apply (Map.fromList (zip fvs2 nms2)) fm2 )

Now we come to nding all possible overlaps. This is a little bit trickier
than it looks, because we want to ensure that the MGU discovered at depth
eventually gets applied to the whole term. The following function denes
all ways of overlapping an equation l = r with another term tm, where the
additional argument rfn is used to create each overall critical pair from an
instantiation i.
The function recursively traverses the term, trying to unify l with each
non-variable subterm and applying rfn to any resulting instantiations to
give the critical pair arising from that overlap. During recursive descent,
the function rfn is itself modied correspondingly. For updating rfn across
the list of arguments we dene the auxiliary function listcases, which we
will re-use later in a dierent situation:

> listcases :: (a -> (Env -> a -> b) -> [c]) -> (Env -> [a] -> b) -> [a] -> [c] -> [c]
> listcases _ _ [] acc = acc
> listcases fn rfn (h:t) acc = 
>   fn h (\i h' -> rfn i (h':t)) ++ 
>   listcases fn (\i t' -> rfn i (h:t')) t acc

> overlaps :: (Term, Term) -> Term -> (Env -> Term -> a) -> [a]
> overlaps (l,r) tm rfn = 
>   case tm of
>     Var _ -> []
>     Num _ -> []
>     Fn f args -> 
>       listcases (overlaps (l,r)) (\i a -> rfn i (Fn f a)) args $
>          case Unif.fullunify [(l, tm)] of
>            Nothing -> []
>            Just env -> [rfn env r]

In order to present a nicer interface, we accept equational formulas rather
than pairs of terms, and return critical pairs in the same way, by appropriately
setting up the initial rfn:

> crit1 :: Formula -> Formula -> [Formula]
> crit1 (Atom (R "=" [l1, r1])) (Atom (R "=" [l2, r2])) = 
>   overlaps (l1, r1) l2 (\i t -> Fol.apply i (Equal.mkEq t r2))
> crit1 _ _ = __IMPOSSIBLE__ 

For the overall function, we need to rename the variables in the initial
formula then nd all overlaps of the rst on the second and vice versa,
unless the two input equations are identical, in which case only one needs
to be done:

> criticalPairs :: Formula -> Formula -> [Formula]
> criticalPairs fma fmb = 
>   let (fm1, fm2) = renamePair (fma, fmb) in
>   if fma == fmb then crit1 fm1 fm2
>   else Set.union (crit1 fm1 fm2) (crit1 fm2 fm1)

* Completion

We could now code up a function to decide if a terminating rewrite system is
con
uent by nding all the critical pairs f(si; ti) j 1  i  ng between pairs
of equations, and for each such (si; ti) reducing the terms to some normal
forms s0
i and t0
i. The resulting system is con
uent i all corresponding pairs
of terms s0
i and t0
i are syntactically equal. However, rather than merely do
this, we can be more ambitious.
If (s0
i; t0
i) is a normalized critical pair, then it is a logical consequence
of the initial equations, since it results from repeated rewriting with those
equations of a common starting term. Thus, we could add s0
i = t0
i or t0
i = s0
i
as a new equation, retaining logical equivalence with the old axiom set. It
may turn out that with this addition, the set will become con
uent. If
not, we can repeat the process with remaining critical pairs and any arising
278 Equality
from the new equation. This idea is known as completion, and was rst
systematically investigated by Knuth and Bendix (1970), who demonstrated
that it can be a remarkably eective technique for arriving at a canonical
rewrite set for many interesting algebraic theories such as groups. It should
be noted, however, that success of the procedure is not guaranteed; two
things can go wrong.
First, adding s0
i = t0
i or t0
i = s0
i may cause the resulting rewrite set to
become nonterminating. To try and avoid this, we will keep a xed term
ordering in mind, and try to orient the equation so that it respects the
ordering, but it may turn out that neither direction respects the ordering.
Second, although the new equation s0
i = t0
i or t0
i = s0
i trivially means that
the originating critical pair (si; ti) is now joinable in the new system, the new
equation will in general create new critical pairs, with the existing equations
and perhaps even with itself. It's entirely possible that the creation of new
critical pairs will `outrun' their processing into new rules, so that the overall
process never terminates.
Despite these provisos, let us implement completion and see it in action.
The central component is a procedure that takes an equation s = t, normalizes
both s and t to give s0 and t0, and attempts to orient these terms into
an equation respecting the given ordering ord, failing if this is impossible.
We assume ord is the re
exive form of ordering, so failure will not occur in
the case where s0 and t0 are identical.

> normalizeAndOrient :: (Term -> Term -> Bool) -> [Formula] -> Formula -> Maybe (Term, Term)
> normalizeAndOrient ord eqs (Atom (R "=" [s, t])) =
>   let s' = Rewrite.rewrite eqs s 
>       t' = Rewrite.rewrite eqs t in
>   if ord s' t' then Just (s', t') 
>   else if ord t' s' then Just (t', s')
>   else Nothing 
> normalizeAndOrient _ _ _ = __IMPOSSIBLE__ 

The central completion procedure maintains a set of equations eqs and a
set of pending critical pairs crits, and successively examines critical pairs,
normalizing and orienting resulting equations and adding them to eqs. However,
since the order in which we examine critical pairs is arbitrary, we try to
avoid failing too hastily by storing equations that cannot as yet be oriented
on a separate `deferred' list def.
Only at the end, by which time these troublesome equations may normalize
to the point of joinability, or at least orientability, do we reconsider
them, putting the rst orientable one back in the main list of critical pairs.
The following auxiliary function is used to conditionally emit a report on
current status, so that the user gets an idea what's going on.

> status :: ([Formula], [Formula], [Formula]) -> [Formula] -> IO ()
> status (eqs, def, crs) eqs0 = 
>   if eqs == eqs0 && not (length crs `mod` 1000 == 0) then return () else
>   do PP.putStrLn $ PP.hsep [ PP.int (length eqs), PP.text "equations and"
>                            , PP.int (length crs), PP.text "pending critical pairs +"
>                            , PP.int (length def), PP.text "deferred" ]

In the main completion loop, if there is a critical pair left to be examined,
we attempt to normalize and orient it; if it is nontrivial (i.e. not of the form
t = t) we add it to the equations, and augment the critical pairs (at the
tail end) with new critical pairs from this new equation and itself plus those
already present. If the orientation fails, then we just add the critical pair to
the `deferred' list. Finally, if there are no critical pairs left, we attempt to
orient and deal with the deferred critical pairs, starting with any found to
be orientable. If we are ultimately left with some that are non-orientable,
we fail. Otherwise we terminate with success and return the new equations.

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
>     [] -> if null def then return (Just eqs) else 
>           case List.find (Maybe.isJust . normalizeAndOrient ord eqs) def of
>             Nothing -> return Nothing
>             Just e -> complete ord (eqs, def \\ [e], [e])

The main loop maintains the invariant that all critical pairs from pairs of
equations in eqs that are not joinable by eqs are contained in crits and
def together, so when successful termination occurs, since crits and def
are both empty, there are no non-joinable critical pairs, and so by Corollary
4.25, the system is con
uent. Moreover, since the original equations are
included in the nal set and we have only added equational consequences
of the original equations, they give a logically equivalent set. In order to
get started, we just have to set crits to the critical pairs for the original
equations and also def = [], so the invariant is true to start with.
Before considering renements, let's try a simple example: the axioms
for groups. For the ordering we choose the lexicographic path ordering,
with 1 having smallest precedence and the inverse operation the largest.
280 Equality
The intuitive reason for giving the inverse the highest precedence is that it
will tend to cause the expansion (x  y)􀀀1 = y􀀀1  x􀀀1 to be applied (when
it is eventually derived), leading to more opportunities for cancellation of
multiple inverse operations. 

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
>   do eqs'' <- complete ord (eqs', [], Set.unions(List.allPairs criticalPairs eqs' eqs'))
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
