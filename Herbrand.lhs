
Relation between FOL and propositonal logic; Herbrand theorem. 

> module Herbrand ( herbfuns
>                 , groundtuples
>                 , gilmore
>                 , dpRefineLoop
>                 , davisputnam
>                 , davisputnam'
>                 ) where

> import Prelude 
> import qualified Data.Map as Map
> import qualified List
> import Text.Printf(printf)

> import qualified Lib 
> import qualified ListSet
> import FormulaSyn
> import qualified Fol 
> import qualified Prop 
> import qualified Skolem 
> import qualified Dp

Function symbols with arity.

> type FuncA = (Func, Int)

Get the constants for Herbrand base, adding nullary one if necessary.

> herbfuns :: Formula -> ([FuncA], [FuncA])
> herbfuns fm = 
>     let syms @ (cns, fns) = List.partition ((== 0) . snd) (Fol.functions fm) in
>     if cns == [] then ([("c", 0)], fns) else syms

The function groundterms enumerates all ground terms involving n functions.
If n = 0 the constant terms are returned. Otherwise all possible
functions are tried, and since we then need to fill the argument places of
each m-ary function with terms involving in total n - 1 functions, one already
having been used, we recursively call groundtuples

groundterms constantTerms functionSymbols numSymbols 
  --> "ground terms with numSymbols function symbols"

> groundterms :: [Term] -> [FuncA] -> Int -> [Term]
> groundterms cntms _ 0 = cntms
> groundterms cntms funcs n = 
>   let grtps (f, arity) =  map (Fn f) (groundtuples cntms funcs (n-1) arity) in
>   concat (map grtps funcs)

while the mutually recursive function groundtuples generates all m-tuples of
ground terms involving (in total) n functions. For all k up to n, this in turn
tries all ways of occupying the first argument place with a k-function term
and then recursively produces all (m - 1)-tuples involving all the remaining
n - k functions.

groundtuples 

> groundtuples :: [Term] -> [FuncA] -> Int -> Int -> [[Term]]
> groundtuples _ _ 0 0 = [[]]
> groundtuples _ _ _ 0 = []
> groundtuples cntms funcs n m = 
>   let tups k = Lib.allPairs (:) 
>                (groundterms cntms funcs k)
>                (groundtuples cntms funcs (n-k) (m-1)) in
>   concat (map tups [0 .. n])

Gilmore's method can be considered just one member of a family of
`Herbrand procedures' that somehow test larger and larger conjunctions of
ground instances until unsatisfiability is verified. We can generalize over
the way the satisfiability test is done (tfn) and the modification function
(mfn) that augments the ground instances with a new instance, whatever
form they may be stored in. This generalization, which not only saves code
but emphasizes that the key ideas are independent of the particular propositional
satisfiability test at the core, is carried through in the following
loop

Several parameters are carried around unchanged: the modification and
testing function parameters, the initial formula in some transformed list
representation (fl0), then constant terms cntms and functions funcs and
the free variables fvs of the formula. The other arguments are n, the next
level of the enumeration to generate, fl, the set of ground instances so far,
tried, the instances tried, and tuples, the remaining ground instances in
the current level. When tuples is empty, we simply generate the next level
and step n up to n + 1. In the other case, we use the modification function
to update fl with another instance. If this is unsatisfiable, then we return
the successful set of instances tried; otherwise, we continue. 

> herbloop :: (a -> (Formula -> Formula) -> [b] -> [b])
>          -> ([b] -> Bool) 
>          -> a -> [Term] -> [FuncA] -> Vars -> Int
>          -> [b] -> [[Term]] -> [[Term]] -> IO [[Term]]
> herbloop mfn tfn fl0 cntms funcs fvs n fl tried tuples = 
>     do printf (show (length tried) ++ " ground instances tried; " ++
>                show (length fl) ++ " items in list\n")
>        case tuples of
>          [] -> let newtups = groundtuples cntms funcs n (length fvs) in
>                herbloop mfn tfn fl0 cntms funcs fvs (n+1) fl tried newtups
>          tup:tups -> let fl' = mfn fl0 (Fol.apply $ Map.fromList $ zip fvs tup) fl in
>                      if not(tfn fl') then return (tup:tried) else
>                      herbloop mfn tfn fl0 cntms funcs fvs n fl' (tup:tried) tups

%%%%%%%%%%%%%%%%%%%%%
%%% Gilmore procedure

In the particular case of the Gilmore procedure, formulas are
maintained in fl0 and fl in a DNF representation, and the modification
function applies the instantiation to the starting formula fl0 and
combines the DNFs by distribution.

We're more usually interested in proving validity rather than unsatisfiability.
For this, we generalize, negate and Skolemize the initial formula and
set up the appropriate sets of free variables, functions and constants. Then
we simply start the main loop, and report if it terminates how many ground
instances were tried:

> gilmoreLoop :: Clauses -> [Term] -> [FuncA] -> Vars -> Int
>             -> Clauses -> [[Term]] -> [[Term]] -> IO [[Term]] 
> gilmoreLoop =
>   let mfn djs0 ifn djs =
>           filter (not . Prop.trivial) 
>              (Prop.distrib (ListSet.image (ListSet.image ifn) djs0) djs) in 
>   herbloop mfn (/= [])

> gilmore :: Formula -> IO Int
> gilmore fm = 
>     let sfm = Skolem.skolemize(Not(Fol.generalize fm)) 
>         fvs = Fol.fv sfm 
>         (consts,funcs) = herbfuns sfm 
>         cntms = map (\(c,_) -> Fn c []) consts in
>     do tms <- gilmoreLoop (Prop.simpdnf sfm) cntms funcs fvs 0 [[]] [] []
>        return (length tms)

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Davis-Putnam procedure

All in all, although the Gilmore procedure is a promising start to firstorder
theorem proving, there is plenty of room for improvement. Since the
main limitation seems to be the explosion in the number of disjuncts in
the DNF, a natural approach is to maintain the same kind of enumeration
procedure but check the propositional satisfiability of the conjunction of
ground instances generated so far by a more efficient propositional algorithm.
In fact, it was for exactly this purpose that ?) developed their procedure
for propositional satisfiability testing (see section 2.9). In this context,
clausal form has the particular advantage that there is no analogue
of the multiplicative explosion of disjuncts. One simply puts the (negated,
Skolemized) formula into clausal form, with say k conjuncts, and each new
ground instance generated just adds another k clauses to the accumulated
pile. Against this, of course, one needs a real satisfiability test algorithm to
be run, whereas in the Gilmore procedure this is simply a matter of looking
for complementary literals. Slightly anachronistically, we will use the DPLL
rather than the DP procedure, since our earlier experiments suggested it is
usually better, and it certainly has better space behaviour. The structure
of the Davis-Putnam program is very similar to the Gilmore one. This time
the stored formulas are all in CNF rather than DNF, and each time we
incorporate a new instance, we check for unsatisfiability using dpll:
The outer wrapper is unchanged except that the formula is put into CNF
rather than DNF:

> dpMfn :: Clauses -> (Formula -> Formula) -> Clauses -> Clauses
> dpMfn cjs0 ifn cjs = ListSet.union (map (map ifn) cjs0) cjs

> dpLoop :: Clauses -> [Term] -> [FuncA] -> Vars 
>           -> Int -> Clauses -> [[Term]] -> [[Term]] -> IO [[Term]] 
> dpLoop = herbloop dpMfn Dp.dpll

> davisputnam :: Formula -> IO Int
> davisputnam fm =
>   let sfm = Skolem.skolemize(Not(Fol.generalize fm)) 
>       fvs = Fol.fv sfm 
>       (consts, funcs) = herbfuns sfm
>       cntms = map (\(c,_) -> Fn c []) consts in -- image
>   do tms <- dpLoop (Prop.simpcnf sfm) cntms funcs fvs 0 [] [] []
>      return (length tms)

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Refined Davis-Putnam

Although the Davis-Putnam procedure avoids the catastrophic explosion
in memory usage that was the bane of the Gilmore procedure, it still often
generates a very large number of ground instances and becomes quite slow
at each propositional step. Typically most of these instances make no contribution
to the final refutation, and a much smaller set would be adequate.
The overall runtime (and ultimately feasibility) depends on how quickly an
adequate set turns up in the enumeration, which is quite unpredictable.
Suppose we define a function that runs through the list of possibly-needed
instances (dunno), putting them onto the list of needed ones need only if
the other instances are satisfiable:

> dpRefine :: Clauses -> Vars -> [[Term]] -> [[Term]] -> [[Term]] 
> dpRefine cjs0 fvs dunno need =
>   case dunno of
>     [] -> need
>     cl : dknow ->
>       let mfn = dpMfn cjs0 . Fol.apply . Map.fromList . zip fvs 
>           need' = if Dp.dpll(foldr mfn [] (need ++ dknow)) 
>                   then cl:need else need in
>       dpRefine cjs0 fvs dknow need'

We can use this refinement process after the main loop has succeeded:

> dpRefineLoop :: Clauses -> [Term] -> [FuncA] -> Vars 
>                 -> Int -> Clauses -> [[Term]] -> [[Term]] -> IO [[Term]]
> dpRefineLoop cjs0 cntms funcs fvs n cjs tried tuples =
>   do tups <- dpLoop cjs0 cntms funcs fvs n cjs tried tuples 
>      return (dpRefine cjs0 fvs tups [])

> davisputnam' :: Formula -> IO Int
> davisputnam' fm =
>   let sfm = Skolem.skolemize(Not(Fol.generalize fm)) 
>       fvs = Fol.fv sfm 
>       (consts, funcs) = herbfuns sfm 
>       cntms = map (\(c,_) -> Fn c []) consts in
>   do tms <- dpRefineLoop (Prop.simpcnf sfm) cntms funcs fvs 0 [] [] []
>      return (length tms)

