
* Signature

> module ATP.Tableaux
>   ( unifyLiterals
>   , deepen
>   , prawitz
>   , tab
>   , splittab
>   )
> where

* Imports

> import ATP.Util.Prelude 
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Prop as Prop
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Unif as Unif
> import qualified ATP.Util.Lib as Lib
> import ATP.Util.Lib((⟾))
> import qualified ATP.Util.List as List
> import qualified ATP.Util.ListSet as Set
> import qualified ATP.Util.Log as Log
> import ATP.Util.Log(Log)
> import qualified Data.List as List
> import qualified Data.Map as Map

* Tableaux

We will maintain the environment of variable assignments globally,
represented as a cycle-free finite partial function just as in unify
itself. To unify atomic formulas, we just treat the predicates as if
they were functions then use the existing unification code, and we
also deal with negation by recursion, and handle the degenerate case
of Bot since we will use this later:

> unifyLiterals :: Env -> (Formula, Formula) -> Maybe Env
> unifyLiterals env pq = case pq of
>   (Atom(R p1 a1), Atom(R p2 a2)) -> Unif.unify env [(Fn p1 a1, Fn p2 a2)]
>   (Not p, Not q) -> unifyLiterals env (p, q)
>   (Bot, Bot) -> Just env
>   _ -> Nothing 

To unify complementary literals, we just first negate one of them:

> unifyComplements :: Env -> (Formula, Formula) -> Maybe Env
> unifyComplements env (p, q) = unifyLiterals env (p, F.opp q)

Next we define a function that iteratively runs down a list
(representing a disjunction), trying all possible complementary pairs
in each member, unifying them and trying to finish the remaining items
with the instantiation so derived. Each disjunct d is itself an
implicitly conjoined list, so we separate it into positive and
negative literals, and for each possible positive-negative pair,
attempt to unify them as complementary literals and solve the
remaining problem with the resulting instantiation.

> unifyRefute :: [[Formula]] -> Env -> Maybe Env
> unifyRefute [] env = Just env
> unifyRefute (d:odjs) env = 
>   let (pos, neg) = List.partition F.positive d 
>       pairs = List.allPairs (,) pos neg 
>       findFn pq = do env' <- unifyComplements env pq 
>                      unifyRefute odjs env'
>   in List.findFirst findFn pairs

Now for the main loop, we maintain the original DNF of the
uninstantiated formula djs0, the set fvs of its free variables, and a
counter n used to generate the fresh variable names as needed. The
main loop creates a new substitution instance using fresh variables
newvars, and incorporates this into the previous DNF djs to give
djs1. The refutation of this DNF is attempted, and if it succeeds, the
final instantiation is returned together with the number of instances
tried (the counter divided by the number of free
variables). Otherwise, the counter is increased and a larger
conjunction tried. Because this approach is quite close to the
pioneering work by Prawitz, Prawitz, and Voghera (1960), we name the
procedure accordingly.

> prawitzLoop :: [[Formula]] -> Vars -> [[Formula]] 
>             -> Int -> Maybe (Env, Int)
> prawitzLoop djs0 fvs djs n = 
>   let l = length fvs
>       newvars = map (\k -> Var ("_" ++ show (n * l + k))) [1 .. l]
>       inst = Map.fromList (zip fvs newvars)
>       djs1 = Prop.distrib (Set.image (Set.image (Fol.apply inst)) djs0) djs in
>   case unifyRefute djs1 Map.empty of
>     Just env -> Just (env, n+1)
>     Nothing -> prawitzLoop djs0 fvs djs1 (n+1)

> prawitz :: Formula -> Maybe Int
> prawitz fm = 
>   let fm0 = Skolem.skolemize $ Not $ Fol.generalize fm in
>   case prawitzLoop (Prop.simpdnf fm0) (Fol.fv fm0) [[]] 0 of
>     Nothing -> Nothing
>     Just (_, n) -> Just n

Although the prawitz procedure is usually far more effcient than
gilmore, some further improvements are worthwhile. In prawitz we
prenexed the formula and replaced formerly universally quantified
variables with fresh ones at once, then expanded the DNF
completely. Instead, we can do all these things incrementally. Suppose
we have a set of assumptions to refute.  If it contains two
complementary literals p and 􀀀p, we are already done.  Otherwise we
pick a non-atomic assumption and deal with it as follows:

  1) For p ^ q, separately assume p and q.
  2) For p _ q, perform two refutations, one assuming p and one assuming q.
  3) For forall x. P[x], introduce a new variable y and assume P[y], but also keep

the original forall x. P[x] in case multiple instances are needed.
This is essentially the method of analytic tableaux. (Analytic because
the new formulas assumed are subformulas of the current formula, and
tableaux because they systematically lay out the assumptions and case
distinctions to be considered.) When used on paper, it's traditional
to write the current assumptions along a branch of a tree, extending
the branch with the new assumptions and splitting it into two
sub-branches when handling disjunctions.  In our implementation, we
maintain a `current' disjunct, which we separate into its literals
(lits) and other conjuncts not yet broken down to literals (fms),
together with the remaining disjuncts that we need to refute.  Rather
than maintain an explicit list for the last item, we use a
continuation (cont). A continuation merely encapsulates the remaining
computation as a function, in this case one that is intended to try
and refute all remaining disjuncts under the given
instantiation. Initially this continuation is just the identity
function, and as we proceed, it is augmented to `remember' what more
remains to be done.  Rather than bounding the number of instances, we
bound the number of universal variables that have been replaced with
fresh variables by a limit n. The other variable k is a counter used
to invent new variables when eliminating a universal quantifier. This
must be passed together with the current environment to the
continuation, since it must avoid re-using the same variable in later
refutations.

> tableau :: ([Formula], [Formula], Int) 
>         -> ((Env, Int) -> Maybe a) -> (Env, Int) -> Maybe a
> tableau (fms, lits, n) cont (env, k) = 
>   if n < 0 then Nothing else
>   case fms of 
>     [] -> Nothing
>     And p q : unexp -> tableau (p:q:unexp, lits, n) cont (env, k)
>     Or p q : unexp -> tableau (p:unexp, lits, n) (tableau (q:unexp, lits, n) cont) (env, k)
>     fm @ (All x p) : unexp -> 
>            let y = Var("_" ++ show k) 
>                p' = Fol.apply (x ⟾ y)  p in
>                     tableau (p':unexp ++ [fm], lits, n-1) cont (env, k+1)
>     fm:unexp -> 
>       let findFn l = do env' <- unifyComplements env (fm,l) 
>                         cont(env', k) in
>       case List.findFirst findFn lits of
>         Just x -> Just x
>         Nothing -> tableau (unexp, fm:lits, n) cont (env,k)

> deepen :: Log m => (Int -> Maybe a) -> Int -> m a
> deepen f n = do 
>   Log.infoM "deepen" $ "Searching with depth limit " ++ show n
>   case f n of
>     Just x -> return x
>     Nothing -> deepen f (n+1)

> tabrefute :: Log m => [Formula] -> m Int
> tabrefute fms =
>   let tabFn n = do tableau (fms, [], n) Just (Map.empty, 0) 
>                    return n in
>   deepen tabFn 0

> tab :: Log m => Formula -> m Int
> tab fm = 
>   let sfm = Skolem.askolemize $ Not $ Fol.generalize fm in
>   if sfm == Bot then return 0 else tabrefute [sfm]

> splittab :: Log m => Formula -> m [Int]
> splittab = mapM tabrefute . Prop.simpdnf . Skolem.askolemize 
>            . Not . Fol.generalize
