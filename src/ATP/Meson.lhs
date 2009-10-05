
MESON: Model Elimination Subgoal OrieNted

* Signature

> module ATP.Meson
>   ( mexpand
>   , contrapositives
>   , basicMeson
>   , meson
>   )
> where
  
* Imports
                      
> import Prelude 
> import qualified Data.List as List
> import qualified Data.Maybe as Maybe
> import qualified Data.Map as Map

> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))
> import ATP.FormulaSyn
> import qualified ATP.Formula as F
> import qualified ATP.Prop as Prop
> import qualified ATP.FOL as FOL
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Tableaux as Tableaux
> import qualified ATP.Prolog as Prolog
> import ATP.Prolog(Rule(Rule))

* MESON

We start with a function to map a clause into all its contrapositives. In line
with the discussion above, we only create an additional rule with Bot as the
conclusion if the original clause is all-negative:

> contrapositives :: Clause -> [Rule]
> contrapositives cls = 
>   let base = map (\c -> Rule (map F.opp (cls \\ [c])) c) cls in
>   if all F.negative cls then Rule (map F.opp cls) Bot : base else base

The main implementation is not far from Prolog, but to make later
extensions easier we use the current goal g and a continuation
function cont to solve remaining subgoals, rather than simply a list
of subgoals. A triple consisting of the current instantiation env, the
maximum number n of additional nodes in the proof tree permitted, and
a counter k for variable renaming are passed through the chain of
continuations. Each goal g also has associated with it the list of
ancestor goals.  

The actions required are simple. If the current size bound has been
exceeded, we fail. Otherwise, we first try to unify the current goal
with the negation of one of its ancestors (not renaming variables of
course since this is a global method) and call cont to solve the
remaining goals under the new instantiation. If this fails, we try a
normal Prolog-style extension with one of the rules, first unifying
with a renamed rule and then iterating the same goal-solving operation
over the list of subgoals, modifying the environment according to the
results of unification, decreasing the permissible number of new nodes
by the number of new subgoals created, and appropriately increasing
the variable renaming counter.

> basicMexpand :: [Rule] -> [Formula] -> Formula 
>         -> ((Env, Int, Int) -> Maybe a) -> (Env, Int, Int) -> Maybe a
> basicMexpand rules ancestors g cont (env, n, k) =
>   if n < 0 then fail "Too deep"  else
>   let findFn a = do env' <- Tableaux.unifyLiterals env (g, F.opp a) 
>                     cont (env', n, k) in
>   case Lib.findApply findFn ancestors of
>     Just env' -> Just env'
>     Nothing -> 
>       let findFn2 rule = 
>             let (Rule asm c, k') = Prolog.renamer k rule in
>             do env' <- Tableaux.unifyLiterals env (g,c)
>                foldr (basicMexpand rules (g:ancestors)) 
>                  cont asm (env', n - length asm, k') in
>       Lib.findApply findFn2 rules 

This can now be packaged up into the overall function with the usual
iterative deepening. As with tableaux, we split the input problem into
subproblems as much as possible. This is particularly worthwhile here
when we reduce the problem to clausal form, since otherwise the
translated form often becomes significantly more complicated.

> pureBasicMeson :: Formula -> IO Int
> pureBasicMeson fm = 
>   let cls = Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm 
>       rules = concat (map contrapositives cls) in
>   Tableaux.deepen (\n -> do basicMexpand rules [] Bot Just (Map.empty, n, 0) 
>                             return n) 0

The overall function starts with the usual generalization, negation and
Skolemization, then attempts to refute the clauses using MESON:

> basicMeson :: Formula -> IO [Int]
> basicMeson fm = 
>   let fm1 = Skolem.askolemize $ Not $ FOL.generalize fm in
>   mapM (pureBasicMeson . F.listConj) (Prop.simpdnf fm1)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Optimization

Effective though it usually is, there are several ways in which the
MESON implementation above can be improved. One simple observation is
that we need never repeat a subgoal on a branch, so that if a current
goal has an identical ancestor, we can always fail; any expansion done
from the current goal could more efficiently be done starting from the
identical ancestor. It is not difficult to test whether two literals
are identical under an existing set of assignments. Rather than code
it explicitly, we can simply call the unification function and see
that no additional assignments are returned.

> equal :: Env -> Formula -> Formula -> Bool
> equal env fm1 fm2 = 
>   case Tableaux.unifyLiterals env (fm1, fm2) of
>     Nothing -> False
>     Just env' -> env == env'

As well as incorporating this test, we can make some more substantial
changes to the search strategy. One quite simple and effective
alternative (Harrison 1996b) is to distribute the available size bound
over subgoals more efficiently. Note that given a current size bound
of n to solve two subgoals g1 and g2, one subgoal or the other must be
solvable with size <= n/2 (where division truncates downwards if n is
odd). Thus, rather than immediately making the full bound of n
available for g1 then solving g2 with what’s left, we can try solving
g1 with size limit n/2 and then g2 with what’s left of the overall n,
and if that fails (or the rest of the goals cannot be solved under any
of the resulting instantiations), reverse the roles of g1 and g2 and
try it that way round. This applies equally well if any number of
subgoals are divided approximately equally into two lists of subgoals.

Since the search space typically grows exponentially, this
optimization is likely to result in an overall saving even though
solutions where both g1 and g2 are solvable with size <= n/2 will be
found twice. We just want to ensure that this duplication doesn’t
cause all the other goals to be attempted twice with the same
instantiations, otherwise there could be an exponential explosion of
duplicated work. Thus, the continuation must sometimes be ignored if a
solution is found with too few steps. The following function is
intended to take a basic expansion function expfn for lists of
subgoals and apply it to goals1 with size limit n1, then attempt
goals2 with whatever is left over from goals1 plus an additional n2,
yet force the continuation to fail unless the second takes more than
n3.

> expand2 :: ([Formula] -> ((Env, Int, Int) -> Maybe a) -> (Env, Int, Int) -> Maybe a) 
>         -> [Formula] -> Int -> [Formula] -> Int -> Int 
>         -> ((Env, Int, Int) -> Maybe a) -> Env -> Int -> Maybe a
> expand2 expfn goals1 n1 goals2 n2 n3 cont env k =
>   expfn goals1 (\(e1,r1,k1) ->
>        expfn goals2 (\(e2,r2,k2) ->
>                        if n2 + r1 <= n3 + r2 then Nothing
>                        else cont(e2,r2,k2))
>               (e1,n2+r1,k1))
>        (env,n1,k)

First, goals1 is attempted with limit n1 and the unused size r1 is
captured before proceeding to goals2. They are solved with limit
n2+r1, leaving r2 of this limit. Now, we want to ensure that more than
n3 steps were used for goals2, so we only call the continuation if (n2
+ r1) − r2 > n3 and fail otherwise. The overall MESON expansion is
now done via two mutually recursive procedures, mexpand dealing with a
single subgoal and mexpands with a list of subgoals. The mexpand
function starts as before with a check for exceeding the size bound
and an attempt at ancestor unification, though it also makes a
repetition check using equal. However, when expanding using a rule,
control is then passed to mexpands to deal with the multiple subgoals.

> mexpand ::  [Rule] -> [Formula] -> Formula
>         -> ((Env, Int, Int) -> Maybe a) -> (Env, Int, Int) -> Maybe a
> mexpand rules ancestors g cont (env,n,k) =
>   if n < 0 then fail "Too deep"
>   else if any (equal env g) ancestors then fail "repetition" else
>   case Lib.findApply (\a -> do env' <- Tableaux.unifyLiterals env (g,F.opp a)
>                                cont (env' ,n, k)) ancestors of
>     Just e -> Just e
>     Nothing -> Lib.findApply findFn rules
>         where findFn r = let (Rule asm c, k') = Prolog.renamer k r in
>                          do env' <- Tableaux.unifyLiterals env (g,c)
>                             mexpands rules (g:ancestors) asm cont 
>                                      (env',n-length asm,k')

In mexpands, if there are too many new subgoals for the current size limit,
we fail at once, and if there is at most one new subgoal, we deal with it in
the same way as before. Only if there are at least two do we initiate the
optimization. The total available limit n is split into two roughly equal parts
n1 and n2, and the list of subgoals is itself chopped in two, giving goals1
and goals2. We try solving goals1 first with size n1 and then goals2 with
the remainder plus n2, with no lower limit (hence the -1), and if that fails,
try it the other way round, this time imposing a lower limit n1 to avoid
running the continuation twice.

> mexpands :: [Rule] -> [Formula] -> [Formula] 
>          -> ((Env, Int, Int) -> Maybe a) -> (Env, Int, Int) -> Maybe a
> mexpands rules ancestors gs cont (env,n,k) =
>   if n < 0 then fail "Too deep" else
>   let m = length gs in
>   if m <= 1 then foldr (mexpand rules ancestors) cont gs (env,n,k) else
>   let n1 = n `div` 2 
>       n2 = n - n1 
>       (goals1,goals2) = splitAt (m `div` 2) gs 
>       expfn = expand2 (mexpands rules ancestors) in
>   case expfn goals1 n1 goals2 n2 (-1) cont env k of
>     Just e -> Just e
>     Nothing -> expfn goals2 n1 goals1 n2 n1 cont env k

> pureMeson :: Formula -> IO Int
> pureMeson fm = 
>   let cls = Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm 
>       rules = concat (map contrapositives cls) in
>   Tableaux.deepen (\n -> do mexpand rules [] Bot Just (Map.empty, n, 0) 
>                             return n) 0

> meson :: Formula -> IO [Int]
> meson fm = 
>   let fm1 = Skolem.askolemize $ Not $ FOL.generalize fm in
>   mapM (pureMeson . F.listConj) (Prop.simpdnf fm1)
