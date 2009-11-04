
* Signature

> module ATP.Resolution 
>   ( rename
>   , termMatch
>   , resolveClauses
>   , incorporate
>   , basicResolution
>   , resolution
>   , positiveResolution
>   , sosResolution
>   ) 
> where

* Imports

> import Prelude 
> import qualified ATP.FOL as FOL
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Prop as Prop
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Tableaux as Tableaux
> import qualified ATP.Unif as Unif
> import qualified ATP.Util.Lib as Lib
> import ATP.Util.Lib((↦))
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet ((\\))
> import qualified Data.List as List
> import qualified Data.Map as Map
> import qualified Data.Maybe as Maybe
> import qualified Text.Printf as T

* Resolution

In contrast with the top-down method of tableaux, all variable assignments
are local, so we actually want to translate the results of unification into
an instantiation for immediate application. Moreover, it’s convenient to
directly unify a set of literals rather than a list of equations between them:

> mgu :: Clause -> Env -> Maybe Env
> mgu (a:b:rest) env = case Tableaux.unifyLiterals env (a,b) of
>                        Nothing -> Nothing
>                        Just env' -> mgu (b:rest) env'
> mgu _ env = Unif.solve env

On the other hand, we’ll also use a simple test for unifiability, and there’s
no point here in fully expanding the unifier:

> unifiable :: Formula -> Formula -> Bool
> unifiable p q = Maybe.isJust (Tableaux.unifyLiterals Map.empty (p, q))

We’ll need to apply renaming to the hypothesis clauses. This is done via
the following function, which adds a prefix to each variable name in a clause:

> rename :: String -> Clause -> Clause
> rename pfx cls =
>   let fvs = FOL.fv(F.listDisj cls)
>       vvs = map (Var . (pfx ++)) fvs in
>             map (FOL.apply (Map.fromList (zip fvs vvs))) cls

We find all resolvents of two clauses cl1 and cl2 via an auxiliary function
that takes a particular literal p in cl1 and an accumulator acc of results
so far. First, all literals ps2 in cl2 that could possibly be unified with -p
are selected, and if there are none no resolvents are added. Otherwise we
filter out the literals ps1 in cl1 that are unifiable with p, other than p itself.
Then we form all possible pairs of nonempty subsets of ps1 and ps2, always
including p in the former. We then pick those pairs where ps1 ++ ps2− are
unifiable (just because each member of this set is in itself unifiable with p
doesn’t mean the whole set is). For each such pair we form the resolvent
and add it into the accumulator:

> resolvents :: Clause -> Clause -> Formula -> [Clause] -> [Clause]
> resolvents cl1 cl2 p acc = 
>   case filter (unifiable (F.opp p)) cl2 of
>     [] -> acc 
>     ps2 -> foldr foldFn acc pairs
>       where ps1 = filter (\q -> q /= p && unifiable p q) cl1
>             pairs = Lib.allPairs (,) (map (p:) (Set.allSubsets ps1))
>                                                (Set.allNonemptySubsets ps2) 
>             foldFn (s1, s2) sof = 
>               case mgu (s1 ++ map F.opp s2) Map.empty of
>                 Just env' -> 
>                   let cs = Set.union (cl1 \\ s1) (cl2 \\ s2) in
>                   Set.image (FOL.apply env') cs : sof
>                 Nothing -> sof 

The overall function to generate all possible resolvents of a set of clauses
now proceeds by renaming the input clauses and mapping the previous function
over all literals in the first clause:

> resolveClauses :: Clause -> Clause -> [Clause]
> resolveClauses cls1 cls2 = 
>   let cls1' = rename "x" cls1 
>       cls2' = rename "y" cls2 in
>   foldr (resolvents cls1' cls2') [] cls1' 

For the main loop of the resolution procedure, we simply keep generating
resolvents of existing clauses until the empty clause is derived. To avoid repeating
work, we split the clauses into two lists, used and unused. The main
loop consists of taking one given clause cls from unused, moving it to used
and generating all possible resolvents of the new clause with clauses from
used (including itself), appending the new clauses to the end of unused.
The idea is that, provided used is initially empty, every pair of clauses is
tried once: if clause 1 comes before clause 2 in unused, then clause 1 will
be moved to used and later clause 2 will be the given clause and have the
opportunity to participate in an inference. On the other hand, once they
have participated, both clauses are moved to used and will never be used
together again. (This organization, used in various resolution implementations
at the Argonne National Lab, is often referred to as the given clause
algorithm.)

> basicResloop :: ([Clause], [Clause]) -> IO ()
> basicResloop (used, unused) = case unused of 
>   [] -> T.printf "No proof found\n"
>   cl:ros -> do { T.printf (show (length used) ++ " used; " ++
>                            show (length unused) ++ " unused.\n")
>                ; let used' = Set.insert cl used 
>                      news = List.concat (map (resolveClauses cl) used') in
>                  if elem [] news then return () else basicResloop (used',ros++news)
>                }

> pureBasicResolution :: Formula -> IO ()
> pureBasicResolution fm = basicResloop ([], Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm)

Overall, we split up the formula, put it into clausal form and start the
main loop.

> basicResolution :: Formula -> IO ()
> basicResolution fm = 
>   let fm1 = Skolem.askolemize $ Not $ FOL.generalize fm in
>   do mapM_ (pureBasicResolution . F.listConj) (Prop.simpdnf fm1)
>      T.printf "Solution found!\n"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Subsumption

In order to implement a subsumption test, we first want a procedure for
matching, which is a cut-down version of unification allowing instantiation
of variables in only the first of each pair of terms. Note that in contrast to
unification we treat the variables in the two terms of a pair as distinct even
if their names coincide, and maintain the left-right distinction in recursive
calls. This means that we won’t need to rename variables first, and won’t
need to check for cycles. On the other hand, we must remember that apparently
‘trivial’ mappings x 7! x are in general necessary, so if x does not
have a mapping already and we need to match it to t, we always add x 7! t
to the function even if t = x. But stylistically, the definition is very close to
that of unify.

> termMatch :: Env -> [(Term, Term)] -> Maybe Env
> termMatch env [] = Just env
> termMatch env (h:oth) = 
>   case h of
>     (Fn f fargs, Fn g gargs) | (f == g && length fargs == length gargs) ->
>            termMatch env (zip fargs gargs ++ oth)
>     (Var x, t) -> case Map.lookup x env of 
>                     Nothing -> termMatch ((x ↦ t) env) oth
>                     Just t' | t == t' -> termMatch env oth
>                     _ -> Nothing
>     _ -> Nothing

We can straightforwardly modify this to attempt to match a pair of literals
instead of a list of pairs of terms:

> matchLiterals :: Env -> (Formula, Formula) -> Maybe Env
> matchLiterals env pq = case pq of
>   (Atom(R p a1), Atom(R q a2)) -> termMatch env [(Fn p a1, Fn q a2)] 
>   (Not(Atom(R p a1)), Not(Atom(R q a2))) -> termMatch env [(Fn p a1, Fn q a2)] 
>   _ -> Nothing

Now our subsumption test proceeds along the first clause cls1, systematically
considering all ways of instantiating the first literal to match one in
the second clause cls2, then, given the necessary instantiations, trying to
do likewise for the others.

> subsumesClause :: Clause -> Clause -> Bool
> subsumesClause cls1 cls2 = Maybe.isJust $ subsume Map.empty cls1
>   where subsume env [] = Just env
>         subsume env (l1:clt) =
>           Lib.findApply 
>             (\l2 -> case matchLiterals env (l1, l2) of
>                       Nothing -> Nothing
>                       Just env' -> subsume env' clt) cls2

... Thus, it seems that the policy of replacement, where the subsumed
clause is replaced by the subsuming one at the original point in the unused
list, is probably better, and this is what we will do. The following replace
function puts cl in place of the first clause in lis that it subsumes, or at
the end if it doesn’t subsume any of them.

> replace :: Clause -> Clauses -> Clauses
> replace cl [] = [cl]
> replace cl (c:cls) = if subsumesClause cl c then cl:cls 
>                      else c:replace cl cls

Now, the procedure for inserting a newly generated clause cl, generated
from given clause gcl, into an unused list is as follows. First we check if cl is
a tautology (using trivial) or subsumed by either gcl or something already
in unused, and if so we discard it. Otherwise we perform the replacement,
which if no back-subsumption is found will simply put the new clause at the
back of the list.

> incorporate :: Clause -> Clause -> Clauses -> Clauses
> incorporate gcl cl unused = 
>   if Prop.trivial cl || any (\c -> subsumesClause c cl) (gcl:unused)
>   then unused else replace cl unused

With the subsumption handling buried inside this auxiliary function, the
main loop is almost the same as before, with incorporate used iteratively
on all the newly generated clauses, rather than their simply being appended
at the end.

> resloop :: ([Clause], [Clause]) -> IO ()
> resloop (used, unused) = case unused of 
>   [] -> T.printf "No proof found\n"
>   cl:ros -> do { T.printf (show (length used) ++ " used; " ++
>                            show (length unused) ++ " unused.\n")
>                ; let used' = Set.insert cl used 
>                      news = List.concat (map (resolveClauses cl) used') in
>                  if elem [] news then return () 
>                  else resloop (used',foldr (incorporate cl) ros news)
>                }

> pureResolution :: Formula -> IO ()
> pureResolution fm = resloop ([], Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm)

Overall, we split up the formula, put it into clausal form and start the
main loop.

> resolution :: Formula -> IO ()
> resolution fm = 
>   let fm1 = Skolem.askolemize $ Not $ FOL.generalize fm in
>   do mapM_ (pureResolution . F.listConj) (Prop.simpdnf fm1)
>      T.printf "Solution found!\n"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Positive resolution

.. Thus we will modify the resolution prover with subsumption to
perform positive resolution. The modification is simplicity itself: we
restrict the core function resolve clauses so that it returns the
empty set unless one of the two input clauses is all-positive:

> presolveClauses :: Clause -> Clause -> [Clause]
> presolveClauses cls1 cls2 = 
>   if all F.positive cls1 || all F.positive cls2 
>   then resolveClauses cls1 cls2 else []

Now we simply re-enter the definition of resloop, this time calling it
presloop and replacing resolve clauses with presolve clauses, and
then define the positive variant of pure resolution in the same way:

> positiveResloop :: ([Clause], [Clause]) -> IO ()
> positiveResloop (used, unused) = case unused of 
>   [] -> T.printf "No proof found\n"
>   cl:ros -> do { T.printf (show (length used) ++ " used; " ++
>                            show (length unused) ++ " unused.\n")
>                ; let used' = Set.insert cl used 
>                      news = List.concat (map (presolveClauses cl) used') in
>                  if elem [] news then return () 
>                  else positiveResloop (used',foldr (incorporate cl) ros news)
>                }

followed by the same function with a different name:

> purePositiveResolution :: Formula -> IO ()
> purePositiveResolution fm = 
>   positiveResloop ([], Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm)

Overall, we split up the formula, put it into clausal form and start the
main loop.

> positiveResolution :: Formula -> IO ()
> positiveResolution fm = 
>   let fm1 = Skolem.askolemize $ Not $ FOL.generalize fm in
>   do mapM_ (purePositiveResolution . F.listConj) (Prop.simpdnf fm1)
>      T.printf "Solution found!\n"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Set of support

To implement the set-of-support restriction, we need no major changes
to the given clause algorithm: simply set the initial used to be the
unsupported clauses rather than the empty set. This precisely ensures
that two unsupported clauses are never resolved together.

One satisfactory choice for the set of support is the collection of allnegative
input clauses. This is because any set of clauses in which each
clause contains a positive literal is satisfiable (just interpret all predicates
as true everywhere), so the basic theoretical condition is satisfied. Thus we
make the following modification:

> pureSosResolution :: Formula -> IO ()
> pureSosResolution fm =
>   resloop (List.partition (any F.positive) 
>                        (Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm))

> sosResolution :: Formula -> IO ()
> sosResolution fm = 
>   let fm1 = Skolem.askolemize $ Not $ FOL.generalize fm in
>   do mapM_ (pureSosResolution . F.listConj) (Prop.simpdnf fm1)
>      T.printf "Solution found!\n"


