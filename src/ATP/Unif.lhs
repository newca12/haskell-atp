
Unification

* Signature

> module ATP.Unif
>   ( unify
>   , solve
>   , fullunify
>   , unifyAndApply
>   )
> where

* Imports

> import Prelude 
> import qualified ATP.Fol as Fol
> import ATP.FormulaSyn
> import ATP.Util.Lib((↦))
> import qualified Data.Map as Map

* Unification

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Unification

Let us now turn to a general method for solving a unification problem or
deciding that it has no solution. Our main function unify is recursive, with
two arguments, env, which is a finite partial function from variables to terms,
and eqs, which is a list of term-term pairs to be unified. The unification
function essentially applies some transformations to eqs and incorporates
the resulting variable-term mappings into env. This env is not quite the final
unifying mapping itself, because it may map a variable to a term containing
variables that are themselves assigned, e.g. x |-> y and y |-> z instead of just
x |-> z directly. But we will require env to be free of cycles. Write x ---> y
to indicate that there is an assignment x |-> t in env with y \in FVT(t). By
a cycle, we mean a nonempty finite sequence leading back to the starting
point:
x0 ---> x1 ---> ... ---> xp ---> x0
Our main unification algorithm will only incorporate new entries x |-> t
into env that preserve the property of being cycle-free. It is sufficient to
ensure the following:
(1) There is no existing assignment x |-> s in env.
(2) There is no variable y \in FVT(t) such that y ---> x, i.e. there is a sequence
of zero or more --->-steps leading from y to x; in particular x \not\in FVT(t).

To see that if env is cycle-free and these properties hold then (x |-> t)env
is also cycle-free, note that if there were now a cycle for the new relation
--->': 

z --->' x1 --->' ... --->' xp --->' z

then there must be one of the following form:
z ---> x1 ---> x --->0 y ---> . . . ---> xp ---> z
for some y 2 FVT(t). For there must be at least one case where the new
assignment x 7! t plays a role, since env was originally cycle-free, while if
there is more than one instance of x, we can cut out any intermediate steps
between the first and the last. However, a cycle of the above form also gives
us the following, contradicting assumption (2):
y ---> . . . ---> xp ---> z ---> x1 ---> x

The following function will return `false' if condition (2) above holds for
a new assignment x |-> t. If condition (2) does not hold then it fails, except
in the case t = x when it returns `true', indicating that the assignment is
`trivial'.

> istriv :: Env -> Var -> Term -> Maybe Bool
> istriv env x (Var y) = 
>   if x == y then Just True else
>   case Map.lookup y env of
>     Nothing -> Just False
>     Just t -> istriv env x t
> istriv env x (Fn _ args) = 
>   if any (\t -> case istriv env x t of -- occurs check
>                   Just False -> False
>                   _ -> True) args 
>   then Nothing else Just False

This is effectively calculating a reflexive-transitive closure of |−>, which
could be done much more efficiently. However, this simple recursive implementation
is usually fast enough, and is certainly guaranteed to terminate,
precisely because the existing env is cycle-free.

Now we come to the main unification function. This just transforms the
list of pairs eqs from the front using various transformations until the front
pair is of the form (x, t). If there is already a definition x |-> s in env, then
the pair is expanded into (s, t) and the recursion proceeds. Otherwise we
know that condition (1) holds, so x |-> t is a candidate for incorporation
into env. If there is a benign cycle istriv env x t is true and env is
unchanged. Any other kind of cycle will cause failure, which will propagate
out. Otherwise condition (2) holds, and x |-> t is incorporated into env for
the next recursive call.

> unify :: Env -> [(Term, Term)] -> Maybe Env
> unify env eqs = case eqs of 
>   [] -> Just env 
>   (Fn f fargs, Fn g gargs):rest -> 
>     if f == g && length fargs == length gargs then 
>        unify env (zip fargs gargs ++ rest)
>     else Nothing
>   (Var x, t) : rest -> unifyVar x t rest
>   (t, Var x) : rest -> unifyVar x t rest
>   where unifyVar x t rest = 
>           case Map.lookup x env of
>             Just t' -> unify env ((t', t) : rest)
>             Nothing -> case istriv env x t of
>                          Just True -> unify env rest
>                          Just False -> unify ((x ↦ t) env) rest
>                          Nothing -> Nothing

We will next show that successful termination of unify indicates that
there is a unifier of the initial set of pairs, and in fact that a most general
unifier can be obtained from the resulting env by applying the following
function to reach a ‘fully solved’ form:

> solve :: Env -> Maybe Env
> solve env = solve' env (Map.toList env)

> solve' :: Env -> [(Var, Term)] -> Maybe Env
> solve' env fs = 
>   if any (\(x,t) -> elem x (Fol.fv t)) fs
>   then Nothing else 
>   let env' = foldr (\(x,t) -> Map.insert x (Fol.apply env t)) Map.empty fs
>       fs' = Map.toList env' in
>   if fs == fs' then Just env else solve' env' fs'

We can now finally package up everything as a function that solves the
unification problem completely and creates an instantiation.

> fullunify :: [(Term, Term)] -> Maybe Env
> fullunify eqs = do env <- unify Map.empty eqs 
>                    solve env

For example, we can use this to find a unifier for a pair of terms, then
apply it, to check that the terms are indeed unified

> unifyAndApply :: [(Term, Term)] -> Maybe [(Term, Term)] 
> unifyAndApply eqs = 
>   do env <- fullunify eqs 
>      let apply (t1, t2) = (Fol.apply env t1, Fol.apply env t2) in
>        return $ map apply eqs
>        
