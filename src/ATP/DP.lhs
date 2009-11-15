
The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.

* Signature

> module ATP.Dp
>   ( dp
>   , dptaut
>   , dpll
>   , dplltaut
>   ) 
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude 
> import qualified ATP.DefCnf as Cnf
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Prop as Prop
> import qualified ATP.Util.List as List
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))

* Davis-Putnam

The One Literal Rule

This rule can be applied whenever one of the clauses is a unit clause,
i.e.  simply a single literal rather than the disjunction of more than
one. If p is such a unit clause, we can get a new formula by:

  Removing any instances of −p from the other clauses.  Removing any
  clauses containing p, including the unit clause itself.

We will show later that this transformation preserves
satisfiability. The 1- literal rule is also called unit propagation
since it propagates the information that p is true into the the other
clauses. To implement it in the list-of-lists representation, we
search for a unit clause, i.e. a list of length 1, and let u be the
sole literal in it and u’ its negation. Then we first remove all
clauses containing u and then remove u’ from the remaining clauses.

Note that even if there is only one unit clause in the initial
formula, an application of the rule may itself create more unit
clauses by deleting other literals.

> oneLiteralRule :: Clauses -> Maybe Clauses
> oneLiteralRule clauses = 
>   case List.find (\cl -> length cl == 1) clauses of
>     Nothing -> Nothing
>     Just [u] -> Just (Set.image (\\ [u']) clauses1) 
>       where u' = F.opp u
>             clauses1 = filter (not . elem u) clauses 
>     _ -> __IMPOSSIBLE__ 

The affirmative-negative rule

This rule, also sometimes called the pure literal rule, exploits the
fact that if any literal occurs either only positively or only
negatively, then we can delete all clauses containing that literal
while preserving satisfiability. For the implementation, we
start by collecting all the literals together and partitioning them
into positive (pos) and negative (neg'). From these we obtain the
literals pure that occur either only positively or only negatively,
then eliminate all clauses that contain any of them.

If any valuation satisfies the original set of clauses, then it must
also satisfy the new set, which is a subset of it. Conversely, if a
valuation v satisfies the new set, we can modify it to set v0(p) =
true for all positive-only literals p in the original and v0(n) =
false for all negative-only literals ¬n, setting v0(a) = v(a) for all
other atoms. By construction this satisfies the deleted clauses, and
since it does not change the assignment to any atom occurring in the
final clauses, satisfies them too and hence the original set of
clauses.

> affirmativeNegativeRule :: Clauses -> Maybe Clauses
> affirmativeNegativeRule clauses = 
>   let (neg', pos) = List.partition F.negative (Set.unions clauses)
>       neg = map F.opp neg'
>       posOnly = pos \\ neg
>       negOnly = neg \\ pos
>       pure = Set.union posOnly (map F.opp negOnly) in
>   case pure of
>     [] -> Nothing
>     _ -> Just (filter (\cl -> null $ Set.intersect cl pure) clauses)

Rule for eliminating atomic formulas

This rule is the only one that can make the formula increase in size,
and in the worst case the increase can be substantial. However, it
completely eliminates some particular atom from consideration, without
any special requirements on the clauses that contain it. The rule is
parametrized by a literal p that occurs positively in at least one
clause and negatively in at least one clause. 

In practice, we will only apply the resolution rule after the 1-literal and
affirmative-negative rules have already been applied. In this case we can
assume that any literal present occurs both positively and negatively, and
are faced with a choice of which literal to resolve on. Given a literal l, we
can predict the change in the number of clauses resulting from resolution on
l:

> findBlowup :: Clauses -> Formula -> (Int, Formula)
> findBlowup cls l = 
>   let m = length(filter (elem l) cls)
>       n = length(filter (elem (F.opp l)) cls) in
>   (m * n - m - n, l)

We will pick the literal that minimizes this blowup. (While this looks
plausible, it is simplistic; much more sophisticated heuristics are possible
and perhaps desirable.)

> resolutionRule :: Clauses -> Clauses
> resolutionRule clauses = 
>   let pvs = filter F.positive (Set.unions clauses)
>       lblows = map (findBlowup clauses) pvs
>       (_, p) = List.minimum lblows in
>   resolveOn p clauses

> resolveOn :: Formula -> Clauses -> Clauses
> resolveOn p clauses =
>   let p' = F.opp p 
>       (pos, notpos) = List.partition (elem p) clauses 
>       (neg, other) = List.partition (elem p') notpos
>       pos' = map (filter (/= p)) pos
>       neg' = map (filter (/= p')) neg
>       res0 = List.allPairs Set.union pos' neg' in
>   Set.union other (filter (not . Prop.trivial) res0)

Davis-Putnam procedure

The main DP procedure is defined recursively. It terminates if the set of
clauses is empty (returning true since that set is trivially satisfiable) or
contains the empty clause (returning false for unsatisfiability). Otherwise,
it applies the first of the rules I, II and III to succeed and then continues
recursively on the new set of clauses.† This recursion must terminate, for
each rule either decreases the number of distinct atoms (in the case of III,
assuming that tautologies are always removed first) or else leaves the number
of atoms unchanged but reduces the total size of the clauses.

> dp :: Clauses -> Bool
> dp [] = True
> dp clauses = if elem [] clauses then False else
>              case oneLiteralRule clauses of
>                Just clauses' -> dp clauses'
>                Nothing -> 
>                  case affirmativeNegativeRule clauses of
>                  Just clauses' -> dp clauses'
>                  Nothing -> dp(resolutionRule clauses)

> dpsat :: Formula -> Bool
> dpsat = dp . Cnf.defcnfs

> dptaut :: Formula -> Bool
> dptaut = not . dpsat . Not

Davis-Putnam-Loveland-Logemann procedure

For more challenging problems, the number and size of the clauses
generated in the DP procedure can grow enormously, and may exhaust
available memory before a decision is reached. This effect was even
more pronounced on the early computers available when the DP algorithm
was developed, and it motivated Davis, Logemann, and Loveland (1962)
to replace the resolution rule III with a splitting rule. If neither
of the rules I and II is applicable, then some literal p is chosen and
the satisfiability of a clause set A is reduced to the satisfiability
of −p:A and of p:A, which are tested separately.  Note that this
preserves satisfiability: A is satisfiable if and only if one of -p:A
and p:A is, since any valuation must satisfy either −p or p.
The new unit clauses will then immediately be used by the 1-literal
rule to simplify the clause set. Since this step reduces the number of
atoms, the termination of the procedure is guaranteed.  A reasonable
choice of splitting literal seems to be the one that occurs most often
(either positively or negatively), since the subsequent unit
propagation will then cause the most substantial simplification.†
Accordingly we define the analogue of the DP procedure’s
resolution_blowup:

> findCount :: Clauses -> Formula -> (Int, Formula)
> findCount cls l =
>   let m = length(filter (elem l) cls)
>       n = length(filter (elem (F.opp l)) cls) in
>   (m + n, l)

Now the basic algorithm is as before except that the resolution rule is
replaced by a case-split:

> dpll :: Clauses -> Bool
> dpll [] = True
> dpll clauses = 
>   if elem [] clauses then False else
>   case oneLiteralRule clauses of
>     Just clauses' -> dpll clauses'
>     Nothing -> 
>       case affirmativeNegativeRule clauses of
>       Just clauses' -> dpll clauses'
>       Nothing -> 
>         let pvs = filter F.positive (Set.unions clauses) 
>             lcounts = map (findCount clauses) pvs 
>             (_, p) = List.maximum lcounts in
>         dpll (Set.insert [p] clauses) 
>         || dpll (Set.insert [F.opp p] clauses)

> dpllsat :: Formula -> Bool
> dpllsat = dpll . Cnf.defcnfs

> dplltaut :: Formula -> Bool
> dplltaut = not . dpllsat . Not
