

* Signature

> module ATP.Cooper
>   ( zero
>   , one
>   , isInteger
>   , integer1
>   , integer2
>   , destInteger
>   , evalc
>   , integerQelim
>   , naturalQelim
>   )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Order as Order
> import qualified ATP.Qelim as Qelim
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Util.ListSet as Set
> import qualified ATP.Util.Print as PP
> import qualified Data.List as List
> import qualified Data.Maybe as Maybe
> import qualified Ratio
> import Ratio ((%))

* Numerals

We have a special abbreviation zero for the integer constant term 0, since
we use it quite often.

> zero :: Term
> zero = Num 0

> one :: Term
> one = Num 1

The following functions convert between terms that are integer constants
and Haskell unlimited-precision numbers, and test whether a term is indeed
an integer constant.

> makeInteger :: Integer -> Term
> makeInteger n = Num $ n Ratio.% 1

> isInteger :: Term -> Bool
> isInteger (Num n) = Ratio.denominator n == 1
> isInteger _ = False

> destInteger :: Term -> Integer
> destInteger (Num n) = 
>   if Ratio.denominator n == 1 then Ratio.numerator n
>   else error "non-integral rational"
> destInteger t = error' $ PP.text "illegal integer:" <+> pPrint t

Using these functions we can take an arbitrary unary or binary operation
on OCaml numbers, such as negation or addition, and lift it to an operation
on numeral constants.

> integer1 :: (Integer -> Integer) -> Term -> Term
> integer1 fn = makeInteger . fn . destInteger

> integer2 :: (Integer -> Integer -> Integer) -> Term -> Term -> Term
> integer2 fn m n = makeInteger $ fn (destInteger m) (destInteger n)

* Arithmetic on canonical terms

As noted, we allow multiplication by numeral constants. Indeed, it makes
the transformations involved in quantifier elimination easier to implement if
we always keep terms in a canonical form:
c1 · x1 + · · · + cn · xn + k
where n  0, ci and k are integer constants, and the xi are distinct variables,
with a fixed order. We insist that ci are present even if they are 1, but that
they are never 0, and that k is present even if it is zero. Thus, a canonical
term is a constant precisely if the top-level operator is not addition.
We need two main operations on terms in canonical form: multiplication
by an integer constant, and addition. The former just amounts to multiplying
up all the coefficients:
n · (c1 · x1 + · · · + cn · xn + k) = (n · c1) · x1 + · · · + (n · cn) · xn + (n · k)
unless n = 0, in which case we should just return 0. This can be implemented
as a simple recursion:

> linearCmul :: Integer -> Term -> Term
> linearCmul 0 _ = zero
> linearCmul n tm = 
>   case tm of 
>     [$term| $c * $x + $r |] -> integer1 ((*) n) c * x + linearCmul n r
>     k -> integer1 ((*) n) k

For addition, we need to merge together the sequences of variables, maintaining
the fixed order. We assume that this order is defined by a list of
variable names, and use earlier to tell us whether element x comes earlier
than element y in such a list. The first clause corresponds to a term addition
(c1 ·x1+r1)+(c2 ·x2+r2) and the action taken depends on the relationship
of the variables x1 and x2. If they are equal, then the coefficients are added
and the remainders dealt with recursively. (Note that if the coefficients cancel,
we do not include that term in the result, since we wanted all the ci to
be nonzero.) Otherwise, whichever variable takes precedence is put at the
head of the output term and recursion proceeds; this is also the action on
the other clauses where one term or the other is a constant term. Finally, if
both terms are constants they are just added as numerals.

> linearAdd :: Vars -> Term -> Term -> Term
> linearAdd vars tm1 tm2 =
>   case (tm1, tm2) of 
>     ([$term| $c1 * ^x1 + $r1 |], [$term| $c2 * ^x2 + $r2|]) -> 
>        if x1 == x2 then
>          let c = integer2 (+) c1 c2 in
>          if c == zero then linearAdd vars r1 r2
>          else c * Var x1 + linearAdd vars r1 r2
>        else if Order.earlier vars x1 x2 then
>          c1 * Var x1 + linearAdd vars r1 tm2
>        else
>          c2 * Var x2 + linearAdd vars tm1 r2
>     ([$term| $c1 * ^x1 + $r1 |], _) -> c1 * Var x1 + linearAdd vars r1 tm2
>     (_, [$term| $c2 * ^x2 + $r2 |]) -> c2 * Var x2 + linearAdd vars tm1 r2
>     _ -> integer2 (+) tm1 tm2

Using these basic functions, it's easy to define negation and subtraction
on canonical forms:

> linearNeg :: Term -> Term
> linearNeg = linearCmul (-1)

> linearSub :: Vars -> Term -> Term -> Term
> linearSub vars tm1 tm2 = linearAdd vars tm1 (linearNeg tm2)

and we can even define multiplication of any two canonical terms, though it
will fail unless at least one is just a constant:

> linearMul :: Term -> Term -> Term
> linearMul tm1 tm2 = 
>   if isInteger tm1 then linearCmul (destInteger tm1) tm2
>   else if isInteger tm2 then linearCmul (destInteger tm2) tm1
>   else error ("linearMul: nonlinearity: (" ++ show tm1 ++ ", " ++ show tm2 ++ ")")

In order to convert any permissible term into canonical form, we proceed
by recursion, applying one of the arithmetic operations just defined to the
340 Decidable problems
translated subexpressions (allowing multiplication only if one side is simply
a numeral), leaving numeral constants unchanged and converting variables
from x into their canonical form 1 · x + 0:

> lint :: Vars -> Term -> Term
> lint vars tm =
>   case tm of
>    [$term| ^_ |] -> one * tm + zero
>    [$term| - $t |] -> linearNeg (lint vars t)
>    [$term| $s + $t |] -> linearAdd vars (lint vars s) (lint vars t)
>    [$term| $s - $t |] -> linearSub vars (lint vars s) (lint vars t)
>    [$term| $s * $t |] -> linearMul (lint vars s) (lint vars t)
>    _ -> if isInteger tm then tm else error $ "lint: unknown term: " ++ show tm

We next extend this linearization to atomic formulas; this will eventually
be plugged into lift qelim as the parameter afn. We force both equations
and inequalities to have zero on the LHS, e.g. transforming s = t to 0 = s􀀀t
and s < t to 0 < t􀀀s; this makes some later code more regular since in the
case of djt the `interesting' term is also the right-hand argument. Because
the integers are a discrete structure, we take the chance to rewrite all the
atomic inequality formulas in terms of <, e.g. s  t as 0 < (t + 1) 􀀀 s. And
finally, we also force the left-hand constants in divisibility assertions to be
positive. We start with a simple helper function mkatom to linearize a term
and create an atom with that as the left-hand argument and zero as the
other:

> mkatom :: Vars -> Pred -> Term -> Formula 
> mkatom vars p t = Atom (R p [zero, lint vars t])

Now the main function is straightforward case-by-case modification of the
input formula.

> linform :: Vars -> Formula -> Formula 
> linform vars fm =
>  case fm of
>    Atom(R "divides" [c, t]) -> Atom(R "divides" [integer1 abs c, lint vars t])
>    [$form| $s = $t |] -> mkatom vars "=" (t - s)
>    [$form| $s < $t |] -> mkatom vars "<" (t - s)
>    [$form| $s > $t |] -> mkatom vars "<" (s - t)
>    [$form| $s ≤ $t |] -> mkatom vars "<" (t + one - s)
>    [$form| $s ≥ $t |] -> mkatom vars "<" (s + one - t)
>    _ -> fm 

In the main body of the procedure, we'll now be able to assume that
the only inequality predicate is `<'. It may still occur negated, but if so
we transform it into an unnegated equivalent using the code below. In the
DLO procedure the analogous transformation involves a case-split such as
:(s < t) , s = t _ t < s, but because of the discreteness of the integers, we
can just use :(0 < t) , 0 < 1 􀀀 t:

> posineq :: Formula -> Formula 
> posineq fm = case fm of
>   [$form| ¬ ($n0 < $t) |] | n0 == zero -> zero ≺ linearSub [] one t
>   _ -> fm

Presburger's original algorithm is fairly straightforward, and follows the classic
quantifier elimination pattern of dealing with the special case of an existentially
quantified conjunction of literals. However, we will present a clever
optimized version due to Cooper (1972), which is hardly more complicated
and allows us to eliminate an existential quantifier whose body is an arbitrary
quantifier-free NNF formula. This can be much more efficient since it
avoids the blowup often caused by the transformation to DNF, especially in
the presence of many quantifier alternations. For an in-depth discussion of
Presburger's original procedure, the reader can consult Enderton (1972) and
Smoryinski (1980), or indeed the original article, which is quite readable |
Stansifer (1984) gives an annotated English translation. Presburger's algorithm
has additional historical significance for us, since the implementation
by Davis (1957) was arguably the first logical decision procedure actually to
be implemented on a computer.

Consider the task of eliminating the existential quantifier from 9x:p where
p is quantifier-free. We will assume that all the atoms have been maintained
in the standard form with 0 on the left and a linearized term on the right,
and only strict inequalities using `<' present. Using cnnf with the parameter
posineq to eliminate negated inequalities, we may assume in the core
procedure that p is in NNF, i.e. built up from conjunction and disjunction
from literals of the forms 0 = t, :(0 = t), 0 < t, d j t or :(d j t), with
each term t normalized so that if x occurs in it, it is of the form c · x + s.
(Note that lift qelim produces the vars parameter in such a way that the
innermost quantified variable, the one we want to eliminate first, is at the
head of the list, and hence will appear first in the canonical form of any term
involving it.) In order to correlate the various instances of x multiplied by
different coefficients, we find the (positive) least common multiple of all the
coefficients of x, returning 1 if there are no instances of x:

> formlcm :: Term -> Formula -> Integer
> formlcm x f = case f of
>   Atom(R _ [_, [$term| $c * $y + _ |]]) 
>    | x == y -> abs $ destInteger c
>   Not p -> formlcm x p
>   And p q -> lcm (formlcm x p) (formlcm x q)
>   Or p q -> lcm (formlcm x p) (formlcm x q)   
>   _ -> 1

(Note that the atom clause works uniformly for divisibility and other predicates,
because the `interesting' term is always the right-hand argument.)
Now, having computed the LCM, say l, by this method, we can make the
coefficient of x equal to ±l everywhere by taking each atomic formula whose
right-hand argument is of the form c · x + z, and consistently multiplying it
through by an appropriate m. For all but inequalities this is m = l=c and
so the resulting coefficient of x will be l; for inequalities we use m = jl=cj,
since we cannot multiply by negative numbers without changing their sense.
Actually, as part of this transformation we force the coefficients of x from
±l · x to ±1 · x, in anticipation of the next stage:

> adjustcoeff :: Term -> Integer -> Formula -> Formula 
> adjustcoeff x l fm = 
>  case fm of
>    Atom (R p [d, [$term| $c * $y + $z |]]) | y == x ->
>      let m = l `div` (destInteger c)
>          n = if p == "<" then abs m else m
>          xtm = fromInteger (m `div` n) * x in
>      Atom(R p [linearCmul (abs m) d, xtm + linearCmul n z])
>    Not p -> (¬) $ adjustcoeff x l p
>    And p q -> adjustcoeff x l p ∧ adjustcoeff x l q
>    Or p q -> adjustcoeff x l p ∨ adjustcoeff x l q
>    _ -> fm

The next stage, which we have partly folded in above, is to replace l · x
with just x and add a new divisibility clause, justified by the following
equivalence:
(9x: P[l · x]) , (9x: l j x ^ P[x])
The following code implements the entire transformation, reducing the 
coefficient of x to be ±1 using the above functions, then adding the additional
conjunct l j x, or actually, to retain canonicality, l j 1 · x + 0. We make the
slight optimization of not including the trivially true divisibility formula if
l = 1, but we still call adjustcoeff since it might be needed to transform,
say, 0 = 􀀀1 · x + 3 into 0 = 1 · x + 􀀀3 which is the form we expect later on.

> unitycoeff :: Term -> Formula -> Formula 
> unitycoeff x fm = 
>   let l = formlcm x fm
>       fm' = adjustcoeff x l fm in
>   if l == 1 then fm' else
>   let xp = one * x + zero in
>   Atom (R "divides" [fromInteger l, xp]) ∧ adjustcoeff x l fm

Here is the `minus infinity' transformation coded in OCaml, assuming that
we have already used the canonical form conversions:

> minusinf :: Term -> Formula -> Formula 
> minusinf x fm =
>  case fm of
>    [$form| $n0 = $n1 * $y + _ |] 
>     | n0 == zero && n1 == one && x == y -> (⊥)
>    [$form| $n0 < $n1 * $y + _ |] 
>     | n0 == zero && n1 == one && x == y -> (⊥)
>    [$form| $n0 < _ * $y + _ |] 
>     | n0 == zero && x == y -> (⊤)
>    [$form| ¬ $p |] -> (¬) $ minusinf x p
>    [$form| $p ∧ $q |] -> minusinf x p ∧ minusinf x q
>    [$form| $p ∨ $q |] -> minusinf x p ∨ minusinf x q
>    _ -> fm

The next key point is that all divisibility terms d j ±x+a are unchanged
if x is altered by an integer multiple of d. Let us find the (positive) least
common multiple D of all d's occurring in formulas of the form d j c · x + a
(we know in fact that c = ±1 at this stage) using the following code:

> divlcm :: Term -> Formula -> Integer
> divlcm x fm =
>  case fm of
>    Atom (R "divides" [d, [$term| _ * $y + _ |]]) 
>     | x == y -> destInteger d
>    Not p -> divlcm x p
>    And p q -> lcm (divlcm x p) (divlcm x q)
>    Or p q -> lcm (divlcm x p) (divlcm x q)
>    _ -> 1

Then all divisibility atoms in the formula are invariant if x is changed
to x ± kD. Indeed, in the case of P􀀀1[x], divisibility atoms and other
atoms not involving x are all that's left, so P􀀀1[x ± kD] , P􀀀1[x] always
holds. Thus we can find a simpler equivalent for our current target formula
8y: 9x: x < y ^ P[x]:

...

The collection of such boundary points for the relevant literals is called
the B-set for the formula in question.y In OCaml:

> bset :: Term -> Formula -> [Term]
> bset x fm = case fm of 
>   [$form| ¬ ($n0 = $n1 * $y + $a) |] 
>    | n0 == zero && n1 == one && x == y -> [linearNeg a]
>   [$form| $n0 = $n1 * $y + $a |] 
>    | n0 == zero && n1 == one && x == y -> [linearNeg $ linearAdd [] a one]
>   [$form| $n0 < $n1 * $y + $a |] 
>    | n0 == zero && n1 == one && x == y -> [linearNeg a]
>   [$form| ¬ $p |] -> bset x p
>   [$form| $p ∧ $q |] -> Set.union (bset x p) (bset x q)
>   [$form| $p ∨ $q |] -> Set.union (bset x p) (bset x q)
>   _ -> []

In order to apply the main theorem, we need to be able to form the
substitution instances like P[b+j] while retaining canonical form. Thus we
implement a function that replaces the top variable x in atoms by another
term t (assumed not to involve x), restoring canonicality:

> linrep :: Vars -> Term -> Term -> Formula -> Formula 
> linrep vars x t fm =
>  case fm of
>    Atom(R p [d, [$term| $c * $y + $a |]]) | x == y ->
>      let ct = linearCmul (destInteger c) t in
>      Atom $ R p [d, linearAdd vars ct a]
>    Not p -> (¬) $ linrep vars x t p
>    And p q -> linrep vars x t p ∧ linrep vars x t q
>    Or p q -> linrep vars x t p ∨ linrep vars x t q
>    _ -> fm

Now for the overall inner quantifier elimination step, we just perform the
transformation corresponding to the equivalence in Corollary 5.9:

> cooper :: Vars -> Formula -> Formula 
> cooper vars (Ex x0 p0) =
>   let x = Var x0
>       p = unitycoeff x p0
>       p_inf = Skolem.simplify $ minusinf x p
>       bs = bset x p
>       js = [1 .. divlcm x p]
>       p_element j b = linrep vars x (linearAdd vars b (makeInteger j)) p
>       stage j = F.listDisj
>         (linrep vars x (makeInteger j) p_inf :
>          map (p_element j) bs) 
>   in F.listDisj (map stage js)
> cooper _ _ = error "cooper: not an existential formula"

If we eventually eliminate all quantifiers from an initially closed formula,
the result will contain no variables at all and each atom can be evaluated
to true (e.g. 0 < 5, 2j4) or false (e.g. 0 = 7). It's convenient to define
the function to perform such evaluation now, since we can also apply it
at intermediate stages as a useful simplification; for example, if we have a
subformula of the form 0 < 􀀀4 ^ P, we can simplify it to ? and never need
to worry about P. The following auxiliary function just associates atoms
with corresponding operations on rational numbers (we will use this later in
other contexts, hence the incorporation of other inequalities):

> operations :: [(Pred, Integer -> Integer -> Bool)]
> operations = [ ("=",(==))
>              , ("<",(<))
>              , (">",(>)) 
>              , ("<=",(<=))
>              , ("≤",(<=)) 
>              , (">=",(>=))
>              , ("≥",(>=))
>              , ("divides", \x y -> y `mod` x == 0)
>              ]

Now the main evaluation function is straightforward. Note that unless an
atom has numerals as both of its two arguments, the inner dest numeral
calls will fail and the atom will be returned unchanged by the error trap.

> evalc :: Formula -> Formula 
> evalc = F.onatoms atfn 
>  where 
>   atfn (at@(R p [s, t])) = case List.lookup p operations of
>     Just op -> 
>       if isInteger s && isInteger t then 
>         if op (destInteger s) (destInteger t) then (⊤) else (⊥)
>       else Atom at
>     Nothing -> Atom at
>   atfn _ = __IMPOSSIBLE__ 

The overall quantifier elimination procedure is built in the usual way,
inserting evalc into the intermediate normalization steps and at the end.
We use an NNF rather than DNF transformation, since Cooper's algorithm
can cope with any NNF formula.

> integerQelim :: Formula -> Formula 
> integerQelim = 
>  Skolem.simplify . evalc .
>     Qelim.lift linform (Qelim.cnnf posineq . evalc) cooper

> relativize :: (Var -> Formula) -> Formula -> Formula 
> relativize r fm =
>  case fm of
>    Not p -> (¬) $ relativize r p
>    And p q -> relativize r p ∧ relativize r q
>    Or p q -> relativize r p ∨ relativize r q
>    Imp p q -> relativize r p ⊃ relativize r q
>    Iff p q -> relativize r p ⇔ relativize r q
>    All x p -> (¥) x (r x ⊃ relativize r p)
>    Ex x p -> (∃) x (r x ∧ relativize r p)
>    _ -> fm

> naturalQelim :: Formula -> Formula 
> naturalQelim = integerQelim . relativize (\x -> zero ≤ Var x)
