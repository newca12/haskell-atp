
* Signature

> module ATP.MPoly
>   ( Monom
>   , mdiv
>   , mlcm
>   , Poly
>   , cmul
>   , const
>   , var
>   , polyatom
>   )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude hiding (const, div)
> import qualified ATP.Util.Prelude as Prelude
> import ATP.Complex (Err, failwith)
> import ATP.FormulaSyn
> import qualified ATP.Order as Order
> import qualified ATP.Util.Monad as M
> import qualified Data.List as List
> import qualified Ratio

* Monomials

We will implement the ring ℚ [x1, …, xn] of polynomials with rational
coefficients in OCaml, where for convenience we adopt a list-based
representation of the graph of the function p, containing exactly the
pairs (c; [i1, …, in]) such that p(i1, …, in) = c with c ≠ 0. (The
zero polynomial is represented by the empty list.) From now on we will
sometimes use the word `monomial' in a more general sense for a pair
(c;m) including a constant multiplier.y We can multiply monomials in
accordance with the definition as follows:

> type Monom = (Rational, [Int])

> mmul :: Monom -> Monom -> Monom
> mmul (c1, m1) (c2, m2) = (c1 * c2, zipWith (+) m1 m2)

Indeed, we can divide one monomial by another in some circumstances:

> mdiv :: Monom -> Monom -> Err Monom
> mdiv (c1, m1) (c2, m2) = do 
>   r <- M.zipWith indexSub m1 m2
>   return $ (c1 / c2, r)
>  where 
>   indexSub n1 n2 
>    | n1 < n2 = failwith "mdiv"
>    | otherwise = return $ n1 - n2

and even find a `least common multiple' of two monomials:

> mlcm :: Monom -> Monom -> Monom
> mlcm (_, m1) (_, m2) = (1, zipWith max m1 m2)

To avoid multiple list representations of the same function 
ℕ^n ↦ ℚ we ensure that the monomials are sorted according to a fixed total order
⟪, with the largest elements under this ordering appearing first in the list.
We adopt the following order, which compares monomials first according to
their multidegree (the sum of the degrees of all the variables), breaking ties
by ordering them reverse lexicographically.
 
> (≪) :: [Int] -> [Int] -> Bool
> m1 ≪ m2 = 
>   let n1 = sum m1
>       n2 = sum m2 
>   in n1 < n2 || n1 == n2 && Order.lexord (>) m1 m2
 
For example, x2^2 ≪ x1^2 x2 because the multidegrees are 2 and 3,
while x1^2 x2 ≪ x2^3 because powers of x1 are considered first in the
lexicographic ordering. The attractions of this ordering are
considered below; here we just note that it is compatible with
monomial multiplication: if m1 ≪ m2 then also m · m1 ≪ m · m2. 
This means that we can multiply a polynomial by a monomial without
reordering the list, which is both simpler and more efficient.

* Polynomials

> type Poly = [Monom]

> instance Num Poly where
>   (+) = add
>   (-) = sub
>   (*) = mul
>   negate = neg
>   abs = error "Unimplemented" 
>   signum = error "Unimplemented" 
>   fromInteger = error "Unimplemented"

> instance Fractional Poly where
>   (/) = div
>   recip = inv
>   fromRational = error "Unimplemented"

> cmul :: Monom -> Poly -> Poly
> cmul = map . mmul

Similarly, a polynomial can be negated by a mapping operation:

> neg :: Poly -> Poly
> neg = map (first negate)

Note that the formal definition of the ring of polynomials renders
`variables' anonymous, but if we have some particular list of
variables x1, …, xn in mind, we can regard xi as a shorthand for
(0, …, 0, 1, 0 … 0) where only the ith entry is nonzero:

> const :: Vars -> Rational -> Poly
> const vars c 
>  | c == 0 = []
>  | otherwise = [(c, map (Prelude.const 0) vars)]

To create a constant polynomial, we use vars too, but only to determine
how many variables we're dealing with. If the constant is zero, we
give the empty list, otherwise a list mapping the constant monomial to an
appropriate value:

> var :: Vars -> Var -> Poly
> var vars x = [(1, map (\y -> if x == y then 1 else 0) vars)]

To add two polynomials, we can run along them recursively, putting the
`larger' of the two head monomials first in the output list, or when two head
monomials have the same degree, merging them by adding coefficients and
if the resulting coefficient is zero, removing it.

> add :: Poly -> Poly -> Poly
> add l1 l2 = case (l1, l2) of
>   ([], _) -> l2
>   (_, []) -> l1
>   ((c1, m1) : o1, (c2, m2) : o2) 
>    | m1 == m2 -> 
>      let c = c1 + c2
>          rest = o1 + o2
>      in if c == 0 then rest else (c, m1) : rest
>    | m2 ≪ m1 -> (c1, m1) : o1 + l2
>    | otherwise -> (c2, m2) : l1 + o2

Addition and negation together give subtraction:

> sub :: Poly -> Poly -> Poly
> sub l1 l2 = l1 + (- l2)

For multiplication, we just multiply the second polynomial by the various
monomials in the first one, adding the results together:

> mul :: Poly -> Poly -> Poly
> mul l1 l2 = case l1 of
>   [] -> []
>   (h1:t1) -> cmul h1 l2 + t1 * l2

and we can get powers by iterated multiplication:

> pow :: Vars -> Poly -> Int -> Poly
> pow vars l n = iterate (* l) (const vars 1) !! n

We can also permit inversion of constant polynomials:

> inv :: Poly -> Poly
> inv p = case p of 
>   [(c, m)] | List.all (== 0) m -> [(1 / c, m)]
>   _ -> error "mpolyInv: non-constant polynomial"

and hence also perform division subject to the same constraint:

> div :: Poly -> Poly -> Poly
> div p q = p * inv q

We can convert any suitable term in the language of rings into a polynomial
by the usual process of recursion:

> polynate :: Vars -> Term -> Poly
> polynate vars tm = case tm of
>   Var x -> var vars x
>   [$term| - $t |] -> - (polynate vars t)
>   [$term| $s + $t |] -> polynate vars s + polynate vars t
>   [$term| $s - $t |] -> polynate vars s - polynate vars t
>   [$term| $s * $t |] -> polynate vars s * polynate vars t
>   [$term| $s / $t |] -> polynate vars s / polynate vars t
>   [$term| $s ^ $n |] -> case n of
>      Num n' | Ratio.denominator n' == 1 -> pow vars (polynate vars s) (fromInteger $ Ratio.numerator n')
>      _ -> __IMPOSSIBLE__ 
>   Num r -> const vars r
>   _ -> __IMPOSSIBLE__ 

Then we can convert any suitable equational formula s = t, which we
think of as s - t = 0, into a corresponding polynomial:

> polyatom :: Vars -> Formula -> Poly
> polyatom vars fm = case fm of
>   Atom (R "=" [s, t]) -> polynate vars [$term| $s - $t |]
>   _ -> error "polyatom: not an equation"

In later discussions, we will write `norm' to abbreviate mpolynate vars
where vars contains all the variables in any of the polynomials under consideration.
We also write s ≈ t to mean norm(s) = norm(t), i.e. that the
terms s and t in the language of rings define the same polynomial.

