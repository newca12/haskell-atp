
* Signature 

> module ATP.Geom
>   ( coordinate )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude 
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified Data.Map as Map

* Geometry 

> coordinations :: [(String, Formula)]
> coordinations = 
>   [ -- Points 1, 2 and 3 lie on a common line 
>     ( "collinear" 
>     , [$form| (x_1 - x_2) * (y_2 - y_3) = (y_1 - y_2) * (x_2 - x_3) |] )
>     -- Lines (1,2) and (3,4) are parallel
>   , ( "parallel"
>     , [$form| (x_1 - x_2) * (y_3 - y_4) = (y_1 - y_2) * (x_3 - x_4) |] )
>     -- Lines (1,2) and (3,4) are perpendicular 
>   , ( "perpendicular"
>     , [$form| (x_1 - x_2) * (x_3 - x_4) + (y_1 - y_2) * (y_3 - y_4) = 0 |] )
>     -- Lines (1,2) and (3,4) have the same length 
>   , ( "lengths_eq"
>     , [$form| (x_1 - x_2)^2 + (y_1 - y_2)^2 = (x_3 - x_4)^2 + (y_3 - y_4)^2 |] )
>   , ( "is_midpoint" -- Point 1 is the midpoint of line (2,3) 
>     , [$form| 2 * x_1 = x_2 + x_3 ∧ 2 * y_1 = y_2 + y_3 |] )
>   , ("is_intersection" -- Lines (2,3) and (4,5) meet at point 1 
>     , [$form| (x_1 - x_2) * (y_2 - y_3) = (y_1 - y_2) * (x_2 - x_3) ∧ 
>          (x_1 - x_4) * (y_4 - y_5) = (y_1 - y_4) * (x_4 - x_5) |] )
>   , ("=" -- Points 1 and 2 are the same
>     , [$form| (x_1 = x_2) /\ (y_1 = y_2) |] )
>   ]

To translate a quantifier-free formula we just use these templates as a
pattern to modify atomic formulas. (To be applicable to general first-order
formulas, we should also expand each quantifier over points into two
quantifiers over coordinates.)

> coordinate :: Formula -> Formula
> coordinate = F.onatoms $ \(R a args) -> 
>   let getVars (Var v) = (Var $ v ++ "_x", Var $ v ++ "_y")
>       getVars _ = __IMPOSSIBLE__ 
>       (xtms, ytms) = unzip (map getVars args)
>       xs = ["x_" ++ show n | n <- [1 .. length args]]
>       ys = ["y_" ++ show n | n <- [1 .. length args]]
>       θ = Map.fromList $ zip (xs ++ ys) (xtms ++ ytms)
>   in Fol.apply θ (fromJust $ lookup a coordinations)

pp $ coordinate [$form| collinear(a,b,c) ==> collinear(b,a,c) |]

We can optimize the translation process somewhat by exploiting the
invariance of geometric properties under certain kinds of spatial
transformation. The following generates an assertion that one of our
geometric properties is unchanged if we systematically map each x ↦ x'
and y ↦ y':

-- > invariant :: (Term, Term) -> (String, Formula) -> Formula
-- > invariant (x', y') (s, z) = z ⇔ Fol.apply θ z
-- >  where 
-- >   m n = 
-- >     let x = "x_" ++ show n
-- >         y = "y_" ++ show n
-- >         i = Map.fromList $ zip ["x", "y"] [Var x, Var y]
-- >     in Map.insert x (Fol.apply i x') . Map.insert y (Fol.apply i y')
-- >   θ = foldr m Map.empty [1..5]

We will check the invariance of our properties under various transformations
of this sort. (We check them over the complex numbers for eciency;
if a universal formula holds over C it also holds over R.) Under a spatial
translation x ↦ x + X, y ↦ y + Y :

-- > invariantUnderTranslation :: (String, Formula) -> Formula
-- > invariantUnderTranslation = invariant ([$term| x + x' |], [$term| y + y' |])
