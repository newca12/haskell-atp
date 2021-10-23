
* Signature 

> module ATP.Geom
>   ( invariantUnderTranslation
>   , invariantUnderRotation
>   , invariantUnderScaling
>   , invariantUnderShearing
>   , originate
>   , wu 
>   )
> where

* Imports



> import ATP.Util.Prelude 
> import ATP.Equal (lhs)
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Grobner as Grobner
> import qualified ATP.Poly as P
> import ATP.Poly (zero)
> import qualified ATP.Util.List as List
> import qualified ATP.Util.ListSet as LSet
> import ATP.Util.ListSet ((\\))
> import qualified Data.Map as Map
> import qualified Data.Set as Set

Allow interactive use of Grobner without unused import warning

> __ :: Formula -> IO Bool
> __ = Grobner.decide

* Geometry 

> coordinations :: [(String, Formula)]
> coordinations = 
>   [ -- Points 1, 2 and 3 lie on a common line 
>     ( "collinear" 
>     , [form| (x_1 - x_2) * (y_2 - y_3) = (y_1 - y_2) * (x_2 - x_3) |] )
>     -- Lines (1,2) and (3,4) are parallel
>   , ( "parallel"
>     , [form| (x_1 - x_2) * (y_3 - y_4) = (y_1 - y_2) * (x_3 - x_4) |] )
>     -- Lines (1,2) and (3,4) are perpendicular 
>   , ( "perpendicular"
>     , [form| (x_1 - x_2) * (x_3 - x_4) + (y_1 - y_2) * (y_3 - y_4) = 0 |] )
>     -- Lines (1,2) and (3,4) have the same length 
>   , ( "lengths_eq"
>     , [form| (x_1 - x_2)^2 + (y_1 - y_2)^2 = (x_3 - x_4)^2 + (y_3 - y_4)^2 |] )
>   , ( "is_midpoint" -- Point 1 is the midpoint of line (2,3) 
>     , [form| 2 * x_1 = x_2 + x_3 ∧ 2 * y_1 = y_2 + y_3 |] )
>   , ("is_intersection" -- Lines (2,3) and (4,5) meet at point 1 
>     , [form| (x_1 - x_2) * (y_2 - y_3) = (y_1 - y_2) * (x_2 - x_3) ∧
>          (x_1 - x_4) * (y_4 - y_5) = (y_1 - y_4) * (x_4 - x_5) |] )
>   , ("=" -- Points 1 and 2 are the same
>     , [form| (x_1 = x_2) /\ (y_1 = y_2) |] )
>   ]

To translate a quantifier-free formula we just use these templates as a
pattern to modify atomic formulas. (To be applicable to general first-order
formulas, we should also expand each quantifier over points into two
quantifiers over coordinates.)

> coordinate :: Formula -> Formula
> coordinate = F.onatoms $ \(R a args) -> 
>   let getVars (Var v) = (Var $ v ++ "_x", Var $ v ++ "_y")
>       getVars _ = (throwImpossible (Impossible __FILE__ __LINE__))
>       (xtms, ytms) = unzip (map getVars args)
>       xs = ["x_" ++ show n | n <- [1 .. length args]]
>       ys = ["y_" ++ show n | n <- [1 .. length args]]
>       θ = Map.fromList $ zip (xs ++ ys) (xtms ++ ytms)
>   in Fol.apply θ (fromJust $ lookup a coordinations)

pp $ coordinate [form| collinear(a,b,c) ==> collinear(b,a,c) |]

We can optimize the translation process somewhat by exploiting the
invariance of geometric properties under certain kinds of spatial
transformation. The following generates an assertion that one of our
geometric properties is unchanged if we systematically map each x ↦ x'
and y ↦ y':

> invariant :: (Term, Term) -> (String, Formula) -> Formula
> invariant (x', y') (_s, z) = z ⇔ Fol.apply θ z
>  where 
>   m n = 
>     let x = "x_" ++ show n
>         y = "y_" ++ show n
>         i = Map.fromList $ zip ["x", "y"] [Var x, Var y]
>     in Map.insert x (Fol.apply i x') . Map.insert y (Fol.apply i y')
>   θ = foldr m Map.empty [1 .. (5 :: Integer)]

We will check the invariance of our properties under various transformations
of this sort. (We check them over the complex numbers for eciency;
if a universal formula holds over C it also holds over R.) Under a spatial
translation x ↦ x + X, y ↦ y + Y :

> invariantUnderTranslation :: (String, Formula) -> Formula
> invariantUnderTranslation = invariant ([term| x + x' |], [term| y + y' |])

M.all (Grobner.decide . invariantUnderTranslation) coordinations

> invariantUnderRotation :: (String, Formula) -> Formula
> invariantUnderRotation fm = 
>   [form| s^2 + c^2 = 1 |] ⊃ (invariant ([term| c * x - s * y |], [term| s * x + c * y |]) fm)

M.all (Grobner.decide . invariantUnderRotation) coordinations

Given any point (x; y), we can choose s and c subject to s2+c2 = 1 to
make sx + cy = 0.  Thus, given two points A and B in the original
problem, we may take them to be (0, 0) and (x, 0) respectively:

> originate :: Formula -> Formula
> originate fm = case Fol.fv fm of
>   a:b:_ -> Fol.apply (Map.fromList [ (a ++ "_x", zero), (a ++ "_y", zero), (b ++ "_y", zero)]) (coordinate fm)
>   _ -> error "Impossible" 

Two other important transformations are scaling and shearing. Any combination
of translation, rotation, scaling and shearing is called an affine
transformation.

> invariantUnderScaling :: (String, Formula) -> Formula
> invariantUnderScaling fm = 
>   [form| ¬ A = 0 |] ⊃ (invariant ([term| A * x |], [term| A * y |]) fm)

Because all our geometric properties are invariant under scaling:

M.all (Grobner.decide . invariantUnderScaling) coordinations

we might be tempted to go further and use (1; 0) for the point B, but we can
only do this if we are happy to rule out the possibility that A = B. Similarly,
we might want to use shearing invariance to justify taking three of the points
as (0; 0), (x; 0) and (0; y), but this is problematic if the three points may be
collinear. In any case, while some properties are invariant under shearing,
perpendicularity and equality of lengths are not, as the reader can conrm
thus:

M.partition (Grobner.decide . invariantUnderShearing) coordinations

Thus, the special choice of coordinates based on invariance under scaling
and shearing seems best left to the user setting up the problem.

> invariantUnderShearing :: (String, Formula) -> Formula
> invariantUnderShearing = invariant ([term| x + b * y |], [term| y |])

:{
(Grobner.decide . originate) 
  [form| is_midpoint(m,a,c) ∧ perpendicular(a,c,m,b) ⊃ lengths_eq(a,b,b,c) |]
:}

> pprove :: Vars -> [Term] -> Term -> [Formula] -> [Formula]
> pprove vars triang p degens 
>  | p == zero = degens
>  | otherwise = case triang of
>    [] -> p ≡ zero : degens
>    q@[term| $_ + ^x * _ |] : qs
>     | x /= head vars -> 
>       if elem (head vars) (Fol.fv p) 
>       then foldr (pprove vars triang) degens (P.coefficients vars p) 
>       else pprove (tail vars) triang p degens
>     | otherwise -> 
>       let (k, p') = P.pdivide vars p q in
>       if k == 0 then pprove vars qs p' degens else
>       let degens' = (¬) (P.phead vars q ≡ zero) : degens in
>       foldr (pprove vars qs) degens' (P.coefficients vars p') 
>    _ -> (throwImpossible (Impossible __FILE__ __LINE__))

Any set of polynomials can be transformed into a triangular set of polynomials
that are all zero whenever all the initial polynomials are. If the
desired `top' variable xk+m occurs in at most one polynomial, we set that
one aside and triangulate the rest with respect to the remaining variables.
Otherwise, we can pick the polynomial p with the lowest degree in xk+m
and pseudo-divide all the other polynomials by p, then repeat. We must
reach a stage where xk+m is confined to one polynomial, since each time we
run pseudo-division we reduce the aggregate degree of xk+m. This is implemented
in the following function, where we assume that polynomials in the
list consts do not involve the head variable in vars, but those in pols may
do:

> triangulate :: Vars -> [Term] -> [Term] -> [Term]
> triangulate vars consts pols 
>  | null vars = pols
>  | otherwise = 
>    let (cns, tpols) = List.partition (P.isConstant vars) pols in
>    if null cns then triangulate vars (cns ++ consts) tpols else
>    if length pols <= 1 then pols ++ triangulate (tail vars) [] consts else
>    let n = minimum $ map (P.degree vars) pols
>        p = fromJust $ List.find (\p' -> P.degree vars p' == n) pols
>        ps = pols \\ [p]
>    in triangulate vars consts $ p : map (\q -> snd $ P.pdivide vars q p) ps

Because geometry statements tend to be of the constructive type, they
are already in `almost triangular' form and the triangulation tends to be
quick and efficient. Constructions like `M is the midpoint of the line AB'
or `P is the intersection of lines AB and CD' define points by one or two
constraints on their coordinates. Assuming all coordinates introduced later
have been triangulated, we now only need to triangulate the two equations
defining these constraints by pseudo-division within this pair, and need not
modify other equations. Thus, forming a triangular set tends to be much
more efficient than forming a Gröobner basis. However, when it comes to
actually reducing with the set, a Gröobner basis is often much more efficient.

Now we will implement the overall procedure that returns a set of sufficient
conditions for one conjunction of polynomial equations to imply another.
The user is expected to list the variables in elimination order in vars, and
specify which coordinates are to be set to zero in zeros. We could attempt
to infer an order automatically, and rely on originate for the choice of
zeros, but since both these parameters can affect efficiency dramatically, a
finer degree of control is useful.

> wu :: Formula -> Vars -> Vars -> [Formula]
> wu fm vars zeros =
>   let gfm0 = coordinate fm
>       gfm = Fol.apply (foldr (flip Map.insert zero) Map.empty zeros) gfm0
>   in if not $ Set.fromList vars == Set.fromList (Fol.fv gfm) then error "wu: bad parameters" else
>   let (ant, con) = F.destImp gfm
>       pols = map (lhs . P.atom vars) (F.conjuncts ant)
>       ps = map (lhs . P.atom vars) (F.conjuncts con)
>       tri = triangulate vars [] pols
>   in foldr (\p -> LSet.union (pprove vars tri p [])) [] ps 
