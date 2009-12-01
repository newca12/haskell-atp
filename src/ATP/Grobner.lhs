
* Signature

> module ATP.Grobner
>   ( decide )
> where

* Imports

#include "../undefined.h" 

> import ATP.Util.Prelude hiding (const, div)
> import qualified ATP.Util.Prelude as Prelude
> import ATP.Complex (Err, failwith, tryFind)
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.MPoly as P
> import ATP.MPoly (Monom, Poly)
> import qualified ATP.Prop as Prop
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Util.List as List
> import qualified ATP.Util.Log as Log
> import ATP.Util.Log (Log)
> import qualified ATP.Util.Monad as M

* Gröbner bases

> type Basis = [Poly]

But first we will implement polynomial reduction as a function, making
natural but arbitrary choices where nondeterminism arises. The
following code attempts to apply pol as a reduction rule to a monomial
cm:

> reduce1 :: Monom -> Poly -> Err Poly
> reduce1 cm pol = case pol of 
>   [] -> failwith "reduce1"
>   hm:cms -> do 
>     (c, m) <- P.mdiv cm hm 
>     return $ P.cmul (-c, m) cms

and the following generalizes this to an entire set pols:

> reduceb ::  Monom -> Basis -> Err Poly
> reduceb = tryFind . reduce1

We use this to reduce a target polynomial repeatedly until no further
reductions are possible; by the above remark, we know that this will
always terminate.

> reduce :: Basis -> Poly -> [Monom]
> reduce pols pol = case pol of
>   [] -> []
>   cm:ptl -> case (do b <- reduceb cm pols
>                      return $ reduce pols (b + ptl)) of 
>     Left _ -> cm : reduce pols ptl
>     Right ms -> ms

Now we can arrive at an analogous theorem to Theorem 4.24 for rewriting.
Given two polynomials p and q, defining reduction rules m1 = p1 and m2 =
p2 according to the chosen ordering, define their S-polynomialy as follows:
S(p, q) = p1 m1' - p2 m2' where LCM(m1, m2) = m1 m1' = m2 m2'
In OCaml this becomes:

> spoly :: Poly -> Poly -> Poly
> spoly pol1 pol2 = case (pol1, pol2) of
>   ([], _) -> []
>   (_, []) -> []
>   (m1:ptl1, m2:ptl2) -> 
>     let m = P.mlcm m1 m2 in
>     case (do d1 <- P.mdiv m m1
>              d2 <- P.mdiv m m2
>              return $ P.cmul d1 ptl1 - P.cmul d2 ptl2) of
>       Left _ -> error "spoly"
>       Right r -> r

The above result shows the value of Gröbner bases in solving (among others)
our original problem, membership of 1 in a polynomial ideal. Moreover,
Theorem 5.35 allows us to implement a decidable test whether a given set
of polynomials constitutes a Gröobner basis. As we shall see, Buchberger's
algorithm allows us to go further and create a Gröobner basis for (the ideal
generated by) any finite set of polynomials.

Suppose that given a set F of polynomials, some f, g ∈ F are such that
S(f, g) ↦F* h where h is in normal form but nonzero. Just as with Knuth-
Bendix completion, we can add the new polynomial h to the set to obtain
F' = F ∪ {h}. Trivially we have h ↦F' 0, but to test F' for confluence we
need also to consider the new S-polynomials of the form {S(h, k) | k ∈ F}.
(Note that we only need to consider one of S(h, k) and S(k, h) since one
reduces to zero iff the other does.) Thus, the following algorithm maintains
the invariant that all S-polynomials of pairs of polynomials from basis are
joinable by the reduction relation induced by basis except possibly those
in pairs. Moreover, since each S(f, g) is of the form hf + kg, the set basis
always defines exactly the same ideal as the original set of polynomials:

> grobner :: Log m => Basis -> [(Poly, Poly)] -> m Basis
> grobner basis pairs = do
>   Log.infoM "grobner" $ show (length basis) ++ " basis elements and " ++ show (length pairs) ++ " pairs"
>   case pairs of
>     [] -> return basis
>     (p1, p2) : opairs -> 
>       let sp = reduce basis (spoly p1 p2) in
>       if null sp then grobner basis opairs else
>       if List.all (List.all (== 0) . snd) sp then return [sp] else
>       let newcps = map (\p -> (p, sp)) basis in
>       grobner (sp:basis) (opairs ++ newcps)

In order to start Buchberger's algorithm off, we just collect the initial set
of S-polynomials, exploiting symmetry to avoid considering both S(f, g) and
S(g, f) for each pair f and g:

> groebner :: Log m => Basis -> m Basis
> groebner basis = grobner basis (List.distinctPairs basis)

Although we could create some polynomials at once and start
experimenting, it's better to fulfil our original purpose of producing
a decision procedure for universal formulas over the complex numbers
(or over all fields of characteristic 0) based on Gröbner bases, since
that provides a more exible input format. In the core quantifier
elimination step, we need to eliminate some block of existential
quantifiers from a conjunction of literals. For the negative
equations, we will use the Rabinowitsch trick. The following maps a
variable v and a polynomial p to 1 - vp as required:

> rabinowitsch :: Vars -> Var -> Poly -> Poly
> rabinowitsch vars v p = P.const vars 1 - P.var vars v * p

The following takes a set of formulas (equations or inequations) and returns
true if they have no common solution. We first separate the input
formulas into positive and negative equations. New variables rvs are created
for the Rabinowitsch transformation of the negated equations, and the
negated polynomials are appropriately transformed. We then find a Gröbner
basis for the resulting set of polynomials and test whether 1 is in the ideal
(i.e. reduces to 0).

> trivial :: Log m => [Formula] -> m Bool
> trivial fms = 
>   let vars0 = Fol.fv fms
>       (eqs, neqs) = List.partition F.positive fms
>       rvs = [ Fol.variant ('_' : show n) vars0 | n <- [1..length neqs] ]
>       vars = vars0 ++ rvs
>       poleqs = map (P.polyatom vars) eqs
>       polneqs = map (P.polyatom vars . F.opp) neqs
>       pols = poleqs ++ zipWith (rabinowitsch vars) rvs polneqs
>   in do 
>     b1 <- groebner pols
>     return $ null $ reduce b1 (P.const vars 1)

For an overall decision procedure for universal formulas, we first perform
some simplification and prenexing, in case some effectively universal quanti
fiers are internal. Then we negate, break the formula into DNF and apply
grobner trivial to each disjunct:

> decide :: Log m => Formula -> m Bool
> decide fm = 
>   let fm1 = Skolem.specialize $ Skolem.prenex $ Skolem.nnf $ Skolem.simplify fm in
>   M.all trivial (Prop.simpdnf $ Skolem.nnf $ Not fm1)
