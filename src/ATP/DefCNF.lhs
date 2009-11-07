
Definitional CNF

* Signature

> module ATP.DefCnf 
>   ( maxVarIndex
>   , defcnf
>   , defcnf1
>   , defcnfs
>   ) 
> where

* Imports

> import ATP.Util.Prelude 
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Prop as Prop
> import qualified ATP.Util.ListSet as Set
> import qualified ATP.Util.Misc as Misc
> import qualified Data.Char as Char
> import qualified Data.List as List
> import qualified Data.Map as Map
> import Data.Map(Map)

* CNF

For the new propositional variables we will use stylized names of the form
p_n. The following function returns such an atom as well as the incremented
index ready for next time.

> mkprop :: Int -> (Formula, Int)
> mkprop n = (Atom $ R ("p_" ++ show n) [], n + 1)

For simplicity, suppose that the starting formulas has been pre-simplified
by nenf, so that negation is only applied to atoms and implication has been
eliminated. The main recursive function maincnf takes a triple consisting
of the formula to be transformed, a finite partial function giving the `definitions'
made so far, and the current variable index counter value. It returns a
similar triple with the transformed formula, the augmented definitions and
a new counter moving past variables used in these definitions. All it does
is decompose the toplevel binary connective into the type constructor and
the immediate subformulas, then pass them as arguments op and (p,q) to
a general function defstep that does the main work. 

> type Trip = (Formula, Map Formula (Formula, Formula), Int)

> maincnf :: Trip -> Trip
> maincnf (trip @ (fm, _, _)) = case fm of
>    And p q -> defstep And (p, q) trip
>    Or p q -> defstep Or (p, q) trip
>    Iff p q -> defstep Iff (p, q) trip
>    _ -> trip

Inside defstep, a recursive call to maincnf transforms the left-hand subformula
p, returning the transformed formula fm1, an augmented list of
definitions defs1 and a counter n1. The right-hand subformula q together
with the new list of definitions and counter are used in another recursive call,
giving a transformed formula fm2 and further modified definitions defs2 and
counter n2. We then construct the appropriate composite formula fm' by
applying the constructor op passed in. Next, we check if there is already
a definition corresponding to this formula, and if so, return the defining
variable. Otherwise we create a new variable and insert a new definition,
afterwards returning this variable as the simplified formula, and of course
the new counter after the call to mkprop.

> defstep :: (Formula -> Formula -> Formula) 
>         -> (Formula, Formula) -> Trip -> Trip
> defstep op (p, q) (_, defs, n) =
>   let (fm1, defs1, n1) = maincnf (p, defs, n) 
>       (fm2, defs2, n2) = maincnf (q, defs1, n1) 
>       fm' = op fm1 fm2 in
>   case Map.lookup fm' defs2 of
>     Just (v,_) -> (v, defs2, n2)
>     Nothing -> (v, Map.insert fm' (v, v ⇔ fm') defs2, n3)
>       where (v, n3) = mkprop n2

We need to make sure that none of our newly introduced atoms already
occur in the starting formula. This tedious business will crop up a few
times in the future, so we implement a more general solution now. The
max_varindex function returns whichever is larger of the argument n and
all possible m such that the string argument s is pfx followed by the string
corresponding to m, if any:

> maxVarIndex :: String -> String -> Int -> Int
> maxVarIndex pfx s n =
>   let m = length pfx 
>       l = length s in
>   if l <= m || take m s /= pfx then n else
>   let s' = take (l-m) (drop m s) in
>   case Misc.getInt s' of
>     Nothing -> n
>     Just n' -> max n n'

Now we can implement the overall function. First the formula is simplified
and negations are pushed down, giving fm', and we use this formula to
choose an appropriate starting variable index, adding 1 to the largest n for
which there is an existing variable `p n'. We then call the main function, kept
as a parameter fn to allow future modification, starting with no definitions
and with the variable-name counter set to the starting index. We then return
the resulting CNF in the set-of-sets representation:

> mkDefcnf :: (Trip -> Trip) -> Formula -> [[Formula]]
> mkDefcnf fn fm =
>   let fm' = Prop.nenf fm 
>       n = 1 + F.overatoms (maxVarIndex "p_" . show) fm' 0
>       (fm'', defs, _) = fn (fm', Map.empty, n) 
>       deflist = map (snd . snd) (Map.toList defs) in
>   Set.unions(Prop.simpcnf fm'' : map Prop.simpcnf deflist)

Our first definitional CNF function just applies this to maincnf and converts
the result back to a formula:

> defcnf1 :: Formula -> Formula
> defcnf1 fm = F.listConj $ map F.listDisj $ mkDefcnf maincnf fm

:module + DefCnf Prop
defcnf1 $ parse "(p ∨ (q ∧ ¬ r)) ∧ s"

  We can optimize the procedure by avoiding some obviously redundant
definitions.  First, when dealing with an iterated conjunction in the
initial formula, we can just put the conjuncts into CNF separately and
conjoin them.y And if any of those conjuncts in their turn contain
disjunctions, we can ignore atomic formulas within them and only
introduce definitions for other subformulas.
  The coding is fairly simple: we first descend through arbitrarily many
nested conjunctions, and then through arbitrarily many nested
disjunctions, before we begin the definitional work. However, we still
need to link the defi- nitional transformations in the different parts
of the formula, so we maintain the same overall structure with three
arguments. The function subcnf has the same structure as defstep
except that it handles the linkage housekeeping without introducing
new definitions, and has the function called recursively as an
additional parameter sfn:

> subcnf :: (Trip -> Trip) -> (Formula -> Formula -> Formula)
>           -> (Formula, Formula) -> Trip -> Trip
> subcnf sfn op (p,q) (_, defs, n) =
>   let (fm1, defs1, n1) = sfn(p,defs,n) 
>       (fm2, defs2, n2) = sfn(q,defs1,n1) in 
>   (op fm1 fm2, defs2, n2)

This is used first to define a function that recursively descends through
disjunctions performing the definitional transformation of the disjuncts:

> orcnf :: Trip -> Trip
> orcnf (trip @ (fm, _, _)) = case fm of
>    Or p q -> subcnf orcnf Or (p,q) trip
>    _ -> maincnf trip

and in turn a function that recursively descends through conjunctions calling
orcnf on the conjuncts:

> andcnf :: Trip -> Trip
> andcnf (trip @ (fm, _, _)) = case fm of
>    And p q -> subcnf andcnf And (p,q) trip
>    _ -> orcnf trip

Now the overall function is the same except that andcnf is used in place
of maincnf. We separate the actual reconstruction of a formula from the
set of sets into a separate function, since it will be useful later to intercept
the intermediate result.

> defcnfs :: Formula -> [[Formula]]
> defcnfs = mkDefcnf andcnf

> defcnf :: Formula -> Formula 
> defcnf = F.listConj . map F.listDisj . defcnfs

%%%%%%%%%%%%%
%%% Test

 import qualified Codec.Binary.UTF8.String as UString

S.putStrLn $ render $ pPrint $ defcnf [$form| (p ∨ (q ∧ ¬ r)) ∧ s |]
