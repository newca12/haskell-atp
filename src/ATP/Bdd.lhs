
* Signature

> module ATP.Bdd 
>   ( Bdd
>   , taut
>   , tests
>   )
> where

* Imports 

> import ATP.Util.Prelude hiding (and, or)
> import qualified ATP.Dp as Dp
> import ATP.FormulaSyn 
> import qualified ATP.Prop as Prop
> import qualified Control.Monad.State as State
> import Control.Monad.State (State)
> import qualified Data.Map as Map
> import Data.Map (Map)
> import qualified Test.QuickCheck as Q
> import Test.QuickCheck (Property)

* BDDs 

Our OCaml representation of a BDD graph works by associating an
integer index with each node.y Complementation is indicated by
negating the node index, and since -0 = 0 we don't use 0 as an
index. Index 1 is reserved for the `true' node, and hence -1 for
`false'; other nodes are allocated indices n with |n| ≥ 2. A BDD node
itself is then just a propositional variable together with the `left'
and `right' node indices:

And index into the BDD

> type Index = Int

> type Node = (String, Index, Index)

The BDD graph is essentially just the association between BDD nodes
and their integer indices, implemented as a finite partial function in
each direction. But the data structure also stores the smallest
(positive) unused node index and the ordering on atoms used in the
graph:

> data Bdd = Bdd { -- Range is the integers ∉ {-1.0,1}
>                  unique :: Map Node Index
>                  -- Domain is the positive integers > 1
>                , expand :: Map Index Node
>                , next :: Int
>                , ord :: String -> String -> Bool
>                }

To pass from an index to the corresponding node, we just apply the `expansion'
function in the data structure, negating appropriately to deal with
complementation. For indices without an expansion, e.g. the terminal nodes
1 and -1, a trivial atom and two equivalent children are returned, since this
makes some later code more regular.

> type S = (Bdd, Map (Index, Index) Index)

> type BddState a = State S a

> expandNode :: Index -> BddState Node
> expandNode n = do
>   (bdd, _) <- State.get
>   return $ 
>    if n >= 0 then maybe ("", 1, 1) id (Map.lookup n $ expand bdd)
>    else let (p, l, r) = maybe ("", 1, 1) id (Map.lookup (-n) $ expand bdd)
>         in (p, -l, -r)

Before any new node is added to the BDD, we check whether there is
already such a node present, by looking it up using the function from nodes
to indices. (Because its role is to ensure a single occurrence of each node in
the graph, that function is traditionally called the unique table.) Otherwise
    a new node is added; in either case the (possibly modiifed) BDD and the
final node index are returned:

> lookupUnique :: Node -> BddState Index
> lookupUnique node = do
>   (bdd, comp) <- State.get
>   case Map.lookup node (unique bdd) of
>     Just node' -> return node'
>     Nothing -> let n = next bdd in do
>       State.put (bdd { unique = Map.insert node n (unique bdd)
>                      , expand = Map.insert n node (expand bdd)
>                      , next = n + 1 }, comp)
>       return n
                     
The core `make a new BDD node' function first checks whether the two
subnodes are identical, and if so returns one them together with an
unchanged BDD. Otherwise it inserts a new node in the table, taking
care to maintain an unnegated left subnode for canonicality.

> mkNode :: Node -> BddState Index
> mkNode (s, l, r) 
>  | l == r = return l
>  | l >= 0 = lookupUnique (s, l, r)
>  | otherwise = fmap negate $ lookupUnique (s, -l, -r)

To get started, we want to be able to create a trivial BDD structure,
with a user-specified ordering of the propositional variables:

> new :: (String -> String -> Bool) -> Bdd
> new = Bdd Map.empty Map.empty 2

The following function extracts the ordering from a BDD, treating the
trivial variable as special so we can sometimes treat terminal nodes
uniformly:

> order :: Bdd -> String -> String -> Bool
> order bdd p1 p2 = p2 == "" && p1 /= "" || ord bdd p1 p2

To implement conjunction of BDDs, we rst consider the trivial cases
where one of the BDDs is `false' or `true', in which case we return `false'
and the other BDD respectively. We also check whether the result has
already been computed; since conjunction is commutative, we can equally
well accept an entry with the arguments either way round. Otherwise, both
BDDs are branches. In general, however, they may not branch on the same
variable | although the order of variables is the same, many choices may
be (and we hope are) omitted because of sharing. If the variables are the
same, then we recursively deal with the left and right pairs, then create a
new node. Otherwise, we pick the variable that comes rst in the ordering
and consider its two sides, but the other side is, at this level, not broken
down. Note that at the end, we update the computed table with the new
information.

> and :: Int -> Int -> BddState Index
> and m1 m2 =
>   if m1 == -1 || m2 == -1 then return (-1)
>   else if m1 == 1 then return m2 else if m2 == 1 then return m1 else
>   do (bdd, comp) <- State.get
>      case (Map.lookup (m1, m2) comp, Map.lookup (m2, m1) comp) of
>        (Just n, _) -> return n
>        (_, Just n) -> return n
>        _ -> do 
>          (p1, l1, r1) <- expandNode m1
>          (p2, l2, r2) <- expandNode m2
>          let (p, lpair, rpair) 
>                | p1 == p2 = (p1, (l1, l2), (r1, r2))
>                | order bdd p1 p2 = (p1, (l1, m2), (r1, m2))
>                | otherwise = (p2, (m1, l2), (m1, r2))
>          lnew <- uncurry and lpair
>          rnew <- uncurry and rpair
>          ind <- mkNode (p, lnew, rnew)
>          State.modify (\(bdd', comp') -> (bdd', Map.insert (m1, m2) ind comp'))
>          return ind

> or :: Int -> Int -> BddState Index
> or m1 m2 = fmap negate $ and (-m1) (-m2)

> imp :: Int -> Int -> BddState Index
> imp m1 m2 = or (-m1) m2

> iff :: Int -> Int -> BddState Index
> iff m1 m2 = do
>   ind1 <- and m1 m2
>   ind2 <- and (-m1) (-m2)
>   or ind1 ind2

Now to construct a BDD for an arbitrary formula, we recurse over its
structure; for the binary connectives we produce BDDs for the two subformulas
then combine them appropriately:

: bdd * (int * int, int) func ->
    prop formula -> (bdd * (int * int, int) func) * int

> fromFormula :: Formula -> BddState Index
> fromFormula fm = case fm of
>   Bot -> return (-1)
>   Top -> return 1
>   Atom (R s []) -> mkNode (s, 1, -1)
>   Atom  _ -> error "Non-propositional atom"
>   Not p -> fmap negate $ fromFormula p
>   And p q -> do
>     ind1 <- fromFormula p
>     ind2 <- fromFormula q
>     and ind1 ind2
>   Or p q -> do
>     ind1 <- fromFormula p
>     ind2 <- fromFormula q
>     or ind1 ind2
>   Imp p q -> do
>     ind1 <- fromFormula p
>     ind2 <- fromFormula q
>     imp ind1 ind2
>   Iff p q -> do
>     ind1 <- fromFormula p
>     ind2 <- fromFormula q
>     iff ind1 ind2
>   _ -> error "Quantifiers"

This can now be made into a tautology-checker simply by creating a BDD
for a formula and comparing the overall node index against the index for
`true'. We just use the default OCaml ordering `<' on variables:

> taut :: Formula -> Bool
> taut fm = 
>   State.evalState (fromFormula fm) (new (<), Map.empty) == 1

The tautology checker bddtaut performs quite well on some examples; for
example it works markedly faster than dplltaut here:

bddtaut (mk_adder_test 4 2);;
- : bool = true

* Tests

> prop_taut_correct :: Property
> prop_taut_correct = Q.label "ATP.Bdd: taut_correct" $
>   Q.forAll (Prop.forms 5) $ \f -> 
>     Dp.dplltaut f == taut f
-->     Prop.tautology f == taut f

> tests :: IO ()
> tests = do 
>   Q.quickCheck prop_taut_correct

