
* Signature

> module ATP.PropExamples
>   ( ramsey
>   , mkIndex
>   , carry
>   , ripplecarry
>   , mkAdderTest
>   , halfAdder
>   , mux
>   , prime
>   )
> where

* Imports

> import ATP.Util.Prelude
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Prop as P
> import qualified ATP.Util.ListSet as Set 
> import qualified ATP.Util.Tuple as Tuple

%%%%%%%%%%%%%%%%%%%%
%%% Ramsey's Theorem 

For any specific positive integers s, t and n, we can formulate a
propositional formula that is a tautology precisely if R(s, t) n. We
index the vertices using integers 1 to n, calculate all s-element and
t-element subsets, and then for each of these s or t-element subsets
in turn, all possible 2- element subsets of them. We want to express
the fact that for one of the s-element sets, each pair of elements is
connected, or for one of the t-element sets, each pair of elements is
disconnected. The local definition e[m;n] produces an atomic formula
p_m_n that we think of as 'm is connected to n' (or 'm knows n' etc.):

> ramsey :: Int -> Int -> Int -> Formula 
> ramsey s t n = 
>   let vertices = [1 .. n]
>       yesgrps = map (Set.allSets 2) (Set.allSets s vertices)
>       nogrps = map (Set.allSets 2) (Set.allSets t vertices) 
>       e [m, n'] = Atom $ R ("p_" ++ show m ++ "_" ++ show n') [] 
>       e _ = error "Impossible" 
>   in (F.listDisj $ map (F.listConj . map e) yesgrps)
>        ∨ (F.listDisj $ map (F.listConj . map ((¬) . e)) nogrps)

%%%%%%%%%%%%%%%%%%%%%%
%%% Ripple carry adder

In order to implement addition of n-bit numbers as circuits or propositional
formulas, the simplest approach is to exploit the regularity of the
algorithm, and produce an adder by replicating a 1-bit adder n times, propagating
the carry between each adjacent pair of elements. The first task is
to produce a 1-bit adder, which isn’t very difficult. We can regard the ‘sum’
(s) and 'carry’ (c) produced by adding two digits as separate Boolean functions
with the following truth-tables, which we draw using 0 and 1 rather
than ‘false’ and ‘true’ to emphasize the arithmetical link:

x y c s
0 0 0 0
0 1 0 1
1 0 0 1
1 1 1 0

The truth-table for carry might look familiar: it’s just an ‘and’ operation
x^y. As for the sum, it is an exclusive version of ‘or’, which we can represent
by ¬(x , y) or x , ¬y and abbreviate XOR. We can implement functions
in OCaml corresponding to these operations as follows:

> halfsum :: Formula -> Formula -> Formula 
> halfsum x y = x ⇔ (¬) y

> halfcarry :: Formula -> Formula -> Formula 
> halfcarry = (∧)

and now we can assert the appropriate relation between the input and output
wires of a half adder as follows:

> halfAdder :: Formula -> Formula -> Formula 
>           -> Formula -> Formula
> halfAdder x y s c = (s ⇔ halfsum x y) ∧ (c ⇔ halfcarry x y)

The use of ‘half’ emphasizes that this is only part of what we need. Except
for the rightmost digit position, we need to add three bits, not just two,
because of the incoming carry. A full adder adds three bits, which since the
answer is  3 can still be returned as just one sum and one carry bit. The
truth table is:
x y z c s
0 0 0 0 0
0 0 1 0 1
0 1 0 0 1
0 1 1 1 0
1 0 0 0 1
1 0 1 1 0
1 1 0 1 0
1 1 1 1 1
and one possible implementation as gates is the following:

> carry :: Formula -> Formula -> Formula -> Formula
> carry x y z = (x ∧ y) ∨ ((x ∨ y) ∧ z)

'sum' is in the Haskell Prelude

> csum :: Formula -> Formula -> Formula -> Formula
> csum x y z = halfsum (halfsum x y) z

> fa :: Formula -> Formula -> Formula -> Formula 
>    -> Formula -> Formula
> fa x y z s c = (s ⇔ csum x y z) ∧ (c ⇔ carry x y z)

It is now straightforward to put multiple full-adders together into an nbit
adder, which moreover allows a carry propagation in at the low end
and propagates out bit n + 1 at the high end. The corresponding OCaml
function expects the user to supply functions x, y, out and c that, when
given an index, generate an appropriate new variable. The values x and y
return variables for the various bits of the inputs, out does the same for the
desired output and c is a set of variables to be used internally for carry, and
to carry in c(0) and carry out c(n).

> type Wire = Int -> Formula

> conjoin :: Wire -> [Int] -> Formula
> conjoin f = F.listConj . map f

> ripplecarry :: Wire -> Wire -> Wire -> Wire -> Wire
> ripplecarry x y c out n = 
>   conjoin (\i -> fa (x i) (y i) (c i) (out i) (c (i+1))) [0 .. n-1]

For example, using indexed extensions of stylized names for the inputs
and generating a 3-bit adder:

> mkIndex :: Var -> Int -> Formula
> mkIndex x i = Atom $ R (x ++ "_" ++ show i) []

> mkIndex2 :: Var -> Int -> Int -> Formula
> mkIndex2 x i j = Atom $ R (x ++ "_" ++ show i ++ "_" ++ show j) []

If we are not interested in a carry in at the low end, we can modify the
structure to use only a half-adder in that bit position. A simpler, if crude,
alternative, is simply to feed in False (i.e. 0) and simplify the resulting
formula:

> ripplecarry0 :: Wire -> Wire -> Wire -> Wire -> Wire
> ripplecarry0 x y c out n =
>   P.simplify (ripplecarry x y (\i -> if i == 0 then Bot else c i) out n)

The term ‘ripple carry’ adder is used because the carry flows through the
full adders from right to left. In practical circuits, there is a propagation
delay between changes in inputs to a gate and the corresponding change in
output. In extreme cases (e.g. 11111 . . . 111 + 1), the final output bits are
only available after the carry has propagated through n stages, taking about
2n gate delays. When n is quite large, say 64, this delay can be unacceptable,
and a different design needs to be used. For example, in a carry-select adder
the n-bit inputs are split into several blocks of k, and corresponding k-bit
blocks are added twice, once assuming a carry of 0 and once assuming a
carry of 1. The correct answer can then be decided by multiplexing using
the actual carry-in from the previous stage as the selector. Then the carries
only need to be propagated through n/k blocks with a few gate delays in
each. To implement such an adder, we need another element to supplement
ripplecarry0, this time forcing a carry-in of 1:

> ripplecarry1 :: Wire -> Wire -> Wire -> Wire -> Wire
> ripplecarry1 x y c out n =
>   P.simplify
>    (ripplecarry x y (\i -> if i == 0 then Top else c i) out n)

and we will be selecting between the two alternatives when we do carry
propagation using a multiplexer:

> mux :: Formula -> Formula -> Formula -> Formula 
> mux sel in0 in1 = ((¬) sel ∧ in0) ∨ (sel ∧ in1)

Now the overall function can be implemented recursively, using an auxiliary
function to offset the indices in an array of bits:

> offset :: Int -> Wire -> Wire
> offset n x i = x(n + i) 

Suppose we are dealing with bits 0, . . . , k - 1 of an overall n bits. We
separately add the block of k bits assuming 0 and 1 carry-in, giving outputs
c0,s0 and c1,s1 respectively. The final output and carry-out bits are selected
by a multiplexer with selector c(0). The remaining n - k bits can be dealt
with by a recursive call, but all the bit-vectors need to be offset by k since
we start at 0 each time. The only additional point to note is that n might
not be an exact multiple of k, so we actually use k0 each time, which is either
k or the total number of bits n, whichever is smaller: 

> carryselect :: Wire -> Wire -> Wire -> Wire -> Wire -> Wire -> Wire 
>             -> Wire -> Int -> Int -> Formula
> carryselect x y c0 c1 s0 s1 c s n k =
>   let k' = min n k 
>       fm = (ripplecarry0 x y c0 s0 k' ∧ ripplecarry1 x y c1 s1 k') 
>            ∧ (c k' ⇔ mux (c 0) (c0 k') (c1 k')) 
>            ∧ conjoin (\i -> s i ⇔ mux (c 0) (s0 i) (s1 i)) [0 .. k'-1] in
>   if k' < k then fm else
>      fm ∧ carryselect
>           (offset k x) (offset k y) (offset k c0) (offset k c1)
>           (offset k s0) (offset k s1) (offset k c) (offset k s)
>           (n - k) k

One of the problems of circuit design is to verify that some efficiency
optimization like this has not made any logical change to the function computed.
Thus, if the optimization in moving from a ripple-carry to a carryselect
structure is sound, the following should always generate tautologies.
It states that if the same input vectors x and y are added by the two different
methods (using different internal variables) then the all sum outputs
and the carry-out bit should be the same in each case.

  This is a useful generator of arbitrarily large tautologies. It also shows
how practical questions in computer design can be tackled by propositional
methods.

> mkAdderTest :: Int -> Int -> Formula
> mkAdderTest n k =
>   let (x, y, c, s, c0, s0, c1, s1, c2, s2) = 
>         Tuple.map10 mkIndex ("x", "y", "c", "s", "c0", "s0", "c1", "s1", "c2", "s2")
>   in (carryselect x y c0 c1 s0 s1 c s n k ∧ (¬) (c 0) ∧
>      (ripplecarry0 x y c2 s2 n) ⊃ 
>        (c n ⇔ c2 n) ∧ conjoin (\i -> s i ⇔ s2 i) [0 .. n-1])

Now that we can add n-bit numbers, we can multiply them using repeated
addition. Once again, the traditional algorithm can be applied. Consider
multiplying two four-bit numbers A and B. We will use the notation Ai, Bi
for the ith bit of A or B, with the least significant bit (LSB) numbered zero
so that bit i is implicitly multiplied by 2i. Just as we do by hand in decimal
arithmetic, we can lay out the numbers as follows with the product terms
AiBj with the same i + j in the same column, then add them all up:

                      A0B3 A0B2 A0B1 A0B0
+                A1B3 A1B2 A1B1 A1B0
+           A2B3 A2B2 A2B1 A2B0
+      A3B3 A3B2 A3B1 A3B0
-------------------------------------
= P7   P6   P5   P4   P3   P2   P1   P0

In future we will write Xij for the product term AiBj ; each such product
term can be obtained from the input bits by a single AND gate. The calculation
of the overall result can be organized by adding the rows together
from the top. Note that by starting at the top, each time we add a row, we
get the rightmost bit fixed since there is nothing else to add in that row. In
fact, we just need to repeatedly add two n-bit numbers, then at each stage
separate the result into the lowest bit and the other n bits (for in general
the sum has n + 1 bits). The operation we iterate is thus:

       Un-1 Un-1 · · · U2 U1 U0
+      Vn-1 Vn-1 · · · V2 V1 V0
--------------------------------
= Wn-1 Wn-2 · · · · · · W1 W0
+                             Z

The following adaptation of ripplecarry0 does just that:

> rippleshift :: Wire -> Wire -> Wire -> Formula -> Wire -> Wire
> rippleshift u v c z w n =
>   ripplecarry0 u v (\i -> if i == n then w(n - 1) else c(i + 1))
>                    (\i -> if i == 0 then z else w(i - 1)) n

Now the multiplier can be implemented by repeating this operation. We
assume the input is an n-by-n array of input bits representing the product
terms, and use the other array u to hold the intermediate sums and v to hold
the carries at each stage. (By ‘array’, we mean a function of two arguments.)

A few special cases need to be checked because the general pattern breaks
down for n <= 2. Otherwise, the lowest product term x 0 0 is fed to the
lowest bit of the output, and then rippleshift is used repeatedly. The first
stage is separated because the topmost bit of one argument is guaranteed
to be zero (note the blank space above A1B3 in the first diagram). At each
stage k of the iterated operation, the addition takes a partial sum in u k, a
new row of input x k and the carry within the current row, v(k + 1), and
produces one bit of output in out k and the rest in the next partial sum
u(k + 1), except that in the last stage, when k = n - 1 is true, it is fed
directly to the output

> type Wire2 = Int -> Int -> Formula

> multiplier :: Wire2 -> Wire2 -> Wire2 -> Wire -> Wire
> multiplier x u v out n =
>   if n == 1 then (out 0 ⇔ x 0 0) ∧ (¬) (out 1) else
>   P.simplify
>    ((out 0 ⇔ x 0 0) 
>     ∧ rippleshift
>          (\i -> if i == n-1 then Bot else x 0 (i + 1))
>          (x 1) (v 2) (out 1) (u 2) n ∧
>             (if n == 2 then (out 2 ⇔ u 2 0) ∧ (out 3 ⇔ u 2 1) else
>             conjoin (\k -> rippleshift (u k) (x k) (v(k + 1)) (out k)
>                                 (if k == n-1 then \i -> out(n + i)
>                                  else u(k + 1)) n) [2 .. n-1]))

Using these formulas representing arithmetic operations, we can encode some
arithmetical assertions as tautology/satisfiability questions. For example,
consider the question of whether a specific integer p > 1 is prime, i.e. has no
factors besides itself and 1. First, we define functions to tell us how many
bits are needed for p in binary notation, and to extract the nth bit of a
nonnegative integer x:

> bitLength :: Int -> Int
> bitLength x = if x == 0 then 0 else 1 + bitLength (x `div` 2)

> bit :: Int -> Int -> Bool
> bit n x = if n == 0 then x `mod` 2 == 1 else bit (n - 1) (x `div` 2)

We can now produce a formula asserting that the atoms x(i) encode the
bits of a value m, at least modulo 2n. We simply form a conjunction of these
variables or their negations depending on whether the corresponding bits
are 1 or 0 respectively:

> congruentTo :: Wire -> Wire2
> congruentTo x m n =
>   conjoin (\i -> if bit i m then x i else (¬) (x i)) [0 .. n-1]

Now, if a number p is composite and requires at most n bits to store, it
must have a factorization with both factors at least 2, hence both  p/2 and
so storable in n−1 bits. To assert that p is prime, then, we need to state that
for all (n−1)-element sequences of bits, the product does not correspond to
the value p. Note that without further restrictions, the product could take
as many as 2n − 2 bits. While we only need to consider those products less
than p, it’s easier not to bother with encoding this property in propositional
terms. Thus the following function applied to a positive integer p should
give a tautology precisely if p is prime.

> prime :: Int -> Formula
> prime p =
>   let (x, y, out) = Tuple.map3 mkIndex ("x", "y", "out")
>       m i j = x i ∧ y j
>       (u, v) = Tuple.map2 mkIndex2 ("u", "v")
>       n = bitLength p in
>   (¬) (multiplier m u v out (n - 1) ∧
>         congruentTo out p (max n (2 * n - 2)))

