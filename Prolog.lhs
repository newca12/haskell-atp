
> module Prolog ( Rule(..)
>               , renamer
>               , hornprove
>               , simpleprolog
>               , prolog
>               ) where
                        
> import Prelude 
> import qualified Data.List as List
> import qualified Data.Maybe as Maybe
> import qualified Data.Map as Map

Parsing 

> import qualified Lex
> import qualified Text.ParserCombinators.Parsec as P
> import Text.ParserCombinators.Parsec (Parser, (<|>), (<?>))
> import qualified Text.ParserCombinators.Parsec.Expr as E

Printing 

> import qualified Text.PrettyPrint.HughesPJ as PP
> import Text.PrettyPrint.HughesPJClass( (<+>), (<>) ) 

> import qualified Lib
> import FormulaSyn
> import qualified Formula as F
> import qualified Prop
> import qualified Fol
> import Fol(Env)
> import qualified Skolem
> import qualified Unif
> import qualified Tableaux

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Rules

> newtype Rule = Rule ([Formula], Formula) 

Parsing

> parseRule :: Parser Rule
> parseRule s = 
>   do (c, rest) <- Parse.readt s 
>      (asm, rest1) <- if rest /= [] && head rest == ":-" 
>                      then Parse.list "," Parse.readt (tail rest)
>                      else Just ([], rest) 
>      return (Rule (asm, c), rest1)

Printing

> instance Pretty Rule where
>   pPrint = ppRule

> ppRule :: Rule -> PP.Doc
> ppRule (Rule([],f)) = Print.pp f <> PP.text "."
> ppRule (Rule(fs,f)) =
>   Print.pp f <+> PP.text ":-" 
>   <+> PP.cat (PP.punctuate PP.comma (map Print.pp fs)) <> PP.text "."

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Backchaining

The implementation of this backchaining search with unification is
quite similar to the tableau implementation from section
3.10. Variable instantiations are kept globally, and backtracking is
initiated when a given instantiation does not lead to a complete
solution. Since the rules are considered universally quantified, we
can introduce fresh variable names each time we use one, so that
different instances of the same rule can be used without restriction.
The following takes an integer k and a rule's assumptions asm and
conclusion c, and renames the variables schematically starting with 
_k, returning both the modified formula and a new index that can be
used next time.

> renamer :: Int -> Rule -> (Rule, Int)
> renamer k (Rule (asm, c)) = 
>   let fvs = Fol.fv $ F.listConj $ c:asm
>       n = length fvs
>       vvs = map (\n -> Var ("_" ++ show n)) [k .. k+n-1]
>       inst :: Formula -> Formula 
>       inst = Fol.apply $ Map.fromList (zip fvs vvs) in
>   (Rule (map inst asm, inst c), k+n)
>       

The core function backchain organizes the backward chaining with
unification and backtracking search. If the list of goals is empty, it
simply succeeds and returns the current instantiation env, unpacked
into a list of pairs for later manipulation, while if n, which is a
limit on the maximum number of rule applications, is zero, it
fails. Otherwise it searches through the rules for one whose head c
can be unified with the current goal g and such that the new subgoals
a together with the original subgoals gs can be solved under that
instantiation.

> backchain :: [Rule] -> Int -> Int -> Env -> [Formula] -> Maybe Env
> backchain rules n k env goals = case goals of 
>   [] -> Just env
>   g:gs -> 
>     if n == 0 then Nothing else Lib.findApply findFn rules
>       where findFn rule = 
>               let (Rule (a,c),k') = renamer k rule in
>               do env' <- Tableaux.unifyLiterals env (c,g) 
>                  backchain rules (n-1) k' env' (a ++ gs)

In order to apply this to validity checking, we need to convert a raw Horn
clause into a rule. Note that we do not literally introduce a new symbol F
to turn a Horn clause into a definite clause, but just use Bot directly:

> hornify :: Clause -> Maybe Rule
> hornify cls = 
>   let (pos, neg) = List.partition F.positive cls in
>   if length pos > 1 then Nothing
>   else Just $ Rule (map F.opp neg, if pos == [] then Bot else head pos)

As with the tableau provers, we now simply need to iteratively increase
the proof size bound n until a proof is found. As well as the instantiations,
the necessary size bound is returned. 

> hornprove :: Formula -> IO (Env, Int)
> hornprove fm = 
>   let rules = map hornify (Prop.simpcnf $ Skolem.skolemize 
>                            $ Not $ Fol.generalize fm) 
>       rules' = if any (not . Maybe.isJust) rules 
>                then error "clause not horn" else map Maybe.fromJust rules 
>       tabFn n = case backchain rules' n 0 Map.empty [Bot] of
>                   Nothing -> Nothing
>                   Just env -> Just (env, n) in
>   Tableaux.deepen tabFn 0

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Prolog

The core of our Prolog interpreter will be the backchain function without
taking into account the bounding size n. We could modify the code to remove
it, but the path of least resistance, albeit a slightly sleazy one, is simply to
start it off with a negative number, since we test for its becoming exactly
zero, and this will never happen (at least, not until integer wraparound
occurs).

> simpleprolog :: [String] -> String -> Maybe Env
> simpleprolog rules gl = simpleprolog' (map Parse.parse rules) (Parse.parse gl)

> simpleprolog' :: [Rule] -> Formula -> Maybe Env
> simpleprolog' rules gl = backchain rules (-1) 0 Map.empty [gl]

At first sight, Prolog is more limited than a functional language like
OCaml because we can only define predicates, not functions with non-
Boolean values. However, because of unification, Prolog can actually return
values by binding one of the variables in the goal.

  Before demonstrating this idea, we’ll set up code to output these variable
bindings clearly. Although we can’t predict whether a free variable in the
goal clause will occur on the left or right of the lists returned, we know,
because no variables are repeated on the left and no composite terms are
there, that any interesting instantiations (i.e. other than temporary variables,
which are equally general) will be derivable by reading the equations
left-to-right. Thus we can modify the interpreter:

> prolog :: [String] -> String -> Maybe [Formula]
> prolog rules gl = prolog' (map Parse.parse rules) (Parse.parse gl)

> prolog' :: [Rule] -> Formula -> Maybe [Formula]
> prolog' rules gl = 
>   let mapFn env x = do t <- Map.lookup x env
>                        return $ Atom(R "=" [Var x, t]) in
>   do env1 <- simpleprolog' rules gl
>      env2 <- Unif.solve env1
>      mapM (mapFn env2) (Fol.fv gl)

