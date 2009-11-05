
First order logic.  Atomic formulas are now relations on
terms where terms are either functions applied to arguments
or variables.

Terms T ::= T '::' T1 | T1
      T1 ::= T1 + T2 | T2
      T2 ::= T3 - T2 | T3
      T3 ::= T3 * T4 | T4
      T4 ::= T5 / T4 | T5
      T5 ::= T6 ^ T5 | A

Term lists TS ::= T | T , TS

Atoms A ::= ( T ) | - A | Var () | Var ( TS ) | Var

Relations R ::= Var() | Var ( TS ) | Var | T = T | T < T 
              | T <= T | T > T | T >= T

* Signature

> module ATP.Fol 
>   ( onformula
>   , isVar
>   , Fv(fv)
>   , Subst(apply)
>   , generalize
>   , functions
>   , predicates
>   , variant
>   , holds
>   ) 
> where

* Imports

> import ATP.Util.Prelude 
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Util.Lib as LIb
> import ATP.Util.Lib((↦))
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))
> import qualified Data.List as List
> import qualified Data.Map as Map
> import Data.Map(Map)

* Util

Terms 

> isVar :: Term -> Bool
> isVar (Var _) = True
> isVar _ = False

Relations
  
> onformula :: (Term -> Term) -> Formula -> Formula
> onformula f = F.onatoms(\(R p a) -> Atom(R p (map f a)))

* Free variables 

> class Fv a where
>   fv :: a -> Vars

> instance Fv Term where
>   fv (Var x) = [x]
>   fv (Fn _ args) = Set.unions (map fv args)

> instance Fv Rel where
>   fv (R _ args) = Set.unions (map fv args)

> instance Fv Formula where
>   fv fm = case fm of
>           [$form| ⊤ |] -> []
>           [$form| ⊥ |] -> []
>           [$form| ¬ $p |] -> fv p
>           [$form| ∀ $x. $p |] -> fv p \\ [x]
>           [$form| exists $x. $p |] -> fv p \\ [x]
>           [$form| $p ∧ $q  |] -> combine p q
>           [$form| $p ∨ $q |] -> combine p q
>           [$form| $p ⊃ $q  |] -> combine p q
>           [$form| $p ⇔ $q |] -> combine p q
>           [$form| ^a |] -> fv a
>     where combine p q = Set.union (fv p) (fv q)

> instance Fv a => Fv [a] where
>   fv xs = Set.unions (map fv xs)

> generalize :: Formula -> Formula
> generalize fm = foldr All fm (fv fm) 

Function symbols with arity

> functions :: Formula -> [(Func, Int)]
> functions = F.atomUnion (\(R _ args) -> foldr (Set.union . funcs) [] args) 

> funcs :: Term -> [(Func, Int)]
> funcs (Var _) = []
> funcs (Fn f args) = foldr (Set.union . funcs) [(f, length args)] args 

> predicates :: Formula -> [(Func, Int)]
> predicates = F.atomUnion (\(R p args) -> [(p, length args)])

Environments

This is generally the correct type for substitutions.  There is one exception
in EqElim where Map Term Term is needed

Substitutions

> class Subst a where
>   apply :: Env -> a -> a

> instance Subst Term where
>   apply env tm = case tm of
>                  Var x -> case Map.lookup x env of
>                           Just t -> t
>                           Nothing -> tm
>                  Fn f args -> Fn f (map (apply env) args)

> instance Subst Rel where
>   apply env (R p args) = R p (map (apply env) args)

> instance Subst Formula where
>   apply env fm = case fm of 
>     [$form| ^a |] -> [$form| ^a' |] 
>       where a' = apply env a
>     [$form| ¬ $p |] -> [$form| ¬ $p' |]
>       where p' = apply env p
>     [$form| $p ∧ $q |] -> [$form| $p' ∧ $q' |]
>       where p' = apply env p 
>             q' = apply env q
>     [$form| $p ∨ $q |] -> [$form| $p' ∨ $q' |]
>       where p' = apply env p 
>             q' = apply env q
>     [$form| $p ⊃ $q |] -> [$form| $p' ⊃ $q' |]
>       where p' = apply env p 
>             q' = apply env q
>     [$form| $p ⇔ $q |] -> [$form| $p' ⇔ $q' |]
>       where p' = apply env p 
>             q' = apply env q
>     [$form| forall $x. $p |] -> applyq env All x p
>     [$form| exists $x. $p |] -> applyq env Ex x p
>     [$form| true |] -> [$form| true |]
>     [$form| false |] -> [$form| false |]

Substitute under a binder
The following functions need the type variable, as they are used at multiple types

> variant :: Var -> Vars -> Var
> variant x vars = if List.elem x vars then variant (x ++ "'") vars else x

> applyq :: Env -> (Var -> Formula -> Formula) 
>        -> Var -> Formula -> Formula
> applyq env quant x p = quant x' (apply ((x ↦ Var x') env) p)
>     where x' = if List.any (\k -> case Map.lookup k env of
>                                   Just v -> List.elem x (fv v)
>                                   Nothing -> False) (fv p \\ [x]) 
>                then variant x (fv(apply (Map.delete x env) p)) else x

> termval :: ([a], Var -> [b] -> b, Var -> [b] -> Bool) -> Map Var b -> Term -> b
> termval m@(_, func, _) v tm =
>   case tm of 
>     Var x -> case Map.lookup x v of
>                Nothing -> error "not in domain" 
>                Just y -> y
>     Fn f args -> func f (map (termval m v) args)

> holds :: ([a], Var -> [a] -> a, Var -> [a] -> Bool) -> Map Var a -> Formula -> Bool
> holds m@(domain, _, f) v fm =
>   case fm of 
>     [$form| ⊥ |] -> False
>     [$form| ⊤ |] -> True
>     Atom (R r args) -> f r (map (termval m v) args)
>     [$form| ¬ $p |] -> not(holds m v p)
>     [$form| $p ∧ $q |] -> holds m v p && holds m v q
>     [$form| $p ∨ $q |] -> holds m v p || holds m v q
>     [$form| $p ⊃ $q |] -> not (holds m v p) || holds m v q
>     [$form| $p ⇔ $q |] -> holds m v p == holds m v q
>     [$form| ∀ $x. $p |] -> List.all (\a -> holds m (Map.insert x a v) p) domain
>     [$form| exists $x. $p |] -> List.any (\a -> holds m (Map.insert x a v) p) domain

