
> module Test (empty)
> where

> newtype LList a = LList [a]



> empty :: LList a 
> empty = LList []

> ($) :: [a] -> LList a
> ($) = LList

-- > v :: LList Int
-- > v = LList [5]


> import qualified Text.PrettyPrint.HughesPJClass as PP
> import Text.PrettyPrint.HughesPJClass (pPrint)
> import FormulaSyn

> tmp = putStrLn $ PP.fullRender PP.PageMode 80 1.5 string_txt "" 
>  (pPrint [$fol| forall x. exists y. p(x, y) ==> forall z. q /\ exists y. p(x, y) ==> forall z. q |])

:m +Text.PrettyPrint.HughesPJClass
:set prompt "$ "
