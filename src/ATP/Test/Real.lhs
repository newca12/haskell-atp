
* Signature 

> module ATP.Test.Real
>   ( tests )
> where 

* Imports

> import Prelude 
> import qualified ATP.Real as Real
> import ATP.FormulaSyn
> import qualified ATP.TestFormulas as Forms
> import qualified Data.Maybe as Maybe
> import Test.HUnit(Test(..), (~:), (@=?))

* Tests

> tests :: Test
> tests = "Real" ~: map mkTest formulas
>   where mkTest (name, f) = name ~: 
>           f @=? Real.qelim (Maybe.fromJust $ Forms.lookup name)

> formulas :: [(String, Formula)]
> formulas = 
>   [ ("real0", [$form| ⊤ |])
>   , ("real1", [$form| ⊤ |])
>   , ("real2", [$form| ⊥ |])
>   , ("real3", [$form| ⊥ |])
>   , ("real4", [$form| ⊥ |])
>   , ("real5", [$form| ⊤ |])
>   , ("real7", [$form| ⊥ |])
>   , ("real8", [$form| ⊤ |])
>   , ("real9", [$form| ⊤ |])
>   ]



