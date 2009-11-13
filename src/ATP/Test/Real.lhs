
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
> import qualified Test.HUnit as Test
> import Test.HUnit(Test(..), (~:), (@=?))

* Tests

> tests :: Test
> tests = "Real" ~: map mkTest formulas
>   where mkTest (name, f) = name ~: 
>           f @=? (Real.qelim $ Maybe.fromJust $ Forms.lookup name)

> formulas :: [(String, Formula)]
> formulas = 
>   [ ("real0", [$form| ⊤ |])
>   ]



