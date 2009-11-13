
* Signature 

> module ATP.Test.Complex
>   ( tests )
> where 

* Imports

> import Prelude 
> import qualified ATP.Complex as Complex
> import ATP.FormulaSyn
> import qualified ATP.TestFormulas as Forms
> import qualified Data.Maybe as Maybe
> import qualified Test.HUnit as Test
> import Test.HUnit(Test(..), (~:), (@=?))

* Tests

> tests :: Test
> tests = "Complex" ~: map mkTest formulas
>   where mkTest (name, f) = name ~: 
>           f @=? (Complex.qelim $ Maybe.fromJust $ Forms.lookup name)

> formulas :: [(String, Formula)]
> formulas = 
>   [ ("cplx1", [$form| ⊤ |])
>   ]



