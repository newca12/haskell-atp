
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
> import Test.HUnit(Test(..), (~:), (@=?))

* Tests

> tests :: Test
> tests = "Complex" ~: map mkTest formulas
>   where mkTest (name, f) = name ~: 
>           f @=? Complex.qelim (Maybe.fromJust $ Forms.lookup name)

> formulas :: [(String, Formula)]
> formulas = 
>   [ ("cplx1", [$form| ⊤ |])
>   , ("cplx3", [$form| ⊤ |])
>   , ("cplx4", [$form| ⊤ |])
>   , ("cplx5", [$form| ⊤ |])
>   , ("cplx6", [$form| ⊤ |])
>   , ("cplx7", [$form| ⊤ |])
>   , ("cplx8", [$form| ⊥ |])
>   , ("cplx9", [$form| ⊤ |])
>   , ("cplx10", [$form| ⊤ |])
>   , ("cplx11", [$form| ⊥ |])
>   , ("cplx12", [$form| ⊤ |])
>   , ("cplx16", [$form| ⊥ |])
>   , ("cplx17", [$form| ⊥ |])
>   , ("cplx18", [$form| ⊤ |])
>   , ("cplx19", [$form| ⊤ |])
>   , ("cplx20", [$form| ⊤ |])
>   , ("cplx21", [$form| ⊤ |])
>   , ("cplx22", [$form| ⊤ |])
>   , ("cplx23", [$form| ⊤ |])
>   , ("cplx24", [$form| ⊤ |])
>   , ("cplx25", [$form| ⊤ |])
>   , ("cplx26", [$form| ⊤ |])
>   , ("cplx27", [$form| ⊤ |])
>   , ("cplx28", [$form| ⊤ |])
>   , ("cplx29", [$form| ⊤ |])
>   , ("cplx30", [$form| ⊤ |])
>   , ("cplx33", [$form| ⊤ |])
>   , ("cplx34", [$form| ⊤ |])
>   , ("cplx35", [$form| ⊤ |])
>   , ("cplx39", [$form| ⊤ |])
>   ]



