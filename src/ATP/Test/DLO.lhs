
* Signature 

> module ATP.Test.DLO 
>   ( tests )
> where 

* Imports

> import Prelude 
> import qualified Data.Maybe as Maybe
> import qualified Test.HUnit as Test
> import Test.HUnit(Test(..), (~:), assert)

> import ATP.FormulaSyn
> import qualified ATP.DLO as DLO
> import qualified ATP.TestFormulas as Forms

* Tests

> mkTest :: (String, Formula) -> Test
> mkTest (s, f) = s ~: assert $ 
>   DLO.qelim (Maybe.fromJust (Forms.lookup s)) == f

> tests :: Test
> tests = "DLO" ~: TestList $ map mkTest
>   [ ("dlo1", [$form| ⊤ |]) 
>   , ("dlo2", [$form| ⊤ |]) 
>   , ("dlo3", [$form| x < y |]) 
>   , ("dlo4", [$form| ¬(b < a ∨ b < a) |]) 
>   , ("dlo5", [$form| ⊤ |]) 
>   , ("dlo6", [$form| ⊤ |]) 
>   , ("dlo7", [$form| ⊥ |]) 
>   , ("dlo8", [$form| ⊤ |]) 
>   , ("dlo9", [$form| ⊤ |]) 
>   , ("dlo10", [$form| ⊤ |]) 
>   , ("dlo11", [$form| ⊥ |]) 
>   , ("dlo12", [$form| ⊥ |]) 
>   , ("dlo13", [$form| x < y |]) 
>   , ("dlo14", [$form| ⊤ |]) 
>   , ("dlo15", [$form| ⊤ |]) 
>   , ("dlo16", [$form| ⊤ |]) 
>   , ("dlo17", [$form| ⊤ |]) 
>   , ("dlo18", [$form| ⊤ |]) 
>   , ("dlo19", [$form| x < y |]) 
>   , ("dlo20", [$form| x < y ∨ x < y ∨ x < y ∨ y = x |]) 
>   , ("dlo21", [$form| x < y ∨ x < y |]) 
>   , ("dlo22", [$form| ⊤ |]) 
>   , ("dlo23", [$form| ¬(x < z ∧ ¬(w < z)) |]) 
>   , ("dlo24", [$form| ⊥ |]) 
>   , ("dlo25", [$form| x < y |]) 
>   , ("dlo26", [$form| ⊤ |]) 
>   , ("dlo27", [$form| ¬(b < a ∨ b < a) |]) 
>   , ("dlo28", [$form| ¬(b < a) |]) 
>   , ("dlo29", [$form| ⊤ |]) 
>   , ("dlo30", [$form| ⊤ |]) 
>   ]



