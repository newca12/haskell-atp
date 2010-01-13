
* Signature 

> module ATP.Test.Dlo 
>   ( tests )
> where 

* Imports

> import Prelude 
> import qualified ATP.Dlo as Dlo
> import ATP.FormulaSyn
> import qualified ATP.TestFormulas as Forms
> import qualified Data.Maybe as Maybe
> import Test.HUnit(Test(..), (~:), (@=?))

* Tests

> tests :: Test
> tests = "Dlo" ~: map mkTest formulas
>   where mkTest (name, f) = name ~: 
>           f @=? Dlo.qelim (Maybe.fromJust (Forms.lookup name)) 

> formulas :: [(String, Formula)]
> formulas = 
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
>   , ("dlo31", [$form| ⊤ |]) 
>   , ("dlo32", [$form| ⊤ |]) 
>   , ("dlo33", [$form| ⊥ |]) 
>   ]



