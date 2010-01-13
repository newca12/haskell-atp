
* Signature 

> module ATP.Test.Taut 
>   ( tests, qtests )
> where

* Imports

> import ATP.Util.Prelude
> import ATP.FormulaSyn
> import qualified ATP.Bdd as Bdd
> import qualified ATP.Dp as Dp
> import qualified ATP.Prop as Prop
> import Test.HUnit(Test(..), (~:), assert)
> import qualified Test.QuickCheck as Q
> import Test.QuickCheck (Property)

* HUnit

> forms :: [(String, Formula, Bool)]
> forms = 
>   [ ("p1", [$form| p ⊃ p |], True)
>   , ("p2", [$form| p ∧ q ⊃ q ∧ p |], True)
>   , ("p3", [$form| ⊥ |], False)
>   , ("p4", [$form| ⊤ |], True)
>   , ("p5", [$form| p ⇔ p |], True)
>   , ("p6", [$form| ¬ ¬ ((⊤ ⊃ p2) ⊃ (⊤ ⇔ p4)) ∨ (⊤ ⇔ ⊥ ∨ p8) |], False)
>   , ("p7", [$form| ((⊤ ∨ (⊤ ⇔ ⊥)) ∧ (p5 ∨ ⊤ ⊃ ⊥ ⊃ p0)) ∧ ((⊤ ⇔ ⊥) ∧ (p10 ⇔ ⊥) ⊃ ¬(p10 ∨ ⊤)) |], True)
>   , ("p8", [$form| (⊤ ⊃ ⊥) ⊃ ⊥ |], True)
>   , ("p9", [$form| (⊤ ⇔ ⊥) ⊃ ⊥ |], True)
>   , ("p10", [$form| (((⊤ ⇔ ⊤) ⊃ ¬⊥) ⊃ ¬(⊤ ∨ ⊥ ∧ ⊤)) ∨ ((⊥ ⊃ p5 ⇔ ¬(p7)) ⊃ ((⊥ ⇔ ⊤) ⇔ ⊥ ⇔ ⊤)) ∨ (⊤ ∨ ⊥ ⊃ (⊥ ⊃ ⊥ ⇔ p5 ∨ ⊥)) |], True)
>   ]

> mkTest :: String -> (Formula -> Bool) -> Test
> mkTest name p = name ~: TestList $ map fn forms
>  where
>   fn (s, f, b) = s ~: assert $ p f == b

> tests :: Test
> tests = "Taut" ~: [ mkTest "tautology" Prop.tautology
>                   , mkTest "dp" Dp.dptaut
>                   , mkTest "dpll" Dp.dplltaut
>                   , mkTest "bdd" Bdd.taut
>                   ]

* QuickCheck

> prop_tauts_same :: Property
> prop_tauts_same = Q.label "tauts_same" $
>   Q.forAll (Prop.forms 5) $ \f -> 
>     let p = Dp.dplltaut f in
>     p == Dp.dptaut f && p == Bdd.taut f 

> qtests :: IO ()
> qtests = Q.quickCheck prop_tauts_same

