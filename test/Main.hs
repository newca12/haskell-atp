{-# LANGUAGE NoImplicitPrelude #-}

module Main (main) where

import Prelude (IO, (>), (||), putStrLn, ($))
import qualified Test.HUnit as HUnit
import System.Exit (exitFailure, exitSuccess)

-- HUnit test suites from the library
import qualified ATP.Test.Taut       as Taut
import qualified ATP.Test.Fo         as Fo
import qualified ATP.Test.Dlo        as Dlo
import qualified ATP.Test.Cooper     as Cooper
import qualified ATP.Test.Combining  as Combining
import qualified ATP.Test.Complex    as Complex
import qualified ATP.Test.Real       as Real
import qualified ATP.Test.Grobner    as Grobner

-- QuickCheck test suites from the library
import qualified ATP.Util.List as List
import qualified ATP.Prop      as Prop
import qualified ATP.DefCnf    as DefCnf
import qualified ATP.Bdd       as Bdd

allTests :: HUnit.Test
allTests = HUnit.TestLabel "All" $ HUnit.TestList
  [ Taut.tests
  , Fo.tests
  , Dlo.tests
  , Cooper.tests
  , Combining.tests
  , Complex.tests
  , Real.tests
  , Grobner.tests
  ]

main :: IO ()
main = do
  -- Run HUnit tests
  putStrLn "=== HUnit Tests ==="
  counts <- HUnit.runTestTT allTests
  putStrLn ""

  -- Run QuickCheck tests
  putStrLn "=== QuickCheck Tests ==="
  List.tests
  Prop.tests
  DefCnf.tests
  Bdd.tests
  Taut.qtests

  -- Report result
  if HUnit.errors counts > 0 || HUnit.failures counts > 0
    then exitFailure
    else exitSuccess
