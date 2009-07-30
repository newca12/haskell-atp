
The front end for the automated theorem proving Haskell port.

> module Main ( main ) where 

> import Prelude 

-- > import qualified List
-- > import qualified System.IO as IO
-- > import Text.Printf(printf)
-- > import qualified Text.PrettyPrint.HughesPJ as PP
-- > import Text.PrettyPrint.HughesPJ( ($+$) ) 
-- > import qualified Control.Exception as Exn

Basics

> import qualified Lib
> import qualified Lex
> import qualified ListSet 

Intro

> import qualified IntroSyn
> import qualified Intro

Formulas 

> import qualified FormulaSyn
> import qualified Formula

Propositional logic

> import qualified Prop 
> import qualified PropExamples
> import qualified DefCnf
> import qualified Fol
> import qualified TestFormulas
> import qualified Dp
> import qualified Herbrand
> import qualified Unif
> import qualified Skolem
> import qualified Tableaux
> import qualified Resolution
> import qualified Prolog
> import qualified Meson

-- > import qualified Equal
-- > import qualified Cong
-- > import qualified Rewrite
-- > import qualified EqElim
-- > import qualified Order()
-- > import qualified Completion()
-- > import qualified Paramodulation
-- > import qualified Decidable
-- > import qualified Qelim
-- > import qualified Cooper
-- > import qualified Complex()
-- > import qualified Interpolation()
-- > import qualified Combining

> main :: IO ()
> main = do putStrLn "Hello World!"
