
The front end for the automated theorem proving Haskell port.

* Pragmas 

> {-# OPTIONS_GHC -fno-warn-unused-imports -fno-warn-unused-binds #-}

* Signature

> module Main 
>   ( main ) 
> where 

* Imports

> import ATP.Util.Prelude
> import qualified ATP.Bdd as Bdd
> import qualified ATP.Combining as Combining
> import qualified ATP.Completion as Completion
> import qualified ATP.Complex as Complex
> import qualified ATP.Cong as Cong
> import qualified ATP.Cooper as Cooper
> import qualified ATP.Decidable as Decidable
> import qualified ATP.DefCnf as Cnf
> import qualified ATP.Dlo as Dlo
> import qualified ATP.Dp as Dp
> import qualified ATP.EqElim as EqElim
> import qualified ATP.Equal as Equal
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Geom as Geom
> import qualified ATP.Grobner as Grobner
> import qualified ATP.Herbrand as Herbrand
> import qualified ATP.Interpolation as Interpolation
> import qualified ATP.Intro as Intro
> import ATP.IntroSyn
> import qualified ATP.Meson as Meson
> import qualified ATP.Order as Order
> import qualified ATP.Paramodulation as Paramodulation
> import qualified ATP.Poly as Poly
> import qualified ATP.Prolog as Prolog
> import qualified ATP.Prop as Prop 
> import qualified ATP.PropExamples as PropExamples
> import qualified ATP.Qelim as Qelim
> import qualified ATP.Real as Real
> import qualified ATP.Resolution as Resolution
> import qualified ATP.Rewrite as Rewrite
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Stal as Stal
> import qualified ATP.Tableaux as Tableaux
> import qualified ATP.Test.Combining
> import qualified ATP.Test.Complex
> import qualified ATP.Test.Cooper
> import qualified ATP.Test.Dlo 
> import qualified ATP.Test.Fo
> import qualified ATP.Test.Grobner
> import qualified ATP.Test.Real
> import qualified ATP.Test.Taut
> import qualified ATP.TestFormulas as Forms
> import qualified ATP.Unif as Unif
> import ATP.Util.Impossible (catchImpossible)
> import qualified ATP.Util.Lex as Lex
> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.List as List
> import qualified ATP.Util.Log as Log
> import ATP.Util.Log (Priority)
> import qualified ATP.Util.Misc as Misc
> import qualified ATP.Util.Monad as M
> import qualified ATP.Util.Parse as P
> import ATP.Util.Parse (parse)
> import qualified ATP.Util.Print as PP
> import ATP.Util.Print (Print, pPrint, (<>), (<+>), ($+$))
> import qualified Codec.Binary.UTF8.String as UString
> import qualified Control.Exception as Exn
> import Control.Exception (Exception)
> import Data.Generics (Data, Typeable)
> import qualified Data.List as List
> import qualified Data.Maybe as Maybe
> import qualified System
> import qualified System.Console.GetOpt as Opt
> import System.Console.GetOpt (OptDescr(..), ArgDescr(..))
> import qualified System.Exit as Exit
> import qualified System.IO.UTF8 as S
> import qualified Test.HUnit as Test
> import Test.HUnit(Test(..), (~:))
> import qualified Test.QuickCheck.Test as QC

* Options

> type Args = [String]

> data Flag = Verbose Priority
>           | LogToTerm
>           | LogToFile
>           | FormulaFlag String
>   deriving (Eq, Show)

> type Flags = [Flag]

> instance Print Flag where
>   pPrint = PP.text . show

> decodeFlag :: Flag -> Flag
> decodeFlag (FormulaFlag s) = FormulaFlag $ UString.decodeString s
> decodeFlag f = f

> options :: [OptDescr Flag]
> options =
>  [ Option ['V'] ["Verbose"] (OptArg verbose (show Log.defaultPrio)) 
>      "Verbosity level.  (debug | info | warn | error)"
>  , Option ['T'] ["LogToTerm"] (NoArg LogToTerm)
>      "Log to terminal on stdout."
>  , Option ['F'] ["LogToFile"] (NoArg LogToFile)
>      "Log to the log file."
>  , Option ['f'] ["formula"] (ReqArg FormulaFlag "<formula>")
>      "Formula to process.  Used in a number of commands."
>  ]

'parseOptions' returns flags, arguments, and unknown flags.

> parseOptions :: Args -> IO (Flags, Args, [String])
> parseOptions argv = case Opt.getOpt' Opt.Permute options argv of
>   (o, n, u, []) -> return (o, n, u)
>   (_, _, _, errs) -> ioError $ userError $ concat errs ++ usageMsg

> verbose :: Maybe String -> Flag
> verbose Nothing = Verbose Log.defaultPrio
> verbose (Just s) = case Log.readPrio s of 
>   Nothing -> error $ "No such setting for 'verbose': " ++ s
>   Just p -> Verbose p

> usageMsg :: String
> usageMsg = Opt.usageInfo usage options 
>   where usage = PP.render block
>         block = PP.vcat [ PP.text "Possible commands:"
>                         , PP.nest 3 (PP.vcat (map group groups))
>                         , PP.text "For help on an individual command, type 'help <cmd>'."
>                         , PP.space
>                         , PP.text "Flags:"
>                         , PP.space 
>                         ]
>         group (s, coms) = PP.text ("=== " ++ s ++ " ===") $+$ PP.space $+$
>                           PP.nest 3 (PP.vcat (map com coms)) $+$ PP.space
>         com (Com s summ _ _) = PP.text (s ++ spaces s ++ ": " ++ summ)
>         spaces s = concat (replicate (20 - length s) " ")

Get a term from commandline options.

> getTerm :: Flags -> Args -> Term
> getTerm flags args = case (List.findFirst isFormulaFlag flags, args) of
>     (Just f, _) -> parse f
>     (Nothing, [n]) -> case Forms.lookupTerm n of 
>                          Nothing -> Exn.throw $ ComExn "Can't determine term"
>                          Just t -> t
>     _ -> Exn.throw $ ComExn "Can't determine term"
>   where isFormulaFlag (FormulaFlag f) = Just f
>         isFormulaFlag _ = Nothing

> getFormula :: Flags -> Args -> Formula
> getFormula flags args = case (List.findFirst isFormulaFlag flags, args) of
>     (Just f, _) -> parse f
>     (Nothing, [n]) -> case Forms.lookup n of 
>                          Nothing -> Exn.throw $ ComExn "Can't determine formula"
>                          Just f -> f
>     (Nothing, ["prime", n]) -> PropExamples.prime $ read n
>     (Nothing, ["adder", n, m]) -> PropExamples.mkAdderTest (read n) (read m)
>     (Nothing, ["ramsey", s, t, n]) -> PropExamples.ramsey (read s) (read t) (read n)
>     _ -> Exn.throw $ ComExn "Can't determine formula"
>   where isFormulaFlag (FormulaFlag f) = Just f
>         isFormulaFlag _ = Nothing

Get a Prolog program from commandline options.

> getProgram :: Flags -> Args -> ([String], String)
> getProgram _ _ = error "Unimplemented" 

Get rewriting rules.

> getRewrites :: Flags -> Args -> ([Formula], Term)
> getRewrites _ _ = error "Unimplemented" 

* Commands

> data Command = Com { name :: String
>                    , summary :: String
>                    , desc :: PP.Doc
>                    , _command :: Flags -> Args -> IO ()
>                    } 

> newtype ComExn = ComExn String
>   deriving (Show, Data, Typeable)

> instance Exn.Exception ComExn where

** Groups

> type Group = (String, [Command])

> groups :: [Group]
> groups = [ ("Misc",
>             [ version, help, echo, bug ])
>          , ("Test",
>             [ test, showTest ])
>          , ("Parsing",
>             [ parseExpr, parseTerm, parseForm ])
>          , ("Formula kung fu", 
>             [ nnf, cnf, dnf, defcnf, pnf, skolem ])
>          , ("Term kung fu", 
>             [ polytest ])
>          , ("Propositional decision procedures",
>             [ truthtable, tautology, dp, dpll, stalmarck, bddtaut ])
>          , ("Basic Herbrand methods",
>             [ gilmore, davisputnam ])
>          , ("Tableaux",
>             [ prawitz, tab, splittab ])
>          , ("Resolution",
>             [ basicResolution, resolution, positiveResolution
>             , sosResolution ])
>          , ("Prolog",
>             [ hornprove, prolog ])
>          , ("MESON",
>             [ basicMeson, meson ])
>          , ("Equality",
>             [ bmeson, paramod, ccvalid, rewrite ])
>          , ("Decidable problems",
>             [ aedecide, dlo, dlovalid, cooper, slowNelop, nelop, nelopDLO, complex, real, grobner ])
>          ]

> commands :: [Command]
> commands = concat (map snd groups)

** Misc

> help :: Command
> help = Com "help" summ usage f
>   where summ = "Show a help message."
>         usage = PP.vcat [ PP.text "help"
>                         , PP.text "help <command>" ]
>         f [] [] = S.putStrLn usageMsg
>         f [] [com] = case List.find (\c -> name c == com) commands of
>                     Nothing -> S.putStrLn $ "Can't find command: " ++ com
>                     Just c -> PP.putStrLn $ 
>                       PP.vcat [ PP.text $ "Command : " ++ name c
>                               , PP.text $ "Summary : " ++ summary c
>                               , PP.text   "Usage   : " <> desc c
>                               ] 
>         f _ _ = Exn.throw $ ComExn "Bad arguments"

> version :: Command
> version = Com "version" summ usage f
>   where summ = "Show the current version."
>         usage = PP.text "version"
>         f [] [] = S.putStrLn $ "Version " ++ Misc.version
>         f _ _ = Exn.throw $ ComExn "'version' takes no arguments"

> echo :: Command
> echo = Com "echo" summ usage f
>   where summ = "Echo the input arguments"
>         usage = PP.text "echo -flag1 -flag2 arg1 arg2"
>         f :: Flags -> Args -> IO ()
>         f fs args = S.putStrLn (show fs ++ show args)

> bug :: Command
> bug = Com "bug" summ usage f
>   where summ = "Run the bug of the moment."
>         usage = PP.text "bug ..."
>         f _ _ = error "Bug"

** Tests

HUnit

> tests :: Test
> tests = "All" ~: TestList 
>   [ ATP.Test.Taut.tests 
>   , ATP.Test.Fo.tests 
>   , ATP.Test.Dlo.tests 
>   , ATP.Test.Cooper.tests 
>   , ATP.Test.Combining.tests 
>   , ATP.Test.Complex.tests 
>   , ATP.Test.Real.tests 
>   , ATP.Test.Grobner.tests 
>   ]

Quickcheck

> qtests :: IO ()
> qtests = do List.tests
>             Prop.tests
>             Cnf.tests
>             Bdd.tests
>             ATP.Test.Taut.qtests

> test :: Command
> test = Com "test" summ usage f
>   where summ = "Run unit tests."
>         usage = PP.text "test"
>         f [] [] = do 
>           S.putStrLn "Running all tests.  This may take awhile."
>           S.putStrLn "HUnit Tests"
>           M.ignore $ Test.runTestTT tests
>           S.putStrLn "QuickCheck"
>           qtests
>         f _ [t] = case t of
>           "complex" -> M.ignore $ Test.runTestTT ATP.Test.Complex.tests
>           "real" -> M.ignore $ Test.runTestTT ATP.Test.Real.tests
>           "grobner" -> M.ignore $ Test.runTestTT ATP.Test.Grobner.tests
>           _ -> Exn.throw $ ComExn $ "Can't find test suite: " ++ t
>         f _ _ = Exn.throw $ ComExn "'test' takes no arguments."

Show a test formula

> showTest :: Command
> showTest = Com "show" summ usage f
>   where summ = "Show a formula."
>         usage = PP.vcat [ PP.text "show -f <formula>"
>                         , PP.text "show <id>"
>                         , PP.text "show prime 5"
>                         , PP.text "show ramsey 2 3 5"
>                         ]
>         f flags args = PP.putStrLn $ pPrint $ getFormula flags args

** Parsing

> parseExpr :: Command
> parseExpr = Com "expr" summ usage f
>   where summ = "Parse an expression."
>         usage = PP.vcat [ PP.text "expr <expr>"
>                         , PP.text "expr 'x + y * 7'" ]
>         f [] [s] = do
>           S.putStrLn $ "Parsing <<" ++ s ++ ">>"
>           let x :: Expr = parse s
>           PP.putStrLn $ pPrint x
>         f _ _ = Exn.throw $ ComExn "Bad arguments"

> parseTerm :: Command
> parseTerm = Com "term" summ usage f
>   where summ = "Parse a term." 
>         usage = PP.vcat [ PP.text "term <term>"
>                         , PP.text "term 'p(x, y) + 8'" ]
>         f [] [s] = do
>           S.putStrLn $ "Parsing <<" ++ s ++ ">>"
>           let x :: Term = parse s
>           PP.putStrLn $ pPrint x
>         f _ _ = Exn.throw $ ComExn "Bad arguments"

> parseForm :: Command
> parseForm = Com "form" summ usage f
>   where summ = "Parse a formula." 
>         usage = PP.vcat [ PP.text "form <formula>"
>                         , PP.text "form '⊤ ∧ f(c) ⊃ ∀ x. P(x)'" ]
>         f [] [s] = do
>           S.putStrLn $ "Parsing <<" ++ s ++ ">>"
>           let x :: Formula = parse s
>           PP.putStrLn $ pPrint x
>         f _ _ = Exn.throw $ ComExn "Bad arguments"

** Formula manipulation

> nnf :: Command
> nnf = Com "nnf" "Negation normal form." usage f
>   where usage = PP.vcat [ PP.text "nnf -f <formula>"
>                         , PP.text "nnf <id>" ]
>         f flags args = PP.putStrLn $ pPrint $ Prop.nnf fm
>           where fm = getFormula flags args

> cnf :: Command
> cnf = Com "cnf" "Conjunctive normal form." usage f
>   where usage = PP.vcat [ PP.text "cnf -f <formula>"
>                         , PP.text "cnf <id>" ]
>         f flags args = PP.putStrLn $ pPrint $ Prop.cnf fm
>           where fm = getFormula flags args

> dnf :: Command
> dnf = Com "dnf" "Disjunctive normal form." usage f
>   where usage = PP.vcat [ PP.text "dnf -f <formula>"
>                         , PP.text "dnf <id>" ]
>         f flags args = PP.putStrLn $ pPrint $ Prop.dnf fm
>           where fm = getFormula flags args

> defcnf :: Command
> defcnf = Com "defcnf" "Conjunctive normal form." usage f
>   where usage = PP.vcat [ PP.text "defcnf -f <formula>"
>                         , PP.text "defcnf <id>" ]
>         f flags args = PP.putStrLn $ pPrint $ Cnf.defcnf fm
>           where fm = getFormula flags args
> pnf :: Command
> pnf = Com "pnf" "Prenex normal form" usage f
>   where usage = PP.vcat [ PP.text "pnf -f <formula>"
>                         , PP.text "pnf <id>" ] 
>         f flags args = PP.putStrLn $ pPrint $ Skolem.pnf fm
>           where fm = getFormula flags args

> skolem :: Command
> skolem = Com "skolem" "Skolem normal form" usage f
>   where usage =  PP.vcat [ PP.text "skolem -f <formula>"
>                          , PP.text "skolem <id>" ] 
>         f flags args = PP.putStrLn $ pPrint $ Skolem.skolemize fm
>           where fm = getFormula flags args

> polytest :: Command
> polytest = Com "polytest" "Polynomial normalization" usage f
>   where usage =  PP.vcat [ PP.text "polytest -f <term>"
>                          , PP.text "polytest <id>" ] 
>         f flags args = PP.putStrLn $ pPrint $ Poly.polynate (Fol.fv tm) tm
>           where tm = getTerm flags args

** Propositional solvers

> run :: Print a => (Formula -> IO a) -> Flags -> Args -> IO ()
> run f flags args = 
>   let fm = getFormula flags args in
>   do res <- f fm 
>      --PP.putStrLn $ pPrint (flags, args)
>      PP.putStrLn $ pPrint fm
>      PP.putStrLn $ pPrint res

> truthtable :: Command
> truthtable = Com "truthtable" "Show propositional truth table" usage f
>   where usage = PP.vcat [ PP.text "truthtable -f <formula>"
>                         , PP.text "truthtable <id>" ]
>         f flags args = S.putStrLn $ Prop.truthtable fm
>           where fm = getFormula flags args

> tautology :: Command
> tautology = Com "tautology" "Tautology checker via truth tables" usage f
>   where usage = PP.vcat [ PP.text "tautology -f <formula>"
>                         , PP.text "tautology <id>"
>                         , PP.text "tautology prime 17"
>                         , PP.text "tautology ramsey 2 3 5"]
>         f = run (return . Prop.tautology)

> dp :: Command
> dp = Com "dp" "Davis-Putnam procedure (propositional)" usage f
>   where usage = PP.vcat [ PP.text "dp -f <formula>"
>                         , PP.text "dp <id>"
>                         , PP.text "dp prime 17"
>                         , PP.text "dp ramsey 2 3 5"]
>         f = run (return . Dp.dptaut)

> dpll :: Command
> dpll = Com "dpll" summ usage f
>   where summ = "Davis-Putnam-Loveland-Logemann procedure (propositional)" 
>         usage = PP.vcat [ PP.text "dpll -f <formula>"
>                         , PP.text "dpll <id>"
>                         , PP.text "dpll prime 17"
>                         , PP.text "dpll ramsey 2 3 5"]
>         f = run (return . Dp.dplltaut)

> stalmarck :: Command
> stalmarck = Com "stalmarck" summ usage f
>   where summ = "Davis-Putnam-Loveland-Logemann procedure (propositional)" 
>         usage = PP.vcat [ PP.text "stalmarck -f <formula>"
>                         , PP.text "stalmarck <id>"
>                         , PP.text "stalmarck prime 17"
>                         , PP.text "stalmarck ramsey 2 3 5"]
>         f = run Stal.stalmarck

> bddtaut :: Command
> bddtaut = Com "bddtaut" summ usage f
>   where summ = "Tautology checking via BDDs"
>         usage = PP.vcat [ PP.text "bddtaut -f <formula>"
>                         , PP.text "bddtaut <id>"
>                         , PP.text "bddtaut prime 17"
>                         , PP.text "bddtaut ramsey 2 3 5"]
>         f = run (return . Bdd.taut)

** First order solvers

> gilmore :: Command
> gilmore = Com "gilmore" "Gilmore procedure." usage f
>   where usage = PP.vcat [ PP.text "gilmore -f <formula>"
>                         , PP.text "gilmore <id>"
>                         ] 
>         f = run Herbrand.gilmore

> davisputnam :: Command
> davisputnam = Com "davisputnam" "Davis-Putnam procedure." usage f
>   where usage = PP.vcat [ PP.text "davisputnam -f <formula>"
>                         , PP.text "davisputnam <id>"
>                         ] 
>         f = run Herbrand.davisputnam

> prawitz :: Command
> prawitz = Com "prawitz" "Prawitz procedure." usage f
>   where usage = PP.vcat [ PP.text "prawitz -f <formula>"
>                         , PP.text "prawitz <id>"
>                         ] 
>         f = run (return . Tableaux.prawitz)

> tab :: Command
> tab = Com "tab" "Analytic tableaux procedure." usage f
>   where usage = PP.vcat [ PP.text "tab -f <formula>"
>                         , PP.text "tab <id>"
>                         ] 
>         f = run Tableaux.tab

> splittab :: Command
> splittab = Com "splittab" "Analytic tableaux procedure." usage f
>   where usage = PP.vcat [ PP.text "splittab -f <formula>"
>                         , PP.text "splittab <id>"
>                         ] 
>         f = run Tableaux.splittab

> basicResolution :: Command
> basicResolution = Com "basicResolution" "Resolution procedure." usage f
>   where usage = PP.vcat [ PP.text "basicResolution -f <formula>"
>                         , PP.text "basicResolution <id>"
>                         ] 
>         f = run Resolution.basicResolution

> resolution :: Command
> resolution = Com "resolution" "Resolution procedure." usage f
>   where usage = PP.vcat [ PP.text "resolution -f <formula>"
>                         , PP.text "resolution <id>"
>                         ] 
>         f = run Resolution.resolution

> positiveResolution :: Command
> positiveResolution = Com "positiveResolution" "Resolution procedure." usage f
>   where usage = PP.vcat [ PP.text "positiveResolution -f <formula>"
>                         , PP.text "positiveResolution <id>"
>                         ] 
>         f = run Resolution.positiveResolution

> sosResolution :: Command
> sosResolution = Com "sosResolution" "Resolution procedure." usage f
>   where usage = PP.vcat [ PP.text "sosResolution -f <formula>"
>                         , PP.text "sosResolution <id>"
>                         ] 
>         f = run Resolution.sosResolution

> hornprove :: Command
> hornprove = Com "hornprove" summ usage f
>   where summ = "Basic horn clause prover using backchaining"
>         usage = PP.vcat [ PP.text "hornprove -f <formula>"
>                         , PP.text "hornprove <id>"
>                         ] 
>         f = run Prolog.hornprove

> prolog :: Command
> prolog = Com "prolog" "Prolog interpreter" usage f
>   where usage = PP.vcat [ PP.text "prolog -f <formula>"
>                         , PP.text "prolog -file <file>"
>                         , PP.text "prolog <id>"
>                         ] 
>         f flags args = case Prolog.prolog prog c of
>                          Nothing -> S.putStrLn "Unsolvable"
>                          Just eqs -> PP.putStrLn $ pPrint eqs
>           where (prog, c) = getProgram flags args

> basicMeson :: Command
> basicMeson = Com "basicMeson" "Basic MESON procedure." usage f
>   where usage = PP.vcat [ PP.text "basicMeson -f <formula>"
>                         , PP.text "basicMeson <id>"
>                         ] 
>         f = run Meson.basicMeson

> meson :: Command
> meson = Com "meson" "MESON procedure." usage f
>   where usage = PP.vcat [ PP.text "meson -f <formula>"
>                         , PP.text "meson <id>"
>                         ] 
>         f = run Meson.meson

> bmeson :: Command
> bmeson = Com "bmeson" "MESON procedure with equality elimination." usage f
>   where usage = PP.vcat [ PP.text "bmeson -f <formula>"
>                         , PP.text "bmeson <id>"
>                         ] 
>         f = run EqElim.bmeson

> paramod :: Command
> paramod = Com "paramod" "Paramodulation." usage f
>   where usage = PP.vcat [ PP.text "paramod -f <formula>"
>                         , PP.text "paramod <id>"
>                         ] 
>         f = run Paramodulation.paramodulation

> ccvalid :: Command
> ccvalid = Com "ccvalid" "Congruence closure." usage f
>   where usage = PP.vcat [ PP.text "ccvalid -f <formula>"
>                         , PP.text "ccvalid <id>"
>                         ] 
>         f = run (return . Cong.ccvalid)

> rewrite :: Command
> rewrite = Com "rewrite" "Rewriting" usage f
>   where usage = PP.vcat [ PP.text "rewrite -file <file>"
>                         , PP.text "rewrite -f <formula>"
>                         ] 
>         f flags args = PP.putStrLn $ pPrint $ Rewrite.rewrite fs t 
>           where (fs, t) = getRewrites flags args 

> aedecide :: Command
> aedecide = Com "aedecide" "Decide AE problems." usage f
>   where usage = PP.vcat [ PP.text "aedecide -f <formula>"
>                         , PP.text "aedecide <id>"
>                         ] 
>         f = run (return . Decidable.aedecide)

> dlo :: Command
> dlo = Com "dlo" "Dense linear orders." usage f
>   where usage = PP.vcat [ PP.text "dlo -f <formula>"
>                         , PP.text "dlo <id>"
>                         ] 
>         f = run (return . Dlo.qelim)

> dlovalid :: Command
> dlovalid = Com "dlovalid" "Dense linear orders." usage f
>   where usage = PP.vcat [ PP.text "dlovalid -f <formula>"
>                         , PP.text "dlovalid <id>"
>                         ] 
>         f = run (return . Dlo.valid)

> cooper :: Command
> cooper = Com "cooper" "Cooper's algorithm for Presburger arithmetic." usage f
>   where usage = PP.vcat [ PP.text "cooper -f <formula>"
>                         , PP.text "cooper <id>"
>                         ] 
>         f = run (return . Cooper.integerQelim)

> nelop :: Command
> nelop = Com "nelop" summ usage f
>   where summ = "The Nelson-Oppen method, linear integer arithmetic"
>         usage = PP.vcat [ PP.text "nelop -f <formula>"
>                         , PP.text "nelop <id>" ] 
>         f = run (return . Combining.nelopInt)

> slowNelop :: Command
> slowNelop = Com "slowNelop" summ usage f
>   where summ = "The Nelson-Oppen method, linear integer arithmetic"
>         usage = PP.vcat [ PP.text "slowNelop -f <formula>"
>                         , PP.text "slowNelop <id>" ] 
>         f = run (return . Combining.slowNelopInt)

> nelopDLO :: Command
> nelopDLO = Com "nelop-dlo" summ usage f
>   where summ = "The Nelson-Oppen method, dense linear orders"
>         usage = PP.vcat [ PP.text "nelop -f <formula>"
>                         , PP.text "nelop <id>" ] 
>         f = run (return . Combining.nelopDlo)

> complex :: Command
> complex = Com "complex" summ usage f
>   where summ = "Complex quantifier elimination"
>         usage = PP.vcat [ PP.text "complex -f <formula>"
>                         , PP.text "complex <id>" ] 
>         f = run (return . Complex.qelim)

> real :: Command
> real = Com "real" summ usage f
>   where summ = "Real quantifier elimination"
>         usage = PP.vcat [ PP.text "real -f <formula>"
>                         , PP.text "real <id>" ] 
>         f = run (return . Real.qelim)

> grobner :: Command
> grobner = Com "grobner" summ usage f
>   where summ = "Grobner basis validity procedure"
>         usage = PP.vcat [ PP.text "grobner -f <formula>"
>                         , PP.text "grobner <id>" ] 
>         f = run Grobner.decide

* Top

> main :: IO ()
> main = System.getArgs >>= doit

> doit :: Args -> IO ()
> doit args = Lib.timeIO $ do 
>   S.putStrLn "Welcome to Haskell ATP!"
>   -- Parse arguments.  Opts is the unknown options that will be parsed by
>   -- the individual prover.  
>   (flags, args', opts) <- parseOptions args
>   let flags' = map decodeFlag flags
>   -- It's important to decode the command line arguments, since they may
>   -- be in Unicode syntax.  UString seems to work.
>       uargs = map UString.decodeString args'
>       uopts = map UString.decodeString opts
>       prio = maybe Log.defaultPrio id (List.findFirst getPrio flags')
>   -- Initialize the log file
>       logToFile = elem LogToFile flags
>   Log.initialize prio logToFile (elem LogToTerm flags)
>   -- Now we can start logging.  Start with a notification that
>   -- logging is taking place!
>   if logToFile
>     then Log.stdout ("Logging output to file: " ++ Log.logFileName) 
>     else return ()
>   Log.infoM' "Atp" $
>     PP.vcat [ PP.text "input        :" <+> pPrint args
>             , PP.text "flags        :" <+> pPrint flags
>             , PP.text "unknown opts :" <+> pPrint uopts 
>             , PP.text "args         :" <+> pPrint uargs ] 
>   -- Run the requested command
>   Exn.catch (forward flags' $ uopts ++ uargs) handle
>   `catchImpossible` \e -> do
>    S.putStr $ show e
>    Exit.exitFailure


Handle exceptions

> handle :: ComExn -> IO ()
> handle (ComExn s) = S.putStrLn s

Determine logging priority.

> getPrio :: Flag -> Maybe Priority
> getPrio (Verbose p) = Just p
> getPrio _ = Nothing

Forward a command from the top level to the requested command.

> forward :: Flags -> Args -> IO ()
> forward _ [] = S.putStrLn usageMsg
> forward flags (com : args) = 
>   case List.find (\c -> name c == com) commands of
>     Nothing -> S.putStrLn $ "No such command: " ++ com
>     Just (Com _ _ _ f) -> f flags args
