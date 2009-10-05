
The front end for the automated theorem proving Haskell port.

* Pragmas 

> {-# OPTIONS_GHC -fno-warn-unused-imports #-}

* Signature

> module Main ( main ) where 

* Imports

> import Prelude hiding (putStr, putStrLn, print)
> import qualified System
> import qualified System.IO.UTF8 as S
> import qualified System.Console.GetOpt as Opt
> import System.Console.GetOpt (OptDescr(..), ArgDescr(..))
> import qualified Codec.Binary.UTF8.String as UString
> import qualified Control.Exception as Exn
> import qualified Data.Maybe as Maybe
> import qualified Data.List as List
> import qualified Test.HUnit as Test
> import Test.HUnit(Test(..), (~:))

Basics

> import qualified ATP.Util.List as List
> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.Lex as Lex
> import qualified ATP.Util.Parse as P
> import ATP.Util.Parse (parse)
> import qualified ATP.Util.Print as PP
> import ATP.Util.Print (Pretty, pPrint, (<+>), ($+$))
> import qualified ATP.Util.Log as Log
> import ATP.Util.Log (Priority)
> import qualified ATP.Util.Misc as Misc
> import qualified ATP.Util.Monad as M

Intro

> import ATP.IntroSyn
> import qualified ATP.Intro as Intro

Formulas 

> import ATP.FormulaSyn
> import qualified ATP.Formula as F

Propositional logic

> import qualified ATP.Prop  as Prop 
> import qualified ATP.PropExamples as PropExamples
> import qualified ATP.DefCNF as CNF
> import qualified ATP.FOL as FOL
> import qualified ATP.DP as DP

First order logic

> import qualified ATP.Skolem as Skolem
> import qualified ATP.Herbrand as Herbrand
> import qualified ATP.Unif as Unif
> import qualified ATP.Tableaux as Tableaux
> import qualified ATP.Resolution as Resolution
> import qualified ATP.Prolog as Prolog
> import qualified ATP.Meson as Meson
> import qualified ATP.Equal as Equal
> import qualified ATP.Cong as Cong
> import qualified ATP.Rewrite as Rewrite
> import qualified ATP.Order as Order
> import qualified ATP.Completion as Completion
> import qualified ATP.EqElim as EqElim
> import qualified ATP.Paramodulation as Paramodulation
> import qualified ATP.Decidable as Decidable
> import qualified ATP.Qelim as Qelim
> import qualified ATP.Cooper as Cooper
> import qualified ATP.Poly as Poly
> import qualified ATP.Complex as Complex
> import qualified ATP.Real as Real
> import qualified ATP.Grobner as Grobner
> import qualified ATP.Geom as Geom
> import qualified ATP.Interpolation as Interpolation
> import qualified ATP.Combining as Combining

Tests

> import qualified ATP.TestFormulas as Forms

* Top

> type Args = [String]

> main :: IO ()
> main = do 
>   S.putStrLn "Welcome to Haskell ATP!"
>   S.putStrLn ""
>   -- Get command line arguments
>   args <- System.getArgs
>   -- Parse arguments.  Opts is the unknown options that will be parsed by
>   -- the individual prover.  
>   (flags, args', opts) <- parseOptions args
>   -- It's important to decode the command line arguments, since they may
>   -- be in Unicode syntax.  UString seems to work.
>   let uargs = map UString.decodeString args'
>       uopts = map UString.decodeString opts
>       prio = maybe Log.defaultPrio id (List.findFirst getPrio flags)
>   -- Initialize the log file
>   let logToFile = elem LogToFile flags
>   Log.initialize prio logToFile (elem LogToTerm flags)
>   -- Now we can start logging.  Start with a notification that
>   -- logging is taking place!
>   if logToFile
>     then Log.stdout ("Logging output to file: " ++ Log.logFileName) 
>     else return ()
>   Log.infoM' "ATP" $ PP.vcat [ PP.text "flags        :" <+> pPrint flags
>                              , PP.text "args         :" <+> pPrint uargs  
>                              , PP.text "unknown opts :" <+> pPrint uopts ]
>   -- Run the requested command
>   forward uargs

Determine logging priority.

> getPrio :: Flag -> Maybe Priority
> getPrio (Verbose p) = Just p
> getPrio _ = Nothing

Forward a command from the top level to the requested command.

> forward :: Args -> IO ()
> forward [] = S.putStrLn usage
> forward (com : args) = 
>   case lookup com (map (\c@(n,_,_) -> (n,c)) commands) of
>     Nothing -> S.putStrLn $ "No such command: " ++ com
>     Just (_, _, f) -> f args

* Commands

> type Command = (String, String, Args -> IO ())
> type Group = (String, [Command])

> groups :: [Group]
> groups = [ ("Misc",
>             [ version
>             , help
>             , echo
>             , bug ])
>          , ("Test",
>             [ test
>             , showTest ])
>          , ("Parsing",
>             [ parseExpr
>             , parseTerm
>             , parseForm ])
>          , ("Propositional formulas", 
>             [ nnf
>             , cnf
>             , dnf
>             , defcnf
>             , truthtable ])
>          , ("Propositional decision procedures",
>             [ tautology
>             , dp
>             , dpll ])
>          , ("First order formulas",
>             [ pnf
>             , skolemize ])
>          , ("Basic Herbrand methods",
>             [ gilmore
>             , davisputnam ])
>          , ("Unification",
>             [ unify ])
>          , ("Tableaux",
>             [ prawitz
>             , tab
>             , splittab ])
>          , ("Resolution",
>             [ basicResolution
>             , resolution
>             , positiveResolution
>             , sosResolution ])
>          , ("Prolog",
>             [ hornprove
>             , prolog ])
>          , ("MESON",
>             [ basicMeson
>             , meson ])
>          , ("Equality",
>             [ ccvalid
>             , rewrite
>             , bmeson 
>             , paramodulation])
>          , ("Decidable problems",
>             [ aedecide
>             , dlo
>             , pres
>             , nelopInt
>             ])
>          ]

> commands :: [Command]
> commands = concat (map snd groups)

** Misc

> help :: Command
> help = ("help", "Show a help message.", f)
>   where f [] = S.putStrLn usage
>         f _ = do S.putStrLn "'help' takes no arguments"
>                  S.putStrLn usage

> version :: Command
> version = ("version", "Show the version..", f)
>   where f [] = S.putStrLn $ "Version " ++ Misc.version
>         f _ = S.putStrLn "'version' takes no arguments"

> echo :: Command
> echo = ("echo", "Echo the input arguments", f)
>   where f args = S.putStrLn $ show args

> bug :: Command
> bug = ("bug", "Run the bug of the moment.", f)
>   where f _ = error "Bug"

** Tests

> tests :: Test
> tests = "All" ~: TestList []

> test :: Command
> test = ("test", "Run unit tests.", f)
>   where f [] = do 
>          S.putStrLn "Running all tests.  This may take awhile."
>          M.ignore $ Test.runTestTT tests
>         f _ = S.putStrLn "'test' takes no arguments."

Show a test formula

> showTest :: Command
> showTest = ("show", "Show a test formula.", f)
>   where f [s] = case Forms.lookup s of
>           Nothing -> S.putStrLn $ "Can't find test: " ++ s
>           Just ψ -> PP.putStrLn $ pPrint ψ
>         f _ = S.putStrLn "usage: show <formula id>"

** Parsing

> parseExpr :: Command
> parseExpr = ("expr", "Parse an expression.", f)
>   where f [s] = do
>           let s' = UString.decodeString s
>           S.putStrLn $ "Parsing <<" ++ s' ++ ">>"
>           let x :: Expr = parse s'
>           PP.putStrLn $ pPrint x
>         f _ = S.putStrLn "usage: expr <expr>"

> parseTerm :: Command
> parseTerm = ("term", "Parse a term.", f)
>   where f [s] = do
>           let s' = UString.decodeString s
>           S.putStrLn $ "Parsing <<" ++ s' ++ ">>"
>           let x :: Term = parse s'
>           PP.putStrLn $ pPrint x
>         f _ = S.putStrLn "usage: term <term>"

> parseForm :: Command
> parseForm = ("form", "Parse a formula.", f)
>   where f [s] = do
>           let s' = UString.decodeString s
>           S.putStrLn $ "Parsing <<" ++ s' ++ ">>"
>           let x :: Formula = parse s'
>           PP.putStrLn $ pPrint x
>         f _ = S.putStrLn "usage: form <formula>"

** Formula manipulation

> nnf :: Command
> nnf = ("nnf", 
>        "negation normal form",
>        PP.putStrLn . pPrint . Prop.nnf . parse . head)

> cnf :: Command
> cnf = ("cnf", 
>        "conjunctive normal form",
>        PP.putStrLn . pPrint . Prop.cnf . parse . head)

> dnf :: Command
> dnf = ("dnf", 
>        "disjunctive normal form",
>        PP.putStrLn . pPrint . Prop.dnf . parse . head)

> defcnf :: Command
> defcnf = ("defcnf", 
>           "definitional cnf",
>           PP.putStrLn . pPrint . CNF.defcnf . parse . head)

> truthtable :: Command
> truthtable = ("truthtable", 
>               "show propositional truth table",
>               S.putStrLn . (\f -> Prop.truthtable f ++ "\n") . parse . head)

** Propositional solvers

> tautology :: Command
> tautology = ("tautology", 
>              "Tautology checker via truth tables",
>              runprop Prop.tautology)

> dp :: Command
> dp = ("dp",
>       "Davis-Putnam procedure (propositional)",
>       runprop DP.dptaut)

> dpll :: Command
> dpll = ("dpll",
>         "Davis-Putnam-Loveland-Logemann procedure (propositional)",
>         runprop DP.dplltaut)

> runprop :: Pretty a => (Formula -> a) -> Args -> IO ()
> runprop f args = 
>   let fm = case args of
>            [] -> error ("Can't read arguments: " ++ show args)
>            [n] -> case Forms.lookup n of
>                     Nothing -> error ("Can't find formula: " ++ n)
>                     Just f' -> f'
>            ("-":"f":fm':_) -> parse fm'
>            ("-":"prime":n:_) -> PropExamples.prime $ read n
>            ("-":"prime0":n:_) -> F.unIff $ PropExamples.prime $ read n
>            ("-":"ramsey":s:t:n:_) -> PropExamples.ramsey (read s) (read t) (read n) 
>            _ -> error "Impossible" 
>   in do PP.putStrLn $ pPrint fm
>         Lib.time $ let res = f fm in PP.putStrLn $ pPrint res

** Unification

> unify :: Command
> unify = ("unify", 
>          "unify two terms",
>          \(s1:s2:_) -> let tm1 :: Term = parse s1
>                            tm2 :: Term = parse s2 in
>                        unifyFun [(tm1,tm2)])

> unifyFun :: [(Term, Term)] -> IO ()
> unifyFun eqs = 
>   case Unif.unifyAndApply eqs of
>     Nothing -> S.putStrLn "Can't unify\n"
>     Just eqs' -> PP.putStrLn $ pPrint $ show eqs'

** First order formulas

> pnf :: Command
> pnf = ("pnf", 
>        "prenex normal form",
>        PP.putStrLn . pPrint . Skolem.pnf . parse . head)

> skolemize :: Command
> skolemize = ("skolemize", 
>        "skolem normal form",
>        PP.putStrLn . pPrint . Skolem.skolemize . parse . head)

** First order solvers

> runfol :: (Formula -> IO a) -> Args -> IO ()
> runfol f args = 
>   do fm <- case args of 
>              [] -> error "Can't read argument"
>              "-":"f":fm':_ -> return (parse fm')
>              n:_ -> case Forms.lookup n of
>                      Nothing -> error $ "Can't find formula: " ++ n
>                      Just ψ -> return ψ
>      fm' <- return (if elem "eq" args then Equal.equalitize fm else fm)
>      PP.putStrLn $ pPrint fm'
>      M.ignore $ Lib.time $ f fm'

> gilmore :: Command
> gilmore = ("gilmore",
>            "Gilmore procedure",
>            runfol Herbrand.gilmore)

> davisputnam :: Command
> davisputnam = ("davisputnam", 
>                "Davis-Putname procedure",
>                runfol Herbrand.davisputnam)

> prawitz :: Command
> prawitz = ("prawitz",
>            "Prawitz procedure",
>            runfol (PP.putStrLn . pPrint . Tableaux.prawitz))

> tab :: Command
> tab = ("tab",
>        "Analytic tableaux procedure",
>        runfol Tableaux.tab)

> splittab :: Command
> splittab = ("splittab",
>             "Analytic tableaux procedure",
>             runfol Tableaux.splittab)

> basicResolution :: Command
> basicResolution = ("basicResolution",
>                    "Basic resolution procedure",
>                    runfol Resolution.basicResolution)

> resolution :: Command
> resolution = ("resolution",
>                "Resolution with subsumption",
>                runfol Resolution.resolution)

> positiveResolution :: Command
> positiveResolution = ("positiveResolution",
>                "Postive resolution",
>                runfol Resolution.positiveResolution)

> sosResolution :: Command
> sosResolution = ("sosResolution",
>                  "Set-of-support resolution",
>                  runfol Resolution.sosResolution)

> paramodulation :: Command
> paramodulation = ("paramodulation",
>                  "Paramodulation",
>                  runfol Paramodulation.paramodulation)

> hornprove :: Command
> hornprove = ("hornprove",
>              "Basic horn clause prover using backchaining",
>              runfol Prolog.hornprove)

> prolog :: Command
> prolog = ("prolog",
>           "Prolog interpreter",
>          \(c:prog) -> case Prolog.prolog prog c of
>                         Nothing -> S.putStrLn "Unsolvable"
>                         Just eqs -> PP.putStrLn $ pPrint eqs)

> basicMeson :: Command
> basicMeson = ("basicMeson",
>               "Basic Meson procedure",
>               runfol Meson.basicMeson)

> meson :: Command
> meson = ("meson",
>          "Optimized Meson procedure",
>          runfol Meson.meson)

> bmeson :: Command
> bmeson = ("bmeson",
>           "Meson with equality elimination",
>          runfol EqElim.bmeson)

> ccvalid :: Command
> ccvalid = ("cc",
>            "Congruence closure validity",
>            runfol (PP.putStrLn . pPrint . Cong.ccvalid))

> rewrite :: Command
> rewrite = ("rewrite",
>            "Rewriting",
>           \(eq:eqs) -> let tm = Rewrite.rewrite (map parse eqs) (parse eq) in
>                        PP.putStrLn $ pPrint tm)

> aedecide :: Command
> aedecide = ("aedecide",
>             "Decide AE problems",
>             runfol (PP.putStrLn . pPrint . Decidable.aedecide))

> dlo :: Command
> dlo = ("dlo", "Dense Linear Orders",
>             runfol (PP.putStrLn . pPrint . Qelim.qelimDLO))

> pres :: Command
> pres = ("pres", "Presburger arithmetic",
>                  runfol (PP.putStrLn . pPrint . Cooper.integerQelim))

> nelopInt :: Command
> nelopInt = ("nelopInt",
>             "Nelson Oppen",
>             runfol (PP.putStrLn . pPrint . Combining.nelop (Combining.addDefault [Combining.intLang])))

* Options

> data Flag = -- Flags
>             Verbose Priority
>           | LogToTerm
>           | LogToFile
>   deriving (Eq, Show)

> instance Pretty Flag where
>   pPrint = PP.text . show

> options :: [OptDescr Flag]
> options =
>  [ Option ['v'] ["Verbose"] (OptArg verbose (show Log.defaultPrio)) 
>      "Verbosity level.  (debug | info | warn | error)"
>  , Option ['T'] ["LogToTerm"] (NoArg LogToTerm)
>      "Log to terminal on stdout."
>  , Option ['F'] ["LogToFile"] (NoArg LogToFile)
>      "Log to the log file."
>  ]

> parseOptions :: Args -> IO ([Flag], [String], [String])
> parseOptions argv = case Opt.getOpt' Opt.Permute options argv of
>   (o, n, u, []) -> return (o, n, u)
>   (_, _, _, errs) -> ioError $ userError $ concat errs ++ usage

> verbose :: Maybe String -> Flag
> verbose Nothing = Verbose Log.defaultPrio
> verbose (Just s) = case Log.readPrio s of 
>   Nothing -> error $ "No such setting for 'verbose': " ++ s
>   Just p -> Verbose p

> usage :: String
> usage = Opt.usageInfo usageMsg options 
>   where usageMsg = PP.render block
>         block = PP.vcat [ PP.text "Possible commands:"
>                         , PP.nest 3 (PP.vcat (map group groups))
>                         , PP.text "Flags:"
>                         ]
>         group (name, coms) = PP.text ("=== " ++ name ++ " ===") $+$ PP.space $+$
>                              PP.nest 3 (PP.vcat (map com coms)) $+$ PP.space
>         com (name, desc, _) = PP.text (name ++ spaces name ++ ": " ++ desc)
>         spaces name = concat (replicate (20 - length name) " ")
