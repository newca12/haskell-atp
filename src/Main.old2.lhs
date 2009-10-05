
-- > commands = []
-- >            , ("Propositional formulas",
-- >               [ 
-- >                 nnf
-- >               , cnf
-- >               , dnf
-- >               , defcnf
-- >               , truthtable ])
-- >            , ("Propositional decision procedures",
-- >               [ tautology
-- >               , dp
-- >               , dpll ])
-- >            , ("First order formulas",
-- >               [ showFol
-- >               , pnf
-- >               , skolemize ])
-- >            , ("Basic Herbrand methods",
-- >               [ gilmore
-- >               , davisputnam ])
-- >            , ("Unification",
-- >               [
-- >                 unify ])
-- >            , ("Tableaux",
-- >               [ prawitz
-- >               , tab
-- >               , splittab ])
-- >            , ("Resolution",
-- >               [ basicResolution
-- >               , resolution
-- >               , positiveResolution
-- >               , sosResolution ])
-- >            , ("Prolog",
-- >               [ hornprove
-- >               , prolog ])
-- >            , ("MESON",
-- >               [ basicMeson
-- >               , meson ])
-- >            , ("Equality",
-- >               [ ccvalid
-- >               , rewrite
-- >               , bmeson 
-- >               , paramodulation])
-- >            , ("Decidable problems",
-- >               [ aedecide
-- >               , dloQelim
-- >               , integerQelim
-- >               , nelopInt
-- >               ])
-- >            ]

-- > commands :: [Command]
-- > commands = concat (map snd groups)


A usage message when the user types 'help'

Something like the following:

  Possible commands:
     help: this message
     parseE: parse an arithmetic expression and print it
     parseP: parse a propositional formula and print it
     parseF: parse a first order formula and print it
     ...

-- > usage :: PP.Doc
-- > usage = PP.vcat [ PP.text "Possible commands:" 
-- >                 , PP.nest 3 $ PP.vcat $ map group groups ]
-- >   where group (name, coms) = PP.vcat [ PP.text $ "=== " ++ name ++ " ==="
-- >                                      , PP.nest 3 $ PP.vcat $ map com coms
-- >                                      ]
-- >         com (name, desc, _) = PP.text $ name ++ spaces name ++ ": " ++ desc
-- >         spaces name = concat $ replicate (20 - length name) " "

-- %%%%%%%%%%%%%%%%%%%%%%%%%
-- %%% Show test formulas

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%% Formula manipulation

-- > nnf :: Command
-- > nnf = ("nnf", 
-- >        "negation normal form",
-- >        output . Prop.nnf . Prop.parse . head)

-- > cnf :: Command
-- > cnf = ("cnf", 
-- >        "conjunctive normal form",
-- >        output . Prop.cnf . Prop.parse . head)

-- > dnf :: Command
-- > dnf = ("dnf", 
-- >        "disjunctive normal form",
-- >        output . Prop.dnf . Prop.parse . head)

-- > defcnf :: Command
-- > defcnf = ("defcnf", 
-- >           "definitional cnf",
-- >           output . DefCnf.defcnf . Prop.parse . head)

-- > truthtable :: Command
-- > truthtable = ("truthtable", 
-- >               "show propositional truth table",
-- >               printf . (\f -> Prop.truthtable f ++ "\n") . Prop.parse . head)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%% Propositional solvers

-- > tautology :: Command
-- > tautology = ("tautology", 
-- >              "Tautology checker via truth tables",
-- >              runprop Prop.tautology)

-- > dp :: Command
-- > dp = ("dp",
-- >       "Davis-Putnam procedure (propositional)",
-- >       runprop Dp.dptaut)

-- > dpll :: Command
-- > dpll = ("dpll",
-- >         "Davis-Putnam-Loveland-Logemann procedure (propositional)",
-- >         runprop Dp.dplltaut)

-- > propNth :: String -> IO (Formula Prop)
-- > propNth name = do forms <- TestFormulas.prop 
-- >                   case lookup name forms of
-- >                     Nothing -> error ("can't find prop formula: " ++ name)
-- >                     Just f -> return f

-- > runprop :: Show a => (Formula Prop -> a) -> Args -> IO ()
-- > runprop f args = 
-- >   do fm <- case args of
-- >            [] -> error ("Can't read arguments: " ++ show args)
-- >            [n] -> propNth n
-- >            ("-":"f":fm':_) -> return $ Prop.parse fm'
-- >            ("-":"prime":n:_) -> return $ PropExamples.prime $ read n
-- >            ("-":"prime0":n:_) -> return $ F.unIff $ PropExamples.prime $ read n
-- >            ("-":"ramsey":s:t:n:_) -> return $ PropExamples.ramsey (read s) (read t) (read n) 
-- >            _ -> error "Impossible" 
-- >      printf (show fm ++ "\n")     
-- >      Lib.time $ let res = f fm in printf $ show res ++ "\n"
-- >      return ()

-- %%%%%%%%%%%%%%%%%%
-- %%% Unification

-- > unify :: Command
-- > unify = ("unify", 
-- >          "unify two terms",
-- >          \(s1:s2:_) -> let tm1 = Fol.parseTerm s1
-- >                            tm2 = Fol.parseTerm s2 in
-- >                        unifyFun [(tm1,tm2)])

-- > unifyFun :: [(Term, Term)] -> IO ()
-- > unifyFun eqs = 
-- >   case Unif.unifyAndApply eqs of
-- >     Nothing -> printf "Can't unify\n"
-- >     Just eqs -> printf $ show eqs ++ "\n"

-- -- > unifyN :: Command
-- -- > unifyN = ("unifyN", 
-- -- >           "unify from library",
-- -- >          \(n:_) -> let eqs = unifyNth (read n) in
-- -- >                    do printf ("unifying: " ++ show eqs ++ "\n") 
-- -- >                       unifyFun eqs)

-- -- > unifyNth :: Int -> [(Term, Term)]
-- -- > unifyNth n = TestFormulas.unify !! n


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%% First order formulas

-- > pnf :: Command
-- > pnf = ("pnf", 
-- >        "prenex normal form",
-- >        output . Skolem.pnf . Fol.parse . head)

-- > skolemize :: Command
-- > skolemize = ("skolemize", 
-- >        "skolem normal form",
-- >        output . Skolem.skolemize . Fol.parse . head)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%% First order solvers

-- > folNth :: String -> IO (Formula Fol)
-- > folNth name = do forms <- TestFormulas.fol 
-- >                  case lookup name forms of
-- >                    Nothing -> error ("can't find fol formula: " ++ name)
-- >                    Just f -> return f

-- > runfol :: (Formula Fol -> IO a) -> Args -> IO ()
-- > runfol f args = 
-- >   do fm <- case args of 
-- >              [] -> error "Can't read argument"
-- >              "-":"f":fm':_ -> return (Fol.parse fm')
-- >              n:_ -> folNth n
-- >      fm' <- return (if elem "eq" args then Equal.equalitize fm else fm)
-- >      printf (show fm' ++ "\n") 
-- >      Lib.time $ f fm'
-- >      return ()

-- > gilmore :: Command
-- > gilmore = ("gilmore",
-- >            "Gilmore procedure",
-- >            runfol Herbrand.gilmore)

-- > davisputnam :: Command
-- > davisputnam = ("davisputnam", 
-- >                "Davis-Putname procedure",
-- >                runfol Herbrand.davisputnam)

-- > prawitz :: Command
-- > prawitz = ("prawitz",
-- >            "Prawitz procedure",
-- >            runfol (printf . show . Tableaux.prawitz))

-- > tab :: Command
-- > tab = ("tab",
-- >        "Analytic tableaux procedure",
-- >        runfol Tableaux.tab)

-- > splittab :: Command
-- > splittab = ("splittab",
-- >             "Analytic tableaux procedure",
-- >             runfol Tableaux.splittab)

-- > basicResolution :: Command
-- > basicResolution = ("basicResolution",
-- >                    "Basic resolution procedure",
-- >                    runfol Resolution.basicResolution)

-- > resolution :: Command
-- > resolution = ("resolution",
-- >                "Resolution with subsumption",
-- >                runfol Resolution.resolution)

-- > positiveResolution :: Command
-- > positiveResolution = ("positiveResolution",
-- >                "Postive resolution",
-- >                runfol Resolution.positiveResolution)

-- > sosResolution :: Command
-- > sosResolution = ("sosResolution",
-- >                  "Set-of-support resolution",
-- >                  runfol Resolution.sosResolution)

-- > paramodulation :: Command
-- > paramodulation = ("paramodulation",
-- >                  "Paramodulation",
-- >                  runfol Paramodulation.paramodulation)

-- > hornprove :: Command
-- > hornprove = ("hornprove",
-- >              "Basic horn clause prover using backchaining",
-- >              runfol Prolog.hornprove)

-- > prolog :: Command
-- > prolog = ("prolog",
-- >           "Prolog interpreter",
-- >          \(c:prog) -> case Prolog.prolog prog c of
-- >                         Nothing -> printf "Unsolvable\n"
-- >                         Just eqs -> printf $ show eqs ++ "\n")

-- > basicMeson :: Command
-- > basicMeson = ("basicMeson",
-- >               "Basic Meson procedure",
-- >               runfol Meson.basicMeson)

-- > meson :: Command
-- > meson = ("meson",
-- >          "Optimized Meson procedure",
-- >          runfol Meson.meson)

-- > bmeson :: Command
-- > bmeson = ("bmeson",
-- >           "Meson with equality elimination",
-- >          runfol EqElim.bmeson)

-- > ccvalid :: Command
-- > ccvalid = ("ccvalid",
-- >            "Congruence closure validity",
-- >            runfol (printf . Print.showLine . Cong.ccvalid))

-- > rewrite :: Command
-- > rewrite = ("rewrite",
-- >            "Rewriting",
-- >           \(eq:eqs) -> let tm = Rewrite.rewrite (map Fol.parse eqs) (Fol.parseTerm eq) in
-- >                        printf $ show tm ++ "\n")

-- > aedecide :: Command
-- > aedecide = ("aedecide",
-- >             "Decide AE problems",
-- >             runfol (output . Decidable.aedecide))

-- > dloQelim :: Command
-- > dloQelim = ("dloQelim",
-- >             "Dense Linear Orders",
-- >             runfol (output . Qelim.qelimDLO))

-- > integerQelim :: Command
-- > integerQelim = ("integerQelim",
-- >             "Presburger arithmetic",
-- >             runfol (output . Cooper.integerQelim))

-- > nelopInt :: Command
-- > nelopInt = ("nelopInt",
-- >             "Nelson Oppen",
-- >             runfol (output . Combining.nelop (Combining.addDefault [Combining.intLang])))
