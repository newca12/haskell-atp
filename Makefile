
default : dist

configure : ATP.cabal ATP.cabal.lib
	runhaskell Setup.lhs configure --user --extra-include-dirs=src/ATP 

build : 
	runhaskell Setup.lhs build

install : 
	runhaskell Setup.lhs install

dist : configure build install 

sdist : configure
	cabal sdist

.PHONY : doc

doc : 
	runhaskell Setup.lhs haddock --executables \
	                             --hyperlink-source \
                                     --haddock-option="--use-unicode" \
                                     --haddock-option="-h" \
                                     --hoogle \
	                             --hscolour-css=util/hscolour.css \

clean :
	runhaskell Setup.lhs clean 
	rm -rf dist atp.prof atp.log
	find . \( -name "*~" -or -name "*.o" -or -name "*.hi" \) -exec rm -f {} \;

# ------------------------------------------------------------------------------
#  hlint                                                                        
# ------------------------------------------------------------------------------

# Having some trouble with hlint due to TH patterns, in particular in Geom.lhs

MODULES=ATP.Util.Debug ATP.Util.Impossible ATP.Util.Lex ATP.Util.Lib ATP.Util.List \
	ATP.Util.ListSet ATP.Util.Log ATP.Util.Log.Class ATP.Util.Misc ATP.Util.Monad \
	ATP.Util.Parse ATP.Util.Parse.Parse ATP.Util.Prelude ATP.Util.Print \
	ATP.Util.Print.Print ATP.Util.TH ATP.Util.Tuple ATP.Util.UnionFind ATP.Bdd \
	ATP.Combining ATP.Completion ATP.Complex ATP.Cong ATP.Cooper ATP.Decidable \
	ATP.DefCnf ATP.Dlo ATP.Dp ATP.EqElim ATP.Equal ATP.Fol ATP.Formula ATP.FormulaSyn \
	ATP.Qelim ATP.Real ATP.Resolution ATP.Rewrite ATP.Skolem ATP.Stal ATP.Tableaux \
	ATP.TestFormulas ATP.Unif ATP.Test.Combining ATP.Test.Complex ATP.Test.Cooper \
	ATP.Test.Dlo ATP.Test.Fo ATP.Test.Grobner ATP.Test.Real ATP.Test.Taut \
	ATP.Meson ATP.Order ATP.Paramodulation ATP.Poly ATP.Prolog ATP.Prop ATP.PropExamples \
	ATP.Grobner ATP.Herbrand ATP.Interpolation ATP.Intro ATP.MPoly ATP.IntroSyn \
        # ATP.Geom # hlint dies on ATP.Geom from TH patterns

hlint :
	hlint -h .hlint $(foreach module, $(MODULES), src/$(subst .,/,$(module)).lhs)
