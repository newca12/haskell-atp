
default : dist

configure : ATP.cabal ATP.cabal.lib
	runhaskell Setup.lhs configure --user --enable-library-profiling

build : 
	runhaskell Setup.lhs build

install : 
	runhaskell Setup.lhs install

dist : configure build install 

sdist : configure 
	cabal sdist

.PHONY : doc

doc : 
	runhaskell Setup.lhs haddock --hyperlink-source \
                                     --haddock-option="--use-unicode" \
                                     --haddock-option="-h" \
                                     --executables \
                                     --internal \
                                     --hoogle \
                                     --hyperlink-source \

clean :
	runhaskell Setup.lhs clean 
	rm -rf doc atp.prof atp.log
	find . \( -name "*~" -or -name "*.o" -or -name "*.hi" \) -exec rm -f {} \;
