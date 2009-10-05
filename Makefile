
default : dist

configure :
	runhaskell Setup.lhs configure --user

build : 
	runhaskell Setup.lhs build

install : 
	runhaskell Setup.lhs install

dist : configure build install 

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
	rm -rf doc

