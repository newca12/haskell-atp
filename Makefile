.PHONY: all build install test clean doc repl

all: build

build:
	cabal build all

install:
	cabal install exe:atp

test:
	cabal test --test-show-details=direct

clean:
	cabal clean
	rm -rf dist atp.prof atp.log
	find . \( -name "*~" -o -name "*.o" -o -name "*.hi" \) -delete

doc:
	cabal haddock

repl:
	cabal repl lib:ATP
