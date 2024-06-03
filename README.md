# haskell-atp


## About ##
Port of the Objective Caml code supporting John Harrison's logic [textbook](http://www.cambridge.org/catalogue/catalogue.asp?isbn=9780521899574) Handbook of Practical Logic and Automated Reasoning to Haskell.

The original code written by [Sean McLaughlin](https://github.com/seanmcl) need GHC 6.10.4  
This repo contains sligth modifications and instructions to fit GHC upto 9.6.5

## Build and use the atp binary ##
1. Install GHC and cabal-install via [GHCup](https://www.haskell.org/ghcup) or via [stack](https://docs.haskellstack.org/en/stable) + `stack install cabal-install`
2.  Update your package database:

        cabal update
   
3. Get the required Haskell libraries:

       cabal install --lib directory hslogger utf8-string HUnit QuickCheck parsec syb

4. Build an executable

       cabal install

5. Make sure ~/.cabal/bin is on your path. The atp executable resides there.
6. Try it !
```
user@dev:$ atp bmeson eq1
Welcome to Haskell ATP!
(∀ x y z. x * y * z = (x * y) * z) ∧
(∀ x. 1 * x = x) ∧ (∀ x. i(x) * x = 1) ⊃
  (∀ x. x * i(x) = 1)
[19]
Computation time: 8.9304 sec
```

## You can also use ghci ##
```
cabal repl
ghci> :l src/Main.lhs
ghci> :main resolution -f "(exists y. forall x. P(x, y)) ==> forall x. exists y. P(x, y)"
Welcome to Haskell ATP!
(∃ y. ∀ x. P(x, y)) ⊃ (∀ x. ∃ y. P(x, y))
()
Computation time: 0.0013 sec
```
