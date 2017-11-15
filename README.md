# haskell-atp


### About ###
Port of the Objective Caml code supporting John Harrison's logic [textbook](http://www.cambridge.org/catalogue/catalogue.asp?isbn=9780521899574) Handbook of Practical Logic and Automated Reasoning to Haskell.

The original code written by [Sean McLaughlin](https://github.com/seanmcl) need GHC 6.10.4  
This repo contains sligth modifications and instructions to fit GHC 8.x


### Installlation ###
1. Install the [Haskell platform](http://hackage.haskell.org/platform/). This will give you [GHC](http://www.haskell.org/ghc/) and the [cabal-install](http://hackage.haskell.org/trac/hackage/wiki/CabalInstall) build tool.
2. [GNU Make](http://www.gnu.org/software/make/) is also required.
3.  Update your package database:

        cabal update
   
4. Get the required Haskell libraries:

       cabal install directory hslogger utf8-string

5. Build an executable

       make

6. Make sure ~/.cabal/bin is on your path.  The atp executable resides there.
7. Try it !
```
user@dev:$ atp bmeson eq1
Welcome to Haskell ATP!
(∀ x y z. x * y * z = (x * y) * z) ∧
(∀ x. 1 * x = x) ∧ (∀ x. i(x) * x = 1) ⊃
  (∀ x. x * i(x) = 1)
[19]
Computation time: 27.7014 sec
```

