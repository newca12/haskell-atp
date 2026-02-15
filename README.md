# Haskell ATP — Automated Theorem Proving

A Haskell port of the OCaml code from John Harrison's
[*Handbook of Practical Logic and Automated Reasoning*](http://www.cambridge.org/9780521899574).

Originally written by [Sean McLaughlin](https://github.com/seanmcl).
Updated to build with modern GHC (9.6.7) and Cabal (3.14).

## Implemented Algorithms

| Category | Commands |
|---|---|
| **Propositional** | `tautology`, `dp`, `dpll`, `stalmarck`, `bddtaut`, `nnf`, `cnf`, `dnf`, `defcnf` |
| **First-order** | `gilmore`, `davisputnam`, `prawitz`, `tab`, `splittab` |
| **Resolution** | `basicResolution`, `resolution`, `positiveResolution`, `sosResolution` |
| **Model elimination** | `basicMeson`, `meson`, `bmeson` |
| **Equality** | `ccvalid`, `paramod`, `rewrite` |
| **Arithmetic (Presburger)** | `cooper` |
| **Dense linear orders** | `dlo`, `dlovalid` |
| **Algebraic** | `complex`, `real`, `grobner` |
| **Combined theories** | `nelop`, `slowNelop`, `nelop-dlo` |
| **Other** | `skolem`, `pnf`, `hornprove`, `prolog`, `aedecide` |

## Prerequisites

Install GHC and Cabal via [GHCup](https://www.haskell.org/ghcup/):

```bash
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

Tested with **GHC 9.6.7** and **cabal-install 3.14**.

## Build

```bash
cabal update
cabal build all
```

## Install the `atp` executable

```bash
cabal install exe:atp
```

This installs the `atp` binary to `~/.cabal/bin/`.
Make sure `~/.cabal/bin` is on your `PATH`:

```bash
export PATH="$HOME/.cabal/bin:$PATH"
```

## Run Tests

```bash
cabal test --test-show-details=direct
```

Or using Make:

```bash
make test
```

## Usage

### Command-line

The `atp` binary takes a command name followed by arguments.
Formulas can be passed inline with `-f` or by referencing built-in test formula IDs.

```bash
# Check a propositional tautology
atp tautology -f "p ==> p"

# MESON procedure with equality elimination (first-order)
atp bmeson eq1

# Resolution on a first-order formula
atp resolution -f "(exists y. forall x. P(x, y)) ==> forall x. exists y. P(x, y)"

# Negation normal form
atp nnf -f "~(p /\ q ==> r)"

# Cooper's algorithm (Presburger arithmetic)
atp cooper -f "forall x. exists y. 2 * y = x \/ 2 * y = x + 1"

# Show a built-in test formula
atp show p1
```

Unicode syntax is also supported:

```
atp tautology -f "p ⊃ p"
atp resolution -f "(∃ y. ∀ x. P(x, y)) ⊃ (∀ x. ∃ y. P(x, y))"
```

### Interactive (GHCi REPL)

```bash
cabal repl lib:ATP
```

```haskell
ghci> :l src/Main.lhs
ghci> :main resolution -f "(exists y. forall x. P(x, y)) ==> forall x. exists y. P(x, y)"
Welcome to Haskell ATP!
(∃ y. ∀ x. P(x, y)) ⊃ (∀ x. ∃ y. P(x, y))
()
Computation time: 0.0013 sec
```

### Generate API documentation

```bash
cabal haddock
```

## Makefile Shortcuts

| Target | Description |
|---|---|
| `make build` | Build library + executable + tests |
| `make install` | Install the `atp` executable |
| `make test` | Run all tests |
| `make doc` | Generate Haddock documentation |
| `make repl` | Open GHCi with the ATP library |
| `make clean` | Clean build artifacts |

## Project Structure

```
src/
  Main.lhs                -- CLI entry point
  Compat.lhs              -- OCaml compatibility layer for interactive use
  ATP/
    Prop.lhs              -- Propositional logic
    Fol.lhs               -- First-order logic
    Formula.lhs           -- Core formula type
    FormulaSyn.lhs        -- Template Haskell quasi-quoters for formulas
    Dp.lhs                -- Davis-Putnam / DPLL
    Resolution.lhs        -- Resolution procedures
    Meson.lhs             -- Model elimination (MESON)
    Tableaux.lhs          -- Analytic tableaux
    Herbrand.lhs          -- Herbrand / Gilmore procedures
    Skolem.lhs            -- Skolemization & prenex normal forms
    Cooper.lhs            -- Presburger arithmetic (Cooper)
    Dlo.lhs               -- Dense linear orders
    Complex.lhs           -- Complex quantifier elimination
    Real.lhs              -- Real quantifier elimination
    Grobner.lhs           -- Gröbner basis procedures
    ...
    Test/                  -- HUnit & QuickCheck test suites
    Util/                  -- Utility libraries (parsing, printing, etc.)
test/
  Main.hs                  -- Test runner (cabal test)
```

## License

GPL-3.0 — see [LICENSE](LICENSE).
