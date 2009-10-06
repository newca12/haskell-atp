
| OCaml compatibility

Here we bring the Haskell implementation into line with the OCaml
implementation by giving the original OCaml names to the Haskell
counterparts and exporting all functions.  For interactive play, the
user should be able to type the same commands, with the difference
that formulas are parsed as [$form| p ∧ q |] rather than <<p /\ q>>
and terms as [$term| x + y |] rather than <<| x + y |>>.  Since

Harrison does not always use unique names (e.g. dnf in prop.ml appears
twice), we assume the last occurrance of the name is the one the user
wants.  If not, she will need to redefine the old definition
interactively.

Usage: ghci Interact

* Pragmas

The monomorphism restriction prevents me from using simple names
when type classes are involved.  For interactive use, we really
don't care about performance, so forget about the restriction. 

> {-# LANGUAGE NoMonomorphismRestriction #-}

* Imports

> import Prelude hiding (print)
> import ATP.FormulaSyn
> import qualified ATP.Formula as F
> import qualified ATP.Prop as Prop
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Decidable as Decidable
> import qualified ATP.Qelim as Qelim
> import qualified ATP.DLO as DLO

* Compatibility functions

lib.ml

intro.ml

formulas.ml

prop.ml

> eval = Prop.eval
> atoms = Prop.atoms
> onallvaluations = Prop.onallvaluations
> print_truthtable = Prop.truthtable
> tautology = Prop.tautology
> unsatisfiable = Prop.unsatisfiable
> satisfiable = Prop.satisfiable
> dual = Prop.dual
> psimplify1 = Prop.simplify1
> psimplify = Prop.simplify
> negative = F.negative
> positive = F.positive
> negate = F.opp
> --nnf = Prop.nnf
> nenf = Prop.nenf
> purednf = Prop.purednf
> trivial = Prop.trivial
> simpdnf = Prop.simpdnf
> dnf = Prop.dnf
> purecnf = Prop.purecnf
> simpcnf = Prop.simpcnf
> cnf = Prop.cnf

propexamples.ml

defcnf.ml

dp.ml

stal.ml

bdd.ml

fol.ml

skolem.ml

> simplify = Skolem.simplify
> nnf = Skolem.nnf
> pnf = Skolem.pnf
> skolemize = Skolem.skolemize

herbrand.ml

unif.ml

tableaux.ml

resolution.ml

prolog.ml

meson.ml

skolems.ml

equal.ml

cong.ml

rewrite.ml

order.ml

completion.ml

eqelim.ml

paramodulation.ml

decidable.ml

> aedecide = Decidable.aedecide
> miniscope = Decidable.miniscope
> wang = Decidable.wang

qelim.ml

> qelim = Qelim.qelim
> lift_qelim = Qelim.lift
> cnnf = Qelim.cnnf
> lfn_dlo = DLO.lfn
> dlobasic = DLO.dloBasic
> afn_dlo = DLO.afn
> qelim_dlo = DLO.qelim

cooper.ml

complex.ml

real.ml

grobner.ml

geom.ml

interpolation.ml

combining.ml

lcf.ml

lcfprop.ml

folderived.ml

lcffol.ml

tactics.ml

limitations.ml

