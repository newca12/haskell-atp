# Implementation Notes

**Haskell port of John Harrison's "Handbook of Practical Logic and Automated Reasoning"**

By Sean McLaughlin

## Overview

This project is a Haskell port of the OCaml code accompanying Harrison's
logic textbook. The code is written in literate Haskell style, preserving the
original file names with Haskell naming conventions. Type classes are used
in places (e.g. polynomial manipulation via binary operators) to make the
code more idiomatic.

## Key Differences from the OCaml Original

### Formula Datatype

Harrison's original code uses a parameterized type:

```haskell
> data Formula a = Atom a
>                | Top
>                | Bot
>                | Not Formula
>                | And Formula Formula 
>                | Or Formula Formula 
>                | Imp Formula Formula
>                | Iff Formula Formula
>                | All Var Formula
>                | Ex Var Formula
```

instantiated with `Prop = P String` and `Fol = R String [Term]`.

This port unifies the two by dropping the type parameter and always using `Fol`:

```haskell
> data Formula = Atom Fol
>              | Top
>              | Bot
>              | Not Formula
>              | And Formula Formula 
>              | Or Formula Formula 
>              | Imp Formula Formula
>              | Iff Formula Formula
>              | All Var Formula
>              | Ex Var Formula
>   deriving(Eq, Ord, Data, Typeable)
```

Propositional atoms are represented as `R "p" []`. This simplifies type
annotations and removes the need for OCaml's polymorphic comparison hack
(`(<) : a -> a -> bool`), relying instead on derived `Eq` and `Ord` instances.

This choice has turned out to be a good one.  I wanted to be explicit
about types, and thus the type annotations are considerably simpler.
It also obviates the need for many type class annotations, since
Harrison relies upon Ocaml's ordering cheat: (<) : a -> a -> bool.
This is well known to be a bad idea, as it breaks type abstraction.
While in ML it is an understandable compromise between abstraction and
obviating the need to write comparison functions, it is not necessary
in Haskell.  We can simply derive Ord and Eq for new types.

### Style

A point-free style is preferred in places, but the correspondence with the
original is straightforward.

