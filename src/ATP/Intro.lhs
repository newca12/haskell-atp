
* Signature

> module ATP.Intro ( simplify ) where

* Imports

> import Prelude
> import ATP.IntroSyn

* Simplify

> simplify :: Expr -> Expr

> simplify [$expr| $e1 + $e2 |] = simplify1 [$expr| $e1' + $e2' |] 
>   where e1' = simplify e1
>         e2' = simplify e2
> simplify [$expr| $e1 * $e2 |] = simplify1 [$expr| $e1' * $e2' |]
>   where e1' = simplify e1
>         e2' = simplify e2
> simplify e = e

> simplify1 :: Expr -> Expr

> simplify1 [$expr| ^m + ^n |] = Const $ m + n
> simplify1 [$expr| ^m * ^n |] = Const $ m * n
> simplify1 [$expr| 0 + $x |] = x
> simplify1 [$expr| $x + 0 |] = x
> simplify1 [$expr| 0 * _ |] = [$expr| 0 |]
> simplify1 [$expr| _ * 0 |] = [$expr| 0 |]
> simplify1 [$expr| _ * 1 |] = [$expr| 1 |]
> simplify1 [$expr| 1 * _ |] = [$expr| 1 |]
> simplify1 x = x
