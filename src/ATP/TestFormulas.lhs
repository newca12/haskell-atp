
Example formulas for testing the algorithms.

* Signature

> module ATP.TestFormulas
>   ( lookup
>   , lookupTerm )
> where

* Imports

> import ATP.Util.Prelude hiding (lookup)
> import ATP.FormulaSyn
> import qualified Data.List as List

* Terms

> lookupTerm :: String -> Maybe Term
> lookupTerm = flip List.lookup terms

> terms :: [(String, Term)]
> terms = 
>   [ 

>     ("lagrange_4", 
>      [term| (((x1^2) + (x2^2) + (x3^2) + (x4^2)) *
>            ((y1^2) + (y2^2) + (y3^2) + (y4^2))) -
>       ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4))^2)  +
>        (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3))^2)  +
>        (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2))^2)  +
>        (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1))^2)) |])

>   , ("lagrange_8",
>       [term|((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
>        (p2^2 + q2^2 + r2^2 + s2^2 + t2^2 + u2^2 + v2^2 + w2^2)) -
>        ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2)^2 +
>         (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2)^2 +
>         (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2)^2 +
>         (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2)^2 +
>         (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2)^2 +
>         (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2)^2 +
>         (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2)^2 +
>         (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2)^2)|])

>   , ("liouville",
>      [term| 6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
>       (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
>         (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
>        ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
>         (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4)) |])

>   , ("fleck", 
>      [term| 60 * (x1^2 + x2^2 + x3^2 + x4^2)^3 -
>       (((x1 + x2 + x3)^6 + (x1 + x2 - x3)^6 +
>         (x1 - x2 + x3)^6 + (x1 - x2 - x3)^6 +
>         (x1 + x2 + x4)^6 + (x1 + x2 - x4)^6 +
>         (x1 - x2 + x4)^6 + (x1 - x2 - x4)^6 +
>         (x1 + x3 + x4)^6 + (x1 + x3 - x4)^6 +
>         (x1 - x3 + x4)^6 + (x1 - x3 - x4)^6 +
>         (x2 + x3 + x4)^6 + (x2 + x3 - x4)^6 +
>         (x2 - x3 + x4)^6 + (x2 - x3 - x4)^6) +
>        2 * ((x1 + x2)^6 + (x1 - x2)^6 +
>             (x1 + x3)^6 + (x1 - x3)^6 +
>             (x1 + x4)^6 + (x1 - x4)^6 +
>             (x2 + x3)^6 + (x2 - x3)^6 +
>             (x2 + x4)^6 + (x2 - x4)^6 +
>             (x3 + x4)^6 + (x3 - x4)^6) +
>        36 * (x1^6 + x2^6 + x3^6 + x4^6)) |]
>     )

>   , ("hurwitz",
>      [term| 5040 * (x1^2 + x2^2 + x3^2 + x4^2)^4 -
>       (6 * ((x1 + x2 + x3 + x4)^8 +
>             (x1 + x2 + x3 - x4)^8 +
>             (x1 + x2 - x3 + x4)^8 +
>             (x1 + x2 - x3 - x4)^8 +
>             (x1 - x2 + x3 + x4)^8 +
>             (x1 - x2 + x3 - x4)^8 +
>             (x1 - x2 - x3 + x4)^8 +
>             (x1 - x2 - x3 - x4)^8) +
>        ((2 * x1 + x2 + x3)^8 +
>         (2 * x1 + x2 - x3)^8 +
>         (2 * x1 - x2 + x3)^8 +
>         (2 * x1 - x2 - x3)^8 +
>         (2 * x1 + x2 + x4)^8 +
>         (2 * x1 + x2 - x4)^8 +
>         (2 * x1 - x2 + x4)^8 +
>         (2 * x1 - x2 - x4)^8 +
>         (2 * x1 + x3 + x4)^8 +
>         (2 * x1 + x3 - x4)^8 +
>         (2 * x1 - x3 + x4)^8 +
>         (2 * x1 - x3 - x4)^8 +
>         (2 * x2 + x3 + x4)^8 +
>         (2 * x2 + x3 - x4)^8 +
>         (2 * x2 - x3 + x4)^8 +
>         (2 * x2 - x3 - x4)^8 +
>         (x1 + 2 * x2 + x3)^8 +
>         (x1 + 2 * x2 - x3)^8 +
>         (x1 - 2 * x2 + x3)^8 +
>         (x1 - 2 * x2 - x3)^8 +
>         (x1 + 2 * x2 + x4)^8 +
>         (x1 + 2 * x2 - x4)^8 +
>         (x1 - 2 * x2 + x4)^8 +
>         (x1 - 2 * x2 - x4)^8 +
>         (x1 + 2 * x3 + x4)^8 +
>         (x1 + 2 * x3 - x4)^8 +
>         (x1 - 2 * x3 + x4)^8 +
>         (x1 - 2 * x3 - x4)^8 +
>         (x2 + 2 * x3 + x4)^8 +
>         (x2 + 2 * x3 - x4)^8 +
>         (x2 - 2 * x3 + x4)^8 +
>         (x2 - 2 * x3 - x4)^8 +
>         (x1 + x2 + 2 * x3)^8 +
>         (x1 + x2 - 2 * x3)^8 +
>         (x1 - x2 + 2 * x3)^8 +
>         (x1 - x2 - 2 * x3)^8 +
>         (x1 + x2 + 2 * x4)^8 +
>         (x1 + x2 - 2 * x4)^8 +
>         (x1 - x2 + 2 * x4)^8 +
>         (x1 - x2 - 2 * x4)^8 +
>         (x1 + x3 + 2 * x4)^8 +
>         (x1 + x3 - 2 * x4)^8 +
>         (x1 - x3 + 2 * x4)^8 +
>         (x1 - x3 - 2 * x4)^8 +
>         (x2 + x3 + 2 * x4)^8 +
>         (x2 + x3 - 2 * x4)^8 +
>         (x2 - x3 + 2 * x4)^8 +
>         (x2 - x3 - 2 * x4)^8) +
>        60 * ((x1 + x2)^8 + (x1 - x2)^8 +
>              (x1 + x3)^8 + (x1 - x3)^8 +
>              (x1 + x4)^8 + (x1 - x4)^8 +
>              (x2 + x3)^8 + (x2 - x3)^8 +
>              (x2 + x4)^8 + (x2 - x4)^8 +
>              (x3 + x4)^8 + (x3 - x4)^8) +
>        6 * ((2 * x1)^8 + (2 * x2)^8 + (2 * x3)^8 + (2 * x4)^8)) |])

>   , ("schur", 
>      [term| 22680 * (x1^2 + x2^2 + x3^2 + x4^2)^5 -
>       (9 * ((2 * x1)^10 +
>             (2 * x2)^10 +
>             (2 * x3)^10 +
>             (2 * x4)^10) +
>        180 * ((x1 + x2)^10 + (x1 - x2)^10 +
>               (x1 + x3)^10 + (x1 - x3)^10 +
>               (x1 + x4)^10 + (x1 - x4)^10 +
>               (x2 + x3)^10 + (x2 - x3)^10 +
>               (x2 + x4)^10 + (x2 - x4)^10 +
>               (x3 + x4)^10 + (x3 - x4)^10) +
>        ((2 * x1 + x2 + x3)^10 +
>         (2 * x1 + x2 - x3)^10 +
>         (2 * x1 - x2 + x3)^10 +
>         (2 * x1 - x2 - x3)^10 +
>         (2 * x1 + x2 + x4)^10 +
>         (2 * x1 + x2 - x4)^10 +
>         (2 * x1 - x2 + x4)^10 +
>         (2 * x1 - x2 - x4)^10 +
>         (2 * x1 + x3 + x4)^10 +
>         (2 * x1 + x3 - x4)^10 +
>         (2 * x1 - x3 + x4)^10 +
>         (2 * x1 - x3 - x4)^10 +
>         (2 * x2 + x3 + x4)^10 +
>         (2 * x2 + x3 - x4)^10 +
>         (2 * x2 - x3 + x4)^10 +
>         (2 * x2 - x3 - x4)^10 +
>         (x1 + 2 * x2 + x3)^10 +
>         (x1 + 2 * x2 - x3)^10 +
>         (x1 - 2 * x2 + x3)^10 +
>         (x1 - 2 * x2 - x3)^10 +
>         (x1 + 2 * x2 + x4)^10 +
>         (x1 + 2 * x2 - x4)^10 +
>         (x1 - 2 * x2 + x4)^10 +
>         (x1 - 2 * x2 - x4)^10 +
>         (x1 + 2 * x3 + x4)^10 +
>         (x1 + 2 * x3 - x4)^10 +
>         (x1 - 2 * x3 + x4)^10 +
>         (x1 - 2 * x3 - x4)^10 +
>         (x2 + 2 * x3 + x4)^10 +
>         (x2 + 2 * x3 - x4)^10 +
>         (x2 - 2 * x3 + x4)^10 +
>         (x2 - 2 * x3 - x4)^10 +
>         (x1 + x2 + 2 * x3)^10 +
>         (x1 + x2 - 2 * x3)^10 +
>         (x1 - x2 + 2 * x3)^10 +
>         (x1 - x2 - 2 * x3)^10 +
>         (x1 + x2 + 2 * x4)^10 +
>         (x1 + x2 - 2 * x4)^10 +
>         (x1 - x2 + 2 * x4)^10 +
>         (x1 - x2 - 2 * x4)^10 +
>         (x1 + x3 + 2 * x4)^10 +
>         (x1 + x3 - 2 * x4)^10 +
>         (x1 - x3 + 2 * x4)^10 +
>         (x1 - x3 - 2 * x4)^10 +
>         (x2 + x3 + 2 * x4)^10 +
>         (x2 + x3 - 2 * x4)^10 +
>         (x2 - x3 + 2 * x4)^10 +
>         (x2 - x3 - 2 * x4)^10) +
>        9 * ((x1 + x2 + x3 + x4)^10 +
>             (x1 + x2 + x3 - x4)^10 +
>             (x1 + x2 - x3 + x4)^10 +
>             (x1 + x2 - x3 - x4)^10 +
>             (x1 - x2 + x3 + x4)^10 +
>             (x1 - x2 + x3 - x4)^10 +
>             (x1 - x2 - x3 + x4)^10 +
>             (x1 - x2 - x3 - x4)^10)) |] )

>    , ("Rajwade", 
>     [term| (x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 + x_6^2 + x_7^2 + x_8^2 + x_9^2) *
>    (y_1^2 + y_2^2 + y_3^2 + y_4^2 + y_5^2 + y_6^2 + y_7^2 + y_8^2 +
>     y_9^2 + y_10^2 + y_11^2 + y_12^2 + y_13^2 + y_14^2 + y_15^2 + y_16^2) -
>    ((0 + x_1 * y_1 + x_2 * y_2 + x_3 * y_3 + x_4 * y_4 + x_5 * y_5 + x_6 * y_6 + x_7 * y_7 + x_8 * y_8 + x_9 * y_9)^2 +
>     (0 - x_2 * y_1 + x_1 * y_2 + x_4 * y_3 - x_3 * y_4 + x_6 * y_5 - x_5 * y_6 - x_8 * y_7 + x_7 * y_8 + x_9 * y_10)^2 +
>     (0 - x_3 * y_1 - x_4 * y_2 + x_1 * y_3 + x_2 * y_4 + x_7 * y_5 + x_8 * y_6 - x_5 * y_7 - x_6 * y_8 + x_9 * y_11)^2 +
>     (0 - x_4 * y_1 + x_3 * y_2 - x_2 * y_3 + x_1 * y_4 + x_8 * y_5 - x_7 * y_6 + x_6 * y_7 - x_5 * y_8 + x_9 * y_12)^2 +
>     (0 - x_5 * y_1 - x_6 * y_2 - x_7 * y_3 - x_8 * y_4 + x_1 * y_5 + x_2 * y_6 + x_3 * y_7 + x_4 * y_8 + x_9 * y_13)^2 +
>     (0 - x_6 * y_1 + x_5 * y_2 - x_8 * y_3 + x_7 * y_4 - x_2 * y_5 + x_1 * y_6 - x_4 * y_7 + x_3 * y_8 + x_9 * y_14)^2 +
>     (0 - x_7 * y_1 + x_8 * y_2 + x_5 * y_3 - x_6 * y_4 - x_3 * y_5 + x_4 * y_6 + x_1 * y_7 - x_2 * y_8 + x_9 * y_15)^2 +
>     (0 - x_8 * y_1 - x_7 * y_2 + x_6 * y_3 + x_5 * y_4 - x_4 * y_5 - x_3 * y_6 + x_2 * y_7 + x_1 * y_8 + x_9 * y_16)^2 +
>     (0 - x_9 * y_1 + x_1 * y_9 - x_2 * y_10 - x_3 * y_11 - x_4 * y_12 - x_5 * y_13 - x_6 * y_14 - x_7 * y_15 - x_8 * y_16)^2 +
>     (0 - x_9 * y_2 + x_2 * y_9 + x_1 * y_10 - x_4 * y_11 + x_3 * y_12 - x_6 * y_13 + x_5 * y_14 + x_8 * y_15 - x_7 * y_16)^2 +
>     (0 - x_9 * y_3 + x_3 * y_9 + x_4 * y_10 + x_1 * y_11 - x_2 * y_12 - x_7 * y_13 - x_8 * y_14 + x_5 * y_15 + x_6 * y_16)^2 +
>     (0 - x_9 * y_4 + x_4 * y_9 - x_3 * y_10 + x_2 * y_11 + x_1 * y_12 - x_8 * y_13 + x_7 * y_14 - x_6 * y_15 + x_5 * y_16)^2 +
>     (0 - x_9 * y_5 + x_5 * y_9 + x_6 * y_10 + x_7 * y_11 + x_8 * y_12 + x_1 * y_13 - x_2 * y_14 - x_3 * y_15 - x_4 * y_16)^2 +
>     (0 - x_9 * y_6 + x_6 * y_9 - x_5 * y_10 + x_8 * y_11 - x_7 * y_12 + x_2 * y_13 + x_1 * y_14 + x_4 * y_15 - x_3 * y_16)^2 +
>     (0 - x_9 * y_7 + x_7 * y_9 - x_8 * y_10 - x_5 * y_11 + x_6 * y_12 + x_3 * y_13 - x_4 * y_14 + x_1 * y_15 + x_2 * y_16)^2 +
>     (0 - x_9 * y_8 + x_8 * y_9 + x_7 * y_10 - x_6 * y_11 - x_5 * y_12 + x_4 * y_13 + x_3 * y_14 - x_2 * y_15 + x_1 * y_16)^2) |])

>   ]

* Formulas

> lookup :: String -> Maybe Formula
> lookup = flip List.lookup formulas

> formulas :: [(String, Formula)]
> formulas = 
>   [ 

** Pellatier's problems

Propositional

>     ("p1", [form| p ⊃ q ⇔ ¬ q ⊃ ¬ p |])
>   , ("p2", [form| ¬ ¬ p ⇔ p |])
>   , ("p3", [form| ¬ (p ⊃ q) ⊃ q ⊃ p |])
>   , ("p4", [form| ¬ p ⊃ q ⇔ ¬ q ⊃ p |])
>   , ("p5", [form| (p ∨ q ⊃ p ∨ r) ⊃ p ∨ (q ⊃ r) |])
>   , ("p6", [form| p ∨ ¬ p |])
>   , ("p7", [form| p ∨ ¬ ¬ ¬ p |])
>   , ("p8", [form| ((p ⊃ q) ⊃ p) ⊃ p |])
>   , ("p9", [form| (p ∨ q) ∧ (¬ p ∨ q) ∧ (p ∨ ¬ q) ⊃ ¬ (¬ q ∨ ¬ q) |])
>   , ("p10", [form| (q ⊃ r) ∧ (r ⊃ p ∧ q) ∧ (p ⊃ q ∧ r) ⊃ (p ⇔ q) |])
>   , ("p11", [form| p ⇔ p |])
>   , ("p12", [form| ((p ⇔ q) ⇔ r) ⇔ (p ⇔ (q ⇔ r)) |])
>   , ("p13", [form| p ∨ q ∧ r ⇔ (p ∨ q) ∧ (p ∨ r) |])
>   , ("p14", [form| (p ⇔ q) ⇔ (q ∨ ¬ p) ∧ (¬ q ∨ p) |])
>   , ("p15", [form| p ⊃ q ⇔ ¬ p ∨ q |])
>   , ("p16", [form| (p ⊃ q) ∨ (q ⊃ p) |])
>   , ("p17", [form| p ∧ (q ⊃ r) ⊃ s ⇔ (¬ p ∨ q ∨ s) ∧ (¬ p ∨ ¬ r ∨ s) |])

First order

>   , ("p18", [form| ∃ y. ∀ x. P(y) ⊃ P(x) |])

>   , ("p19", [form| ∃ x. ∀ y z. (P(y) ⊃ Q(z)) ⊃ P(x) ⊃ Q(x) |])

>   , ("p20", [form| (∀ x y. ∃ z. ∀ w. P(x) ∧ Q(y) ⊃ R(z) ∧ U(w))
>                       ⊃ (∃ x y. P(x) ∧ Q(y)) ⊃ (∃ z. R(z)) |])

>   , ("p21", [form| (∃ x. P ⊃ Q(x)) ∧ (∃ x. Q(x) ⊃ P)
>                       ⊃ (∃ x. P ⇔ Q(x)) |])

>   , ("p22", [form| (∀ x. P ⇔ Q(x)) ⊃ (P ⇔ (∀ x. Q(x))) |])

>   , ("p23", [form| (∀ x. P ∨ Q(x)) ⇔ P ∨ (∀ x. Q(x)) |])

>   , ("p24", [form|  ¬ (∃ x. U(x) ∧ Q(x)) ∧
>                    (∀ x. P(x) ⊃ Q(x) ∨ R(x)) ∧       
>                  ¬ (∃ x. P(x) ⊃ (∃ x. Q(x))) ∧   
>                    (∀ x. Q(x) ∧ R(x) ⊃ U(x))         
>                  ⊃ (∃ x. P(x) ∧ R(x)) |]) 

>   , ("p25", [form| (∃ x. P(x)) ∧
>                  (∀ x. U(x) ⊃ ¬ G(x) ∧ R(x)) ∧ 
>                  (∀ x. P(x) ⊃ G(x) ∧ U(x)) ∧ 
>                  ((∀ x. P(x) ⊃ Q(x)) ∨ (∃ x. Q(x) ∧ P(x))) 
>                  ⊃ (∃ x. Q(x) ∧ P(x)) |]) 

>   , ("p26", [form| ((∃ x. P(x)) ⇔ (∃ x. Q(x))) ∧
>                   (∀ x y. P(x) ∧ Q(y) ⊃ (R(x) ⇔ U(y))) 
>                   ⊃ ((∀ x. P(x) ⊃ R(x)) ⇔ (∀ x. Q(x) ⊃ U(x))) |])

>   , ("p27", [form| (∃ x. P(x) ∧ ¬ Q(x)) ∧
>                   (∀ x. P(x) ⊃ R(x)) ∧ 
>                   (∀ x. U(x) ∧ V(x) ⊃ P(x)) ∧ 
>                   (∃ x. R(x) ∧ ¬ Q(x)) 
>                   ⊃ (∀ x. U(x) ⊃ ¬ R(x)) 
>                   ⊃ (∀ x. U(x) ⊃ ¬ V(x)) |])

>   , ("p28", [form| (∀ x. P(x) ⊃ (∀ x. Q(x))) ∧
>                   ((∀ x. Q(x) ∨ R(x)) ⊃ (∃ x. Q(x) ∧ R(x))) ∧ 
>                   ((∃ x. R(x)) ⊃ (∀ x. L(x) ⊃ M(x))) ⊃ 
>                   (∀ x. P(x) ∧ L(x) ⊃ M(x)) |])

>   , ("p29", [form| (∃ x. P(x)) ∧ (∃ x. G(x)) ⊃
>                   ((∀ x. P(x) ⊃ H(x)) ∧ (∀ x. G(x) ⊃ J(x)) ⇔ 
>                   (∀ x y. P(x) ∧ G(y) ⊃ H(x) ∧ J(y))) |])

>   , ("p30", [form| (∀ x. P(x) ∨ G(x) ⊃ ¬ H(x)) ∧
>                   (∀ x. (G(x) ⊃ ¬ U(x)) ⊃ P(x) ∧ H(x)) 
>                   ⊃ (∀ x. U(x)) |])

>   , ("p31", [form| ¬ (∃ x. P(x) ∧ (G(x) ∨ H(x))) ∧
>                   (∃ x. Q(x) ∧ P(x)) ∧ 
>                   (∀ x. ¬ H(x) ⊃ J(x)) 
>                   ⊃ (∃ x. Q(x) ∧ J(x)) |])

>   , ("p32", [form| (∀ x. P(x) ∧ (G(x) ∨ H(x)) ⊃ Q(x)) ∧
>                   (∀ x. Q(x) ∧ H(x) ⊃ J(x)) ∧ 
>                   (∀ x. R(x) ⊃ H(x)) 
>                   ⊃ (∀ x. P(x) ∧ R(x) ⊃ J(x)) |])

>   , ("p33", [form| (∀ x. P(a) ∧ (P(x) ⊃ P(b)) ⊃ P(c)) ⇔
>                   (∀ x. P(a) ⊃ P(x) ∨ P(c)) ∧ (P(a) ⊃ P(b) ⊃ P(c)) |])

>   , ("p34", [form| ((∃ x. ∀ y. P(x) ⇔ P(y)) ⇔
>                      ((∃ x. Q(x)) ⇔ (∀ y. Q(y)))) ⇔ 
>                   ((∃ x. ∀ y. Q(x) ⇔ Q(y)) ⇔ 
>                   ((∃ x. P(x)) ⇔ (∀ y. P(y)))) |])

>   , ("p35", [form| ∃ x y. P(x,y) ⊃ (∀ x y. P(x,y)) |])

>   , ("p36", [form| (∀ x. ∃ y. P(x,y)) ∧
>                   (∀ x. ∃ y. G(x,y)) ∧ 
>                   (∀ x y. P(x,y) ∨ G(x,y) 
>                   ⊃ (∀ z. P(y,z) ∨ G(y,z) ⊃ H(x,z))) 
>                   ⊃ (∀ x. ∃ y. H(x,y)) |])

>   , ("p37", [form| (∀ z.
>                   ∃ w. ∀ x. ∃ y. (P(x,z) ⊃ P(y,w)) ∧ P(y,z) ∧ 
>                   (P(y,w) ⊃ (∃ u. Q(u,w)))) ∧ 
>                   (∀ x z. ¬ P(x,z) ⊃ (∃ y. Q(y,z))) ∧ 
>                   ((∃ x y. Q(x,y)) ⊃ (∀ x. R(x,x))) ⊃ 
>                   (∀ x. ∃ y. R(x,y)) |])

>   , ("p38", [form| (∀ x.
>                     P(a) ∧ (P(x) ⊃ (∃ y. P(y) ∧ R(x,y))) ⊃ 
>                   (∃ z w. P(z) ∧ R(x,w) ∧ R(w,z))) ⇔ 
>                   (∀ x. 
>                   (¬ P(a) ∨ P(x) ∨ (∃ z w. P(z) ∧ R(x,w) ∧ R(w,z))) ∧ 
>                     (¬ P(a) ∨ ¬ (∃ y. P(y) ∧ R(x,y)) ∨ 
>                   (∃ z w. P(z) ∧ R(x,w) ∧ R(w,z)))) |])

>   , ("p39", [form| ¬ (∃ x. ∀ y. P(y,x) ⇔ ¬ P(y,y)) |])

>   , ("p40", [form| (∃ y. ∀ x. P(x,y) ⇔ P(x,x))
>                   ⊃ ¬ (∀ x. ∃ y. ∀ z. P(z,y) ⇔ ¬ P(z,x)) |])

>   , ("p41", [form| (∀ z. ∃ y. ∀ x. P(x,y) ⇔ P(x,z) ∧ ¬ P(x,x))
>                   ⊃ ¬ (∃ z. ∀ x. P(x,z)) |])

>   , ("p42", [form| ¬ (∃ y. ∀ x. P(x,y) ⇔ ¬ (∃ z. P(x,z) ∧ P(z,x))) |])

>   , ("p43", [form| (∀ x y. Q(x,y) ⇔ ∀ z. P(z,x) ⇔ P(z,y))
>                     ⊃ ∀ x y. Q(x,y) ⇔ Q(y,x) |])

>   , ("p44", [form| (∀ x. P(x) ⊃ (∃ y. G(y) ∧ H(x,y)) ∧
>                   (∃ y. G(y) ∧ ¬ H(x,y))) ∧ 
>                   (∃ x. J(x) ∧ (∀ y. G(y) ⊃ H(x,y))) 
>                   ⊃ (∃ x. J(x) ∧ ¬ P(x)) |])

>   , ("p45", [form|  (∀ x. P(x) ∧ (∀ y. G(y) ∧ H(x,y) ⊃ J(x,y))
>                       ⊃ (∀ y. G(y) ∧ H(x,y) ⊃ R(y))) ∧           
>                    ¬ (∃ y. L(y) ∧ R(y)) ∧                             
>                       (∃ x. P(x) ∧ (∀ y. H(x,y) ⊃ L(y)) ∧     
>                     (∀ y. G(y) ∧ H(x,y) ⊃ J(x,y)))                  
>                     ⊃ (∃ x. P(x) ∧ ¬ (∃ y. G(y) ∧ H(x,y))) |])

>   , ("p46", [form| (∀ x. P(x) ∧ (∀ y. P(y) ∧ H(y,x) ⊃ G(y)) ⊃ G(x)) ∧
>                   ((∃ x. P(x) ∧ ¬ G(x)) ⊃ 
>                   (∃ x. P(x) ∧ ¬ G(x) ∧ 
>                   (∀ y. P(y) ∧ ¬ G(y) ⊃ J(x,y)))) ∧ 
>                   (∀ x y. P(x) ∧ P(y) ∧ H(x,y) ⊃ ¬ J(y,x)) ⊃ 
>                   (∀ x. P(x) ⊃ G(x)) |])

>   , ("p55", [form| lives(agatha) ∧ lives(butler) ∧ lives(charles) ∧
>                   (killed(agatha,agatha) ∨ killed(butler,agatha) ∨ 
>                   killed(charles,agatha)) ∧ 
>                   (∀ x y. killed(x,y) ⊃ hates(x,y) ∧ ¬ richer(x,y)) ∧ 
>                   (∀ x. hates(agatha,x) ⊃ ¬ hates(charles,x)) ∧ 
>                   (hates(agatha,agatha) ∧ hates(agatha,charles)) ∧ 
>                   (∀ x. lives(x) ∧ ¬ richer(x,agatha) ⊃ hates(butler,x)) ∧ 
>                   (∀ x. hates(agatha,x) ⊃ hates(butler,x)) ∧ 
>                   (∀ x. ¬ hates(x,agatha) ∨ ¬ hates(x,butler) ∨ ¬ hates(x,charles)) 
>                   ⊃ killed(agatha,agatha) ∧ 
>                   ¬ killed(butler,agatha) ∧ 
>                   ¬ killed(charles,agatha) |])

>   , ("p57", [form| P(f((a),b),f(b,c)) ∧
>                   P(f(b,c),f(a,c)) ∧ 
>                   (∀ x y z. P(x,y) ∧ P(y,z) ⊃ P(x,z)) 
>                   ⊃ P(f(a,b),f(a,c)) |])
>   , ("p58", [form| ∀ P Q R. ∀ x. ∃ v. ∃ w. ∀ y. ∀ z. 
>                   ((P(x) ∧ Q(y)) ⊃ ((P(v) ∨ R(w))  ∧ (R(z) ⊃ Q(v)))) |])
>   , ("p59", [form| (∀ x. P(x) ⇔ ¬ P(f(x))) ⊃ (∃ x. P(x) ∧ ¬ P(f(x))) |])
>   , ("p60", [form| ∀ x. P(x,f(x)) ⇔
>                         ∃ y. (∀ z. P(z,y) ⊃ P(z,f(x))) ∧ P(x,y) |])

Gilmore

>   , ("gilmore_1", [form| ∃ x. ∀ y z.
>                          ((F(y) ⊃ G(y)) ⇔ F(x)) ∧ 
>                          ((F(y) ⊃ H(y)) ⇔ G(x)) ∧ 
>                          (((F(y) ⊃ G(y)) ⊃ H(y)) ⇔ H(x)) 
>                         ⊃ F(z) ∧ G(z) ∧ H(z) |])

>   , ("gilmore_2", [form| ∃ x y. ∀ z.
>                        (F(x,z) ⇔ F(z,y)) ∧ (F(z,y) ⇔ F(z,z)) ∧ (F(x,y) ⇔ F(y,x)) 
>                        ⊃ (F(x,y) ⇔ F(x,z)) |])

>   , ("gilmore_3", [form| ∃ x. ∀ y z.
>                         ((F(y,z) ⊃ (G(y) ⊃ H(x))) ⊃ F(x,x)) ∧ 
>                         ((F(z,x) ⊃ G(x)) ⊃ H(z)) ∧ 
>                         F(x,y) 
>                         ⊃ F(z,z) |])

>   , ("gilmore_4", [form| ∃ x y. ∀ z.
>                         (F(x,y) ⊃ F(y,z) ∧ F(z,z)) ∧ 
>                         (F(x,y) ∧ G(x,y) ⊃ G(x,z) ∧ G(z,z)) |])

>   , ("gilmore_5", [form| (∀ x. ∃ y. F(x,y) ∨ F(y,x)) ∧
>                           (∀ x y. F(y,x) ⊃ F(y,y)) 
>                         ⊃ ∃ z. F(z,z) |])

>   , ("gilmore_6", [form| ∀ x. ∃ y.
>                         (∃ u. ∀ v. F(u,x) ⊃ G(v,u) ∧ G(u,x)) 
>                         ⊃ (∃ u. ∀ v. F(u,y) ⊃ G(v,u) ∧ G(u,y)) ∨ 
>                         (∀ u v. ∃ w. G(v,u) ∨ H(w,y,u) ⊃ G(u,w)) |])

>   , ("gilmore_7", [form| (∀ x. K(x) ⊃ ∃ y. L(y) ∧ (F(x,y) ⊃ G(x,y))) ∧
>                         (∃ z. K(z) ∧ ∀ u. L(u) ⊃ F(z,u)) 
>                         ⊃ ∃ v w. K(v) ∧ L(w) ∧ G(v,w) |])

>   , ("gilmore_8", [form| ∃ x. ∀ y z.
>                         ((F(y,z) ⊃ (G(y) ⊃ (∀ u. ∃ v. H(u,v,x)))) ⊃ F(x,x)) ∧ 
>                         ((F(z,x) ⊃ G(x)) ⊃ (∀ u. ∃ v. H(u,v,z))) ∧ 
>                         F(x,y) 
>                         ⊃ F(z,z) |])

>   , ("gilmore_9", [form| ∀ x. ∃ y. ∀ z.
>                         ((∀ u. ∃ v. F(y,u,v) ∧ G(y,u) ∧ ¬ H(y,x)) 
>                         ⊃ (∀ u. ∃ v. F(x,u,v) ∧ G(z,u) ∧ ¬ H(x,z)) 
>                         ⊃ (∀ u. ∃ v. F(x,u,v) ∧ G(y,u) ∧ ¬ H(x,y))) ∧ 
>                         ((∀ u. ∃ v. F(x,u,v) ∧ G(y,u) ∧ ¬ H(x,y)) 
>                         ⊃ ¬ (∀ u. ∃ v. F(x,u,v) ∧ G(z,u) ∧ ¬ H(x,z)) 
>                         ⊃ (∀ u. ∃ v. F(y,u,v) ∧ G(y,u) ∧ ¬ H(y,x)) ∧ 
>                         (∀ u. ∃ v. F(z,u,v) ∧ G(y,u) ∧ ¬ H(z,y))) |])

Misc

>   , ("davis_putnam_example", [form| ∃ x. ∃ y. ∀ z.
>                                    (F(x,y) ⊃ (F(y,z) ∧ F(z,z))) ∧ 
>                                    ((F(x,y) ∧ G(x,y)) ⊃ (G(x,z) ∧ G(z,z))) |])

>   , ("los", [form| (∀ x y z. P(x,y) ∧ P(y,z) ⊃ P(x,z)) ∧
>                   (∀ x y z. Q(x,y) ∧ Q(y,z) ⊃ Q(x,z)) ∧ 
>                   (∀ x y. Q(x,y) ⊃ Q(y,x)) ∧ 
>                   (∀ x y. P(x,y) ∨ Q(x,y)) 
>                   ⊃ (∀ x y. P(x,y)) ∨ (∀ x y. Q(x,y)) |])

>   , ("steamroller", [form| ((∀ x. P1(x) ⊃ P0(x)) ∧ (∃ x. P1(x))) ∧
>                          ((∀ x. P2(x) ⊃ P0(x)) ∧ (∃ x. P2(x))) ∧ 
>                          ((∀ x. P3(x) ⊃ P0(x)) ∧ (∃ x. P3(x))) ∧ 
>                          ((∀ x. P4(x) ⊃ P0(x)) ∧ (∃ x. P4(x))) ∧ 
>                          ((∀ x. P5(x) ⊃ P0(x)) ∧ (∃ x. P5(x))) ∧ 
>                          ((∃ x. Q1(x)) ∧ (∀ x. Q1(x) ⊃ Q0(x))) ∧ 
>                          (∀ x. P0(x) 
>                              ⊃ (∀ y. Q0(y) ⊃ R(x,y)) ∨ 
>                                   ((∀ y. P0(y) ∧ S0(y,x) ∧ 
>                                       (∃ z. Q0(z) ∧ R(y,z)) 
>                                          ⊃ R(x,y)))) ∧ 
>                          (∀ x y. P3(y) ∧ (P5(x) ∨ P4(x)) ⊃ S0(x,y)) ∧ 
>                          (∀ x y. P3(x) ∧ P2(y) ⊃ S0(x,y)) ∧ 
>                          (∀ x y. P2(x) ∧ P1(y) ⊃ S0(x,y)) ∧ 
>                          (∀ x y. P1(x) ∧ (P2(y) ∨ Q1(y)) ⊃ ¬ (R(x,y))) ∧ 
>                          (∀ x y. P3(x) ∧ P4(y) ⊃ R(x,y)) ∧ 
>                          (∀ x y. P3(x) ∧ P5(y) ⊃ ¬ (R(x,y))) ∧ 
>                          (∀ x. (P4(x) ∨ P5(x)) ⊃ ∃ y. Q0(y) ∧ R(x,y)) 
>                          ⊃ ∃ x y. P0(x) ∧ P0(y) ∧ 
>                                  ∃ z. Q1(z) ∧ R(y,z) ∧ R(x,y) |])

>   , ("wishnu", [form| (∃ x. x = f(g(x)) ∧ ∀ x'. x' = f(g(x')) ⊃ x = x') ⇔
>            (∃ y. y = g(f(y)) ∧ ∀ y'. y' = g(f(y')) ⊃ y = y') |])

>   , ("eq1", [form| (∀ x y z. x * (y * z) = (x * y) * z) ∧
>                   (∀ x. 1 * x = x) ∧ 
>                   (∀ x. i(x) * x = 1) 
>                   ⊃ ∀ x. x * i(x) = 1 |])

>   , ("eq2", [form| (∀ x y z. x * (y * z) = (x * y) * z) ∧
>                   (∀ x. 1 * x = x) ∧ 
>                   (∀ x. x * 1 = x) ∧ 
>                   (∀ x. x * x = 1) 
>                   ⊃ ∀ x y. x * y  = y * x |])


>   , ("eq3", [form| (∀ x. x = x) ∧
>                   (∀ x y z. x * (y * z) = (x * y) * z) ∧ 
>                   (∀ x y z. (x * y) * z = x * (y * z)) ∧ 
>                   (∀ x. 1 * x = x) ∧ 
>                   (∀ x. x = 1 * x) ∧ 
>                   (∀ x. i(x) * x = 1) ∧ 
>                   (∀ x. 1 = i(x) * x) ∧ 
>                   (∀ x y. x = y ⊃ i(x) = i(y)) ∧ 
>                   (∀ x y z. x = y ⊃ x * z = y * z) ∧ 
>                   (∀ x y z. x = y ⊃ z * x = z * y) ∧ 
>                   (∀ x y z. x = y ∧ y = z ⊃ x = z)
>                   ⊃ ∀ x. x * i(x) = 1 |])


>   , ("eq4", [form| (∀ x y z. axiom(x * (y * z),(x * y) * z)) ∧
>                   (∀ x y z. axiom((x * y) * z,x * (y * z)) ∧ 
>                   (∀ x. axiom(1 * x,x)) ∧ 
>                   (∀ x. axiom(x,1 * x)) ∧ 
>                   (∀ x. axiom(i(x) * x,1)) ∧ 
>                   (∀ x. axiom(1,i(x) * x)) ∧ 
>                   (∀ x x'. x = x' ⊃ cchain(i(x),i(x'))) ∧ 
>                   (∀ x x' y y'. x = x' ∧ y = y' ⊃ cchain(x * y,x' * y'))) ∧ 
>                   (∀ s t. axiom(s,t) ⊃ achain(s,t)) ∧ 
>                   (∀ s t u. axiom(s,t) ∧ (t = u) ⊃ achain(s,u)) ∧ 
>                   (∀ x x' u. x = x' ∧ achain(i(x'),u) ⊃ cchain(i(x),u)) ∧ 
>                   (∀ x x' y y' u. 
>                   x = x' ∧ y = y' ∧ achain(x' * y',u) ⊃ cchain(x * y,u)) ∧ 
>                   (∀ s t. cchain(s,t) ⊃ s = t) ∧ 
>                   (∀ s t. achain(s,t) ⊃ s = t) ∧ 
>                   (∀ t. t = t) 
>                   ⊃ ∀ x. x * i(x) = 1 |])

>   , ("eq5", [form| (∀ x y z. axiom(x * (y * z),(x * y) * z)) ∧
>                   (∀ x y z. axiom((x * y) * z,x * (y * z)) ∧ 
>                   (∀ x. axiom(1 * x,x)) ∧ 
>                   (∀ x. axiom(x,1 * x)) ∧ 
>                   (∀ x. axiom(i(x) * x,1)) ∧ 
>                   (∀ x. axiom(1,i(x) * x)) ∧ 
>                   (∀ x x'. x = x' ⊃ cong(i(x),i(x'))) ∧ 
>                   (∀ x x' y y'. x = x' ∧ y = y' ⊃ cong(x * y,x' * y'))) ∧ 
>                   (∀ s t. axiom(s,t) ⊃ achain(s,t)) ∧ 
>                   (∀ s t. cong(s,t) ⊃ cchain(s,t)) ∧ 
>                   (∀ s t u. axiom(s,t) ∧ (t = u) ⊃ achain(s,u)) ∧ 
>                   (∀ s t u. cong(s,t) ∧ achain(t,u) ⊃ cchain(s,u)) ∧ 
>                   (∀ s t. cchain(s,t) ⊃ s = t) ∧ 
>                   (∀ s t. achain(s,t) ⊃ s = t) ∧ 
>                   (∀ t. t = t) 
>                   ⊃ ∀ x. x * i(x) = 1 |]) 

>   , ("eq6", [form| axiom(f(f(f(f(f(c))))),c) ∧
>                   axiom(c,f(f(f(f(f(c)))))) ∧ 
>                   axiom(f(f(f(c))),c) ∧ 
>                   axiom(c,f(f(f(c)))) ∧ 
>                   (∀ s t. axiom(s,t) ⊃ achain(s,t)) ∧ 
>                   (∀ s t. cong(s,t) ⊃ cchain(s,t)) ∧ 
>                   (∀ s t u. axiom(s,t) ∧ (t = u) ⊃ achain(s,u)) ∧ 
>                   (∀ s t u. cong(s,t) ∧ achain(t,u) ⊃ cchain(s,u)) ∧ 
>                   (∀ s t. cchain(s,t) ⊃ s = t) ∧ 
>                   (∀ s t. achain(s,t) ⊃ s = t) ∧ 
>                   (∀ t. t = t) ∧ 
>                   (∀ x y. x = y ⊃ cong(f(x),f(y))) 
>                   ⊃ f(c) = c |])

>   , ("eq7", [form| (∀ x y z. eqA (x * (y * z),(x * y) * z)) ∧
>                   (∀ x y z. eqA ((x * y) * z)) ∧ 
>                   (∀ x. eqA (1 * x,x)) ∧ 
>                   (∀ x. eqA (x,1 * x)) ∧ 
>                   (∀ x. eqA (i(x) * x,1)) ∧ 
>                   (∀ x. eqA (1,i(x) * x)) ∧ 
>                   (∀ x. eqA (x,x)) ∧ 
>                   (∀ x y. eqA (x,y) ⊃ eqC (i(x),i(y))) ∧ 
>                   (∀ x y. eqC (x,y) ⊃ eqC (i(x),i(y))) ∧ 
>                   (∀ x y. eqT (x,y) ⊃ eqC (i(x),i(y))) ∧ 
>                   (∀ w x y z. eqA (w,x) ∧ eqA (y,z) ⊃ eqC (w * y,x * z)) ∧ 
>                   (∀ w x y z. eqA (w,x) ∧ eqC (y,z) ⊃ eqC (w * y,x * z)) ∧ 
>                   (∀ w x y z. eqA (w,x) ∧ eqT (y,z) ⊃ eqC (w * y,x * z)) ∧ 
>                   (∀ w x y z. eqC (w,x) ∧ eqA (y,z) ⊃ eqC (w * y,x * z)) ∧ 
>                   (∀ w x y z. eqC (w,x) ∧ eqC (y,z) ⊃ eqC (w * y,x * z)) ∧ 
>                   (∀ w x y z. eqC (w,x) ∧ eqT (y,z) ⊃ eqC (w * y,x * z)) ∧ 
>                   (∀ w x y z. eqT (w,x) ∧ eqA (y,z) ⊃ eqC (w * y,x * z)) ∧ 
>                   (∀ w x y z. eqT (w,x) ∧ eqC (y,z) ⊃ eqC (w * y,x * z)) ∧ 
>                   (∀ w x y z. eqT (w,x) ∧ eqT (y,z) ⊃ eqC (w * y,x * z)) ∧ 
>                   (∀ x y z. eqA (x,y) ∧ eqA (y,z) ⊃ eqT (x,z)) ∧ 
>                   (∀ x y z. eqC (x,y) ∧ eqA (y,z) ⊃ eqT (x,z)) ∧ 
>                   (∀ x y z. eqA (x,y) ∧ eqC (y,z) ⊃ eqT (x,z)) ∧ 
>                   (∀ x y z. eqA (x,y) ∧ eqT (y,z) ⊃ eqT (x,z)) ∧ 
>                   (∀ x y z. eqC (x,y) ∧ eqT (y,z) ⊃ eqT (x,z)) 
>                   ⊃ ∀ x. eqT (x * i(x),1) |]) 

>   , ("eq8", [form| (∀ x y z. eqA (x * (y * z),(x * y) * z)) ∧ 
>                  (∀ x y z. eqA ((x * y) * z)) ∧ 
>                  (∀ x. eqA (1 * x,x)) ∧ 
>                  (∀ x. eqA (x,1 * x)) ∧ 
>                  (∀ x. eqA (i(x) * x,1)) ∧ 
>                  (∀ x. eqA (1,i(x) * x)) ∧ 
>                  (∀ x y. eqA (x,y) ⊃ eqC (i(x),i(y))) ∧ 
>                  (∀ x y. eqC (x,y) ⊃ eqC (i(x),i(y))) ∧ 
>                  (∀ w x y. eqA (w,x) ⊃ eqC (w * y,x * y)) ∧ 
>                  (∀ w x y. eqC (w,x) ⊃ eqC (w * y,x * y)) ∧ 
>                  (∀ x y z. eqA (y,z) ⊃ eqC (x * y,x * z)) ∧ 
>                  (∀ x y z. eqC (y,z) ⊃ eqC (x * y,x * z)) ∧ 
>                  (∀ x y z. eqA (x,y) ∧ eqA (y,z) ⊃ eqT (x,z)) ∧ 
>                  (∀ x y z. eqC (x,y) ∧ eqA (y,z) ⊃ eqT (x,z)) ∧ 
>                  (∀ x y z. eqA (x,y) ∧ eqC (y,z) ⊃ eqT (x,z)) ∧ 
>                  (∀ x y z. eqC (x,y) ∧ eqC (y,z) ⊃ eqT (x,z)) ∧ 
>                  (∀ x y z. eqA (x,y) ∧ eqT (y,z) ⊃ eqT (x,z)) ∧ 
>                  (∀ x y z. eqC (x,y) ∧ eqT (y,z) ⊃ eqT (x,z)) 
>                  ⊃ ∀ x. eqT (x * i(x),1) ∨ eqC (x * i(x),1) |]) 

>   , ("eq9", [form| (∀ x y z. eq1(x * (y * z),(x * y) * z)) ∧
>                   (∀ x y z. eq1((x * y) * z,x * (y * z))) ∧ 
>                   (∀ x. eq1(1 * x,x)) ∧ 
>                   (∀ x. eq1(x,1 * x)) ∧ 
>                   (∀ x. eq1(i(x) * x,1)) ∧ 
>                   (∀ x. eq1(1,i(x) * x)) ∧ 
>                   (∀ x y z. eq1(x,y) ⊃ eq1(x * z,y * z)) ∧ 
>                   (∀ x y z. eq1(x,y) ⊃ eq1(z * x,z * y)) ∧ 
>                   (∀ x y z. eq1(x,y) ∧ eq2(y,z) ⊃ eq2(x,z)) ∧ 
>                   (∀ x y. eq1(x,y) ⊃ eq2(x,y)) 
>                   ⊃ ∀ x. eq2(x,i(x)) |]) 

>   , ("eq10", [form| f(f(f(f(f(c))))) = c ∧ f(f(f(c))) = c
>                    ⊃ f(c) = c ∨ f(g(c)) = g(f(c)) |])

>   , ("eq11", [form| ∀ c. f(f(f(f(f(c))))) = c ∧ f(f(f(c))) = c ⊃ f(c) = c |])

eqelim.ml

>   , ("eq12", [form| (∀ x. R(x,x)) ∧
>                    (∀ x y. R(x,y) ⊃  R(y,x)) ∧ 
>                    (∀ x y z. R(x,y) ∧ R(y,z) ⊃ R(x,z)) 
>                    ⇔ (∀ x y. R(x,y) ⇔ (∀ z. R(x,z) ⇔ R(y,z))) |]) 

>   , ("abel", [form| (∀ x. P(1,x,x)) ∧
>          (∀ x. P(x,x,1)) ∧ 
>          (∀ u v w x y z. P(x,y,u) ∧ P(y,z,w) 
>                              ⊃ (P(x,w,v) ⇔ P(u,z,v))) 
>            ⊃ ∀ a b c. P(a,b,c) ⊃ P(b,a,c) |])

>   , ("abel_false", [form| (∀ x. P(x,x,1)) ∧
>                              (∀ u v w x y z.
>                                 P(x,y,u) ∧ P(y,z,w) ⊃ (P(x,w,v) ⇔ P(u,z,v)))
>                              ⊃ ∀ a b c. P(a,b,c) ⊃ P(b,a,c) |])

>   , ("ewd1062", [form| (∀ x. x ≤ x) ∧
>                       (∀ x y z. x ≤ y ∧ y ≤ z ⊃ x ≤ z) ∧ 
>                        (∀ x y. f(x) ≤ y ⇔ x ≤ g(y)) 
>                       ⊃ (∀ x y. x ≤ y ⊃ f(x) ≤ f(y)) ∧ 
>                       (∀ x y. x ≤ y ⊃ g(x) ≤ g(y)) |])

paramodulation.ml 

>   , ("para1", [form| (∀ x. f(f(x)) = f(x)) ∧ (∀ x. ∃ y. f(y) = x)
>    ⊃ ∀ x. f(x) = x |])
>     -- Groups

>   , ("group1", [form| (∀ x y z. x * (y * z) = (x * y) * z) ∧
>    (∀ x. e * x = x) ∧
>    (∀ x. i(x) * x = e)
>    ⊃ ∀ x. x * e = x |])

>   , ("group2", [form| (∀ x y z. x * (y * z) = (x * y) * z) ∧
>    (∀ x. e * x = x) ∧
>    (∀ x. i(x) * x = e)
>    ⊃ ∀ x. x * i(x) = e |])

** DLO

>   , ("dlo1", [form| ∀ x y. ∃ z. z < x ∧ z < y |])
>   , ("dlo2", [form| ∃ z. z < x ∧ z < y |])
>   , ("dlo3", [form| ∃ z. x < z ∧ z < y |])
>   , ("dlo4", [form| (∀ x. x < a ⊃ x < b) |])
>   , ("dlo5", [form| ∀ a b. (∀ x. x < a ⊃ x < b) ⇔ a ≤ b |])
>   , ("dlo6", [form| ∀ a b. (∀ x. x < a ⇔ x < b) ⇔ a = b |])
>   , ("dlo7", [form| ∃ x y z. ∀ u.
>                  x < x ∨ ¬ x < u ∨ (x < y ∧ y < z ∧ ¬ x < z) |])
>   , ("dlo8", [form| ∀ x. ∃ y. x < y |])
>   , ("dlo9", [form| ∀ x y z. x < y ∧ y < z ⊃ x < z |])
>   , ("dlo10", [form| ∀ x y. x < y ∨ (x = y) ∨ y < x |])
>   , ("dlo11", [form| ∃ x y. x < y ∧ y < x |])
>   , ("dlo12", [form| ∀ x y. ∃ z. z < x ∧ x < y |])
>   , ("dlo13", [form| ∃ z. z < x ∧ x < y |])
>   , ("dlo14", [form| ∀ x y. ∃ z. z < x ∧ z < y |])
>   , ("dlo15", [form| ∀ x y. x < y ⊃ ∃ z. x < z ∧ z < y |])
>   , ("dlo16", [form| ∀ x y. ¬ (x = y) ⊃ ∃ u. u < x ∧ (y < u ∨ x < y) |])
>   , ("dlo17", [form| ∃ x. x = x |])
>   , ("dlo18", [form| ∃ x. x = x ∧ x = y |])
>   , ("dlo19", [form| ∃ z. x < z ∧ z < y |])
>   , ("dlo20", [form| ∃ z. x ≤ z ∧ z ≤ y |])
>   , ("dlo21", [form| ∃ z. x < z ∧ z ≤ y |])
>   , ("dlo22", [form| ∀ x y z. ∃ u. u < x ∧ u < y ∧ u < z |])
>   , ("dlo23", [form| ∀ y. x < y ∧ y < z ⊃ w < z |])
>   , ("dlo24", [form| ∀ x y. x < y |])
>   , ("dlo25", [form| ∃ z. z < x ∧ x < y |])
>   , ("dlo26", [form| ∀ a b. (∀ x. x < a ⊃ x < b) ⇔ a ≤ b |])
>   , ("dlo27", [form| ∀ x. x < a ⊃ x < b |])
>   , ("dlo28", [form| ∀ x. x < a ⊃ x ≤ b |])
>   , ("dlo29", [form| ∀ a b. ∃ x. ¬ (x = a) ∨ ¬ (x = b) ∨ (a = b) |])
>   , ("dlo30", [form| ∀ x y. x ≤ y ∨ x > y |])
>   , ("dlo31", [form| 1 < 2 |])
>   , ("dlo32", [form| 1 < 2 ∧ 3 < 4 |])
>   , ("dlo33", [form| 1 < 2 ∧ 4 < 3 |])

** Presburger

>   , ("pres0", [form| ∀ x y. ¬ (2 * x + 1 = 2 * y) |])
>   , ("pres1", [form| ∀ x. ∃ y. 2 * y ≤ x ∧ x < 2 * (y + 1) |])
>   , ("pres2", [form| ∃ x y. 4 * x - 6 * y = 1 |])
>   , ("pres3", [form| ∀ x. ¬ divides(2,x) ∧ divides(3,x-1) ⇔
>                           divides(12,x-1) ∨ divides(12,x-7) |])
>   , ("pres4", [form| ∀ x. b < x ⊃ a ≤ x |])
>   , ("pres5", [form| ∃ x y. x > 0 ∧ y ≥ 0 ∧ 3 * x - 5 * y = 1 |])
>   , ("pres6", [form| ∃ x y z. 4 * x - 6 * y = 1 |])
>   , ("pres7", [form| ∀ x. a < 3 * x ⊃ b < 3 * x |])
>   , ("pres8", [form| ∀ x y. x ≤ y ⊃ 2 * x + 1 < 2 * y |])
>   , ("pres9", [form| (∃ d. y = 65 * d) ⊃ (∃ d. y = 5 * d) |])
>   , ("pres10", [form| ∀ y. (∃ d. y = 65 * d) ⊃ (∃ d. y = 5 * d) |])
>   , ("pres11", [form| ∀ x y. ¬ (2 * x + 1 = 2 * y) |])
>   , ("pres12", [form| ∀ x y z. (2 * x + 1 = 2 * y) ⊃ x + y + z > 129 |])
>   , ("pres13", [form| ∀ x. a < x ⊃ b < x |])
>   , ("pres14", [form| ∀ x. a ≤ x ⊃ b < x |])

Formula examples from Cooper's paper. 

>   , ("pres15", [form| ∀ a b. ∃ x. a < 20 * x ∧ 20 * x < b |])
>   , ("pres16", [form| ∃ x. a < 20 * x ∧ 20 * x < b |])
>   , ("pres17", [form| ∀ b. ∃ x. a < 20 * x ∧ 20 * x < b |])
>   , ("pres18", [form| ∀ a. ∃ b. a < 4 * b + 3 * a ∨ (¬ (a < b) ∧ a > b + 1) |])
>   , ("pres19", [form| ∃ y. ∀ x. x + 5 * y > 1 ∧ 13 * x - y > 1 ∧ x + 2 < 0 |])

More of my own.                                                           

>   , ("pres20", [form| ∀ x y. x ≥ 0 ∧ y ≥ 0
>                   ⊃ 12 * x - 8 * y < 0 ∨ 12 * x - 8 * y > 2 |])
>   , ("pres21", [form| ∃ x y. 5 * x + 3 * y = 1 |])
>   , ("pres22", [form| ∃ x y. 5 * x + 10 * y = 1 |])
>   , ("pres23", [form| ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 5 * x - 6 * y = 1 |])
>   , ("pres24", [form| ∃ w x y z. 2 * w + 3 * x + 4 * y + 5 * z = 1 |])
>   , ("pres25", [form| ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 5 * x - 3 * y = 1 |])
>   , ("pres26", [form| ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x - 5 * y = 1 |])
>   , ("pres27", [form| ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 6 * x - 3 * y = 1 |])
>   , ("pres28", [form| ∀ x y. ¬ (x = 0) ⊃ 5 * y < 6 * x ∨ 5 * y > 6 * x |])
>   , ("pres29", [form| ∀ x y. ¬ divides(5,x) ∧ ¬ divides(6,y) ⊃ ¬ (6 * x = 5 * y) |])
>   , ("pres30", [form| ∀ x y. ¬ divides(5,x) ⊃ ¬ (6 * x = 5 * y) |])
>   , ("pres31", [form| ∀ x y. ¬ (6 * x = 5 * y) |])
>   , ("pres32", [form| ∀ x y. 6 * x = 5 * y ⊃ ∃ d. y = 3 * d |])
>   , ("pres33", [form| 6 * x = 5 * y ⊃ ∃ d. y = 3 * d |])

Positive variant of the Bezout theorem (see the exercise).                

>   , ("pres34", [form| ∀ z. z > 7 ⊃ ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z |])
>   , ("pres35", [form| ∀ z. z > 2 ⊃ ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z |])
>   , ("pres36", [form| ∀ z.
>         z ≤ 7
>         ⊃ ((∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z) ⇔
>              ¬ (∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = 7 - z)) |])

Basic result about congruences.                                           

>   , ("pres37", [form| ∀ x. ¬ divides(2,x) ∧ divides(3,x-1) ⇔
>               divides(12,x-1) ∨ divides(12,x-7) |])
>   , ("pres38", [form| ∀ x. ¬ (∃ m. x = 2 * m) ∧ (∃ m. x = 3 * m + 1) ⇔
>               (∃ m. x = 12 * m + 1) ∨ (∃ m. x = 12 * m + 7) |])

Something else.

>   , ("pres39", [form| ∀ x.
>         ¬ (divides(2,x))
>         ⊃ divides(4,x-1) ∨
>             divides(8,x-1) ∨
>             divides(8,x-3) ∨
>             divides(6,x-1) ∨
>             divides(14,x-1) ∨
>             divides(14,x-9) ∨
>             divides(14,x-11) ∨
>             divides(24,x-5) ∨
>             divides(24,x-11) |])

Testing fix for an earlier version with negative result from formlcm.     

>   , ("pres40", [form| a + 2 = b ∧ v_3 = b - a + 1 ∧ v_2 = b - 2 ∧ v_1 = 3 ⊃ ⊥ |])

Inspired by the Collatz conjecture.                                       

>   , ("pres41", [form| ∃ a b. ¬ (a = 1) ∧ ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧ (a = b) |])
>   , ("pres42", [form| ∃ a b. a > 1 ∧ b > 1 ∧
>                ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧
>                (a = b) |])

Haskell destroys ML on this example.x

>   , ("pres43", [form| ∃ a b. a > 1 ∧ b > 1 ∧
>                ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧
>                ((2 * a = b) ∨ (2 * a = 3 * b + 1)) |])

Bob Constable's "stamp problem".  Haskell is much faster on these problems.

>   , ("pres45", [form| ∀ x. x ≥ 8 ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 5 * v |])

>   , ("pres46", [form| ∃ l.
>         ∀ x. x ≥ l
>                   ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 5 * v |])

>   , ("pres47", [form| ∃ l.
>         ∀ x. x ≥ l
>                   ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 7 * v |])

>   , ("pres48", [form| ∃ l.
>         ∀ x. x ≥ l
>                   ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 8 * v |])

 FIXME: This one explodes memory to 1GB within a few seconds.  Investigate
 when you get a chance.

>   , ("pres49", [form| ∃ l.
>         ∀ x. x ≥ l
>                   ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 7 * u + 8 * v |])

Example from reciprocal mult: (2622 * x)>>16 = x/100 within a range.      

>   , ("pres50", [form| ∀ x q1 q2 r1 r2.
>         x < 4699 ∧
>         2622 * x = 65536 * q1 + r1 ∧ 0 ≤ q1 ∧ 0 ≤ r1 ∧ r1 < 65536 ∧
>         x = 100 * q2 + r2 ∧ 0 ≤ q2 ∧ 0 ≤ r2 ∧ r2 < 100
>         ⊃ q1 = q2 |])
>   , ("pres51", [form| ∀ x y.
>         (∃ d. x + y = 2 * d) ⇔
>         ((∃ d. x = 2 * d) ⇔ (∃ d. y = 2 * d)) |])

Landau trick! Is it too slow?

>   , ("pres52", [form| ∀ n.
>      0 < n ∧ n < 2400
>        ⊃ n ≤ 2 ∧ 2 ≤ 2 * n ∨
>            n ≤ 3 ∧ 3 ≤ 2 * n ∨
>            n ≤ 5 ∧ 5 ≤ 2 * n ∨
>            n ≤ 7 ∧ 7 ≤ 2 * n ∨
>            n ≤ 13 ∧ 13 ≤ 2 * n ∨
>            n ≤ 23 ∧ 23 ≤ 2 * n ∨
>            n ≤ 43 ∧ 43 ≤ 2 * n ∨
>            n ≤ 83 ∧ 83 ≤ 2 * n ∨
>            n ≤ 163 ∧ 163 ≤ 2 * n ∨
>            n ≤ 317 ∧ 317 ≤ 2 * n ∨
>            n ≤ 631 ∧ 631 ≤ 2 * n ∨
>            n ≤ 1259 ∧ 1259 ≤ 2 * n ∨
>            n ≤ 2503 ∧ 2503 ≤ 2 * n |])
>   , ("pres53", [form| ∀ d. ∃ x y. 3 * x + 5 * y = d |])
>   , ("pres54", [form| ∀ d. ∃ x y. 3 * x + 5 * y = d |])
>   , ("pres55", [form| ∀ d. d ≥ 8 ⊃ ∃ x y. 3 * x + 5 * y = d |])
>   , ("pres56", [form| ∀ d. ∃ x y. 3 * x - 5 * y = d |])

** Nelson-Oppen

>   , ("nelop0", [form| f(v - 1) - 1 = v + 1 ∧ f(u) + 1 = u - 1 ∧ u + 1 = v ⊃ ⊥ |])
>   , ("nelop1", [form| y ≤ x ∧ y ≥ x + z ∧ z ≥ 0 ⊃ f(f(x) - f(y)) = f(z) |])
>   , ("nelop2", [form| x = y ∧ y ≥ z ∧ z ≥ x ⊃ f(z) = f(x) |])
>   , ("nelop3", [form| a ≤ b ∧ b ≤ f(a) ∧ f(a) ≤ 1
>   ⊃ a + b ≤ 1 ∨ b + f(b) ≤ 1 ∨ f(f(b)) ≤ f(a) |])

Failures of original Shostak procedure.                                   

>   , ("nelop4", [form| f(v - 1) - 1 = v + 1 ∧ f(u) + 1 = u - 1 ∧ u + 1 = v ⊃ ⊥ |])

And this one is where the original procedure loops 

>   , ("nelop5", [form| f(v) = v ∧ f(u) = u - 1 ∧ u = v ⊃ ⊥ |])

This is on p. 8 of Shostak's "Deciding combinations" paper 

>   , ("nelop6", [form| z = f(x - y) ∧ x = z + y ∧ ¬ (-(y) = -(x - f(f(z)))) ⊃ ⊥ |])

This (ICS theories-1) fails without array operations 

>   , ("nelop7", [form| a + 2 = b ⊃ f(read(update(A,a,3),b-2)) = f(b - a + 1) |])

can-001 from ICS examples site, with if-then-elses expanded manually 

>   , ("nelop8", [form| (x = y ∧ z = 1 ⊃ f(f((x+z))) = f(f((1+y)))) |])

RJB example; lists plus uninterpreted functions 

>   , ("nelop9", [form| hd(x) = hd(y) ∧ tl(x) = tl(y) ∧ ¬ (x = nil) ∧ ¬ (y = nil)
>    ⊃ f(x) = f(y) |])

Another one from the ICS paper 

>   , ("nelop10", [form| ¬ (f(f(x) - f(y)) = f(z)) ∧ y ≤ x ∧ y ≥ x + z ∧ z ≥ 0 ⊃ ⊥ |])

Shostak's "A Practical Decision Procedure..."

No longer works since I didn't do predicates in congruence closure

>   , ("nelop11", [form| x < f(y) + 1 ∧ f(y) ≤ x ⊃ (P(x,y) ⇔ P(f(y),y)) |])

Shostak's "Practical..." paper again, using extra clauses for MAX 

>   , ("nelop12", [form| (x ≥ y ⊃ MAX(x,y) = x) ∧ (y ≥ x ⊃ MAX(x,y) = y)
>                           ⊃ x = y + 2 ⊃ MAX(x,y) = x |])

Shostak's "Practical..." paper again 

>   , ("nelop13", [form| x ≤ g(x) ∧ x ≥ g(x) ⊃ x = g(g(g(g(x)))) |])

Easy example I invented 

>   , ("nelop14", [form| x^2 =  1 ⊃ (f(x) = f(-(x)))  ⊃ (f(x) = f(1)) |])

Taken from Clark Barrett's CVC page 

>   , ("nelop15", [form| 2 * f(x + y) = 3 * y ∧ 2 * x = y ⊃ f(f(x + y)) = 3 * x |])

My former running example in the text; seems too slow.
Anyway this also needs extra predicates in CC

>   , ("nelop16", [form| x^2 = y^2 ∧ x < y ∧ z^2 = z ∧ x < x * z ∧ P(f(1 + z))
>                               ⊃ P(f(x + y) - f(0)) |])

An example where the "naive" procedure is slow but feasible

>   , ("nelop17", [form| 4 * x = 2 * x + 2 * y ∧ x = f(2 * x - y) ∧
>                            f(2 * y - x) = 3 ∧ f(x) = 4 ⊃ ⊥ |])

DKAL

>   , ("alice1", [form|
>        ((curTime(alice) < licExp(X) ∧
>        curTime(alice) < licExp(X)) ∧
>       curTime(alice) < licExp(Y)) ⊃
>       (((curTime(alice) < licExp(Y)) ∧
>        curTime(alice) < licExp(Y)) ∧
>        curTime(alice) < licExp(Y)) |])

>   , ("alice2", [form|
>       ((curTime(alice) < licExp(X) ∧ ⊤ ∧ ⊤ ∧ ⊤) ∧
>        curTime(alice) < licExp(X) ∧ ⊤ ∧ ⊤ ∧ ⊤) ∧
>       curTime(alice) < licExp(Y) ∧ ⊤ ∧ ⊤ ∧ ⊤ ⊃
>       ((curTime(alice) < licExp(Y) ∧ ⊤ ∧ ⊤ ∧ ⊤) ∧
>        curTime(alice) < licExp(Y) ∧ ⊤ ∧ ⊤ ∧ ⊤) ∧
>       curTime(alice) < licExp(Y) ∧ ⊤ ∧ ⊤ ∧ ⊤ |])

Complex

>   , ("cplx1", [form| ∀ a x. a^2 = 2 ∧ x^2 + a * x + 1 = 0 ⊃ x^4 + 1 = 0 |])

>   , ("cplx2", [form| ∀ a x. a^2 = 2 ∧ x^2 + a * x + 1 = 0 ⊃ x^4 + c = 0 |])

>   , ("cplx3", [form|
>        ∀ c. (∀ a x. a^2 = 2 ∧ x^2 + a * x + 1 = 0 ⊃ x^4 + c = 0)
>            ⇔ c = 1 |])

>   , ("cplx4", [form|
>      ∀ a b c x y.
>       a * x^2 + b * x + c = 0 ∧ a * y^2 + b * y + c = 0 ∧ ~(x = y)
>       ⊃ a * x * y = c ∧ a * (x + y) + b = 0 |])

>   , ("cplx5", [form| ∃ x. x + 2 = 3 |])

>   , ("cplx6", [form| ∃ x. x^2 + a = 3 |])

>   , ("cplx7", [form| ∃ x. x^2 + x + 1 = 0 |])

>   , ("cplx8", [form| ∃ x. x^2 + x + 1 = 0 ∧ x^3 + x^2 + 1 = 0 |])

>   , ("cplx9", [form| ∃ x. x^2 + 1 = 0 ∧ x^4 + x^3 + x^2 + x = 0 |])

>   , ("cplx10", [form| ∀ a x. a^2 = 2 ∧ x^2 + a * x + 1 = 0 ⊃ x^4 + 1 = 0 |])

>   , ("cplx11", [form| ∀ a x. a^2 = 2 ∧ x^2 + a * x + 1 = 0 ⊃ x^4 + 2 = 0 |])

>   , ("cplx12", [form| ∃ a x. a^2 = 2 ∧ x^2 + a * x + 1 = 0 ∧ ~(x^4 + 2 = 0) |])

>   , ("cplx13", [form| ∃ x. a^2 = 2 ∧ x^2 + a * x + 1 = 0 ∧ ~(x^4 + 2 = 0) |])

>   , ("cplx14", [form| ∀ x. x^2 + a * x + 1 = 0 ⊃ x^4 + 2 = 0 |])

>   , ("cplx15", [form| ∀ a. a^2 = 2 ∧ x^2 + a * x + 1 = 0 ⊃ x^4 + 2 = 0 |])

>   , ("cplx16", [form| ∃ a b c x y.
>         a * x^2 + b * x + c = 0 ∧
>         a * y^2 + b * y + c = 0 ∧
>         ~(x = y) ∧
>         ~(a * x * y = c) |])

>   , ("cplx17", [form| ∀ a b c x.
>         (∀ z. a * z^2 + b * z + c = 0 <=> z = x)
>         ⊃ a * x * x = c ∧ a * (x + x) + b = 0 |])

>   , ("cplx18", [form| ∀ x y.
>     (∀ a b c. (a * x^2 + b * x + c = 0) ∧
>                    (a * y^2 + b * y + c = 0)
>                    ⊃ (a * x * y = c) ∧ (a * (x + y) + b = 0))
>     <=> ~(x = y) |])

>   , ("cplx19", [form| ∀ y_1 y_2 y_3 y_4.
>      (y_1 = 2 * y_3) ∧
>      (y_2 = 2 * y_4) ∧
>      (y_1 * y_3 = y_2 * y_4)
>      ⊃ (y_1^2 = y_2^2) |])

>   , ("cplx20", [form| ∀ x y. x^2 = 2 ∧ y^2 = 3
>          ⊃ (x * y)^2 = 6 |])

>   , ("cplx21", [form| ∀ x a. (a^2 = 2) ∧ (x^2 + a * x + 1 = 0)
>          ⊃ (x^4 + 1 = 0) |])

>   , ("cplx22", [form| ∀ a x. (a^2 = 2) ∧ (x^2 + a * x + 1 = 0)
>          ⊃ (x^4 + 1 = 0) |])

>   , ("cplx23", [form| ~(∃ a x y. (a^2 = 2) ∧
>              (x^2 + a * x + 1 = 0) ∧
>              (y * (x^4 + 1) + 1 = 0)) |])

>   , ("cplx24", [form| ∀ x. ∃ y. x^2 = y^3 |])
> 
>   , ("cplx25", [form| ∀ x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
>                2 * (b * x + b * z - a * y) |])

>   , ("cplx26", [form| ∀ a b. ~(a = b) ⊃ ∃ x y. (y * x^2 = a) ∧ (y * x^2 + x = b) |])
> 
>   , ("cplx27", [form| ∀ a b c x y. (a * x^2 + b * x + c = 0) ∧
>                (a * y^2 + b * y + c = 0) ∧
>                ~(x = y)
>                ⊃ (a * x * y = c) ∧ (a * (x + y) + b = 0) |])

>   , ("cplx28", [form| ~(∀ a b c x y. (a * x^2 + b * x + c = 0) ∧
>                  (a * y^2 + b * y + c = 0)
>                  ⊃ (a * x * y = c) ∧ (a * (x + y) + b = 0)) |])

>   , ("cplx29", [form| ∀ y_1 y_2 y_3 y_4.
>      (y_1 = 2 * y_3) ∧
>      (y_2 = 2 * y_4) ∧
>      (y_1 * y_3 = y_2 * y_4)
>      ⊃ (y_1^2 = y_2^2) |])

>   , ("cplx30", [form| ∀ a1 b1 c1 a2 b2 c2.
>         ~(a1 * b2 = a2 * b1)
>         ⊃ ∃ x y. (a1 * x + b1 * y = c1) ∧ (a2 * x + b2 * y = c2) |])

>   , ("cplx31", [form| (a * x^2 + b * x + c = 0) ∧
>   (a * y^2 + b * y + c = 0) ∧
>   (∀ z. (a * z^2 + b * z + c = 0)
>        ⊃ (z = x) ∨ (z = y))
>   ⊃ (a * x * y = c) ∧ (a * (x + y) + b = 0) |])

>   , ("cplx32", [form| ∀ y. (a * x^2 + b * x + c = 0) ∧
>             (a * y^2 + b * y + c = 0) ∧
>             (∀ z. (a * z^2 + b * z + c = 0)
>                        ⊃ (z = x) ∨ (z = y))
>             ⊃ (a * x * y = c) ∧ (a * (x + y) + b = 0) |])

>   , ("cplx33", [form| ~(∀ x1 y1 x2 y2 x3 y3.
>       ∃ x0 y0. (x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 ∧
>                     (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2) |])

>   , ("cplx34", [form| ∀ a b c.
>       (∃ x y. (a * x^2 + b * x + c = 0) ∧
>              (a * y^2 + b * y + c = 0) ∧
>              ~(x = y)) <=>
>       (a = 0) ∧ (b = 0) ∧ (c = 0) ∨
>       ~(a = 0) ∧ ~(b^2 = 4 * a * c) |])

>   , ("cplx35", [form| ~(∀ x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
>         (x1 - x0)^2 + (y1 - y0)^2 =
>         (x2 - x0)^2 + (y2 - y0)^2 ∧
>         (x2 - x0)^2 + (y2 - y0)^2 =
>         (x3 - x0)^2 + (y3 - y0)^2 ∧
>         (x1 - x0')^2 + (y1 - y0')^2 =
>         (x2 - x0')^2 + (y2 - y0')^2 ∧
>         (x2 - x0')^2 + (y2 - y0')^2 =
>         (x3 - x0')^2 + (y3 - y0')^2
>         ⊃ x0 = x0' ∧ y0 = y0') |])

>   , ("cplx36", [form| ∀ a b c.
>         a * x^2 + b * x + c = 0 ∧
>         a * y^2 + b * y + c = 0 ∧
>         ~(x = y)
>         ⊃ a * (x + y) + b = 0 |])

>   , ("cplx37", [form| ∀ a b c.
>         (a * x^2 + b * x + c = 0) ∧
>         (2 * a * y^2 + 2 * b * y + 2 * c = 0) ∧
>         ~(x = y)
>         ⊃ (a * (x + y) + b = 0) |])

>   , ("cplx38", [form| ~(y_1 = 2 * y_3 ∧
>     y_2 = 2 * y_4 ∧
>     y_1 * y_3 = y_2 * y_4 ∧
>     (y_1^2 - y_2^2) * z = 1) |])

>   , ("cplx39", [form| ∀ y_1 y_2 y_3 y_4.
>        (y_1 = 2 * y_3) ∧
>        (y_2 = 2 * y_4) ∧
>        (y_1 * y_3 = y_2 * y_4)
>        ⊃ (y_1^2 = y_2^2) |])

>   , ("cplx40", [form| (x1 = u3) ∧
>   (x1 * (u2 - u1) = x2 * u3) ∧
>   (x4 * (x2 - u1) = x1 * (x3 - u1)) ∧
>   (x3 * u3 = x4 * u2) ∧
>   ~(u1 = 0) ∧
>   ~(u3 = 0)
>   ⊃ (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2) |])

>   , ("cplx41", [form| (u1 * x1 - u1 * u3 = 0) ∧
>   (u3 * x2 - (u2 - u1) * x1 = 0) ∧
>   (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) ∧
>   (u3 * x4 - u2 * x3 = 0) ∧
>   ~(u1 = 0) ∧
>   ~(u3 = 0)
>   ⊃ (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0) |])

>   , ("cplx42", [form| (y1 * y3 + x1 * x3 = 0) ∧
>   (y3 * (y2 - y3) + (x2 - x3) * x3 = 0) ∧
>   ~(x3 = 0) ∧
>   ~(y3 = 0)
>   ⊃ (y1 * (x2 - x3) = x1 * (y2 - y3)) |])

>   , ("cplx43", [form| ∀ a b c.
>    (∃ x. a * x^2 + b * x + c = 0 ∧ 2 * a * x + b = 0) ∨ (a = 0) <=>
>    (4*a^2*c-b^2*a = 0) |])

>   , ("cplx44", [form| ∀ a b c d e.
>   (∃ x. a * x^2 + b * x + c = 0 ∧ d * x + e = 0) ∨
>    a = 0 ∧ d = 0 <=> d^2*c-e*d*b+a*e^2 = 0 |])

>   , ("cplx45", [form| ∀ a b c d e f.
>    (∃ x. a * x^2 + b * x + c = 0 ∧ d * x^2 + e * x + f = 0) ∨
>    (a = 0) ∧ (d = 0) <=>
>    d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0 |])

>   , ("cplx46", [form| ∀ x y. x^2 + y^2 = 1 ⊃ (2 * y^2 - 1)^2 + (2 * x * y)^2 = 1 |])
> 
>   , ("cplx47", [form| ∀ s c. s^2 + c^2 = 1
>       ⊃ 2 * s - (2 * s * c * c - s^3) = 3 * s^3 |])

>   , ("cplx48", [form| ∀ u v.
>   -((((9 * u^8) * v) * v - (u * u^9)) * 128) -
>      (((7 * u^6) * v) * v - (u * u^7)) * 144 -
>      (((5 * u^4) * v) * v - (u * u^5)) * 168 -
>      (((3 * u^2) * v) * v - (u * u^3)) * 210 -
>      (v * v - (u * u)) * 315 + 315 - 1280 * u^10 =
>    (-(1152) * u^8 - 1008 * u^6 - 840 * u^4 - 630 * u^2 - 315) *
>    (u^2 + v^2 - 1) |])

>   , ("cplx49", [form| ∀ u v.
>         u^2 + v^2 = 1
>         ⊃ (((9 * u^8) * v) * v - (u * u^9)) * 128 +
>             (((7 * u^6) * v) * v - (u * u^7)) * 144 +
>             (((5 * u^4) * v) * v - (u * u^5)) * 168 +
>             (((3 * u^2) * v) * v - (u * u^3)) * 210 +
>             (v * v - (u * u)) * 315 + 1280 * u^10 = 315 |])

>   , ("cplx50", [form| ∃ z. x * z^87 + y * z^44 + 1 = 0 |])
> 
>   , ("cplx51", [form| ∀ u. ∃ v. x * (u + v^2)^2 + y * (u + v^2) + z = 0 |])

>   , ("cplx52", [form| ∀ x y. (∃ z. x * z^87 + y * z^44 + 1 = 0)
>                   <=> ~(x = 0) ∨ ~(y = 0) |])

>   , ("cplx53", [form| ∀ x y z. (∀ u. ∃ v.
>                          x * (u + v^2)^2 + y * (u + v^2) + z = 0)
>                     <=> ~(x = 0) ∨ ~(y = 0) ∨ z = 0 |])

>   , ("cplx54", [form| ∃ w x y z. (a * w + b * y = 1) ∧
>                       (a * x + b * z = 0) ∧
>                       (c * w + d * y = 0) ∧
>                       (c * x + d * z = 1) |])

>   , ("cplx55", [form| ∀ a b c d.
>         (∃ w x y z. (a * w + b * y = 1) ∧
>                          (a * x + b * z = 0) ∧
>                          (c * w + d * y = 0) ∧
>                          (c * x + d * z = 1))
>         <=> ~(a * d = b * c) |])

>   , ("cplx56", [form| ∀ m n x u t cu ct.
>    t - u = n ∧ 27 * t * u = m^3 ∧
>    ct^3 = t ∧ cu^3 = u ∧
>    x = ct - cu
>    ⊃ x^3 + m * x = n |])

>   , ("cplx57", [form| ∀ m n x u t.
>    t - u = n ∧ 27 * t * u = m^3
>    ⊃ ∃ ct cu. ct^3 = t ∧ cu^3 = u ∧
>                      (x = ct - cu ⊃ x^3 + m * x = n) |])

>   , ("cplx58", [form| ∀ x y z.
>     (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
>      x^2 * y^2 * (x^2 + y^2 + 1) * (x^2 + y^2 - 2)^2 + (x^2 - y^2)^2 |])

>   , ("cplx59", [form| ∀ x y z.
>     (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
>     x^2 * y^2 * x^2  * (x^2 + y^2 - 2)^2 +
>     x^2 * y^2 * y^2 * (x^2 + y^2 - 2)^2 +
>     x^2 * y^2 * (x^2 + y^2 - 2)^2 +
>     (x^2 - y^2)^2 |])

>   , ("cplx60", [form| ∀ x y z.
>     (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
>     x^4 * y^2 * (x^2 + y^2 - 2)^2 +
>     x^2 * y^4 * (x^2 + y^2 - 2)^2 +
>     x^2 * y^2 * (x^2 + y^2 - 2)^2 +
>     (x^2 - y^2)^2 |])

>   , ("cplx61", [form| ∀ x y z.
>     (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
>     (x^2 * y * (x^2 + y^2 - 2))^2 +
>     (x * y^2 * (x^2 + y^2 - 2))^2 +
>     (x * y * (x^2 + y^2 - 2))^2 +
>     (x^2 - y^2)^2 |])

>   , ("cplx62", [form| ∀ x y. (a * x + b * y = u * x - v * y) ∧
>                 (c * x + d * y = u * y + v * x)
>                 ⊃ (a = d) |])

>   , ("cplx63", [form| ∀ a b c d.
>       (∀ x y. (a * x + b * y = u * x - v * y) ∧
>                    (c * x + d * y = u * y + v * x))
>                    ⊃ (a = d) ∧ (b = -(c)) |])

>   , ("cplx64", [form| ∀ a b c d.
>         (∃ u v. ∀ x y. (a * x + b * y = u * x - v * y) ∧
>                                  (c * x + d * y = u * y + v * x))
>         <=> (a = d) ∧ (b = -(c)) |])

>   , ("cplx65", [form| ∀ x1 y1 x2 y2. ∃ a b.
>       ~(a = 0 ∧ b = 0) ∧ a * x1 + b * y1 = 0 ∧ a * x2 + b * y2 = 0 |])

>   , ("cplx66", [form| ∀ x y. (a * x^2 + b * x + c = 0) ∧
>               (a * y^2 + b * y + c = 0) ∧ 
>               (∀ z. (a * z^2 + b * z + c = 0)
>                          ⊃ (z = x) ∨ (z = y))
>               ⊃ (a * x * y = c) ∧ (a * (x + y) + b = 0) |])

Real

>   , ("real0", [form| ∃ x. x^2 = 0 |])
>   , ("real1", [form| ∃ x. x^3 + x + 1 = 0 |])
>   , ("real2", [form| ∃ x. x^4 + x^2 + 1 = 0 |])

>   , ("real3", [form| ∃ x y. x^3 - x^2 + x - 1 = 0 ∧
>                          y^3 - y^2 + y - 1 = 0 ∧ ~(x = y) |])

>   , ("real4", [form| ∃ x. x^2 - 3 * x + 2 = 0 ∧ 2 * x - 3 = 0 |])

>   , ("real5", [form| ∀ a f k. (∀ e. k < e ⊃ f < a * e) ⊃ f ≤ a * k |])

>   , ("real6", [form| ∃ x. a * x^2 + b * x + c = 0 |])

>   , ("real7", [form| ∀ a b c. (∃ x. a * x^2 + b * x + c = 0) ⇔
>                            b^2 >= 4 * a * c |])

>   , ("real8", [form| ∀ a b c. (∃ x. a * x^2 + b * x + c = 0) ⇔
>                            a = 0 ∧ (b = 0 ⊃ c = 0) ∨
>                           ~(a = 0) ∧ b^2 >= 4 * a * c |])

>   , ("real9", [form| 1 < 2 ∧ (∀ x. 1 < x ⊃ 1 < x^2) ∧
>              (∀ x y. 1 < x ∧ 1 < y ⊃ 1 < x * (1 + 2 * y)) |])

>   , ("real10", [form| ∀ d.
>      (∃ c. ∀ a b. (a = d ∧ b = c) ∨ (a = c ∧ b = 1)
>                             ⊃ a^2 = b)
>       ⇔ d^4 = 1 |])

Grobner

>   , ("grob0", [form| a^2 = 2 ∧ x^2 + a*x + 1 = 0 ⊃ x^4 + 1 = 0 |])

>   , ("grob1", [form| a^2 = 2 ∧ x^2 + a*x + 1 = 0 ⊃ x^4 + 2 = 0 |])

>   , ("grob2", [form| (a * x^2 + b * x + c = 0) ∧
>                       (a * y^2 + b * y + c = 0) ∧
>                         ~(x = y) ⊃ (a * x * y = c) ∧ (a * (x + y) + b = 0) |])

>   , ("grob3", [form| a^2 = 2 ∧ x^2 + a*x + 1 = 0 ⊃ x^4 + 1 = 0 |])

>   , ("grob4", [form| a^2 = 2 ∧ x^2 + a*x + 1 = 0 ⊃ x^4 + 2 = 0 |])

>   , ("grob5", [form| (a * x^2 + b * x + c = 0) ∧
>      (a * y^2 + b * y + c = 0) ∧
>      ~(x = y)
>      ⊃ (a * x * y = c) ∧ (a * (x + y) + b = 0) |])

>   , ("grob6", [form| (y_1 = 2 * y_3) ∧
>                (y_2 = 2 * y_4) ∧
>                (y_1 * y_3 = y_2 * y_4)
>                ⊃ (y_1^2 = y_2^2) |])

>   , ("grob7",  [form| (x1 = u3) ∧
>              (x1 * (u2 - u1) = x2 * u3) ∧
>              (x4 * (x2 - u1) = x1 * (x3 - u1)) ∧
>              (x3 * u3 = x4 * u2) ∧
>              ~(u1 = 0) ∧
>              ~(u3 = 0)
>              ⊃ (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2) |])

>   , ("grob8", [form| (u1 * x1 - u1 * u3 = 0) ∧
>             (u3 * x2 - (u2 - u1) * x1 = 0) ∧
>             (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) ∧
>             (u3 * x4 - u2 * x3 = 0) ∧
>             ~(u1 = 0) ∧
>             ~(u3 = 0)
>             ⊃ (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0) |])

Checking resultants (in one direction) 

>   , ("grob9", [form| a * x^2 + b * x + c = 0 ∧ 2 * a * x + b = 0 ⊃ 4*a^2*c-b^2*a = 0 |])

>   , ("grob10", [form| a * x^2 + b * x + c = 0 ∧ d * x + e = 0 ⊃ d^2*c-e*d*b+a*e^2 = 0 |])

>   , ("grob11", [form| a * x^2 + b * x + c = 0 ∧ d * x^2 + e * x + f = 0 ⊃ d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0 |])

>   , ("grob12", [form| a * x^3 + b * x^2 + c * x + d = 0 ∧ e * x^2 + f * x + g = 0
>                 ⊃ e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
>                   g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0 |])

>   , ("grob13", [form| (x1 - x0)^2 + (y1 - y0)^2 =
>          (x2 - x0)^2 + (y2 - y0)^2 ∧
>          (x2 - x0)^2 + (y2 - y0)^2 =
>          (x3 - x0)^2 + (y3 - y0)^2 ∧
>          (x1 - x0')^2 + (y1 - y0')^2 =
>          (x2 - x0')^2 + (y2 - y0')^2 ∧
>          (x2 - x0')^2 + (y2 - y0')^2 =
>          (x3 - x0')^2 + (y3 - y0')^2
>          ⊃ x0 = x0' ∧ y0 = y0' |])

Corrected with non-isotropy conditions; even lengthier

>   , ("grob14", [form| (x1 - x0)^2 + (y1 - y0)^2 =
>              (x2 - x0)^2 + (y2 - y0)^2 ∧
>              (x2 - x0)^2 + (y2 - y0)^2 =
>              (x3 - x0)^2 + (y3 - y0)^2 ∧
>              (x1 - x0')^2 + (y1 - y0')^2 =
>              (x2 - x0')^2 + (y2 - y0')^2 ∧
>              (x2 - x0')^2 + (y2 - y0')^2 =
>              (x3 - x0')^2 + (y3 - y0')^2 ∧
>              ~((x1 - x0)^2 + (y1 - y0)^2 = 0) ∧
>              ~((x1 - x0')^2 + (y1 - y0')^2 = 0)
>              ⊃ x0 = x0' ∧ y0 = y0' |])

Maybe this is more efficient? (No?)

>   , ("grob15", [form| (x1 - x0)^2 + (y1 - y0)^2 = d ∧
>             (x2 - x0)^2 + (y2 - y0)^2 = d ∧
>             (x3 - x0)^2 + (y3 - y0)^2 = d ∧
>             (x1 - x0')^2 + (y1 - y0')^2 = e ∧
>             (x2 - x0')^2 + (y2 - y0')^2 = e ∧
>             (x3 - x0')^2 + (y3 - y0')^2 = e ∧
>             ~(d = 0) ∧ ~(e = 0)
>             ⊃ x0 = x0' ∧ y0 = y0' |])

(* ------------------------------------------------------------------------- *)
(* Inversion of homographic function (from Gosper's CF notes).               *)
(* ------------------------------------------------------------------------- *)

>   , ("grob16", [form| y * (c * x + d) = a * x + b ⊃ x * (c * y - a) = b - d * y |])

(* ------------------------------------------------------------------------- *)
(* Manual "sums of squares" for 0 <= a ∧ a <= b ⊃ a^3 <= b^3.             *)
(* ------------------------------------------------------------------------- *)

>   , ("grob17", [form| ∀ a b c d e.
>      a = c^2 ∧ b = a + d^2 ∧ (b^3 - a^3) * e^2 + 1 = 0
>      ⊃ (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
>         0 |])

>   , ("grob18", [form| a = c^2 ∧ b = a + d^2 ∧ (b^3 - a^3) * e^2 + 1 = 0
>        ⊃ (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
>           0 |])

(* ------------------------------------------------------------------------- *)
(* Special case of a = 1, i.e. 1 <= b ⊃ 1 <= b^3                           *)
(* ------------------------------------------------------------------------- *)

>   , ("grob19", [form| ∀ b d e.
>      b = 1 + d^2 ∧ (b^3 - 1) * e^2 + 1 = 0
>      ⊃ 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 = 0 |])

>   , ("grob20", [form| b = 1 + d^2 ∧ (b^3 - 1) * e^2 + 1 = 0
>       ⊃ 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 =  0 |])

(* ------------------------------------------------------------------------- *)
(* Converse, 0 <= a ∧ a^3 <= b^3 ⊃ a <= b                                 *)
(*                                                                           *)
(* This derives b <= 0, but not a full solution.                             *)
(* ------------------------------------------------------------------------- *)

>   , ("grob21", [form| a = c^2 ∧ b^3 = a^3 + d^2 ∧ (b - a) * e^2 + 1 = 0
>                  ⊃ c^2 * b + a^2 + b^2 + (e * d)^2 = 0 |])

(* ------------------------------------------------------------------------- *)
(* Here are further steps towards a solution, step-by-step.                  *)
(* ------------------------------------------------------------------------- *)

>   , ("grob22", [form| a = c^2 ∧ b^3 = a^3 + d^2 ∧ (b - a) * e^2 + 1 = 0
>    ⊃ c^2 * b = -(a^2 + b^2 + (e * d)^2) |])

>   , ("grob23", [form| a = c^2 ∧ b^3 = a^3 + d^2 ∧ (b - a) * e^2 + 1 = 0
>    ⊃ c^6 * b^3 = -(a^2 + b^2 + (e * d)^2)^3 |])

>   , ("grob24", [form| a = c^2 ∧ b^3 = a^3 + d^2 ∧ (b - a) * e^2 + 1 = 0
>    ⊃ c^6 * (c^6 + d^2) + (a^2 + b^2 + (e * d)^2)^3 = 0 |])

(* ------------------------------------------------------------------------- *)
(* A simpler one is ~(x < y ∧ y < x), i.e. x < y ⊃ x <= y.                  *)
(*                                                                           *)
(* Yet even this isn't completed!                                            *)
(* ------------------------------------------------------------------------- *)

>   , ("grob25", [form| (y - x) * s^2 = 1 ∧ (x - y) * t^2 = 1 ⊃ s^2 + t^2 = 0 |])

(* ------------------------------------------------------------------------- *)
(* Inspired by Cardano's formula for a cubic. This actually works worse than *)
(* with naive quantifier elimination (of course it's false...)               *)
(* ------------------------------------------------------------------------- *)

>   , ("grob26", [form| t - u = n ∧ 27 * t * u = m^3 ∧
>    ct^3 = t ∧ cu^3 = u ∧
>    x = ct - cu
>    ⊃ x^3 + m * x = n |])

End

>   ]



