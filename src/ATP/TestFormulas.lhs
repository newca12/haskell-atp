
Example formulas for testing the algorithms.

* Signature

> module ATP.TestFormulas
>   ( lookup )

> where

> import Prelude hiding (lookup)
> import qualified Data.List as List
> import ATP.FormulaSyn

* Table

> lookup :: String -> Maybe Formula
> lookup = flip List.lookup formulas

> formulas :: [(String, Formula)]
> formulas = 
>   [ 

** Pellatier's problems

Propositional

>     ("p1", [$form| p ⊃ q ⇔ ¬ q ⊃ ¬ p |])
>   , ("p2", [$form| ¬ ¬ p ⇔ p |])
>   , ("p3", [$form| ¬ (p ⊃ q) ⊃ q ⊃ p |])
>   , ("p4", [$form| ¬ p ⊃ q ⇔ ¬ q ⊃ p |])
>   , ("p5", [$form| (p ∨ q ⊃ p ∨ r) ⊃ p ∨ (q ⊃ r) |])
>   , ("p6", [$form| p ∨ ¬ p |])
>   , ("p7", [$form| p ∨ ¬ ¬ ¬ p |])
>   , ("p8", [$form| ((p ⊃ q) ⊃ p) ⊃ p |])
>   , ("p9", [$form| (p ∨ q) ∧ (¬ p ∨ q) ∧ (p ∨ ¬ q) ⊃ ¬ (¬ q ∨ ¬ q) |])
>   , ("p10", [$form| (q ⊃ r) ∧ (r ⊃ p ∧ q) ∧ (p ⊃ q ∧ r) ⊃ (p ⇔ q) |])
>   , ("p11", [$form| p ⇔ p |])
>   , ("p12", [$form| ((p ⇔ q) ⇔ r) ⇔ (p ⇔ (q ⇔ r)) |])
>   , ("p13", [$form| p ∨ q ∧ r ⇔ (p ∨ q) ∧ (p ∨ r) |])
>   , ("p14", [$form| (p ⇔ q) ⇔ (q ∨ ¬ p) ∧ (¬ q ∨ p) |])
>   , ("p15", [$form| p ⊃ q ⇔ ¬ p ∨ q |])
>   , ("p16", [$form| (p ⊃ q) ∨ (q ⊃ p) |])
>   , ("p17", [$form| p ∧ (q ⊃ r) ⊃ s ⇔ (¬ p ∨ q ∨ s) ∧ (¬ p ∨ ¬ r ∨ s) |])

First order

>   , ("p18", [$form| ∃ y. ∀ x. P(y) ⊃ P(x) |])

>   , ("p19", [$form| ∃ x. ∀ y z. (P(y) ⊃ Q(z)) ⊃ P(x) ⊃ Q(x) |])

>   , ("p20", [$form| (∀ x y. ∃ z. ∀ w. P(x) ∧ Q(y) ⊃ R(z) ∧ U(w)) 
>                       ⊃ (∃ x y. P(x) ∧ Q(y)) ⊃ (∃ z. R(z)) |])

>   , ("p21", [$form| (∃ x. P ⊃ Q(x)) ∧ (∃ x. Q(x) ⊃ P) 
>                       ⊃ (∃ x. P ⇔ Q(x)) |])

>   , ("p22", [$form| (∀ x. P ⇔ Q(x)) ⊃ (P ⇔ (∀ x. Q(x))) |])

>   , ("p23", [$form| (∀ x. P ∨ Q(x)) ⇔ P ∨ (∀ x. Q(x)) |])

>   , ("p24", [$form|  ¬ (∃ x. U(x) ∧ Q(x)) ∧ 
>                    (∀ x. P(x) ⊃ Q(x) ∨ R(x)) ∧       
>                  ¬ (∃ x. P(x) ⊃ (∃ x. Q(x))) ∧   
>                    (∀ x. Q(x) ∧ R(x) ⊃ U(x))         
>                  ⊃ (∃ x. P(x) ∧ R(x)) |]) 

>   , ("p25", [$form| (∃ x. P(x)) ∧ 
>                  (∀ x. U(x) ⊃ ¬ G(x) ∧ R(x)) ∧ 
>                  (∀ x. P(x) ⊃ G(x) ∧ U(x)) ∧ 
>                  ((∀ x. P(x) ⊃ Q(x)) ∨ (∃ x. Q(x) ∧ P(x))) 
>                  ⊃ (∃ x. Q(x) ∧ P(x)) |]) 

>   , ("p26", [$form| ((∃ x. P(x)) ⇔ (∃ x. Q(x))) ∧ 
>                   (∀ x y. P(x) ∧ Q(y) ⊃ (R(x) ⇔ U(y))) 
>                   ⊃ ((∀ x. P(x) ⊃ R(x)) ⇔ (∀ x. Q(x) ⊃ U(x))) |])

>   , ("p27", [$form| (∃ x. P(x) ∧ ¬ Q(x)) ∧ 
>                   (∀ x. P(x) ⊃ R(x)) ∧ 
>                   (∀ x. U(x) ∧ V(x) ⊃ P(x)) ∧ 
>                   (∃ x. R(x) ∧ ¬ Q(x)) 
>                   ⊃ (∀ x. U(x) ⊃ ¬ R(x)) 
>                   ⊃ (∀ x. U(x) ⊃ ¬ V(x)) |])

>   , ("p28", [$form| (∀ x. P(x) ⊃ (∀ x. Q(x))) ∧ 
>                   ((∀ x. Q(x) ∨ R(x)) ⊃ (∃ x. Q(x) ∧ R(x))) ∧ 
>                   ((∃ x. R(x)) ⊃ (∀ x. L(x) ⊃ M(x))) ⊃ 
>                   (∀ x. P(x) ∧ L(x) ⊃ M(x)) |])

>   , ("p29", [$form| (∃ x. P(x)) ∧ (∃ x. G(x)) ⊃ 
>                   ((∀ x. P(x) ⊃ H(x)) ∧ (∀ x. G(x) ⊃ J(x)) ⇔ 
>                   (∀ x y. P(x) ∧ G(y) ⊃ H(x) ∧ J(y))) |])

>   , ("p30", [$form| (∀ x. P(x) ∨ G(x) ⊃ ¬ H(x)) ∧ 
>                   (∀ x. (G(x) ⊃ ¬ U(x)) ⊃ P(x) ∧ H(x)) 
>                   ⊃ (∀ x. U(x)) |])

>   , ("p31", [$form| ¬ (∃ x. P(x) ∧ (G(x) ∨ H(x))) ∧ 
>                   (∃ x. Q(x) ∧ P(x)) ∧ 
>                   (∀ x. ¬ H(x) ⊃ J(x)) 
>                   ⊃ (∃ x. Q(x) ∧ J(x)) |])

>   , ("p32", [$form| (∀ x. P(x) ∧ (G(x) ∨ H(x)) ⊃ Q(x)) ∧ 
>                   (∀ x. Q(x) ∧ H(x) ⊃ J(x)) ∧ 
>                   (∀ x. R(x) ⊃ H(x)) 
>                   ⊃ (∀ x. P(x) ∧ R(x) ⊃ J(x)) |])

>   , ("p33", [$form| (∀ x. P(a) ∧ (P(x) ⊃ P(b)) ⊃ P(c)) ⇔ 
>                   (∀ x. P(a) ⊃ P(x) ∨ P(c)) ∧ (P(a) ⊃ P(b) ⊃ P(c)) |])

>   , ("p34", [$form| ((∃ x. ∀ y. P(x) ⇔ P(y)) ⇔ 
>                      ((∃ x. Q(x)) ⇔ (∀ y. Q(y)))) ⇔ 
>                   ((∃ x. ∀ y. Q(x) ⇔ Q(y)) ⇔ 
>                   ((∃ x. P(x)) ⇔ (∀ y. P(y)))) |])

>   , ("p35", [$form| ∃ x y. P(x,y) ⊃ (∀ x y. P(x,y)) |])

>   , ("p36", [$form| (∀ x. ∃ y. P(x,y)) ∧ 
>                   (∀ x. ∃ y. G(x,y)) ∧ 
>                   (∀ x y. P(x,y) ∨ G(x,y) 
>                   ⊃ (∀ z. P(y,z) ∨ G(y,z) ⊃ H(x,z))) 
>                   ⊃ (∀ x. ∃ y. H(x,y)) |])

>   , ("p37", [$form| (∀ z. 
>                   ∃ w. ∀ x. ∃ y. (P(x,z) ⊃ P(y,w)) ∧ P(y,z) ∧ 
>                   (P(y,w) ⊃ (∃ u. Q(u,w)))) ∧ 
>                   (∀ x z. ¬ P(x,z) ⊃ (∃ y. Q(y,z))) ∧ 
>                   ((∃ x y. Q(x,y)) ⊃ (∀ x. R(x,x))) ⊃ 
>                   (∀ x. ∃ y. R(x,y)) |])

>   , ("p38", [$form| (∀ x. 
>                     P(a) ∧ (P(x) ⊃ (∃ y. P(y) ∧ R(x,y))) ⊃ 
>                   (∃ z w. P(z) ∧ R(x,w) ∧ R(w,z))) ⇔ 
>                   (∀ x. 
>                   (¬ P(a) ∨ P(x) ∨ (∃ z w. P(z) ∧ R(x,w) ∧ R(w,z))) ∧ 
>                     (¬ P(a) ∨ ¬ (∃ y. P(y) ∧ R(x,y)) ∨ 
>                   (∃ z w. P(z) ∧ R(x,w) ∧ R(w,z)))) |])

>   , ("p39", [$form| ¬ (∃ x. ∀ y. P(y,x) ⇔ ¬ P(y,y)) |])

>   , ("p40", [$form| (∃ y. ∀ x. P(x,y) ⇔ P(x,x)) 
>                   ⊃ ¬ (∀ x. ∃ y. ∀ z. P(z,y) ⇔ ¬ P(z,x)) |])

>   , ("p41", [$form| (∀ z. ∃ y. ∀ x. P(x,y) ⇔ P(x,z) ∧ ¬ P(x,x)) 
>                   ⊃ ¬ (∃ z. ∀ x. P(x,z)) |])

>   , ("p42", [$form| ¬ (∃ y. ∀ x. P(x,y) ⇔ ¬ (∃ z. P(x,z) ∧ P(z,x))) |])

>   , ("p43", [$form| (∀ x y. Q(x,y) ⇔ ∀ z. P(z,x) ⇔ P(z,y)) 
>                     ⊃ ∀ x y. Q(x,y) ⇔ Q(y,x) |])

>   , ("p44", [$form| (∀ x. P(x) ⊃ (∃ y. G(y) ∧ H(x,y)) ∧ 
>                   (∃ y. G(y) ∧ ¬ H(x,y))) ∧ 
>                   (∃ x. J(x) ∧ (∀ y. G(y) ⊃ H(x,y))) 
>                   ⊃ (∃ x. J(x) ∧ ¬ P(x)) |])

>   , ("p45", [$form|  (∀ x. P(x) ∧ (∀ y. G(y) ∧ H(x,y) ⊃ J(x,y))  
>                       ⊃ (∀ y. G(y) ∧ H(x,y) ⊃ R(y))) ∧           
>                    ¬ (∃ y. L(y) ∧ R(y)) ∧                             
>                       (∃ x. P(x) ∧ (∀ y. H(x,y) ⊃ L(y)) ∧     
>                     (∀ y. G(y) ∧ H(x,y) ⊃ J(x,y)))                  
>                     ⊃ (∃ x. P(x) ∧ ¬ (∃ y. G(y) ∧ H(x,y))) |])

>   , ("p46", [$form| (∀ x. P(x) ∧ (∀ y. P(y) ∧ H(y,x) ⊃ G(y)) ⊃ G(x)) ∧ 
>                   ((∃ x. P(x) ∧ ¬ G(x)) ⊃ 
>                   (∃ x. P(x) ∧ ¬ G(x) ∧ 
>                   (∀ y. P(y) ∧ ¬ G(y) ⊃ J(x,y)))) ∧ 
>                   (∀ x y. P(x) ∧ P(y) ∧ H(x,y) ⊃ ¬ J(y,x)) ⊃ 
>                   (∀ x. P(x) ⊃ G(x)) |])

>   , ("p55", [$form| lives(agatha) ∧ lives(butler) ∧ lives(charles) ∧ 
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

>   , ("p57", [$form| P(f((a),b),f(b,c)) ∧ 
>                   P(f(b,c),f(a,c)) ∧ 
>                   (∀ x y z. P(x,y) ∧ P(y,z) ⊃ P(x,z)) 
>                   ⊃ P(f(a,b),f(a,c)) |])
>   , ("p58", [$form| ∀ P Q R. ∀ x. ∃ v. ∃ w. ∀ y. ∀ z. 
>                   ((P(x) ∧ Q(y)) ⊃ ((P(v) ∨ R(w))  ∧ (R(z) ⊃ Q(v)))) |])
>   , ("p59", [$form| (∀ x. P(x) ⇔ ¬ P(f(x))) ⊃ (∃ x. P(x) ∧ ¬ P(f(x))) |])
>   , ("p60", [$form| ∀ x. P(x,f(x)) ⇔ 
>                         ∃ y. (∀ z. P(z,y) ⊃ P(z,f(x))) ∧ P(x,y) |])

Gilmore

>   , ("gilmore_1", [$form| ∃ x. ∀ y z.
>                          ((F(y) ⊃ G(y)) ⇔ F(x)) ∧ 
>                          ((F(y) ⊃ H(y)) ⇔ G(x)) ∧ 
>                          (((F(y) ⊃ G(y)) ⊃ H(y)) ⇔ H(x)) 
>                         ⊃ F(z) ∧ G(z) ∧ H(z) |])

>   , ("gilmore_2", [$form| ∃ x y. ∀ z. 
>                        (F(x,z) ⇔ F(z,y)) ∧ (F(z,y) ⇔ F(z,z)) ∧ (F(x,y) ⇔ F(y,x)) 
>                        ⊃ (F(x,y) ⇔ F(x,z)) |])

>   , ("gilmore_3", [$form| ∃ x. ∀ y z. 
>                         ((F(y,z) ⊃ (G(y) ⊃ H(x))) ⊃ F(x,x)) ∧ 
>                         ((F(z,x) ⊃ G(x)) ⊃ H(z)) ∧ 
>                         F(x,y) 
>                         ⊃ F(z,z) |])

>   , ("gilmore_4", [$form| ∃ x y. ∀ z. 
>                         (F(x,y) ⊃ F(y,z) ∧ F(z,z)) ∧ 
>                         (F(x,y) ∧ G(x,y) ⊃ G(x,z) ∧ G(z,z)) |])

>   , ("gilmore_5", [$form| (∀ x. ∃ y. F(x,y) ∨ F(y,x)) ∧ 
>                           (∀ x y. F(y,x) ⊃ F(y,y)) 
>                         ⊃ ∃ z. F(z,z) |])

>   , ("gilmore_6", [$form| ∀ x. ∃ y. 
>                         (∃ u. ∀ v. F(u,x) ⊃ G(v,u) ∧ G(u,x)) 
>                         ⊃ (∃ u. ∀ v. F(u,y) ⊃ G(v,u) ∧ G(u,y)) ∨ 
>                         (∀ u v. ∃ w. G(v,u) ∨ H(w,y,u) ⊃ G(u,w)) |])

>   , ("gilmore_7", [$form| (∀ x. K(x) ⊃ ∃ y. L(y) ∧ (F(x,y) ⊃ G(x,y))) ∧ 
>                         (∃ z. K(z) ∧ ∀ u. L(u) ⊃ F(z,u)) 
>                         ⊃ ∃ v w. K(v) ∧ L(w) ∧ G(v,w) |])

>   , ("gilmore_8", [$form| ∃ x. ∀ y z. 
>                         ((F(y,z) ⊃ (G(y) ⊃ (∀ u. ∃ v. H(u,v,x)))) ⊃ F(x,x)) ∧ 
>                         ((F(z,x) ⊃ G(x)) ⊃ (∀ u. ∃ v. H(u,v,z))) ∧ 
>                         F(x,y) 
>                         ⊃ F(z,z) |])

>   , ("gilmore_9", [$form| ∀ x. ∃ y. ∀ z. 
>                         ((∀ u. ∃ v. F(y,u,v) ∧ G(y,u) ∧ ¬ H(y,x)) 
>                         ⊃ (∀ u. ∃ v. F(x,u,v) ∧ G(z,u) ∧ ¬ H(x,z)) 
>                         ⊃ (∀ u. ∃ v. F(x,u,v) ∧ G(y,u) ∧ ¬ H(x,y))) ∧ 
>                         ((∀ u. ∃ v. F(x,u,v) ∧ G(y,u) ∧ ¬ H(x,y)) 
>                         ⊃ ¬ (∀ u. ∃ v. F(x,u,v) ∧ G(z,u) ∧ ¬ H(x,z)) 
>                         ⊃ (∀ u. ∃ v. F(y,u,v) ∧ G(y,u) ∧ ¬ H(y,x)) ∧ 
>                         (∀ u. ∃ v. F(z,u,v) ∧ G(y,u) ∧ ¬ H(z,y))) |])

Misc

>   , ("davis_putnam_example", [$form| ∃ x. ∃ y. ∀ z. 
>                                    (F(x,y) ⊃ (F(y,z) ∧ F(z,z))) ∧ 
>                                    ((F(x,y) ∧ G(x,y)) ⊃ (G(x,z) ∧ G(z,z))) |])

>   , ("los", [$form| (∀ x y z. P(x,y) ∧ P(y,z) ⊃ P(x,z)) ∧ 
>                   (∀ x y z. Q(x,y) ∧ Q(y,z) ⊃ Q(x,z)) ∧ 
>                   (∀ x y. Q(x,y) ⊃ Q(y,x)) ∧ 
>                   (∀ x y. P(x,y) ∨ Q(x,y)) 
>                   ⊃ (∀ x y. P(x,y)) ∨ (∀ x y. Q(x,y)) |])

>   , ("steamroller", [$form| ((∀ x. P1(x) ⊃ P0(x)) ∧ (∃ x. P1(x))) ∧ 
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

>   , ("wishnu", [$form| (∃ x. x = f(g(x)) ∧ ∀ x'. x' = f(g(x')) ⊃ x = x') ⇔ 
>            (∃ y. y = g(f(y)) ∧ ∀ y'. y' = g(f(y')) ⊃ y = y') |])

>   , ("eq1", [$form| (∀ x y z. x * (y * z) = (x * y) * z) ∧ 
>                   (∀ x. 1 * x = x) ∧ 
>                   (∀ x. i(x) * x = 1) 
>                   ⊃ ∀ x. x * i(x) = 1 |])

>   , ("eq2", [$form| (∀ x y z. x * (y * z) = (x * y) * z) ∧ 
>                   (∀ x. 1 * x = x) ∧ 
>                   (∀ x. x * 1 = x) ∧ 
>                   (∀ x. x * x = 1) 
>                   ⊃ ∀ x y. x * y  = y * x |])


>   , ("eq3", [$form| (∀ x. x = x) ∧ 
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


>   , ("eq4", [$form| (∀ x y z. axiom(x * (y * z),(x * y) * z)) ∧ 
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

>   , ("eq5", [$form| (∀ x y z. axiom(x * (y * z),(x * y) * z)) ∧ 
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

>   , ("eq6", [$form| axiom(f(f(f(f(f(c))))),c) ∧ 
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

>   , ("eq7", [$form| (∀ x y z. eqA (x * (y * z),(x * y) * z)) ∧ 
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

>   , ("eq8", [$form| (∀ x y z. eqA (x * (y * z),(x * y) * z)) ∧ 
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

>   , ("eq9", [$form| (∀ x y z. eq1(x * (y * z),(x * y) * z)) ∧ 
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

>   , ("eq10", [$form| f(f(f(f(f(c))))) = c ∧ f(f(f(c))) = c 
>                    ⊃ f(c) = c ∨ f(g(c)) = g(f(c)) |])

>   , ("eq11", [$form| ∀ c. f(f(f(f(f(c))))) = c ∧ f(f(f(c))) = c ⊃ f(c) = c |])

eqelim.ml

>   , ("eq12", [$form| (∀ x. R(x,x)) ∧ 
>                    (∀ x y. R(x,y) ⊃  R(y,x)) ∧ 
>                    (∀ x y z. R(x,y) ∧ R(y,z) ⊃ R(x,z)) 
>                    ⇔ (∀ x y. R(x,y) ⇔ (∀ z. R(x,z) ⇔ R(y,z))) |]) 

>   , ("abel", [$form| (∀ x. P(1,x,x)) ∧ 
>          (∀ x. P(x,x,1)) ∧ 
>          (∀ u v w x y z. P(x,y,u) ∧ P(y,z,w) 
>                              ⊃ (P(x,w,v) ⇔ P(u,z,v))) 
>            ⊃ ∀ a b c. P(a,b,c) ⊃ P(b,a,c) |])

>   , ("abel_false", [$form| (∀ x. P(x,x,1)) ∧
>                              (∀ u v w x y z.
>                                 P(x,y,u) ∧ P(y,z,w) ⊃ (P(x,w,v) ⇔ P(u,z,v)))
>                              ⊃ ∀ a b c. P(a,b,c) ⊃ P(b,a,c) |])

>   , ("ewd1062", [$form| (∀ x. x ≤ x) ∧ 
>                       (∀ x y z. x ≤ y ∧ y ≤ z ⊃ x ≤ z) ∧ 
>                        (∀ x y. f(x) ≤ y ⇔ x ≤ g(y)) 
>                       ⊃ (∀ x y. x ≤ y ⊃ f(x) ≤ f(y)) ∧ 
>                       (∀ x y. x ≤ y ⊃ g(x) ≤ g(y)) |])

paramodulation.ml 

>   , ("para1", [$form| (∀ x. f(f(x)) = f(x)) ∧ (∀ x. ∃ y. f(y) = x)
>    ⊃ ∀ x. f(x) = x |])
>     -- Groups

>   , ("group1", [$form| (∀ x y z. x * (y * z) = (x * y) * z) ∧
>    (∀ x. e * x = x) ∧
>    (∀ x. i(x) * x = e)
>    ⊃ ∀ x. x * e = x |])

>   , ("group2", [$form| (∀ x y z. x * (y * z) = (x * y) * z) ∧
>    (∀ x. e * x = x) ∧
>    (∀ x. i(x) * x = e)
>    ⊃ ∀ x. x * i(x) = e |])

DLO

>   , ("dlo1", [$form| ∀ x y. ∃ z. z < x ∧ z < y |])
>   , ("dlo2", [$form| ∃ z. z < x ∧ z < y |])
>   , ("dlo3", [$form| ∃ z. x < z ∧ z < y |])
>   , ("dlo4", [$form| (∀ x. x < a ⊃ x < b) |])
>   , ("dlo5", [$form| ∀ a b. (∀ x. x < a ⊃ x < b) ⇔ a ≤ b |])
>   , ("dlo6", [$form| ∀ a b. (∀ x. x < a ⇔ x < b) ⇔ a = b |])
>   , ("dlo7", [$form| ∃ x y z. ∀ u.
>                  x < x ∨ ¬ x < u ∨ (x < y ∧ y < z ∧ ¬ x < z) |])
>   , ("dlo8", [$form| ∀ x. ∃ y. x < y |])
>   , ("dlo9", [$form| ∀ x y z. x < y ∧ y < z ⊃ x < z |])
>   , ("dlo10", [$form| ∀ x y. x < y ∨ (x = y) ∨ y < x |])
>   , ("dlo11", [$form| ∃ x y. x < y ∧ y < x |])
>   , ("dlo12", [$form| ∀ x y. ∃ z. z < x ∧ x < y |])
>   , ("dlo13", [$form| ∃ z. z < x ∧ x < y |])
>   , ("dlo14", [$form| ∀ x y. ∃ z. z < x ∧ z < y |])
>   , ("dlo15", [$form| ∀ x y. x < y ⊃ ∃ z. x < z ∧ z < y |])
>   , ("dlo16", [$form| ∀ x y. ¬ (x = y) ⊃ ∃ u. u < x ∧ (y < u ∨ x < y) |])
>   , ("dlo17", [$form| ∃ x. x = x |])
>   , ("dlo18", [$form| ∃ x. x = x ∧ x = y |])
>   , ("dlo19", [$form| ∃ z. x < z ∧ z < y |])
>   , ("dlo20", [$form| ∃ z. x ≤ z ∧ z ≤ y |])
>   , ("dlo21", [$form| ∃ z. x < z ∧ z ≤ y |])
>   , ("dlo22", [$form| ∀ x y z. ∃ u. u < x ∧ u < y ∧ u < z |])
>   , ("dlo23", [$form| ∀ y. x < y ∧ y < z ⊃ w < z |])
>   , ("dlo24", [$form| ∀ x y. x < y |])
>   , ("dlo25", [$form| ∃ z. z < x ∧ x < y |])
>   , ("dlo26", [$form| ∀ a b. (∀ x. x < a ⊃ x < b) ⇔ a ≤ b |])
>   , ("dlo27", [$form| ∀ x. x < a ⊃ x < b |])
>   , ("dlo28", [$form| ∀ x. x < a ⊃ x ≤ b |])
>   , ("dlo29", [$form| ∀ a b. ∃ x. ¬ (x = a) ∨ ¬ (x = b) ∨ (a = b) |])
>   , ("dlo30", [$form| ∀ x y. x ≤ y ∨ x > y |])

** Presburger

>   , ("pres0", [$form| ∀ x y. ¬ (2 * x + 1 = 2 * y) |])
>   , ("pres1", [$form| ∀ x. ∃ y. 2 * y ≤ x ∧ x < 2 * (y + 1) |])
>   , ("pres2", [$form| ∃ x y. 4 * x - 6 * y = 1 |])
>   , ("pres3", [$form| ∀ x. ¬ divides(2,x) ∧ divides(3,x-1) ⇔
>                           divides(12,x-1) ∨ divides(12,x-7) |])
>   , ("pres4", [$form| ∀ x. b < x ⊃ a ≤ x |])
>   , ("pres5", [$form| ∃ x y. x > 0 ∧ y ≥ 0 ∧ 3 * x - 5 * y = 1 |])
>   , ("pres6", [$form| ∃ x y z. 4 * x - 6 * y = 1 |])
>   , ("pres7", [$form| ∀ x. a < 3 * x ⊃ b < 3 * x |])
>   , ("pres8", [$form| ∀ x y. x ≤ y ⊃ 2 * x + 1 < 2 * y |])
>   , ("pres9", [$form| (∃ d. y = 65 * d) ⊃ (∃ d. y = 5 * d) |])
>   , ("pres10", [$form| ∀ y. (∃ d. y = 65 * d) ⊃ (∃ d. y = 5 * d) |])
>   , ("pres11", [$form| ∀ x y. ¬ (2 * x + 1 = 2 * y) |])
>   , ("pres12", [$form| ∀ x y z. (2 * x + 1 = 2 * y) ⊃ x + y + z > 129 |])
>   , ("pres13", [$form| ∀ x. a < x ⊃ b < x |])
>   , ("pres14", [$form| ∀ x. a ≤ x ⊃ b < x |])

Formula examples from Cooper's paper. 

>   , ("pres15", [$form| ∀ a b. ∃ x. a < 20 * x ∧ 20 * x < b |])
>   , ("pres16", [$form| ∃ x. a < 20 * x ∧ 20 * x < b |])
>   , ("pres17", [$form| ∀ b. ∃ x. a < 20 * x ∧ 20 * x < b |])
>   , ("pres18", [$form| ∀ a. ∃ b. a < 4 * b + 3 * a ∨ (¬ (a < b) ∧ a > b + 1) |])
>   , ("pres19", [$form| ∃ y. ∀ x. x + 5 * y > 1 ∧ 13 * x - y > 1 ∧ x + 2 < 0 |])

More of my own.                                                           

>   , ("pres20", [$form| ∀ x y. x ≥ 0 ∧ y ≥ 0
>                   ⊃ 12 * x - 8 * y < 0 ∨ 12 * x - 8 * y > 2 |])
>   , ("pres21", [$form| ∃ x y. 5 * x + 3 * y = 1 |])
>   , ("pres22", [$form| ∃ x y. 5 * x + 10 * y = 1 |])
>   , ("pres23", [$form| ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 5 * x - 6 * y = 1 |])
>   , ("pres24", [$form| ∃ w x y z. 2 * w + 3 * x + 4 * y + 5 * z = 1 |])
>   , ("pres25", [$form| ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 5 * x - 3 * y = 1 |])
>   , ("pres26", [$form| ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x - 5 * y = 1 |])
>   , ("pres27", [$form| ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 6 * x - 3 * y = 1 |])
>   , ("pres28", [$form| ∀ x y. ¬ (x = 0) ⊃ 5 * y < 6 * x ∨ 5 * y > 6 * x |])
>   , ("pres29", [$form| ∀ x y. ¬ divides(5,x) ∧ ¬ divides(6,y) ⊃ ¬ (6 * x = 5 * y) |])
>   , ("pres30", [$form| ∀ x y. ¬ divides(5,x) ⊃ ¬ (6 * x = 5 * y) |])
>   , ("pres31", [$form| ∀ x y. ¬ (6 * x = 5 * y) |])
>   , ("pres32", [$form| ∀ x y. 6 * x = 5 * y ⊃ ∃ d. y = 3 * d |])
>   , ("pres33", [$form| 6 * x = 5 * y ⊃ ∃ d. y = 3 * d |])

Positive variant of the Bezout theorem (see the exercise).                

>   , ("pres34", [$form| ∀ z. z > 7 ⊃ ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z |])
>   , ("pres35", [$form| ∀ z. z > 2 ⊃ ∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z |])
>   , ("pres36", [$form| ∀ z.
>         z ≤ 7
>         ⊃ ((∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z) ⇔
>              ¬ (∃ x y. x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = 7 - z)) |])

Basic result about congruences.                                           

>   , ("pres37", [$form| ∀ x. ¬ divides(2,x) ∧ divides(3,x-1) ⇔
>               divides(12,x-1) ∨ divides(12,x-7) |])
>   , ("pres38", [$form| ∀ x. ¬ (∃ m. x = 2 * m) ∧ (∃ m. x = 3 * m + 1) ⇔
>               (∃ m. x = 12 * m + 1) ∨ (∃ m. x = 12 * m + 7) |])

Something else.

>   , ("pres39", [$form| ∀ x.
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

>   , ("pres40", [$form| a + 2 = b ∧ v_3 = b - a + 1 ∧ v_2 = b - 2 ∧ v_1 = 3 ⊃ ⊥ |])

Inspired by the Collatz conjecture.                                       

>   , ("pres41", [$form| ∃ a b. ¬ (a = 1) ∧ ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧ (a = b) |])
>   , ("pres42", [$form| ∃ a b. a > 1 ∧ b > 1 ∧
>                ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧
>                (a = b) |])
>   , ("pres43", [$form| ∃ a b. a > 1 ∧ b > 1 ∧
>                ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧
>                ((2 * a = b) ∨ (2 * a = 3 * b + 1)) |])

Bob Constable's "stamp problem".

>   , ("pres45", [$form| ∀ x. x ≥ 8 ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 5 * v |])
>   , ("pres46", [$form| ∃ l.
>         ∀ x. x ≥ l
>                   ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 5 * v |])
>   , ("pres47", [$form| ∃ l.
>         ∀ x. x ≥ l
>                   ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 7 * v |])
>   , ("pres48", [$form| ∃ l.
>         ∀ x. x ≥ l
>                   ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 8 * v |])
>   , ("pres49", [$form| ∃ l.
>         ∀ x. x ≥ l
>                   ⊃ ∃ u v. u ≥ 0 ∧ v ≥ 0 ∧ x = 7 * u + 8 * v |])

Example from reciprocal mult: (2622 * x)>>16 = x/100 within a range.      

>   , ("pres50", [$form| ∀ x q1 q2 r1 r2.
>         x < 4699 ∧
>         2622 * x = 65536 * q1 + r1 ∧ 0 ≤ q1 ∧ 0 ≤ r1 ∧ r1 < 65536 ∧
>         x = 100 * q2 + r2 ∧ 0 ≤ q2 ∧ 0 ≤ r2 ∧ r2 < 100
>         ⊃ q1 = q2 |])
>   , ("pres51", [$form| ∀ x y.
>         (∃ d. x + y = 2 * d) ⇔
>         ((∃ d. x = 2 * d) ⇔ (∃ d. y = 2 * d)) |])

Landau trick! Is it too slow?

>   , ("pres52", [$form| ∀ n.
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
>   , ("pres53", [$form| ∀ d. ∃ x y. 3 * x + 5 * y = d |])
>   , ("pres54", [$form| ∀ d. ∃ x y. 3 * x + 5 * y = d |])
>   , ("pres55", [$form| ∀ d. d ≥ 8 ⊃ ∃ x y. 3 * x + 5 * y = d |])
>   , ("pres56", [$form| ∀ d. ∃ x y. 3 * x - 5 * y = d |])

** Nelson-Oppen

>   , ("nelop0", [$form| f(v - 1) - 1 = v + 1 ∧ f(u) + 1 = u - 1 ∧ u + 1 = v ⊃ ⊥ |])
>   , ("nelop1", [$form| y ≤ x ∧ y ≥ x + z ∧ z ≥ 0 ⊃ f(f(x) - f(y)) = f(z) |])
>   , ("nelop2", [$form| x = y ∧ y ≥ z ∧ z ≥ x ⊃ f(z) = f(x) |])
>   , ("nelop3", [$form| a ≤ b ∧ b ≤ f(a) ∧ f(a) ≤ 1
>   ⊃ a + b ≤ 1 ∨ b + f(b) ≤ 1 ∨ f(f(b)) ≤ f(a) |])

Failures of original Shostak procedure.                                   

>   , ("nelop4", [$form| f(v - 1) - 1 = v + 1 ∧ f(u) + 1 = u - 1 ∧ u + 1 = v ⊃ ⊥ |])

And this one is where the original procedure loops 

>   , ("nelop5", [$form| f(v) = v ∧ f(u) = u - 1 ∧ u = v ⊃ ⊥ |])

This is on p. 8 of Shostak's "Deciding combinations" paper 

>   , ("nelop6", [$form| z = f(x - y) ∧ x = z + y ∧ ¬ (-(y) = -(x - f(f(z)))) ⊃ ⊥ |])

This (ICS theories-1) fails without array operations 

>   , ("nelop7", [$form| a + 2 = b ⊃ f(read(update(A,a,3),b-2)) = f(b - a + 1) |])

can-001 from ICS examples site, with if-then-elses expanded manually 

>   , ("nelop8", [$form| (x = y ∧ z = 1 ⊃ f(f((x+z))) = f(f((1+y)))) |])

RJB example; lists plus uninterpreted functions 

>   , ("nelop9", [$form| hd(x) = hd(y) ∧ tl(x) = tl(y) ∧ ¬ (x = nil) ∧ ¬ (y = nil)
>    ⊃ f(x) = f(y) |])

Another one from the ICS paper 

>   , ("nelop10", [$form| ¬ (f(f(x) - f(y)) = f(z)) ∧ y ≤ x ∧ y ≥ x + z ∧ z ≥ 0 ⊃ ⊥ |])

Shostak's "A Practical Decision Procedure..."

No longer works since I didn't do predicates in congruence closure

>   , ("nelop11", [$form| x < f(y) + 1 ∧ f(y) ≤ x ⊃ (P(x,y) ⇔ P(f(y),y)) |])

Shostak's "Practical..." paper again, using extra clauses for MAX 

>   , ("nelop12", [$form| (x ≥ y ⊃ MAX(x,y) = x) ∧ (y ≥ x ⊃ MAX(x,y) = y)
>                           ⊃ x = y + 2 ⊃ MAX(x,y) = x |])

Shostak's "Practical..." paper again 

>   , ("nelop13", [$form| x ≤ g(x) ∧ x ≥ g(x) ⊃ x = g(g(g(g(x)))) |])

Easy example I invented 

>   , ("nelop14", [$form| x^2 =  1 ⊃ (f(x) = f(-(x)))  ⊃ (f(x) = f(1)) |])

Taken from Clark Barrett's CVC page 

>   , ("nelop15", [$form| 2 * f(x + y) = 3 * y ∧ 2 * x = y ⊃ f(f(x + y)) = 3 * x |])

My former running example in the text; seems too slow.
Anyway this also needs extra predicates in CC

>   , ("nelop16", [$form| x^2 = y^2 ∧ x < y ∧ z^2 = z ∧ x < x * z ∧ P(f(1 + z))
>                               ⊃ P(f(x + y) - f(0)) |])

An example where the "naive" procedure is slow but feasible

>   , ("nelop17", [$form| 4 * x = 2 * x + 2 * y ∧ x = f(2 * x - y) ∧
>                            f(2 * y - x) = 3 ∧ f(x) = 4 ⊃ ⊥ |])

>   ]
