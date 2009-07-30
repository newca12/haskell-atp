
> module TestFormulas where

> import Prelude 
> import FormulaSyn

-- -----------------------------------------------------------------------------
--  Propositional                                                               
-- -----------------------------------------------------------------------------

> p1 = [$fol| p ==> q <=> ~q ==> ~p |]

> p2 = [$fol| ~ ~p <=> p |]

> p3 = [$fol| ~(p ==> q) ==> q ==> p |]

> p4 = [$fol| ~p ==> q <=> ~q ==> p |]

> p5 = [$fol| (p \/ q ==> p \/ r) ==> p \/ (q ==> r) |]

> p6 = [$fol| p \/ ~p |]

> p7 = [$fol| p \/ ~ ~ ~p |]

> p8 = [$fol| ((p ==> q) ==> p) ==> p |]

> p9 = [$fol| (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q) |]

> p10 = [$fol| (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q) |]

> p11 = [$fol| p <=> p |]

> p12 = [$fol| ((p <=> q) <=> r) <=> (p <=> (q <=> r)) |]

> p13 = [$fol| p \/ q /\ r <=> (p \/ q) /\ (p \/ r) |]

> p14 = [$fol| (p <=> q) <=> (q \/ ~p) /\ (~q \/ p) |]

> p15 = [$fol| p ==> q <=> ~p \/ q |]

> p16 = [$fol| (p ==> q) \/ (q ==> p) |]

> p17 = [$fol| p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s) |]

-- -----------------------------------------------------------------------------
--  First order                                                                 
-- -----------------------------------------------------------------------------

> p18 = [$fol| exists y. forall x. P(y) ==> P(x) |]

> p19 = [$fol| exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x) |]

> p20 = [$fol| (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
>                     ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z)) |]

> p21 = [$fol| (exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) 
>                  ==> (exists x. P <=> Q(x)) |]

> p22 = [$fol| (forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x))) |]

> p23 = [$fol| (forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x)) |]

> p24 = [$fol|  ~(exists x. U(x) /\ Q(x)) /\ 
>                    (forall x. P(x) ==> Q(x) \/ R(x)) /\       
>                  ~(exists x. P(x) ==> (exists x. Q(x))) /\   
>                    (forall x. Q(x) /\ R(x) ==> U(x))         
>                  ==> (exists x. P(x) /\ R(x)) |] 

> p25 = [$fol| (exists x. P(x)) /\ 
>                  (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
>                  (forall x. P(x) ==> G(x) /\ U(x)) /\ 
>                  ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
>                  ==> (exists x. Q(x) /\ P(x)) |] 

> p26 = [$fol| ((exists x. P(x)) <=> (exists x. Q(x))) /\ 
>                   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) 
>                   ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x))) |]

> p27 = [$fol| (exists x. P(x) /\ ~Q(x)) /\ 
>                   (forall x. P(x) ==> R(x)) /\ 
>                   (forall x. U(x) /\ V(x) ==> P(x)) /\ 
>                   (exists x. R(x) /\ ~Q(x)) 
>                   ==> (forall x. U(x) ==> ~R(x)) 
>                   ==> (forall x. U(x) ==> ~V(x)) |]

> p28 = [$fol| (forall x. P(x) ==> (forall x. Q(x))) /\ 
>                   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\ 
>                   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> 
>                   (forall x. P(x) /\ L(x) ==> M(x)) |]

> p29 = [$fol| (exists x. P(x)) /\ (exists x. G(x)) ==> 
>                   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
>                   (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y))) |]

> p30 = [$fol| (forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
>                   (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
>                   ==> (forall x. U(x)) |]

> p31 = [$fol| ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
>                   (exists x. Q(x) /\ P(x)) /\ 
>                   (forall x. ~H(x) ==> J(x)) 
>                   ==> (exists x. Q(x) /\ J(x)) |]

> p32 = [$fol| (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
>                   (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
>                   (forall x. R(x) ==> H(x)) 
>                   ==> (forall x. P(x) /\ R(x) ==> J(x)) |]

> p33 = [$fol| (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
>                   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c)) |]

> p34 = [$fol| ((exists x. forall y. P(x) <=> P(y)) <=> 
>                      ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> 
>                   ((exists x. forall y. Q(x) <=> Q(y)) <=> 
>                   ((exists x. P(x)) <=> (forall y. P(y)))) |]

> p35 = [$fol| exists x y. P(x,y) ==> (forall x y. P(x,y)) |]

> p36 = [$fol| (forall x. exists y. P(x,y)) /\ 
>                   (forall x. exists y. G(x,y)) /\ 
>                   (forall x y. P(x,y) \/ G(x,y) 
>                   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
>                   ==> (forall x. exists y. H(x,y)) |]

> p37 = [$fol| (forall z. 
>                   exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
>                   (P(y,w) ==> (exists u. Q(u,w)))) /\ 
>                   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
>                   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
>                   (forall x. exists y. R(x,y)) |]

> p38 = [$fol| (forall x. 
>                     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
>                   (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
>                   (forall x. 
>                   (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
>                     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
>                   (exists z w. P(z) /\ R(x,w) /\ R(w,z)))) |]

> p39 = [$fol| ~(exists x. forall y. P(y,x) <=> ~P(y,y)) |]

> p40 = [$fol| (exists y. forall x. P(x,y) <=> P(x,x)) 
>                   ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x)) |]

> p41 = [$fol| (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
>                   ==> ~(exists z. forall x. P(x,z)) |]

> p42 = [$fol| ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x))) |]

> p43 = [$fol| (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
>                     ==> forall x y. Q(x,y) <=> Q(y,x) |]

> p44 = [$fol| (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
>                   (exists y. G(y) /\ ~H(x,y))) /\ 
>                   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) 
>                   ==> (exists x. J(x) /\ ~P(x)) |]

> p45 = [$fol|  (forall x. P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))  
>                       ==> (forall y. G(y) /\ H(x,y) ==> R(y))) /\           
>                    ~(exists y. L(y) /\ R(y)) /\                             
>                       (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) /\     
>                     (forall y. G(y) /\ H(x,y) ==> J(x,y)))                  
>                     ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y))) |]

> p46 = [$fol| (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
>                   ((exists x. P(x) /\ ~G(x)) ==> 
>                   (exists x. P(x) /\ ~G(x) /\ 
>                   (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
>                   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
>                   (forall x. P(x) ==> G(x)) |]

> p55 = [$fol| lives(agatha) /\ lives(butler) /\ lives(charles) /\ 
>                   (killed(agatha,agatha) \/ killed(butler,agatha) \/ 
>                   killed(charles,agatha)) /\ 
>                   (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\ 
>                   (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\ 
>                   (hates(agatha,agatha) /\ hates(agatha,charles)) /\ 
>                   (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\ 
>                   (forall x. hates(agatha,x) ==> hates(butler,x)) /\ 
>                   (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles)) 
>                   ==> killed(agatha,agatha) /\ 
>                   ~killed(butler,agatha) /\ 
>                   ~killed(charles,agatha) |]

> p57 = [$fol| P(f((a),b),f(b,c)) /\ 
>                   P(f(b,c),f(a,c)) /\ 
>                   (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
>                   ==> P(f(a,b),f(a,c)) |]

> p58 = [$fol| forall P Q R. forall x. exists v. exists w. forall y. forall z. 
>                   ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v)))) |]

> p59 = [$fol| (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x))) |]

> p60 = [$fol| forall x. P(x,f(x)) <=> 
>                         exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y) |]

Gilmore

> gilmore_1 = [$fol| exists x. forall y z.
>                          ((F(y) ==> G(y)) <=> F(x)) /\ 
>                          ((F(y) ==> H(y)) <=> G(x)) /\ 
>                          (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
>                         ==> F(z) /\ G(z) /\ H(z) |]

> gilmore_2 = [$fol| exists x y. forall z. 
>                        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
>                        ==> (F(x,y) <=> F(x,z)) |]

> gilmore_3 = [$fol| exists x. forall y z. 
>                         ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
>                         ((F(z,x) ==> G(x)) ==> H(z)) /\ 
>                         F(x,y) 
>                         ==> F(z,z) |]

> gilmore_4 = [$fol| exists x y. forall z. 
>                         (F(x,y) ==> F(y,z) /\ F(z,z)) /\ 
>                         (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z)) |]

> gilmore_5 = [$fol| (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
>                           (forall x y. F(y,x) ==> F(y,y)) 
>                         ==> exists z. F(z,z) |]

> gilmore_6 = [$fol| forall x. exists y. 
>                         (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) 
>                         ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ 
>                         (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w)) |]

> gilmore_7 = [$fol| (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\ 
>                         (exists z. K(z) /\ forall u. L(u) ==> F(z,u)) 
>                         ==> exists v w. K(v) /\ L(w) /\ G(v,w) |]

> gilmore_8 = [$fol| exists x. forall y z. 
>                         ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\ 
>                         ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ 
>                         F(x,y) 
>                         ==> F(z,z) |]

> gilmore_9 = [$fol| forall x. exists y. forall z. 
>                         ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
>                         ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
>                         ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
>                         ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
>                         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
>                         ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
>                         (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y))) |]

Misc

> davis_putnam_example = [$fol| exists x. exists y. forall z. 
>                                    (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
>                                    ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z))) |]

> los = [$fol| (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\ 
>                   (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\ 
>                   (forall x y. Q(x,y) ==> Q(y,x)) /\ 
>                   (forall x y. P(x,y) \/ Q(x,y)) 
>                   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y)) |]

> steamroller = [$fol| ((forall x. P1(x) ==> P0(x)) /\ (exists x. P1(x))) /\ 
>                          ((forall x. P2(x) ==> P0(x)) /\ (exists x. P2(x))) /\ 
>                          ((forall x. P3(x) ==> P0(x)) /\ (exists x. P3(x))) /\ 
>                          ((forall x. P4(x) ==> P0(x)) /\ (exists x. P4(x))) /\ 
>                          ((forall x. P5(x) ==> P0(x)) /\ (exists x. P5(x))) /\ 
>                          ((exists x. Q1(x)) /\ (forall x. Q1(x) ==> Q0(x))) /\ 
>                          (forall x. P0(x) 
>                              ==> (forall y. Q0(y) ==> R(x,y)) \/ 
>                                   ((forall y. P0(y) /\ S0(y,x) /\ 
>                                       (exists z. Q0(z) /\ R(y,z)) 
>                                          ==> R(x,y)))) /\ 
>                          (forall x y. P3(y) /\ (P5(x) \/ P4(x)) ==> S0(x,y)) /\ 
>                          (forall x y. P3(x) /\ P2(y) ==> S0(x,y)) /\ 
>                          (forall x y. P2(x) /\ P1(y) ==> S0(x,y)) /\ 
>                          (forall x y. P1(x) /\ (P2(y) \/ Q1(y)) ==> ~(R(x,y))) /\ 
>                          (forall x y. P3(x) /\ P4(y) ==> R(x,y)) /\ 
>                          (forall x y. P3(x) /\ P5(y) ==> ~(R(x,y))) /\ 
>                          (forall x. (P4(x) \/ P5(x)) ==> exists y. Q0(y) /\ R(x,y)) 
>                          ==> exists x y. P0(x) /\ P0(y) /\ 
>                                  exists z. Q1(z) /\ R(y,z) /\ R(x,y) |]

> wishnu = [$fol| (exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=> 
>            (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y') |]

> eq1 = [$fol| (forall x y z. x * (y * z) = (x * y) * z) /\ 
>                   (forall x. 1 * x = x) /\ 
>                   (forall x. i(x) * x = 1) 
>                   ==> forall x. x * i(x) = 1 |]

> eq2 = [$fol| (forall x y z. x * (y * z) = (x * y) * z) /\ 
>                   (forall x. 1 * x = x) /\ 
>                   (forall x. x * 1 = x) /\ 
>                   (forall x. x * x = 1) 
>                   ==> forall x y. x * y  = y * x |]

-- > eq3 = [$fol| (forall x. x = x) /\ 
-- >                   (forall x y z. x * (y * z) = (x * y) * z) /\ 
-- >                   (forall x y z. (x * y) * z = x * (y * z)) /\ 
-- >                   (forall x. 1 * x = x) /\ 
-- >                   (forall x. x = 1 * x) /\ 
-- >                   (forall x. i(x) * x = 1) /\ 
-- >                   (forall x. 1 = i(x) * x) /\ 
-- >                   (forall x y. x = y ==> i(x) = i(y)) /\ 
-- >                   (forall x y z. x = y ==> x * z = y * z) /\ 
-- >                   (forall x y z. x = y ==> z * x = z * y) /\ 
-- >                   (forall x y z. x = y /\ y = z ==> x = z)
-- >                   ==> forall x. x * i(x) = 1 |]

> eq4 = [$fol| (forall x y z. axiom(x * (y * z),(x * y) * z)) /\ 
>                   (forall x y z. axiom((x * y) * z,x * (y * z)) /\ 
>                   (forall x. axiom(1 * x,x)) /\ 
>                   (forall x. axiom(x,1 * x)) /\ 
>                   (forall x. axiom(i(x) * x,1)) /\ 
>                   (forall x. axiom(1,i(x) * x)) /\ 
>                   (forall x x'. x = x' ==> cchain(i(x),i(x'))) /\ 
>                   (forall x x' y y'. x = x' /\ y = y' ==> cchain(x * y,x' * y'))) /\ 
>                   (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
>                   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
>                   (forall x x' u. x = x' /\ achain(i(x'),u) ==> cchain(i(x),u)) /\ 
>                   (forall x x' y y' u. 
>                   x = x' /\ y = y' /\ achain(x' * y',u) ==> cchain(x * y,u)) /\ 
>                   (forall s t. cchain(s,t) ==> s = t) /\ 
>                   (forall s t. achain(s,t) ==> s = t) /\ 
>                   (forall t. t = t) 
>                   ==> forall x. x * i(x) = 1 |]

> eq5 = [$fol| (forall x y z. axiom(x * (y * z),(x * y) * z)) /\ 
>                   (forall x y z. axiom((x * y) * z,x * (y * z)) /\ 
>                   (forall x. axiom(1 * x,x)) /\ 
>                   (forall x. axiom(x,1 * x)) /\ 
>                   (forall x. axiom(i(x) * x,1)) /\ 
>                   (forall x. axiom(1,i(x) * x)) /\ 
>                   (forall x x'. x = x' ==> cong(i(x),i(x'))) /\ 
>                   (forall x x' y y'. x = x' /\ y = y' ==> cong(x * y,x' * y'))) /\ 
>                   (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
>                   (forall s t. cong(s,t) ==> cchain(s,t)) /\ 
>                   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
>                   (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\ 
>                   (forall s t. cchain(s,t) ==> s = t) /\ 
>                   (forall s t. achain(s,t) ==> s = t) /\ 
>                   (forall t. t = t) 
>                   ==> forall x. x * i(x) = 1 |] 

> eq6 = [$fol| axiom(f(f(f(f(f(c))))),c) /\ 
>                   axiom(c,f(f(f(f(f(c)))))) /\ 
>                   axiom(f(f(f(c))),c) /\ 
>                   axiom(c,f(f(f(c)))) /\ 
>                   (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
>                   (forall s t. cong(s,t) ==> cchain(s,t)) /\ 
>                   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
>                   (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\ 
>                   (forall s t. cchain(s,t) ==> s = t) /\ 
>                   (forall s t. achain(s,t) ==> s = t) /\ 
>                   (forall t. t = t) /\ 
>                   (forall x y. x = y ==> cong(f(x),f(y))) 
>                   ==> f(c) = c |]

> eq7 = [$fol| (forall x y z. eqA (x * (y * z),(x * y) * z)) /\ 
>                   (forall x y z. eqA ((x * y) * z)) /\ 
>                   (forall x. eqA (1 * x,x)) /\ 
>                   (forall x. eqA (x,1 * x)) /\ 
>                   (forall x. eqA (i(x) * x,1)) /\ 
>                   (forall x. eqA (1,i(x) * x)) /\ 
>                   (forall x. eqA (x,x)) /\ 
>                   (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\ 
>                   (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\ 
>                   (forall x y. eqT (x,y) ==> eqC (i(x),i(y))) /\ 
>                   (forall w x y z. eqA (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\ 
>                   (forall w x y z. eqA (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\ 
>                   (forall w x y z. eqA (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\ 
>                   (forall w x y z. eqC (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\ 
>                   (forall w x y z. eqC (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\ 
>                   (forall w x y z. eqC (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\ 
>                   (forall w x y z. eqT (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\ 
>                   (forall w x y z. eqT (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\ 
>                   (forall w x y z. eqT (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\ 
>                   (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\ 
>                   (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\ 
>                   (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\ 
>                   (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\ 
>                   (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z)) 
>                   ==> forall x. eqT (x * i(x),1) |] 

> eq8 = [$fol| (forall x y z. eqA (x * (y * z),(x * y) * z)) /\ 
>                  (forall x y z. eqA ((x * y) * z)) /\ 
>                  (forall x. eqA (1 * x,x)) /\ 
>                  (forall x. eqA (x,1 * x)) /\ 
>                  (forall x. eqA (i(x) * x,1)) /\ 
>                  (forall x. eqA (1,i(x) * x)) /\ 
>                  (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\ 
>                  (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\ 
>                  (forall w x y. eqA (w,x) ==> eqC (w * y,x * y)) /\ 
>                  (forall w x y. eqC (w,x) ==> eqC (w * y,x * y)) /\ 
>                  (forall x y z. eqA (y,z) ==> eqC (x * y,x * z)) /\ 
>                  (forall x y z. eqC (y,z) ==> eqC (x * y,x * z)) /\ 
>                  (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\ 
>                  (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\ 
>                  (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\ 
>                  (forall x y z. eqC (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\ 
>                  (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\ 
>                  (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z)) 
>                  ==> forall x. eqT (x * i(x),1) \/ eqC (x * i(x),1) |] 

> eq9 = [$fol| (forall x y z. eq1(x * (y * z),(x * y) * z)) /\ 
>                   (forall x y z. eq1((x * y) * z,x * (y * z))) /\ 
>                   (forall x. eq1(1 * x,x)) /\ 
>                   (forall x. eq1(x,1 * x)) /\ 
>                   (forall x. eq1(i(x) * x,1)) /\ 
>                   (forall x. eq1(1,i(x) * x)) /\ 
>                   (forall x y z. eq1(x,y) ==> eq1(x * z,y * z)) /\ 
>                   (forall x y z. eq1(x,y) ==> eq1(z * x,z * y)) /\ 
>                   (forall x y z. eq1(x,y) /\ eq2(y,z) ==> eq2(x,z)) /\ 
>                   (forall x y. eq1(x,y) ==> eq2(x,y)) 
>                   ==> forall x. eq2(x,i(x)) |] 

> eq10 = [$fol| f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c 
>                    ==> f(c) = c \/ f(g(c)) = g(f(c)) |]

> eq11 = [$fol| forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c |]

% eqelim.ml

> eq12 = [$fol| (forall x. R(x,x)) /\ 
>                    (forall x y. R(x,y) ==>  R(y,x)) /\ 
>                    (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) 
>                    <=> (forall x y. R(x,y) <=> (forall z. R(x,z) <=> R(y,z))) |] 

% eqelim.ml

> abel = [$fol| (forall x. P(1,x,x)) /\ 
>          (forall x. P(x,x,1)) /\ 
>          (forall u v w x y z. P(x,y,u) /\ P(y,z,w) 
>                              ==> (P(x,w,v) <=> P(u,z,v))) 
>            ==> forall a b c. P(a,b,c) ==> P(b,a,c) |]

> abel_false = [$fol| (forall x. P(x,x,1)) /\
>    (forall u v w x y z.
>         P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
>    ==> forall a b c. P(a,b,c) ==> P(b,a,c) |]
> 

-- > ewd1062 = [$fol| (forall x. x <= x) /\ 
-- >                       (forall x y z. x <= y /\ y <= z ==> x <= z) /\ 
-- >                        (forall x y. f(x) <= y <=> x <= g(y)) 
-- >                       ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ 
-- >                       (forall x y. x <= y ==> g(x) <= g(y)) |]

paramodulation.ml 

> para1 = [$fol| (forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
>    ==> forall x. f(x) = x |]

Groups

> group1 = [$fol| (forall x y z. x * (y * z) = (x * y) * z) /\
>    (forall x. e * x = x) /\
>    (forall x. i(x) * x = e)
>    ==> forall x. x * e = x |]

> group2 = [$fol| (forall x y z. x * (y * z) = (x * y) * z) /\
>    (forall x. e * x = x) /\
>    (forall x. i(x) * x = e)
>    ==> forall x. x * i(x) = e |]

DLO

> dlo1 = [$fol| forall x y. exists z. z < x /\ z < y |]

> dlo2 = [$fol| exists z. z < x /\ z < y |]

> dlo3 = [$fol| exists z. x < z /\ z < y |]

> dlo4 = [$fol| (forall x. x < a ==> x < b) |]

> dlo5 = [$fol| forall a b. (forall x. x < a ==> x < b) <=> a <= b |]

> dlo6 = [$fol| forall a b. (forall x. x < a <=> x < b) <=> a = b |]

> dlo7 = [$fol| exists x y z. forall u.
>                  x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z) |]

> dlo8 = [$fol| forall x. exists y. x < y |]

> dlo9 = [$fol| forall x y z. x < y /\ y < z ==> x < z |]

> dlo10 = [$fol| forall x y. x < y \/ (x = y) \/ y < x |]

> dlo11 = [$fol| exists x y. x < y /\ y < x |]

> dlo12 = [$fol| forall x y. exists z. z < x /\ x < y |]

> dlo13 = [$fol| exists z. z < x /\ x < y |]

> dlo14 = [$fol| forall x y. exists z. z < x /\ z < y |]

> dlo15 = [$fol| forall x y. x < y ==> exists z. x < z /\ z < y |]

> dlo16 = [$fol| forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y) |]

> dlo17 = [$fol| exists x. x = x |]

> dlo18 = [$fol| exists x. x = x /\ x = y |]

> dlo19 = [$fol| exists z. x < z /\ z < y |]

> dlo20 = [$fol| exists z. x <= z /\ z <= y |]

> dlo21 = [$fol| exists z. x < z /\ z <= y |]

> dlo22 = [$fol| forall x y z. exists u. u < x /\ u < y /\ u < z |]

> dlo23 = [$fol| forall y. x < y /\ y < z ==> w < z |]

> dlo24 = [$fol| forall x y. x < y |]

> dlo25 = [$fol| exists z. z < x /\ x < y |]

> dlo26 = [$fol| forall a b. (forall x. x < a ==> x < b) <=> a <= b |]

> dlo27 = [$fol| forall x. x < a ==> x < b |]

> dlo28 = [$fol| forall x. x < a ==> x <= b |]

> dlo29 = [$fol| forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b) |]

> dlo30 = [$fol| forall x y. x <= y \/ x > y |]

Presburger

> pres0 = [$fol| forall x y. ~(2 * x + 1 = 2 * y) |]

> pres1 = [$fol| forall x. exists y. 2 * y <= x /\ x < 2 * (y + 1) |]

> pres2 = [$fol| exists x y. 4 * x - 6 * y = 1 |]

> pres3 = [$fol| forall x. ~divides(2,x) /\ divides(3,x-1) <=>
>                           divides(12,x-1) \/ divides(12,x-7) |]

> pres4 = [$fol| forall x. b < x ==> a <= x |]

> pres5 = [$fol| exists x y. x > 0 /\ y >= 0 /\ 3 * x - 5 * y = 1 |]

> pres6 = [$fol| exists x y z. 4 * x - 6 * y = 1 |]

> pres7 = [$fol| forall x. a < 3 * x ==> b < 3 * x |]

> pres8 = [$fol| forall x y. x <= y ==> 2 * x + 1 < 2 * y |]

> pres9 = [$fol| (exists d. y = 65 * d) ==> (exists d. y = 5 * d) |]

> pres10 = [$fol| forall y. (exists d. y = 65 * d) ==> (exists d. y = 5 * d) |]

> pres11 = [$fol| forall x y. ~(2 * x + 1 = 2 * y) |]

> pres12 = [$fol| forall x y z. (2 * x + 1 = 2 * y) ==> x + y + z > 129 |]

> pres13 = [$fol| forall x. a < x ==> b < x |]

> pres14 = [$fol| forall x. a <= x ==> b < x |]

Formula examples from Cooper's paper. 

> pres15 = [$fol| forall a b. exists x. a < 20 * x /\ 20 * x < b |]

> pres16 = [$fol| exists x. a < 20 * x /\ 20 * x < b |]

> pres17 = [$fol| forall b. exists x. a < 20 * x /\ 20 * x < b |]

> pres18 = [$fol| forall a. exists b. a < 4 * b + 3 * a \/ (~(a < b) /\ a > b + 1) |]

> pres19 = [$fol| exists y. forall x. x + 5 * y > 1 /\ 13 * x - y > 1 /\ x + 2 < 0 |]

More of my own.                                                           

> pres20 = [$fol| forall x y. x >= 0 /\ y >= 0
>                   ==> 12 * x - 8 * y < 0 \/ 12 * x - 8 * y > 2 |]

> pres21 = [$fol| exists x y. 5 * x + 3 * y = 1 |]

> pres22 = [$fol| exists x y. 5 * x + 10 * y = 1 |]

> pres23 = [$fol| exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 6 * y = 1 |]

> pres24 = [$fol| exists w x y z. 2 * w + 3 * x + 4 * y + 5 * z = 1 |]

> pres25 = [$fol| exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 3 * y = 1 |]

> pres26 = [$fol| exists x y. x >= 0 /\ y >= 0 /\ 3 * x - 5 * y = 1 |]

> pres27 = [$fol| exists x y. x >= 0 /\ y >= 0 /\ 6 * x - 3 * y = 1 |]

> pres28 = [$fol| forall x y. ~(x = 0) ==> 5 * y < 6 * x \/ 5 * y > 6 * x |]

> pres29 = [$fol| forall x y. ~divides(5,x) /\ ~divides(6,y) ==> ~(6 * x = 5 * y) |]

> pres30 = [$fol| forall x y. ~divides(5,x) ==> ~(6 * x = 5 * y) |]

> pres31 = [$fol| forall x y. ~(6 * x = 5 * y) |]

> pres32 = [$fol| forall x y. 6 * x = 5 * y ==> exists d. y = 3 * d |]

> pres33 = [$fol| 6 * x = 5 * y ==> exists d. y = 3 * d |]

Positive variant of the Bezout theorem (see the exercise).                

> pres34 = [$fol| forall z. z > 7 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z |]

> pres35 = [$fol| forall z. z > 2 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z |]

> pres36 = [$fol| forall z.
>         z <= 7
>         ==> ((exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z) <=>
>              ~(exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = 7 - z)) |]

Basic result about congruences.                                           

> pres37 = [$fol| forall x. ~divides(2,x) /\ divides(3,x-1) <=>
>               divides(12,x-1) \/ divides(12,x-7) |]

> pres38 = [$fol| forall x. ~(exists m. x = 2 * m) /\ (exists m. x = 3 * m + 1) <=>
>               (exists m. x = 12 * m + 1) \/ (exists m. x = 12 * m + 7) |]

Something else.

> pres39 = [$fol| forall x.
>         ~(divides(2,x))
>         ==> divides(4,x-1) \/
>             divides(8,x-1) \/
>             divides(8,x-3) \/
>             divides(6,x-1) \/
>             divides(14,x-1) \/
>             divides(14,x-9) \/
>             divides(14,x-11) \/
>             divides(24,x-5) \/
>             divides(24,x-11) |]

Testing fix for an earlier version with negative result from formlcm.     

> pres40 = [$fol| a + 2 = b /\ v_3 = b - a + 1 /\ v_2 = b - 2 /\ v_1 = 3 ==> false |]

Inspired by the Collatz conjecture.                                       

> pres41 = [$fol| exists a b. ~(a = 1) /\ ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b) |]

> pres42 = [$fol| exists a b. a > 1 /\ b > 1 /\
>                ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
>                (a = b) |]

> pres43 = [$fol| exists a b. a > 1 /\ b > 1 /\
>                ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
>                ((2 * a = b) \/ (2 * a = 3 * b + 1)) |]

Bob Constable's "stamp problem".

> pres45 = [$fol| forall x. x >= 8 ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v |]

> pres46 = [$fol| exists l.
>         forall x. x >= l
>                   ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v |]

> pres47 = [$fol| exists l.
>         forall x. x >= l
>                   ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 7 * v |]

> pres48 = [$fol| exists l.
>         forall x. x >= l
>                   ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 8 * v |]

> pres49 = [$fol| exists l.
>         forall x. x >= l
>                   ==> exists u v. u >= 0 /\ v >= 0 /\ x = 7 * u + 8 * v |]

Example from reciprocal mult: (2622 * x)>>16 = x/100 within a range.      

> pres50 = [$fol| forall x q1 q2 r1 r2.
>         x < 4699 /\
>         2622 * x = 65536 * q1 + r1 /\ 0 <= q1 /\ 0 <= r1 /\ r1 < 65536 /\
>         x = 100 * q2 + r2 /\ 0 <= q2 /\ 0 <= r2 /\ r2 < 100
>         ==> q1 = q2 |]

> pres51 = [$fol| forall x y.
>         (exists d. x + y = 2 * d) <=>
>         ((exists d. x = 2 * d) <=> (exists d. y = 2 * d)) |]

Landau trick! Is it too slow?

> pres52 = [$fol| forall n.
>      0 < n /\ n < 2400
>        ==> n <= 2 /\ 2 <= 2 * n \/
>            n <= 3 /\ 3 <= 2 * n \/
>            n <= 5 /\ 5 <= 2 * n \/
>            n <= 7 /\ 7 <= 2 * n \/
>            n <= 13 /\ 13 <= 2 * n \/
>            n <= 23 /\ 23 <= 2 * n \/
>            n <= 43 /\ 43 <= 2 * n \/
>            n <= 83 /\ 83 <= 2 * n \/
>            n <= 163 /\ 163 <= 2 * n \/
>            n <= 317 /\ 317 <= 2 * n \/
>            n <= 631 /\ 631 <= 2 * n \/
>            n <= 1259 /\ 1259 <= 2 * n \/
>            n <= 2503 /\ 2503 <= 2 * n |]

> pres53 = [$fol| forall d. exists x y. 3 * x + 5 * y = d |]

> pres54 = [$fol| forall d. exists x y. 3 * x + 5 * y = d |]

> pres55 = [$fol| forall d. d >= 8 ==> exists x y. 3 * x + 5 * y = d |]

> pres56 = [$fol| forall d. exists x y. 3 * x - 5 * y = d |]

Nelson Oppen

> nelop0 = [$fol| f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false |]

> nelop1 = [$fol| y <= x /\ y >= x + z /\ z >= 0 ==> f(f(x) - f(y)) = f(z) |]

> nelop2 = [$fol| x = y /\ y >= z /\ z >= x ==> f(z) = f(x) |]

> nelop3 = [$fol| a <= b /\ b <= f(a) /\ f(a) <= 1
>   ==> a + b <= 1 \/ b + f(b) <= 1 \/ f(f(b)) <= f(a) |]

Failures of original Shostak procedure.                                   

> nelop4 = [$fol| f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false |]

And this one is where the original procedure loops 

> nelop5 = [$fol| f(v) = v /\ f(u) = u - 1 /\ u = v ==> false |]

This is on p. 8 of Shostak's "Deciding combinations" paper 

> nelop6 = [$fol| z = f(x - y) /\ x = z + y /\ ~(-(y) = -(x - f(f(z)))) ==> false |]

This (ICS theories-1) fails without array operations 

> nelop7 = [$fol| a + 2 = b ==> f(read(update(A,a,3),b-2)) = f(b - a + 1) |]

can-001 from ICS examples site, with if-then-elses expanded manually 

> nelop8 = [$fol| (x = y /\ z = 1 ==> f(f((x+z))) = f(f((1+y)))) |]

RJB example; lists plus uninterpreted functions 

> nelop9 = [$fol| hd(x) = hd(y) /\ tl(x) = tl(y) /\ ~(x = nil) /\ ~(y = nil)
>    ==> f(x) = f(y) |]

Another one from the ICS paper 

> nelop10 = [$fol| ~(f(f(x) - f(y)) = f(z)) /\ y <= x /\ y >= x + z /\ z >= 0 ==> false |]

Shostak's "A Practical Decision Procedure..."

No longer works since I didn't do predicates in congruence closure

> nelop11 = [$fol| x < f(y) + 1 /\ f(y) <= x ==> (P(x,y) <=> P(f(y),y)) |]

Shostak's "Practical..." paper again, using extra clauses for MAX 

> nelop12 = [$fol| (x >= y ==> MAX(x,y) = x) /\ (y >= x ==> MAX(x,y) = y)
>    ==> x = y + 2 ==> MAX(x,y) = x |]

Shostak's "Practical..." paper again 

> nelop13 = [$fol| x <= g(x) /\ x >= g(x) ==> x = g(g(g(g(x)))) |]

Easy example I invented 

> nelop14 = [$fol| x^2 =  1 ==> (f(x) = f(-(x)))  ==> (f(x) = f(1)) |]

Taken from Clark Barrett's CVC page 

> nelop15 = [$fol| 2 * f(x + y) = 3 * y /\ 2 * x = y ==> f(f(x + y)) = 3 * x |]

My former running example in the text; seems too slow.
Anyway this also needs extra predicates in CC

> nelop16 = [$fol| x^2 = y^2 /\ x < y /\ z^2 = z /\ x < x * z /\ P(f(1 + z))
>   ==> P(f(x + y) - f(0)) |]

An example where the "naive" procedure is slow but feasible

> nelop17 = [$fol| 4 * x = 2 * x + 2 * y /\ x = f(2 * x - y) /\
>   f(2 * y - x) = 3 /\ f(x) = 4 ==> false |]


