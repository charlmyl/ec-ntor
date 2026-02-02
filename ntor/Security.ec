require import AllCore FSet FMap Distr DProd List SplitRO.
require (*  *) Birthday SplitRO StdBigop StdOrder Games.

(*   *) import StdBigop.Bigreal.BRA StdOrder.RealOrder.

clone import Games as Gamesc.
import NTOR_nosid_c NTORc GAKE_mod HRO_mod_c DH.G DH.GP DH.FD DH.GP.ZModE.

(* ------------------------------------------------------------------------------------------ *)
(* Reductions *)
(* ------------------------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------------------------ *)
(* Ctxt Collision Reduction *)
op q_is : { int | 0 <= q_is } as ge0_q_is.
op q_m1 : { int | 0 <= q_m1 } as ge0_q_m1.
op q_m2 : { int | 0 <= q_m2 } as ge0_q_m2.

clone Birthday as BB with
  type T  <- skey,
  op   uT <- dt,
  op   q  <- q_is + q_m1 + q_m2
  proof *.
realize ge0_q by smt(ge0_q_is ge0_q_m1 ge0_q_m2).

module Counter (G : GAKE_nodhs) : GAKE_nodhs_i = {
  var cis, cm1, cm2 : int

  include G[h, send_msg3, c_rev_skey, s_rev_skey, rev_ltkey, c_rev_ephkey, s_rev_ephkey, c_test, s_test]

  proc init_mem(b: bool) = {
    (cis, cm1, cm2) <- (0, 0, 0);
  }
  
  proc init_s() = {
    var m;
    cis <- cis + 1;
    m <@ G.init_s();
    return m;
  }
  proc send_msg1(x) = {
    var m;
    cm1 <- cm1 + 1;
    m <@ G.send_msg1(x);
    return m;
  }
  proc send_msg2(x) = {
    var m;
    cm2 <- cm2 + 1;
    m <@ G.send_msg2(x);
    return m;
  }
}.

module Red_Coll_O_AKE (S : BB.ASampler) = Game0 with {
  proc init_s [
    ^sk<$ ~ {sk <@ S.s();}
  ]

  proc send_msg1 [
    ^if.^match#None.^sk<$ ~ {sk <@ S.s();}
  ]

  proc send_msg2 [
    ^match#Some.^match#None.^sk<$ ~ {sk <@ S.s();}
  ]
}.

module (Red_Coll_real (A : A_GAKE_nodhs) : BB.Adv) (S : BB.ASampler) = {
  proc a() = {
    var b';

    Red_Coll_O_AKE(S).init_mem(false);
    Counter(Red_Coll_O_AKE(S)).init_mem(false);
    b' <@ A(Counter(Red_Coll_O_AKE(S))).run();
  }
}.

module (Red_Coll_ideal (A : A_GAKE_nodhs) : BB.Adv) (S : BB.ASampler) = {
  proc a() = {
    var b';

    Red_Coll_O_AKE(S).init_mem(true);
    Counter(Red_Coll_O_AKE(S)).init_mem(true);
    b' <@ A(Counter(Red_Coll_O_AKE(S))).run();
  }
}.

module E_GAKE_BB (A : A_GAKE_nodhs) = {
  module O = Game1

  proc run(b: bool) : bool = {
    var b' : bool;

    O.init_mem(b);
    
    b' <@ A(O).run();
    
    return b' /\ !O.bad1;
  }
}.



(* ------------------------------------------------------------------------------------------ *)
(* ROM Reductions *)
clone Split as ROc with
  type from        <= pkey * pkey * pkey * pkey * pkey,
  type to          <= tag * key,
  op   sampleto  _ <= dtag `*` dkey,
  type input       <= bool,
  type output      <= bool
proof *.

clone ROc.SplitCodom as ROSc with 
  type to1       <- tag,
  type to2       <- key,
  op topair tk   <- tk,
  op ofpair tk   <- tk,
  op sampleto1 _ <- dtag,
  op sampleto2 _ <- dkey
  proof *.
realize topairK by rewrite /topair /ofpair.
realize sample_spec by rewrite /ofpair dprodC dmap_comp //=.

print Game2.

module (Red_ROM (D : A_GAKE_nodhs) : ROc.IdealAll.RO_Distinguisher) (O : ROc.IdealAll.RO) = {
  module AKE_O : GAKE_nodhs = Game2 with {
    proc h [ 
      ^if.^tk<$ ~ {tk <@ O.get(x);}
      ^if.^if -
      ^if.^tk<- -
    ]
  }

  proc distinguish(b) = {
    var b';
    AKE_O.init_mem(b);
    b' <@ D(AKE_O).run();
    return b';
  }
}.

print Game3.

module (Red_ROM2 (D : A_GAKE_nodhs) (O1 : ROSc.I1.RO) : ROSc.I2.RO_Distinguisher) (O2 : ROSc.I2.RO) = {
  module AKE_O : GAKE_nodhs = Game3 with {
    proc init_mem [
      ^h1m<- ~ {O1.init();}
      ^h2m<- -
    ]

    proc h [ 
      ^if.^tk<- ~ {tk <- (t, k);}
      ^if.^t<$ ~ {t <@ O1.get(x); k <@ O2.get(x);}
      ^if.^if -
      ^if.^k<$ -
      ^if.^if -
    ]

    proc send_msg2 [
      ^if.^match#Some.^match#None.^if.^ts<$ ~ {t_B <@ O1.get(x); O2.sample(x); key <- witness;}
      [^if.^match#Some.^match#None.^if.^if - ^key<-] -
    ]

    proc send_msg3 [
      ^if.^match#Some.^match#Pending_mod.^ts<$ ~ {t_A <@ O1.get(x); O2.sample(x); key <- witness;}
      ^if.^match#Some.^match#Pending_mod.^if ~ (pt.`2 \notin m1_set /\ pt.`2 \notin x_set)
      ^if.^match#Some.^match#Pending_mod.^if.^x_set<- ~ {x_set <- x_set `|` fset1 pt.`2;}
      [^if.^match#Some.^match#Pending_mod.^if - ^key<-] -
    ]


    proc c_rev_skey [
      var ks : key
      var x : pkey * pkey * pkey * pkey * pkey
      ^if.^match#Some.^match#Accepted_mod.^if.^k<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1); ks <@ O2.get(x); k <- Some ks;}
    ]

    proc s_rev_skey [
      var ks : key
      var x : pkey * pkey * pkey * pkey * pkey
      ^if.^match#Some.^match#Accepted_mod.^if.^k<- ~ {x <- ((t'.`1).`2 ^ (oget st'.`2), (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, g ^ (oget st'.`2)); ks <@ O2.get(x); k <- Some ks;}
    ]

    proc c_test [
      var ks2 : key
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^ks<$ + ^ {ks2 <@ O2.get(x);}
    ]

    proc s_test [
      var ks2 : key
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^ks<$ + ^ {ks2 <@ O2.get(x);}
    ]
  }

  proc distinguish(b) = {
    var b';
    AKE_O.init_mem(b);
    b' <@ D(AKE_O).run();
    return b';
  }
}.


(* CDH stuff for now *)
module type Oracle = {
  proc ddh(x y z : group) : bool 
  proc gen1() : group
  proc gen2() : group
  proc corrupt1(i : int) : exp option
  proc corrupt2(j : int) : exp option
}.

module type Oracle_i = {
  include Oracle

  proc init_mem() : unit
}.

module St_CDH_O : Oracle_i = {
  var win : bool
  var n, m : int
  var cr1, cr2 : int fset
  var x_map : (int, exp) fmap
  var y_map : (int, exp) fmap

  proc init_mem() : unit = {
    win <- false;
    n <- 0;
    m <- 0;
    cr1 <- fset0;
    cr2 <- fset0;
    x_map <- empty;
    y_map <- empty;
  }

  proc ddh(x y z : group) : bool  = {
    var r <- false;

    if (exists i, i \in x_map /\ x = g ^ (oget x_map.[i]) /\ z = y ^ (oget x_map.[i])) {
      if (exists i j, i \in x_map /\ x = g ^ (oget x_map.[i]) /\ z = y ^ (oget x_map.[i]) /\ i \notin cr1 /\ 
                    j \in y_map /\ y = g ^ (oget y_map.[j]) /\ j \notin cr2) {
         win <- true;
      }
      r <- true;
    } elif (exists j, j \in y_map /\ y = g ^ (oget y_map.[j]) /\ z = x ^ (oget y_map.[j])) {
      r <- true;
    }

    return r;
  }

  proc gen1() : group = {
    var x_n;

    n <- n + 1;
    x_n <$ dt;
    x_map.[n] <- x_n;

    return (g ^ x_n);
  }

  proc gen2() : group = {
    var y_m;

    m <- m + 1;
    y_m <$ dt;
    y_map.[m] <- y_m;

    return (g ^ y_m);
  }

  proc corrupt1(i : int) : exp option = {
    var r <- None;

    if (i \in x_map) {
      cr1 <- cr1 `|` fset1 i;
      r <- x_map.[i];
    }

    return r;
  }

  proc corrupt2(j : int) : exp option = {
    var r <- None;

    if (j \in y_map) {
      cr2 <- cr2 `|` fset1 j;
      r <- y_map.[j];
    }

    return r;
  }
}.

module St_CDH_O_nc : Oracle_i = {
  var win : bool
  var n, m : int
  var cr1, cr2 : int fset
  var x_map : (int, exp) fmap
  var y_map : (int, exp) fmap

  proc init_mem() : unit = {
    win <- false;
    n <- 0;
    m <- 0;
    cr1 <- fset0;
    cr2 <- fset0;
    x_map <- empty;
    y_map <- empty;
  }

  proc ddh(x y z : group) : bool  = {
    var r <- false;

    if (exists i, i \in x_map /\ x = g ^ (oget x_map.[i]) /\ z = y ^ (oget x_map.[i])) {
      if (exists i j, i \in x_map /\ x = g ^ (oget x_map.[i]) /\ z = y ^ (oget x_map.[i]) /\ i \notin cr1 /\ 
                    j \in y_map /\ y = g ^ (oget y_map.[j]) /\ j \notin cr2) {
         win <- true;
      }
      r <- true;
    } elif (exists j, j \in y_map /\ y = g ^ (oget y_map.[j]) /\ z = x ^ (oget y_map.[j])) {
      r <- true;
    }

    return r;
  }

  proc gen1() : group = {
    var x_n;

    n <- n + 1;
    x_n <$ dt;
    if (!rng x_map x_n) {
      x_map.[n] <- x_n;
    }

    return (g ^ x_n);
  }

  proc gen2() : group = {
    var y_m;

    m <- m + 1;
    y_m <$ dt;
    if (!rng y_map y_m) {
      y_map.[m] <- y_m;
    }

    return (g ^ y_m);
  }

  proc corrupt1(i : int) : exp option = {
    var r <- None;

    if (i \in x_map) {
      cr1 <- cr1 `|` fset1 i;
      r <- x_map.[i];
    }

    return r;
  }

  proc corrupt2(j : int) : exp option = {
    var r <- None;

    if (j \in y_map) {
      cr2 <- cr2 `|` fset1 j;
      r <- y_map.[j];
    }

    return r;
  }
}.

module type St_CDH_A (O : Oracle) = {
  proc solve() : unit
}.

module St_CDH_E (O : Oracle_i) (A : St_CDH_A) = {
  proc run(): unit = {
    
    O.init_mem();
    A(O).solve();

    return ();
  }
}.

(* CDH reductions *)
print Game4Ltk.

module (Red_Ltk (A : A_GAKE_nodhs) : St_CDH_A) (O : Oracle) = {
  module Red_O : GAKE_nodhs_i = Game4Ltk with {
    var count_b : int
    var b_inst : (pkey, int) fmap
    var count_i : int
    var i_inst : (int, int) fmap
    var h1m_opt : (pkey option * pkey option * pkey * pkey * pkey, tag) fmap
    var h2m_opt : (pkey option * pkey option * pkey * pkey * pkey, key) fmap
    var tags_opt : (pkey option * pkey option * pkey * pkey * pkey, tag) fmap
    var tq_opt : (pkey option * pkey option * pkey * pkey * pkey) option
    var hq_opt : (pkey option * pkey option * pkey * pkey * pkey) fset

    proc init_mem [
      -1 + {tags_opt <- empty; h1m_opt <- empty; h2m_opt <- empty; count_b <- 0; b_inst <- empty; count_i <- 0; i_inst <- empty;}
    ]

    proc h [
      var valid1, valid2 : bool
      var win1 : bool
      var x1, x2 : group option
      var rt : tag
      var rk : key

      [^if.0 - ^tk<-] ~ { if (x.`3 \in servers) {
                         valid2 <@ O.ddh((x.`4, x.`3, x.`2));
                         if (valid2) { 
                           valid1 <@ O.ddh((x.`4, x.`5, x.`1)); 
                           if (valid1) {
                             if (x.`4 \in m1_set) {x1 <- None; x2 <- None;} else {x1 <- Some x.`1; x2 <- Some x.`2;}
                           } else {if (x.`4 \notin m1_set /\ x.`5 \in m2_set /\ x.`5 \notin servers) {x1 <- Some x.`1; x2 <- None;} else {x1 <- Some x.`1; x2 <- Some x.`2;}}
                         } else {x1 <- Some x.`1; x2 <- Some x.`2;}
                       } else {x1 <- Some x.`1; x2 <- Some x.`2;}
                       t <$ dtag;
                       if ((x1, x2, x.`3, x.`4, x.`5) \notin h1m_opt) {h1m_opt.[(x1, x2, x.`3, x.`4, x.`5)] <- t;}
                       k <$ dkey;
                       if ((x1, x2, x.`3, x.`4, x.`5) \notin h2m_opt) {h2m_opt.[(x1, x2, x.`3, x.`4, x.`5)] <- k;}
                       tk <- (oget h1m_opt.[(x1, x2, x.`3, x.`4, x.`5)], oget h2m_opt.[(x1, x2, x.`3, x.`4, x.`5)]);}
      ^if.^badq<- - 
      ^if.^hq<- -
    ]

    proc init_s [
      [^if.^sk<$ - ^pk<-] ~ {count_b <- count_b + 1; sk <- witness; pk <@ O.gen2();}
      ^if.^if.^bad2<- + ^ {b_inst.[pk] <- count_b;}
    ]

    proc send_msg1 [
      [^if.^if.^match#None.^sk<$ - ^pk<-] ~ {count_i <- count_i + 1; sk <- witness; pk <@ O.gen1(); i_inst.[i] <- count_i;}
    ]

    proc send_msg2 [
      var x1 : group option

      ^if.^match#Some.^match#None.^if.^if{2} ~ ((x1, None, x.`3, x.`4, x.`5) \notin h1m_opt)
      ^if.^match#Some.^match#None.^if.^if{2}.^h1m<- ~ {h1m_opt.[(x1, None, x.`3, x.`4, x.`5)] <- ts;}
      ^if.^match#Some.^match#None.^if.^t_B<- ~ {t_B <- oget h1m_opt.[(x1, None, x.`3, x.`4, x.`5)];} 
      ^if.^match#Some.^match#None.^if.^x<- ~ {x <- (m2 ^ sk, m2 ^ sk_b, b, m2, pk); if (m2 \in m1_set) {x1 <- None;} else {x1 <- Some x.`1;}}
      ^if.^match#Some.^match#None.^if.^s_smap<- ~ {s_smap.[b, j] <- Accepted_mod (witness, Some sk) ((b, m2), Some (pk, t_B)) key (false, false, false);}

    ]

    proc send_msg3 [
      ^if.^match#Some.^match#Pending_mod.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h1m_opt)
      ^if.^match#Some.^match#Pending_mod.^if.^h1m<- ~ {h1m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ts;}
      ^if.^match#Some.^match#Pending_mod.^t_A<- ~ {t_A <- oget h1m_opt.[(None, None, x.`3, x.`4, x.`5)];}
      ^if.^match#Some.^match#Pending_mod.^x<- ~ {x <- (m3.`1 ^ sk_ce, b ^ sk_ce, b, pt.`2, m3.`1);}
    ]

    proc c_rev_skey [
      ^if.^match#Some.^match#Accepted_mod.^if.^x<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, t'.`1.`1, t'.`1.`2, (oget t'.`2).`1);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
      ^if.^match#Some.^match#Accepted_mod.^if.^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];}
    ]

    proc s_rev_skey [
      var x1 : group option

      ^if.^match#Some.^match#Accepted_mod.^if.^x<- ~ {x <- (t'.`1.`2 ^ oget st'.`2, t'.`1.`2 ^ st'.`1, t'.`1.`1, t'.`1.`2, g ^ oget st'.`2);}
      ^if.^match#Some.^match#Accepted_mod.^if.^ks<$ + {if (t'.`1.`2 \notin m1_set) {x1 <- Some x.`1;} else {x1 <- None;}}
      ^if.^match#Some.^match#Accepted_mod.^if.^if ~ ((x1, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^h2m<- ~ {h2m_opt.[(x1, None, x.`3, x.`4, x.`5)] <- ks;}
      ^if.^match#Some.^match#Accepted_mod.^if.^k<- ~ {k <- h2m_opt.[(x1, None, x.`3, x.`4, x.`5)];} 
    ]

    proc rev_ltkey [
      var inst : int

      ^if.^match#Some.^match#Honest_mod.^if.^if{2}.^ltk<- ~ {inst <- oget b_inst.[b]; ltk <@ O.corrupt2(inst);}
    ]

    proc c_rev_ephkey [
      var inst : int

      ^if.^match#Some.^match#Pending_mod.^if.^ek<- ~ {inst <- oget i_inst.[i]; ek <@ O.corrupt1(inst);}
      ^if.^match#Some.^match#Accepted_mod.^if.^ek<- ~ {inst <- oget i_inst.[i]; ek <@ O.corrupt1(inst);}
    ]

    proc c_test [
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^x<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, t'.`1.`1, t'.`1.`2, (oget t'.`2).`1);}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^tq<- -
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^badq<- -
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];} 
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^x<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, t'.`1.`1, t'.`1.`2, (oget t'.`2).`1);}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^tq<- -
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^badq<- -
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks2;}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];}
    ]

    proc s_test [
      var x1 : group option

      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^x<- ~ {x <- (t'.`1.`2 ^ oget st'.`2, t'.`1.`2 ^ st'.`1, t'.`1.`1, t'.`1.`2, g ^ oget st'.`2);}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^tq<- -
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^badq<- -
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^x<- ~ {x <- (t'.`1.`2 ^ oget st'.`2, t'.`1.`2 ^ st'.`1, t'.`1.`1, t'.`1.`2, g ^ oget st'.`2);}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^tq<- -
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^badq<- -
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks2;}
      ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];}
    ]
  }

  proc solve() : unit = {
    var b' : bool;

    Red_O.init_mem(true);
    b' <@ A(Red_O).run();
    return ();
  }
}.

print Red_Ltk.Red_O.


(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GAKE_nodhs {-GAKEb_nodhs, -Game0, -Game1, -Game2, -Game3, -Game4, -Game4Ltk, -ROc.IdealAll.RO, -RO, -FRO, -ROSc.I1.RO, -ROSc.I2.RO, -ROSc.I1.FRO, -ROSc.I2.FRO, -Red_Coll_real, -Red_Coll_ideal, -BB.Sample, -Red_ROM, -Red_ROM2, -St_CDH_O, -Red_Ltk }.

declare axiom A_ll (G <: GAKE_nodhs{-A}):
  islossless G.h =>
  islossless G.init_s =>
  islossless G.send_msg1 =>
  islossless G.send_msg2 =>
  islossless G.send_msg3 =>
  islossless G.c_rev_skey =>
  islossless G.s_rev_skey =>
  islossless G.rev_ltkey =>
  islossless G.c_rev_ephkey =>
  islossless G.s_rev_ephkey =>
  islossless G.c_test =>
  islossless G.s_test =>
  islossless A(G).run.

declare axiom A_bounded_qs: forall (G <: GAKE_nodhs{-A}), hoare[A(Counter(G)).run: Counter.cis = 0 /\ Counter.cm1 = 0 /\ Counter.cm2 = 0 ==> Counter.cis <= q_is /\ Counter.cm1 <= q_m1 /\ Counter.cm2 <= q_m2].



(* ------------------------------------------------------------------------------------------ *)
(* Step 0: Inlining everything. *)
lemma gake_game0 b &m :
  Pr[E_GAKE_nodhs(GAKEb_nodhs(NTOR_S_mod, NTOR_C_mod, RO), A).run(b) @ &m : res] = Pr[E_GAKE_nodhs(Game0, A).run(b) @ &m : res].
proof. admit. (*
byequiv => //.
proc; inline.
call (: ={b0, servers, c_smap, s_smap, tested}(GAKEb_nodhs, Game0) /\ RO.m{1} = Game0.hm{2}); try sim />.

- proc; inline; auto; if => //; auto => /#.

- proc; inline. 
  sp; if => //.
  sp; match = => //; auto.

- proc; inline.
  sp; match = => // sko.
  match = => //.
  match Some {1} 4.
  + by auto=> /> _ _ _ _; exists (sko, None).
  match Some {1} ^match=> //; 1: by auto=> /> /#.
  auto => />.

- proc; inline; auto=> />.
  sp; match = => //; 1: auto. 
  by match = => //; 1: by auto. *)
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 1: Remove collisions in ephemeral and long-term keys. Strategy with 2 * bound *)
lemma game0_game1 b &m: `| Pr[E_GAKE_nodhs(Game0, A).run(b) @ &m : res] - Pr[E_GAKE_nodhs(Game1, A).run(b) @ &m : res] | <= Pr[E_GAKE_nodhs(Game0, A).run(b) @ &m : Game0.bad1].
proof. admit. (*
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game1.bad1 => //; first last.
+ smt().
symmetry; proc; inline*.
call (: Game1.bad1
      , ={b0, servers, c_smap, s_smap, tested, b_set, x_set, y_set, m1_set, m2_set, pk_set, hm, bad1, bad2}(Game0, Game1)
      , ={bad1}(Game0, Game1)) => //; try sim />.

- exact A_ll.

- proc; inline.
  rcondt{2} ^if. auto => />.
  auto => />.
- move => &2 bad; proc; auto => />. 
  by rewrite weight_dprod dkey_ll dtag_ll.
- move => &1; proc; auto.
  rcondf ^if; auto => />.
  
- proc.
  rcondt{2} ^if. auto => />.
  sp; seq 1 1: (#pre /\ ={sk}); 1: by auto.
  by sp 1 1; if{2}; auto => />.
- move => &2 bad.
  proc; auto.
  rewrite dt_ll //=. smt().
- move => &1. 
  proc. 
  rcondf ^if; auto => />.

- proc.
  rcondt{2} ^if. auto => />.
  sp; if => //.
  sp; match = => //. 
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  by rewrite dt_ll; smt().
- move => &1. 
  proc. 
  rcondf ^if; auto => />. 

- proc; inline. 
  rcondt{2} ^if. auto => />.
  sp; match = => // sk.
  match = => //.
  + seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp 0 3; if{2}.
  + rcondt{2} ^if. auto => />.
    by auto => />. 
  auto.
- move => &2 bad.
  proc; inline; sp; match; auto => />.
  match; auto => />.
  rewrite dt_ll weight_dprod dkey_ll dtag_ll. 
  by smt().
- move => &1. 
  proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  rcondt{2} ^if. auto => />.
  sp; match = => // st.
  match = => // s pt ir.
  rcondt{2} ^if. auto => />.
  auto => />.
- move => &2 bad.
  proc; inline.
  sp; match; auto. 
  match; auto => />.
  by rewrite weight_dprod dkey_ll dtag_ll.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  rcondt{2} ^if. auto => />.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  rcondt{2} ^if. auto => />.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  rcondt{2} ^if. auto => />.
  sp; match = => // st.
  match = => // sk.
  auto => />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  rcondt{2} ^if. auto => />.
  sp; match = => // st.
  match = => // [s pt ir|s t k ir].
  + auto => />.
  auto => />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  rcondt{2} ^if. auto => />.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  rcondt{2} ^if. auto => />.
  sp; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //; if => //.
  + auto => />.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  rcondt{2} ^if. auto => />.
  sp; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //; if => //.
  + auto => />.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

auto => />.
move => rl rr al bl b1l b2l csl hml m1l m2l pkl ssl sl tl xl yl ar br b1r b2r csr hmr m1r m2r pkr ssr sr tr xr yr. 
by case : (!b1r) => />. *)
qed.


(* ------------------------------------------------------------------------------------------ *)
(* Step 1b: Bound the bad event. *)
lemma game0_bad bit &m: Pr[E_GAKE_nodhs(Game0, A).run(bit) @ &m : Game0.bad1] <= ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt).
proof. admit. (*
case (bit) => real_ideal.

(* Proof for the ideal side *)
apply (StdOrder.RealOrder.ler_trans Pr[BB.Exp(BB.Sample, Red_Coll_ideal(A)).main() @ &m : ! uniq BB.Sample.l]); first last.
+ apply (BB.pr_collision_q2 (Red_Coll_ideal(A))).
  + move => S S_ll.
    islossless.
    apply (A_ll (Counter(Red_Coll_O_AKE(S)))); islossless.
    + match; 1: auto; islossless.
    + match; auto. 
      by sp; match; auto; islossless.
    + match => //.
      by sp; match; auto; islossless.
    + match => //; islossless.
      by match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
  proc; inline.
  sp.
  conseq (: _ ==> size BB.Sample.l <= Counter.cis + Counter.cm1 + Counter.cm2) (: Counter.cis = 0 /\ Counter.cm1 = 0 /\ Counter.cm2 = 0 ==> Counter.cis <= q_is /\ Counter.cm1 <= q_m1 /\ Counter.cm2 <= q_m2)=> //.
  + smt().
  + by call (A_bounded_qs (Red_Coll_O_AKE(BB.Sample))).
  call (: size BB.Sample.l <= Counter.cis + Counter.cm1 + Counter.cm2) => //.
  + by proc; auto.
  + by proc; inline; sp; auto => /#.
  + proc; inline; sp; if => //; 2: auto => /#.
    by sp; match; auto => /#.
  + proc; inline; sp; match; 1: auto => /#.
    case ((Red_Coll_O_AKE.s_smap.[b, j]) = None).
    + by match None ^match; auto => /#.
    by match Some ^match; auto => /#.
  + by proc; inline; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; if => //; sp; match; 1: auto; match; auto; if => //; if => //; auto.
  + by proc; sp; if => //; sp; match; 1: auto; match; auto; if => //; if => //; auto.
  auto => /#.
byequiv => //.
proc. inline.
call (:
 ={b0, hm, servers, c_smap, s_smap, tested, b_set, x_set, y_set, pk_set, m1_set, m2_set, bad1, bad2}(Game0, Red_Coll_O_AKE(BB.Sample))
 /\ (Game0.bad1{1} => !uniq BB.Sample.l{2})
 /\ (forall sk, g ^ sk \in (Game0.pk_set{1} `|` Game0.m1_set{1} `|` Game0.m2_set{1})  => sk \in BB.Sample.l{2})
) => //; try sim />.
+ proc; inline; sp 0 2; auto => />.
  smt(mem_set in_fsetU1 in_fsetU pow_bij).
+ proc; inline; sp 2 4; if => //; auto.
  sp; match = => //.
  auto => />.
  smt(mem_set in_fsetU1 in_fsetU pow_bij).
+ proc; inline; sp 2 4; match = => // [|st]; 1: auto.
  match = => // [|st']; 2: auto.
  auto => />.
  smt(mem_set in_fsetU1 in_fsetU pow_bij).
auto => />.
smt(in_fset0).

(* Proof for the real side *)
apply (StdOrder.RealOrder.ler_trans Pr[BB.Exp(BB.Sample, Red_Coll_real(A)).main() @ &m : ! uniq BB.Sample.l]); first last.
+ apply (BB.pr_collision_q2 (Red_Coll_real(A))).
  + move => S S_ll.
    islossless.
    apply (A_ll (Counter(Red_Coll_O_AKE(S)))); islossless.
    + match; 1: auto; islossless.
    + match; auto. 
      by sp; match; auto; islossless.
    + match => //.
      by sp; match; auto; islossless.
    + match => //; islossless.
      by match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
    + by match; 1: auto; match; islossless.
  proc; inline.
  sp.
  conseq (: _ ==> size BB.Sample.l <= Counter.cis + Counter.cm1 + Counter.cm2) (: Counter.cis = 0 /\ Counter.cm1 = 0 /\ Counter.cm2 = 0 ==> Counter.cis <= q_is /\ Counter.cm1 <= q_m1 /\ Counter.cm2 <= q_m2)=> //.
  + smt().
  + by call (A_bounded_qs (Red_Coll_O_AKE(BB.Sample))).
  call (: size BB.Sample.l <= Counter.cis + Counter.cm1 + Counter.cm2) => //.
  + by proc; auto.
  + by proc; inline; sp; auto => /#.
  + proc; inline; sp; if => //; 2: auto => /#.
    by sp; match; auto => /#.
  + proc; inline; sp; match; 1: auto => /#.
    case ((Red_Coll_O_AKE.s_smap.[b, j]) = None).
    + by match None ^match; auto => /#.
    by match Some ^match; auto => /#.
  + by proc; inline; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; if => //; sp; match; 1: auto; match; auto; if => //; if => //; auto.
  + by proc; sp; if => //; sp; match; 1: auto; match; auto; if => //; if => //; auto.
  auto => /#.
byequiv => //.
proc. inline.
call (:
 ={b0, hm, servers, c_smap, s_smap, tested, pk_set, m1_set, m2_set, bad1}(Game0, Red_Coll_O_AKE(BB.Sample))
 /\ (Game0.bad1{1} => !uniq BB.Sample.l{2})
 /\ (forall sk, g ^ sk \in (Game0.pk_set{1} `|` Game0.m1_set{1} `|` Game0.m2_set{1}) => sk \in BB.Sample.l{2})
) => //; try sim />.
+ proc; inline; sp 0 2; auto => />.
  smt(mem_set in_fsetU1 in_fsetU pow_bij).
+ proc; inline; sp 2 4; if => //; auto.
  sp; match = => //.
  auto => />.
  smt(mem_set in_fsetU1 in_fsetU pow_bij).
+ proc; inline; sp 2 4; match = => // [|st]; 1: auto.
  match = => // [|st']; 2: auto.
  auto => />.
  smt(mem_set in_fsetU1 in_fsetU pow_bij).
auto => />.
smt(in_fset0). *)
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 2: Restricting ability to predict public keys in RO queries *)
lemma game1_game2 b &m: `| Pr[E_GAKE_nodhs(Game1, A).run(b) @ &m : res] - Pr[E_GAKE_nodhs(Game2, A).run(b) @ &m : res] | <= Pr[E_GAKE_nodhs(Game1, A).run(b) @ &m : Game1.bad2].
proof. admit. (*
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game2.bad2 => //; first last.
+ smt().
symmetry; proc; inline*.
call (: Game2.bad2
      , ={b0, servers, c_smap, s_smap, tested, b_set, x_set, y_set, pk_set, m1_set, m2_set, hm, bad1, bad2}(Game1, Game2)
      , ={bad2}(Game1, Game2)) => //; try sim />.

- exact A_ll.

- proc; inline.
  sp; if => //.
  auto => />.
- move => &2 bad; proc; sp; if; auto => />. 
  by rewrite weight_dprod dkey_ll dtag_ll.
- move => &1; proc; auto.
  rcondf ^if; auto => />.
  
- proc.
  sp; if => //.
  sp; seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp 1 1; if => //.
  auto => />. smt().
- move => &2 bad.
  proc; sp; if; auto.
  rewrite dt_ll //=. smt().
- move => &1. 
  proc. 
  rcondf ^if; auto => />.

- proc.
  sp; if => //.
  sp; if => //.
  sp; match = => //. 
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  auto => />. smt().
- move => &2 bad.
  proc; sp; if => //; sp; if. 
  + match; auto => />.
    by rewrite dt_ll; smt().
  by auto.
- move => &1. 
  proc. 
  rcondf ^if; auto => />. 

- proc; inline. 
  sp; if => //.
  sp; match = => // sk.
  match = => //.
  + seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp 3 3; if{2}.
  + rcondt {2} ^if. auto => />.
    rcondt{1} ^if. auto => />.
    rcondt{1} ^if. auto => />.
    by auto => />.
  if {1} => //.
  rcondt{1} ^if. auto => />. 
  auto => />. smt().
- move => &2 bad.
  proc; inline; sp; if; sp. 
  match; auto => />.
  match; auto => />.
  seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dt_ll.
  + sp; if => //.
    + rcondt ^if. auto => />.
      auto => />.
      by rewrite weight_dprod dkey_ll dtag_ll /#.
    auto => /#.
  + hoare. 
    by auto => />.
  auto => />.
- move => &1. 
  proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // s pt ir.
  rcondt{2} ^if. auto => />.
  rcondt{1} ^if. auto => />.
  auto => />.
- move => &2 bad.
  proc; inline.
  sp; if => //.
  sp; match; auto. 
  match => //. 
  rcondt ^if. auto => />.
  auto => />.
  by rewrite weight_dprod dkey_ll dtag_ll.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp.
  match => //. 
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />.
- move => &2 bad.
  proc; sp; if => //.  
  match => //. 
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // sk.
  auto => />.
- move => &2 bad.
  proc; sp; if => //. 
  match => //.
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // [s pt ir|s t k ir].
  + auto => />.
  auto => />.
- move => &2 bad.
  proc; sp; if => //.
  match => //. 
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />.
- move => &2 bad.
  proc; sp; if => //.
  match => //. 
  match; auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if => //.
  sp; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //; if => //.
  + auto => />.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp; if => //.
  match => //.
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if => //.
  sp; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //; if => //.
  + auto => />.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp; if => //.
  match => //.
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

auto => />.
move => rl rr al bl b1l b2l csl hml kpl m1l m2l ssl sl tl xl yl ar br b1r b2r csr hmr pkr m1r m2r ssr sr tr xr yr. 
by case : (!b2r) => />. *)
qed.



(* ------------------------------------------------------------------------------------------ *)
(* Step 3: Splitting the random oracle. *)
local clone import DProd.ProdSampling with
  type t1 <- tag,
  type t2 <- key
proof *.

lemma game2_game3 bit &m: Pr[E_GAKE_nodhs(Game2, A).run(bit) @ &m : res] =  Pr[E_GAKE_nodhs(Game3, A).run(bit) @ &m : res].
proof. admit. (*
(* Proof on the real side *)
byequiv (: ={glob A, glob Red_ROM} /\ arg{1} = bit /\ arg{2} = bit ==> _) => //.
proc*.
transitivity*  {1} { r <@ ROc.IdealAll.MainD(Red_ROM(A), ROc.IdealAll.RO).distinguish(bit); }.

+ inline; wp.
  call (: ={b0, servers, c_smap, s_smap, tested, b_set, x_set, y_set, pk_set, m1_set, m2_set, bad1, bad2}(Game2, Red_ROM.AKE_O) /\ Game2.hm{1} = ROc.IdealAll.RO.m{2}); 
    try sim />.

  + proc; inline.
    sp; if => //.
    auto => />.

  + proc; inline.
    sp; if => //.
    sp; match = => // key.
    match = => //.
    seq 1 1: (#pre /\ ={sk}); 1: by auto.
    sp 3 3; if => //.
    rcondt {1} ^if. auto => />.
    rcondt {2} ^if. auto => />.
    auto => />.

  + proc; inline.
    sp; if => //.
    sp; match = => // st.
    match = => // st' pt ir.
    rcondt {1} ^if. auto => />.
    rcondt {2} ^if. auto => />.
    auto => />.

  + auto.

transitivity*  {2} { r <@ ROc.IdealAll.MainD(Red_ROM(A), ROSc.RO_Pair(ROSc.I1.RO,ROSc.I2.RO)).distinguish(bit); };
  1: by call (ROSc.RO_split (Red_ROM(A))).

inline; wp.
call (: ={b0, servers, c_smap, s_smap, tested, b_set, x_set, y_set, pk_set, m1_set, m2_set, bad1, bad2}(Red_ROM.AKE_O, Game3) /\ Game3.h1m{2} = ROSc.I1.RO.m{1} /\ Game3.h2m{2} = ROSc.I2.RO.m{1}
          /\ (forall x, x \in ROSc.I1.RO.m{1} <=> x \in ROSc.I2.RO.m{1})
          /\ (forall b, b \in Game3.servers{2} => b \in Game3.pk_set{2})
          /\ (forall b sk, b \in Game3.servers{2} => (get_skey (oget Game3.servers{2}.[b])) = Some sk => b = g ^ sk)
          /\ (forall i st pt ir, i \in Game3.c_smap{2} => Game3.c_smap{2}.[i] = Some (Pending_mod st pt ir) => st.`1 \in Game3.servers{2}));
    try sim />.

+ proc; inline.
  sp; if => //.
  + sp; seq 1 1: (#pre /\ r{1} = t{2}); 1: by auto => />.
    auto => />.
    smt(mem_set).
  auto => />.

+ proc; inline.
  sp; if => //.
  auto => /> *. smt(mem_set get_setE in_fsetU1).

+ proc; inline.
  sp; if => //; sp; if => //; match => //.
  auto => /> *. smt(in_fsetU1 get_setE).

+ proc; inline.
  sp; if => //.
  sp; match = => // key.
  match = => //.
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp 3 3; if => //.
  rcondt {1} ^if. auto => />.
  sp. seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto => />.
  if => //.
  + sp. seq 1 1: (#pre /\ r3{1} = ks{2}); 1: by auto => />.
    rcondf {1} ^if{2}. auto => /> *. smt(get_setE in_fsetU1).
    rcondf {1} ^if{3}. auto => /> *. by rewrite in_fsetU1.
    auto => /> &1 &2 *. smt(mem_set in_fsetU1).
  sp. seq 1 1: (#pre /\ r3{1} = ks{2}); 1: by auto => />.
  rcondf {1} ^if{2}. auto => /> *. smt(get_setE in_fsetU1).
  rcondf {1} ^if{3}. auto => /> *. by rewrite in_fsetU1.
  auto => /> &1 &2 *. smt(mem_set in_fsetU1).

+ proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // st' pt ir.
  rcondt {1} ^if. auto => />.
  sp. seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto => />.
  rcondf {1} ^if{3}. auto => /> *. smt(get_setE).
  if => //; auto => />; smt(mem_set in_fsetU1 pow_bij get_setE).

+ proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />. smt(get_setE).

+ proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // sk.
  auto => />. smt(get_setE).

+ proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // [s pt ir|s t k ir].
  + auto => />. smt(get_setE).
  auto => />. smt(get_setE).

+ proc; inline.
  sp; if => //.
  sp; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //; if => //.
  + auto => />. smt(get_setE).
  auto => />. smt(get_setE).

auto => />.
smt(emptyE). *)
qed.


(* ------------------------------------------------------------------------------------------ *)
(* Step 4: Moving sampling of the shared key. *)

(* Clearing the key out of the state *)
local op s_clear_k (s : pr_st_server instance_state) =
match s with
| Pending_mod _ _ _ => s
| Accepted_mod st t k ir => Accepted_mod st t witness ir
| Aborted_mod _ _ _ => s
end.

local op c_clear_k (s : pr_st_client instance_state) =
match s with
| Pending_mod _ _ _ => s
| Accepted_mod st t k ir => Accepted_mod st t witness ir
| Aborted_mod _ _ _ => s
end.

(* Equivalence of partnering notions after keys are cleared *)
local lemma c_eq_partners_ck tr sml smr: 
  (forall h, omap (fun (v: pr_st_server instance_state) => s_clear_k v) sml.[h] = smr.[h]) =>
untested_partner_c tr sml = untested_partner_c tr smr.
proof.
move=> eqsm @/untested_partner_c.
have ->: get_partners_c tr sml = get_partners_c tr smr.
+ rewrite /get_partners_c; apply: fsetP=> x; rewrite !mem_fdom.
  rewrite !mem_filter !domE -eqsm.
  by case: (sml.[x])=> /> [] @/s_clear_k /#.
have -> //: get_untested_partners_c tr sml = get_untested_partners_c tr smr.
rewrite /get_untested_partners_c; apply: fsetP=> x; rewrite !mem_fdom.
rewrite !mem_filter !domE -eqsm.
by case: (sml.[x])=> /> [] @/s_clear_k /#.
qed.

local lemma s_eq_partners_ck tr sml smr: 
  (forall h, omap (fun (v: pr_st_client instance_state) => c_clear_k v) sml.[h] = smr.[h]) =>
untested_partner_s tr sml = untested_partner_s tr smr.
proof.
move=> eqsm @/untested_partner_s.
have ->: get_partners_s tr sml = get_partners_s tr smr.
+ rewrite /get_partners_s; apply: fsetP=> x; rewrite !mem_fdom.
  rewrite !mem_filter !domE -eqsm.
  by case: (sml.[x])=> /> [] @/c_clear_k /#.
have -> //: get_untested_partners_s tr sml = get_untested_partners_s tr smr.
rewrite /get_untested_partners_s; apply: fsetP=> x; rewrite !mem_fdom.
rewrite !mem_filter !domE -eqsm.
by case: (sml.[x])=> /> [] @/c_clear_k /#.
qed.

local lemma c_eq_origins_ck tr sml smr: 
  (forall h, omap (fun (v: pr_st_server instance_state) => s_clear_k v) sml.[h] = smr.[h]) =>
untested_origins_c tr sml = untested_origins_c tr smr.
proof.
move=> eqsm; rewrite /untested_origins_c.
have ->: get_origins_c tr sml = get_origins_c tr smr.
+ rewrite /get_origins_c; apply: fsetP=> x; rewrite !mem_fdom.
  rewrite !mem_filter !domE -eqsm.
  by case: (sml.[x])=> /> [] @/s_clear_k /#.
have -> //: get_untested_origins_c tr sml = get_untested_origins_c tr smr.
rewrite /get_untested_origins_c; apply: fsetP=> x; rewrite !mem_fdom.
rewrite !mem_filter !domE -eqsm.
by case: (sml.[x])=> /> [] @/s_clear_k /#.
qed.

local lemma c_eq_fresh_ck tr sm1l sm1r sm2: 
  (forall h, omap (fun (v: pr_st_server instance_state) => s_clear_k v) sm1l.[h] = sm1r.[h]) =>
fresh_partner_c tr sm1l sm2 = fresh_partner_c tr sm1r sm2.
proof.
move=> eqsm; rewrite /fresh_partner_c.
have ->: get_fresh_partners_c tr sm1l sm2 = get_fresh_partners_c tr sm1r sm2.
+ rewrite /get_fresh_partners_c; apply: fsetP=> x; rewrite !mem_fdom.
  rewrite !mem_filter !domE -eqsm.
  by case: (sm1l.[x])=> /> [] @/s_clear_k /#.
have -> //: get_partners_c tr sm1l = get_partners_c tr sm1r.
rewrite /get_origins_c; apply: fsetP=> x; rewrite !mem_fdom.
rewrite !mem_filter !domE -eqsm.
by case: (sm1l.[x])=> /> [] @/s_clear_k /#.
qed.

local lemma s_eq_fresh_ck tr sml smr: 
  (forall h, omap (fun (v: pr_st_client instance_state) => c_clear_k v) sml.[h] = smr.[h]) =>
fresh_partner_s tr sml = fresh_partner_s tr smr.
proof.
move=> eqsm; rewrite /fresh_partner_s.
have ->: get_fresh_partners_s tr sml = get_fresh_partners_s tr smr.
+ rewrite /get_fresh_partners_s; apply: fsetP=> x; rewrite !mem_fdom.
  rewrite !mem_filter !domE -eqsm.
  by case: (sml.[x])=> /> [] @/c_clear_k /#.
have -> //: get_origins_s tr sml = get_origins_s tr smr.
rewrite /get_origins_s; apply: fsetP=> x; rewrite !mem_fdom.
rewrite !mem_filter !domE -eqsm.
by case: (sml.[x])=> /> [] @/c_clear_k /#.
qed.

lemma game3_RO bit &m: Pr[E_GAKE_nodhs(Game3, A).run(bit) @ &m : res] = Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(bit) @ &m : res].
proof. admit. (*
byequiv (: ={glob A, glob Red_ROM2} /\ arg{1} = bit /\ arg{2} = bit ==> _)  => //.
proc*.

rewrite equiv [{2} 1 -(ROSc.I2.FullEager.RO_LRO (Red_ROM2(A, ROSc.I1.RO)) _)]; 2: by move => _; exact dkey_ll.

inline; wp.
call (: ={b0, hm, servers, b_set, x_set, y_set, pk_set, m1_set, m2_set, bad1, bad2, hq, tq, badq}(Game3, Red_ROM2.AKE_O)
          /\ Game3.h1m{1} = ROSc.I1.RO.m{2} /\ Game3.h2m{1} = ROSc.I2.RO.m{2}
          /\ (forall h, omap (fun v => c_clear_k v) Game3.c_smap.[h]{1} = Red_ROM2.AKE_O.c_smap.[h]{2})
          /\ (forall h, omap (fun v => s_clear_k v) Game3.s_smap.[h]{1} = Red_ROM2.AKE_O.s_smap.[h]{2})
          /\ (forall i st pt ir, Game3.c_smap{1}.[i] = Some (Pending_mod st pt ir) 
                => pt.`2 = g ^ st.`2 /\ (exists b, ir = (b, false, false)))
          /\ (forall i st pt ir, Game3.s_smap{1}.[i] = Some (Pending_mod st pt ir) 
                => ir = (false, false, false))
          /\ (forall i st t k ir, Game3.c_smap{1}.[i] = Some (Accepted_mod st t k ir)
                => (exists k', Red_ROM2.AKE_O.c_smap{2}.[i] = Some (Accepted_mod st t k' ir))
                   /\ ((oget t.`2).`1 ^ st.`2, st.`1 ^ st.`2, st.`1, g ^ st.`2, (oget t.`2).`1) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[((oget t.`2).`1 ^ st.`2, st.`1 ^ st.`2, st.`1, g ^ st.`2, (oget t.`2).`1)])
          /\ (forall i st t k ir, Game3.s_smap{1}.[i] = Some (Accepted_mod st t k ir)
                => (exists k', Red_ROM2.AKE_O.s_smap{2}.[i] = Some (Accepted_mod st t k' ir))
                   /\ ((t.`1).`2 ^ (oget st.`2), (t.`1).`2 ^ st.`1, g ^ st.`1, (t.`1).`2, g ^ (oget st.`2)) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[((t.`1).`2 ^ (oget st.`2), (t.`1).`2 ^ st.`1, g ^ st.`1, (t.`1).`2, g ^ (oget st.`2))])
          /\ (forall x, x \in ROSc.I1.RO.m{2} <=> x \in ROSc.I2.RO.m{2})
          /\ (Game3.tested{1} <> None <=> Red_ROM2.AKE_O.tested{2} <> None)).

- proc; inline.
  sp; if => //.  
  + auto => /> &1 &2 *. smt(mem_set get_setE). 

- sim />.

- proc; inline.
  sp; if => //.
  sp; if => //.
  sp; match.
  + smt().
  + smt().
  + by auto=> />; smt(get_setE).
  move=> stl str; auto=> />.

- proc; inline.
  sp; if => //.
  sp; match = => // sko.
  match => //.
  + smt().
  + smt().
  seq 1 1: (#pre /\ ={sk}); 1:by auto.
  sp 3 3; if => //.
  swap {1} ^ts<$ @ 1; swap {1} ^ks<$ @ 2.
  swap {2} ^r0<$ @ 1; swap {2} ^r1<$ @ 2. 
  seq  2  2: (#pre /\ ts{1} = r0{2} /\ ks{1} = r1{2}); 1: by auto=> />.
  sp ^if & -1 ^if & -1; if {1} => //.
  + rcondt {1} ^if; 1: by auto => /#.
    rcondt {2} ^if; 1: by auto => /#.
    rcondt {2} ^if; 1: by auto => /#.
    sp 4 6; if => //; auto => /> &1 &2 *; smt(mem_set get_setE in_fsetU1).
  rcondf {1} ^if; 1: by auto => /#.
  rcondf {2} ^if; 1: by auto => /#.
  rcondf {2} ^if; 1: by auto => /#.
  auto => /> &1 &2.
  smt(mem_set get_setE).

- proc; inline.
  sp; if => //.
  sp; match => //.
  + smt().
  + smt().
  move=> stl str.
  match => //; 1..3: smt().
  move => st'l ptl irl st'r ptr irr.
  swap {1} ^ts<$ @ 1; swap {1} ^ks<$ @ 2.
  swap {2} ^r0<$ @ 1; swap {2} ^r1<$ @ 2.
  seq  2  2: (#pre /\ ts{1} = r0{2} /\ ks{1} = r1{2}); 1: by auto.
  sp ^if & -1   ^if & -1.
  seq  ^if{3} & -1   ^if{3} & -1: (#pre /\ ={t_A} /\ key{2} = witness /\ (x0{2} \in ROSc.I1.RO.m{2}) /\ key{1} = oget ROSc.I2.RO.m{2}.[m3{2}.`1 ^ sk_ce{2}, b{2} ^ sk_ce{2}, b{2}, g ^ sk_ce{2}, m3{2}.`1]).
  + if {1} => //.
    + rcondt {1} ^if; 1: by auto => /#.
      rcondt {2} ^if; 1: by auto => /#.
      rcondt {2} ^if; 1: by auto => /#. 
      by auto=> />; smt(mem_set get_setE).
    rcondf {1} ^if; 1: by auto => /#.
    rcondf {2} ^if; 1: by auto => /#.
    rcondf {2} ^if; 1: by auto => /#.
    by auto=> />; smt(mem_set get_setE).
  if=> //.
  + auto=> /> &1 &2 cstl cstr inv *. 
    have->: sk_ce{1} = sk_ce{2}. 
    + have := inv i{2}. 
      rewrite cstl cstr /c_clear_k //=.
    smt(mem_set get_setE pow_bij).
  + auto => /> &1 &2 *. smt(mem_set get_setE).
  auto => /> &1 &2 *. smt(mem_set get_setE).

- proc; inline.
  sp; if => //.
  sp; match=> //.
  + smt().
  + smt().
  move => stl str.
  match => //; 1..3: smt().
  move => st'l ptl kl irl st'r ptr kr irr.
  if => //.
  + auto=> />; 1: by smt(c_eq_partners_ck).
  rcondf{2} ^if; 1: by auto => /#.
  auto => /> &1 &2 *.
  by smt(get_setE mem_set).

- proc; inline.
  sp; if => //.
  sp; match=> //.
  + smt().
  + smt().
  move => stl str.
  match => //; 1..3: smt().
  move => st'l ptl kl irl st'r ptr kr irr.
  if => //.
  + auto=> />; 1: by smt(s_eq_partners_ck).
  rcondf{2} ^if; 1: by auto => /#.
  auto => /> &1 &2 *.
  by smt(get_setE mem_set).

- proc; inline.
  sp; if => //.
  sp; match => //.
  move => stl str.
  match = => //; 1: smt().
  move => kp.
  if => //.
  + move => /> &1 &2 hkp _ c_clear s_clear inv1 inv2 inv3 inv4 inv5 eq_dom nb1 nb2.
    split.
    + move => + j - /(_ j). 
      rewrite !domE -s_clear => />.
      case : (Game3.s_smap.[b{2}, j]{1}) => />.
      by smt(s_eq_partners_ck). 
    move => + j - /(_ j). 
    rewrite !domE -s_clear => />.
    case : (Game3.s_smap.[b{2}, j]{1}) => />.
    by smt(s_eq_partners_ck).
  by auto => />.
  
- proc; inline.
  sp; if => //.
  sp; match => //.
  + smt().
  + smt().
  move => stl str.
  match => //; 1..3: smt().
  + move => st'l ptl irl st'r ptr irr.
    auto => /> &1 &2 *. 
    by smt(c_eq_origins_ck get_setE mem_set).
  move => st'l ptl kl irl st'r ptr kr irr.
  if => //; 1: by smt(c_eq_partners_ck).
  auto => /> &1 &2.
  by smt(get_setE).

- proc; inline.
  sp; if => //.
  sp; match => //.
  + smt().
  + smt().
  move => stl str.
  match => //; 1..3: smt().
  move => st'l ptl kl irl st'r ptr kr irr.
  if => //.
  + by smt(s_eq_partners_ck).
  auto => /> &1 &2.
  by smt(get_setE).

- proc; inline.
  sp; if => //.
  sp; if => //. sp; match => //.
  + smt().
  + smt().
  move => stl str.
  match => //; 1..3: smt().
  move => st'l ptl kl irl st'r ptr kr irr.
  if => //.
  + auto => />.
    by smt(c_eq_fresh_ck).
  if => //.
  + auto => />.
    by smt(get_setE).
  auto => />.
  by smt(get_setE).

- proc; inline.
  sp; if => //.
  sp; if => //. sp; match => //.
  + smt().
  + smt().
  move => stl str.
  match => //; 1..3: smt().
  move => st'l ptl kl irl st'r ptr kr irr.
  if => //.
  + auto => />.
    by smt(s_eq_fresh_ck).
  if => //.
  + auto => />.
    by smt(get_setE).
  auto => />.
  by smt(get_setE).

by auto => />; smt(map_empty emptyE). *)
qed.


lemma LRO_game4 bit &m: Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(bit) @ &m : res] = Pr[E_GAKE_nodhs(Game4, A).run(bit) @ &m : res].
proof. admit. (*
byequiv => //.
proc*.
inline; wp.
call (: ={b0, hm, servers, c_smap, s_smap, tested, b_set, x_set, y_set, pk_set, m1_set, m2_set, bad1, bad2, hq, tq, badq}(Red_ROM2.AKE_O, Game4) 
           /\ ROSc.I1.RO.m{1} = Game4.h1m{2} /\ ROSc.I2.RO.m{1} = Game4.h2m{2}); try sim />.

+ proc; inline.
  sp; if => //.
  auto => />.

+ proc; inline.
  sp; if => //.
  sp; match = => // skb.
  match = => //.
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp; if => //; auto => />.

+ proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // st' pt ir.
  sp; seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto.
  auto => />.

+ proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // st' pt k ir.
  if => //.
  sp; seq 1 1: (#pre /\ r{1} = ks{2}); 1: by auto.
  if => //; auto => />; smt(get_setE).

+ proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // st' pt k ir.
  if => //.
  sp; seq 1 1: (#pre /\ r{1} = ks{2}); 1: by auto.
  if => //; auto => />; smt(get_setE).

+ proc; inline.
  sp; if => //.
  sp; if => //; match = => // st.
  match = => // st' pt k ir.
  if => //; if => //; auto => />; smt(get_setE).

+ proc; inline.
  sp; if => //.
  sp; if => //; match = => // st.
  match = => // st' pt k ir.
  if => //; if => //; auto => />; smt(get_setE).

auto => />. *)
qed.


(* Step 5: Turn the indistinguishability of real/ideal into probability of the bad event happening *)
op inv_Game4 (tested : int option, 
tq : (pkey * pkey * pkey * pkey * pkey) option, 
badq : bool, 
pks : pkey fset,
m1s : pkey fset,
m2s : pkey fset,
ssm : (pkey * int, pr_st_server instance_state) fmap, 
hq : (pkey * pkey * pkey * pkey * pkey) fset, 
csm : (int, pr_st_client instance_state) fmap,
h1m : (pkey * pkey * pkey * pkey * pkey, tag) fmap, 
h2m : (pkey * pkey * pkey * pkey * pkey, key) fmap, 
servers : (pkey, server_state) fmap) = 
       (tested = None <=> tq = None)
        /\ (badq <=> (tq <> None /\ oget tq \in hq))
        /\ (forall x y b, tq = Some (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x b), g ^ b, g ^ x, g ^ y) 
             => (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x b), g ^ b, g ^ x, g ^ y) \in h2m 
               /\ ((exists i tag key ir, i \in csm /\ csm.[i] = Some (Accepted_mod (g ^ b, x) ((g ^ b, g ^ x), Some (g ^ y, tag)) key ir)
                     /\ get_ir_test (oget csm.[i]))
                  \/ (exists i tag key ir, i \in ssm /\ ssm.[i] = Some (Accepted_mod (b, Some y) ((g ^ b, g ^ x), Some (g ^ y, tag)) key ir)
                     /\ get_ir_test (oget ssm.[i]))))
        /\ (forall i st t k ir, csm.[i] = Some (Accepted_mod st t k ir) => tested = None => !ir.`3)
        /\ (forall i st t k ir, ssm.[i] = Some (Accepted_mod st t k ir) => tested = None => !ir.`3)
        /\ (forall sk, g ^ sk \in (pks `|` m1s `|` m2s) => sk \in dt)
        /\ (forall i i' m1 m2 m2', csm.[i] <> None /\ get_trace (oget csm.[i]) = Some (m1, m2)
                => csm.[i'] <> None /\ get_trace (oget csm.[i']) = Some (m1, m2')
                => i = i')
        /\ (forall i tr pks, csm.[i] <> None 
                => get_trace (oget csm.[i]) = Some (pks, tr) 
                => pks.`2 \in m1s)
        /\ (forall i i' m1 m2 tag m1' tag', ssm.[i] <> None /\ get_trace (oget ssm.[i]) = Some (m1, Some (m2, tag))
                => ssm.[i'] <> None /\ get_trace (oget ssm.[i']) = Some (m1', Some (m2, tag'))
                => i = i')
        /\ (forall i tr pk tag, ssm.[i] <> None 
                => get_trace (oget ssm.[i]) = Some (tr, Some (pk, tag)) 
                => pk \in m2s)
        /\ (forall i st pt ir, csm.[i] = Some (Pending_mod st pt ir)
                => (pt.`1 = st.`1) /\ (pt.`2 = g ^ st.`2) /\ (pt.`2 \in m1s) /\ !ir.`3)
        /\ (forall i st t k ir, csm.[i] = Some (Accepted_mod st t k ir)
                => ((t.`1).`1 = st.`1) /\ ((t.`1).`2 = g ^ st.`2) /\ (exists pk tag, (t.`2 = Some (pk, tag))) 
                      /\ ((oget t.`2).`1 ^ st.`2, st.`1 ^ st.`2, st.`1, g ^ st.`2, (oget t.`2).`1) \in h1m 
                      /\ (oget t.`2).`2 = oget h1m.[((oget t.`2).`1 ^ st.`2, st.`1 ^ st.`2, st.`1, g ^ st.`2, (oget t.`2).`1)])
        /\ (forall i st t k ir, ssm.[i] = Some (Accepted_mod st t k ir)
                => ((oget t.`2).`1 = g ^ oget st.`2) /\ ((t.`1).`1 = g ^ st.`1) 
                      /\ (exists sk, st.`2 = Some sk) /\ (exists pk tag, (t.`2 = Some (pk, tag)))
                      /\ ((t.`1).`2 ^ (oget st.`2), (t.`1).`2 ^ st.`1, g ^ st.`1, (t.`1).`2, g ^ (oget st.`2)) \in h1m
                      /\ (oget t.`2).`2 = oget h1m.[((t.`1).`2 ^ (oget st.`2), (t.`1).`2 ^ st.`1, g ^ st.`1, (t.`1).`2, g ^ (oget st.`2))])
        /\ (forall x y b, (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x b), g ^ b, g ^ x, g ^ y) \in h2m
                => (exists i tag key ir, csm.[i] = Some (Accepted_mod (g ^ b, x) ((g ^ b, g ^ x), Some (g ^ y, tag)) key ir)
                     /\ (get_ir_sess (oget csm.[i]) \/ get_ir_test (oget csm.[i])))
                  \/ (exists i tag key ir, ssm.[i] = Some (Accepted_mod (b, Some y) ((g ^ b, g ^ x), Some (g ^ y, tag)) key ir)
                     /\ (get_ir_sess (oget ssm.[i]) \/ get_ir_test (oget ssm.[i])))
                  \/ (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x b), g ^ b, g ^ x, g ^ y) \in hq)
        /\ (forall b sk, b \in servers => (get_skey (oget servers.[b])) = Some sk => b = g ^ sk).


hoare Game4_inv_h: Game4.h:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
auto => />.
smt(get_setE in_fsetU1 mem_set).
qed.

hoare Game4_inv_init_s: Game4.init_s:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
auto => />.
smt(get_setE in_fsetU1 pow_bij in_fsetU).
qed.

hoare Game4_inv_send_msg1: Game4.send_msg1:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
sp; if => //.
match => //.
seq 1: (#pre /\ sk \in dt); 1: by auto => />.
sp 3; if => //.
+ auto => /> &1 4? inv 4? inv2 5? inv3 *.
  do split; ~1,4,8: smt(get_setE in_fsetU1 in_fsetU pow_bij mem_set).
  + move => x0 y0 b0 tqeq.
    have := inv x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set).  
  + move => // i0 i'.
    case (i0 = i{1}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = i{1}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      move => m10 m2 m2' [] m10eq m2eq trs.
      have := inv2 i' None (m1{1}, g ^ sk{1}).
      by smt(pow_bij).
    case (i' = i{1}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => stnn.
    rewrite i'eq !get_set_sameE //=.
    by smt(pow_bij).
  move => x0 y0 b0 x0in.
  have := inv3 x0 y0 b0 x0in.
  move => [H1|[H2|H3]].
  + left.
    move : H1 => [i'] t' k' ir' H1.
    exists i'. 
    smt(get_setE).
  + smt().
  by smt().
auto => /> &1 *.
do split; by smt(get_setE in_fsetU1 in_fsetU pow_bij).
qed.

hoare Game4_inv_send_msg2: Game4.send_msg2:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
sp; match => //.
match => //.
seq 1: (#pre /\ sk \in dt); 1: by auto => />.
sp 3; if => //.
+ sp; seq 1: (#pre /\ ts \in dtag); 1: by auto=> />.
  if => //.
  + sp 3; if => //.
    + auto => /> &1 7? inv 6? inv2 3? inv3 inv4 *.
    do split; ~1,7,8: smt(get_setE in_fsetU1 in_fsetU pow_bij mem_set).
    + move => x0 y0 b0 tqeq.
      have := inv x0 y0 b0 tqeq.
      move => [] H1 [H2|H3].
      + smt().
      split; 1: by smt().
      move : H3 => [i'] t k ir H3.
      right. exists i'.
      by smt(get_setE).
    + move => i st t k ir.
      case (i = (b,j){1}) => bjeq.
      rewrite get_setE bjeq //=.
      rewrite get_setE //=.
      move => [#] steq teq keq ireq.
      split. smt(get_setE pow_bij). 
      split.
      rewrite -teq -steq //=.
      have := inv4 b{1} sk_b{1}.
      smt().
      smt(get_setE).
      by smt(get_setE).
    move => x0 y0 b0 x0in.
    have := inv3 x0 y0 b0 x0in.
    move => [H1|[H2|H3]].
    + smt().
    + right. left.
      move : H2 => [i'] t k ir H2.
      exists i'. 
      smt(get_setE).
    by smt().
  auto => /> &1 7? inv 6? inv2 3? inv3 inv4 *.
  do split; ~1,7,8: smt(get_setE in_fsetU1 in_fsetU pow_bij mem_set).
  + move => x0 y0 b0 tqeq.
    have := inv x0 y0 b0 tqeq.
    move => [] H1 [H2|H3].
    + smt().
    split; 1: by smt().
    move : H3 => [i'] t k ir H3.
    right. exists i'.
    by smt(get_setE).
  + move => i st t k ir.
    case (i = (b,j){1}) => bjeq.
    rewrite get_setE bjeq //=.
    rewrite get_setE //=.
    move => [#] steq teq keq ireq.
    split. smt(get_setE pow_bij). 
    split.
    rewrite -teq -steq //=.
    have := inv4 b{1} sk_b{1}.
    smt().
    smt(get_setE).
    by smt(get_setE).
  move => x0 y0 b0 x0in.
  have := inv3 x0 y0 b0 x0in.
  move => [H1|[H2|H3]].
  + smt().
  + right. left.
    move : H2 => [i'] t k ir H2.
    exists i'. 
    smt(get_setE).
  by smt().
auto => /> &1 6? inv 6? inv2 3? inv3 inv4 *.
do split; ~1,6,7: smt(get_setE in_fsetU1 in_fsetU pow_bij mem_set).
+ move => x0 y0 b0 tqeq.
  have := inv x0 y0 b0 tqeq.
  move => [] H1 [H2|H3].
  + smt().
  split; 1: by smt().
  move : H3 => [i'] t k ir H3.
  right. exists i'.
  by smt(get_setE).
  move => i st t k ir.
  case (i = (b,j){1}) => bjeq.
  rewrite get_setE bjeq //=.
  move => [#] steq teq keq ireq.
  split. smt(get_setE pow_bij). 
  split.
  rewrite -teq -steq //=.
  have := inv4 b{1} sk_b{1}.
  smt().
  smt(get_setE).
  by smt(get_setE).
move => x0 y0 b0 x0in.
have := inv3 x0 y0 b0 x0in.
move => [H1|[H2|H3]].
+ smt().
+ right. left.
  move : H2 => [i'] t k ir H2.
  exists i'. 
  smt(get_setE).
by smt().
qed.

hoare Game4_inv_send_msg3: Game4.send_msg3:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
sp; match => //.
match => //.
sp; seq 1: (#pre /\ ts \in dtag); 1: by auto=> />.
if => //.
+ sp 3; if => //.
  + sp 1; if => //.
    + sp 1; if => //.
      + auto => /> &1 *. do split; by smt(get_setE).
      auto => /> &1 *. do split; by smt(get_setE).
    if => //.
    + auto => /> &1 *. do split; by smt(get_setE).
    auto => /> &1 *. do split; by smt(get_setE).
admit. admit.
(*
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    move => x0 y0 b0 x0in.
    have := inv5 x0 y0 b0 x0in.
    move => [H1|[H2|H3]].
    + left.
      move : H1 => [i'] t' k' ir' H1.
      exists i'. 
      smt(get_setE).
    + smt().
    by smt().
  move => *. 
    do split; ~2,9: by smt(get_setE).
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    move => x0 y0 b0 x0in.
    have := inv5 x0 y0 b0 x0in.
    move => [H1|[H2|H3]].
    + left.
      move : H1 => [i'] t' k' ir' H1.
      exists i'. 
      smt(get_setE).
    + smt().
    by smt().
  move => *. split. move => *.
    do split; ~2,9: by smt(get_setE).
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    move => x0 y0 b0 x0in.
    have := inv5 x0 y0 b0 x0in.
    move => [H1|[H2|H3]].
    + left.
      move : H1 => [i'] t' k' ir' H1.
      exists i'. 
      smt(get_setE).
    + smt().
    by smt().
  move => *. 
    do split; ~2,9: by smt(get_setE).
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    move => x0 y0 b0 x0in.
    have := inv5 x0 y0 b0 x0in.
    move => [H1|[H2|H3]].
    + left.
      move : H1 => [i'] t' k' ir' H1.
      exists i'. 
      smt(get_setE).
    + smt().
    by smt().
    auto => /> &1 &2 ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *. split. move => *. split. move => *.
    do split; ~2,9: by smt(get_setE). 
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~2,9: by smt(get_setE). 
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
 move => *. split. move => *.
    do split; ~2,9: by smt(get_setE). 
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~2,9: by smt(get_setE). 
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
  sp ^if & -1 ^if & -1; if => //.
  + auto => /> &1 &2 ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *. split. move => *. split. move => *.
    do split; ~8: by smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~8: by smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
move => *. split. move => *.
    do split; ~8: by smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~8: by smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
  auto => /> &1 &2 ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *. split. move => *. split. move => *.
    do split; ~2,4,8: by smt(mem_set get_setE).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set). 
    + clear inv2 inv5. smt(mem_set get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~2,4,8: by smt(mem_set get_setE).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set). 
    + clear inv2 inv5. smt(mem_set get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
move => *. split. move => *.
    do split; ~2,4,8: by smt(mem_set get_setE).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set). 
    + clear inv2 inv5. smt(mem_set get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
move => *.
    do split; ~2,4,8: by smt(mem_set get_setE).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set). 
    + clear inv2 inv5. smt(mem_set get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().

admit.*)
qed.

hoare Game4_inv_c_rev_skey: Game4.c_rev_skey:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
sp; match => //.
match => //.
if => //.
sp; seq 1: (#pre); 1: by auto=> />.
if => //.
+ auto => /> &1 &2 ? inv2 ? ? ? inv3 ? ? ? ? ? ? inv *.
  do split; ~1,3,7: smt(get_setE).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set).
  + move => // i0 i'.
    case (i0 = i{1}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = i{1}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      move => m10 m2 m2' trace stnn.
      have := inv3 i0 i{1}.
      smt().
    case (i' = i{1}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => m10 m2 m2' stnn.
    rewrite i'eq !get_set_sameE //=.
    have := inv3 i0 i{1}.
    smt().
  move => x0 y0 b0 x0in.
  case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) 
               = ((oget t'{1}.`2).`1 ^ st'{1}.`2, st'{1}.`1 ^ st'{1}.`2, st'{1}.`1, g ^ st'{1}.`2, (oget t'{1}.`2).`1)) 
      => [[] in1 in2 in3 in4 in5|neq].
  + left.
    exists i{1} (oget t'{1}.`2).`2 k'{1} (ir'{1}.`1, true, ir'{1}.`3).
    smt(get_setE pow_bij expgK).
  have := inv x0 y0 b0.
  have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{1}; 1: by smt(mem_set). 
  move => [H1|H2].
  + left. 
    move : H1 => [i'] t k ir H1.
    exists i'. 
    smt(get_setE).
  by smt().
auto => /> &1 &2 inv6 inv2 ? ? ? inv5 ? inv3 ? ? inv7 inv4 inv ? ? ? fresh *.
do split; ~1,3,7: smt(get_setE).
+ move => x0 y0 b0 tqeq.
  have := inv2 x0 y0 b0 tqeq.
  move => [H1] [H2|H3]. 
  + split; 1: by smt(mem_set).
    left.
    move : H2 => [i'] t k ir'' H2.
    exists i'. 
    by smt(get_setE).     
  smt(mem_set).
+ move => // i0 i'.
  case (i0 = i{1}) => ieq.
  + rewrite ieq get_set_sameE //=.
    case (i' = i{1}) => i'eq; 1: by rewrite i'eq.
    rewrite get_set_neqE //=.
    move => m10 m2 m2' trace stnn.
    have := inv5 i0 i{1}.
    smt().
  case (i' = i{1}) => i'eq; 2: by smt(get_set_neqE).
  rewrite get_set_neqE //=.
  move => m10 m2 m2' stnn.
  rewrite i'eq !get_set_sameE //=.
  have := inv5 i0 i{1}.
  smt().
move => x0 y0 b0 x0in.
case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) 
       = ((oget t'{1}.`2).`1 ^ st'{1}.`2, st'{1}.`1 ^ st'{1}.`2, st'{1}.`1, g ^ st'{1}.`2, (oget t'{1}.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
+ left.
  exists i{1} (oget t'{1}.`2).`2 k'{1} (ir'{1}.`1, true, ir'{1}.`3).
  smt(get_setE pow_bij expgK).
have := inv x0 y0 b0.
have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{1}; 1: by smt(mem_set). 
move => [H1|H2].
+ left. 
  move : H1 => [i'] t k ir H1.
  exists i'. 
  smt(get_setE).
by smt().
qed.

hoare Game4_inv_s_rev_skey: Game4.s_rev_skey:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
sp; match => //.
match => //.
if => //.
sp 1; seq 1: (#pre); 1: by auto=> />.
if => //.
+ auto => /> &1 ? inv6 inv2 c3 c4 _ ? ? ? ? ? ? inv5 inv inv3 ? inv4 *.
  do split; ~1,3,6: smt(get_setE mem_set).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]; 1: smt(mem_set).
    split; 1: by smt(mem_set).
    right.
    move : H3 => [i'] t k ir'' H3.
    exists i' t k ir''.
    case (i' = (b, j){1}) => i'eq; smt(get_setE).
  + move => // i0 i'. clear c3 c4 inv inv2 inv3 inv4.
    case (i0 = (b, j){1}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = (b, j){1}) => i'eq; 1: by rewrite i'eq.
      by rewrite get_set_neqE /#.
    case (i' = (b, j){1}) => i'eq; 2: by smt(get_set_neqE).
    rewrite i'eq get_set_sameE //=.
    rewrite get_set_neqE /#.
  move => x0 y0 b0 x0in.
  case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) 
         = ((t'{1}.`1).`2 ^ oget st'{1}.`2, (t'{1}.`1).`2 ^ st'{1}.`1, g ^ st'{1}.`1, (t'{1}.`1).`2, (oget t'{1}.`2).`1)) 
      => [[] in1 in2 in3 in4 in5|neq].
  + right. left.
    exists (b, j){1} (oget t'{1}.`2).`2 k'{1} (ir'{1}.`1, true, ir'{1}.`3).
    smt(get_setE pow_bij expgK).
  have := inv x0 y0 b0.
  have->: (g ^ (x0 * y0), g ^ (x0 * b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{1}; 1: by smt(mem_set). 
  simplify.
  move => [H1|[H2|H3]].
  + by smt().
  + right; left. 
    move : H2 => [i'] t k ir H2.
    exists i' t k ir.
    case (i' = (b, j){1}) => bjeq; 2: by smt(get_setE).
    rewrite bjeq.
    have : get_trace (oget Game4.s_smap{1}.[b{1}, j{1} <- Accepted_mod st'{1} t'{1} k'{1} (ir'{1}.`1, true, ir'{1}.`3)].[b{1}, j{1}]) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]) by smt(get_setE).
    smt(get_setE mem_set).
  by smt().
auto => /> &1 ? inv4 inv2 ? ? _ inv3 ? inv5 ? ? inv7 inv8 inv ? inv6 *.
do split; ~1,3,6: smt(get_setE mem_set).
+ move => x0 y0 b0 tqeq.
  have := inv2 x0 y0 b0 tqeq.
  move => [H1] [H2|H3]; 1: smt(mem_set).
  split. smt(mem_set).
  right.
  move : H3 => [i'] t k ir'' H3.
  exists i' t k ir''. 
  have : get_trace (oget (Some (Accepted_mod st'{1} t'{1} k'{1} (ir'{1}.`1, true, ir'{1}.`3)))) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]); 1: by smt().
  case (i' = (b,j){1}); smt(get_setE).
+ move => // i0 i'.
  case (i0 = (b, j){1}) => ieq.
  + rewrite ieq get_set_sameE //=.
    case (i' = (b, j){1}) => i'eq; 1: by rewrite i'eq.
    rewrite get_set_neqE //=.
    have : get_trace (oget (Some (Accepted_mod st'{1} t'{1} k'{1} (ir'{1}.`1, true, ir'{1}.`3)))) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]); 1: by smt().
    smt().
  case (i' = (b, j){1}) => i'eq; 2: by smt(get_set_neqE).
  rewrite get_set_neqE //=.
  move => m1 m2 tag m1' tag' stnn.
  rewrite i'eq !get_set_sameE.
  have : get_trace (oget (Some (Accepted_mod st'{1} t'{1} k'{1} (ir'{1}.`1, true, ir'{1}.`3)))) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]); 1: by smt().
  smt().
move => x0 y0 b0 x0in.
case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) 
         = ((t'.`1).`2 ^ oget st'.`2, (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, (oget t'.`2).`1){1}) 
       => [[] in1 in2 in3 in4 in5|neq].
+ right. left.
  exists (b, j){1} (oget t'{1}.`2).`2 k'{1} (ir'{1}.`1, true, ir'{1}.`3).
  smt(get_setE mem_set pow_bij expgK).
have := inv x0 y0 b0.
have->: (g ^ (x0 * y0), g ^ (x0 * b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{1}; 1: by smt(mem_set). 
simplify.
move => [H1|[H2|H3]].
+ by smt().
+ right; left. 
  move : H2 => [i'] t k ir H2.
  exists i' t k ir. 
  case (i' = (b,j){1}); 2: smt(get_setE mem_set).
  have : get_trace (oget Game4.s_smap{1}.[b{1}, j{1} <- Accepted_mod st'{1} t'{1} k'{1} (ir'{1}.`1, true, ir'{1}.`3)].[b{1}, j{1}]) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]) by smt(get_setE).
  smt(get_setE mem_set).
by smt().
qed.

hoare Game4_inv_rev_ltkey: Game4.rev_ltkey:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
sp; match => //.
match => //.
if => //.
auto => /> &1 &2 13? inv 4?.
move => b0 sk0.
case (b0 = b{1}) => beq.
+ rewrite beq mem_set //=.
  rewrite get_setE //=.
  have := inv b{1} sk{1}.
  smt(get_setE mem_set).
smt(get_setE mem_set).
qed.

hoare Game4_inv_c_rev_ephkey: Game4.c_rev_ephkey:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
sp; match => //.
match => //.
if => //.
+ auto => /> &1 ? ? inv2 ? ? _ inv3 ? ? ? ? ? ? inv *.
  do split; ~1,3,7: smt(get_setE mem_set).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split. smt().
      left.
      move : H2 => [i'] t k ir' H2.
      exists i'. 
      by smt(get_setE).     
    smt().
  + move => // i0 i'.
    case (i0 = i{1}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = i{1}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      move => m10 m2 m2' trace stnn.
      have := inv3 i0 i'.
      smt().
    case (i' = i{1}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => m10 m2 m2' stnn.
    rewrite i'eq !get_set_sameE //=.
    have := inv3 i0 i'.
    smt().
  move => x0 y0 b0 x0in.
  have := inv x0 y0 b0.
  rewrite x0in //=.
  move => [H1|H2].
  + left.
    move : H1 => [i'] t k ir' H1.
    exists i'. 
    by smt(get_setE).
  by smt().
if => //.
auto => /> &1 ? inv3 inv2 ? ? _ ? ? ? ? ? ? ? inv *.
do split; ~1,3,7: smt(get_setE mem_set).
+ move => x0 y0 b0 tqeq.
  have := inv2 x0 y0 b0 tqeq.
  move => [H1] [H2|H3].
  + split. smt().
    left.
    move : H2 => [i'] t' k' ir' H2.
    exists i'. 
    by smt(get_setE).     
  smt().
+ clear inv inv2 inv3. by smt(get_setE).
move => x0 y0 b0 x0in.
have := inv x0 y0 b0.
rewrite x0in //=.
move => [H1|H2].
+ left. 
  move : H1 => [i'] t' k' ir' H1.
  exists i'.
  by smt(get_setE).
by smt().
qed.

hoare Game4_inv_s_rev_ephkey: Game4.s_rev_ephkey:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
sp; if => //.
sp; match => //.
match => //.
if => //; if => //.
+ auto => /> &1 ? inv6 inv2 c2 c3 _ ? ? inv5 ? ? ? ? inv inv3 inv4 *.
  do split; ~1,3,4,6: smt(get_setE mem_set).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    smt().
    split. smt().
    right.
    move : H3 => [i'] t k ir'' H3.
    case ((b, j){1} = i') => i'eq.
    + have : Game4.s_smap{1}.[b{1}, j{1}] = Game4.s_smap{1}.[i']; 1: by smt().
      move => H2.
      exists i'{1} t{1} k{1} (true, ir''{1}.`2, ir''{1}.`3).
      by smt(get_setE).
    exists i' t k ir''.
    by smt(get_setE).
  + move => // i0 i'.
    case (i0 = (b, j){1}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = (b, j){1}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      have : get_trace (oget (Some (Accepted_mod st0{1} t{1} k{1} (true, ir{1}.`2, ir{1}.`3)))) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]); 1: by smt().
      by smt().
    case (i' = (b, j){1}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => m1 m2 tag m1' tag' stnn.
    rewrite i'eq !get_set_sameE.
    have : get_trace (oget (Some (Accepted_mod st0{1} t{1} k{1} (true, ir{1}.`2, ir{1}.`3)))) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]); 1: by smt().
    by smt().
  + have : get_trace (oget (Some (Accepted_mod st0{1} t{1} k{1} (true, ir{1}.`2, ir{1}.`3)))) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]); 1: by smt().
    by smt(get_setE). 
  move => x0 y0 b0 x0in.
  have := inv x0 y0 b0.
  rewrite x0in //=.
  move => [H1|[H2|H3]].
  + by smt().
  + right; left.
    move : H2 => [i'] t k'' ir'' H2.
    case ((b, j){1} = i') => i'eq.
      have : Game4.s_smap{1}.[b{1}, j{1}] = Game4.s_smap{1}.[i']; 1: by smt().
      move => H1.
      exists i' t k'' (true, ir''.`2, ir''.`3).
      by smt(get_setE).
    exists i' t k'' ir''.
    by smt(get_setE). 
  by smt().
auto => /> &1 ? inv6 inv2 c2 c3 _ ? ? inv5 ? ? ? ? inv inv3 inv4 *.
do split; ~1,3,4,6: smt(get_setE mem_set).
+ move => x0 y0 b0 tqeq.
  have := inv2 x0 y0 b0 tqeq.
  move => [H1] [H2|H3]. 
  smt().
  split. smt().
  right.
  move : H3 => [i'] t k ir'' H3.
  case ((b, j){1} = i') => i'eq.
  + have : Game4.s_smap{1}.[b{1}, j{1}] = Game4.s_smap{1}.[i']; 1: by smt().
    move => H2.
    exists i'{1} t{1} k{1} (true, ir''{1}.`2, ir''{1}.`3).
    by smt(get_setE).
  exists i' t k ir''.
  by smt(get_setE).
+ move => // i0 i'.
  case (i0 = (b, j){1}) => ieq.
  + rewrite ieq get_set_sameE //=.
    case (i' = (b, j){1}) => i'eq; 1: by rewrite i'eq.
    rewrite get_set_neqE //=.
    have : get_trace (oget (Some (Accepted_mod st0{1} t{1} k{1} (true, ir{1}.`2, ir{1}.`3)))) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]); 1: by smt().
    by smt().
  case (i' = (b, j){1}) => i'eq; 2: by smt(get_set_neqE).
  rewrite get_set_neqE //=.
  move => m1 m2 tag m1' tag' stnn.
  rewrite i'eq !get_set_sameE.
  have : get_trace (oget (Some (Accepted_mod st0{1} t{1} k{1} (true, ir{1}.`2, ir{1}.`3)))) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]); 1: by smt().
  by smt().
+ have : get_trace (oget (Some (Accepted_mod st0{1} t{1} k{1} (true, ir{1}.`2, ir{1}.`3)))) = get_trace (oget Game4.s_smap{1}.[b{1}, j{1}]); 1: by smt().
  by smt(get_setE). 
move => x0 y0 b0 x0in.
have := inv x0 y0 b0.
rewrite x0in //=.
move => [H1|[H2|H3]].
+ by smt().
+ right; left.
  move : H2 => [i'] t k'' ir'' H2.
  case ((b, j){1} = i') => i'eq.
    have : Game4.s_smap{1}.[b{1}, j{1}] = Game4.s_smap{1}.[i']; 1: by smt().
    move => H1.
    exists i' t k'' (true, ir''.`2, ir''.`3).
    by smt(get_setE).
  exists i' t k'' ir''.
  by smt(get_setE). 
by smt().
qed.

hoare Game4_inv_c_test: Game4.c_test:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
admit.
qed.

hoare Game4_inv_s_test: Game4.s_test:
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers)
==>
    (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers).
proof.
proc; inline.
admit.
qed.


lemma interestingbit &m: `|Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : res] - Pr[E_GAKE_nodhs(Game4, A).run(true) @ &m : res]| <= Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : Game4.badq].
proof. admit. (*
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game4.badq => //; first last.
+ smt().
symmetry; proc; inline.
wp.
call (: Game4.badq
      , ={servers, c_smap, s_smap, tested, b_set, x_set, y_set, pk_set, m1_set, m2_set, hm, bad1, bad2, h1m, hq, tq, badq}(Game4, Game4)
        /\ (Game4.tq{1} = None => ={Game4.h2m})
        /\ (forall x, Game4.tq{1} = Some x => eq_except (pred1 x) Game4.h2m{1} Game4.h2m{2})
        /\ Game4.b0{1} = false /\ Game4.b0{2} = true
        /\ (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.pk_set Game4.m1_set Game4.m2_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.servers){2}
        /\ (forall x, x \in Game4.h2m{1} <=> x \in Game4.h2m{2})
      , ={badq}(Game4, Game4)) => //; last first.

- auto => />.
split; 1: by smt(emptyE in_fset0 in_fsetU).
move => ntc nts ninkps injc pkins injs trs pc acc acs inv skpk rl rr al bl b1l b2l bql csl hql xl yl pkl m1l m2l ssl sl tl tql h1ml h2ml ar br b1r b2r bqr csr hqr xr yr pkr m1r m2r ssr sr tr tqr h1mr h2mr. 
by case : (!bqr) => />. 

- exact A_ll.

- proc; inline.
  sp; if => //.
  sp; seq 1 1: (#pre /\ t{1} = t{2}); 1: by auto=> />.
  if => //.
  + sp; seq 1 1: (#pre /\ ={k}); 1: by auto => />.
    if => //; auto => /> &1 &2 *; by smt(get_setE in_fsetU1 mem_set).
  seq 1 1: (#pre /\ ={k}); 1: by auto => />.
  if => //; auto => /> &1 &2 *; by smt(get_setE in_fsetU1 mem_set).
- move => &2 badq; proc*; inline. 
  sp; if => //; auto => />. 
  rewrite dkey_ll dtag_ll //=. smt().
- move => &1; proc*; inline.
  sp; if => //; auto.
  rewrite dkey_ll dtag_ll //=. smt(). 

- proc.
  sp; if => //.
  auto => /> &1 &2 *.
  smt(in_fsetU1 in_fsetU pow_bij get_setE).
- move => &2 badq; proc.
  sp; if => //; auto.
  rewrite dt_ll //=.
- move => &1; proc.
  sp; if => //; auto => />. 
  by rewrite dt_ll.
 
- proc; inline.
  sp; if => //.
  sp; if => //.
  sp; match = => //.
  seq 1 1: (#pre /\ ={sk} /\ sk{2} \in dt); 1: by auto => />.
  sp 3 3; if => //.
  + auto => /> &1 &2 ? ? ? _ ? ? ? ? ? inv4 ? ? ? ? inv ? ? ? inv3 inv5 inv2 inv6 inv7 *.
    do split; 1,3,4,6..8: by smt(get_setE in_fsetU1 in_fsetU pow_bij).
    + move => x0 y0 b0 tqeq.
      have := inv4 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).  
    + move => // i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m10 m2 m2' [] m10eq m2eq trs.
        have := inv i' None (m1{2}, g ^ sk{2}).
        by smt(pow_bij).
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => stnn.
      rewrite i'eq !get_set_sameE //=.
      by smt(pow_bij).
    move => x0 y0 b0 x0in.
    have := inv2 x0 y0 b0 x0in.
    move => [H1|[H2|H3]].
    + left.
      move : H1 => [i'] t' k' ir' H1.
      exists i'. 
      smt(get_setE).
    + smt().
    by smt().
  auto => /> &1 &2 *.
  do split; by smt(get_setE in_fsetU1 in_fsetU pow_bij).
- move => &2 bad.
  proc; sp; if => //. 
  sp; if => //.
  match; auto => />.
  rewrite dt_ll. smt().
- move => &1. 
  proc; sp; if => //. 
  sp; if => //.
  sp; match; auto => />.
  by rewrite dt_ll.
  
- proc; inline.
  sp; if => //.
  sp; match = => // sk_s.
  match = => //.
  seq 1 1: (#pre /\ ={sk} /\ sk{2} \in dt); 1: by auto=> />.
  sp 3 3; if => //.
  sp; seq 1 1: (#pre /\ ={ts}); 1: by auto=> />.
  if => //.
  + sp 3 3; if => //.
    + auto => /> &1 &2 ? kps ? ? ? _ ? _ ? ? c1 ? ? inv5 ? ? ? ? ? ? inv ? inv2 inv8 inv6 inv4 *.
      do split; ~2,8,9: by smt(get_setE in_fsetU1 in_fsetU pow_bij).
      + clear inv8.
        move => x0 y0 b0 tqeq.
        have := inv5 x0 y0 b0 tqeq.
        move => [] H1 [H2|H3].
        + smt().
        split; 1: by smt().
        move : H3 => [i'] t k ir H3.
        right. exists i'.
        by smt(get_setE).
      + move => i st t k ir.
        case (i = (b,j){2}) => bjeq.
        rewrite get_setE bjeq //=.
        rewrite get_setE //=.
        move => [#] steq teq keq ireq.
        split. smt(get_setE pow_bij). 
        split.
        rewrite -teq -steq //=.
        have := inv4 b{2} sk_s.
        smt().
        smt(get_setE).
        by smt(get_setE).
      clear inv8.
      move => x0 y0 b0 x0in.
      have := inv6 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + smt().
      + right. left.
        move : H2 => [i'] t k ir H2.
        exists i'. 
        smt(get_setE).
      by smt().
    auto => /> &1 &2 ? kps ? ? ? _ ? _ ? ? c1 ? ? inv5 ? ? ? ? ? ? inv ? inv2 inv8 inv6 inv4 *.
    do split; ~2,8,9: by smt(get_setE in_fsetU1 in_fsetU pow_bij).
    + move => x0 y0 b0 tqeq.
      have := inv5 x0 y0 b0 tqeq.
      move => [] H1 [H2|H3].
      + smt().
      split; 1: by smt().
      move : H3 => [i'] t k ir H3.
      right. exists i'.
      by smt(get_setE).
move => i st t k ir.
case (i = (b,j){2}) => bjeq.
rewrite get_setE bjeq //=.
rewrite get_setE //=.
move => [#] steq teq keq ireq.
split. smt(get_setE pow_bij). 
split.
rewrite -teq -steq //=.
have := inv4 b{2} sk_s.
smt().
smt(get_setE).
by smt(get_setE).
    clear inv8.
    + move => x0 y0 b0 x0in.
      have := inv6 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + smt().
      + right. left.
        move : H2 => [i'] t k ir H2.
        exists i'. 
        smt(get_setE).
      by smt().
  sp 2 2; if => //.
  + auto => /> &1 &2 kps ? ? _ ? _ ? ? ? c1 ? ? inv5 ? ? ? ? ? ? inv2 ? ? inv8 inv inv4 *.
    do split; ~2,7,8: by smt(get_setE in_fsetU1 in_fsetU pow_bij).
    + move => x0 y0 b0 tqeq.
      have := inv5 x0 y0 b0 tqeq.
      move => [] H1 [H2|H3].
      + smt().
      split; 1: by smt().
      move : H3 => [i'] t k ir H3.
      right. exists i'.
      by smt(get_setE).
move => i st t k ir.
case (i = (b,j){2}) => bjeq.
rewrite get_setE bjeq //=.
move => [#] steq teq keq ireq.
split. smt(get_setE pow_bij). 
split.
rewrite -teq -steq //=.
have := inv4 b{2} sk_s.
smt().
smt(get_setE).
by smt(get_setE).
  clear inv8.
  + move => x0 y0 b0 x0in.
    have := inv x0 y0 b0 x0in.
    move => [H1|[H2|H3]].
    + smt().
    + right. left.
      move : H2 => [i'] t k ir H2.
      exists i'. 
      smt(get_setE).
    by smt().
  auto => /> &1 &2 kps ? ? _ ? _ ? ? ? c1 ? ? inv5 ? ? ? ? ? ? inv2 ? ? inv8 inv inv4 *.
  do split; ~2,7,8: by smt(get_setE in_fsetU1 in_fsetU pow_bij).
  + move => x0 y0 b0 tqeq.
    have := inv5 x0 y0 b0 tqeq.
    move => [] H1 [H2|H3].
    + smt().
    split; 1: by smt().
    move : H3 => [i'] t k ir H3.
    right. exists i'.
    by smt(get_setE).
move => i st t k ir.
case (i = (b,j){2}) => bjeq.
rewrite get_setE bjeq //=.
move => [#] steq teq keq ireq.
split. smt(get_setE pow_bij). 
split.
rewrite -teq -steq //=.
have := inv4 b{2} sk_s.
smt().
smt(get_setE).
by smt(get_setE).
  clear inv8.
  + move => x0 y0 b0 x0in.
    have := inv x0 y0 b0 x0in.
    move => [H1|[H2|H3]].
    + smt().
    + right. left.
      move : H2 => [i'] t k ir H2.
      exists i'. 
      smt(get_setE).
    by smt().
- move => &2 bad.
  proc; inline.
  sp; if => //.
  sp; match; auto => />.
  match => //.
  islossless.
- move => &1. 
  proc; inline.
  sp; if => //.
  sp; match; auto => />.
  match => //.
  islossless.
 
- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // st' pt ir.
  sp; seq 1 1: (#pre /\ ={ts}); 1: by auto=> />.
  if => //.
  + sp 3 3; if => //.
    + auto => /> &1 &2 ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *. split. move => *. split. move => *.
      do split; ~2,9: by smt(get_setE).
      + move => x0 y0 b0 tqeq.
        have := inv2 x0 y0 b0 tqeq.
        move => [H1] [H2|H3]. 
        + split; 1: by smt(mem_set).
          left.
          move : H2 => [i'] t k ir'' H2.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).
      move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *. 
      do split; ~2,9: by smt(get_setE).
      + move => x0 y0 b0 tqeq.
        have := inv2 x0 y0 b0 tqeq.
        move => [H1] [H2|H3]. 
        + split; 1: by smt(mem_set).
          left.
          move : H2 => [i'] t k ir'' H2.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).
      move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *. split. move => *.
      do split; ~2,9: by smt(get_setE).
      + move => x0 y0 b0 tqeq.
        have := inv2 x0 y0 b0 tqeq.
        move => [H1] [H2|H3]. 
        + split; 1: by smt(mem_set).
          left.
          move : H2 => [i'] t k ir'' H2.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).
      move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *. 
      do split; ~2,9: by smt(get_setE).
      + move => x0 y0 b0 tqeq.
        have := inv2 x0 y0 b0 tqeq.
        move => [H1] [H2|H3]. 
        + split; 1: by smt(mem_set).
          left.
          move : H2 => [i'] t k ir'' H2.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).
      move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    auto => /> &1 &2 ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *. split. move => *. split. move => *.
    do split; ~2,9: by smt(get_setE). 
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~2,9: by smt(get_setE). 
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
 move => *. split. move => *.
    do split; ~2,9: by smt(get_setE). 
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~2,9: by smt(get_setE). 
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
  sp ^if & -1 ^if & -1; if => //.
  + auto => /> &1 &2 ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *. split. move => *. split. move => *.
    do split; ~8: by smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~8: by smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
move => *. split. move => *.
    do split; ~8: by smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~8: by smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
  auto => /> &1 &2 ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *. split. move => *. split. move => *.
    do split; ~2,4,8: by smt(mem_set get_setE).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set). 
    + clear inv2 inv5. smt(mem_set get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => *.
    do split; ~2,4,8: by smt(mem_set get_setE).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set). 
    + clear inv2 inv5. smt(mem_set get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
move => *. split. move => *.
    do split; ~2,4,8: by smt(mem_set get_setE).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set). 
    + clear inv2 inv5. smt(mem_set get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
move => *.
    do split; ~2,4,8: by smt(mem_set get_setE).
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set). 
    + clear inv2 inv5. smt(mem_set get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
- move => &2 bad.
  proc; inline.
  sp; if => //.
  sp; match; auto. 
  match; auto => />.
  by rewrite dtag_ll.
- move => &1.
  proc; inline. 
  sp; if => //.
  sp; match; auto.
  match; auto.
  by rewrite dtag_ll.
 
- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // st' t' k' ir'.
  if => //.
  swap{1} ^ks<$ @ 1.
  swap{2} ^ks<$ @ 1.
  seq 1 1: (#pre /\ ={ks}); 1: by auto=> />.
  sp 1 1; if => //.
  + smt().
(************ case that the handle was not yet in h2m ************)
  + auto => /> &1 &2 ? ? ? ? ? ? ? inv2 ? ? ? inv3 ? ? ? ? ? ? inv *.
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split.
    + split; 1: by smt().
      split. 
      + move => x0 y0 b0 tqeq.
        have := inv2 x0 y0 b0 tqeq.
        move => [H1] [H2|H3]. 
        + split; 1: by smt(mem_set).
          left.
          move : H2 => [i'] t k ir'' H2.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).
      split. smt(get_setE).
      split. 
      + move => // i0 i'.
        case (i0 = i{2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m10 m2 m2' trace stnn.
          have := inv3 i0 i{2}.
          smt().
        case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
        rewrite get_set_neqE //=.
        move => m10 m2 m2' stnn.
        rewrite i'eq !get_set_sameE //=.
        have := inv3 i0 i{2}.
        smt().
      split. smt(get_setE).
      split. smt(get_setE).
      split. smt(get_setE).
      + move => x0 y0 b0 x0in.
        case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) 
               = ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
        + left.
          exists i{2} (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
          smt(get_setE pow_bij expgK).
        have := inv x0 y0 b0.
        have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set). 
        move => [H1|H2].
        + left. 
          move : H1 => [i'] t k ir H1.
          exists i'. 
          smt(get_setE).
        by smt().
    by smt(get_setE mem_set).
(************ case that the handle was in h2m ************)
  auto => /> &1 &2 stc ? ? ? ? ? inv6 inv2 ? ? ? inv5 ? inv3 ? ? inv7 inv4 inv ? fresh *.
  split.
  + case (Game4.tested{2} = None) => test; 1: by smt().
    case (Game4.tq{2} = Some ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1)); 2: by smt().
    have->: ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1) = (g ^ (st'.`2 * loge (oget t'.`2).`1), g ^ (st'.`2 * loge st'.`1), st'.`1, g ^ st'.`2, g ^ loge (oget t'.`2).`1). 
    + congr.
      + by rewrite ComRing.mulrC expM expgK. 
      + by rewrite ComRing.mulrC expM expgK.
      by rewrite expgK.
    have{2}->: st'.`1 = g ^ (loge st'.`1) by rewrite expgK.
    move => tqeq2.
    have := inv2 st'.`2 (loge (oget t'.`2).`1) (loge st'.`1) tqeq2.
    rewrite //= some_oget //=; 1: smt().
    move => [] tqin. move => [[i0 t k ir [H1 [+ H2]]]|[i0 t k ir [H1 [H2 H3]]]].
    + rewrite expgK. 
      have{2}->: st'.`1 = t'.`1.`1. smt().
      have{1}->: g ^ st'.`2 = t'.`1.`2. smt().
      move => H3.
      have : (i0 = i{2}).
      + apply (inv5 i0 i{2} (t'.`1.`1, t'.`1.`2) (Some (g ^ loge (oget t'.`2).`1, t)) t'.`2); smt(get_setE).
      smt(get_setE).
    have : untested_partner_c t' Game4.s_smap{2} = Some false.
    + rewrite /untested_partner_c.
      have->: get_partners_c t' Game4.s_smap{2} = fset1 i0.
      + rewrite /get_partners_c.
        apply in_eq_fset1. 
        move => x0.
        rewrite mem_fdom mem_filter /=.
        split.
        + move => [x0in trx0]. 
          apply (inv3 x0 i0 t'.`1 (oget t'.`2).`1 (oget t'.`2).`2 (g ^ loge st'.`1, g ^ st'.`2) t); smt(expgK).
        move => ->.
        split; 1: by smt().
        rewrite H2 /get_trace //=.
        have->: (g ^ st'.`2 = (t'.`1).`2). smt().
        have->: g ^ loge st'.`1 = (t'.`1).`1. smt(expgK).
        have->: t = (oget t'.`2).`2.
        + have v := inv4 i0 (loge st'.`1, Some (loge (oget t'.`2).`1)) ((g ^ loge st'.`1, g ^ st'.`2), Some (g ^ loge (oget t'.`2).`1, t)) k ir H2.
          rewrite v.
          simplify.
          have v2 := inv7 i{2} st' t' k' ir'.
          rewrite v2; 1: smt().
          smt(ComRing.mulrC expM expgK).
        smt(get_setE mem_set expgK).
      have->: get_untested_partners_c t' Game4.s_smap{2} = fset0.
      + rewrite /get_untested_partners_c.
        apply in_eq_fset0.
        move => x0.
        rewrite mem_fdom mem_filter !negb_and /=. 
        case (x0 = i0) => x0eq; 1: by smt().
        case (get_trace (oget Game4.s_smap{2}.[x0]) = Some t'); 2: by smt().
        have:= inv3 x0 i0 t'.`1 (oget t'.`2).`1 (oget t'.`2).`2 (g ^ loge st'.`1, g ^ st'.`2) t.
        smt(expgK).
      smt(fcard1 fcards0).
    smt().
  split; 1: by smt().
  split.
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set).
  split; 1: by smt(get_setE).
  split.
      + move => // i0 i'.
        case (i0 = i{2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m10 m2 m2' trace stnn.
          have := inv5 i0 i{2}.
          smt().
        case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
        rewrite get_set_neqE //=.
        move => m10 m2 m2' stnn.
        rewrite i'eq !get_set_sameE //=.
        have := inv5 i0 i{2}.
        smt().
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  + move => x0 y0 b0 x0in.
    case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) 
           = ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
    + left.
      exists i{2} (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
      smt(get_setE pow_bij expgK).
    have := inv x0 y0 b0.
    have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set). 
    move => [H1|H2].
    + left. 
      move : H1 => [i'] t k ir H1.
      exists i'. 
      smt(get_setE).
    by smt().
- move => &2 bad; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.
  if => //; inline.
  auto => />.
  by rewrite dkey_ll.
- move => &1; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.
  if => //; inline. 
  auto => />.
  by rewrite dkey_ll.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // st' t' k' ir'.
  if => //.
  swap{1} ^ks<$ @ 1.
  swap{2} ^ks<$ @ 1.
  seq 1 1: (#pre /\ ={ks}); 1: by auto=> />.
  sp 1 1; if => //.
  + smt().
(************ case that the handle was not yet in h2m ************)
  + auto => /> &1 &2 ? ? ? ? c1 c2 inv6 inv2 c3 c4 _ ? ? ? ? ? ? inv5 inv inv3 ? inv4 *.
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split.
    + split; 1: by smt().
      split. 
      + move => x0 y0 b0 tqeq.
        have := inv2 x0 y0 b0 tqeq.
        move => [H1] [H2|H3]; 1: smt(mem_set).
        split; 1: by smt(mem_set).
        right.
        move : H3 => [i'] t k ir'' H3.
        exists i' t k ir''.
        case (i' = (b, j){2}) => i'eq; smt(get_setE).
      split; 1: by smt(get_setE).
      split. clear c1 c2 c3 c4 inv inv2 inv3 inv4.
      + move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          by rewrite get_set_neqE /#.
        case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
        rewrite i'eq get_set_sameE //=.
        rewrite get_set_neqE /#.
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      + move => x0 y0 b0 x0in.
        case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) 
               = ((t'.`1).`2 ^ oget st'.`2, (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
        + right. left.
          exists (b, j){2} (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
          smt(get_setE pow_bij expgK).
        have := inv x0 y0 b0.
        have->: (g ^ (x0 * y0), g ^ (x0 * b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set). 
        simplify.
        move => [H1|[H2|H3]].
        + by smt().
        + right; left. 
          move : H2 => [i'] t k ir H2.
          exists i' t k ir.
          case (i' = (b, j){2}) => bjeq; 2: by smt(get_setE).
          rewrite bjeq.
          have : get_trace (oget Game4.s_smap{2}.[b{2}, j{2} <- Accepted_mod st' t' k' (ir'.`1, true, ir'.`3)].[b{2}, j{2}]) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]) by smt(get_setE).
          smt(get_setE mem_set).
        by smt().
     (* move => x0 x0in. 
      have:= inv4 x0 x0in.
      move => [H1] [H2] [j'] st'' k'' ir'' H3.
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      exists j'. 
      by smt(get_setE).*)
    by smt(get_setE mem_set).
(************ case that the handle was in h2m ************)
  auto => /> &1 &2 stbj ? ? ? ? ? inv4 inv2 ? ? _ inv3 ? inv5 ? ? inv7 inv8 inv ? inv6 *.
  split.
  + case (Game4.tested{2} <> None) => test; 2: by smt().
    case (Game4.tq{2} = Some ((t'.`1).`2 ^ oget st'.`2, (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, (oget t'.`2).`1)); 2: by smt().
    have : ((t'.`1).`2 ^ oget st'.`2, (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, (oget t'.`2).`1) = (g ^ (loge (t'.`1).`2 * (oget st'.`2)), g ^ (loge (t'.`1).`2 * st'.`1), g ^ st'.`1, g ^ (loge (t'.`1).`2), g ^ oget st'.`2). 
    + congr.
      + by rewrite expM expgK. 
      + by rewrite expM expgK.
      + by rewrite expgK.
      smt().
    move => eq. rewrite eq.
    move => tqeq2.
    have := inv2 (loge (t'.`1).`2) (oget st'.`2) st'.`1 tqeq2.
    rewrite //= some_oget //=; 1: smt().
    move => [] tqin [[i0 t k ir [H1 [H2 H3]]]|[i0 t k ir [H1 H2]]]. 
    + have : untested_partner_s t' Game4.c_smap{2} = Some false.
      + rewrite /untested_partner_s.
        have->: get_partners_s t' Game4.c_smap{2} = fset1 i0.
        + rewrite /get_partners_s.
          apply in_eq_fset1. 
          move => x0.
          rewrite mem_fdom mem_filter /=.
          split. 
          + move => [x0in trx0].
            have := inv3 x0 i0 t'.`1 t'.`2 (Some (g ^ oget st'.`2, t)).
            smt(get_setE).
          move => ->.
          split; 1: by smt().
          rewrite H2 /get_trace //=.
          have->: (g ^ loge (t'.`1).`2 = (t'.`1).`2). by rewrite expgK.
          have->: t = (oget t'.`2).`2.
          + have v := inv7 i0 (g ^ st'.`1, loge t'.`1.`2) ((g ^ st'.`1, g ^ loge t'.`1.`2), Some (g ^ oget st'.`2, t)) k ir H2.
            rewrite v //=.
            have v2 := inv8 (b,j){2} st' t' k' ir'.
            rewrite v2; 1: smt().
            smt(expgK expM).
          smt(get_setE).
        have->: get_untested_partners_s t' Game4.c_smap{2} = fset0.
        + rewrite /get_untested_partners_s.
          apply in_eq_fset0.
          move => x0.
          rewrite mem_fdom mem_filter !negb_and /=. 
          case (x0 = i0) => x0eq; 1: by smt().
          case (get_trace (oget Game4.c_smap{2}.[x0]) = Some t'); 2: by smt().
          have:= (inv3 x0 i0 t'.`1 t'.`2 (Some ((oget t'.`2).`1, t))).
          by smt(get_setE).
        by smt(fcard1 fcards0).
      by smt().
    have : (get_ir_test (oget Game4.s_smap{2}.[b{2}, j{2}])).
    + have := inv5 (b,j){2} i0 t'.`1 (oget t'.`2).`1 (oget t'.`2).`2 t'.`1 t.
      move => H4.
      have->: (b,j){2} = i0 by smt(get_setE mem_set).
      by smt().
    by smt().
  split; 1: by smt().
  split.
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]; 1: smt(mem_set).
    split. smt(mem_set).
    right.
    move : H3 => [i'] t k ir'' H3.
    exists i' t k ir''. 
    have : get_trace (oget (Some (Accepted_mod st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    case (i' = (b,j){2}); smt(get_setE).
  split; 1: by smt(get_setE).
  split.
  + move => // i0 i'.
    case (i0 = (b, j){2}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      have : get_trace (oget (Some (Accepted_mod st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
      smt().
    case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => m1 m2 tag m1' tag' stnn.
    rewrite i'eq !get_set_sameE.
    have : get_trace (oget (Some (Accepted_mod st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    smt().
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  + move => x0 y0 b0 x0in.
    case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) 
           = ((t'.`1).`2 ^ oget st'.`2, (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
    + right. left.
      exists (b, j){2} (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
      smt(get_setE mem_set pow_bij expgK).
    have := inv x0 y0 b0.
    have->: (g ^ (x0 * y0), g ^ (x0 * b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set). 
    simplify.
    move => [H1|[H2|H3]].
    + by smt().
    + right; left. 
      move : H2 => [i'] t k ir H2.
      exists i' t k ir. 
      case (i' = (b,j){2}); 2: smt(get_setE mem_set).
      have : get_trace (oget Game4.s_smap{2}.[b{2}, j{2} <- Accepted_mod st' t' k' (ir'.`1, true, ir'.`3)].[b{2}, j{2}]) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]) by smt(get_setE).
      smt(get_setE mem_set).
    by smt().
- move => &2 bad; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.
  if => //; inline.
  auto => />.
  by rewrite dkey_ll.
- move => &1; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.
  if => //; inline.
  auto => />.
  by rewrite dkey_ll.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // sk.
  if => //.
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? inv *. split. smt(get_setE mem_set). 
  move => b0 sk0.
  case (b0 = b{2}) => beq.
  + rewrite beq mem_set //=.
    rewrite get_setE //=.
    have := inv b{2} sk.
    smt(get_setE mem_set).
  smt(get_setE mem_set).
- move => &2 bad; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.
- move => &1; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // [st' pt ir| st' t k ir].
  + auto => /> &1 &2 ? ? ? ? ? ? ? inv2 ? ? _ inv3 ? ? ? ? ? ? inv *.
    split; 1: by smt(get_setE).
    split. 
    + move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1] [H2|H3]. 
      split. smt().
      left.
      move : H2 => [i'] t k ir' H2.
      exists i'. 
      by smt(get_setE).     
      smt(). 
    split; 1: by smt(get_setE).
    split.
      + move => // i0 i'.
        case (i0 = i{2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m10 m2 m2' trace stnn.
          have := inv3 i0 i'.
          smt().
        case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
        rewrite get_set_neqE //=.
        move => m10 m2 m2' stnn.
        rewrite i'eq !get_set_sameE //=.
        have := inv3 i0 i'.
        smt().
    split; 1: by smt(get_setE oget_some).
    split; 1: by smt(get_setE).
    split. smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv x0 y0 b0.
      rewrite x0in //=.
      move => [H1|H2].
      + left.
        move : H1 => [i'] t k ir' H1.
        exists i'. 
        by smt(get_setE).
      by smt().
  auto => /> &1 &2 ? ? ? ? ? ? inv3 inv2 ? ? _ ? ? ? ? ? ? ? inv *. 
  split; 1: by smt(get_setE).
  split.
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3].
    split. smt().
    left.
    move : H2 => [i'] t' k' ir' H2.
    exists i'. 
    by smt(get_setE).     
    smt(). 
  split; 1: by smt(get_setE).
  split. clear inv inv2 inv3. by smt(get_setE).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split. smt(get_setE).
  + move => x0 y0 b0 x0in.
    have := inv x0 y0 b0.
    rewrite x0in //=.
    move => [H1|H2].
    + left. 
      move : H1 => [i'] t' k' ir' H1.
      exists i'.
      by smt(get_setE).
    by smt().
- move => &2 bad; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.
- move => &1; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // st' t' k' ir'.
  auto => /> &1 &2 ? ? ? ? c1 ? inv6 inv2 c2 c3 _ ? ? inv5 ? ? ? ? inv inv3 inv4 *.
  split; 1: by smt(get_setE).
  split. 
  + move => x0 y0 b0 tqeq.
    have := inv2 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    smt().
    split. smt().
    right.
    move : H3 => [i'] t k ir'' H3.
    case ((b, j){2} = i') => i'eq.
    + have : Game4.s_smap{2}.[b{2}, j{2}] = Game4.s_smap{2}.[i']; 1: by smt().
      move => H2.
      exists i' t k' (true, ir'.`2, ir'.`3).
      by smt(get_setE).
    exists i' t k ir''.
    by smt(get_setE).
  split; 1: by smt(get_setE).
  split.
  + move => // i0 i'.
    case (i0 = (b, j){2}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      have : get_trace (oget (Some (Accepted_mod st' t' k' (true, ir'.`2, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
      by smt().
    case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => m1 m2 tag m1' tag' stnn.
    rewrite i'eq !get_set_sameE.
    have : get_trace (oget (Some (Accepted_mod st' t' k' (true, ir'.`2, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    by smt().
  split. 
  + have : get_trace (oget (Some (Accepted_mod st' t' k' (true, ir'.`2, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    by smt(get_setE). 
  split; 1: by smt(get_setE).
  + move => x0 y0 b0 x0in.
    have := inv x0 y0 b0.
    rewrite x0in //=.
    move => [H1|[H2|H3]].
    + by smt().
    + right; left.
      move : H2 => [i'] t k'' ir'' H2.
      case ((b, j){2} = i') => i'eq.
        have : Game4.s_smap{2}.[b{2}, j{2}] = Game4.s_smap{2}.[i']; 1: by smt().
        move => H1.
        exists i' t k' (true, ir'.`2, ir'.`3).
        by smt(get_setE).
      exists i' t k'' ir''.
      by smt(get_setE). 
    by smt().
- move => &2 bad; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.
- move => &1; proc.
  sp; if => //.
  sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
  sp; if => //.
  sp; if => //; sp; match = => //.
  move => st.
  match = => //.
  move => st' t' k' ir'.
  if => //.
  rcondt{1} ^if; 1: by auto.
  rcondf{2} ^if; 1: by auto.
  inline{2}. swap {2} ^ks2<$ @ 1.
  seq 0 1: (#pre /\ ks2{2} \in dkey). auto => />.
  sp 3 3.
  case (x{2} \notin Game4.h2m{2}).
  + rcondt {1} ^if. auto => /#.
    rcondt {2} ^if. auto => /#.
    auto => /> &1 &2 badq tq ? ? ? ? ? ? inv6 inv2 ? ? _ ? ? ? ? ? ? inv3 inv *.
    split. smt(get_setE mem_set).
    split. smt(get_setE mem_set).
    split. 
    + split. 
      + move => x0 y0 sk0 eq1 eq2 eq3 eq4 eq5.
        split. smt(mem_set).
        left.
        exists i{2} (oget t'.`2).`2 k' (ir'.`1, ir'.`2, true). 
        smt(get_setE mem_set pow_bij).
      split.
      + move => // i0 i'.
        case (i0 = i{2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          by smt().
        case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
        rewrite get_set_neqE //=.
        move => m1 m2 tag m1' tag' stnn.
        rewrite i'eq !get_set_sameE.
        by smt().
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      + move => x0 y0 b0 x0in.
        case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) = ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
        + left.
          exists i{2} (oget t'.`2).`2 k' (ir'.`1, ir'.`2, true).
          smt(get_setE pow_bij expgK).
        have := inv x0 y0 b0.
        have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set).
        simplify.
        move => [H1|H2].
        + left.
          move : H1 => [i'] t k'' ir'' H1.
          exists i'.
          smt(get_setE).
        by smt().
      by smt(get_setE).
  rcondf {1} ^if. auto => /#.
  rcondf {2} ^if. auto => /#.
  auto => /> &1 &2 ? ? stc ? ? ? ? ? ? ? ? ? _ inv2 ? inv4 ? ? ? ? inv inv3 ? fresh ? ? ? x2in *.
  suff //=:false.
  have := inv st'.`2 (loge (oget t'.`2).`1) (loge st'.`1).
  have->: (g ^ (st'.`2 * loge (oget t'.`2).`1), g ^ (st'.`2 * loge st'.`1), g ^ loge st'.`1, g ^ st'.`2, g ^ loge (oget t'.`2).`1) = ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1). 
  congr.
  + by rewrite ComRing.mulrC expM expgK.
  + by rewrite ComRing.mulrC expM expgK.
  + by rewrite expgK. 
  by rewrite expgK.
  rewrite x2in //=.
  rewrite !negb_or.
  split.
  + rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game4.c_smap{2}.[int] = Some (Accepted_mod (g ^ loge st'.`1, st'.`2) ((g ^ loge st'.`1, g ^ st'.`2), Some (g ^ loge (oget t'.`2).`1, t)) k ir)); 2: by done.
    simplify. 
    move => stint. 
    smt(get_setE pow_bij expgK).
  split.
  + rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game4.s_smap{2}.[int] = Some (Accepted_mod (loge st'.`1, Some (loge (oget t'.`2).`1)) ((g ^ loge st'.`1, g ^ st'.`2), Some (g ^ loge (oget t'.`2).`1, t)) k ir)); 2: by done.
    simplify.
    move => stint.
    rewrite negb_or.
    case (ir.`2) => rev.
    + have : fresh_partner_c t' Game4.s_smap{2} Game4.servers{2} = Some false; 2: by smt().
      rewrite /fresh_partner_c.
      have : (int \in (get_origins_c t' Game4.s_smap{2})).
      + rewrite /get_origins_c.
        rewrite mem_fdom mem_filter /=.
        split; 1: by smt().
        exists (Some (g ^ loge (oget t'.`2).`1, t)).
        smt(get_setE mem_set expgK).
      move => H3.
      have->: 1 <= card (get_origins_c t' Game4.s_smap{2}) by smt(@FMap).
      have->: (get_fresh_partners_c t' Game4.s_smap{2} Game4.servers{2}) = fset0; 2: by smt(fcards0).
      rewrite /get_fresh_partners_c.
      apply in_eq_fset0.
      move => x0.
      rewrite mem_fdom mem_filter !negb_and /=. 
      case (x0 = int) => x0eq; 1: by smt().
      case (get_trace (oget Game4.s_smap{2}.[x0]) = Some t'); 2: by smt().
      have:= (inv4 x0 int t'.`1 (g ^ loge (oget t'.`2).`1) (oget t'.`2).`2 (g ^ loge st'.`1, g ^ st'.`2) t). 
      by smt(expgK).
    case (ir.`3) => tes; 2: by smt().
    by smt().
  by smt().
- move => &2 bad; proc; inline.
  sp; if => //.
  sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + inline; auto => />.
    by rewrite dkey_ll /#.
  auto => />.
  by rewrite dkey_ll /#.
- move => &1; proc; inline.
  sp; if => //.
  sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + inline; auto => />.
    by rewrite dkey_ll /#.
  auto => />.
  by rewrite dkey_ll /#.

- proc; inline.
  sp; if => //.
  sp; if => //; sp; match = => //.
  move => st.
  match = => //.
  move => st' t' k' ir'.
  if => //.
  rcondt{1} ^if; 1: by auto.
  rcondf{2} ^if; 1: by auto.
  inline{2}. swap {2} ^ks2<$ @ 1.
  seq 0 1: (#pre /\ ks2{2} \in dkey). auto => />.
  sp 3 3.
  case (x{2} \notin Game4.h2m{2}).
  + rcondt {1} ^if. auto => /#.
    rcondt {2} ^if. auto => /#.
    auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? _ ? ? ? ? ? ? ? inv ? inv2*.
    split. smt(get_setE mem_set).
    split. smt(get_setE mem_set).
    split. 
    + split.
      + move => x0 y0 sk0 eq1 eq2 eq3 eq4 eq5.
        split; 1: by  smt(mem_set).
        right.
        exists (b,j){2} (oget t'.`2).`2 k' (ir'.`1, ir'.`2, true).
        smt(get_setE pow_bij expgK).
      split.
      + move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          have : get_trace (oget (Some (Accepted_mod st' t' k' (ir'.`1, ir'.`2, true)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
          by smt().
        case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
        rewrite get_set_neqE //=.
        move => m1 m2 tag m1' tag' stnn.
        rewrite i'eq !get_set_sameE.
        have : get_trace (oget (Some (Accepted_mod st' t' k' (ir'.`1, ir'.`2, true)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
        by smt().
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      + move => x0 y0 b0 x0in.
        case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) = ((t'.`1).`2 ^ oget st'.`2, (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
        + right; left.
          exists (b,j){2} (oget t'.`2).`2 k' (ir'.`1, ir'.`2, true).
          smt(get_setE pow_bij expgK).
        have := inv x0 y0 b0.
        have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 b0), g ^ b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set).
        simplify.
        move => [H1|[H2|H3]].
        + smt().      
        + right; left.
          move : H2 => [i'] t k'' ir'' H2.
          exists i' t k''.
          case (i' = (b,j){2}) => i'eq. 
          + exists (ir''.`1, ir''.`2, true). 
            split. by smt(get_setE).
            by rewrite i'eq get_set_sameE /#.
          exists ir''.
          by smt(get_setE).
        by smt().
    by smt(get_setE).
  rcondf {1} ^if. auto => /#.
  rcondf {2} ^if. auto => /#.
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? _ inv3 ? inv2 ? ? ? ? inv ? ? fresh ? ? ? x2in *.
  suff //=:false.
  have := inv (loge (t'.`1).`2) (oget st'.`2) st'.`1.
  have<-: ((t'.`1).`2 ^ oget st'.`2, (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, g ^ oget st'.`2) = (g ^ (loge (t'.`1).`2 * (oget st'.`2)), g ^ (loge (t'.`1).`2 * st'.`1), g ^ st'.`1, g ^ (loge (t'.`1).`2), g ^ oget st'.`2).
  + congr.
    + by rewrite expM expgK. 
    + by rewrite expM expgK.
    by rewrite expgK.
  rewrite x2in //=.
  rewrite !negb_or.
  split.
  + rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game4.c_smap{2}.[int] = Some (Accepted_mod (g ^ st'.`1, loge t'.`1.`2) ((g ^ st'.`1, g ^ loge (t'.`1).`2), Some (g ^ oget st'.`2, t)) k ir)); 2: by done.
    simplify. 
    move => stint.
    rewrite negb_or.
    case (ir.`2) => rev.
    + have : fresh_partner_s t' Game4.c_smap{2} = Some false; 2: by smt().
      rewrite /fresh_partner_s.
      have : (int \in (get_origins_s t' Game4.c_smap{2})).
      + rewrite /get_origins_s.
        rewrite mem_fdom mem_filter /=.
        split; 1: by smt().
        exists (Some (g ^ oget st'.`2,  t)).
        smt(get_setE pow_bij expgK).
      move => H3.
      have->: 1 <= card (get_origins_s t' Game4.c_smap{2}) by smt(@FMap).
      have->: (get_fresh_partners_s t' Game4.c_smap{2}) = fset0; 2: by smt(fcards0).
      rewrite /get_fresh_partners_s.
      apply in_eq_fset0.
      move => x0.
      rewrite mem_fdom mem_filter !negb_and /=. 
      case (x0 = int) => x0eq; 1: by smt().
      case (exists (m2o : (pkey * tag) option), get_trace (oget Game4.c_smap{2}.[x0]) = Some (t'.`1, m2o)) ; 2: by smt().
      have:= (inv3 int x0 (g ^ st'.`1, g ^ loge (t'.`1).`2) (Some (g ^ oget st'.`2, t))). 
      smt(get_setE pow_bij expgK). 
    case (ir.`3) => tes; 2: by smt().
    by smt().
  split.
  + rewrite //=.
    rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game4.s_smap{2}.[int] = Some (Accepted_mod (st'.`1, Some (oget st'.`2)) ((g ^ st'.`1, g ^ loge (t'.`1).`2), Some (g ^ oget st'.`2,  t)) k ir)); 2: by done.
    simplify.
    move => stint.
    have : int = (b,j){2}; 1: by have := inv2 int (b,j){2} (g ^ st'.`1, g ^ loge (t'.`1).`2) (oget t'.`2).`1 t t'.`1 (oget t'.`2).`2; smt().
    move => inteq.
    rewrite negb_or.
    split. 
    + have : ir.`2 = get_ir_sess (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by rewrite -inteq /#.
      smt().
    have : ir.`3 = get_ir_test (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by rewrite -inteq /#.
    smt().
  smt().
- move => &2 bad; proc; inline.
  sp; if => //.
  sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + inline; auto => />.
    by rewrite dkey_ll /#.
  auto => />.
  by rewrite dkey_ll /#.
- move => &1; proc; inline.
  sp; if => //.
  sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + inline; auto => />.
    by rewrite dkey_ll /#.
  auto => />.
  by rewrite dkey_ll /#. *)
qed.



(* update where we are *)
lemma sofar &m: `| Pr[E_GAKE_nodhs(GAKEb_nodhs(NTOR_S_mod, NTOR_C_mod, RO), A).run(false) @ &m : res] - Pr[E_GAKE_nodhs(GAKEb_nodhs(NTOR_S_mod, NTOR_C_mod, RO), A).run(true) @ &m : res]|
  <= Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : Game4.badq] 
       + Pr[E_GAKE_nodhs(Game1, A).run(false) @ &m : Game1.bad2] + Pr[E_GAKE_nodhs(Game1, A).run(true) @ &m : Game1.bad2] + 2%r * ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt).
proof. 
rewrite !(gake_game0 _).
apply (ler_trans (`|Pr[E_GAKE_nodhs(Game1, A).run(false) @ &m : res] - Pr[E_GAKE_nodhs(Game1, A).run(true) @ &m : res]| + 2%r * ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt))).
+ smt(game0_game1 game0_bad).
rewrite ler_add2r.
apply (ler_trans (`|Pr[E_GAKE_nodhs(Game2, A).run(false) @ &m : res] - Pr[E_GAKE_nodhs(Game2, A).run(true) @ &m : res]| 
        + Pr[E_GAKE_nodhs(Game1, A).run(false) @ &m : Game1.bad2] + Pr[E_GAKE_nodhs(Game1, A).run(true) @ &m : Game1.bad2])).
+ smt(game1_game2).
rewrite ler_add2r.
rewrite !(game2_game3 _).
rewrite !game3_RO !LRO_game4 ler_add2r. 
by apply interestingbit.
qed.



(* Step 7: Reduction to multi-instance st-CDH assumption *) (*
lemma test_ephrev_nn &m: Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : Game4.badq /\ Game4.test_ephrev_s = None] = 0%r.
proof. admit. (*
byphoare => //; hoare.
proc; inline.
call (_: ! (Game4.badq /\ Game4.test_ephrev_s = None) /\ (Game4.test_ephrev_s = None <=> Game4.tq = None) /\ (Game4.tested = None <=> Game4.tq = None)); 2..10: conseq (: true) => //.

- proc; inline. sp; if => //. auto => /#.

- proc; inline.
  sp; if => //.
  sp; if => //.
  exlim Game4.c_smap.[i{!hr}] => csi.
  case (csi = None).
  + match None ^match => //.
  match Some ^match => //.
  + skip => /#.
  match => //; if => //; if => //.
  + sp; seq 1: (#pre /\ ks \in dkey); 1: by auto => />.
    auto => />.
  sp; seq 1: (#pre /\ ks2 \in dkey); 1: by auto => />.
  auto => />.

- proc; inline.
  sp; if => //.
  sp; if => //.
  exlim Game4.s_smap.[(b, j)] => ssj.
  case (ssj = None).
  + match None ^match => //.
  match Some ^match => //.
  + skip => /#.
  match => //; if => //; if => //.
  + sp; seq 1: (#pre /\ ks \in dkey); 1: by auto => />.
    auto => />.
  sp; seq 1: (#pre /\ ks2 \in dkey); 1: by auto => />.
  auto => />.

auto => /#. *)
qed. *)

lemma split_pr &m: Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : Game4.badq] = 
                     Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : Game4.badq /\ Game4.test_ephrev_s = true] 
                     + Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : Game4.badq /\ Game4.test_ephrev_s = false].
proof.
rewrite Pr[mu_split Game4.test_ephrev_s = true].
by congr; rewrite Pr[mu_eq] // => &hr; smt().
qed.

print Red_Ltk.Red_O.

op no_clear_ddh(x : group * group * group * group * group) = (Some x.`1, Some x.`2, x.`3, x.`4, x.`5).

op clear_ddh1(x : group * group * group * group * group) =
  if (x.`4 ^ (loge x.`3) = x.`2) then (Some x.`1, None, x.`3, x.`4, x.`5) 
    else (Some x.`1, Some x.`2, x.`3, x.`4, x.`5).

op clear_ddh2(x : group * group * group * group * group) =
  if (x.`4 ^ (loge x.`5) = x.`1) /\ (x.`4 ^ (loge x.`3) = x.`2) then (None, None, x.`3, x.`4, x.`5) 
    else (Some x.`1, Some x.`2, x.`3, x.`4, x.`5).

local op clear_sk (s : server_state) =
match s with
| Honest_mod sk => Honest_mod witness
| Corrupt_mod sk => Corrupt_mod witness
| Dishonest_mod => s
end.

local op clear_opt_c (s : pr_st_client option) : (pkey * skey) option = if s <> None then Some ((oget s).`1, witness) else None.

local op clear_esk (s : pr_st_client instance_state) = 
match s with
| Pending_mod st pt ir => let (pk, sk) = st in Pending_mod (pk, witness) pt ir
| Accepted_mod st t k ir => let (pk, sk) = st in Accepted_mod (pk, witness) t k ir
| Aborted_mod st t ir => Aborted_mod (clear_opt_c st) t ir
end.

local op clear_opt_s (s : pr_st_server option) : (skey * skey option) option = if s <> None then Some (witness, (oget s).`2) else None.

local op clear_ltsk (s : pr_st_server instance_state) = 
match s with 
| Pending_mod st pt ir => let (sk, esk) = st in Pending_mod (witness, esk) pt ir
| Accepted_mod st t k ir => let (sk, esk) = st in Accepted_mod (witness, esk) t k ir
| Aborted_mod st t ir => Aborted_mod (clear_opt_s st) t ir
end. 

print Game4. 

lemma game4_ltk &m: Pr[E_GAKE_nodhs(Game4, A).run(true) @ &m : Game4.badq /\ Game4.test_ephrev_s = true] <= 
                  Pr[E_GAKE_nodhs(Game4Ltk, A).run(true) @ &m : Game4Ltk.badq].
byequiv (: ={glob A, arg} /\ arg{1} = true ==> _) => //.
proc; inline *.
call (: Game4Ltk.test_ltkrev, 
        ={b0, hm, h1m, h2m, c_smap, s_smap, servers, tested, b_set, x_set, y_set, pk_set, m1_set, m2_set, bad1, bad2, tq, hq, badq, test_ephrev_s, test_ltkrev}(Game4, Game4Ltk)
         /\ (Game4.test_ephrev_s => Game4.tested <> None){1}
         /\ (forall b j, (b, j) \in Game4.s_smap => (oget (get_trace (oget Game4Ltk.s_smap{2}.[b, j]))).`1.`1 = b
              /\ b \in Game4.servers /\ (oget (get_trace (oget Game4.s_smap.[(b, j)]))).`2 <> None){1}
         /\ (forall i t, i \in Game4.c_smap => get_trace (oget Game4.c_smap.[i]) = Some t => t.`2 <> None 
              => (oget t.`2).`1 \in Game4.m2_set \/ (oget t.`2).`1 \in Game4.y_set){1}
         /\ (forall i s pt ir, i \in Game4.c_smap => Game4.c_smap.[i] = Some (Pending_mod s pt ir) => !ir.`3){1}
         /\ (forall b j, (b, j) \in Game4.s_smap => get_ir_test (oget Game4.s_smap.[(b, j)]) => !get_ir_eph (oget Game4.s_smap.[(b, j)]) => !Game4.test_ephrev_s){1}
         /\ (forall b j, Game4.tested = None => (b, j) \in Game4.s_smap => !get_ir_test (oget Game4.s_smap.[(b,j)])){1}
         /\ (forall i, Game4.tested = None => i \in Game4.c_smap => !get_ir_test (oget Game4.c_smap.[i])){1}
         /\ (forall b1 b2 j1 j2, (b1, j1) \in Game4.s_smap => (b2, j2) \in Game4.s_smap => get_ir_test (oget Game4.s_smap.[(b1, j1)])
              => get_ir_test (oget Game4.s_smap.[(b2, j2)]) => (b1, j1) = (b2, j2)){1}
       , ={test_ltkrev}(Game4, Game4Ltk) /\ Game4.tested{1} <> None /\ !Game4.test_ephrev_s{1}
         /\ (forall b j, (b, j) \in Game4.s_smap => b \in Game4.servers /\ (oget (get_trace (oget Game4.s_smap.[(b, j)]))).`2 <> None){1}
         /\ (forall i t, i \in Game4.c_smap => get_trace (oget Game4.c_smap.[i]) = Some t => t.`2 <> None 
              => (oget t.`2).`1 \in Game4.m2_set \/ (oget t.`2).`1 \in Game4.y_set){1}
         /\ (forall i s pt ir, i \in Game4.c_smap => Game4.c_smap.[i] = Some (Pending_mod s pt ir) => !ir.`3){1}
         /\ (forall b j, (b, j) \in Game4.s_smap 
              => get_ir_test (oget Game4.s_smap.[(b, j)]) \/ (exists i, i \in Game4.c_smap 
                               /\ get_trace (oget Game4.c_smap.[i]) = get_trace (oget Game4.s_smap.[(b, j)]) /\ get_ir_test (oget Game4.c_smap.[i]))
              => get_sr_ltk (oget Game4.servers.[b])){1}
) => //; last first.

auto => />.
split. smt(emptyE).
move => inv inv2 inv3 inv4 inv5 rl rr al bl b1l b2l bql csl h1ml h2ml hql m1l m2l pkl ssm sm tltkl tl tql xl yl ar br b1r b2r bqr csr h1mr h2mr hqr m1r m2r pkr ssr sr tephr tltkr tr tqr xr yr. 
by case : (tltkr) => />.

- exact A_ll.

(* h *)
- proc; inline.
  sp; if => //.
  sp; seq 1 1: (#pre /\ ={t}); 1: by auto => />.
  if => //.
  + sp; seq 1 1: (#pre /\ ={k}); 1: by auto => />. 
    if => //.
    + auto => />. smt(in_fsetU1 get_setE mem_set).
    auto => />. smt(in_fsetU1 get_setE mem_set).
  sp; seq 1 1: (#pre /\ ={k}); 1: by auto => />. 
  if => //.
  + auto => />. smt(in_fsetU1 get_setE mem_set).
  auto => />. smt(in_fsetU1 get_setE mem_set).
- move => &2 bad; proc; sp; if; auto => />. 
  rewrite dkey_ll dtag_ll //=.  
  smt(in_fsetU1).
- move => &1; proc; auto.
  rcondf ^if; auto => />.

(* init_s *)
- proc.
  sp; if => //.
  sp; seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp 1 1; if => //.
  auto => />. smt(get_setE mem_set).
- move => &2 bad.
  proc; sp; if; auto => />.
  rewrite dt_ll //=. 
  smt(get_setE mem_set).
- move => &1. 
  proc. 
  rcondf ^if; auto => />.

(* send_msg1 *)
- proc.
  sp; if => //.
  sp; if => //.
  sp; match = => //. 
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  auto => />. smt(get_setE mem_set).
- move => &2 bad.
  proc; sp; if => //; sp; if. 
  + match; auto => />.
    rewrite dt_ll //=.
    move => &hr 10? v *. split; smt(get_setE mem_set).
  by auto.
- move => &1. 
  proc. 
  rcondf ^if; auto => />.

(* send_msg2 *)
- proc; inline. 
  sp; if => //.
  sp; match = => // sk.
  match = => //.
  + seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp 3 3; if => //. 
  sp 2 2; seq 1 1: (#pre /\ ={ts}); 1: by auto => />.
  if => //.
  + sp 3 3; if => //.
    + auto => />. smt(mem_set get_setE in_fsetU1).
    auto => />. smt(mem_set get_setE in_fsetU1).
  sp 2 2; if => //.
  + auto => />. smt(mem_set get_setE in_fsetU1).
  auto => />. smt(mem_set get_setE in_fsetU1).
- move => &2 bad.
  proc; inline; sp; if; sp. 
  match; auto => />.
  match; auto => />.
  seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dt_ll.
  + sp; if => //. 
    auto => />.
    rewrite dtag_ll //=. 
    move => &hr *. split. 
    + move => *. split. smt(mem_set get_setE). split. smt(in_fsetU1).
      move => b0 j0.
      case ((b0, j0) = (b, j){hr}) => bjeq; 2: by smt(mem_set get_setE).
      rewrite get_setE bjeq mem_set //=.
      smt(get_setE).
    move => *. split. smt(mem_set get_setE). split. smt(in_fsetU1).
    move => b0 j0.
    case ((b0, j0) = (b, j){hr}); 2: by smt(mem_set get_setE).
    move => ->.
    rewrite get_setE mem_set //=.
    smt().
  + hoare. 
    by auto => />.
  auto => />.
- move => &1. 
  proc; inline.
  rcondf ^if; auto => />.

(* send_msg3 *)
- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // s pt ir.  
  auto => />. smt(get_setE mem_set in_fsetU1).
- move => &2 bad.
  proc; inline.
  sp; if => //.
  sp; match; auto. 
  match => //.
  sp; seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dtag_ll.
  + if => //.
    + auto => /> &hr *. smt(get_setE mem_set in_fsetU1).
    auto => /> &hr *. smt(get_setE mem_set in_fsetU1).
  hoare. 
  by auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

(* c_rev_skey *)
- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // s t k ir.
  if => //.
  sp; seq 1 1: (#pre /\ ={ks}); 1: by auto => />.
  if => //.
  + auto => /> &2 *. split; smt(get_setE mem_set in_fsetU1).
  auto => /> &2 *. split; smt(get_setE mem_set in_fsetU1).
- move => &2 bad.
  proc; sp; if => //; sp.
  match => //. 
  match => //; if.
  + sp; seq 1 : (#pre); try by auto.
    + auto => />. by rewrite dkey_ll.
    + if => //.
      + auto => /> &hr *. split; smt(get_setE mem_set in_fsetU1).
      auto => /> &hr *. split; smt(get_setE mem_set in_fsetU1).
    hoare. 
    by auto => />.
  auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

(* s_rev_skey *)
- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // s t k ir.
  if => //.
  sp; seq 1 1: (#pre /\ ={ks}); 1: by auto => />.
  if => //.
  + auto => /> &2 *. split; smt(mem_set get_setE).
  auto => /> &2 *. split; smt(mem_set get_setE).
- move => &2 bad.
  proc; sp; if => //.  
  match => //. 
  match => //; if; auto => />.
  rewrite dkey_ll //=. smt(mem_set get_setE).
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

(* rev_ltkey *)
- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // sk.
  if => //; if => //.
  + sp 1 1; rcondf {2} ^if. auto => />.
    auto => /> &1 14? fresh ntpp j bjin [tests|testp].
    + have := fresh j bjin.
      rewrite negb_and negb_or tests //=.
      move => *.
      split. smt(). split. smt().
      split. smt(get_setE mem_set).
      admit.
    have := fresh j bjin.
    rewrite negb_and negb_or testp //=.
    move => *.
    split. admit. (* Partner is tested means that tested is not none *)
    split. admit. (* The partner is tested and not ephrev => not test_ephrev - not the last invariant *)
    split. smt(get_setE mem_set).
    admit.
  auto => />. smt(get_setE mem_set).
- move => &2 bad.
  proc; sp; if => //. 
  match => //.
  match => //; if; auto => />.
  rewrite bad //=. smt(mem_set get_setE).
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

(* c_rev_ephkey *)
- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // [s pt ir|s t k ir].
  + auto => />. smt(mem_set get_setE).
  auto => /> &2 *. do split; smt(mem_set get_setE).
- move => &2 bad.
  proc; sp; if => //.
  match => //.
  match => //. 
  + if => //; auto => /> &hr *.
    do split; smt(get_setE mem_set).
  if => //; auto => /> &hr *.
  do split; smt(get_setE mem_set).
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

(* s_rev_ephkey *)
- proc; inline.
  sp; if => //.
  sp; match = => // st.
  match = => // s t k ir.
  if => //; if => //.
  + auto => /> &2 13?.
    rewrite negb_and negb_or.
    have->: ir.`3 = get_ir_test (oget Game4Ltk.s_smap{2}.[b{2}, j{2}]). smt().
    move => [] [#]. smt().
    move => ? [tests|]. smt(get_setE mem_set).
    rewrite /untested_partner_s.
    case (1 <= card (get_partners_s t Game4Ltk.c_smap{2})); 2: by smt().
    case (1 <= card (get_untested_partners_s t Game4Ltk.c_smap{2})); 1: by smt().
    rewrite /get_untested_partners_s /get_partners_s //=.
    move => nunt ge1.
    have : (1 <= card (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                   get_trace val = Some t /\ get_ir_test val = true) Game4Ltk.c_smap{2}))). admit. (* not the last invariant *)
    admit. (* not the last invariant *)
  auto => /> &2 13?.
  rewrite negb_and !negb_or.
  have->: ir.`3 = get_ir_test (oget Game4Ltk.s_smap{2}.[b{2}, j{2}]). smt().
  move => [] [#]. move => *. do split; smt(mem_set get_setE).
  move => ? [] ? ?. 
  smt(mem_set get_setE).
- move => &2 bad.
  proc; sp; if => //.
  match => //. 
  match => //.
  if => //.
  if => //.
  + auto => /> &hr *.
    rewrite negb_and negb_or !negb_and negb_or //=.
    case (get_ir_test (oget Game4.s_smap{hr}.[b{hr}, j{hr}])) => tests; 1: by smt().
    case (untested_partner_s t{hr} Game4.c_smap{hr} = Some false) => testp; 2: by smt().
    case (get_sr_ltk (oget Game4.servers{hr}.[b{hr}])) => sltkr; 1: by smt().
    left; left; right; right; left; right; right; right; right; right; right; right.
    rewrite negb_forall //=.
    have := testp.
    rewrite /untested_partner_s.
    rewrite /get_partners_s /get_untested_partners_s.
    admit. (* How can I connect the two? *)
  auto => /> &hr *.
  smt(get_setE mem_set).
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

(* c_test *)
- proc; inline.
  sp; if => //.
  sp; if => //.
  match = => //.
  + auto => />.
  move => st.
  match = => //.
  + auto => />.
  + move => s t k ir.
    if => //; 2: by auto => />.
    if => //.
    + sp 3 3; if {2} => //.
      + auto => /> &2 *. 
        split. move => *. do split; smt(mem_set get_setE). move => *. do split; smt(mem_set get_setE).
      auto => /> &2 15?.
      rewrite !negb_or negb_and.
      move => [#] 2? + + H.
      rewrite H //=.
      move => + H2 ? ?.
      rewrite /fresh_partner_c ifT //=. smt(fcard_ge0).
      rewrite /get_fresh_partners_c.
      rewrite H //=.
      move => H3.
      split. split. smt(). admit. (* find right lemmas? *)
      do split; 1..3: smt(mem_set get_setE).
      move => b j bjin []. smt().
      move => [i0].
      case (i0 = i{2}) => i0eq; 1: by smt(get_setE mem_set).
      rewrite mem_set i0eq get_setE i0eq //=. 
      smt().
    sp 3 3; if {2} => //.
    + auto => /> &2 *.
      split. move => *. do split; smt(mem_set get_setE). move => *. do split; smt(mem_set get_setE).
    auto => /> &2 14?. 
    rewrite !negb_or negb_and.
    move => ? [#] 2? + + ? H.
    rewrite H //=.
    move => + H2 ? ? ? ?.
    rewrite /fresh_partner_c ifT //=. smt(fcard_ge0).
    rewrite /get_fresh_partners_c.
    rewrite H //=.
    move => H3.
    split. split. smt(). admit. (* find right lemmas? *)
    do split; 1..3: smt(mem_set get_setE).
    move => b j bjin []. smt().
    move => [i0].
    case (i0 = i{2}) => i0eq; 1: by smt(get_setE mem_set).
    rewrite mem_set i0eq get_setE i0eq //=.
    smt().
  auto => />.
- move => &2 bad.
  proc; sp; if => //.
  rcondf ^if. auto => />.
  auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.

(* s_test *)
- proc; inline.
  sp; if => //.
  sp; if => //.
  match = => //.
  + auto => />.
  move => st.
  match = => //.
  + auto => />.
  + move => s t k ir.
    if => //; 2: by auto => />. 
    if => //.
    + sp 2 2; if {2} => //.
      + auto => /> &2 *. smt(get_setE mem_set).
      auto => /> &2 15? + ? _ _. 
      rewrite !negb_or negb_and.
      move => [#] ? [] ? ?. 
      + do split; 1..3: smt(get_setE mem_set). admit.
      do split; 1..3: smt(get_setE mem_set). admit.
    sp 2 2; if {2} => //.
    + auto => /> &2 *. split; smt(get_setE mem_set).
    auto => /> &2 15? + ? ? _ _ _ _. 
    rewrite !negb_or negb_and.
    move => [#] ? [] ? ?.
    + do split; 1..3: smt(get_setE mem_set). admit.
    do split; 1..3: smt(get_setE mem_set). admit.
  auto => />.
- move => &2 bad.
  proc; sp; if => //.
  rcondf ^if. auto => />.
  auto => />.
- move => &1.
  proc; inline*.
  rcondf ^if; auto => />.
qed.





lemma cdh_red_ltk &m: Pr[E_GAKE_nodhs(Game4Ltk, A).run(true) @ &m : Game4Ltk.badq] <= 
                 Pr[St_CDH_E(St_CDH_O, Red_Ltk(A)).run() @ &m : St_CDH_O.win].
proof. 
byequiv (: ={glob A} /\ arg{1} = true ==> _) => //.
proc; inline.
symmetry.
call (: Game4Ltk.badq,
        ={b0, hm, tested, b_set, x_set, y_set, pk_set, m1_set, m2_set, bad1, bad2, test_ephrev_s, test_ltkrev}(Red_Ltk.Red_O, Game4Ltk)
         /\ (forall x, x \in Game4Ltk.h1m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1}) => x.`4 \in Red_Ltk.Red_O.m1_set{1}
              => (exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] 
                        /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i] /\ x{2}.`2 = x.`3 ^ oget St_CDH_O.x_map{1}.[i])
              => (None, None, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h1m_opt{1} /\ Game4Ltk.h1m{2}.[x] = Red_Ltk.Red_O.h1m_opt{1}.[(None, None, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h1m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1}) => x.`5 \in Red_Ltk.Red_O.m2_set{1} => x.`5 \notin Red_Ltk.Red_O.servers{1} => x.`4 \notin Red_Ltk.Red_O.m1_set{1}
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i]) 
              => !(exists j, (j \in St_CDH_O.y_map{1}) /\ x.`5 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`1 = x.`4 ^ oget St_CDH_O.y_map{1}.[j])
              => (exists j, (j \in St_CDH_O.y_map{1}) /\ x.`3 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`2 = x.`4 ^ oget St_CDH_O.y_map{1}.[j]) 
              => (Some x.`1, None, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h1m_opt{1} /\ Game4Ltk.h1m{2}.[x] = Red_Ltk.Red_O.h1m_opt{1}.[(Some x.`1, None, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h1m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1})
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`2 = x.`3 ^ oget St_CDH_O.x_map{1}.[i]) 
              => !(exists j, (j \in St_CDH_O.y_map{1}) /\ x.`3 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`2 = x.`4 ^ oget St_CDH_O.y_map{1}.[j]) 
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h1m_opt{1} /\ Game4Ltk.h1m{2}.[x] = Red_Ltk.Red_O.h1m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h1m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1})
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i]) 
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`2 = x.`3 ^ oget St_CDH_O.x_map{1}.[i])
              => (exists j, j \in St_CDH_O.y_map{1} /\ x.`5 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`1 = x.`4 ^ oget St_CDH_O.y_map{1}.[j])
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h1m_opt{1} /\ Game4Ltk.h1m{2}.[x] = Red_Ltk.Red_O.h1m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h1m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1}) => x.`4 \in Red_Ltk.Red_O.m1_set{1}
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i]) 
              => !(exists j, (j \in St_CDH_O.y_map{1}) /\ x.`5 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`1 = x.`4 ^ oget St_CDH_O.y_map{1}.[j]) 
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h1m_opt{1} /\ Game4Ltk.h1m{2}.[x] = Red_Ltk.Red_O.h1m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h1m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1}) => ! ((x{2}.`4 \notin Game4Ltk.m1_set{2}) /\ (x{2}.`5 \in Game4Ltk.m2_set{2}) /\ (x{2}.`5 \notin Red_Ltk.Red_O.servers{1}))
              => (exists j, (j \in St_CDH_O.y_map{1}) /\ x.`3 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`2 = x.`4 ^ oget St_CDH_O.y_map{1}.[j]) 
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i]) 
              => !(exists j, (j \in St_CDH_O.y_map{1}) /\ x.`5 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`1 = x.`4 ^ oget St_CDH_O.y_map{1}.[j]) 
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h1m_opt{1} /\ Game4Ltk.h1m{2}.[x] = Red_Ltk.Red_O.h1m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h1m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => x.`3 \notin Red_Ltk.Red_O.servers{1}
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h1m_opt{1} /\ Game4Ltk.h1m{2}.[x] = Red_Ltk.Red_O.h1m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h2m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => x.`3 \in Red_Ltk.Red_O.servers{1} => x.`4 \in Red_Ltk.Red_O.m1_set{1}
              => (exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] 
                        /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i] /\ x{2}.`2 = x.`3 ^ oget St_CDH_O.x_map{1}.[i])
              => (None, None, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h2m_opt{1} /\ Game4Ltk.h2m{2}.[x] = Red_Ltk.Red_O.h2m_opt{1}.[(None, None, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h2m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1}) => x.`5 \in Red_Ltk.Red_O.m2_set{1} => x.`5 \notin Red_Ltk.Red_O.servers{1} => x.`4 \notin Red_Ltk.Red_O.m1_set{1}
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i])
              => !(exists j, (j \in St_CDH_O.y_map{1}) /\ x.`5 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`1 = x.`4 ^ oget St_CDH_O.y_map{1}.[j])
              => (exists j, (j \in St_CDH_O.y_map{1}) /\ x.`3 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`2 = x.`4 ^ oget St_CDH_O.y_map{1}.[j])
              => (Some x.`1, None, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h2m_opt{1} /\ Game4Ltk.h2m{2}.[x] = Red_Ltk.Red_O.h2m_opt{1}.[(Some x.`1, None, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h2m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1})
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`2 = x.`3 ^ oget St_CDH_O.x_map{1}.[i]) 
              => !(exists j, (j \in St_CDH_O.y_map{1}) /\ x.`3 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`2 = x.`4 ^ oget St_CDH_O.y_map{1}.[j]) 
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h2m_opt{1} /\ Game4Ltk.h2m{2}.[x] = Red_Ltk.Red_O.h2m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h2m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1})
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i]) 
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`2 = x.`3 ^ oget St_CDH_O.x_map{1}.[i])
              => (exists j, j \in St_CDH_O.y_map{1} /\ x.`5 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`1 = x.`4 ^ oget St_CDH_O.y_map{1}.[j])
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h2m_opt{1} /\ Game4Ltk.h2m{2}.[x] = Red_Ltk.Red_O.h2m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h2m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1}) => x.`4 \in Red_Ltk.Red_O.m1_set{1}
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i]) 
              => !(exists j, (j \in St_CDH_O.y_map{1}) /\ x.`5 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`1 = x.`4 ^ oget St_CDH_O.y_map{1}.[j]) 
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h2m_opt{1} /\ Game4Ltk.h2m{2}.[x] = Red_Ltk.Red_O.h2m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h2m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => (x.`3 \in Red_Ltk.Red_O.servers{1}) => ! ((x{2}.`4 \notin Game4Ltk.m1_set{2}) /\ (x{2}.`5 \in Game4Ltk.m2_set{2}) /\ (x{2}.`5 \notin Red_Ltk.Red_O.servers{1}))
              => (exists j, (j \in St_CDH_O.y_map{1}) /\ x.`3 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`2 = x.`4 ^ oget St_CDH_O.y_map{1}.[j]) 
              => !(exists i, i \in St_CDH_O.x_map{1} /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] /\ x.`1 = x.`5 ^ oget St_CDH_O.x_map{1}.[i]) 
              => !(exists j, (j \in St_CDH_O.y_map{1}) /\ x.`5 = g ^ oget St_CDH_O.y_map{1}.[j] /\ x.`1 = x.`4 ^ oget St_CDH_O.y_map{1}.[j]) 
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h2m_opt{1} /\ Game4Ltk.h2m{2}.[x] = Red_Ltk.Red_O.h2m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])
         /\ (forall x, x \in Game4Ltk.h2m{2} => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2}
              => x.`3 \notin Red_Ltk.Red_O.servers{1}
              => (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h2m_opt{1} /\ Game4Ltk.h2m{2}.[x] = Red_Ltk.Red_O.h2m_opt{1}.[(Some x.`1, Some x.`2, x.`3, x.`4, x.`5)])

         /\ (forall b x y, (None, None, b, x, y) \in Red_Ltk.Red_O.h1m_opt{1} => (x ^ (loge y), x ^ (loge b), b, x, y) \in Game4Ltk.h1m{2}
                      /\ Red_Ltk.Red_O.h1m_opt{1}.[(None, None, b, x, y)] = Game4Ltk.h1m{2}.[(x ^ (loge y), x ^ (loge b), b, x, y)])
         /\ (forall xy b x y, (Some xy, None, b, x, y) \in Red_Ltk.Red_O.h1m_opt{1} => (xy, x ^ (loge b), b, x, y) \in Game4Ltk.h1m{2})
         /\ (forall (x : group * group * group * group * group), (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h1m_opt{1} => x \in Game4Ltk.h1m{2})
         /\ (forall b x y, (None, None, b, x, y) \in Red_Ltk.Red_O.h2m_opt{1} => (x ^ (loge y), x ^ (loge b), b, x, y) \in Game4Ltk.h2m{2})
         /\ (forall xy b x y, (Some xy, None, b, x, y) \in Red_Ltk.Red_O.h2m_opt{1} => (xy, x ^ (loge b), b, x, y) \in Game4Ltk.h2m{2})
         /\ (forall (x : group * group * group * group * group), (Some x.`1, Some x.`2, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.h2m_opt{1} => x \in Game4Ltk.h2m{2})

         /\ (Game4Ltk.tq{2} <> None => oget Game4Ltk.tq{2} \in Game4Ltk.hq{2} => St_CDH_O.win{1})

         /\ (forall pk, omap clear_sk Game4Ltk.servers{2}.[pk] = Red_Ltk.Red_O.servers{1}.[pk])
         /\ (forall bj, omap clear_ltsk Game4Ltk.s_smap{2}.[bj] = Red_Ltk.Red_O.s_smap{1}.[bj])
         /\ (forall i, omap clear_esk Game4Ltk.c_smap{2}.[i] = Red_Ltk.Red_O.c_smap{1}.[i])

         /\ (forall i st pt ir, i \in Game4Ltk.c_smap{2} => Game4Ltk.c_smap{2}.[i] = Some (Pending_mod st pt ir)
              => pt.`2 = g ^ st.`2 /\ pt.`2 \in Game4Ltk.m1_set{2} /\ pt.`1 = st.`1 /\ pt.`1 \in Game4Ltk.servers{2} 
                      /\ i \in Red_Ltk.Red_O.i_inst{1} /\ (oget Red_Ltk.Red_O.i_inst{1}.[i]) \in St_CDH_O.x_map{1} 
                      /\ st.`2 = oget St_CDH_O.x_map{1}.[(oget Red_Ltk.Red_O.i_inst{1}.[i])]
                      /\ (ir.`1 <=> (oget Red_Ltk.Red_O.i_inst{1}.[i]) \in St_CDH_O.cr1{1})
                      /\ st.`1 \in Red_Ltk.Red_O.b_inst{1} /\ (oget Red_Ltk.Red_O.b_inst{1}.[st.`1]) \in St_CDH_O.y_map{1}
                      /\ !ir.`3)
         /\ (forall i st t k ir, i \in Game4Ltk.c_smap{2} => Game4Ltk.c_smap{2}.[i] = Some (Accepted_mod st t k ir)
              => t.`1.`2 = g ^ st.`2 /\ t.`1.`2 \in Game4Ltk.m1_set{2} /\ t.`1.`1 = st.`1 /\ st.`1 \in Game4Ltk.servers{2} 
                      /\ ((oget t.`2).`1 \in Game4Ltk.m2_set{2} \/ (oget t.`2).`1 \in Game4Ltk.y_set{2})
                      /\ i \in Red_Ltk.Red_O.i_inst{1} /\ (oget Red_Ltk.Red_O.i_inst{1}.[i] \in St_CDH_O.x_map{1}) 
                      /\ st.`2 = oget St_CDH_O.x_map{1}.[(oget Red_Ltk.Red_O.i_inst{1}.[i])]
                      /\ (ir.`1 <=> (oget Red_Ltk.Red_O.i_inst{1}.[i]) \in St_CDH_O.cr1{1})
                      /\ st.`1 \in Red_Ltk.Red_O.b_inst{1} /\ (oget Red_Ltk.Red_O.b_inst{1}.[st.`1]) \in St_CDH_O.y_map{1} 
                      /\ t.`1.`1 = g ^ (oget St_CDH_O.y_map{1}.[(oget Red_Ltk.Red_O.b_inst{1}.[st.`1])])
                      /\ t.`2 <> None)
         /\ (forall bj st t k ir, bj \in Game4Ltk.s_smap{2} => Game4Ltk.s_smap{2}.[bj] = Some (Accepted_mod st t k ir)
              => t.`1.`1 = g ^ st.`1 /\ (g ^ st.`1) \in Game4Ltk.servers{2} /\ g ^ st.`1 = bj.`1
                      /\ t.`2 <> None /\ st.`2 <> None /\ g ^ (oget st.`2) = (oget t.`2).`1
                      /\ g ^ (oget st.`2) \in Game4Ltk.m2_set{2} /\ g ^ (oget st.`2) \notin Game4Ltk.servers{2}
                      /\ (t.`1.`2 \in Game4Ltk.m1_set{2} \/ t.`1.`2 \in Game4Ltk.x_set{2})
                      /\ bj.`1 \in Red_Ltk.Red_O.b_inst{1} /\ (oget Red_Ltk.Red_O.b_inst{1}.[bj.`1]) \in St_CDH_O.y_map{1} 
                      /\ st.`1 = (oget St_CDH_O.y_map{1}.[(oget Red_Ltk.Red_O.b_inst{1}.[bj.`1])]))

         /\ (forall b sk, b \in Game4Ltk.servers{2} => obind get_skey Game4Ltk.servers{2}.[b] = Some sk
              => b = g ^ sk)
         /\ (forall m, m \in Game4Ltk.m1_set{2} <=> (exists i, i \in St_CDH_O.x_map{1} /\ m = g ^ oget St_CDH_O.x_map{1}.[i]))
         /\ (forall i pk, i \in St_CDH_O.x_map{1} => pk = g ^ oget St_CDH_O.x_map{1}.[i] => pk \in Game4Ltk.m1_set{2})
         /\ (forall j pk, j \in St_CDH_O.y_map{1} => pk = g ^ oget St_CDH_O.y_map{1}.[j] => pk \in Game4Ltk.pk_set{2}) 
         /\ (forall j pk, j \in St_CDH_O.y_map{1} => pk = g ^ oget St_CDH_O.y_map{1}.[j] => !Game4Ltk.bad1{2} => !Game4Ltk.bad2{2} => pk \in Game4Ltk.servers{2})
         /\ (forall x, x \in Game4Ltk.h1m{2} => (x.`3 \in Game4Ltk.pk_set{2} \/ x.`3 \in Game4Ltk.b_set{2}) /\ (x.`4 \in Game4Ltk.m1_set{2} \/ x.`4 \in Game4Ltk.x_set{2}) 
                      /\ (x.`5 \in Game4Ltk.m2_set{2} \/ x.`5 \in Game4Ltk.y_set{2}))
         /\ (forall x, x \in Game4Ltk.h2m{2} => (x.`3 \in Game4Ltk.pk_set{2} \/ x.`3 \in Game4Ltk.b_set{2}) /\ (x.`4 \in Game4Ltk.m1_set{2} \/ x.`4 \in Game4Ltk.x_set{2}) 
                      /\ (x.`5 \in Game4Ltk.m2_set{2} \/ x.`5 \in Game4Ltk.y_set{2}))
         /\ (forall x, x \in Red_Ltk.Red_O.h1m_opt{1} => x.`5 \in Red_Ltk.Red_O.m2_set{1} \/ x.`5 \in Red_Ltk.Red_O.y_set{1})
         /\ (forall x, x \in Red_Ltk.Red_O.h2m_opt{1} => x.`5 \in Red_Ltk.Red_O.m2_set{1} \/ x.`5 \in Red_Ltk.Red_O.y_set{1})
         /\ (forall b, b \in Game4Ltk.servers{2} => (b \in Game4Ltk.pk_set{2} /\ (exists j, j \in St_CDH_O.y_map{1} /\ b = g ^ oget St_CDH_O.y_map{1}.[j])))
         /\ (forall b, b \in Game4Ltk.servers{2} => b \in Red_Ltk.Red_O.b_inst{1} /\ (oget Red_Ltk.Red_O.b_inst{1}.[b]) \in St_CDH_O.y_map{1} 
                      /\ b = g ^ (oget St_CDH_O.y_map{1}.[(oget Red_Ltk.Red_O.b_inst{1}.[b])]) 
                      /\ (get_sr_ltk (oget Game4Ltk.servers{2}.[b]) => (oget Red_Ltk.Red_O.b_inst{1}.[b]) \in St_CDH_O.cr2{1}))

         /\ (Red_Ltk.Red_O.b0{1})

         /\ (forall n i, St_CDH_O.n < n => n \notin St_CDH_O.x_map /\ n \notin St_CDH_O.cr1 /\ Red_Ltk.Red_O.i_inst.[i] <> Some n){1}
         /\ (forall m b, St_CDH_O.m < m => m \notin St_CDH_O.y_map /\ m \notin St_CDH_O.cr2 /\ Red_Ltk.Red_O.b_inst.[b] <> Some m){1}
         /\ (St_CDH_O.n = Red_Ltk.Red_O.count_i){1}
         /\ (St_CDH_O.m = Red_Ltk.Red_O.count_b){1}
         /\ (forall i i', i \in Red_Ltk.Red_O.i_inst{1} => i' \in Red_Ltk.Red_O.i_inst{1}
              => Red_Ltk.Red_O.i_inst{1}.[i] = Red_Ltk.Red_O.i_inst{1}.[i']
              => i = i')
         /\ (forall b b', b \in Red_Ltk.Red_O.b_inst{1} => b' \in Red_Ltk.Red_O.b_inst{1}
              => Red_Ltk.Red_O.b_inst{1}.[b] = Red_Ltk.Red_O.b_inst{1}.[b']
              => b = b')

        /\ (forall i t1 t2, Game4Ltk.c_smap.[i] <> None 
                => get_trace (oget Game4Ltk.c_smap.[i]) = Some (t1, t2) 
                => t1.`2 \in Game4Ltk.m1_set){2}
        /\ (forall i t1 t2, Game4Ltk.s_smap.[i] <> None 
                => get_trace (oget Game4Ltk.s_smap.[i]) = Some (t1, Some t2) 
                => t2.`1 \in Game4Ltk.m2_set){2}
         /\ (forall i i' m1 m2 m2', Game4Ltk.c_smap.[i] <> None /\ get_trace (oget Game4Ltk.c_smap.[i]) = Some (m1, m2)
              => Game4Ltk.c_smap.[i'] <> None /\ get_trace (oget Game4Ltk.c_smap.[i']) = Some (m1, m2')
              => i = i'){2}
         /\ (forall i i' m1 m2 tag m1' tag', Game4Ltk.s_smap.[i] <> None /\ get_trace (oget Game4Ltk.s_smap.[i]) = Some (m1, Some (m2, tag))
              => Game4Ltk.s_smap.[i'] <> None /\ get_trace (oget Game4Ltk.s_smap.[i']) = Some (m1', Some (m2, tag'))
              => i = i'){2}
         /\ (forall x y b, Game4Ltk.tq{2} = Some (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x b), g ^ b, g ^ x, g ^ y) 
              => ((exists i tag key ir, i \in Game4Ltk.c_smap /\ Game4Ltk.c_smap.[i] = Some (Accepted_mod (g ^ b, x) ((g ^ b, g ^ x), Some (g ^ y, tag)) key ir)
                     /\ get_ir_test (oget Game4Ltk.c_smap.[i]))
                  \/ (exists i tag key ir, i \in Game4Ltk.s_smap /\ Game4Ltk.s_smap.[i] = Some (Accepted_mod (b, Some y) ((g ^ b, g ^ x), Some (g ^ y, tag)) key ir)
                     /\ get_ir_test (oget Game4Ltk.s_smap.[i])))){2}
         /\ (forall x, Game4Ltk.tq{2} = Some x => (x.`3 \in Red_Ltk.Red_O.servers{1})
                      /\ x \in Game4Ltk.h2m{2}
                   (*   /\ x.`4 \in Red_Ltk.Red_O.m1_set{1} *)
                      /\ (exists (i j : int), (i \in St_CDH_O.x_map{1}) /\ x.`4 = g ^ oget St_CDH_O.x_map{1}.[i] 
                               /\ x.`1 = x{2}.`5 ^ oget St_CDH_O.x_map{1}.[i] /\ x.`2 = x{2}.`3 ^ oget St_CDH_O.x_map{1}.[i]
                               /\ j \in St_CDH_O.y_map{1} /\ x.`3 = g ^ oget St_CDH_O.y_map{1}.[j] /\ (i \notin St_CDH_O.cr1{1}) /\ (j \notin St_CDH_O.cr2{1})))
       , St_CDH_O.win{1}); last first.

auto => />.
split. do split; smt(emptyE mem_empty in_fset0).
move => inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 inv9 inv10 inv11 inv12 inv13 inv14 inv15 inv16 inv17 inv18 inv19 inv20 inv21 inv22 inv23 inv24 inv25 inv26 inv27 inv28 inv29 inv30 inv31 inv32 inv33 inv34 inv35 inv36 inv37 inv38 inv39 inv40 inv41 inv42 inv43 inv44 inv45 inv46 inv47 inv48 inv49 inv50 inv51 inv52 inv53 inv54 inv55 inv56 inv57 inv58 inv59 inv60 rl rr al bl b1l b2l h1l h2l pksl m1l m2l tel tll tl xsl ysl wl ar br b1r b2r bqr h1r h2r hqr pksr m1r m2r tlr tr tqr xsr ysr.
by case : (!br) => />.

- exact A_ll.


+ proc; inline.
  sp; if => //.
  if {1} => //. 
  + sp 2 0; if {1} => //.
    + if {1} => //.
      + rcondt {1} ^if. auto => /#.
        sp 5 0; if {1} => //.
        + if {1} => //.
          + rcondt {1} ^if. auto => /#.
            sp 3 0; if {1} => //.
            + sp; seq 1 1: (#pre /\ ={t}). auto => />.
              if => //. auto => /> &1 &2 *.  smt(expgK expM).
              + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
                if => //. smt(expgK expM).
                + rcondf {1} ^if. auto => /#.
                  rcondf {2} ^if. auto => /#.
                  rcondf {1} ^if. auto => />.
                  rcondf {2} ^if. auto => />.
                  sp 2 2; if => //. 
                  + auto => /> &1 &2 *. do split; smt(mem_set get_setE in_fsetU1 expgK expM).
                  auto => /> &1 &2 *. do split; smt(mem_set get_setE in_fsetU1 expgK expM).
                rcondf {1} ^if. auto => /#.
                rcondf {2} ^if. auto => /#.
                rcondf {1} ^if{2}. auto => /#.
                rcondf {2} ^if{2}. auto => /#.
                sp 1 1; if => //.
                + auto => /> &1 &2 *.
                auto => /> &1 &2 *. do split; smt(mem_set get_setE in_fsetU1 expgK expM).
              seq 1 1: (#pre /\ ={k}). auto => />.
              if => //. smt(expgK expM).
              + rcondf {1} ^if. auto => /#.
                rcondf {2} ^if. auto => /#.
                rcondf {1} ^if{2}. auto => /#.
                rcondf {2} ^if{2}. auto => /#.
                sp 2 2; if => //.
                + auto => /> &1 &2 *.
                auto => /> &1 &2 *. do split; smt(mem_set get_setE in_fsetU1 expgK expM).
              rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if{2}. auto => /#.
              rcondf {2} ^if{2}. auto => /#.
              sp 1 1; if => //.
              + auto => /> &1 &2 *.
              auto => /> &1 &2 *. smt(expgK expM).
            sp; seq 1 1: (#pre /\ ={t}). auto => />.
            if => //. auto => /> &1 &2 *. smt(expgK expM).
            + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
              if => //. smt(expgK expM).
              + rcondf {1} ^if. auto => /#.
                rcondf {2} ^if. auto => /#.
                rcondf {1} ^if{2}. auto => /#.
                rcondf {2} ^if{2}. auto => /#.
                sp 2 2; if => //.
                + auto => /> *. do split; smt(mem_set get_setE expgK expM).
                auto => /> *. do split; smt(mem_set get_setE expgK expM).
              rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if{2}. auto => /#.
              rcondf {2} ^if{2}. auto => /#.
              sp 1 1; if => //.
              + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
              auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            seq 1 1: (#pre /\ ={k}). auto => />.
            if => //. smt(expgK expM).
            + rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if{2}. auto => /#.
              rcondf {2} ^if{2}. auto => /#.
              sp 2 2; if => //. 
              + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
              auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 1 1; if => //.
            + auto => /> &1 &2 *. smt(expgK expM).
            auto => /> &1 &2 *. smt(expgK expM).
          rcondt {1} ^if. auto => /#.
          sp 2 0; if {1} => //.
          + sp; seq 1 1: (#pre /\ ={t}). auto => />.
            if => //. auto => /> &1 &2 *. smt(expgK expM).
            + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
              if => //. smt(expgK expM).
              + rcondf {1} ^if. auto => /#.
                rcondf {2} ^if. auto => /#.
                sp 2 2; if => //.
                + sp 1 1; if => //.
                  auto => /> *.
                if => //.
                + auto => /> *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
                auto => /> *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
              rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if{2}. auto => /#.
              rcondf {2} ^if{2}. auto => /#.
              sp 1 1; if => //.
              + auto => /> &1 &2 *.
              auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            seq 1 1: (#pre /\ ={k}). auto => />.
            if => //. smt(expgK expM).
            + rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if{2}. auto => /#.
              rcondf {2} ^if{2}. auto => /#.
              sp 2 2; if => //.
              + auto => /> &1 &2 *.
              auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 1 1; if => //.
            + auto => /> &1 &2 *.
            auto => /> &1 &2 *. smt(expgK expM).
          sp; seq 1 1: (#pre /\ ={t}). auto => />.
          if => //. auto => /> &1 &2 *. smt(expgK expM).
          + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
            if => //. smt(expgK expM).
            + rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if{2}. auto => /#.
              rcondf {2} ^if{2}. auto => /#.
              sp 2 2; if => //.
              + auto => /> *. do split; smt(mem_set get_setE expgK expM).
              auto => /> *. do split; smt(mem_set get_setE expgK expM).
            rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 1 1; if => //.
            + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          seq 1 1: (#pre /\ ={k}). auto => />.
          if => //. smt(expgK expM).
          + rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 2 2; if => //.
            + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 1 1; if => //.
          + auto => /> &1 &2 *. smt(expgK expM).
          auto => /> &1 &2 *. smt(expgK expM).
        if {1} => //.
        + rcondt {1} ^if. auto => /#.
          sp 2 0; if {1} => //. 
          + sp; seq 1 1: (#pre /\ ={t}). auto => />.
            if => //. auto => /> &1 &2 *. smt(expgK expM).
            + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
              if => //. smt(expgK expM).
              + rcondf {1} ^if. auto => /#.
                rcondf {2} ^if. auto => /#.
                rcondf {1} ^if. auto => /#.
                rcondf {2} ^if. auto => /#.
                sp 2 2; if => //. 
                + auto => /> *. do split; smt(mem_set get_setE expgK expM).
                auto => /> *. do split; smt(mem_set get_setE expgK expM).
              rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if{2}. auto => /#.
              rcondf {2} ^if{2}. auto => /#.
              sp 1 1; if => //. 
              + auto => /> &1 &2 *.
              auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            seq 1 1: (#pre /\ ={k}). auto => />.
            if => //. smt(expgK expM).
            + rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if{2}. auto => /#.
              rcondf {2} ^if{2}. auto => /#.
              sp 2 2; if => //. 
              + auto => /> &1 &2 *.
              auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 1 1; if => //. 
            + auto => /> &1 &2 *.
            auto => /> &1 &2 *. smt(expgK expM).
          sp; seq 1 1: (#pre /\ ={t}). auto => />.
          if => //. auto => /> &1 &2 *. smt(expgK expM).
          + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
            if => //. smt(expgK expM).
            + rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if{2}. auto => /#.
              rcondf {2} ^if{2}. auto => /#.
              sp 2 2; if => //. 
              + auto => /> *. do split; smt(mem_set get_setE expgK expM).
              auto => /> *. do split; smt(mem_set get_setE expgK expM).
            rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 1 1; if => //. 
            + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          seq 1 1: (#pre /\ ={k}). auto => />.
          if => //. smt(expgK expM).
          + rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 2 2; if => //. 
            + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 1 1; if => //. 
          + auto => /> &1 &2 *. smt(expgK expM).
          auto => /> &1 &2 *. smt(expgK expM).
        rcondf {1} ^if. auto => /#.
        rcondf {1} ^if. auto => /#.
        sp; seq 1 1: (#pre /\ ={t}). auto => />.
        if => //. auto => /> &1 &2 *. smt(expgK loggK expM).
        + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
          if => //. auto => /> &1 &2 *. smt(expgK expM).
          + rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            sp 2 2; if => //. 
            + sp 1 1; if => //.
              + auto => /> *. do split; smt(mem_set get_setE expgK expM). 
              auto => /> *. do split; smt(mem_set get_setE expgK expM).
            if => //.
            + auto => /> *. do split; smt(mem_set get_setE expgK expM in_fsetU1). 
            auto => /> *. do split; smt(mem_set get_setE expgK expM).
          rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 1 1; if => //. 
          + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
        seq 1 1: (#pre /\ ={k}). auto => />.
        if => //. smt(expgK expM).
        + rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 2 2; if => //. 
          + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
        rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        rcondf {1} ^if{2}. auto => /#.
        rcondf {2} ^if{2}. auto => /#.
        sp 1 1; if => //. 
        + auto => /> &1 &2 *. smt(expgK expM).
        auto => /> &1 &2 *. smt(expgK expM).
      rcondt {1} ^if. auto => /#.
      sp 4 0; if {1} => //.
      + if {1} => //. 
        + rcondt {1} ^if. auto => /#.
          rcondt {1} ^if. auto => />. smt(expgK expM).
          sp; seq 1 1: (#pre /\ ={t}). auto => />.
          if => //. auto => /> &1 &2 *. smt(expgK expM).
          + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
            if => //. smt(expgK expM loggK).
            + rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              sp 2 2; if => //. 
              + auto => /> *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
              auto => /> *. do split; smt(mem_set get_setE expgK expM).
            rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 1 1; if => //.
            + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          seq 1 1: (#pre /\ ={k}). auto => />.
          if => //. smt(expgK expM loggK).
          + rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 2 2; if => //. 
            + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 1 1; if => //. 
          + auto => /> &1 &2 *. smt(expgK expM).
          auto => /> &1 &2 *. smt(expgK expM).
        rcondt {1} ^if. auto => /#.
        rcondt {1} ^if. auto => />. smt(expgK expM).
        sp; seq 1 1: (#pre /\ ={t}). auto => />.
        if => //. auto => /> &1 &2 *. smt(expgK expM loggK).
        + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
          if => //. smt(expgK expM loggK).
          + rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            sp 2 2; if => //. 
            + sp 1 1; if => //. 
              + auto => /> *. do split; smt(mem_set get_setE expgK expM). 
              auto => /> *. do split; smt(mem_set get_setE expgK expM).
            if => //.
            + auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
            auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
          rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 1 1; if => //. 
          + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE expgK expM).
          auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE expgK expM).
        seq 1 1: (#pre /\ ={k}). auto => />.
        if => //. smt(expgK expM).
        + rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 2 2; if => //. 
          + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
          auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
        rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        rcondf {1} ^if{2}. auto => /#.
        rcondf {2} ^if{2}. auto => /#.
        sp 1 1; if => //. 
        + auto => /> &1 &2 *. smt(expgK expM in_fsetU1).
        auto => /> &1 &2 *. split. smt(loggK in_fsetU1). smt(expgK expM in_fsetU1).
      rcondf {1} ^if. auto => />. smt(expgK expM loggK).
      rcondf {1} ^if. auto => /#.
      rcondf {1} ^if. auto => /#.
      sp; seq 1 1: (#pre /\ ={t}). auto => />.
      if => //. auto => /> &1 &2 *. smt(expgK loggK expM).
      + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
        if => //. smt(expgK expM).
        + rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          sp 2 2; if => //. 
          + sp 1 1; if => //.
            + auto => /> *. do split; smt(mem_set get_setE expgK expM). 
            auto => /> *. do split; smt(mem_set get_setE expgK expM).
          if => //.
          + auto => /> *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
          auto => /> *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
        rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        rcondf {1} ^if{2}. auto => /#.
        rcondf {2} ^if{2}. auto => /#.
        sp 1 1; if => //. 
        + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
        auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
      seq 1 1: (#pre /\ ={k}). auto => />.
      if => //. smt(expgK expM).
      + rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        rcondf {1} ^if{2}. auto => /#.
        rcondf {2} ^if{2}. auto => /#.
        sp 2 2; if => //. 
        + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
        auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
      rcondf {1} ^if. auto => /#.
      rcondf {2} ^if. auto => /#.
      rcondf {1} ^if{2}. auto => /#.
      rcondf {2} ^if{2}. auto => /#.
      sp 1 1; if => //. 
      + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE expgK expM).
      auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE expgK expM). (* got until here !!!! *)
    if {1} => //.
    + rcondt {1} ^if. auto => /#.
      sp 4 0; if {1} => //.
      + if {1} => //.
        + rcondt {1} ^if. auto => /#.
          rcondt {1} ^if. auto => />. smt(expgK expM loggK).
          sp; seq 1 1: (#pre /\ ={t}). auto => />.
          if => //. auto => /> &1 &2 *.  smt(expgK expM).
          + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
            if => //. smt(expgK expM).
            + rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              rcondf {1} ^if. auto => /#.
              rcondf {2} ^if. auto => /#.
              sp 2 2; if => //. 
              + auto => /> *. do split; smt(mem_set get_setE expgK expM).
              auto => /> *. do split; smt(mem_set get_setE expgK expM).
            rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 1 1; if => //. 
            + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
            auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          seq 1 1: (#pre /\ ={k}). auto => />.
          if => //. smt(expgK expM).
          + rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 2 2; if => //. 
            + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM). 
            auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 1 1; if => //. 
          + auto => /> &1 &2 *. smt(expgK expM).
          auto => /> &1 &2 *. smt(expgK expM).
        rcondt {1} ^if. auto => /#.
        rcondt {1} ^if. auto => />. smt(expgK expM loggK).
        sp; seq 1 1: (#pre /\ ={t}). auto => />.
        if => //. auto => /> &1 &2 *. smt(expgK expM).
        + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
          if => //. smt(expgK expM).
          + rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            sp 2 2; if => //.
            + sp 1 1; if => //.
              + auto => /> *. do split; smt(mem_set get_setE expgK expM). 
              auto => /> *. do split; smt(mem_set get_setE expgK expM).
            if => //.
            + auto => /> *. do split; smt(mem_set get_setE expgK expM).
            auto => /> *. do split; smt(mem_set get_setE expgK expM).
          rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 1 1; if => //. 
          + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
        seq 1 1: (#pre /\ ={k}). auto => />.
        if => //. smt(expgK expM).
        + rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 2 2; if => //. 
          + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
          auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM).
        rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        rcondf {1} ^if{2}. auto => /#.
        rcondf {2} ^if{2}. auto => /#.
        sp 1 1; if => //. 
        + auto => /> &1 &2 *. smt(expgK expM).
        auto => /> &1 &2 *. smt(expgK expM).
      if {1} => //.
      + rcondt {1} ^if. auto => /#.
        rcondf {1} ^if. auto => />. smt(expgK expM loggK).
        sp; seq 1 1: (#pre /\ ={t}). auto => />.
        if => //. auto => /> &1 &2 *. smt(expgK expM).
        + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
          if => //. auto => /> &1 &2 *. smt(expgK expM).
          + rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            sp 2 2; if => //.
            + sp 1 1; if => //.
              + auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
              auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
            if => //.
            + auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
            auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
          rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 1 1; if => //. 
          + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
          auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
        seq 1 1: (#pre /\ ={k}). auto => />.
        if => //. auto => /> &1 &2 *. smt(expgK expM).
        + rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 2 2; if => //. 
          + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
          auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
        rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        rcondf {1} ^if{2}. auto => /#.
        rcondf {2} ^if{2}. auto => /#.
        sp 1 1; if => //. 
        + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
        auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
      rcondf {1} ^if. auto => /#.
      sp 1 0; if {1} => //.
      + sp; seq 1 1: (#pre /\ ={t}). auto => />.
        if => //. auto => /> &1 &2 *. smt(expgK expM loggK).
        + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
          if => //. smt(loggK expgK expM).
          + rcondf {1} ^if. auto => /#.
            rcondf {2} ^if. auto => /#.
            rcondf {1} ^if{2}. auto => /#.
            rcondf {2} ^if{2}. auto => /#.
            sp 2 2; if => //. 
            + auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
            auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
          rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 1 1; if => //. 
          + auto => /> &1 &2 *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
          auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
        seq 1 1: (#pre /\ ={k}). auto => />.
        if => //. smt(loggK expgK expM).
        + rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          rcondf {1} ^if{2}. auto => /#.
          rcondf {2} ^if{2}. auto => /#.
          sp 2 2; if => //. 
          + auto => /> &1 &2 *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
          auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
        rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        rcondf {1} ^if{2}. auto => /#.
        rcondf {2} ^if{2}. auto => /#.
        sp 1 1; if => //. 
        + auto => /> &1 &2 *. smt(loggK expgK expM in_fsetU1).
        auto => /> &1 &2 *. smt(loggK expgK expM in_fsetU1).
      sp; seq 1 1: (#pre /\ ={t}). auto => />.
      if => //. auto => /> &1 &2 *. smt(loggK expgK expM).
      + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
        if => //. auto => /> &1 &2 *. smt(loggK expgK expM).
        + rcondf {1} ^if. auto => /#.
          rcondf {2} ^if. auto => /#.
          sp 2 2; if => //. 
          + sp 1 1; if => //.
            + auto => /> *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
            auto => /> *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
          if => //.
          + auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
          auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
        rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        rcondf {1} ^if{2}. auto => /#.
        rcondf {2} ^if{2}. auto => /#.
        sp 1 1; if => //. 
        + auto => /> &1 &2 *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
        auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
      seq 1 1: (#pre /\ ={k}). auto => />.
      if => //. auto => /> &1 &2 *. smt(loggK expgK expM).
      + rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        rcondf {1} ^if{2}. auto => /#.
        rcondf {2} ^if{2}. auto => /#.
        sp 2 2; if => //. 
        + auto => /> &1 &2 *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
        auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
      rcondf {1} ^if. auto => /#.
      rcondf {2} ^if. auto => /#.
      rcondf {1} ^if{2}. auto => /#.
      rcondf {2} ^if{2}. auto => /#.
      sp 1 1; if => //. 
      + auto => /> &1 &2 *. smt(loggK expgK expM in_fsetU1).
      auto => /> &1 &2 *. split. smt(loggK in_fsetU1). smt(loggK expgK expM in_fsetU1). 
    rcondf {1} ^if. auto => /#.
    sp; seq 1 1: (#pre /\ ={t}). auto => />.
    if => //. smt(loggK expgK expM).
    + sp 1 1; seq 1 1: (#pre /\ ={k}). auto => />.
      if => //. smt(loggK expgK expM).
      + rcondf {1} ^if. auto => /#.
        rcondf {2} ^if. auto => /#.
        sp 2 2; if => //.
        + sp 1 1; if => //.
          + auto => /> *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
          auto => /> *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
        if => //.
        + auto => /> *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1).
        auto => /> *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
      rcondf {1} ^if. auto => /#.
      rcondf {2} ^if. auto => /#.
      rcondf {1} ^if{2}. auto => /#.
      rcondf {2} ^if{2}. auto => /#.
      sp 1 1; if => //. 
      + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
      auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
    seq 1 1: (#pre /\ ={k}). auto => />.
    if => //. smt(loggK expgK expM).
    + rcondf {1} ^if. auto => /#.
      rcondf {2} ^if. auto => /#.
      rcondf {1} ^if{2}. auto => /#.
      rcondf {2} ^if{2}. auto => /#.
      sp 2 2; if => //. 
      + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
      auto => /> &1 &2 *. split. smt(loggK in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
    rcondf {1} ^if. auto => /#.
    rcondf {2} ^if. auto => /#.
    rcondf {1} ^if{2}. auto => /#.
    rcondf {2} ^if{2}. auto => /#.
    sp 1 1; if => //. 
    + auto => /> &1 &2 *. smt(in_fsetU1 loggK expgK expM).
    auto => /> &1 &2 *. split. smt(loggK in_fsetU1). smt(in_fsetU1 loggK expgK expM).
  sp; seq 1 1: (#pre /\ ={t}). auto => />.
  if => //. auto => /> &1 &2 *. smt(loggK expgK expM).
  + sp; seq 1 1: (#pre /\ ={k}). auto => />.
    if => //. smt(loggK expgK expM).
    + sp 2 2; if => //.
      + sp 1 1; if => //.
        + sp 1 1; if => //.
          + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
          auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
        if => //.
        + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
        auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
      if => //.
      + sp 1 1; if => //.
        + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE expgK expM in_fsetU1). 
        auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
      if => //.
      + auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
      auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
    sp 1 1; if => //.
    + sp 1 1; if => //.
      + sp 1 1; if => //.
        + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
        auto => /> &1 &2 *.  do split; smt(mem_set get_setE expgK expM in_fsetU1).
      if => //.
      + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
      auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
    if => //.
    + sp 1 1; if => //.
      + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
      auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
    if => //.
    + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
    auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
  seq 1 1: (#pre /\ ={k}). auto => />.
  if => //. smt(loggK expgK expM).
  + sp 2 2; if => //.
    + sp 1 1; if => //.
      + sp 1 1; if => //.
        + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
        auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
      if => //.
      + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
      auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
    if => //.
    + sp 1 1; if => //.
      + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
      auto => /> &1 &2 *. split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
    if => //.
    + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
    auto => /> &1 &2 *.  split. smt(in_fsetU1). move => *. do split; smt(mem_set get_setE loggK expgK expM).
  sp 1 1; if => //.
  + sp 1 1; if => //.
    + sp 1 1; if => //.
      + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
      auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
    if => //.
    + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
    auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
  if => //.
  + sp 1 1; if => //.
    + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
    auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
  if => //.
  + auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1).
  auto => /> &1 &2 *. do split; smt(mem_set get_setE expgK expM in_fsetU1). *)
auto => />.*)
- move => &2 bad; proc; inline.
  sp; if => //; auto => />. 
  by rewrite dtag_ll dkey_ll //=.
- move => &1; proc; inline.
  sp; if => //.
  sp; auto; smt(dtag_ll dkey_ll).

+ proc; inline. admit. (*
  sp; if => //.
  sp; seq 1 1 : (#pre /\ sk{2} = y_m{1}). auto => />.
  + sp 2 1; if => //. smt().
    + sp 4 3; if => //.
      + auto => /> &1 &2 4? y_map m *. do split; ~2,3,9,10,24,28: smt(mem_set get_setE expgK expM in_fsetU1).
move => x xin.
have : ! (exists (j : int),
     (j \in y_map.[m + 1 <- y_m{1}]) /\
     x.`5 = g ^ oget y_map.[m + 1 <- y_m{1}].[j] /\
     x.`1 = x.`4 ^ oget y_map.[m + 1 <- y_m{1}].[j]) => ! (exists (j : int),
          (j \in y_map) /\
          x.`5 = g ^ oget y_map.[j] /\ x.`1 = x.`4 ^ oget y_map.[j]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE).
move => x xin.
have : ! (exists (j : int),
     (j \in y_map.[m + 1 <- y_m{1}]) /\
     x.`3 = g ^ oget y_map.[m + 1 <- y_m{1}].[j] /\
     x.`2 = x.`4 ^ oget y_map.[m + 1 <- y_m{1}].[j]) => ! (exists (j : int),
          (j \in y_map) /\
          x.`3 = g ^ oget y_map.[j] /\ x.`2 = x.`4 ^ oget y_map.[j]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE).
move => x xin.
have : ! (exists (j : int),
     (j \in y_map.[m + 1 <- y_m{1}]) /\
     x.`5 = g ^ oget y_map.[m + 1 <- y_m{1}].[j] /\
     x.`1 = x.`4 ^ oget y_map.[m + 1 <- y_m{1}].[j]) => ! (exists (j : int),
          (j \in y_map) /\
          x.`5 = g ^ oget y_map.[j] /\ x.`1 = x.`4 ^ oget y_map.[j]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE).
move => x xin.
have : ! (exists (j : int),
     (j \in y_map.[m + 1 <- y_m{1}]) /\
     x.`3 = g ^ oget y_map.[m + 1 <- y_m{1}].[j] /\
     x.`2 = x.`4 ^ oget y_map.[m + 1 <- y_m{1}].[j]) => ! (exists (j : int),
          (j \in y_map) /\
          x.`3 = g ^ oget y_map.[j] /\ x.`2 = x.`4 ^ oget y_map.[j]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE).
move => b.
rewrite mem_set.
move => [].
have : (exists (j : int), (j \in y_map) /\ b = g ^ oget y_map.[j]) => (exists (j : int),
  (j \in y_map.[m + 1 <- y_m{1}]) /\ b = g ^ oget y_map.[m + 1 <- y_m{1}].[j]).
move => [j jin].
exists j.
smt(mem_set get_setE).
smt(mem_set get_setE expgK expM in_fsetU1).
move => ->.
rewrite in_fsetU1 //=.
exists (m + 1). smt(mem_set get_setE).
move => x xeq.
split. 
smt(mem_set).
smt(mem_set get_setE expgK expM in_fsetU1).
      auto => /> &1 &2 4? y_map m *. do split; ~22: smt(mem_set get_setE expgK expM in_fsetU1). 
move => b bin.
have : (exists (j : int), (j \in y_map) /\ b = g ^ oget y_map.[j]) => (exists (j : int),
  (j \in y_map.[m + 1 <- y_m{1}]) /\ b = g ^ oget y_map.[m + 1 <- y_m{1}].[j]).
move => [j jin].
exists j.
smt(mem_set get_setE).
smt(mem_set get_setE expgK expM in_fsetU1). 

    auto => /> &1 &2 y_map m 44? inv inv2 inv3 inv4 inv5 inv6 *. do split; ~1,2,6,7,13,16: smt(mem_set get_setE expgK expM in_fsetU1).
move => x xin x3in x5in x5nin x4nin nex1 nex2 j.
have : ! (exists (j : int),
     (j \in y_map.[m + 1 <- y_m{1}]) /\
     x.`5 = g ^ oget y_map.[m + 1 <- y_m{1}].[j] /\
     x.`1 = x.`4 ^ oget y_map.[m + 1 <- y_m{1}].[j]) => ! (exists (j : int),
          (j \in y_map) /\
          x.`5 = g ^ oget y_map.[j] /\ x.`1 = x.`4 ^ oget y_map.[j]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
case (j = m + 1).
move => ->.
rewrite mem_set get_setE //=.
clear inv inv2 inv3 inv4 inv5 inv6.
smt(mem_set get_setE expgK expM in_fsetU1 pow_bij).
smt(mem_set get_setE).
move => x xin.
have : ! (exists (j : int),
     (j \in y_map.[m + 1 <- y_m{1}]) /\
     x.`3 = g ^ oget y_map.[m + 1 <- y_m{1}].[j] /\
     x.`2 = x.`4 ^ oget y_map.[m + 1 <- y_m{1}].[j]) => ! (exists (j : int),
          (j \in y_map) /\
          x.`3 = g ^ oget y_map.[j] /\ x.`2 = x.`4 ^ oget y_map.[j]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE).
move => x xin x3in x5in x5nin x4nin nex1 nex2 j.
have : ! (exists (j : int),
     (j \in y_map.[m + 1 <- y_m{1}]) /\
     x.`5 = g ^ oget y_map.[m + 1 <- y_m{1}].[j] /\
     x.`1 = x.`4 ^ oget y_map.[m + 1 <- y_m{1}].[j]) => ! (exists (j : int),
          (j \in y_map) /\
          x.`5 = g ^ oget y_map.[j] /\ x.`1 = x.`4 ^ oget y_map.[j]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
case (j = m + 1).
move => ->.
rewrite mem_set get_setE //=.
clear inv inv2 inv3 inv4 inv5 inv6. 
smt(mem_set get_setE expgK expM in_fsetU1 pow_bij).
smt(mem_set get_setE).
move => x xin.
have : ! (exists (j : int),
     (j \in y_map.[m + 1 <- y_m{1}]) /\
     x.`3 = g ^ oget y_map.[m + 1 <- y_m{1}].[j] /\
     x.`2 = x.`4 ^ oget y_map.[m + 1 <- y_m{1}].[j]) => ! (exists (j : int),
          (j \in y_map) /\
          x.`3 = g ^ oget y_map.[j] /\ x.`2 = x.`4 ^ oget y_map.[j]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE).
move => bj st t k ir bjin bjacc.
smt(mem_set get_setE expgK expM pow_bij).
move => b bin.
have : (exists (j : int), (j \in y_map) /\ b = g ^ oget y_map.[j]) => (exists (j : int),
  (j \in y_map.[m + 1 <- y_m{1}]) /\ b = g ^ oget y_map.[m + 1 <- y_m{1}].[j]).
move => [j jin].
exists j.
smt(mem_set get_setE).
smt(mem_set get_setE expgK expM in_fsetU1). *)
- move => &2 bad; proc; inline.
  sp; if => //; auto => />. 
  by rewrite dt_ll //=.
- move => &1; proc; inline.
  sp; if => //; auto => />.
  by rewrite dt_ll //=.

+ proc; inline. admit. (*
  sp; if => //.
  sp; if => //. auto => /#.
  match {1} => //.
  + match None {2} ^match. auto => /#.
    sp; seq 1 1: (#pre /\ x_n{1} = sk{2}). auto => />.
    + sp 5 3; if => //.
      + auto => /> &1 &2 3? x_map n 31? inv 18? inv2 *. do split; ~3..6,9..13,19,28: smt(mem_set get_setE expgK expM in_fsetU1).
move => x xin x3in.
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`2 = x.`3 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`2 = x.`3 ^ oget x_map.[i0]). 
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE).
move => x.
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`2 = x.`3 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`2 = x.`3 ^ oget x_map.[i0]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`1 = x.`5 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`1 = x.`5 ^ oget x_map.[i0]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE).
move => x xin x3in.
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`1 = x.`5 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`1 = x.`5 ^ oget x_map.[i0]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE expgK expM in_fsetU1).
move => x xin x3in.
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`1 = x.`5 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`1 = x.`5 ^ oget x_map.[i0]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE expgK expM in_fsetU1).

move => x xin x3in.
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`2 = x.`3 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`2 = x.`3 ^ oget x_map.[i0]). 
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE expgK expM in_fsetU1).
move => x.
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`2 = x.`3 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`2 = x.`3 ^ oget x_map.[i0]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`1 = x.`5 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`1 = x.`5 ^ oget x_map.[i0]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE).
move => x xin x3in.
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`1 = x.`5 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`1 = x.`5 ^ oget x_map.[i0]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE expgK expM in_fsetU1).
move => x xin x3in.
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`1 = x.`5 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`1 = x.`5 ^ oget x_map.[i0]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE expgK expM in_fsetU1).
move => x xin x3in.
have: ! (exists (i0 : int),
     (i0 \in x_map.[n + 1 <- sk{2}]) /\
     x.`4 = g ^ oget x_map.[n + 1 <- sk{2}].[i0] /\
     x.`1 = x.`5 ^ oget x_map.[n + 1 <- sk{2}].[i0]) => ! (exists (i0 : int),
          (i0 \in x_map) /\ x.`4 = g ^ oget x_map.[i0] /\ x.`1 = x.`5 ^ oget x_map.[i0]).
rewrite implybNN.
move => [i iin].
exists i.
smt(mem_set get_setE expgK expM in_fsetU1).
smt(mem_set get_setE expgK expM in_fsetU1).
move => m.
split; 2: by smt(mem_set get_setE in_fsetU1).
rewrite in_fsetU1.
move => [min|meq].
+ have := inv m.
  rewrite min //=.
  move => [i0 i0in].
  exists i0.
  smt(mem_set get_setE).
exists (n + 1).
smt(mem_set get_setE).

+ move => x0 y0 b0 tqeq.
      have := inv2 x0 y0 b0 tqeq.
      move => [H1|H2]. 
      + left.
        move : H1 => [i'] t k ir'' H1.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set). 

      auto => /> &1 &2 3? x_map n 31? inv *. do split; ~18: smt(mem_set get_setE expgK expM in_fsetU1).
move => m.
split; 2: by smt(mem_set get_setE in_fsetU1).
rewrite in_fsetU1.
move => [min|meq]. 
+ have := inv m.
  rewrite min //=.
  move => [i0 i0in].
  exists i0.
  smt(mem_set get_setE).
exists (n + 1).
smt(mem_set get_setE).
  match Some {2} ^match. auto => /#.
  auto => />. *)
- move => &2 bad; proc; inline. 
  sp; if => //.
  sp; if => //; match; auto => />. 
  by rewrite dt_ll //=.
- move => &1; proc; inline.
  sp; if => //.
  sp; if => //; match; auto => />.
  by rewrite dt_ll //=.

+ proc; inline. admit. (*
  sp; if => //.
  sp; match {1} => //.
  + match None {2} ^match => //. auto => /#.
  match Some {2} ^match => //. auto => /#.
  match {1} => //.
  + match None {2} ^match. auto => /#.
    seq 1 1: (#pre /\ ={sk}). auto => />.
    sp; if => //.
    + sp 2 2; if {1} => //.
      + sp; seq 1 1: (#pre /\ ={ts}). auto => />.
        rcondt {1} ^if. auto => /#.
        rcondt {2} ^if. auto => /#.
        sp 3 3; if => //.
        + auto => /> &1 &2 *. 
        auto => /> &1 &2 57? inv *. do split; ~29: smt(mem_set get_setE loggK expgK expM in_fsetU1 pow_bij).
        move => x0 y0 b0 tqeq.
        have := inv x0 y0 b0 tqeq.
        move => [H1|H2].
        + smt().
        move : H2 => [i'] t k ir H2.
        right. exists i'.
        by smt(get_setE).
      sp; seq 1 1: (#pre /\ ={ts}). auto => />.
      rcondt {1} ^if. auto => /#.
      rcondt {2} ^if. auto => /#.
      sp 3 3; if => //.
      + auto => /> &1 &2 57? inv *. do split; ~17,29: smt(mem_set get_setE loggK expgK expM in_fsetU1). 
clear inv.
smt(mem_set get_setE loggK expgK expM in_fsetU1 pow_bij).
+ move => x0 y0 b0 tqeq.
have := inv x0 y0 b0 tqeq.
move => [H1|H2]; 1: by smt().
right.
move : H2 => [i'] t k ir'' H2.
exists i'. 
by smt(get_setE).     
      auto => /> &1 &2 57? inv *. do split; ~17,29: smt(mem_set get_setE loggK expgK expM in_fsetU1 pow_bij).
clear inv.
smt(mem_set get_setE loggK expgK expM in_fsetU1 pow_bij).
+ move => x0 y0 b0 tqeq.
have := inv x0 y0 b0 tqeq.
move => [H1|H2]; 1: by smt().
right.
move : H2 => [i'] t k ir'' H2.
exists i'. 
by smt(get_setE).
    auto => /> &1 &2 *. do split; smt(mem_set get_setE loggK expgK expM in_fsetU1 pow_bij).
  match Some {2} ^match. auto => /#.
  auto => />. *)
- move => &2 bad; proc; inline. 
  sp; if => //.
  sp; match => //. 
  match => //. 
  seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dt_ll.
  + sp; if => //; auto => />.
    by rewrite dtag_ll.
  hoare. 
  by auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  match; auto => />.
  seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dt_ll.
  + sp; if => //; auto => />.
    by rewrite dtag_ll.
  hoare. 
  by auto => />.

+ proc; inline. admit. (*
  sp; if => //.
  sp; match {1} => //.
  + match None {2} ^match. auto => /#.
    auto => />.
  match Some {2} ^match. auto => /#.
  match {1} => //.
  + match Pending_mod {2} ^match. auto => /#.
    sp; seq 1 1 : (#pre /\ ={ts}). auto => />.
    if => //. auto => /> &1 &2 *. smt(expM expgK loggK).
      sp 3 3; if => //. smt(expM expgK loggK).
      + sp 1 1; if => //.
        + sp 1 1; if => //. smt(expM expgK loggK).
          + auto => /> &1 &2 *. do split; smt(get_setE mem_set in_fsetU1 loggK expgK expM).
          auto => /> &1 &2 *. do split; ~2: smt(get_setE mem_set in_fsetU1 loggK expgK expM). smt(get_setE mem_set in_fsetU1 loggK expgK expM).
        if => //.  smt(expM expgK loggK).
        + auto => /> &1 &2 *. do split; smt(get_setE mem_set in_fsetU1 loggK expgK expM).
        auto => /> &1 &2 *. do split; smt(get_setE mem_set in_fsetU1 loggK expgK expM).
      if => //.
      + sp 1 1; if => //. smt(get_setE mem_set in_fsetU1 loggK expgK expM).
        + auto => /> &1 &2 53? inv *. do split; ~1,6,8,14,20: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => x0.
rewrite mem_set.
move => []. smt(mem_set get_setE).
move => -> //=.
smt(mem_set get_setE loggK expgK expM).
move => x0.
rewrite mem_set //=.
move => []. smt(mem_set get_setE loggK expgK expM).
move => -> //=.
smt(mem_set get_setE loggK expgK expM).
move => b0 x0 y0.
rewrite mem_set //=.
move => [].
smt(get_setE mem_set loggK expgK expM).
move => [#] -> -> ->.
split. smt(get_setE loggK expgK expM pow_bij).
smt(get_setE loggK expgK expM pow_bij).
move => x0.
rewrite mem_set.
move => []. smt(in_fsetU1).
move => -> //=.
smt(in_fsetU1 loggK expgK expM).
        move => x0 y0 b0 tqeq.
        have := inv x0 y0 b0 tqeq.
        move => [H1|H2].
        move : H1 => [i'] t k ir H1.
        left. exists i'.
        by smt(get_setE).
        smt().
        auto => /> &1 &2 51? inv ? inv2 *. do split; ~6,8,14,19,20: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => x0.
rewrite mem_set //=.
move => []. smt(mem_set get_setE loggK expgK expM).
move => -> //=.
smt(mem_set get_setE loggK expgK expM).
move => b0 x0 y0.
rewrite mem_set //=.
move => [xin|].
have->: (g ^ sk_ce{2} = pt{1}.`2) by smt().
split; smt(get_setE mem_set loggK expgK expM).
move => [#] -> -> ->.
split. smt(mem_set get_setE loggK expgK expM pow_bij).
smt(get_setE loggK expgK expM pow_bij).
move => x0.
rewrite mem_set.
move => [x0in|x0eq]. smt(in_fsetU1).
split. smt().
split. smt().
smt(in_fsetU1).
move => i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m1 m2 m2' teq stnn tr.
        have := inv i{2} i' m1 m2 m2'. 
        smt().
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => m1 m2 m2'.
      rewrite i'eq !get_set_sameE //=.
      have := inv i{2} i0. 
      smt().
move => x0 y0 b0 tqeq.
have := inv2 x0 y0 b0 tqeq.
move => [H1|H2].
move : H1 => [i'] t k ir H1.
left. exists i'.
by smt(get_setE).
smt().
      if => //. smt(get_setE mem_set in_fsetU1 loggK expgK expM).
      + auto => /> &1 &2 52? inv *. do split; ~1,6,8,14,18: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => x0.
rewrite mem_set.
move => []. smt(mem_set get_setE).
move => -> //=.
smt(mem_set get_setE loggK expgK expM).
move => x0.
rewrite mem_set //=.
move => []. smt(mem_set get_setE loggK expgK expM).
move => -> //=.
smt(mem_set get_setE loggK expgK expM).
move => b0 x0 y0.
rewrite mem_set //=.
move => []. 
move => *.
split. smt(mem_set get_setE loggK expgK expM pow_bij).
smt(get_setE loggK expgK expM pow_bij).
move => [#] -> -> ->.
split. smt(get_setE loggK expgK expM pow_bij).
smt(get_setE loggK expgK expM pow_bij).
move => x0.
rewrite mem_set.
move => []. smt(in_fsetU1).
move => -> //=.
smt(in_fsetU1 loggK expgK expM).
move => x0 y0 b0 tqeq.
have := inv x0 y0 b0 tqeq.
move => [H1|H2].
move : H1 => [i'] t k ir H1.
left. exists i'.
by smt(get_setE).
smt().
      auto => /> &1 &2 50? inv ? inv2 *. do split; ~1,6,8,14,17,18: smt(mem_set get_setE loggK expgK expM).
move => x0.
rewrite mem_set.
move => []. smt(mem_set get_setE).
move => -> //=.
smt(mem_set get_setE loggK expgK expM).
move => x0.
rewrite mem_set //=.
move => []. smt(mem_set get_setE loggK expgK expM).
move => -> //=.
smt(mem_set get_setE loggK expgK expM).
move => b0 x0 y0.
rewrite mem_set //=.
move => [xin|].
have->: (g ^ sk_ce{2} = pt{1}.`2) by smt().
split; smt(get_setE mem_set loggK expgK expM).
move => [#] -> -> ->.
split. smt(mem_set get_setE loggK expgK expM).
smt(get_setE loggK expgK expM).
move => x0.
rewrite mem_set.
move => []. smt(in_fsetU1).
move => -> //=.
smt(in_fsetU1 loggK expgK expM).
move => i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m1 m2 m2' teq stnn tr.
        have := inv i{2} i' m1 m2 m2'. 
        smt().
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => m1 m2 m2'.
      rewrite i'eq !get_set_sameE //=.
      have := inv i{2} i0. 
      smt().
move => x0 y0 b0 tqeq.
have := inv2 x0 y0 b0 tqeq.
move => [H1|H2].
move : H1 => [i'] t k ir H1.
left. exists i'.
by smt(get_setE).
smt().
    rcondf {1} ^if. auto => /#.
    rcondf {2} ^if. auto => /#.
    + sp 2 2; if => //.
      + sp 1 1; if => //. smt(expM expgK loggK).
        + auto => /> &1 &2 *. do split; smt(get_setE mem_set in_fsetU1 loggK expgK expM). 
        auto => /> &1 &2 *. do split; smt(get_setE mem_set in_fsetU1 loggK expgK expM).
      if => //. auto => /> &1 &2 *. split. smt(expM expgK loggK). smt(expM expgK loggK).
      + auto => /> &1 &2 50? inv *. do split; ~6:smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => x0 y0 b0 tqeq.
have := inv x0 y0 b0 tqeq.
move => [H1|H2].
move : H1 => [i'] t k ir H1.
left. exists i'.
by smt(get_setE).
smt().
      auto => /> &1 &2 50? inv *. do split; ~6: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => x0 y0 b0 tqeq.
have := inv x0 y0 b0 tqeq.
move => [H1|H2].
move : H1 => [i'] t k ir H1.
left. exists i'.
by smt(get_setE).
smt().
  + match Accepted_mod {2} ^match. auto => /#.
    auto => />.
  match Aborted_mod {2} ^match. auto => /#.
  auto => />. *)
- move => &2 bad; proc; inline. 
  sp; if => //.
  sp; match => //. 
  match => //.
  seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dtag_ll.
  hoare. 
  by auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  match; auto => />.
  by rewrite dtag_ll.

+ proc; inline. admit. (*
  sp; if => //.
  sp; match {1} => //.
  + match None {2} ^match. auto => /#.
    auto => />.
  match Some {2} ^match. auto => /#.
  match {1} => //.
  + match Pending_mod {2} ^match. auto => /#.
    auto => />.
  + match Accepted_mod {2} ^match. auto => /#.
    if => //.
    + auto => &1 &2 *.
      rewrite /untested_partner_c.
      rewrite /get_partners_c /get_untested_partners_c.
      have->: (fdom
          (filter
             (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                get_trace val = Some t'{2}) Game4Ltk.s_smap{2})) = (fdom
          (filter
             (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                get_trace val = Some t'{1}) Red_Ltk.Red_O.s_smap{1})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      have->: (fdom
            (filter
               (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                  get_trace val = Some t'{2} /\ get_ir_test val = false)
               Game4Ltk.s_smap{2})) = (fdom
            (filter
               (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                  get_trace val = Some t'{1} /\ get_ir_test val = false)
               Red_Ltk.Red_O.s_smap{1})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      smt().
    + sp; seq 1 1 : (#pre /\ ={ks}). auto => />.
      if => //.
      + auto => /> &1 &2 *. 
        have->: t'{1} = t'{2}. smt().
        smt(get_setE mem_set expgK expM loggK).
      + auto => /> &1 &2 42? c1 c2 c3 c4 c5 c6 c7 c8 inv *. do split; ~2,9,18,19: smt(get_setE mem_set in_fsetU1 loggK expgK expM). 
move => x0.
rewrite mem_set.
move => []. 
move => *. split. 
rewrite mem_set //=.
smt(mem_set get_setE).
rewrite get_setE //=.
case : (x0 =
    ((oget t'{2}.`2).`1 ^ st'{2}.`2, st'{2}.`1 ^ st'{2}.`2, st'{2}.`1,
     g ^ st'{2}.`2, (oget t'{2}.`2).`1)). 
smt(get_setE). 
have->: st'{2}.`1 = t'{1}.`1.`1. smt().
have->: g ^ st'{2}.`2 = t'{1}.`1.`2. smt().
have->: st'{2}.`2 = loge t'{1}.`1.`2. smt(loggK expgK expM). smt(get_setE pow_bij loggK expgK expM).
move => -> //= x3in x4in i0 i0in x4eq x1eq x2eq.
smt(mem_set get_setE loggK expgK expM).
move => b0 x0 y0.
rewrite mem_set //=.
move => [].
smt(get_setE mem_set loggK expgK expM).
move => [#] -> -> ->.
smt(mem_set get_setE loggK expgK expM).
    + move => i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m1 m2 m2' teq stnn tr.
        have := c7 i{2} i' m1 m2 m2'. 
        smt().
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => m1 m2 m2'.
      rewrite i'eq !get_set_sameE //=.
      have := c7 i{2} i0. 
      smt().
      + move => x0 y0 b0 tqeq.
        have := inv x0 y0 b0 tqeq.
        move => [H1|H2]. 
        + left.
          move : H1 => [i'] t k ir'' H1.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).

      auto => /> &1 &2 48? c7 c8 inv *. do split; ~6,7: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
    + move => i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m1 m2 m2' teq stnn tr.
        have := c7 i{2} i' m1 m2 m2'. 
        smt().
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => m1 m2 m2'.
      rewrite i'eq !get_set_sameE //=.
      have := c7 i{2} i0. 
      smt(). 
      + move => x0 y0 b0 tqeq.
        have := inv x0 y0 b0 tqeq.
        move => [H1|H2]. 
        + left.
          move : H1 => [i'] t k ir'' H1.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).
  match Aborted_mod {2} ^match. auto => /#.
  auto => />. *)
- move => &2 bad; proc; inline.
  sp; if => //.
  sp; match => //. 
  match => //.
  if => //.
  sp; seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dkey_ll.
  hoare. 
  by auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  match; auto => />.
  if => //.
  sp; seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dkey_ll.
  hoare. 
  by auto => />.

+ proc; inline. admit. (*
  sp; if => //.
  sp; match {1} => //.
  + match None {2} ^match. auto => /#.
    auto => />.
  match Some {2} ^match. auto => /#.
  match {1} => //.
  + match Pending_mod {2} ^match. auto => /#.
    auto => />.
  + match Accepted_mod {2} ^match. auto => /#.
    if => //.
    + auto => /> &1 &2 46? c1 c2 c3 c4 c5 c6. clear c1 c2 c3 c4 c5 c6.
      rewrite /untested_partner_s.
      rewrite /get_partners_s /get_untested_partners_s.
      have->: (fdom 
          (filter
             (fun (_ : int) (val : pr_st_client instance_state) =>
                get_trace val = Some t'{2}) Game4Ltk.c_smap{2})) = (fdom
          (filter
             (fun (_ : int) (val : pr_st_client instance_state) =>
                get_trace val = Some t'{1}) Red_Ltk.Red_O.c_smap{1})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      have->: (fdom
            (filter
               (fun (_ : int) (val : pr_st_client instance_state) =>
                  get_trace val = Some t'{2} /\ get_ir_test val = false)
               Game4Ltk.c_smap{2})) = (fdom
            (filter
               (fun (_ : int) (val : pr_st_client instance_state) =>
                  get_trace val = Some t'{1} /\ get_ir_test val = false)
               Red_Ltk.Red_O.c_smap{1})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      smt().
    + sp; seq 1 1 : (#pre /\ ={ks}). auto => />.
      if {1} => //.
      + sp 1 0; if => //.
        + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU1 loggK expgK expM).
        + auto => /> &1 &2 47? inv ? inv2 inv3 *. do split; ~2,10,16..18: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => x0. 
rewrite mem_set //=.
move => [].
move => xin x3in x4in i0 i0in x4eq x1eq x2eq.
smt(mem_set get_setE).
move => -> //=.
move => *.
have->: t'{1} = t'{2}. smt().
have->: st'{1}.`2 = st'{2}.`2. smt().
have->: g ^ st'{2}.`1 = t'{2}.`1.`1. smt().
smt(mem_set get_setE).
smt(get_setE mem_set pow_bij loggK expgK expM).
move => i t1 t2.
case : (i = (b, j){2}); 2: by smt(get_setE).
move => -> //=.
have := inv (b, j){2} t1 t2.
smt(get_setE).
+ move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m1 m2 tag m1' tag'.
          have := inv2 (b,j){2} i' m1 m2 tag m1' tag'.
          smt().
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite i'eq get_set_sameE //=.
      rewrite get_set_neqE //=.
      move => m1 m2 tag m1' tag'.
      have := inv2 (b,j){2} i0 m1 m2 tag m1' tag'.
      smt(). 
+ move => x0 y0 b0 tqeq.
have := inv3 x0 y0 b0 tqeq.
move => [H1|H2]; 1: by smt().
right.
move : H2 => [i'] t k ir'' H2.
exists i'. 
by smt(get_setE). 
        auto => /> &1 &2 47? inv ? inv2 inv3 *.  do split; ~4..6: smt(get_setE mem_set in_fsetU1 loggK expgK expM). 
move => i t1 t2.
case : (i = (b, j){2}); 2: by smt(get_setE).
move => -> //=.
have := inv (b, j){2} t1 t2.
smt(get_setE).
+ move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m1 m2 tag m1' tag'.
          have := inv2 (b,j){2} i' m1 m2 tag m1' tag'.
          smt().
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite i'eq get_set_sameE //=.
      rewrite get_set_neqE //=.
      move => m1 m2 tag m1' tag'.
      have := inv2 (b,j){2} i0 m1 m2 tag m1' tag'.
      smt(). 
+ move => x0 y0 b0 tqeq.
have := inv3 x0 y0 b0 tqeq.
move => [H1|H2]; 1: by smt().
right.
move : H2 => [i'] t k ir'' H2.
exists i'. 
by smt(get_setE).
      sp 1 0; if => //.
      + auto => /> &1 &2 *.
          have->: t'{1} = t'{2}. smt().
          have->: st'{1}.`2 = st'{2}.`2. smt().
          smt(get_setE mem_set expgK expM loggK). 
      + auto => /> &1 &2 47? inv ? inv2 inv3 *. do split; ~2,6,16..18: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => x0. 
rewrite mem_set //=.
move => [].
move => xin x3in x4in i0 i0in x4eq x1eq x2eq.
split. smt(mem_set).
rewrite get_setE //=.
case (x0 =
    (t'{2}.`1.`2 ^ oget st'{2}.`2, t'{2}.`1.`2 ^ st'{2}.`1, g ^ st'{2}.`1,
     t'{2}.`1.`2, g ^ oget st'{2}.`2)).
smt(get_setE).
rewrite get_setE.
smt(loggK expgK expM pow_bij).
move => -> //=.
move => *.
have->: t'{1} = t'{2}. smt().
have->: st'{1}.`2 = st'{2}.`2. smt().
have->: g ^ st'{2}.`1 = t'{2}.`1.`1. smt().
smt(mem_set get_setE).
move => x0. clear inv inv2 inv3.
rewrite mem_set //=.
move => []. 
move => x0in x3in x4in inex jnex.
have->: t'{1} = t'{2}. smt().
have->: st'{1}.`2 = st'{2}.`2. smt().
have->: g ^ st'{2}.`1 = t'{2}.`1.`1. smt().
have->: st'{2}.`1 = loge t'{1}.`1.`1. smt(loggK expgK expM). 
smt(get_setE pow_bij loggK expgK expM).
smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => i t1 t2.
case : (i = (b, j){2}); 2: by smt(get_setE).
move => -> //=.
have := inv (b, j){2} t1 t2.
smt(get_setE).
+ move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m1 m2 tag m1' tag'.
          have := inv2 (b,j){2} i' m1 m2 tag m1' tag'.
          smt().
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite i'eq get_set_sameE //=.
      rewrite get_set_neqE //=.
      move => m1 m2 tag m1' tag'.
      have := inv2 (b,j){2} i0 m1 m2 tag m1' tag'.
      smt(). 
+ move => x0 y0 b0 tqeq.
have := inv3 x0 y0 b0 tqeq.
move => [H1|H2]; 1: by smt().
right.
move : H2 => [i'] t k ir'' H2.
exists i'. 
by smt(get_setE).
      auto => /> &1 &2 47? inv ? inv2 inv3 *. do split; ~1,4..6: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
have: t'{1} = t'{2} by smt().
smt(mem_set get_setE loggK expgK expM).
move => i t1 t2.
case : (i = (b, j){2}); 2: by smt(get_setE).
move => -> //=.
have := inv (b, j){2} t1 t2.
smt(get_setE).
+ move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m1 m2 tag m1' tag'.
          have := inv2 (b,j){2} i' m1 m2 tag m1' tag'.
          smt().
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite i'eq get_set_sameE //=.
      rewrite get_set_neqE //=.
      move => m1 m2 tag m1' tag'.
      have := inv2 (b,j){2} i0 m1 m2 tag m1' tag'.
      smt(). 
+ move => x0 y0 b0 tqeq.
have := inv3 x0 y0 b0 tqeq.
move => [H1|H2]; 1: by smt().
right.
move : H2 => [i'] t k ir'' H2.
exists i'. 
by smt(get_setE). 
  match Aborted_mod {2} ^match. auto => /#.
  auto => />. *)
- move => &2 bad; proc; inline. 
  sp; if => //.
  sp; match => //. 
  match => //.
  if => //.
  sp; seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dkey_ll.
  hoare. 
  by auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  match; auto => />.
  if => //.
  sp; seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dkey_ll.
  hoare. 
  by auto => />.

+ proc; inline.
  sp; if => //.
  sp; match {1} => //.
  + match None {2} ^match. auto => /#.
    auto => />.
  match Some {2} ^match. auto => /#.
  match {1} => //.
  + match Honest_mod {2} ^match. auto => /#.
    if => //.
    + auto => /> &1 &2 46? c1 c2 c3 c4 c5 c6 *.
clear c1 c2 c3 c4 c5 c6.
split.
move => + ntpp.
have->: ! tested_pot_partner_c b{2} Game4Ltk.c_smap{2} Game4Ltk.s_smap{2}.
have := ntpp.
rewrite /tested_pot_partner_c.
rewrite /get_tested_pot_partner_c.
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
              (exists (m1o : pkey) (m2o : (pkey * tag) option),
                 get_trace val = Some ((b{2}, m1o), m2o)) /\
              get_ir_test val = true /\
              forall (j0 : int),
                (b{2}, j0) \in Red_Ltk.Red_O.s_smap{1} =>
                get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]) <>
                get_trace val) Red_Ltk.Red_O.c_smap{1})) = (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
             (exists (m1o : pkey) (m2o : (pkey * tag) option),
                get_trace val = Some ((b{2}, m1o), m2o)) /\
             get_ir_test val = true /\
             forall (j0 : int),
               (b{2}, j0) \in Game4Ltk.s_smap{2} =>
               get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j0]) <> get_trace val)
          Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split.
move => H.
split. smt(mem_set get_setE).
split. smt(mem_set get_setE).
split. smt(mem_set get_setE).
move => j0 j0in.
have->: get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j0]) = get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]). smt(mem_set get_setE).
have->: get_trace (oget Game4Ltk.c_smap{2}.[x]) = get_trace (oget Red_Ltk.Red_O.c_smap{1}.[x]). smt(mem_set get_setE).
smt().
move => H.
split. smt(mem_set get_setE).
split. smt(mem_set get_setE).
split. smt(mem_set get_setE).
move => j0 j0in.
have<-: get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j0]) = get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]). smt(mem_set get_setE).
have<-: get_trace (oget Game4Ltk.c_smap{2}.[x]) = get_trace (oget Red_Ltk.Red_O.c_smap{1}.[x]). smt(mem_set get_setE).
smt().
smt().
simplify.
move => + j pkin - /(_ j).
have : (b{2}, j) \in Red_Ltk.Red_O.s_smap{1}  by smt().
move => bjin //=.
rewrite /untested_partner_s.
rewrite /get_partners_s /get_untested_partners_s.
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                       get_trace val = Some (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j])))) Red_Ltk.Red_O.c_smap{1})) = (fdom
                (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                      get_trace val = Some (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j])))) Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
smt(mem_set get_setE).
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                      get_trace val = Some (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j]))) /\
                      get_ir_test val = false) Red_Ltk.Red_O.c_smap{1})) = (fdom (filter
                  (fun (_ : int) (val : pr_st_client instance_state) =>
                     get_trace val = Some (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j]))) /\
                     get_ir_test val = false) Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
admit. (* too much in context *)
smt().

move => + ntpp.
have->: ! tested_pot_partner_c b{2} Red_Ltk.Red_O.c_smap{1} Red_Ltk.Red_O.s_smap{1}.
have := ntpp.
rewrite /tested_pot_partner_c.
rewrite /get_tested_pot_partner_c.
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
              (exists (m1o : pkey) (m2o : (pkey * tag) option),
                 get_trace val = Some ((b{2}, m1o), m2o)) /\
              get_ir_test val = true /\
              forall (j0 : int),
                (b{2}, j0) \in Red_Ltk.Red_O.s_smap{1} =>
                get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]) <>
                get_trace val) Red_Ltk.Red_O.c_smap{1})) = (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
             (exists (m1o : pkey) (m2o : (pkey * tag) option),
                get_trace val = Some ((b{2}, m1o), m2o)) /\
             get_ir_test val = true /\
             forall (j0 : int),
               (b{2}, j0) \in Game4Ltk.s_smap{2} =>
               get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j0]) <> get_trace val)
          Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split.
move => H.
split. smt(mem_set get_setE).
split. smt(mem_set get_setE).
split. smt(mem_set get_setE).
move => j0 j0in.
have->: get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j0]) = get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]). smt(mem_set get_setE).
have->: get_trace (oget Game4Ltk.c_smap{2}.[x]) = get_trace (oget Red_Ltk.Red_O.c_smap{1}.[x]). smt(mem_set get_setE).
smt().
move => H.
split. smt(mem_set get_setE).
split. smt(mem_set get_setE).
split. smt(mem_set get_setE).
move => j0 j0in.
have<-: get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j0]) = get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]). smt(mem_set get_setE).
have<-: get_trace (oget Game4Ltk.c_smap{2}.[x]) = get_trace (oget Red_Ltk.Red_O.c_smap{1}.[x]). smt(mem_set get_setE).
smt().
smt().
simplify.
move => + j pkin - /(_ j).
have : (b{2}, j) \in Red_Ltk.Red_O.s_smap{1}  by smt().
move => bjin //=.
rewrite /untested_partner_s.
rewrite /get_partners_s /get_untested_partners_s.
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                       get_trace val = Some (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j])))) Red_Ltk.Red_O.c_smap{1})) = (fdom
                (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                      get_trace val = Some (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j])))) Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
smt(mem_set get_setE).
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                      get_trace val = Some (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j]))) /\
                      get_ir_test val = false) Red_Ltk.Red_O.c_smap{1})) = (fdom (filter
                  (fun (_ : int) (val : pr_st_client instance_state) =>
                     get_trace val = Some (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j]))) /\
                     get_ir_test val = false) Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
admit. (* too much in context *)
smt().

if => //.
+ auto => /> &1 &2 43? c1 c2 c3 c4 c5 c6 c7 c8 c9 *.
clear c1 c2 c3 c4 c5 c6 c7 c8 c9.
split.
move => j bjin H.
exists j.
have->: untested_partner_s (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j])))
   Game4Ltk.c_smap{2} = untested_partner_s
     (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j]))) Red_Ltk.Red_O.c_smap{1}.
rewrite /untested_partner_s.
rewrite /get_partners_s /get_untested_partners_s.
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                       get_trace val = Some (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j])))) Red_Ltk.Red_O.c_smap{1})) = (fdom
                (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                      get_trace val = Some (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j])))) Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
smt(mem_set get_setE).
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                      get_trace val = Some (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j]))) /\
                      get_ir_test val = false) Red_Ltk.Red_O.c_smap{1})) = (fdom (filter
                  (fun (_ : int) (val : pr_st_client instance_state) =>
                     get_trace val = Some (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j]))) /\
                     get_ir_test val = false) Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
smt(mem_set get_setE).
smt().
smt().
move => j bjin H.
exists j.
have<-: untested_partner_s (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j])))
   Game4Ltk.c_smap{2} = untested_partner_s
     (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j]))) Red_Ltk.Red_O.c_smap{1}.
rewrite /untested_partner_s.
rewrite /get_partners_s /get_untested_partners_s.
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                       get_trace val = Some (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j])))) Red_Ltk.Red_O.c_smap{1})) = (fdom
                (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                      get_trace val = Some (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j])))) Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
smt(mem_set get_setE).
have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                      get_trace val = Some (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j]))) /\
                      get_ir_test val = false) Red_Ltk.Red_O.c_smap{1})) = (fdom (filter
                  (fun (_ : int) (val : pr_st_client instance_state) =>
                     get_trace val = Some (oget (get_trace (oget Game4Ltk.s_smap{2}.[b{2}, j]))) /\
                     get_ir_test val = false) Game4Ltk.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
smt(mem_set get_setE).
smt().
smt().
sp 1 1; if => //.
    rcondt {1} ^if. auto => /#. 
    auto => />.
if => //.
rcondt {1} ^if. auto => /#. 
    auto => /> &1 &2 50? inv inv2 ? ? ? fresh npp nltkt *. do split; ~1,25: smt(get_setE mem_set in_fsetU1 loggK expgK expM). 
have : b{2} = g ^ sk{2}. smt(loggK expgK expM).
smt(pow_bij).
move => x xeq.
split. smt(mem_set).
split. smt().
have := inv2 x xeq.
move => [#] _ _ [i0 j0 [#] i0in x4eq x1eq x2eq j0in x3eq i0ncr j0ncr].
exists i0 j0.
do split; 1..7: smt().
rewrite in_fsetU1 negb_or.
split. smt().
have := inv (oget St_CDH_O.x_map{1}.[i0]) (loge x.`5) (oget St_CDH_O.y_map{1}.[j0]).
rewrite ComRing.mulrC expM expgK -x1eq ComRing.mulrC expM -x3eq -x2eq -x4eq xeq.
have->: x = (x.`1, x.`2, x.`3, x.`4, x.`5) by smt().
rewrite //=.
move => [[i2 tag key ir'] [# i2in i2acc i2test]|[i2 tag key ir'] [# i2in i2acc i2test]].
case (j0 = oget Red_Ltk.Red_O.b_inst{1}.[b{2}]) => jbeq; 2: by smt().

+ case : (! 1 <=
    card
      (get_partners_s
         (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]))) Red_Ltk.Red_O.c_smap{1})) => nop.
  
  
  + have : (untested_partner_s (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]))) Red_Ltk.Red_O.c_smap{1} = None).
    by rewrite /untested_partner_s ifF //=.
    move => nontp.
    have : tested_pot_partner_c b{2} Red_Ltk.Red_O.c_smap{1} Red_Ltk.Red_O.s_smap{1}.
    + rewrite /tested_pot_partner_c.
      rewrite /get_tested_pot_partner_c.
      rewrite /get_partners_s in nop.
      have->: (fdom
       (filter
          (fun (_ : int) (val : pr_st_client instance_state) =>
             (exists (m1o : pkey) (m2o : (pkey * tag) option),
                get_trace val = Some ((b{2}, m1o), m2o)) /\
             get_ir_test val = true /\
             forall (j1 : int),
               (b{2}, j1) \in Red_Ltk.Red_O.s_smap{1} =>
               get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j1]) <>
               get_trace val) Red_Ltk.Red_O.c_smap{1})) = fset1 i2.
      + apply in_eq_fset1. 
        move => x0.
        rewrite mem_fdom mem_filter /=.
        split.
        + admit. (* BAUSTELLE !!!! *)
        move => ->.
        do split; 1,3: by smt().
        + exists x.`4 (Some (x.`5, tag)).
          smt().
        admit. (* if there would be a server with the same trace it contradicts nop *)
      smt(fcard1).
    smt().
  have : untested_partner_s (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]))) Red_Ltk.Red_O.c_smap{1} = Some false.
  + rewrite /untested_partner_s.
    have->: get_partners_s (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]))) Red_Ltk.Red_O.c_smap{1} = fset1 i2.
    + rewrite /get_partners_s.
      apply in_eq_fset1. 
      move => x0.
      rewrite mem_fdom mem_filter /=.
      split.
      + admit. (* BAUSTELLE !!!! *)
      move => ->.
      split; 1: by smt().
      admit. (* trace equality *)
    rewrite ifT. by rewrite fcard1 //=.
    have->: (get_untested_partners_s (oget (get_trace (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j0]))) Red_Ltk.Red_O.c_smap{1}) = fset0.
    + rewrite /get_untested_partners_s.
      apply in_eq_fset0.
      move => x0.
      rewrite mem_fdom mem_filter !negb_and /=. 
      case (x0 = i2) => x0eq; 1: by smt().
      admit. 
    smt(fcards0).
  move => nuntp.
  rewrite negb_exists //= in nltkt.
  have := nltkt j0.
  have->: (b{2}, j0) \in Red_Ltk.Red_O.s_smap{1}. admit.
  rewrite nuntp //=.
have : x.`3 = i2.`1 by smt().
case : (b{2} = i2.`1).
move => ->>.
have : (i2.`1, i2.`2) \in Red_Ltk.Red_O.s_smap{1} by smt().
move => i2inRed.
have i2testRed : (get_ir_test (oget Red_Ltk.Red_O.s_smap{1}.[i2.`1, i2.`2])) by smt().
have := fresh i2.`2 i2inRed.
rewrite i2testRed //=.
smt().
smt().
  + match Corrupt_mod {2} ^match. auto => /#.
    auto => />.
  match Dishonest_mod {2} ^match. auto => /#.
  auto => />.
- move => &2 bad; proc; inline. 
  sp; if => //.
  sp; match => //. 
  match => //.
  by auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  match => //.
  by auto => />.

+ proc; inline.
  sp; if => //.
  sp; match {1} => //.
  + match None {2} ^match. auto => /#.
    auto => />.
  match Some {2} ^match. auto => /#.
  match {1} => //.
  + match Pending_mod {2} ^match. auto => /#.
    if => //.
    + auto => /> &1 &2 *.
      rewrite /untested_origins_c.
      rewrite /get_origins_c /get_untested_origins_c //=.
      have->: (fdom (filter
             (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                exists (m2o : (pkey * tag) option),
                  get_trace val = Some (pk_e{2}, m2o)) Game4Ltk.s_smap{2})) = (fdom (filter
             (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                exists (m2o : (pkey * tag) option),
                  get_trace val = Some (pk_e{1}, m2o)) Red_Ltk.Red_O.s_smap{1})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      have->: (fdom (filter
             (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (pk_e{1}, m2o)) /\
                  get_ir_test val = false) Red_Ltk.Red_O.s_smap{1})) = (fdom (filter
             (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (pk_e{2}, m2o)) /\
                  get_ir_test val = false) Game4Ltk.s_smap{2})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      smt().
    rcondt {1} ^if. auto => /#.
    auto => /> &1 &2 48? inv ? inv2 inv3 ? ? ? fresh *. split. smt(in_fsetU1). move => *. do split; ~6..8: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
    + move => i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m1 m2 m2' teq stnn tr.
      have := inv i{2} i' m1 m2 m2'. 
        smt().
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => m1 m2 m2'.
      rewrite i'eq !get_set_sameE //=.
      have := inv i{2} i0. 
      smt(). 
      + move => x0 y0 b0 tqeq.
        have := inv2 x0 y0 b0 tqeq.
        move => [H1|H2]. 
        + left.
          move : H1 => [i'] t k ir'' H1.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).
move => x xeq.
split. smt(mem_set).
split. smt().
have := inv3 x xeq.
move => [#] _ _ [i0 j0 [#] i0in x4eq x1eq x2eq j0in x3eq i0ncr j0ncr].
exists i0 j0.
do split; 1..6,8: smt().
rewrite in_fsetU1 negb_or.
split. smt().
have := inv2 (oget St_CDH_O.x_map{1}.[i0]) (loge x.`5) (oget St_CDH_O.y_map{1}.[j0]).
rewrite ComRing.mulrC expM expgK -x1eq ComRing.mulrC expM -x3eq -x2eq -x4eq xeq.
have->: x = (x.`1, x.`2, x.`3, x.`4, x.`5) by smt().
rewrite //=.
move => [[i2 tag key ir'] H|[i2 tag key ir'] H].
admit.
rewrite /untested_origins_c in fresh.
admit. 
  + match Accepted_mod {2} ^match. auto => /#.
    if => //.
    + auto => /> &1 &2 *. 
      rewrite /untested_partner_c.
      rewrite /get_partners_c /get_untested_partners_c.
      have->: (fdom
          (filter (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                get_trace val = Some t{1}) Red_Ltk.Red_O.s_smap{1})) = (fdom (filter
             (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                get_trace val = Some t{2}) Game4Ltk.s_smap{2})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      have->: (fdom
            (filter (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                  get_trace val = Some t{1} /\ get_ir_test val = false)
               Red_Ltk.Red_O.s_smap{1})) = (fdom
            (filter (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                  get_trace val = Some t{2} /\ get_ir_test val = false)
               Game4Ltk.s_smap{2})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      smt().
    rcondt {1} ^if. auto => /#.
    auto => /> &1 &2 48? inv ? inv2 inv3 *. do split; ~7..9: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
    + move => i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m1 m2 m2' teq stnn tr.
      have := inv i{2} i' m1 m2 m2'. 
        smt().
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => m1 m2 m2'.
      rewrite i'eq !get_set_sameE //=.
      have := inv i{2} i0. 
      smt(). 
      + move => x0 y0 b0 tqeq.
        have := inv2 x0 y0 b0 tqeq.
        move => [H1|H2]. 
        + left.
          move : H1 => [i'] t k ir'' H1.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).
move => x xeq.
split. smt(mem_set).
split. smt().
have := inv3 x xeq.
move => [#] _ _ [i0 j0 i0in].
exists i0 j0.
do split; 1..6,8: smt().
rewrite in_fsetU1 negb_or.
split. smt().
admit. (* same as above *)
  match Aborted_mod {2} ^match. auto => /#.
  auto => />.
- move => &2 bad; proc; inline.
  sp; if => //. 
  sp; match => //. 
  by match => //; auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  by match; auto => />.

+ proc; inline.
  sp; if => //.
  sp; match {1} => //.
  + match None {2} ^match. auto => /#.
    auto => />.
  match Some {2} ^match. auto => /#.
  match {1} => //.
  + match Pending_mod {2} ^match. auto => /#.
    auto => />.
  + match Accepted_mod {2} ^match. auto => /#.
    if => //.
    + auto => /> &1 &2 43? c1 c2 c3 c4 c5 inv inv2 inv3 inv4 *. clear c1 c2 c3 c4 c5 inv inv2 inv3 inv4.
      rewrite /untested_partner_s.
      rewrite /get_partners_s /get_untested_partners_s.
      have->: (fdom
          (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                get_trace val = Some t{1}) Red_Ltk.Red_O.c_smap{1})) = (fdom (filter
             (fun (_ : int) (val : pr_st_client instance_state) =>
                 get_trace val = Some t{2}) Game4Ltk.c_smap{2})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                  get_trace val = Some t{1} /\ get_ir_test val = false)
               Red_Ltk.Red_O.c_smap{1})) = (fdom
            (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                   get_trace val = Some t{2} /\ get_ir_test val = false)
                Game4Ltk.c_smap{2})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      have->: get_sr_ltk (oget Red_Ltk.Red_O.servers{1}.[b{2}]) = get_sr_ltk (oget Game4Ltk.servers{2}.[b{2}]) by smt().
      have->: get_ir_test (oget Red_Ltk.Red_O.s_smap{1}.[b{2}, j{2}]) = (get_ir_test (oget Game4Ltk.s_smap{2}.[b{2}, j{2}])) by smt().
      smt().

if => //.
admit.


    auto => /> &1 &2 47? inv ? inv2 inv3 *. do split; ~4..6: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => i t1 t2.
case : (i = (b, j){2}); 2: by smt(get_setE).
move => -> //=.
have := inv (b, j){2} t1 t2.
smt(get_setE).
+ move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m1 m2 tag m1' tag'.
          have := inv2 (b,j){2} i' m1 m2 tag m1' tag'.
          smt().
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite i'eq get_set_sameE //=.
      rewrite get_set_neqE //=.
      move => m1 m2 tag m1' tag'.
      have := inv2 (b,j){2} i0 m1 m2 tag m1' tag'.
      admit.
+ move => x0 y0 b0 tqeq.
have := inv3 x0 y0 b0 tqeq.
move => [H1|H2]; 1: by smt().
right.
move : H2 => [i'] t k ir'' H2.
exists i'. 
by smt(get_setE).

    auto => /> &1 &2 47? inv ? inv2 inv3 *. do split; ~4..6: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => i t1 t2.
case : (i = (b, j){2}); 2: by smt(get_setE).
move => -> //=.
have := inv (b, j){2} t1 t2.
smt(get_setE).
+ move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m1 m2 tag m1' tag'.
          have := inv2 (b,j){2} i' m1 m2 tag m1' tag'.
          smt().
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite i'eq get_set_sameE //=.
      rewrite get_set_neqE //=.
      move => m1 m2 tag m1' tag'.
      have := inv2 (b,j){2} i0 m1 m2 tag m1' tag'.
      admit.
+ move => x0 y0 b0 tqeq.
have := inv3 x0 y0 b0 tqeq.
move => [H1|H2]; 1: by smt().
right.
move : H2 => [i'] t k ir'' H2.
exists i'. 
by smt(get_setE).

  match Aborted_mod {2} ^match. auto => /#.
  auto => />.
- move => &2 bad; proc; inline. 
  sp; if => //.
  sp; match => //. 
  by match => //; auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  by match; auto => />.

+ proc; inline.
  sp; if => //.
  sp; if => //.
  match {1} => //.
  + match None {2} ^match. auto => /#.
    auto => />.
  match Some {2} ^match. auto => /#.
  match {1} => //.
  + match Pending_mod {2} ^match. auto => /#.
    auto => />.
  + match Accepted_mod {2} ^match. auto => /#.
    if => //.
    + auto => /> &1 &2 27? c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 *. clear c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25.
      rewrite /fresh_partner_c.
      rewrite /get_partners_c /get_fresh_partners_c.
      have->: (fdom (filter
             (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                get_trace val = Some t'{1}) Red_Ltk.Red_O.s_smap{1})) = (fdom (filter
             (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
               get_trace val = Some t'{2}) Game4Ltk.s_smap{2})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      have->: (fdom
            (filter
               (fun (bj : pkey * int)
                  (val : pr_st_server instance_state) =>
                  get_trace val = Some t'{2} /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\
                  (get_ir_eph val = false \/
                   get_sr_ltk (oget Game4Ltk.servers{2}.[bj.`1]) = false))
               Game4Ltk.s_smap{2})) = (fdom
            (filter
               (fun (bj : pkey * int)
                  (val : pr_st_server instance_state) =>
                  get_trace val = Some t'{1} /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\
                  (get_ir_eph val = false \/
                   get_sr_ltk (oget Red_Ltk.Red_O.servers{1}.[bj.`1]) =
                   false)) Red_Ltk.Red_O.s_smap{1})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set pow_bij).
      smt().
    rcondf {1} ^if. auto => />.
    rcondf {2} ^if. auto => />.
    sp; seq 1 1 : (#pre /\ ={ks2}). auto => />.
    if => //.
    + auto => /> &1 &2 *.
      have->: t'{1} = t'{2}. smt().
      smt(get_setE mem_set expgK expM loggK).
    + auto => /> &1 &2 5? c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 4? c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c1 c2 c3 c4 c5 c6 c7 c8 inv c9 inv2 c10 inv3 inv4 *. split. 




admit. 
move => *. do split; ~1,2,9,18,19,21,22: smt(get_setE mem_set in_fsetU1 loggK expgK expM pow_bij).
clear inv inv2 inv3 inv4 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41.
have->: (get_fresh_partners_c t'{1} Red_Ltk.Red_O.s_smap{1}
                     Red_Ltk.Red_O.servers{1}) = (get_fresh_partners_c t'{2} Game4.s_smap{2} Game4.servers{2}).
rewrite /get_fresh_partners_c. 
      have->: (fdom
            (filter
               (fun (bj : pkey * int)
                  (val : pr_st_server instance_state) =>
                  get_trace val = Some t'{2} /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\
                  (get_ir_eph val = false \/
                   get_sr_ltk (oget Game4Ltk.servers{2}.[bj.`1]) = false))
               Game4Ltk.s_smap{2})) = (fdom
            (filter
               (fun (bj : pkey * int)
                  (val : pr_st_server instance_state) =>
                  get_trace val = Some t'{1} /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\
                  (get_ir_eph val = false \/
                   get_sr_ltk (oget Red_Ltk.Red_O.servers{1}.[bj.`1]) =
                   false)) Red_Ltk.Red_O.s_smap{1})). 
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set).
      smt().
    smt(get_setE mem_set).
move => x0. 
rewrite mem_set //=.
move => [].
move => xin x3in x4in i0 i0in x4eq x1eq x2eq.
rewrite mem_set.
split. smt().
have->: st'{2}.`1 = t'{1}.`1.`1. smt().
have->: g ^ st'{2}.`2 = t'{1}.`1.`2. smt().
have->: st'{2}.`2 = loge t'{1}.`1.`2. smt(loggK expgK expM). smt(get_setE pow_bij loggK expgK expM).
smt(get_setE mem_set loggK expgK expM).
move => b0 x0 y0.
have->: st'{2}.`2 = loge t'{1}.`1.`2. smt(loggK expgK expM). 
smt(mem_set pow_bij loggK expgK expM).
    + move => i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m1 m2 m2' teq stnn tr.
      have := inv2 i{2} i' m1 m2 m2'. 
        smt().
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => m1 m2 m2'.
      rewrite i'eq !get_set_sameE //=.
      have := inv2 i{2} i0. 
      smt(). 

      move => x0 y0 b0 x1eq x2eq x3eq x4eq x5eq.
      left.
      rewrite -x3eq -x4eq -x5eq.
      have->: x0 = st'{2}.`2 by smt(pow_bij).
      exists i{2} (oget t'{2}.`2).`2 k'{2} (ir'{2}.`1, ir'{2}.`2, true).
      rewrite mem_set get_setE //=.
      split. smt().
      have->: st'{2}.`1 = t'{2}.`1.`1 by smt().
      have->: g ^ st'{2}.`2 = t'{2}.`1.`2 by smt().
      smt(get_setE mem_set).

have->: st'{2}.`2 = loge t'{1}.`1.`2. smt(loggK expgK expM). 
smt(mem_set).

exists (oget Red_Ltk.Red_O.i_inst{1}.[i{2}]) (oget Red_Ltk.Red_O.b_inst{1}.[st'{2}.`1]).
do split; 1..7: smt().
have : (forall i st t k ir, i \in Game4.c_smap{2} => Game4.c_smap{2}.[i] = Some (Accepted_mod st t k ir) 
         => oget Red_Ltk.Red_O.b_inst{1}.[st.`1] \in St_CDH_O.cr2{1} => get_ir_sess (oget Red_Ltk.Red_O.c_smap{1}.[i])
               \/ fresh_partner_c t Red_Ltk.Red_O.s_smap{1} Red_Ltk.Red_O.servers{1} = Some false). admit.
smt().


(* I can kill this branch - I know that if x is in h2m then either this instance is tested or session key revealed or its partner is or it has been queried by the adverasry and I have won! *)


    auto => /> &1 &2 5? c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 4? c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c1 c2 c3 c4 c5 c6 c7 c8 inv c9 inv2 c10 inv3 inv4 *. split. 
admit. (* show that win has happened as above *)
move => *. do split; ~1,6,7,9,10: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
clear inv inv2 inv3 inv4 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41.
have->: (get_fresh_partners_c t'{1} Red_Ltk.Red_O.s_smap{1}
                     Red_Ltk.Red_O.servers{1}) = (get_fresh_partners_c t'{2} Game4.s_smap{2} Game4.servers{2}).
rewrite /get_fresh_partners_c. 
      have->: (fdom
            (filter
               (fun (bj : pkey * int)
                  (val : pr_st_server instance_state) =>
                  get_trace val = Some t'{2} /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\
                  (get_ir_eph val = false \/
                   get_sr_ltk (oget Game4Ltk.servers{2}.[bj.`1]) = false))
               Game4Ltk.s_smap{2})) = (fdom
            (filter
               (fun (bj : pkey * int)
                  (val : pr_st_server instance_state) =>
                  get_trace val = Some t'{1} /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\
                  (get_ir_eph val = false \/
                   get_sr_ltk (oget Red_Ltk.Red_O.servers{1}.[bj.`1]) =
                   false)) Red_Ltk.Red_O.s_smap{1})). 
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        smt(get_setE mem_set pow_bij).
      smt().
    smt(get_setE mem_set).
    + move => i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m1 m2 m2' teq stnn tr.
      have := inv2 i{2} i' m1 m2 m2'. 
        smt().
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => m1 m2 m2'.
      rewrite i'eq !get_set_sameE //=.
      have := inv2 i{2} i0. 
      smt(). 

      move => x0 y0 b0 x1eq x2eq x3eq x4eq x5eq.
      left.
      rewrite -x3eq -x4eq -x5eq.
      have->: x0 = st'{2}.`2 by smt(pow_bij).
      exists i{2} (oget t'{2}.`2).`2 k'{2} (ir'{2}.`1, ir'{2}.`2, true).
      rewrite mem_set get_setE //=.
      split. smt().
      have->: st'{2}.`1 = t'{2}.`1.`1 by smt().
      have->: g ^ st'{2}.`2 = t'{2}.`1.`2 by smt().
      smt(get_setE mem_set).
have->: st'{2}.`2 = loge t'{1}.`1.`2. smt(loggK expgK expM). 
have->: st'{2}.`1 = t'{1}.`1.`1 by smt().
smt(ComRing.mulrC loggK pow_bij expM expgK).


exists (oget Red_Ltk.Red_O.i_inst{1}.[i{2}]) (oget Red_Ltk.Red_O.b_inst{1}.[st'{2}.`1]).
do split; 1..7: smt().
admit. (* connect with freshness condition *)

  match Aborted_mod {2} ^match. auto => /#.
  auto => />.
- move => &2 bad; proc; inline. 
  sp; if => //.
  sp; if => //; match => //. 
  match => //.
  if => //; if => //.
  + auto => />. by rewrite dkey_ll.
  sp; seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dkey_ll.
  + auto => />. by rewrite dkey_ll.
  hoare. 
  by auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; if => //.
  sp; match => //. 
  match; auto => />.
  by if => //; if => //; auto => />; rewrite dkey_ll.

+ proc; inline.
  sp; if => //.
  sp; if => //.
  match {1} => //.
  + match None {2} ^match. auto => /#.
    auto => />.
  match Some {2} ^match. auto => /#.
  match {1} => //.
  + match Pending_mod {2} ^match. auto => /#.
    auto => />.
  + match Accepted_mod {2} ^match. auto => /#.
    if => //.
    + auto => /> &1 &2 *.
      rewrite /fresh_partner_s.
      rewrite /get_origins_s /get_fresh_partners_s.
      have->: (fdom
          (filter
             (fun (_ : int) (val : pr_st_client instance_state) =>
                exists (m2o : (pkey * tag) option),
                  get_trace val = Some (t'{2}.`1, m2o)) Game4Ltk.c_smap{2})) = (fdom (filter
             (fun (_ : int) (val : pr_st_client instance_state) =>
                exists (m2o : (pkey * tag) option),
                  get_trace val = Some (t'{1}.`1, m2o)) Red_Ltk.Red_O.c_smap{1})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        admit. (* too much in context *)
      have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (t'{1}.`1, m2o)) /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\ get_ir_eph val = false) Red_Ltk.Red_O.c_smap{1})) = (fdom
            (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (t'{2}.`1, m2o)) /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\ get_ir_eph val = false) Game4Ltk.c_smap{2})).
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        admit. (* too much in context *)
      smt().
    rcondf {1} ^if. auto => />.
    rcondf {2} ^if. auto => />.
    sp; seq 1 1 : (#pre /\ ={ks2}). auto => />.
    if => //.
    + auto => /> &1 &2 *. 
      have->: t'{1} = t'{2}. smt().
      have<-: st'{1}.`2 = st'{2}.`2. smt().
      have->: t'{2}.`1.`1 = g ^ st'{2}.`1. smt(). split.
      smt(get_setE mem_set in_fsetU1 loggK expgK expM).
      have : g ^ st'{2}.`1 \in Red_Ltk.Red_O.servers{1}. smt().
      have : t'{2}.`1.`2 \in Game4.m1_set{2}. admit. (* this needs to use freshness condition, since fresh_partner is Some true there is an honest client with this message *)
      move => *.
      have : (exists (i : int),
        (i \in St_CDH_O.x_map{1}) /\
        t'{2}.`1.`2 = g ^ oget St_CDH_O.x_map{1}.[i] /\
        t'{2}.`1.`2 ^ oget st'{2}.`2 = g ^ oget st'{2}.`2 ^ oget St_CDH_O.x_map{1}.[i] /\
        t'{2}.`1.`2 ^ st'{2}.`1 = g ^ st'{2}.`1 ^ oget St_CDH_O.x_map{1}.[i]). smt(get_setE mem_set pow_bij loggK expgK expM ComRing.mulrC).
      smt(get_setE mem_set loggK expgK expM).
    + auto => /> &1 &2 49? inv ? inv2 inv3 *. split. 
     admit. 
     move => *. do split; ~1,3,4,6,17..19,22: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
have->: (get_fresh_partners_s t'{1} Red_Ltk.Red_O.c_smap{1}) = (get_fresh_partners_s t'{2} Game4Ltk.c_smap{2}).
rewrite /get_fresh_partners_s.
      have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (t'{1}.`1, m2o)) /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\ get_ir_eph val = false) Red_Ltk.Red_O.c_smap{1})) = (fdom
            (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (t'{2}.`1, m2o)) /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\ get_ir_eph val = false) Game4Ltk.c_smap{2})). 
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        admit. (* too much in context *)
      smt().
smt().
move => x0.
rewrite mem_set.
move => []. 
move => *.
have->: t'{1} = t'{2}. smt().
have<-: st'{1}.`2 = st'{2}.`2. smt().
have->: t'{2}.`1.`1 = g ^ st'{2}.`1. smt().
split. smt(get_setE mem_set in_fsetU1 loggK expgK expM).
smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => -> //= *. 
have->: t'{1} = t'{2}. smt().
have<-: st'{1}.`2 = st'{2}.`2. smt().
have->: t'{2}.`1.`1 = g ^ st'{2}.`1. smt().
split. smt(get_setE mem_set in_fsetU1 loggK expgK expM).
smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => x0.
have : t'{2}.`1.`2 \in Game4.m1_set{2}. admit.
smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => x0.
have : t'{2}.`1.`2 \in Game4.m1_set{2}. admit.
smt(get_setE mem_set in_fsetU1 loggK expgK expM).
move => i t1 t2.
case : (i = (b, j){2}); 2: by smt(get_setE).
move => -> //=.
have := inv (b, j){2} t1 t2.
smt(get_setE).
+ move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m1 m2 tag m1' tag'.
          have := inv2 (b,j){2} i' m1 m2 tag m1' tag'.
          smt().
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite i'eq get_set_sameE //=.
      rewrite get_set_neqE //=.
      move => m1 m2 tag m1' tag'.
      have := inv2 (b,j){2} i0 m1 m2 tag m1' tag'.
      smt(). 
      move => x0 y0 b0 x1eq x2eq x3eq x4eq x5eq.
      right.
      rewrite -x3eq -x4eq -x5eq.
      have->: b0 = st'{2}.`1 by smt(pow_bij).
      have->: y0 = oget st'{2}.`2 by smt(pow_bij).
      exists (b, j){2} (oget t'{2}.`2).`2 k'{2} (ir'{2}.`1, ir'{2}.`2, true).
      rewrite mem_set get_setE //=.
      split. smt().
      have->: g ^ st'{2}.`1 = t'{2}.`1.`1 by smt().
      have->: g ^ oget st'{2}.`2 = (oget t'{2}.`2).`1 by smt().
      smt(get_setE mem_set).

admit. (* I need to get the index from my partner first
exists (oget Red_Ltk.Red_O.i_inst{1}.[]) (oget Red_Ltk.Red_O.b_inst{1}.[(b, j){2}]).
do split; 1..7: smt().
admit. (* connect with freshness condition as in corruption *)*)



    auto => /> &1 &2 49? inv ? inv2 inv3 *. split. 
admit. 
move => *. do split; ~1,5..7,10: smt(get_setE mem_set in_fsetU1 loggK expgK expM).
have->: (get_fresh_partners_s t'{1} Red_Ltk.Red_O.c_smap{1}) = (get_fresh_partners_s t'{2} Game4Ltk.c_smap{2}).
rewrite /get_fresh_partners_s.
      have->: (fdom (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (t'{1}.`1, m2o)) /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\ get_ir_eph val = false) Red_Ltk.Red_O.c_smap{1})) = (fdom
            (filter (fun (_ : int) (val : pr_st_client instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (t'{2}.`1, m2o)) /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\ get_ir_eph val = false) Game4Ltk.c_smap{2})). 
      + rewrite fsetP.
        move => x.
        do rewrite mem_fdom mem_filter.
        admit. (* too much in context *)
      smt().
smt().
smt(get_setE).
+ move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          move => m1 m2 tag m1' tag'.
          have := inv2 (b,j){2} i' m1 m2 tag m1' tag'.
          smt().
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite i'eq get_set_sameE //=.
      rewrite get_set_neqE //=.
      move => m1 m2 tag m1' tag'.
      have := inv2 (b,j){2} i0 m1 m2 tag m1' tag'.
      smt(). 
      move => x0 y0 b0 x1eq x2eq x3eq x4eq x5eq.
      right.
      rewrite -x3eq -x4eq -x5eq.
      have->: b0 = st'{2}.`1 by smt(pow_bij).
      have->: y0 = oget st'{2}.`2 by smt(pow_bij).
      exists (b, j){2} (oget t'{2}.`2).`2 k'{2} (ir'{2}.`1, ir'{2}.`2, true).
      rewrite mem_set get_setE //=.
      split. smt().
      have->: g ^ st'{2}.`1 = t'{2}.`1.`1 by smt().
      have->: g ^ oget st'{2}.`2 = (oget t'{2}.`2).`1 by smt().
      smt(get_setE mem_set).

admit. (* I need to get the index from my partner first
exists (oget Red_Ltk.Red_O.i_inst{1}.[]) (oget Red_Ltk.Red_O.b_inst{1}.[(b, j){2}]).
do split; 1..7: smt().
admit. (* connect with freshness condition as in corruption *)*)

  match Aborted_mod {2} ^match. auto => /#.
  auto => />.
- move => &2 bad; proc; inline. 
  sp; if => //.
  sp; if => //; match => //. 
  match => //.
  if => //; if => //.
  + auto => />. by rewrite dkey_ll.
  sp; seq 1 : (#pre); try by auto.
  + auto => />. by rewrite dkey_ll.
  + auto => />. by rewrite dkey_ll.
  hoare. 
  by auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; if => //.
  sp; match => //. 
  match; auto => />.
  by if => //; if => //; auto => />; rewrite dkey_ll.
qed.

module Reduction_Eph (A : A_GAKE_nodhs) (D : DDH_oracle) = {
  var solution : group option

  module Red_O : GAKE_nodhs_i = GameDDH with {
    var t_i, t_j : int
    var t_b : pkey
    var ga, gb : group
    var stop : bool

    proc init_mem [
      -1 + {stop <- false; t_b <- witness;}
    ]

    proc h [
       0 + ^ {rt <- witness; rk <- witness; }
      [0 - ^rk<-] + ^ (!stop)
      ^t<$ + ^ {stop <- stop \/ ((x1, x2) = (None, None));}
    ]

    proc init_s [
      [0 - ^if] + ^ (!stop)
    ]

    proc send_msg1 [
      [0 - ^if] + ^ (!stop)
      ^if.^match#None.^if.^pk<- + ^ (i = t_i)
      ^if.^match#None.^if.^kp_set<- + {pk <- ga; t_b <- m1;}
    ]

    proc send_msg2 [
      [0 - ^match] + ^ (!stop)
      ^match#Some.^match#None.^if.^pk<- + ^ (b = t_b /\ j = t_j)
      ^match#Some.^match#None.^if.^kp_set<- + {pk <- gb;}
    ]

    proc send_msg3 [
      [0 - ^match] + ^ (!stop)
    ]

    proc c_rev_skey [
      [0 - ^match] + ^ (!stop)
    ]

    proc s_rev_skey [
      [0 - ^match] + ^ (!stop)
    ]

    proc rev_ltkey [
      [0 - ^match] + ^ (!stop)
    ]

    proc c_rev_ephkey [
      [0 - ^match] + ^ (!stop)
    ]

    proc s_rev_ephkey [
      [0 - ^match] + ^ (!stop)
    ]

    proc c_test [
      [0 - ^if] + ^ (!stop)
    ]

    proc s_test [
      [0 - ^if] + ^ (!stop)
    ]

  }

  proc solve(t_i, t_j : int, ga, gb : group) : group option = {
    var b' : bool;

    solution <- witness;
    Red_O.t_i <- t_i;
    Red_O.t_j <- t_j;
    Red_O.ga <- ga;
    Red_O.gb <- gb;
    b' <@ A(Red_O).run();
    return solution;
  }
}.

print Reduction_Eph.Red_O.


lemma embed_eph &m i j: `| Pr[GAKEc.E_GAKE_nodhs(GAKEb_st(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), Hon_s_Red(A)).run(bit) @ &m : res]
     - Pr[GAKE_mod.E_GAKE_nodhs(GAKE_mod.GAKEb_nodhs(NTOR_S_mod(GAKE_mod.HROc.RO), NTOR_C_mod(GAKE_mod.HROc.RO), GAKE_mod.HROc.RO), Name_Red(Hon_s_Red(A))).run(bit) @ &m : res] | 
                 <= Pr[GAKEc.E_GAKE_nodhs(GAKEb_st(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), Hon_s_Red(A)).run(bit) @ &m : GAKEb_st.stop].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Name_Red.O_GAKE.stop => //; first last.
+ smt().
symmetry; proc; inline*.
wp; call (: Name_Red.O_GAKE.stop


end section.




