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
    
    return b' /\ !O.bad;
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

module (Red_ROM (D : A_GAKE_nodhs) : ROc.IdealAll.RO_Distinguisher) (O : ROc.IdealAll.RO) = {
  module AKE_O : GAKE_nodhs = Game1 with {
    proc h [ 
      ^tk<$ ~ {tk <@ O.get(x);}
      ^if -
    ] res ~ (tk)
  }

  proc distinguish(b) = {
    var b';
    AKE_O.init_mem(b);
    b' <@ D(AKE_O).run();
    return b';
  }
}.

module (Red_ROM2 (D : A_GAKE_nodhs) (O1 : ROSc.I1.RO) : ROSc.I2.RO_Distinguisher) (O2 : ROSc.I2.RO) = {
  module AKE_O : GAKE_nodhs = Game3 with {
    proc init_mem [
      ^h1m<- ~ {O1.init();}
      ^h2m<- -
    ]

    proc h [ 
      ^t<$ ~ {t <@ O1.get(x); k <@ O2.get(x);}
      ^if -
      ^k<$ -
      ^if -
    ] res ~ ((t, k))

    proc send_msg2 [
      ^match#Some.^match#None.^if.^ts<$ ~ {t_B <@ O1.get(x); O2.sample(x); key <- witness;}
      [^match#Some.^match#None.^if.^if - ^key<-] -
    ]

    proc send_msg3 [
      ^match#Some.^match#Pending_mod.^ts<$ ~ {t_A <@ O1.get(x); O2.sample(x); key <- witness;}
      [^match#Some.^match#Pending_mod.^if - ^key<-] -
    ]

    proc c_rev_skey [
      var ks : key
      var x : pkey * pkey * pkey * pkey * pkey
      ^match#Some.^match#Accepted_mod.^if.^k<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1); ks <@ O2.get(x); k <- Some ks;}
    ]

    proc s_rev_skey [
      var ks : key
      var x : pkey * pkey * pkey * pkey * pkey
      ^match#Some.^match#Accepted_mod.^if.^k<- ~ {x <- ((t'.`1).`2 ^ (oget st'.`2), (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, g ^ (oget st'.`2)); ks <@ O2.get(x); k <- Some ks;}
    ]

    proc c_test [
      var ks2 : key
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^ks<$ + ^ {ks2 <@ O2.get(x);}
    ]

    proc s_test [
      var ks2 : key
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^ks<$ + ^ {ks2 <@ O2.get(x);}
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

  proc ddh(x y z : group) : bool = {
    var r <- false;

    if (exists i, i \in x_map /\ x = g ^ (oget x_map.[i]) /\ z = y ^ (oget x_map.[i]) /\ i \notin cr1) {
      if (exists j, j \in y_map /\ y = g ^ (oget y_map.[j]) /\ j \notin cr2) {
         win <- true;
         r <- true;
      }
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

module type St_CDH_A (O : Oracle) = {
  proc solve() : unit
}.


module St_CDH_E (O : Oracle_i) (A : St_CDH_A) = {
  proc run(): unit = {
    
    A(O).solve();

    return ();
  }
}.

(* CDH reductions *)
print Game4.

module (Red_Ltk (A : A_GAKE_nodhs) : St_CDH_A) (O : Oracle) = {


  module Red_O : GAKE_nodhs_i = Game4 with {
    var stop : bool
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
      -1 + {stop <- false; tags_opt <- empty; h1m_opt <- empty; h2m_opt <- empty;}
    ]

    proc h [
      var x1, x2 : group option
      var rt : tag
      var rk : key

      0 + ^ {rt <- witness; rk <- witness;}
      [0 - ^rk<-] + ^ (!stop)
      ^if{2} + {rt <- oget h1m.[x]; rk <- oget h2m.[x];}
      ^badq<- - 
      ^hq<- -
      0 + {stop <@ O.ddh((x.`4, x.`5, x.`1)); }


    ] res ~ (rt, rk)

    proc h [
       0 + ^ {rt <- witness; rk <- witness;}
      [0 - ^rk<-] + ^ (!stop)
      ^ <@ ~ { }
    ]

    proc init_s [
      [0 - ^if] + ^ (!stop)
      [^sk<$ - ^pk<-] ~ {count_b <- count_b + 1; sk <- witness; pk <@ O.gen2(); b_inst.[pk] <- count_b;}
    ]

    proc send_msg1 [
      [0 - ^if] + ^ (!stop)
      [^if.^match#None.^sk<$ - ^pk<-] ~ {count_i <- count_i + 1; sk <- witness; pk <@ O.gen1(); i_inst.[i] <- count_i;}
    ]

    proc send_msg2 [
      [0 - ^match] + ^ (!stop)
      ^match#Some.^match#None.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h1m_opt)
      ^match#Some.^match#None.^if.^if.^h1m<- ~ {h1m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ts;}
      ^match#Some.^match#None.^if.^t_B<- ~ {t_B <- oget h1m_opt.[(None, None, x.`3, x.`4, x.`5)];} 
      ^match#Some.^match#None.^if.^x<- ~ {x <- (m2 ^ sk, m2 ^ sk_b, b, m2, pk);}
      ^match#Some.^match#None.^if.^tags_prot<- ~ {tags_opt.[(None, None, x.`3, x.`4, x.`5)] <- t_B;}
      ^match#Some.^match#None.^if.^s_smap<- ~ {s_smap.[b, j] <- Accepted_mod (witness, Some sk) ((b, m2), Some (pk, t_B)) key (false, false, false);}

    ]

    proc send_msg3 [
      [0 - ^match] + ^ (!stop)
      ^match#Some.^match#Pending_mod.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h1m_opt)
      ^match#Some.^match#Pending_mod.^if.^h1m<- ~ {h1m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ts;}
      ^match#Some.^match#Pending_mod.^t_A<- ~ {t_A <- oget h1m_opt.[(None, None, x.`3, x.`4, x.`5)];}
      ^match#Some.^match#Pending_mod.^x<- ~ {x <- (m3.`1 ^ sk_ce, b ^ sk_ce, b, pt.`2, m3.`1);}
      ^match#Some.^match#Pending_mod.^badt2<- ~ {badt2 <- badt2 \/ badt1 \/ ((None, None, x.`3, x.`4, x.`5) \notin tags_opt);}
    ]

    proc c_rev_skey [
      [0 - ^match] + ^ (!stop)
      ^match#Some.^match#Accepted_mod.^if.^x<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, t'.`1.`1, t'.`1.`2, (oget t'.`2).`1);}
      ^match#Some.^match#Accepted_mod.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^match#Some.^match#Accepted_mod.^if.^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
      ^match#Some.^match#Accepted_mod.^if.^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];}
    ]

    proc s_rev_skey [
      [0 - ^match] + ^ (!stop)
      ^match#Some.^match#Accepted_mod.^if.^x<- ~ {x <- (t'.`1.`2 ^ oget st'.`2, t'.`1.`2 ^ st'.`1, t'.`1.`1, t'.`1.`2, g ^ oget st'.`2);}
      ^match#Some.^match#Accepted_mod.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^match#Some.^match#Accepted_mod.^if.^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
      ^match#Some.^match#Accepted_mod.^if.^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];} 
    ]

    proc rev_ltkey [
      var inst : int

      [0 - ^match] + ^ (!stop)
      ^match#Some.^match#Honest_mod.^if.^ltk<- ~ {inst <- oget b_inst.[b]; ltk <@ O.corrupt2(inst);}
    ]

    proc c_rev_ephkey [
      var inst : int

      [0 - ^match] + ^ (!stop)
      ^match#Some.^match#Pending_mod.^if.^ek<- ~ {inst <- oget i_inst.[i]; ek <@ O.corrupt1(inst);}
    ]

    proc s_rev_ephkey [
      [0 - ^match] + ^ (!stop)
    ]

    proc c_test [
      [0 - ^if] + ^ (!stop)
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^x<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, t'.`1.`1, t'.`1.`2, (oget t'.`2).`1);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^tq<- ~ {tq_opt <- Some (None, None, x.`3, x.`4, x.`5);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^badq<- ~ {badq <- badq \/ (oget tq_opt \in hq_opt);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];} 
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks2;}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^x<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, t'.`1.`1, t'.`1.`2, (oget t'.`2).`1);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^tq<- ~ {tq_opt <- Some (None, None, x.`3, x.`4, x.`5);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^badq<- ~ {badq <- badq \/ (oget tq_opt \in hq_opt);}
    ]

    proc s_test [
      [0 - ^if] + ^ (!stop)
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^x<- ~ {x <- (t'.`1.`2 ^ oget st'.`2, t'.`1.`2 ^ st'.`1, t'.`1.`1, t'.`1.`2, g ^ oget st'.`2);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^tq<- ~ {tq_opt <- Some (None, None, x.`3, x.`4, x.`5);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^badq<- ~ {badq <- badq \/ (oget tq_opt \in hq_opt);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
      ^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];} 
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2m_opt)
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^if.^h2m<- ~ {h2m_opt.[(None, None, x.`3, x.`4, x.`5)] <- ks2;}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^k<- ~ {k <- h2m_opt.[(None, None, x.`3, x.`4, x.`5)];}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^x<- ~ {x <- (t'.`1.`2 ^ oget st'.`2, t'.`1.`2 ^ st'.`1, t'.`1.`1, t'.`1.`2, g ^ oget st'.`2);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^tq<- ~ {tq_opt <- Some (None, None, x.`3, x.`4, x.`5);}
      ^if.^match#Some.^match#Accepted_mod.^if.^if?^badq<- ~ {badq <- badq \/ (oget tq_opt \in hq_opt);}
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

declare module A <: A_GAKE_nodhs {-GAKEb_nodhs, -Game0, -Game1, -Game2, -Game3, -Game4, -GameDDH, -ROc.IdealAll.RO, -RO, -FRO, -ROSc.I1.RO, -ROSc.I2.RO, -ROSc.I1.FRO, -ROSc.I2.FRO, -Red_Coll_real, -Red_Coll_ideal, -BB.Sample, -Red_ROM, -Red_ROM2, -St_CDH_O, -Red_Ltk }.

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
  Pr[E_GAKE_nodhs(GAKEb_nodhs(NTOR_S_mod(RO), NTOR_C_mod(RO), RO), A).run(b) @ &m : res] = Pr[E_GAKE_nodhs(Game0, A).run(b) @ &m : res].
proof. 
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
  by match = => //; 1: by auto. 
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 1: Remove collisions in ephemeral and long-term keys. Strategy with 2 * bound *)
lemma game0_game1 b &m: `| Pr[E_GAKE_nodhs(Game0, A).run(b) @ &m : res] - Pr[E_GAKE_nodhs(Game1, A).run(b) @ &m : res] | <= Pr[E_GAKE_nodhs(Game0, A).run(b) @ &m : Game0.bad].
proof. 
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game1.bad => //; first last.
+ smt().
symmetry; proc; inline*.
call (: Game1.bad
      , ={b0, servers, c_smap, s_smap, tested, kp_set, hm, bad}(Game0, Game1)
      , ={bad}(Game0, Game1)) => //; try sim />.

- exact A_ll.

- move => &2 bad; proc; auto => />. 
  by rewrite weight_dprod dkey_ll dtag_ll.
- move => &1; proc; auto.
  by rewrite weight_dprod dkey_ll dtag_ll.

- proc.
  sp; seq 1 1: (#pre /\ ={sk}); 1: by auto.
  by sp 1 1; if{2}; auto => />.
- move => &2 bad.
  proc; auto.
  rewrite dt_ll //=. smt().
- move => &1. 
  proc. 
  auto => />.
  by rewrite dt_ll.

- proc.
  sp; if => //.
  sp; match = => //. 
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  by rewrite dt_ll; smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  by rewrite dt_ll.

- proc; inline.
  sp; match = => //. 
  move => sk.
  match = => //.
  + seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp 0 2; if{2}.
  + by auto => />. 
  auto.
- move => &2 bad.
  proc; inline; sp; match; auto => />.
  match; auto => />.
  rewrite dt_ll weight_dprod dkey_ll dtag_ll. 
  by smt().
- move => &1. 
  proc; inline; sp; match; auto => />.
  match; 2: by auto => />. 
  rcondf ^if; 1: by auto => />. 
  auto => />.
  by rewrite dt_ll.

- move => &2 bad.
  proc; inline.
  sp; match; auto. 
  match; auto => />.
  by rewrite weight_dprod dkey_ll dtag_ll.
- move => &1.
  proc; inline*; auto => />.
  sp; match; auto.
  match; auto.
  by rewrite weight_dprod dkey_ll dtag_ll.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.

- move => &2 bad.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.

auto => />.
move => rl rr al bl csl hml kpl ssl sl tl ar br csr hmr kpr ssr sr tr. 
by case : (!br) => />.
qed.


(* ------------------------------------------------------------------------------------------ *)
(* Step 1b: Bound the bad event. *)
lemma game0_bad bit &m: Pr[E_GAKE_nodhs(Game0, A).run(bit) @ &m : Game0.bad] <= ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt).
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
 ={b0, hm, servers, c_smap, s_smap, tested, kp_set, bad}(Game0, Red_Coll_O_AKE(BB.Sample))
 /\ (Game0.bad{1} => !uniq BB.Sample.l{2})
 /\ (forall sk, g ^ sk \in Game0.kp_set{1} => sk \in BB.Sample.l{2})
) => //; try sim />.
+ proc; inline; sp 0 2; auto => />.
  smt(mem_set in_fsetU1 pow_bij).
+ proc; inline; sp 2 4; if => //; auto.
  sp; match = => //.
  auto => />.
  smt(mem_set in_fsetU1 pow_bij).
+ proc; inline; sp 2 4; match = => // [|st]; 1: auto.
  match = => // [|st']; 2: auto.
  auto => />.
  smt(mem_set in_fsetU1 pow_bij).
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
 ={b0, hm, servers, c_smap, s_smap, tested, kp_set, bad}(Game0, Red_Coll_O_AKE(BB.Sample))
 /\ (Game0.bad{1} => !uniq BB.Sample.l{2})
 /\ (forall sk, g ^ sk \in Game0.kp_set{1} => sk \in BB.Sample.l{2})
) => //; try sim />.
+ proc; inline; sp 0 2; auto => />.
  smt(mem_set in_fsetU1 pow_bij).
+ proc; inline; sp 2 4; if => //; auto.
  sp; match = => //.
  auto => />.
  smt(mem_set in_fsetU1 pow_bij).
+ proc; inline; sp 2 4; match = => // [|st]; 1: auto.
  match = => // [|st']; 2: auto.
  auto => />.
  smt(mem_set in_fsetU1 pow_bij).
auto => />.
smt(in_fset0).*)
qed.


(* ------------------------------------------------------------------------------------------ *)
(* Step 2: Splitting the random oracle. *)
local clone import DProd.ProdSampling with
  type t1 <- tag,
  type t2 <- key
proof *.

lemma game1_game2 bit &m: Pr[E_GAKE_nodhs(Game1, A).run(bit) @ &m : res] =  Pr[E_GAKE_nodhs(Game2, A).run(bit) @ &m : res].
proof. admit. (*
(* Proof on the real side *)
byequiv (: ={glob A, glob Red_ROM} /\ arg{1} = bit /\ arg{2} = bit ==> _) => //.
proc*.
transitivity*  {1} { r <@ ROc.IdealAll.MainD(Red_ROM(A), ROc.IdealAll.RO).distinguish(bit); }.

+ inline; wp.
  call (: ={b0, servers, c_smap, s_smap, tested, kp_set, bad}(Game1, Red_ROM.AKE_O) /\ Game1.hm{1} = ROc.IdealAll.RO.m{2}); 
    try sim />.

  + proc; inline.
    case ((x \in Game1.hm){1}).
    - auto => />.
    sp; seq 1 1: (#pre /\ tk{1} = r{2}); 1: by auto.
    auto => />.

  + proc; inline.
    sp 2 2; match = => // key.
    match = => //.
    seq 1 1: (#pre /\ ={sk}); 1: by auto.
    sp 2 2; if => //.
    sp. seq 1 1: (#pre /\ tk{1} = r0{2}); 1: by auto => />.
    auto => />.

  + proc; inline.
    sp 1 1; match = => // st.
    match = => // st' pt ir.
    sp. seq 1 1: (#pre /\ tk{1} = r0{2}); 1: by auto.
    auto => />.

  + auto.

transitivity*  {2} { r <@ ROc.IdealAll.MainD(Red_ROM(A), ROSc.RO_Pair(ROSc.I1.RO,ROSc.I2.RO)).distinguish(bit); };
  1: by call (ROSc.RO_split (Red_ROM(A))).

inline; wp.
call (: ={b0, servers, c_smap, s_smap, tested, kp_set, bad}(Red_ROM.AKE_O, Game2) /\ Game2.h1m{2} = ROSc.I1.RO.m{1} /\ Game2.h2m{2} = ROSc.I2.RO.m{1}
          /\ forall x, x \in ROSc.I1.RO.m{1} <=> x \in ROSc.I2.RO.m{1}); 
    try sim />.

+ proc; inline.
  case ((x \in Game1.hm){1}).
  - auto => />. smt(mem_set).
  sp; seq 1 1: (#pre /\ r{1} = t{2}); 1: by auto => />.
  auto => />.
  smt(mem_set).

+ proc; inline.
  sp 2 2; match = => // key.
  match = => //.
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp 2 2; if => //.
  sp. seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto => />.
  auto => />.
  smt(mem_set).

+ proc; inline.
  sp 1 1; match = => // st.
  match = => // st' pt ir.
  sp. seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto => />.
  auto => />.
  smt(mem_set).

auto => />.
smt(emptyE).*)
qed.

print Game3.

(* ------------------------------------------------------------------------------------------ *)
(* Step 3: Removing case of adversary guessing right tag. *)
local lemma game2_game3 b &m: `| Pr[E_GAKE_nodhs(Game2, A).run(b) @ &m : res] - Pr[E_GAKE_nodhs(Game3, A).run(b) @ &m : res] | <= Pr[E_GAKE_nodhs(Game2, A).run(b) @ &m : Game2.badt2].
proof. admit. (*
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game3.badt2 => //; first last.
+ smt().
symmetry; proc; inline*.
call (: Game3.badt2
      , ={b0, servers, c_smap, s_smap, tested, kp_set, hm, bad, h1m, h2m, hq, tq, badq, tags_adv, tags_prot, badt2, badt1}(Game2, Game3)
      , ={badt2}(Game2, Game3)) => //; try sim />; last first.

auto => />.
move => rl rr al bl bql bt1l bt2l csl h1ml h2ml hql kpsl ssl sl tal tpl tl tql ar br bqr bt1r bt2r csr h1mr h2mr hqr kpsr ssr sr tar tpr tr tqr.
by case : (!bt2r) => />.

- exact A_ll.

- move => &2 bad; proc; auto => />. 
  by rewrite dkey_ll dtag_ll.
- move => &1; proc; auto.
  by rewrite dkey_ll dtag_ll.

- move => &2 bad.
  proc; auto.
  rewrite dt_ll //=.
- move => &1.
  proc.
  auto => />.
  by rewrite dt_ll.

- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  rewrite dt_ll. smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  by rewrite dt_ll.

- move => &2 bad.
  proc; sp.
  match; auto => />. 
  match; auto => />.
  islossless.
- move => &1. 
  proc; sp.
  match; auto => />.
  match; auto => />.
  islossless.

- proc; inline. 
  sp; match = => // st.
  match = => // st' pt' ir'.
  auto => />.
- move => &2 bad.
  proc; inline.
  sp; match; auto => />. 
  match; auto => />.
  rewrite dkey_ll dtag_ll //=. 
  by smt().
- move => &1.
  proc; inline*; auto => />.
  sp; match; auto => />.
  match; auto => />.
  by rewrite dkey_ll dtag_ll.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- move => &2 bad.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.

- move => &2 bad.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + auto => />.
  auto => />.
  by rewrite dkey_ll.*)
qed.

local lemma split_badt b &m : Pr[E_GAKE_nodhs(Game2, A).run(b) @ &m : Game2.badt2] =  Pr[E_GAKE_nodhs(Game2, A).run(b) @ &m : Game2.badt2 /\ Game2.badt1] + Pr[E_GAKE_nodhs(Game2, A).run(b) @ &m : Game2.badt2 /\ !Game2.badt1].
proof. 
by rewrite Pr[mu_split Game2.badt1].
qed. 


(* TODO: reduce Pr[E_GAKE_nodhs(Game2, A).run(b) @ &m : Game2.badt1] to the strong CDH assumption!!!! *)


(* ------------------------------------------------------------------------------------------ *)
(* Step 3: Moving sampling of the shared key. *)

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
have -> //: get_origins_c tr sm1l = get_origins_c tr sm1r.
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
call (: ={b0, hm, servers, kp_set, bad, hq, tq, badq, tags, badt}(Game3, Red_ROM2.AKE_O)
          /\ Game3.h1m{1} = ROSc.I1.RO.m{2} /\ Game3.h2m{1} = ROSc.I2.RO.m{2}
          /\ (forall h, omap (fun v => c_clear_k v) Game3.c_smap.[h]{1} = Red_ROM2.AKE_O.c_smap.[h]{2})
          /\ (forall h, omap (fun v => s_clear_k v) Game3.s_smap.[h]{1} = Red_ROM2.AKE_O.s_smap.[h]{2})
          /\ (forall i st pt ir, Game3.c_smap{1}.[i] = Some (Pending st pt ir) 
                => (exists b, ir = (b, false, false)))
          /\ (forall i st pt ir, Game3.s_smap{1}.[i] = Some (Pending st pt ir) 
                => ir = (false, false, false))
          /\ (forall i st t k ir, Game3.c_smap{1}.[i] = Some (Accepted st t k ir)
                => (exists k', Red_ROM2.AKE_O.c_smap{2}.[i] = Some (Accepted st t k' ir))
                   /\ ((oget t.`2).`1 ^ st.`2, st.`1 ^ st.`2, st.`1, g ^ st.`2, (oget t.`2).`1) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[((oget t.`2).`1 ^ st.`2, st.`1 ^ st.`2, st.`1, g ^ st.`2, (oget t.`2).`1)])
          /\ (forall i st t k ir, Game3.s_smap{1}.[i] = Some (Accepted st t k ir)
                => (exists k', Red_ROM2.AKE_O.s_smap{2}.[i] = Some (Accepted st t k' ir))
                   /\ ((t.`1).`2 ^ (oget st.`2), (t.`1).`2 ^ st.`1, g ^ st.`1, (t.`1).`2, g ^ (oget st.`2)) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[((t.`1).`2 ^ (oget st.`2), (t.`1).`2 ^ st.`1, g ^ st.`1, (t.`1).`2, g ^ (oget st.`2))])
          /\ (forall x, x \in ROSc.I1.RO.m{2} <=> x \in ROSc.I2.RO.m{2})
          /\ (Game3.tested{1} <> None <=> Red_ROM2.AKE_O.tested{2} <> None)).

- proc; inline.
  auto => /> &1 &2 *. smt(mem_set get_setE). 

- by sim />. 

- proc; inline.
  sp; if => //.
  sp; match.
  + smt().
  + smt().
  + by auto=> />; smt(get_setE).
  move=> stl str; auto=> />.

- proc; inline.
  sp; match = => // sk.
  match => //.
  + smt().
  + smt().
  seq 1 1: (#pre /\ ={sk}); 1:by auto.
  sp 2 2; if => //.
  swap {1} ^ts<$ @ 1; swap {1} ^ks<$ @ 2.
  swap {2} ^r0<$ @ 1; swap {2} ^r1<$ @ 2. 
  seq  2  2: (#pre /\ ts{1} = r0{2} /\ ks{1} = r1{2}); 1: by auto=> />.
  sp ^if & -1 ^if & -1; if {1} => //.
  + rcondt {1} ^if; 1: by auto => /#.
    rcondt {2} ^if; 1: by auto => /#.
    rcondt {2} ^if; 1: by auto => /#. 
    auto => /> &1 &2 *.
    smt(mem_set get_setE).
  rcondf {1} ^if; 1: by auto => /#.
  rcondf {2} ^if; 1: by auto => /#.
  rcondf {2} ^if; 1: by auto => /#.
  auto => /> &1 &2.
  smt(mem_set get_setE).

- proc; inline.
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
  auto=> /> &1 &2.
  case _: (Game3.c_smap{1}.[i{2}])=> /> c_smap1_i.
  case _: (Red_ROM2.AKE_O.c_smap.[i]{2})=> /> c_smap2_i.
  move=> c_clear s_clear inv1 inv2 inv3 inv4 eq_dom mem_ro.
  move: c_smap2_i; rewrite -c_clear.
  rewrite c_smap1_i=> />.
  smt(mem_set get_setE).


- proc; inline.
  sp; match=> //.
  + smt().
  + smt().
  move => stl str.
  match => //; 1..3: smt().
  move => st'l ptl kl irl st'r ptr kr irr.
  if => //.
  + auto=> />; 1: by smt(c_eq_partners_ck).
  rcondf{2} ^if; 1: by auto => /#.
  auto => /> &1 &2.
  case _: (Game3.c_smap{1}.[i{2}])=> /> c_smap1_i.
  case _: (Red_ROM2.AKE_O.c_smap.[i]{2})=> /> c_smap2_i.
  move=> c_clear s_clear inv1 inv2 inv3 inv4 inv5 eq_dom _ k _. 
  by smt(get_setE mem_set).

- proc; inline.
  sp; match=> //.
  + smt().
  + smt().
  move => stl str.
  match => //; 1..3: smt().
  move => st'l ptl kl irl st'r ptr kr irr.
  if => //.
  + auto=> />; 1: by smt(s_eq_partners_ck).
  rcondf{2} ^if; 1: by auto => /#.
  auto => /> &1 &2.
  case _: (Game3.s_smap{1}.[(b, j){2}])=> /> s_smap1_i.
  case _: (Red_ROM2.AKE_O.s_smap.[(b, j)]{2})=> /> s_smap2_i.
  move=> c_clear s_clear inv1 inv2 inv3 inv4 inv5 eq_dom _ k _.
  by smt(get_setE mem_set).

- proc; inline.
  sp; match => //.
  move => stl str.
  match = => //; 1: smt().
  move => kp.
  if => //.
  + move => /> &1 &2 hkp _ c_clear s_clear inv1 inv2 inv3 inv4 inv5 eq_dom.
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

by auto => />; smt(map_empty emptyE).*)
qed.

lemma LRO_game4 bit &m: Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(bit) @ &m : res] = Pr[E_GAKE_nodhs(Game4, A).run(bit) @ &m : res].
proof. admit. (* Needs fixing
byequiv => //.
proc*.
inline; wp.
call (: ={b0, hm, servers, c_smap, s_smap, tested, kp_set, bad, hq, tq, badq, tags_adv, tags_prot, badt1, badt2}(Red_ROM2.AKE_O, Game4) 
           /\ ROSc.I1.RO.m{1} = Game4.h1m{2} /\ ROSc.I2.RO.m{1} = Game4.h2m{2}); try sim />.

+ proc; inline; auto => />.

+ proc; inline.
  sp; match = => // skb.
  match = => //.
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  sp; if => //; auto => />.

+ proc; inline.
  sp 1 1; match = => // st.
  match = => // st' pt ir.
  sp; seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto.
  auto => />.

+ proc; inline.
  sp 1 1; match = => // st.
  match = => // st' pt k ir.
  if => //.
  sp; seq 1 1: (#pre /\ r{1} = ks{2}); 1: by auto.
  if => //; auto => />; smt(get_setE).

+ proc; inline.
  sp 1 1; match = => // st.
  match = => // st' pt k ir.
  if => //.
  sp; seq 1 1: (#pre /\ r{1} = ks{2}); 1: by auto.
  if => //; auto => />; smt(get_setE).

+ proc; inline.
  sp 1 1; if => //; match = => // st.
  match = => // st' pt k ir.
  if => //; if => //; auto => />; smt(get_setE).

+ proc; inline.
  sp 1 1; if => //; match = => // st.
  match = => // st' pt k ir.
  if => //; if => //; auto => />; smt(get_setE).

auto => />.*)
qed.

(* Step 5: Turn the indistinguishability of real/ideal into probability of the bad event happening *)

op inv_Game4 (tested : int option, 
tq : (pkey * pkey * pkey * pkey * pkey) option, 
badq : bool, 
kp_set : pkey fset, 
ssm : (pkey * int, pr_st_server instance_state) fmap, 
hq : (pkey * pkey * pkey * pkey * pkey) fset, 
csm : (int, pr_st_client instance_state) fmap,
h1m : (pkey * pkey * pkey * pkey * pkey, tag) fmap, 
h2m : (pkey * pkey * pkey * pkey * pkey, key) fmap, 
tags : (pkey * pkey * pkey * pkey * pkey, tag) fmap,
servers : (pkey, server_state) fmap) = 
       (tested = None <=> tq = None)
        /\ (badq <=> (tq <> None /\ oget tq \in hq))
      (*  /\ (forall x, tq = Some x => (exists i m1 tag, i \in ssm /\ get_trace (oget ssm.[i]) = Some (m1, Some (x.`5, tag))))*)
        /\ (forall x y b, tq = Some (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x b), g ^ b, g ^ x, g ^ y) 
             => (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x b), g ^ b, g ^ x, g ^ y) \in h2m 
               /\ ((exists i tag key ir, i \in csm /\ csm.[i] = Some (Accepted_mod (g ^ b, x) ((g ^ b, g ^ x), Some (g ^ y, tag)) key ir)
                     /\ get_ir_test (oget csm.[i]))
                  \/ (exists i tag key ir, i \in ssm /\ ssm.[i] = Some (Accepted_mod (b, Some y) ((g ^ b, g ^ x), Some (g ^ y, tag)) key ir)
                     /\ get_ir_test (oget ssm.[i]))))
        /\ (forall i st t k ir, csm.[i] = Some (Accepted_mod st t k ir) => tested = None => !ir.`3)
        /\ (forall i st t k ir, ssm.[i] = Some (Accepted_mod st t k ir) => tested = None => !ir.`3)
        /\ (forall sk, g ^ sk \in kp_set => sk \in dt)
        /\ (forall i i' m1 m2 m2', csm.[i] <> None /\ get_trace (oget csm.[i]) = Some (m1, m2)
                => csm.[i'] <> None /\ get_trace (oget csm.[i']) = Some (m1, m2')
                => i = i')
        /\ (forall i tr pks, csm.[i] <> None 
                => get_trace (oget csm.[i]) = Some (pks, tr) 
                => pks.`2 \in kp_set)
        /\ (forall i i' m1 m2 tag m1' tag', ssm.[i] <> None /\ get_trace (oget ssm.[i]) = Some (m1, Some (m2, tag))
                => ssm.[i'] <> None /\ get_trace (oget ssm.[i']) = Some (m1', Some (m2, tag'))
                => i = i')
        /\ (forall i tr pk tag, ssm.[i] <> None 
                => get_trace (oget ssm.[i]) = Some (tr, Some (pk, tag)) 
                => pk \in kp_set)
        /\ (forall i st pt ir, csm.[i] = Some (Pending_mod st pt ir)
                => (pt.`1 = st.`1) /\ (pt.`2 = g ^ st.`2) /\ (pt.`2 \in kp_set) /\ !ir.`3)
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
    (*    /\ (forall i st t k ir, csm.[i] = Some (Accepted_mod st t k ir)
                => (exists j st' k' ir', ssm.[j] = Some (Accepted_mod st' t k' ir')))
        /\ (forall x, x \in tags
                => x \in h1m /\ oget tags.[x] = oget h1m.[x] /\ (exists i st k ir, ssm.[i] = Some (Accepted_mod st ((x.`3, x.`4), Some (x.`5, oget tags.[x])) k ir)))*)
        /\ (forall b sk, b \in servers => (get_skey (oget servers.[b])) = Some sk => b = g ^ sk).



lemma interestingbit &m: `|Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : res] - Pr[E_GAKE_nodhs(Game4, A).run(true) @ &m : res]| <= Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : Game4.badq].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game4.badq => //; first last.
+ smt().
symmetry; proc; inline.
wp.
call (: Game4.badq
      , ={servers, c_smap, s_smap, tested, kp_set, hm, bad, h1m, hq, tq, badq, tags_adv, tags_prot, badt1, badt2}(Game4, Game4)
        /\ (Game4.tq{1} = None => ={Game4.h2m})
        /\ (forall x, Game4.tq{1} = Some x => eq_except (pred1 x) Game4.h2m{1} Game4.h2m{2})
        /\ Game4.b0{1} = false /\ Game4.b0{2} = true
        /\ (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.kp_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.tags_prot Game4.servers){2}
        /\ (forall x, x \in Game4.h2m{1} <=> x \in Game4.h2m{2})
      , ={badq}(Game4, Game4)) => //; last first.

- auto => />.
split; 1: by smt(emptyE in_fset0).
move => ntc nts ninkps injc pkins injs trs pc acc acs inv acas skpk rl rr al bl bql csl hql kpl ssl sl tl tql h1ml h2ml btl tgsl ar br bqr csr hqr kpr ssr sr tr tqr h1mr h2mr btr tgsr b1 b2 b3. 
by case : (!csr) => />. 

- exact A_ll.

- proc; inline.  
  sp; seq 1 1: (#pre /\ t{1} = t{2}); 1: by auto=> />.
  if => //.
  + sp; seq 1 1: (#pre /\ ={k}); 1: by auto => />.
    if => //; auto => /> &1 &2 *; by smt(get_setE in_fsetU1 mem_set).
  seq 1 1: (#pre /\ ={k}); 1: by auto => />.
  if => //; auto => /> &1 &2 *; by smt(get_setE in_fsetU1 mem_set).
- move => &2 badq; proc*; inline. auto => />. 
  rewrite dkey_ll dtag_ll //=. smt().
- move => &1; proc*; inline; auto.
  rewrite dkey_ll dtag_ll //=. smt(). 

- proc.
  auto => /> &1 &2 *.
  smt(in_fsetU1 pow_bij get_setE).
- move => &2 badq.
  proc; auto.
  rewrite dt_ll //=.
- move => &1. 
  proc.
  auto => />. 
  by rewrite dt_ll.
 
- proc; inline.
  sp; if => //.
  sp; match = => //.
  auto => /> &1 &2 ? _ ? ? ? ? ? inv4 ? ? ? ? inv ? ? ? inv3 inv5 inv2 inv6 inv7 ? sk *.
  split; 1: by smt().
  split.
  + move => x0 y0 b0 tqeq.
    have := inv4 x0 y0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set).
  split; 1: by smt(get_setE).
  split; 1: by smt(in_fsetU1 pow_bij).
  split.    
  + move => // i0 i'.
    case (i0 = i{2}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      move => m10 m2 m2' [] m10eq m2eq trs.
      have := inv i' None (m1{2}, g ^ sk).
      by smt(pow_bij).
    case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => stnn.
    rewrite i'eq !get_set_sameE //=.
    by smt(pow_bij).
  split; 1: by smt(get_setE in_fsetU1).
  split; 1: by smt(get_setE in_fsetU1).
  split; 1: by smt(get_setE in_fsetU1).
  split; 1: by smt(get_setE in_fsetU1).
  + move => x0 y0 b0 x0in.
  have := inv2 x0 y0 b0 x0in.
  move => [H1|[H2|H3]].
  + left.
    move : H1 => [i'] t' k' ir' H1.
    exists i'. 
    smt(get_setE).
  + smt().
  by smt().
- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  rewrite dt_ll. smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  by rewrite dt_ll.
  
- proc; inline.
  sp; match = => // sk_s.
  match = => //.
  seq 1 1: (#pre /\ ={sk} /\ sk{2} \in dt); 1: by auto=> />.
  sp 2 2; if => //.
  sp; seq 1 1: (#pre /\ ={ts}); 1: by auto=> />.
  if => //.
  + auto => /> &1 &2 kps ? ? _ ? _ ? ? ? c1 ? inv5 ? ? ? ? ? ? inv ? inv2 inv8 inv6 inv4 *.
    split; 1: by smt(get_setE in_fsetU1).
    split. clear inv8.
    + move => x0 y0 b0 tqeq.
      have := inv5 x0 y0 b0 tqeq.
      move => [] H1 [H2|H3].
      + smt().
      split; 1: by smt().
      move : H3 => [i'] t k ir H3.
      right. exists i'.
      by smt(get_setE).
    split; 1: by smt(get_setE).
    split; 1: by smt(in_fsetU1 pow_bij).
    split; 1: by smt(get_setE in_fsetU1).
    split. 
    + move => // i0 i'.
      case (i0 = (b, j){2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_sameE get_set_neqE //=.
        move => m1 m20 tag m1' tag' stnn trs.
        have := inv i' (g^ sk_s, m2{2}) pk{2} ts{2}.
        by smt(pow_bij).
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => stnn.
      rewrite i'eq !get_set_sameE //=.
      by smt(pow_bij).
    split; 1: by smt(get_setE in_fsetU1).
    split. smt(get_setE in_fsetU1).
split. smt(get_setE).
split. 
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
(*    move => x0.
    case (x0 = (m2{2} ^ sk{2}, m2{2} ^ sk_s, g ^ sk_s, m2{2}, (g ^ sk{2}))) => x0eq; rewrite get_setE mem_set x0eq //=.
    + do rewrite get_set_sameE.
      split; 1: by smt(mem_set).
      split; 1: by done. 
      exists (b, j){2} (sk_s, Some sk{2}) witness (false, false, false).
      have := inv7 b{2} sk_s.
      smt(get_setE).
    rewrite get_set_neqE //=.
    move => x0in.
    split; 1: by smt(get_setE).
    split; 1: by smt(get_setE).
    have:= inv4 x0 x0in.
    move => [H1] [H2] [i st k ir] H3.
    exists i st k ir.
    case ((b,j){2} = i) => ieq; 1: by smt().
    smt(get_set_neqE).*)
  auto => /> &1 &2 kps ? ? _ ? _ ? ? ? c1 ? inv5 ? ? ? ? ? ? inv2 ? ? inv8 inv inv4 *.
  split; 1: by smt(get_setE in_fsetU1).
  split. clear inv8.
  + move => x0 y0 b0 tqeq.
    have := inv5 x0 y0 b0 tqeq.
    move => [] H1 [H2|H3].
    + smt().
    split; 1: by smt().
    move : H3 => [i'] t k ir H3.
    right. exists i'.
    by smt(get_setE).
  split; 1: by smt(get_setE).
  split. smt(in_fsetU1 pow_bij).
  split; 1: by smt(get_setE in_fsetU1).
  split.
  + move => // i0 i'.
    case (i0 = (b, j){2}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      move => m1 m20 tag m1' tag' stnn trs.
      have := inv2 i' (g ^ sk_s, m2{2}) pk{2} ts{2}.
      by smt(pow_bij).
    case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => stnn.
    rewrite i'eq !get_set_sameE //=.
    by smt(pow_bij).
  split; 1: by smt(get_setE in_fsetU1).
    split. smt(mem_set get_setE in_fsetU1).
split.
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
(*  move => x0.
  case (x0 = (m2{2} ^ sk{2}, m2{2} ^ sk_s, g ^ sk_s, m2{2}, (g ^ sk{2}))) => x0eq; rewrite get_setE mem_set x0eq //=.
  + split; 1: by smt(get_setE).
    exists (b,j){2} (sk_s, Some sk{2}) witness (false, false, false).
    have := inv7 b{2} sk_s.
    smt(get_setE).
  move => x0in.
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  have:= inv4 x0 x0in.
  move => [H1] [H2] [i st k ir] H3.
  exists i st k ir.
  case ((b,j){2} = i) => ieq; 1: by smt().
  smt(get_set_neqE).*)
- move => &2 bad.
  proc; inline; sp; match; auto => />.
  match => //.
  islossless.
- move => &1. 
  proc; inline; sp; match; auto => />.
  match => //.
  islossless.
 
- proc; inline.
  sp; match = => // st.
  match = => // st' pt ir.
  sp; seq 1 1: (#pre /\ ={ts}); 1: by auto=> />.
  if => //.
  + sp 5 5; if => //.
    + auto => /> &1 &2 ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *.
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
    auto => /> &1 &2 ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *.
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
  + auto => /> &1 &2 ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *.
    split; 1: by smt(get_setE).
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
    split. smt(get_setE). 
    split. smt(get_setE). 
    split. smt(get_setE).
    split. smt(get_setE).
    + move => x0 y0 b0 x0in.
      have := inv5 x0 y0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
  auto => /> &1 &2 ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *.
  split; 1: by smt(get_setE).
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
  split. smt(get_setE). 
  split. smt(get_setE). 
  split. smt(get_setE).
  split. smt(get_setE).
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
  sp; match; auto. 
  match; auto => />.
  by rewrite dtag_ll.
- move => &1.
  proc; inline*; auto => />.
  sp; match; auto.
  match; auto.
  by rewrite dtag_ll.
 
- proc; inline.
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
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
  if => //; inline.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.
  if => //; inline. 
  auto => />.
  by rewrite dkey_ll.

- proc; inline.
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
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
  if => //; inline.
  auto => />.
  by rewrite dkey_ll.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.
  if => //; inline.
  auto => />.
  by rewrite dkey_ll.

- proc; inline.
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
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
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
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
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
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
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
      split. admit.
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
  auto => /> &1 &2 ? ? stc ? ? ? ? ? ? ? ? ? _ inv2 ? inv4 ? ? ? ? inv inv3 ? fresh ? x2in *.
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
- move => &2 bad.
  proc; inline; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + inline; auto => />.
    by rewrite dkey_ll /#.
  auto => />.
  by rewrite dkey_ll /#.
- move => &1.
  proc; inline; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + inline; auto => />.
    by rewrite dkey_ll /#.
  auto => />.
  by rewrite dkey_ll /#.

- proc; inline.
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
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? _ inv3 ? inv2 ? ? ? ? inv ? ? fresh ? x2in *.
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
- move => &2 bad.
  proc; inline; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + inline; auto => />.
    by rewrite dkey_ll /#.
  auto => />.
  by rewrite dkey_ll /#.
- move => &1.
  proc; inline; sp; if => //; sp; match; 1: by auto. 
  match; auto.
  if => //; if => //.
  + inline; auto => />.
    by rewrite dkey_ll /#.
  auto => />.
  by rewrite dkey_ll /#.
qed.



(* update where we are *)
lemma sofar &m: `| Pr[E_GAKE_nodhs(GAKEb_nodhs(NTOR_S_mod(RO), NTOR_C_mod(RO), RO), A).run(false) @ &m : res] - Pr[E_GAKE_nodhs(GAKEb_nodhs(NTOR_S_mod(RO), NTOR_C_mod(RO), RO), A).run(true) @ &m : res]|
  <= Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : Game4.badq] 
       + Pr[E_GAKE_nodhs(Game2, A).run(false) @ &m : Game2.badt] + Pr[E_GAKE_nodhs(Game2, A).run(true) @ &m : Game2.badt] 
       + 2%r * ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt).
proof. 
rewrite !(gake_game0 _).
apply (ler_trans (`|Pr[E_GAKE_nodhs(Game1, A).run(false) @ &m : res] - Pr[E_GAKE_nodhs(Game1, A).run(true) @ &m : res]| + 2%r * ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt))).
+ smt(game0_game1 game0_bad).
rewrite ler_add2r.
rewrite !(game1_game2 _).
apply (ler_trans (`|Pr[E_GAKE_nodhs(Game3, A).run(false) @ &m : res] - Pr[E_GAKE_nodhs(Game3, A).run(true) @ &m : res]| + Pr[E_GAKE_nodhs(Game2, A).run(false) @ &m : Game2.badt] +
             Pr[E_GAKE_nodhs(Game2, A).run(true) @ &m : Game2.badt])).
+ smt(game2_game3).
rewrite !ler_add2r.
by rewrite !game3_RO !LRO_game4 interestingbit.
qed. 





(* Step 7: Reduction to multi-instance st-CDH assumption *)
(*
lemma game4_gameddh &m: Pr[E_GAKE_nodhs(Game4, A).run(false) @ &m : Game4.badq] = Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq].
proof.
byequiv => //.
proc; inline.
call (: ={b0, hm, servers, c_smap, s_smap, tested, kp_set, bad, hq, tq, badq, tags, badt, test_ephrev_s}(Game4, GameDDH)
        /\ (Game4.b0{1} = false)
        /\ (forall x, Game4.h1m{1}.[x] = GameDDH.h1mDDH{2}.[(clear_ddh x)])
        /\ (forall x, Game4.h2m{1}.[x] = GameDDH.h2mDDH{2}.[(clear_ddh x)])); 2,3, 8, 9,10: sim />; last first.

auto => />.
smt(emptyE in_fset0).

+ proc; inline.
  sp 2 6. 
  if{2} => //.
  + sp. seq 1 1: (#pre /\ ={t}); 1: by auto => />.
    if => //; 1: auto => /#.
    + sp. seq 1 1: (#pre /\ ={k}); 1: by auto => />.
      if => //; 1: by auto => /#.
      + auto => />. smt(get_setE).
      auto => />. smt(get_setE).
    sp; seq 1 1: (#pre /\ ={k}); 1: by auto => />.
    if => //; 1: by auto => /#.
    + auto => />. smt(get_setE mem_set).
    auto => />. smt(get_setE).
  sp. seq 1 1: (#pre /\ ={t}); 1: by auto => />.
  if => //; 1: auto => /#.
  + sp. seq 1 1: (#pre /\ ={k}); 1: by auto => />.
    if => //; 1: by auto => /#.
    + auto => />. smt(get_setE).
    auto => />. smt(get_setE).
  sp; seq 1 1: (#pre /\ ={k}); 1: by auto => />.
  if => //; 1: by auto => /#.
  + auto => /> &1 &2 *. smt(get_setE mem_set).
  auto => /> &1 &2 *. smt(get_setE).

+ proc; inline.
  sp; match = => // sk_b.
  match = => //.
  seq 1 1 : (#pre /\ ={sk}). auto => />.
  sp 2 2; if => //.
  sp; seq 1 1 : (#pre /\ ={ts}). auto => />.
  if => //. auto => />. 
  + smt(mem_set loggK).
  + auto => />. smt(get_setE mem_set loggK).
  auto => />. smt(get_setE mem_set loggK).

+ proc; inline.
  sp; match = => // st.
  match = => // s pt ir.
  sp; seq 1 1 : (#pre /\ ={ts}). auto => />.
  if => //. auto => />. 
  + smt(ComRing.mulrC expM expgK mem_set). 
  + auto => />. smt(ComRing.mulrC expM expgK get_setE mem_set).
  auto => />. smt(ComRing.mulrC expM expgK mem_set). 

+ proc; inline.
  sp; match = => // st.
  match = => // s t k ir.
  if => //.
  sp; seq 1 1 : (#pre /\ ={ks}). auto => />.
  if => //. auto => />. smt(ComRing.mulrC expM expgK mem_set). 
  + auto => /> &1 &2 *. smt(ComRing.mulrC expM expgK get_setE mem_set).
  auto => />. smt(ComRing.mulrC expM expgK mem_set). 

+ proc; inline.
  sp; match = => // st.
  match = => // s t k ir.
  if => //.
  sp; seq 1 1 : (#pre /\ ={ks}). auto => />.
  if => //. auto => />. smt(get_setE mem_set loggK).
  + auto => />. smt(get_setE mem_set loggK).
  auto => />. smt(get_setE mem_set loggK).

+ proc; inline.
  sp 1 1; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //.
  if => //.
  + sp; seq 1 1 : (#pre /\ ={ks}). auto => />.
    if => //. auto => />. smt(ComRing.mulrC expM expgK mem_set). 
    + auto => />. smt(ComRing.mulrC expM expgK get_setE mem_set).
    auto => />. smt(ComRing.mulrC expM expgK mem_set). 
  auto => />.

+ proc; inline.
  sp 1 1; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //.
  if => //.
  + sp; seq 1 1 : (#pre /\ ={ks}). auto => />.
    if => //. auto => />. smt(get_setE mem_set loggK).
    + auto => />. smt(get_setE mem_set loggK).
    auto => />. smt(get_setE mem_set loggK).
  auto => />.
qed.
*)

(*
lemma tested_nn &m: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.tested = None] = 0%r.
proof.
byphoare => //; hoare.
proc; inline.
call (_: ! (GameDDH.badq /\ GameDDH.tested = None) /\ (GameDDH.tested = None <=> GameDDH.tq = None)); 2..10: conseq (: true) => //.

- proc; inline; auto => /#.


- proc; inline.
  sp; if => //.
  exlim GameDDH.c_smap.[i] => csi.
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
  exlim GameDDH.s_smap.[(b, j)] => ssj.
  case (ssj = None).
  + match None ^match => //.
  match Some ^match => //.
  + skip => /#.
  match => //; if => //; if => //.
  + sp; seq 1: (#pre /\ ks \in dkey); 1: by auto => />.
    auto => />.
  sp; seq 1: (#pre /\ ks2 \in dkey); 1: by auto => />.
  auto => />.

auto => /> badq tested tq.
qed.


lemma test_i_pr &m: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq] = Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ (exists i, GameDDH.tested = Some i)].
proof.
have->: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq] = Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.tested = None] 
               + Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.tested <> None] by rewrite Pr[mu_split GameDDH.tested = None].
have->: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.tested <> None] = Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ (exists i, GameDDH.tested = Some i)].
+ rewrite Pr[mu_eq] // => &hr.
  by smt().
by smt(tested_nn).
qed.


op max_qc : int.
axiom max_qc : 0 < max_qc.

lemma sum_pr &m: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ (exists i, GameDDH.tested = Some i)] = 
                   big predT (fun i => Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.tested = Some i]) (range 1 (max_qc + 1))
                   + Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ (exists i, GameDDH.tested = Some i) /\ !mem (range 1 (max_qc + 1)) (oget GameDDH.tested)].
proof.
rewrite Pr[mu_split (mem (range 1 (max_qc + 1)) (oget GameDDH.tested))]. congr.
+ elim: (range 1 (max_qc + 1)) (range_uniq 1 (max_qc + 1)) => /=; 1: by rewrite big_nil Pr[mu_false].
  move => x xs ih [] x_notin_xs uniq_xs /=.
  rewrite {1}andb_orr Pr[mu_or] andbCA !andbA. 
  have ->: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : ((((GameDDH.badq /\ exists (i : int), GameDDH.tested = Some i) /\ GameDDH.badq) /\
     exists (i : int), GameDDH.tested = Some i) /\ oget GameDDH.tested = x) /\ (oget GameDDH.tested \in xs)]
         = Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : false].
  + rewrite Pr[mu_eq] // => &hr.
    by smt().
  rewrite Pr[mu_false] //= big_cons {1}/predT /=. congr.
  + rewrite Pr[mu_eq] // => &hr. 
    by smt().
  exact/ih.
by rewrite andbA.
qed.


lemma test_ephrev_nn &m i: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : (GameDDH.badq /\ GameDDH.tested = Some i) /\ GameDDH.test_ephrev_s = None] = 0%r.
proof.
byphoare => //; hoare.
proc; inline.
call (_: ! (GameDDH.badq /\ GameDDH.tested = None /\ GameDDH.test_ephrev_s = None) /\ (GameDDH.test_ephrev_s = None <=> GameDDH.tq = None) /\ (GameDDH.tested = None <=> GameDDH.tq = None)); 2..10: conseq (: true) => //.

- proc; inline; auto => /#.

- proc; inline.
  sp; if => //.
  exlim GameDDH.c_smap.[i{!hr}] => csi.
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
  exlim GameDDH.s_smap.[(b, j)] => ssj.
  case (ssj = None).
  + match None ^match => //.
  match Some ^match => //.
  + skip => /#.
  match => //; if => //; if => //.
  + sp; seq 1: (#pre /\ ks \in dkey); 1: by auto => />.
    auto => />.
  sp; seq 1: (#pre /\ ks2 \in dkey); 1: by auto => />.
  auto => />.

auto => /#.
qed.


lemma split_pr &m i: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.tested = Some i] = 
                     Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.tested = Some i /\ GameDDH.test_ephrev_s = Some true] 
                     + Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.tested = Some i /\ GameDDH.test_ephrev_s = Some false].
proof.
rewrite Pr[mu_split GameDDH.test_ephrev_s = None].
rewrite test_ephrev_nn //=.
rewrite Pr[mu_split GameDDH.test_ephrev_s = Some true].
do rewrite -andbA.
by congr; rewrite Pr[mu_eq] // => &hr; smt().
qed.

lemma split_j_pr 


module type DDH_oracle = {
  proc run(gx : group, gy : group, gz : group) : bool
}.

module DDH_O : DDH_oracle = {
  proc run(gx, gy, gz : group): bool = {
    return (gz = gy ^ (loge gx));
  }
}.*)

lemma test_ephrev_nn &m: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.test_ephrev_s = None] = 0%r.
proof.
byphoare => //; hoare.
proc; inline.
call (_: ! (GameDDH.badq /\ GameDDH.test_ephrev_s = None) /\ (GameDDH.test_ephrev_s = None <=> GameDDH.tq = None) /\ (GameDDH.tested = None <=> GameDDH.tq = None)); 2..10: conseq (: true) => //.

- proc; inline; auto => /#.

- proc; inline.
  sp; if => //.
  exlim GameDDH.c_smap.[i{!hr}] => csi.
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
  exlim GameDDH.s_smap.[(b, j)] => ssj.
  case (ssj = None).
  + match None ^match => //.
  match Some ^match => //.
  + skip => /#.
  match => //; if => //; if => //.
  + sp; seq 1: (#pre /\ ks \in dkey); 1: by auto => />.
    auto => />.
  sp; seq 1: (#pre /\ ks2 \in dkey); 1: by auto => />.
  auto => />.

auto => /#.
qed.

lemma split_pr &m: Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq] = 
                     Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.test_ephrev_s = Some true] 
                     + Pr[E_GAKE_nodhs(GameDDH, A).run(false) @ &m : GameDDH.badq /\ GameDDH.test_ephrev_s = Some false].
proof.
rewrite Pr[mu_split GameDDH.test_ephrev_s = None].
rewrite test_ephrev_nn //=.
rewrite Pr[mu_split GameDDH.test_ephrev_s = Some true].
do rewrite -andbA.
by congr; rewrite Pr[mu_eq] // => &hr; smt().
qed.

print Red_Ltk.Red_O.

op clear_ddh(x : group * group * group * group * group) =
  if (x.`4 ^ (loge x.`5) = x.`1) /\ (x.`4 ^ (loge x.`3) = x.`2) then (None, None, x.`3, x.`4, x.`5) 
    else (Some x.`1, Some x.`2, x.`3, x.`4, x.`5).

local op clear_sk (s : server_state) =
match s with
| Honest_mod sk => Honest_mod witness
| Corrupt_mod sk => Corrupt_mod witness
| Dishonest_mod => s
end.

local op clear_opt_c (s : pr_st_client option) = if s <> None then Some ((oget s).`1, witness) else Some ((oget s).`1, (oget s).`2).

local op clear_esk (s : pr_st_client instance_state) = 
match s with
| Pending_mod st pt ir => let (pk, sk) = st in Pending_mod (pk, witness) pt ir
| Accepted_mod st t k ir => let (pk, sk) = st in Accepted_mod (pk, witness) t k ir
| Aborted_mod st t ir => Aborted_mod (clear_opt_c st) t ir
end. 

local op clear_opt_s (s : pr_st_server option) = if s <> None then Some (witness, (oget s).`2) else Some ((oget s).`1, (oget s).`2).

local op clear_ltsk (s : pr_st_server instance_state) = 
match s with 
| Pending_mod st pt ir => let (sk, esk) = st in Pending_mod (witness, esk) pt ir
| Accepted_mod st t k ir => let (sk, esk) = st in Accepted_mod (witness, esk) t k ir
| Aborted_mod st t ir => Aborted_mod (clear_opt_s st) t ir
end.

lemma cdh_red_ltk &m: Pr[E_GAKE_nodhs(Game4, A).run(true) @ &m : Game4.badq /\ Game4.test_ephrev_s = Some true] <= 
                 Pr[St_CDH_E(St_CDH_O, Red_Ltk(A)).run() @ &m : St_CDH_O.win].
proof. 
byequiv (: ={glob A} /\ arg{1} = true ==> _) => //.
proc; inline.
call (: Red_Ltk.Red_O.stop,
        ={b0, hm, tested, kp_set, bad, badt, test_ephrev_s}(Game4, Red_Ltk.Red_O)
         /\ (forall x, (clear_ddh x) \in Red_Ltk.Red_O.h1m_opt{2} => Game4.h1m{1}.[x] = Red_Ltk.Red_O.h1m_opt{2}.[(clear_ddh x)])
         /\ (forall x, (clear_ddh x) \in Red_Ltk.Red_O.h2m_opt{2} => Game4.h2m{1}.[x] = Red_Ltk.Red_O.h2m_opt{2}.[(clear_ddh x)])
         /\ (forall x, x \in Red_Ltk.Red_O.h1m{2} => Game4.h1m{1}.[x] = Red_Ltk.Red_O.h1m{2}.[x])
         /\ (forall x, x \in Red_Ltk.Red_O.h2m{2} => Game4.h2m{1}.[x] = Red_Ltk.Red_O.h2m{2}.[x])
         /\ (forall x, x \in Game4.h1m{1} => x \in Red_Ltk.Red_O.h1m{2} \/ Red_Ltk.Red_O.stop{2})
         /\ (forall x, x \in Game4.h2m{1} => x \in Red_Ltk.Red_O.h2m{2} \/ Red_Ltk.Red_O.stop{2})
         /\ (forall x, x \in Game4.tags{1} => (None, None, x.`3, x.`4, x.`5) \in Red_Ltk.Red_O.tags_opt{2})
         /\ (forall x, x \in Red_Ltk.Red_O.tags_opt{2} => (x.`4 ^ (loge x.`5), x.`4 ^ (loge x.`3), x.`3, x.`4, x.`5) \in Game4.tags{1})
         /\ (forall pk, omap clear_sk Game4.servers{1}.[pk] = Red_Ltk.Red_O.servers{2}.[pk])
         /\ (forall bj, omap clear_ltsk Game4.s_smap{1}.[bj] = Red_Ltk.Red_O.s_smap{2}.[bj])
         /\ (forall i, omap clear_esk Game4.c_smap{1}.[i] = Red_Ltk.Red_O.c_smap{2}.[i])
         /\ (forall i st pt ir, i \in Game4.c_smap{1} => Game4.c_smap{1}.[i] = Some (Pending_mod st pt ir)
              => pt.`2 = g ^ st.`2 /\ pt.`1 = st.`1)
         /\ (forall i st t k ir, i \in Game4.c_smap{1} => Game4.c_smap{1}.[i] = Some (Accepted_mod st t k ir)
              => t.`1.`2 = g ^ st.`2 /\ t.`1.`1 = st.`1)
         /\ (forall bj st t k ir, bj \in Game4.s_smap{1} => Game4.s_smap{1}.[bj] = Some (Accepted_mod st t k ir)
              => t.`1.`1 = g ^ st.`1)
         /\ (forall b sk, b \in Game4.servers{1} => obind get_skey Game4.servers{1}.[b] = Some sk
              => b = g ^ sk)
       (*  /\ (forall i st pt ir, i \in Red_Ltk.Red_O.c_smap{2} => Red_Ltk.Red_O.c_smap{2}.[i] = Some (Pending_mod st pt ir)
              => st.`2 = witness)*)
         /\ (Game4.badq{1} /\ Game4.test_ephrev_s{1} = Some true => St_CDH_O.win{2}),
        St_CDH_O.win{2}); last first.

auto => />.
split. smt(emptyE mem_empty).
move => inv1 inv6 inv7 inv8 inv9 inv10 inv11 inv12 roeq inj csm ssm pkin inv inv2 inv3 inv4 inv5 rl rr al hsl csl pksl ssl sl stl tl url ml ar hsr csr tr str huh ssr sr pksr urr mr.
by case : (!ssr) => />.

- exact A_ll.

+ proc; inline.
  sp; if {2} => //.
  + sp 0 2; if {2} => //.
    + if {2} => //.
      + auto => />.
      sp; seq 1 1: (#pre /\ ={t}). auto => />.
      if => //. auto => /#.
      + sp; seq 1 1: (#pre /\ ={k}). auto => />.
        if => //. auto => /#.
        + auto => /> &1 &2 *.  do split; ~9: smt(mem_set get_setE in_fsetU in_fset1 loggK expgK). admit.
        auto => /> &1 &2 *. do split; ~6: smt(mem_set get_setE in_fsetU in_fset1 loggK expgK). admit.
      auto => /> &1 &2 *. admit.
    sp; seq 1 1: (#pre /\ ={t}). auto => />.
    if => //. auto => /#.
    + sp; seq 1 1: (#pre /\ ={k}). auto => />.
      if => //. auto => /#.
      + auto => /> &1 &2 *. do split; ~9: smt(mem_set get_setE in_fsetU in_fset1 loggK expgK). admit.
      auto => /> &1 &2 *.  do split; ~6: smt(mem_set get_setE in_fsetU in_fset1 loggK expgK). admit.
    auto => /> &1 &2 *.  admit.
  auto => />.
- move => &2 bad; proc; inline; auto => />. 
  by rewrite dtag_ll dkey_ll //=.
- move => &1; proc; inline.
  sp; if => //; auto; smt(dtag_ll dkey_ll).

+ proc; inline.
  if {2} => //; 2: by auto => />.
  sp; seq 1 1 : (#pre /\ sk{1} = y_m{2}). auto => />.
  auto => /> &1 &2 *. smt(mem_set get_setE in_fsetU in_fset1). 
- move => &2 bad; proc; inline; auto => />. 
  by rewrite dt_ll //=.
- move => &1; proc; inline.
  sp; if => //.
  auto => />.

+ proc; inline.
  if {2} => //.
  + sp; if => //. auto => /#.
    + match {1} => //.
      + match None {2} ^match. auto => /#.
        auto => />. smt(mem_set get_setE in_fsetU in_fset1).
      match Some {2} ^match. auto => /#.
      auto => />.
    auto => />.
  sp 2 0; if {1} => //.
  match {1} => //.
  auto => />.
- move => &2 bad; proc; inline. 
  sp; if => //; match; auto => />. 
  by rewrite dt_ll //=.
- move => &1; proc; inline.
  sp; if => //.
  sp; if => //; match; auto => />.

+ proc; inline.
  if {2} => //.
  + sp; match {1} => //.
    + match None {2} ^match => //. auto => /#.
    match Some {2} ^match => //. auto => /#.
    match {1} => //.
    + match None {2} ^match. auto => /#.
      seq 1 1: (#pre /\ ={sk}). auto => />.
      sp; if => //.
      sp; seq 1 1: (#pre /\ ={ts}). auto => />.
      if => //. auto => /#.
      + auto => /> &1 &2 *. do split; smt(mem_set get_setE in_fsetU in_fset1 loggK expgK).
      auto => /> &1 &2 *. do split; smt(mem_set get_setE in_fsetU in_fset1 loggK expgK).
    match Some {2} ^match. auto => /#.
    auto => />.
  sp; match {1} => //.
  match {1} => //.
  seq 1 0 : (#pre /\ sk{1} \in dt). auto => />.
  sp 2 0; if {1} => //.
  auto => />.
- move => &2 bad; proc; inline. 
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
  sp; if => //; auto => />.

+ proc; inline.
  if {2} => //.
  + sp; match {1} => //.
    + match None {2} ^match. auto => /#.
      auto => />.
    match Some {2} ^match. auto => /#.
    match {1} => //.
    + match Pending_mod {2} ^match. auto => /#.
      sp; seq 1 1 : (#pre /\ ={ts}). auto => />.
      if => //. auto => /#.
      + sp 4 4; if => //. 
        + auto => /> &1 &2 *. smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).
        + auto => /> &1 &2 *. split. move => *. split. smt(get_setE). move => *. do split; smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).
move => *. split. smt(get_setE). move => *. do split; smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).
        auto => /> &1 &2 *. smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).  
      auto => /> &1 &2 *. split. move => *. split. smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).  move => *. split. move => *. split. smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC). move => *. do split; smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC). move => *. do split; smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC). move => *. do split; smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).
    + match Accepted_mod {2} ^match. auto => /#.
      auto => />.
    match Aborted_mod {2} ^match. auto => /#.
    auto => />.
  sp; match {1} => //.
  match {1} => //; auto => />.
- move => &2 bad; proc; inline. 
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

+ proc; inline.
  if {2} => //.
  + sp; match {1} => //.
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
                  get_trace val = Some t'{1}) GameDDH.s_smap{1})) = (fdom
            (filter
               (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                  get_trace val = Some t'{2}) Red_Ltk.Red_O.s_smap{2})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          smt(get_setE mem_set).
        have->: (fdom
              (filter
                 (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                    get_trace val = Some t'{1} /\ get_ir_test val = false)
                 GameDDH.s_smap{1})) = (fdom
              (filter
                 (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                    get_trace val = Some t'{2} /\ get_ir_test val = false)
                 Red_Ltk.Red_O.s_smap{2})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          smt(get_setE mem_set).
        smt().
      + auto => /> &1 &2 *. do split; smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).
    match Aborted_mod {2} ^match. auto => /#.
    auto => />.
  sp; match {1} => //.
  match {1} => //; if {1} => //; auto => />.
- move => &2 bad; proc; inline. 
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

+ proc; inline.
  if {2} => //.
  + sp; match {1} => //.
    + match None {2} ^match. auto => /#.
      auto => />.
    match Some {2} ^match. auto => /#.
    match {1} => //.
    + match Pending_mod {2} ^match. auto => /#.
      auto => />.
    + match Accepted_mod {2} ^match. auto => /#.
      if => //.
      + auto => &1 &2 *.
        rewrite /untested_partner_s.
        rewrite /get_partners_s /get_untested_partners_s.
        have->: (fdom
            (filter
               (fun (_ : int) (val : pr_st_client instance_state) =>
                  get_trace val = Some t'{1}) GameDDH.c_smap{1})) = (fdom
            (filter
               (fun (_ : int) (val : pr_st_client instance_state) =>
                  get_trace val = Some t'{2}) Red_Ltk.Red_O.c_smap{2})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          smt(get_setE mem_set).
        have->: (fdom
              (filter
                 (fun (_ : int) (val : pr_st_client instance_state) =>
                    get_trace val = Some t'{1} /\ get_ir_test val = false)
                 GameDDH.c_smap{1})) = (fdom
              (filter
                 (fun (_ : int) (val : pr_st_client instance_state) =>
                    get_trace val = Some t'{2} /\ get_ir_test val = false)
                 Red_Ltk.Red_O.c_smap{2})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          smt(get_setE mem_set).
        smt().
      + auto => /> &1 &2 *. do split; smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).
    match Aborted_mod {2} ^match. auto => /#.
    auto => />.
  sp; match {1} => //.
  match {1} => //; if {1} => //; auto => />.
- move => &2 bad; proc; inline. 
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

+ proc; inline.
  admit.
- move => &2 bad; proc; inline. 
  sp; match => //. 
  match => //.
  by auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  by auto => />.

+ proc; inline.
  admit.
- move => &2 bad; proc; inline. 
  sp; match => //. 
  by match => //; auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  by match; auto => />.

+ proc; inline.
  admit.
- move => &2 bad; proc; inline. 
  sp; match => //. 
  by match => //; auto => />.
- move => &1; proc; inline.
  sp; if => //.
  sp; match => //. 
  by match; auto => />.

+ proc; inline.
  if {2} => //.
  + sp; if => //.
    match {1} => //.
    + match None {2} ^match. auto => /#.
      auto => />.
    match Some {2} ^match. auto => /#.
    match {1} => //.
    + match Pending_mod {2} ^match. auto => /#.
      auto => />.
    + match Accepted_mod {2} ^match. auto => /#.
      if => //.
      + auto => &1 &2 *.
        rewrite /fresh_partner_c.
        rewrite /get_origins_c /get_fresh_partners_c.
        have->: (fdom
            (filter
               (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                  exists (m2o : (pkey * tag) option),
                    get_trace val = Some (t'{1}.`1, m2o)) GameDDH.s_smap{1})) = (fdom (filter
               (fun (_ : pkey * int) (val : pr_st_server instance_state) =>
                  exists (m2o : (pkey * tag) option),
                    get_trace val = Some (t'{2}.`1, m2o)) Red_Ltk.Red_O.s_smap{2})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          smt(get_setE mem_set).
        have->: (fdom
              (filter
                 (fun (bj : pkey * int)
                    (val : pr_st_server instance_state) =>
                    get_trace val = Some t'{1} /\
                    get_ir_test val = false /\
                    get_ir_sess val = false /\
                    (get_ir_eph val = false \/
                     get_sr_ltk (oget GameDDH.servers{1}.[bj.`1]) = false))
                 GameDDH.s_smap{1})) = (fdom
              (filter
                 (fun (bj : pkey * int)
                    (val : pr_st_server instance_state) =>
                    get_trace val = Some t'{2} /\
                    get_ir_test val = false /\
                    get_ir_sess val = false /\
                    (get_ir_eph val = false \/
                     get_sr_ltk (oget Red_Ltk.Red_O.servers{2}.[bj.`1]) =
                     false)) Red_Ltk.Red_O.s_smap{2})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          smt(get_setE mem_set).
        smt().
      + if => //.
        + sp; seq 1 1 : (#pre /\ ={ks}). auto => />.
          if => //. auto => />. smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).
          + auto => /> &1 &2 *. do split; ~3,7,8,13: smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).
          auto => /> &1 &2 *. do split; ~1: smt(mem_set get_setE in_fsetU in_fset1 loggK expgK expM ComRing.mulrC).
    match Aborted_mod {2} ^match. auto => /#.
    auto => />.
  sp; match {1} => //.
  match {1} => //; if {1} => //; auto => />.
- move => &2 bad; proc; inline. 
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
  sp; if => //; match => //. 
  match; auto => />.
  if => //; if => //; auto => />.

+ proc; inline.
  admit.
- move => &2 bad; proc; inline. 
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
  sp; if => //; match => //. 
  match; auto => />.
  if => //; if => //; auto => />.
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




