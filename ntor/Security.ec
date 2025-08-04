require import AllCore FSet FMap Distr DProd List SplitRO NTOR Games.
(*   *) import GAKEc HROc.
require (*  *) Birthday SplitRO StdBigop StdOrder DiffieHellman.
(*   *) import StdBigop.Bigreal.BRA StdOrder.RealOrder DH.G DH.GP DH.FD DH.GP.ZModE.




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

module Counter (G : GAKE_out) : GAKE_out_i = {
  var cis, cm1, cm2 : int

  include G[h, set_cert, send_msg3, c_rev_skey, s_rev_skey, rev_ltkey, c_rev_ephkey, s_rev_ephkey, c_test, s_test]

  proc init_mem(b: bool) = {
    (cis, cm1, cm2) <- (0, 0, 0);
  }
  
  proc init_s(x) = {
    var m;
    cis <- cis + 1;
    m <@ G.init_s(x);
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
    ^if.^sk<$ ~ {sk <@ S.s();}
  ]

  proc send_msg1 [
    ^if.^match#None.^sk<$ ~ {sk <@ S.s();}
  ]

  proc send_msg2 [
    ^match#Some.^match#None.^sk<$ ~ {sk <@ S.s();}
  ]
}.

module (Red_Coll_real (A : A_GAKE) : BB.Adv) (S : BB.ASampler) = {
  proc a() = {
    var b';

    Red_Coll_O_AKE(S).init_mem(false);
    Counter(Red_Coll_O_AKE(S)).init_mem(false);
    b' <@ A(Counter(Red_Coll_O_AKE(S))).run();
  }
}.

module (Red_Coll_ideal (A : A_GAKE) : BB.Adv) (S : BB.ASampler) = {
  proc a() = {
    var b';

    Red_Coll_O_AKE(S).init_mem(true);
    Counter(Red_Coll_O_AKE(S)).init_mem(true);
    b' <@ A(Counter(Red_Coll_O_AKE(S))).run();
  }
}.

module E_GAKE_BB (A : A_GAKE) = {
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
  type from        <= pkey * pkey * s_id * pkey * pkey,
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
realize ofpairK by rewrite /topair /ofpair.
realize sample_spec by rewrite /ofpair dprodC dmap_comp //=.

module (Red_ROM (D : A_GAKE) : ROc.IdealAll.RO_Distinguisher) (O : ROc.IdealAll.RO) = {
  module AKE_O : GAKE_out = Game1 with {
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

module (Red_ROM2 (D : A_GAKE) (O1 : ROSc.I1.RO) : ROSc.I2.RO_Distinguisher) (O2 : ROSc.I2.RO) = {
  module AKE_O : GAKE_out = Game3 with {
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
      ^match#Some.^match#Pending.^ts<$ ~ {t_A <@ O1.get(x); O2.sample(x); key <- witness;}
      [^match#Some.^match#Pending.^if - ^key<-] -
    ]

    proc c_rev_skey [
      var ks : key
      var x : pkey * pkey * s_id * pkey * pkey
      ^match#Some.^match#Accepted.^if.^k<- ~ {x <- ((oget t'.`2).`1 ^ st'.`3, st'.`2 ^ st'.`3, st'.`1, g ^ st'.`3, (oget t'.`2).`1); ks <@ O2.get(x); k <- Some ks;}
    ]

    proc s_rev_skey [
      var ks : key
      var x : pkey * pkey * s_id * pkey * pkey
      ^match#Some.^match#Accepted.^if.^k<- ~ {x <- (t'.`1 ^ (oget st'.`3), t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1); ks <@ O2.get(x); k <- Some ks;}
    ]

    proc c_test [
      var ks2 : key
      ^if.^match#Some.^match#Accepted.^if.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
      ^if.^match#Some.^match#Accepted.^if.^if?^ks<$ + ^ {ks2 <@ O2.get(x);}
    ]

    proc s_test [
      var ks2 : key
      ^if.^match#Some.^match#Accepted.^if.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
      ^if.^match#Some.^match#Accepted.^if.^if?^ks<$ + ^ {ks2 <@ O2.get(x);}
    ]
  }

  proc distinguish(b) = {
    var b';
    AKE_O.init_mem(b);
    b' <@ D(AKE_O).run();
    return b';
  }
}.


(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GAKE {-GAKEb, -Game0, -Game1, -Game2, -Game3, -Game4, -ROc.IdealAll.RO, -RO, -FRO, -ROSc.I1.RO, -ROSc.I2.RO, -ROSc.I1.FRO, -ROSc.I2.FRO, -Red_Coll_real, -Red_Coll_ideal, -BB.Sample, -Red_ROM, -Red_ROM2 }.

declare axiom A_ll (G <: GAKE_out{-A}):
  islossless G.h =>
  islossless G.init_s =>
  islossless G.set_cert =>
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

declare axiom A_bounded_qs: forall (G <: GAKE_out{-A}), hoare[A(Counter(G)).run: Counter.cis = 0 /\ Counter.cm1 = 0 /\ Counter.cm2 = 0 ==> Counter.cis <= q_is /\ Counter.cm1 <= q_m1 /\ Counter.cm2 <= q_m2].



(* ------------------------------------------------------------------------------------------ *)
(* Step 0: Inlining everything. *)
lemma gake_game0 b &m :
  Pr[E_GAKE(GAKEb(NTOR_S(RO), NTOR_C(RO), RO), A).run(b) @ &m : res] = Pr[E_GAKE(Game0, A).run(b) @ &m : res].
proof. 
byequiv => //.
proc; inline.
call (: ={b0, servers, c_smap, s_smap, tested}(GAKEb, Game0) /\ RO.m{1} = Game0.hm{2}); try sim />.

- proc; inline; auto; if => //; auto => /#.

- proc; inline. 
  sp; if => //.
  sp; match = => // [|st]; 1:by auto.
  by match = => // st' pt' ir'; auto.

- proc; inline.
  sp; match = => // sk.
  match = => //.
  match Some {1} 4.
  + by auto=> /> _ _ _ _; exists (b{!m0}, sk, None).
  match Some {1} ^match=> //; 1: by auto=> /> /#.
  by auto => />.

- proc; inline; auto=> />.
  sp; match = => //; 1: auto. 
  by match = => //; 1: by auto. 
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 1: Remove collisions in ephemeral and long-term keys. Strategy with 2 * bound *)
lemma game0_game1 b &m: `| Pr[E_GAKE(Game0, A).run(b) @ &m : res] - Pr[E_GAKE(Game1, A).run(b) @ &m : res] | <= Pr[E_GAKE(Game0, A).run(b) @ &m : Game0.bad].
proof. admit. (*
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
  if => //.
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  by sp 2 2; if{2}; auto => />.
- move => &2 bad.
  proc; if; auto.
  rewrite dt_ll //=. smt().
- move => &1. 
  proc; if => //. 
  rcondf ^if; auto => />.
  by rewrite dt_ll.

- move => &2 bad.
  proc; auto => />.
- move => &1. 
  proc; auto => />. 

- proc.
  sp; if => //.
  sp; match = => //. 
  + seq 1 1: (#pre /\ ={sk}); 1: by auto.
    by sp 2 2; if{2}; auto => />.
  move => st. 
  match = => //.
  move => st' pr' ir'.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  + rewrite dt_ll. smt().
  by smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  + by rewrite dt_ll.
  by smt().

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
by case : (!br) => />. *)
qed.


(* ------------------------------------------------------------------------------------------ *)
(* Step 1b: Bound the bad event. *)
lemma game0_bad bit &m: Pr[E_GAKE(Game0, A).run(bit) @ &m : Game0.bad] <= ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt).
proof. admit. (*
case (bit) => real_ideal.

(* Proof for the ideal side *)
apply (StdOrder.RealOrder.ler_trans Pr[BB.Exp(BB.Sample, Red_Coll_ideal(A)).main() @ &m : ! uniq BB.Sample.l]); first last.
+ apply (BB.pr_collision_q2 (Red_Coll_ideal(A))).
  + move => S S_ll.
    islossless.
    apply (A_ll (Counter(Red_Coll_O_AKE(S)))); islossless.
    + match; 1: auto; islossless.
      match; auto.
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
  + by proc; inline; sp; if => //; auto => /#.
  + by proc; auto.
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
 /\ (forall sk pk, (pk, sk) \in Game0.kp_set{1} => sk \in BB.Sample.l{2})
) => //; try sim />.
+ proc; inline; sp 0 2; if => //; auto => />. 
  smt(mem_set in_fsetU1).
+ proc; inline; sp 2 4; if => //; auto.
  sp; match = => // [|st].
  + auto => />.
    smt(mem_set in_fsetU1).
  match = => // st' pt ir. 
  auto => />.
+ proc; inline; sp 2 4; match = => // [|st]; 1: auto.
  match = => // [|st']; 2: auto.
  auto => />.
  smt(mem_set in_fsetU1).
auto => />.
smt(in_fset0).

(* Proof for the real side *)
apply (StdOrder.RealOrder.ler_trans Pr[BB.Exp(BB.Sample, Red_Coll_real(A)).main() @ &m : ! uniq BB.Sample.l]); first last.
+ apply (BB.pr_collision_q2 (Red_Coll_real(A))).
  + move => S S_ll.
    islossless.
    apply (A_ll (Counter(Red_Coll_O_AKE(S)))); islossless.
    + match; 1: auto; islossless.
      match; auto.
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
  + by proc; inline; sp; if => //; auto => /#.
  + by proc; auto.
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
 /\ (forall kp, kp \in Game0.kp_set{1} => kp.`2 \in BB.Sample.l{2})
) => //; try sim />.
+ proc; inline; sp 0 2; if => //; auto => />. 
  smt(mem_set in_fsetU1).
+ proc; inline; sp 2 4; if => //; auto.
  sp; match = => // [|st].
  + auto => />.
    smt(mem_set in_fsetU1).
  match = => // st' pt ir. 
  auto => />.
+ proc; inline; sp 2 4; match = => // [|st]; 1: auto.
  match = => // [|st']; 2: auto.
  auto => />.
  smt(mem_set in_fsetU1).
auto => />.
smt(in_fset0). *)
qed.


(* ------------------------------------------------------------------------------------------ *)
(* Step 1: Remove collisions in ephemeral and long-term keys. Strategy with single birthday bound. *)
lemma game0_musplit bit &m: Pr[E_GAKE(Game0, A).run(bit) @ &m : res] = Pr[E_GAKE(Game0, A).run(bit) @ &m : res /\ Game0.bad] + Pr[E_GAKE(Game0, A).run(bit) @ &m : res /\ !Game0.bad]. 
proof. 
by rewrite Pr[mu_split Game0.bad].
qed.

lemma game0_res_bad bit &m: Pr[E_GAKE(Game0, A).run(bit) @ &m : res /\ Game0.bad] <= Pr[E_GAKE(Game0, A).run(bit) @ &m : Game0.bad].
proof.
+ byequiv (: _ ==> ={Game0.bad}) => //; sim.
qed. 

lemma game0_res_notbad bit &m: Pr[E_GAKE(Game0, A).run(bit) @ &m : res /\ !Game0.bad] <= Pr[E_GAKE(Game0, A).run(bit) @ &m : !Game0.bad].
proof.
byequiv (: _ ==> ={Game0.bad}) => //; sim.
qed. 



lemma game0_notbad_game1 bit &m: Pr[E_GAKE(Game0, A).run(bit) @ &m : res /\ !Game0.bad] = Pr[E_GAKE_BB(A).run(bit) @ &m : res].
proof. admit. (*
byequiv => //.
proc; inline.
call (: Game1.bad
      , ={b0, servers, c_smap, s_smap, tested, kp_set, hm, bad}(Game0, Game1)
      , ={bad}(Game0, Game1)) => //; try sim />; last first.

wp; skip => />.
move => rl rr al bl csl hml kpl ssl sl tl ar br csr hmr kpr ssr sr tr. 
case : (!br) => />. 

- exact A_ll.

- move => &2 bad; proc; auto => />. 
  by rewrite weight_dprod dkey_ll dtag_ll.
- move => &1; proc; auto.
  by rewrite weight_dprod dkey_ll dtag_ll.

- proc.
  if => //.
  seq 1 1: (#pre /\ ={sk}); 1: by auto.
  by sp 0 2; if{2}; auto => />.
- move => &2 bad.
  proc; if; auto.
  rewrite dt_ll //=. smt().
- move => &1. 
  proc; if => //. 
  rcondf ^if; auto => />.
  by rewrite dt_ll.

- move => &2 bad.
  proc; auto => />.
- move => &1. 
  proc; auto => />. 

- proc.
  sp; if => //.
  sp; match = => //. 
  + seq 1 1: (#pre /\ ={sk}); 1: by auto.
    by sp 0 2; if{2}; auto => />.
  move => st. 
  match = => //.
  move => st' pr' ir'.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  + rewrite dt_ll. smt().
  by smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  + by rewrite dt_ll.
  by smt().

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
  by rewrite dkey_ll. *)
qed.

lemma game0_game1_adv &m: `| Pr[E_GAKE(Game0, A).run(false) @ &m : res] - Pr[E_GAKE(Game0, A).run(true) @ &m : res] |
                       <= `| Pr[E_GAKE_BB(A).run(false) @ &m : res] - Pr[E_GAKE_BB(A).run(true) @ &m : res] | +  ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt).
proof. 
rewrite !(game0_musplit _).
apply (StdOrder.RealOrder.ler_trans 
        (`| Pr[E_GAKE(Game0, A).run(false) @ &m : res /\ !Game0.bad] - Pr[E_GAKE(Game0, A).run(true) @ &m : res /\ !Game0.bad]| 
          + `| Pr[E_GAKE(Game0, A).run(false) @ &m : res /\ Game0.bad] - Pr[E_GAKE(Game0, A).run(true) @ &m : res /\ Game0.bad]|)).
smt(StdOrder.RealOrder.ler_norm_add).
do rewrite -(game0_notbad_game1 _).
search (<=) (+).
rewrite StdOrder.RealOrder.ler_add2l.
search (<=).
apply (StdOrder.RealOrder.ler_trans
        (StdOrder.RealOrder.maxr 
            Pr[E_GAKE(Game0, A).run(false) @ &m : res /\ Game0.bad]
            Pr[E_GAKE(Game0, A).run(true) @ &m : res /\ Game0.bad])).
+ by rewrite StdOrder.RealOrder.ler_norm_maxr Pr[mu_ge0].
case (Pr[E_GAKE(Game0, A).run(false) @ &m : res /\ Game0.bad] <= Pr[E_GAKE(Game0, A).run(true) @ &m : res /\ Game0.bad]) => maxb.
search StdOrder.RealOrder.maxr.
+ rewrite StdOrder.RealOrder.ler_maxr => //.
  smt(game0_res_bad game0_bad).
rewrite StdOrder.RealOrder.ler_maxl => //.
+ smt().
smt(game0_res_bad game0_bad).
qed.


(* How to work with it from here? *)



(* ------------------------------------------------------------------------------------------ *)
(* Step 2: Splitting the random oracle. *)
local clone import DProd.ProdSampling with
  type t1 <- tag,
  type t2 <- key
proof *.

lemma game1_game2 bit &m: Pr[E_GAKE(Game1, A).run(bit) @ &m : res] =  Pr[E_GAKE(Game2, A).run(bit) @ &m : res].
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
smt(emptyE). *)
qed.



(* ------------------------------------------------------------------------------------------ *)
(* Step 3: Removing case of adversary guessing right tag. *)
lemma game2_game3 b &m: `| Pr[E_GAKE(Game2, A).run(b) @ &m : res] - Pr[E_GAKE(Game3, A).run(b) @ &m : res] | <= Pr[E_GAKE(Game2, A).run(b) @ &m : Game2.badt].
proof. admit. (*
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game3.badt => //; first last.
+ smt().
symmetry; proc; inline*.
call (: Game3.badt
      , ={b0, servers, c_smap, s_smap, tested, kp_set, hm, bad, h1m, h2m, hq, tq, badq, tags, badt}(Game2, Game3)
      , ={badt}(Game2, Game3)) => //; try sim />; last first.

auto => />.
move => rl rr al bl csl btl kpl h1ml h2ml hql kpsl ssl sl tgsl tl tql ar br csr btr kpr h1mr h2mr hqr kpsr ssr sr tgsr tr tqr. 
by case : (!btr) => />.

- exact A_ll.

- move => &2 bad; proc; auto => />. 
  by rewrite dkey_ll dtag_ll.
- move => &1; proc; auto.
  by rewrite dkey_ll dtag_ll.

- move => &2 bad.
  proc; if; auto.
  rewrite dt_ll //=.
- move => &1.
  proc; if => //.
  auto => />.
  by rewrite dt_ll.

- move => &2 bad.
  proc; auto => />.
- move => &1. 
  proc; auto => />. 

- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  + rewrite dt_ll. smt().
  by smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  + by rewrite dt_ll.
  by smt().

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
  by rewrite dkey_ll. *)
qed.



(* ------------------------------------------------------------------------------------------ *)
(* Step 3: Moving sampling of the shared key. *)

(* Clearing the key out of the state *)
local op s_clear_k (s : pr_st_server instance_state) =
match s with
| Pending _ _ _ => s
| Accepted st t k ir => Accepted st t witness ir
| Aborted _ _ _ => s
end.

local op c_clear_k (s : pr_st_client instance_state) =
match s with
| Pending _ _ _ => s
| Accepted st t k ir => Accepted st t witness ir
| Aborted _ _ _ => s
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

lemma game3_RO bit &m: Pr[E_GAKE(Game3, A).run(bit) @ &m : res] = Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(bit) @ &m : res].
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
          /\ (forall i st pt k ir, Game3.c_smap{1}.[i] = Some (Accepted st pt k ir)
                => (exists k', Red_ROM2.AKE_O.c_smap{2}.[i] = Some (Accepted st pt k' ir))
                   /\ ((oget pt.`2).`1 ^ st.`3, st.`2 ^ st.`3, st.`1, g ^ st.`3, (oget pt.`2).`1) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[((oget pt.`2).`1 ^ st.`3, st.`2 ^ st.`3, st.`1, g ^ st.`3, (oget pt.`2).`1)])
          /\ (forall i st pt k ir, Game3.s_smap{1}.[i] = Some (Accepted st pt k ir)
                => (exists k', Red_ROM2.AKE_O.s_smap{2}.[i] = Some (Accepted st pt k' ir))
                   /\ (pt.`1 ^ oget st.`3, pt.`1 ^ st.`2, st.`1, pt.`1, (oget pt.`2).`1) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[(pt.`1 ^ oget st.`3, pt.`1 ^ st.`2, st.`1, pt.`1, (oget pt.`2).`1)])
          /\ (forall x, x \in ROSc.I1.RO.m{2} <=> x \in ROSc.I2.RO.m{2})
          /\ (Game3.tested{1} <> None <=> Red_ROM2.AKE_O.tested{2} <> None)).

- proc; inline; auto => />; smt(mem_set get_setE).

- by sim />. 

- by sim />.

- proc; inline.
  sp; if => //.
  sp; match.
  + smt().
  + smt().
  + by auto=> />; smt(get_setE).
  move=> stl str; auto=> />.
  by smt(get_setE).

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
    by smt(mem_set get_setE).
  rcondf {1} ^if; 1: by auto => /#.
  rcondf {2} ^if; 1: by auto => /#.
  rcondf {2} ^if; 1: by auto => /#.
  auto => /> &1 &2.
  by smt(mem_set get_setE).

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
  seq  ^if{3} & -1   ^if{3} & -1: (#pre /\ ={t_A} /\ key{2} = witness /\ (x0{2} \in ROSc.I1.RO.m{2}) /\ key{1} = oget ROSc.I2.RO.m{2}.[m3{2}.`1 ^ sk_ce{2}, pk_b{2} ^ sk_ce{2}, b{2}, g ^ sk_ce{2}, m3{2}.`1]).
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
  by smt(get_setE).

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
  + auto => /> &1 &2 *.
    by smt(get_setE).
  auto => />.
  by smt(get_setE).

by auto => />; smt(map_empty emptyE). *)
qed.

lemma LRO_game4 bit &m: Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(bit) @ &m : res] = Pr[E_GAKE(Game4, A).run(bit) @ &m : res].
proof. admit. (*
byequiv => //.
proc*.
inline; wp.
call (: ={b0, hm, servers, c_smap, s_smap, tested, kp_set, bad, hq, tq, badq, tags, badt}(Red_ROM2.AKE_O, Game4) 
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

auto => />. *)
qed.

(* Step 5: Turn the indistinguishability of real/ideal into probability of the bad event happening *)
(*
op log : pkey -> pkey -> skey.
op root : skey -> pkey -> pkey.

axiom logC pk sk: log (pk ^ sk) pk = sk.
axiom rootC pk sk: root sk (pk ^ sk) = pk.

axiom sk_uq pk sk sk': (pk, sk) \in dkp /\ (pk, sk') \in dkp => sk = sk'.*)


op inv_Game4 (tested : int option, 
tq : (pkey * pkey * s_id * pkey * pkey) option, 
badq : bool, 
kp_set : ((pkey * skey)) fset, 
ssm : (s_id * int, pr_st_server instance_state) fmap, 
hq : (pkey * pkey * s_id * pkey * pkey) fset, 
csm : (int, pr_st_client instance_state) fmap,
h1m : (pkey * pkey * s_id * pkey * pkey, tag) fmap, 
h2m : (pkey * pkey * s_id * pkey * pkey, key) fmap, 
tags : (pkey * pkey * s_id * pkey * pkey, tag) fmap) = 
       (tested = None <=> tq = None)
        /\ (badq <=> (tq <> None /\ oget tq \in hq))
        /\ (forall x y sk b, tq = Some (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x sk), b, g ^ x, g ^ y) 
                => (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x sk), b, g ^ x, g ^ y) \in h2m 
                         /\ ((exists i pk_s sk_ce tag key ir, csm.[i] = Some (Accepted (b, pk_s, sk_ce) (g ^ x, Some (g ^ y, tag)) key ir)
                     /\ get_ir_test (oget csm.[i]))
                  \/ (exists i sk_s sk_se tag key ir, ssm.[i] = Some (Accepted (b, sk_s, Some sk_se) (g ^ x, Some (g ^ y, tag)) key ir)
                     /\ get_ir_test (oget ssm.[i]))))
        /\ (forall i st t k ir, csm.[i] = Some (Accepted st t k ir) => tested = None => !ir.`3)
        /\ (forall i st t k ir, ssm.[i] = Some (Accepted st t k ir) => tested = None => !ir.`3)
        /\ (forall kp, kp \in kp_set => kp.`2 \in dt /\ (kp.`1 = g ^ kp.`2))
        /\ (forall i i' m1 m2 m2', csm.[i] <> None /\ get_trace (oget csm.[i]) = Some (m1, m2)
                => csm.[i'] <> None /\ get_trace (oget csm.[i']) = Some (m1, m2')
                => i = i')
        /\ (forall i tr pk, csm.[i] <> None 
                => get_trace (oget csm.[i]) = Some (pk, tr) 
                => exists sk, (pk, sk) \in kp_set)
        /\ (forall i i' m1 m2 tag m1' tag', ssm.[i] <> None /\ get_trace (oget ssm.[i]) = Some (m1, Some (m2, tag))
                => ssm.[i'] <> None /\ get_trace (oget ssm.[i']) = Some (m1', Some (m2, tag'))
                => i = i')
        /\ (forall i tr pk tag, ssm.[i] <> None 
                => get_trace (oget ssm.[i]) = Some (tr, Some (pk, tag)) 
                => exists sk, (pk, sk) \in kp_set)
        /\ (forall i st pt ir, csm.[i] = Some (Pending st pt ir)
                => (pt = g ^ st.`3) /\ !ir.`3)
        /\ (forall i st t k ir, csm.[i] = Some (Accepted st t k ir)
                => (t.`1 = g ^ st.`3) /\ (exists pk tag, (t.`2 = Some (pk, tag))))
        /\ (forall i st t k ir, ssm.[i] = Some (Accepted st t k ir)
                => ((oget t.`2).`1 = g ^ oget st.`3) /\ (exists sk, st.`3 = Some sk) /\ (exists pk tag, (t.`2 = Some (pk, tag))))
        /\ (forall x y sk b, (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x sk), b, g ^ x, g ^ y) \in h2m
                => (exists i pk_s sk_ce tag key ir, csm.[i] = Some (Accepted (b, pk_s, sk_ce)
                                  (g ^ x, Some (g ^ y, tag)) key ir)
                     /\ (get_ir_sess (oget csm.[i]) \/ get_ir_test (oget csm.[i])))
                  \/ (exists i sk_s sk_se tag key ir, ssm.[i] = Some (Accepted (b, sk_s, Some sk_se)
                                  (g ^ x, Some (g ^ y, tag)) key ir)
                     /\ (get_ir_sess (oget ssm.[i]) \/ get_ir_test (oget ssm.[i])))
                  \/ (g ^ (ZModE.( * ) x y), g ^ (ZModE.( * ) x sk), b, g ^ x, g ^ y) \in hq)
        /\ (forall i st t k ir, csm.[i] = Some (Accepted st t k ir)
                => (exists j st' k' ir', ssm.[j] = Some (Accepted st' t k' ir')))
        /\ (forall x, x \in tags
                => x \in h1m /\ oget tags.[x] = oget h1m.[x] /\ (exists i st k ir, ssm.[i] = Some (Accepted st (x.`4, Some (x.`5, oget tags.[x])) k ir))).



lemma interestingbit &m: `|Pr[E_GAKE(Game4, A).run(false) @ &m : res] - Pr[E_GAKE(Game4, A).run(true) @ &m : res]| <= Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game4.badq => //; first last.
+ smt().
symmetry; proc; inline.
wp.
call (: Game4.badq
      , ={servers, c_smap, s_smap, tested, kp_set, hm, bad, h1m, hq, tq, badq, tags, badt}(Game4, Game4)
        /\ (Game4.tq{1} = None => ={Game4.h2m})
        /\ (forall x, Game4.tq{1} = Some x => eq_except (pred1 x) Game4.h2m{1} Game4.h2m{2})
        /\ Game4.b0{1} = false /\ Game4.b0{2} = true
        /\ (inv_Game4 Game4.tested Game4.tq Game4.badq Game4.kp_set Game4.s_smap Game4.hq Game4.c_smap Game4.h1m Game4.h2m Game4.tags){2}
        /\ (forall x, x \in Game4.h2m{1} <=> x \in Game4.h2m{2})
      , ={badq}(Game4, Game4)) => //; last first.

- auto => />.
split; 1: by smt(emptyE in_fset0).
move => ntc nts ninkps injc pkins injs trs pc acc acs inv acas tgas rl rr al bl bql csl hql kpl ssl sl tl tql h1ml h2ml btl tgsl ar br bqr csr hqr kpr ssr sr tr tqr h1mr h2mr btr tgsr. 
by case : (!bqr) => />. 

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
  if => //.
  auto => /> &1 &2 *.
  smt(in_fsetU1).
- move => &2 badq.
  proc; if; auto.
  rewrite dt_ll //=.
- move => &1. 
  proc; if => //.
  auto => />. 
  by rewrite dt_ll.

- sim />.
- move => &2 badq.
  proc; auto => />.
- move => &1. 
  proc; auto => />.
 
- proc; inline.
  sp; if => //.
  sp; match = => // [|st].
  + auto => /> &1 &2 ? _ ? ? ? ? ? inv4 ? ? ? ? inv ? ? ? inv3 inv5 inv2 inv6 inv7 ? ? sk *.
    split; 1: by smt().
    split.
    + move => x0 y0 sk0 b0 tqeq.
      have := inv4 x0 y0 sk0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] pk_s sk_ce t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    split; 1: by smt(get_setE).
    split; 1: by smt(in_fsetU1).
    split.    
    + move => // i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m10 m2 m2' [] m10eq m2eq trs.
        have := inv i' None (g ^ sk).
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
    split.
    + move => x0 y0 sk0 b0 x0in.
    have := inv2 x0 y0 sk0 b0 x0in.
    move => [H1|[H2|H3]].
    + left.
      move : H1 => [i'] pk_s sk_ce t' k' ir' H1.
      exists i'. 
      smt(get_setE).
    + smt().
    by smt().
    smt(get_setE).
  match = => // st' pt ir.
  auto => /> &1 &2 ? ? ? ? ? ? ? inv4 ? ? _ ? inv ? ? ? ? ? inv5 inv2 inv3 *.
  split; 1: by smt().
  split. 
  move => x0 y0 sk0 b0 tqeq.
  have := inv4 x0 y0 sk0 b0 tqeq.
  move => [H1] [H2|H3]. 
  + split; 1: by smt(mem_set).
    left.
    move : H2 => [i'] pk_s sk_ce t k ir'' H2.
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
      by smt().
    case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite i'eq get_set_sameE get_set_neqE //=.
    by smt().
  split; 1: by smt(get_setE in_fsetU1).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split. 
  + move => x0 y0 sk0 b0 x0in.
  have := inv5 x0 y0 sk0 b0 x0in.
  move => [H1|[H2|H3]].
  + left.
    move : H1 => [i'] pk_s sk_ce t' k' ir' H1.
    exists i'. 
    smt(get_setE).
  + smt().
  by smt().
  smt(get_setE).
- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  + rewrite dt_ll. smt().
  by smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  + by rewrite dt_ll.
  by smt().
  
- proc; inline.
  sp; match = => // sk_s.
  match = => //.
  seq 1 1: (#pre /\ ={sk} /\ sk{2} \in dt); 1: by auto=> />.
  sp 2 2; if => //.
  sp; seq 1 1: (#pre /\ ={ts}); 1: by auto=> />.
  if => //.
  + auto => /> &1 &2 kps ? ? _ ? _ ? ? ? c1 ? inv5 ? ? ? ? ? ? inv ? inv2 ? inv6 inv3 inv4 *.
    split; 1: by smt(get_setE in_fsetU1).
    split. 
    + move => x0 y0 sk0 b0 tqeq.
      have := inv5 x0 y0 sk0 b0 tqeq.
      move => [] H1 [H2|H3].
      + smt().
      split; 1: by smt().
      move : H3 => [i'] sk_s' sk_se t k ir H3.
      right. exists i'.
      by smt(get_setE).
    split; 1: by smt(get_setE).
    split; 1: by smt(in_fsetU1).
    split; 1: by smt(get_setE in_fsetU1).
    split. 
    + move => // i0 i'.
      case (i0 = (b, j){2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_sameE get_set_neqE //=.
        move => m1 m20 tag m1' tag' stnn trs.
        have := inv i' m2{2} kp{2}.`1 ts{2}.
        by smt(pow_bij).
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => stnn.
      rewrite i'eq !get_set_sameE //=.
      by smt(pow_bij).
    split; 1: by smt(get_setE in_fsetU1).
    split; 1: by smt(get_setE).
    split.
    + move => x0 y0 sk0 b0 x0in.
      have := inv6 x0 y0 sk0 b0 x0in.
      move => [H1|[H2|H3]].
      + smt().
      + right. left.
        move : H2 => [i'] sk_s' sk_se t k ir H2.
        exists i'. 
        smt(get_setE).
      by smt().
    split. clear inv5 inv6. smt(get_setE).
    move => x0.
    case (x0 = (m2{2} ^ sk{2}, m2{2} ^ sk_s, b{2}, m2{2}, (g ^ sk{2}))) => x0eq; rewrite get_setE mem_set x0eq //=.
    + do rewrite get_set_sameE.
      split; 1: by smt(mem_set).
      split; 1: by done. 
      exists (b, j){2} (b{2}, sk_s, Some sk{2}) witness (false, false, false).
      smt(mem_set get_setE).
    rewrite get_set_neqE //=.
    move => x0in.
    split; 1: by smt(get_setE).
    split; 1: by smt(get_setE).
    have:= inv4 x0 x0in.
    move => [H1] [H2] [i st k ir] H3.
    exists i st k ir.
    case ((b,j){2} = i) => ieq; 1: by smt().
    smt(get_set_neqE).
  auto => /> &1 &2 kps ? ? _ ? _ ? ? ? c1 ? inv5 ? ? ? ? ? ? inv2 ? ? ? inv inv3 inv4*.
  split; 1: by smt(get_setE in_fsetU1).
  split. 
  + move => x0 y0 sk0 b0 tqeq.
    have := inv5 x0 y0 sk0 b0 tqeq.
    move => [] H1 [H2|H3].
    + smt().
    split; 1: by smt().
    move : H3 => [i'] sk_s' sk_se t k ir H3.
    right. exists i'.
    by smt(get_setE).
  split; 1: by smt(get_setE).
  split. smt(in_fsetU1).
  split; 1: by smt(get_setE in_fsetU1).
  split.
  + move => // i0 i'.
    case (i0 = (b, j){2}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      move => m1 m20 tag m1' tag' stnn trs.
      have := inv2 i' m2{2} kp{2}.`1 ts{2}.
      by smt(pow_bij).
    case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => stnn.
    rewrite i'eq !get_set_sameE //=.
    by smt(pow_bij).
  split; 1: by smt(get_setE in_fsetU1).
  split; 1: by smt(get_setE).
  split.
  + move => x0 y0 sk0 b0 x0in.
    have := inv x0 y0 sk0 b0 x0in.
    move => [H1|[H2|H3]].
    + smt().
    + right. left.
      move : H2 => [i'] sk_s' sk_se t k ir H2.
      exists i'. 
      smt(get_setE).
    by smt().
  split. clear inv inv5. smt(get_setE).
  move => x0.
  case (x0 = (m2{2} ^ sk{2}, m2{2} ^ sk_s, b{2}, m2{2}, (g ^ sk{2}))) => x0eq; rewrite get_setE mem_set x0eq //=.
  + split; 1: by smt(get_setE).
    exists (b,j){2} (b{2}, sk_s, Some sk{2}) witness (false, false, false).
    smt(get_setE).
  move => x0in.
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  have:= inv4 x0 x0in.
  move => [H1] [H2] [i st k ir] H3.
  exists i st k ir.
  case ((b,j){2} = i) => ieq; 1: by smt().
  smt(get_set_neqE).
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
  + rcondf{1} ^if. auto => /#.
    rcondf{2} ^if. auto => /#.
    auto => /> &1 &2.
    smt(get_setE mem_set).
  sp ^if & -1 ^if & -1; if => //. if => //.
  + auto => /> &1 &2 ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *.
    split; 1: by smt(get_setE).
    split. 
    + move => x0 y0 sk0 b0 tqeq.
      have := inv2 x0 y0 sk0 b0 tqeq.
      move => [H1] [H2|H3]. 
      + split; 1: by smt(mem_set).
        left.
        move : H2 => [i'] pk_s sk_ce t k ir'' H2.
        exists i'. 
        by smt(get_setE).     
      smt(mem_set).
    split. smt(get_setE).
    split. smt(get_setE). 
    split. smt(get_setE). 
    split. smt(get_setE).
    split. smt(get_setE).
    split. 
    + move => x0 y0 sk0 b0 x0in.
      have := inv5 x0 y0 sk0 b0 x0in.
      move => [H1|[H2|H3]].
      + left.
        move : H1 => [i'] pk_s sk_ce t' k' ir' H1.
        exists i'. 
        smt(get_setE).
      + smt().
      by smt().
    move => i0 st0 t0 k0 ir0.
    case (i0 = i{2}) => [->|]; 2: by smt(get_set_neqE).
    have:= inv3 (m3{2}.`1 ^ sk_ce{2}, pk_b{2} ^ sk_ce{2}, b{2}, g ^ sk_ce{2}, m3{2}.`1).
    have->: (m3{2}.`1 ^ sk_ce{2}, pk_b{2} ^ sk_ce{2}, b{2}, g ^ sk_ce{2}, m3{2}.`1) \in Game4.tags{2} by smt().
    simplify. 
    move => [H1] [H2] [j st'' k'' ir''] H3 H4.
    exists j st'' k'' ir''.
    have->: (t0 = (g ^ sk_ce{2}, Some (m3{2}.`1, oget Game4.tags{2}.[m3{2}.`1 ^ sk_ce{2}, pk_b{2} ^ sk_ce{2}, b{2}, g ^ sk_ce{2}, m3{2}.`1]))).
    + have->: (t0 = (g ^ sk_ce{2}, Some m3{2})) by smt(get_setE).
      do congr. smt(get_setE).
    by smt().
  auto => /> &1 &2 ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? inv4 ? ? ? ? inv5 inv inv3 *.
  split; 1: by smt(get_setE).
  split.
  + move => x0 y0 sk0 b0 tqeq.
    have := inv2 x0 y0 sk0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] pk_s sk_ce t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set).
  split. smt(get_setE).
  split. smt(get_setE). 
  split. smt(get_setE). 
  split. smt(get_setE).
  split. smt(get_setE).
  split. 
  + move => x0 y0 sk0 b0 x0in.
    have := inv5 x0 y0 sk0 b0 x0in.
    move => [H1|[H2|H3]].
    + left.
      move : H1 => [i'] pk_s sk_ce t' k' ir' H1.
      exists i'. 
      smt(get_setE).
    + smt().
    by smt().
  by smt(get_setE mem_set).
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
      + move => x0 y0 sk0 b0 tqeq.
        have := inv2 x0 y0 sk0 b0 tqeq.
        move => [H1] [H2|H3]. 
        + split; 1: by smt(mem_set).
          left.
          move : H2 => [i'] pk_s sk_ce t k ir'' H2.
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
      split.
      + move => x0 y0 sk0 b0 x0in.
        case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) 
               = ((oget t'.`2).`1 ^ st'.`3, st'.`2 ^ st'.`3, st'.`1, g ^ st'.`3, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
        + left.
          exists i{2} st'.`2 st'.`3 (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
          smt(get_setE).
        have := inv x0 y0 sk0 b0.
        have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set). 
        move => [H1|H2].
        + left. 
          move : H1 => [i'] pk_s sk_ce t k ir H1.
          exists i'. 
          smt(get_setE).
        by smt().
      by smt(get_setE).
    by smt(get_setE mem_set).
(************ case that the handle was in h2m ************)
  auto => /> &1 &2 stc ? ? ? ? ? ? inv2 ? ? ? inv5 ? inv3 ? ? ? ? inv inv4 fresh *.
  split.
  + case (Game4.tested{2} <> None) => test; 2: by smt().
    case (Game4.tq{2} = Some ((oget t'.`2).`1 ^ st'.`3, st'.`2 ^ st'.`3, st'.`1, g ^ st'.`3, (oget t'.`2).`1)); 2: by smt().
    have : ((oget t'.`2).`1 ^ st'.`3, st'.`2 ^ st'.`3, st'.`1, g ^ st'.`3, (oget t'.`2).`1) = (g ^ (st'.`3 * loge (oget t'.`2).`1), g ^ (st'.`3 * loge st'.`2), st'.`1, g ^ st'.`3, g ^ loge (oget t'.`2).`1). 
    + congr.
      + by rewrite ComRing.mulrC expM expgK. 
      + by rewrite ComRing.mulrC expM expgK.
      by rewrite expgK.
    move => eq. rewrite eq.
    move => tqeq2.
    have := inv2 st'.`3 (loge (oget t'.`2).`1) (loge st'.`2) st'.`1 tqeq2.
    rewrite //= some_oget //=; 1: smt().
    move => [] tqin [[i0 pk_s sk_ce t k ir [H1 H2]]|[i0 sk_s sk_se t k ir [H1 H2]]].
    + have : get_trace (oget Game4.c_smap{2}.[i0]) = get_trace (oget Game4.c_smap{2}.[i{2}]); smt().
    have : untested_partner_c t' Game4.s_smap{2} = Some false.
    + rewrite /untested_partner_c.
      have->: get_partners_c t' Game4.s_smap{2} = fset1 i0.
      + rewrite /get_partners_c.
        apply in_eq_fset1. 
        move => x0.
        rewrite mem_fdom mem_filter /=.
        split. 
        + move => [x0in trx0]. 
          apply (inv3 x0 i0 t'.`1 (oget t'.`2).`1 (oget t'.`2).`2 (g ^ st'.`3) t); smt().
        move => ->.
        split; 1: by smt().
        rewrite H1 /get_trace //=.
        have->: (g ^ st'.`3 = t'.`1). smt().
        have->: t = (oget t'.`2).`2.
        + have := inv4 i{2} st' t' k' ir' stc.
          move => [j st'' k'' ir''].
          have := inv3 i0 j (g ^ st'.`3) (oget t'.`2).`1  t t'.`1 (oget t'.`2).`2. smt().
        smt().
      have->: get_untested_partners_c t' Game4.s_smap{2} = fset0.
      + rewrite /get_untested_partners_c.
        apply in_eq_fset0.
        move => x0.
        rewrite mem_fdom mem_filter !negb_and /=. 
        case (x0 = i0) => x0eq; 1: by smt().
        case (get_trace (oget Game4.s_smap{2}.[x0]) = Some t'); 2: by smt().
        have:= inv3 x0 i0 t'.`1 (oget t'.`2).`1 (oget t'.`2).`2 (g ^ st'.`3) t.
        smt().
      smt(fcard1 fcards0).
    smt().
  split; 1: by smt().
  split.
  + move => x0 y0 sk0 b0 tqeq.
    have := inv2 x0 y0 sk0 b0 tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] pk_s sk_ce t k ir'' H2.
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
  split.
  + move => x0 y0 sk0 b0 x0in.
    case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) 
           = ((oget t'.`2).`1 ^ st'.`3, st'.`2 ^ st'.`3, st'.`1, g ^ st'.`3, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
    + left.
      exists i{2} st'.`2 st'.`3 (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
      smt(get_setE).
    have := inv x0 y0 sk0 b0.
    have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set). 
    move => [H1|H2].
    + left. 
      move : H1 => [i'] pk_s sk_ce t k ir H1.
      exists i'. 
      smt(get_setE).
    by smt().     
  smt(get_setE).
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
  + auto => /> &1 &2 ? ? ? ? ? c1 c2 inv2 c3 c4 _ ? ? ? ? ? ? ? inv inv3 inv4 *.
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split.
    + split; 1: by smt().
      split. 
      + move => x0 y0 sk0 b0 tqeq.
        have := inv2 x0 y0 sk0 b0 tqeq.
        move => [H1] [H2|H3]; 1: smt(mem_set).
        split; 1: by smt(mem_set).
        right.
        move : H3 => [i'] sk_s sk_se t k ir'' H3.
        exists i' sk_s sk_se t k ir''.
        case (i' = (b, j){2}) => i'eq; smt(get_setE).
      split; 1: by smt(get_setE).
      split. clear c1 c2 c3 c4 inv inv2 inv3 inv4.
      + move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          by rewrite get_set_neqE /#.
        case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
        rewrite get_set_neqE //=.
        move => m1 m2 tag m1' tag' stnn.
        by rewrite i'eq !get_set_sameE /#.
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      split. 
      + move => x0 y0 sk0 b0 x0in.
        case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) 
               = (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
        + right. left.
          exists (b, j){2} st'.`2 (oget st'.`3) (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
          smt(get_setE).
        have := inv x0 y0 sk0 b0.
        have->: (g ^ (x0 * y0), g ^ (x0 * sk0), b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set). 
        simplify.
        move => [H1|[H2|H3]].
        + by smt().
        + right; left. 
          move : H2 => [i'] sk_s' sk_se t k ir H2.
          exists i'. 
          smt(get_setE).
        by smt().
      split.
      + move => i st0 t k0 ir H1. 
        have:= inv3 i st0 t k0 ir H1.
        move => [j'] st'' k'' ir'' H2.
        exists j'. 
        by smt(get_setE).
      move => x0 x0in. 
      have:= inv4 x0 x0in.
      move => [H1] [H2] [j'] st'' k'' ir'' H3.
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      exists j'. 
      by smt(get_setE).
    by smt(get_setE mem_set).
(************ case that the handle was in h2m ************)
  auto => /> &1 &2 stbj ? ? ? ? ? ? inv2 ? ? _ inv3 ? inv5 ? ? ? ? inv inv4 inv6 *.
  split.
  + case (Game4.tested{2} <> None) => test; 2: by smt().
    case (Game4.tq{2} = Some (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1)); 2: by smt().
    have : (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1) = (g ^ (loge t'.`1 * (oget st'.`3)), g ^ (loge t'.`1 * st'.`2), st'.`1, g ^ (loge t'.`1), g ^ oget st'.`3). 
    + congr.
      + by rewrite expM expgK. 
      + by rewrite expM expgK.
      + by rewrite expgK.
      smt().
    move => eq. rewrite eq.
    move => tqeq2.
    have := inv2 (loge t'.`1) (oget st'.`3) st'.`2 st'.`1 tqeq2.
    rewrite //= some_oget //=; 1: smt().
    move => [] tqin [[i0 pk_s sk_ce t k ir [H1 H2]]|[i0 sk_s sk_se t k ir [H1 H2]]]. 
    + have : untested_partner_s t' Game4.c_smap{2} = Some false.
      + rewrite /untested_partner_s.
        have->: get_partners_s t' Game4.c_smap{2} = fset1 i0.
        + rewrite /get_partners_s.
          apply in_eq_fset1. 
          move => x0.
          rewrite mem_fdom mem_filter /=.
          split. 
          + move => [x0in trx0].
            apply (inv3 x0 i0 t'.`1 t'.`2 (Some ((oget t'.`2).`1, t))); smt().
          move => ->.
          split; 1: by smt().
          rewrite H1 /get_trace //=.
          have->: (g ^ loge t'.`1 = t'.`1). by rewrite expgK.
          have->: t = (oget t'.`2).`2.
          + have := inv4 i0 (st'.`1, pk_s, sk_ce) (g ^ loge t'.`1, Some (g ^ oget st'.`3, t)) k ir H1.
            move => [i st'' k'' ir''] H3.
            have := inv5 (b,j){2} i t'.`1 (oget t'.`2).`1 (oget t'.`2).`2 t'.`1 t.
            move => H4.
            have : (b,j){2} = i by smt().
            move => ieq.
            have : get_trace (oget Game4.s_smap{2}.[i]) = get_trace (oget Game4.s_smap{2}.[(b, j){2}]) by smt().
            by smt().  
          by smt().
        have->: get_untested_partners_s t' Game4.c_smap{2} = fset0.
        + rewrite /get_untested_partners_s.
          apply in_eq_fset0.
          move => x0.
          rewrite mem_fdom mem_filter !negb_and /=. 
          case (x0 = i0) => x0eq; 1: by smt().
          case (get_trace (oget Game4.c_smap{2}.[x0]) = Some t'); 2: by smt().
          have:= (inv3 x0 i0 t'.`1 t'.`2 (Some ((oget t'.`2).`1, t))).
          by smt().
        by smt(fcard1 fcards0).
      by smt().
    have : (get_ir_test (oget Game4.s_smap{2}.[b{2}, j{2}])).
    + have := inv5 (b,j){2} i0 t'.`1 (oget t'.`2).`1 (oget t'.`2).`2 t'.`1 t.
      move => H4.
      have->: (b,j){2} = i0 by smt().
      by smt().
    by smt().
  split; 1: by smt().
  split.
  + move => x0 y0 sk0 b0 tqeq.
    have := inv2 x0 y0 sk0 b0 tqeq.
    move => [H1] [H2|H3]; 1: smt(mem_set).
    split. smt(mem_set).
    right.
    move : H3 => [i'] sk_s sk_se t k ir'' H3.
    exists i' sk_s sk_se t k ir''. 
    have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    case (i' = (b,j){2}); smt(get_setE).
  split; 1: by smt(get_setE).
  split.
  + move => // i0 i'.
    case (i0 = (b, j){2}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
      smt().
    case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => m1 m2 tag m1' tag' stnn.
    rewrite i'eq !get_set_sameE.
    have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    smt().
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split.
  + move => x0 y0 sk0 b0 x0in.
    case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) 
           = (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
    + right. left.
      exists (b, j){2} st'.`2 (oget st'.`3) (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
      smt(get_setE).
    have := inv x0 y0 sk0 b0.
    have->: (g ^ (x0 * y0), g ^ (x0 * sk0), b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set). 
    simplify.
    move => [H1|[H2|H3]].
    + by smt().
    + right; left. 
      move : H2 => [i'] sk_s' sk_se t k ir H2.
      exists i' sk_s' sk_se t k ir. 
      have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
      case (i' = (b,j){2}); smt(get_setE).
    by smt().
  split.
  + move => i st0 t k0 ir H1. 
    have:= inv4 i st0 t k0 ir H1.
    move => [j'] st'' k'' ir'' H2.
    exists j'. 
    by smt(get_setE).
  move => x0 H1. 
  have:= inv6 x0 H1.
  move => [H2] [H3] [j'] st'' k'' ir'' H4.
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  exists j'. 
  by smt(get_setE).
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

- sim />.
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
    + move => x0 y0 sk0 b0 tqeq.
      have := inv2 x0 y0 sk0 b0 tqeq.
      move => [H1] [H2|H3]. 
      split. smt().
      left.
      move : H2 => [i'] pk_s sk_ce t k ir' H2.
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
    split. 
    + move => x0 y0 sk0 b0 x0in.
      have := inv x0 y0 sk0 b0.
      rewrite x0in //=.
      move => [H1|H2].
      + left.
        move : H1 => [i'] sk_s' sk_se t k ir' H1.
        exists i'. 
        by smt(get_setE).
      by smt().
    smt(get_setE).
  auto => /> &1 &2 ? ? ? ? ? ? ? inv2 ? ? _ ? ? ? ? ? ? ? inv *. 
  split; 1: by smt(get_setE).
  split.
  + move => x0 y0 sk0 b0 tqeq.
    have := inv2 x0 y0 sk0 b0 tqeq.
    move => [H1] [H2|H3].
    split. smt().
    left.
    move : H2 => [i'] pk_s sk_ce t' k' ir' H2.
    exists i'. 
    by smt(get_setE).     
    smt(). 
  split; 1: by smt(get_setE).
  split. clear inv inv2. by smt(get_setE).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split. smt(get_setE).
  split.
  + move => x0 y0 sk0 b0 x0in.
    have := inv x0 y0 sk0 b0.
    rewrite x0in //=.
    move => [H1|H2].
    + left. 
      move : H1 => [i'] sk_s' sk_se t' k' ir' H1.
      exists i'.
      by smt(get_setE).
    by smt().
  by smt(get_setE).
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
  sp; match = => // st.
  match = => // st' t' k' ir'.
  auto => /> &1 &2 ? ? ? ? ? c1 ? inv2 c2 c3 _ ? ? inv5 ? ? ? ? inv inv3 inv4 *.
  split; 1: by smt(get_setE).
  split. 
  + move => x0 y0 sk0 b0 tqeq.
    have := inv2 x0 y0 sk0 b0 tqeq.
    move => [H1] [H2|H3]. 
    smt().
    split. smt().
    right.
    move : H3 => [i'] sk_s sk_se t k ir'' H3.
    case ((b, j){2} = i') => i'eq.
    + have : Game4.s_smap{2}.[b{2}, j{2}] = Game4.s_smap{2}.[i']; 1: by smt().
      move => H2.
      exists i' sk_s sk_se t k' (true, ir'.`2, ir'.`3).
      by smt(get_setE).
    exists i' sk_s sk_se t k ir''.
    by smt(get_setE).
  split; 1: by smt(get_setE).
  split.
  + move => // i0 i'.
    case (i0 = (b, j){2}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      have : get_trace (oget (Some (Accepted st' t' k' (true, ir'.`2, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
      by smt().
    case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => m1 m2 tag m1' tag' stnn.
    rewrite i'eq !get_set_sameE.
    have : get_trace (oget (Some (Accepted st' t' k' (true, ir'.`2, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    by smt().
  split. 
  + have : get_trace (oget (Some (Accepted st' t' k' (true, ir'.`2, ir'.`3)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    by smt(get_setE). 
  split; 1: by smt(get_setE).
  split. 
  + move => x0 y0 sk0 b0 x0in.
    have := inv x0 y0 sk0 b0.
    rewrite x0in //=.
    move => [H1|[H2|H3]].
    + by smt().
    + right; left.
      move : H2 => [i'] sk_s' sk_se t k'' ir'' H2.
      case ((b, j){2} = i') => i'eq.
        have : Game4.s_smap{2}.[b{2}, j{2}] = Game4.s_smap{2}.[i']; 1: by smt().
        move => H1.
        exists i' sk_s' sk_se t k' (true, ir'.`2, ir'.`3).
        by smt(get_setE).
      exists i' sk_s' sk_se t k'' ir''.
      by smt(get_setE). 
    by smt().
  split.
  + move => i st0 t k0 ir H1. 
    have:= inv3 i st0 t k0 ir H1.
    move => [j'] st'' k'' ir'' H2.
    exists j'. 
    by smt(get_setE).
  move => x0 H1. 
  have:= inv4 x0 H1.
  move => [H2] [H3] [j'] st'' k'' ir'' H4.
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  exists j'. 
  by smt(get_setE).
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
    auto => /> &1 &2 badq tq ? ? ? ? ? ? ? inv2 ? ? _ ? ? ? ? ? ? ? inv *.
    split. smt(get_setE mem_set).
    split. smt(get_setE mem_set).
    split. 
    + split.
      + move => x0 y0 sk0 eq1 eq2 eq3 eq4.
        split. smt(mem_set).
        left.
        exists i{2} st'.`2 st'.`3 (oget t'.`2).`2 k' (ir'.`1, ir'.`2, true).
        by smt(get_setE).
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      split.
      + move => x0 y0 sk0 b0 x0in.
        case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) = ((oget t'.`2).`1 ^ st'.`3, st'.`2 ^ st'.`3, st'.`1, g ^ st'.`3, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
        + left.
          exists i{2} st'.`2 st'.`3 (oget t'.`2).`2 k' (ir'.`1, ir'.`2, true).
          smt(get_setE).
        have := inv x0 y0 sk0 b0.
        have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set).
        simplify.
        move => [H1|H2].
        + left.
          move : H1 => [i'] pk_s sk_ce t k'' ir'' H1.
          exists i'.
          smt(get_setE).
        by smt().
      by smt(get_setE).
    by smt(get_setE mem_set).
  rcondf {1} ^if. auto => /#.
  rcondf {2} ^if. auto => /#.
  auto => /> &1 &2 ? ? stc ? ? ? ? ? ? ? ? ? _ inv2 ? inv4 ? ? ? ? inv inv3 ? ? fresh ? x2in *.
  suff //=:false.
  have := inv st'.`3 (loge (oget t'.`2).`1) (loge st'.`2) st'.`1.
  have->: (g ^ (st'.`3 * loge (oget t'.`2).`1), g ^ (st'.`3 * loge st'.`2), st'.`1, g ^ st'.`3, g ^ loge (oget t'.`2).`1) = ((oget t'.`2).`1 ^ st'.`3, st'.`2 ^ st'.`3, st'.`1, g ^ st'.`3, (oget t'.`2).`1). 
  congr.
  + by rewrite ComRing.mulrC expM expgK.
  + by rewrite ComRing.mulrC expM expgK.
  by rewrite expgK.
  rewrite x2in //=.
  rewrite !negb_or.
  split.
  + rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => pk_s.
    rewrite negb_exists.
    move => sk_ce.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game4.c_smap{2}.[int] = Some (Accepted (st'.`1, pk_s, sk_ce) (g ^ st'.`3, Some (g ^ loge (oget t'.`2).`1, t)) k ir)); 2: by done.
    simplify. 
    move => stint.
    have := inv2 int i{2} (g ^ st'.`3) (Some (g ^ loge (oget t'.`2).`1, t)) t'.`2.
    smt().
  split.
  + rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => sk_s.
    rewrite negb_exists.
    move => sk_se.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game4.s_smap{2}.[int] = Some (Accepted (st'.`1, sk_s, Some sk_se) (g ^ st'.`3, Some (g ^ loge (oget t'.`2).`1, t)) k ir)); 2: by done.
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
        smt().
      move => H3.
      have->: 1 <= card (get_origins_c t' Game4.s_smap{2}) by smt(@FMap).
      have->: (get_fresh_partners_c t' Game4.s_smap{2} Game4.servers{2}) = fset0; 2: by smt(fcards0).
      rewrite /get_fresh_partners_c.
      apply in_eq_fset0.
      move => x0.
      rewrite mem_fdom mem_filter !negb_and /=. 
      case (x0 = int) => x0eq; 1: by smt().
      case (get_trace (oget Game4.s_smap{2}.[x0]) = Some t'); 2: by smt().
      have:= (inv4 x0 int t'.`1 (g ^ loge (oget t'.`2).`1) (oget t'.`2).`2 (g ^ st'.`3) t). 
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
      + move => x0 y0 sk0 eq1 eq2 eq3 eq4.
        split; 1: by  smt(mem_set).
        right.
        exists (b,j){2} st'.`2 (oget st'.`3) (oget t'.`2).`2 k' (ir'.`1, ir'.`2, true).
        smt(get_setE).
      split.
      + move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, ir'.`2, true)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
          by smt().
        case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
        rewrite get_set_neqE //=.
        move => m1 m2 tag m1' tag' stnn.
        rewrite i'eq !get_set_sameE.
        have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, ir'.`2, true)))) = get_trace (oget Game4.s_smap{2}.[b{2}, j{2}]); 1: by smt().
        by smt().
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      split.
      + move => x0 y0 sk0 b0 x0in.
        case ((g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) = (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1)) => [[] in1 in2 in3 in4 in5|neq].
        + right; left.
          exists (b,j){2} st'.`2 (oget st'.`3) (oget t'.`2).`2 k' (ir'.`1, ir'.`2, true).
          smt(get_setE).
        have := inv x0 y0 sk0 b0.
        have->: (g ^ (ZModE.( * ) x0 y0), g ^ (ZModE.( * ) x0 sk0), b0, g ^ x0, g ^ y0) \in Game4.h2m{2}; 1: by smt(mem_set).
        simplify.
        move => [H1|[H2|H3]].
        + smt().      
        + right; left.
          move : H2 => [i'] sk_s sk_se t k'' ir'' H2.
          exists i' sk_s sk_se t k''.
          case (i' = (b,j){2}) => i'eq. 
          + exists (ir''.`1, ir''.`2, true). 
            split. by smt(get_setE).
            by rewrite i'eq get_set_sameE /#.
          exists ir''.
          by smt(get_setE).
        by smt().
      split; 1: by smt(get_setE).
      move => x0 x0in.
      have:= inv2 x0 x0in.
      move => [H1] [H2] [j'] st'' k'' ir'' H3.
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      exists j'. 
      by smt(get_setE).
    by smt(get_setE mem_set).
  rcondf {1} ^if. auto => /#.
  rcondf {2} ^if. auto => /#.
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? _ inv3 ? inv2 ? ? ? ? inv ? ? ? fresh ? x2in *.
  suff //=:false.
  have := inv (loge t'.`1) (oget st'.`3) st'.`2 st'.`1. 
  have<-: (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1) = (g ^ (loge t'.`1 * (oget st'.`3)), g ^ (loge t'.`1 * st'.`2), st'.`1, g ^ (loge t'.`1), g ^ oget st'.`3). 
  + congr.
    + by rewrite expM expgK. 
    + by rewrite expM expgK.
    + by rewrite expgK.
    smt().
  rewrite x2in //=.
  rewrite !negb_or.
  split.
  + rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => pk_s.
    rewrite negb_exists.
    move => sk_ce.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game4.c_smap{2}.[int] = Some (Accepted (st'.`1, pk_s, sk_ce) (g ^ loge t'.`1, Some (g ^ oget st'.`3, t)) k ir)); 2: by done.
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
        exists (Some (g ^ oget st'.`3,  t)).
        by smt(expgK).
      move => H3.
      have->: 1 <= card (get_origins_s t' Game4.c_smap{2}) by smt(@FMap).
      have->: (get_fresh_partners_s t' Game4.c_smap{2}) = fset0; 2: by smt(fcards0).
      rewrite /get_fresh_partners_s.
      apply in_eq_fset0.
      move => x0.
      rewrite mem_fdom mem_filter !negb_and /=. 
      case (x0 = int) => x0eq; 1: by smt().
      case (exists (m2o : (pkey * tag) option), get_trace (oget Game4.c_smap{2}.[x0]) = Some (t'.`1, m2o)) ; 2: by smt().
      have:= (inv3 int x0 (g ^ loge t'.`1) (Some (g ^ oget st'.`3, t))). 
      by smt(expgK).
    case (ir.`3) => tes; 2: by smt().
    by smt().
  split.
  + rewrite //=.
    rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => sk_s.
    rewrite negb_exists.
    move => sk_se.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game4.s_smap{2}.[int] = Some (Accepted (st'.`1, sk_s, Some sk_se) (g ^ loge t'.`1, Some (g ^ oget st'.`3,  t)) k ir)); 2: by done.
    simplify.
    move => stint.
    have : int = (b,j){2}; 1: by have := inv2 int (b,j){2} (g ^ loge t'.`1) (oget t'.`2).`1 t t'.`1 (oget t'.`2).`2; smt().
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
lemma sofar &m: `| Pr[E_GAKE(GAKEb(NTOR_S(RO), NTOR_C(RO), RO), A).run(false) @ &m : res] - Pr[E_GAKE(GAKEb(NTOR_S(RO), NTOR_C(RO), RO), A).run(true) @ &m : res]|
  <= Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq] 
       + Pr[E_GAKE(Game2, A).run(false) @ &m : Game2.badt] + Pr[E_GAKE(Game2, A).run(true) @ &m : Game2.badt] 
       + 2%r * ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt).
proof. 
rewrite !(gake_game0 _).
apply (ler_trans (`|Pr[E_GAKE(Game1, A).run(false) @ &m : res] - Pr[E_GAKE(Game1, A).run(true) @ &m : res]| + 2%r * ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dt (mode dt))).
+ smt(game0_game1 game0_bad).
rewrite ler_add2r.
rewrite !(game1_game2 _).
apply (ler_trans (`|Pr[E_GAKE(Game3, A).run(false) @ &m : res] - Pr[E_GAKE(Game3, A).run(true) @ &m : res]| + Pr[E_GAKE(Game2, A).run(false) @ &m : Game2.badt] +
             Pr[E_GAKE(Game2, A).run(true) @ &m : Game2.badt])).
+ smt(game2_game3).
rewrite !ler_add2r.
by rewrite !game3_RO !LRO_game4 interestingbit.
qed. 





(* Step 6: Split up probability into all possible test sessions *)
lemma tested_nn &m: Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ Game4.tested = None] = 0%r.
proof.
byphoare => //; hoare.
proc; inline.
call (_: ! (Game4.badq /\ Game4.tested = None) /\ (Game4.tested = None <=> Game4.tq = None)); 2..11: conseq (: true) => //.

- proc; auto => /#.

- proc; inline.
  sp; if => //.
  exlim Game4.c_smap.[i] => csi.
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

auto => /> badq tested tq.
qed.


lemma test_i_pr &m: Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq] = Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ (exists i, Game4.tested = Some i)].
proof.
have->: Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq] = Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ Game4.tested = None] 
               + Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ Game4.tested <> None] by rewrite Pr[mu_split Game4.tested = None].
have->: Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ Game4.tested <> None] = Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ (exists i, Game4.tested = Some i)].
+ rewrite Pr[mu_eq] // => &hr.
  by smt().
by smt(tested_nn).
qed.


op max_qc : int.
axiom max_qc : 0 < max_qc.

lemma sum_pr &m: Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ (exists i, Game4.tested = Some i)] = 
                   big predT (fun i => Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ Game4.tested = Some i]) (range 1 (max_qc + 1))
                   + Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ (exists i, Game4.tested = Some i) /\ !mem (range 1 (max_qc + 1)) (oget Game4.tested)].
proof.
rewrite Pr[mu_split (mem (range 1 (max_qc + 1)) (oget Game4.tested))]. congr.
+ elim: (range 1 (max_qc + 1)) (range_uniq 1 (max_qc + 1)) => /=; 1: by rewrite big_nil Pr[mu_false].
  move => x xs ih [] x_notin_xs uniq_xs /=.
  rewrite {1}andb_orr Pr[mu_or] andbCA !andbA. 
  have ->: Pr[E_GAKE(Game4, A).run(false) @ &m : ((((Game4.badq /\ exists (i : int), Game4.tested = Some i) /\ Game4.badq) /\
     exists (i : int), Game4.tested = Some i) /\ oget Game4.tested = x) /\ (oget Game4.tested \in xs)]
         = Pr[E_GAKE(Game4, A).run(false) @ &m : false].
  + rewrite Pr[mu_eq] // => &hr.
    by smt().
  rewrite Pr[mu_false] //= big_cons {1}/predT /=. congr.
  + rewrite Pr[mu_eq] // => &hr. 
    by smt().
  exact/ih.
by rewrite andbA.
qed.


lemma test_ephrev_nn &m i: Pr[E_GAKE(Game4, A).run(false) @ &m : (Game4.badq /\ Game4.tested = Some i) /\ Game4.test_ephrev_s = None] = 0%r.
proof.
byphoare => //; hoare.
proc; inline.
call (_: ! (Game4.badq /\ Game4.tested = None /\ Game4.test_ephrev_s = None) /\ (Game4.test_ephrev_s = None <=> Game4.tq = None) /\ (Game4.tested = None <=> Game4.tq = None)); 2..11: conseq (: true) => //.

- proc; auto => /#.

- proc; inline.
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

auto => /#.
qed.


lemma split_pr &m i: Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ Game4.tested = Some i] = 
                     Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ Game4.tested = Some i /\ Game4.test_ephrev_s = Some true] 
                     + Pr[E_GAKE(Game4, A).run(false) @ &m : Game4.badq /\ Game4.tested = Some i /\ Game4.test_ephrev_s = Some false].
proof.
rewrite Pr[mu_split Game4.test_ephrev_s = None].
rewrite test_ephrev_nn //=.
rewrite Pr[mu_split Game4.test_ephrev_s = Some true].
do rewrite -andbA.
by congr; rewrite Pr[mu_eq] // => &hr; smt().
qed.


(* Step 7: Reduction to CDH assumption *)
module type DDH_oracle = {
  proc run(gx : group, gy : group, gz : group) : bool
}.

module DDH_O : DDH_oracle = {
  proc run(gx, gy, gz : group) = {
    return (gz = gy ^ (loge gx));
  }
}.

print Game4.




module Reduction_Ltk (A : A_GAKE) (D : DDH_oracle) = {
  var solution : group option

  module Red_O : GAKE_out_i = Game4 with {
    var i : int
    var b_hat : s_id
    var ga, gb : group
    var stop : bool

    proc init_mem [
      -1 + {stop <- false;}
    ]

  }

  proc solve(i : int, b_hat : s_id, ga, gb : group) : group option = {
    var b' : bool;

    solution <- witness;
    Red_O.i <- i;
    Red_O.b_hat <- b_hat;
    Red_O.ga <- ga;
    Red_O.gb <- gb;
    Red_O.init_mem(true);
    b' <@ A(Red_O).run();
    return solution;
  }
}.





module Reduction_Eph (A : A_GAKE) (D : DDH_oracle) = {
  var solution : group option

  module Red_O : GAKE_out_i = Game4 with {
    var i, j : int
    var ga, gb : group

    proc init_mem [
      ^b0<- ~ {b0 <- true;}
    ]
  }

  proc solve(i, j : int, ga, gb : group) : group option = {
    var b' : bool;

    solution <- witness;
    Red_O.i <- i;
    Red_O.j <- j;
    Red_O.ga <- ga;
    Red_O.gb <- gb;
    b' <@ A(Red_O).run();
    return solution;
  }
}.





end section.




