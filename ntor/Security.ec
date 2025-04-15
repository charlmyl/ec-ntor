require import AllCore FSet FMap Distr DProd List SplitRO NTOR Games.
import GAKEc HROc.
require Birthday SplitRO.

(* ------------------------------------------------------------------------------------------ *)
(* Reductions *)
(* ------------------------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------------------------ *)
(* Ctxt Collision Reduction *)
op q_is : { int | 0 <= q_is } as ge0_q_is.
op q_m1 : { int | 0 <= q_m1 } as ge0_q_m1.
op q_m2 : { int | 0 <= q_m2 } as ge0_q_m2.

clone Birthday as BB with
  type T  <- (pkey * skey),
  op   uT <- dkp,
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
    ^if.^kp<$ ~ {kp <@ S.s();}
  ]

  proc send_msg1 [
    ^if.^match#None.^kp<$ ~ {kp <@ S.s();}
  ]

  proc send_msg2 [
    ^match#Some.^match#None.^kp<$ ~ { kp <@ S.s(); }
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
  module AKE_O : GAKE_out = Game2 with {
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
      ^match#Some.^match#None.^if.^ts<$ ~ {t_B <@ O1.get(x); O2.sample(x); sk <- witness;}
      [^match#Some.^match#None.^if.^if - ^sk<-] -
    ]

    proc send_msg3 [
      ^match#Some.^match#Pending.^ts<$ ~ {t_A <@ O1.get(x); O2.sample(x); sk <- witness;}
      [^match#Some.^match#Pending.^if - ^sk<-] -
    ]

    proc c_rev_skey [
      var ks : key
      var x : pkey * pkey * s_id * pkey * pkey
      ^match#Some.^match#Accepted.^if.^k<- ~ {x <- ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1); ks <@ O2.get(x); k <- Some ks;}
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

declare module A <: A_GAKE {-GAKEb, -Game0, -Game1, -Game2, -Game3, -ROc.IdealAll.RO, -RO, -FRO, -ROSc.I1.RO, -ROSc.I2.RO, -ROSc.I1.FRO, -ROSc.I2.FRO, -Red_Coll_real, -Red_Coll_ideal, -BB.Sample, -Red_ROM, -Red_ROM2 }.

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
  by match = => //; 1: auto.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 1: Remove collisions in ephemeral and long-term keys. Strategy with 2 * bound *)
lemma game0_game1 b &m: `| Pr[E_GAKE(Game0, A).run(b) @ &m : res] - Pr[E_GAKE(Game1, A).run(b) @ &m : res] | <= Pr[E_GAKE(Game0, A).run(b) @ &m : Game0.bad].
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
  if => //.
  seq 1 1: (#pre /\ ={kp}); 1: by auto.
  by sp 0 1; if{2}; auto => />.
- move => &2 bad.
  proc; if; auto.
  rewrite dkp_ll //=. smt().
- move => &1. 
  proc; if => //. 
  rcondf ^if; auto => />.
  by rewrite dkp_ll.

- move => &2 bad.
  proc; auto => />.
- move => &1. 
  proc; auto => />. 

- proc.
  sp; if => //.
  sp; match = => //. 
  + seq 1 1: (#pre /\ ={kp}); 1: by auto.
    by sp 0 1; if{2}; auto => />.
  move => st. 
  match = => //.
  move => st' pr' ir'.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  + rewrite dkp_ll. smt().
  by smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  + by rewrite dkp_ll.
  by smt().

- proc; inline.
  sp; match = => //. 
  move => sk.
  match = => //.
  + seq 1 1: (#pre /\ ={kp}); 1: by auto.
  sp 0 1; if{2}.
  + by auto => />. 
  auto.
- move => &2 bad.
  proc; inline; sp; match; auto => />.
  match; auto => />.
  rewrite dkp_ll weight_dprod dkey_ll dtag_ll. 
  by smt().
- move => &1. 
  proc; inline; sp; match; auto => />.
  match; 2: by auto => />. 
  rcondf ^if; 1: by auto => />. 
  auto => />.
  by rewrite dkp_ll.

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
lemma game0_bad bit &m: Pr[E_GAKE(Game0, A).run(bit) @ &m : Game0.bad] <= ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dkp (mode dkp).
proof.
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
 /\ (forall kp, kp \in Game0.kp_set{1} => kp \in BB.Sample.l{2})
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
 /\ (forall kp, kp \in Game0.kp_set{1} => kp \in BB.Sample.l{2})
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


lemma game0_notbad_game1 bit &m: Pr[E_GAKE(Game0, A).run(bit) @ &m : res /\ !Game0.bad] = Pr[E_GAKE(Game1, A).run(bit) @ &m : res].
proof. 
byequiv => //.
proc; inline.
call (: Game1.bad
      , ={b0, servers, c_smap, s_smap, tested, kp_set, hm, bad}(Game0, Game1)
      , ={bad}(Game0, Game1)) => //; try sim />; last first.

wp; skip => />.
move => rl rr al bl csl hml kpl ssl sl tl ar br csr hmr kpr ssr sr tr. 
case : (!br) => />.
admit. 

- exact A_ll.

- move => &2 bad; proc; auto => />. 
  by rewrite weight_dprod dkey_ll dtag_ll.
- move => &1; proc; auto.
  by rewrite weight_dprod dkey_ll dtag_ll.

- proc.
  if => //.
  seq 1 1: (#pre /\ ={kp}); 1: by auto.
  by sp 0 1; if{2}; auto => />.
- move => &2 bad.
  proc; if; auto.
  rewrite dkp_ll //=. smt().
- move => &1. 
  proc; if => //. 
  rcondf ^if; auto => />.
  by rewrite dkp_ll.

- move => &2 bad.
  proc; auto => />.
- move => &1. 
  proc; auto => />. 

- proc.
  sp; if => //.
  sp; match = => //. 
  + seq 1 1: (#pre /\ ={kp}); 1: by auto.
    by sp 0 1; if{2}; auto => />.
  move => st. 
  match = => //.
  move => st' pr' ir'.
  auto => />.
- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  + rewrite dkp_ll. smt().
  by smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  + by rewrite dkp_ll.
  by smt().

- proc; inline.
  sp; match = => //. 
  move => sk.
  match = => //.
  + seq 1 1: (#pre /\ ={kp}); 1: by auto.
  sp 0 1; if{2}.
  + by auto => />. 
  auto.
- move => &2 bad.
  proc; inline; sp; match; auto => />.
  match; auto => />.
  rewrite dkp_ll weight_dprod dkey_ll dtag_ll. 
  by smt().
- move => &1. 
  proc; inline; sp; match; auto => />.
  match; 2: by auto => />. 
  rcondf ^if; 1: by auto => />. 
  auto => />.
  by rewrite dkp_ll.

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
qed.

lemma game0_game1_adv &m: `| Pr[E_GAKE(Game0, A).run(false) @ &m : res] - Pr[E_GAKE(Game0, A).run(true) @ &m : res] |
                       <= `| Pr[E_GAKE(Game1, A).run(false) @ &m : res] - Pr[E_GAKE(Game1, A).run(true) @ &m : res] | +  ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dkp (mode dkp).
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










(* ------------------------------------------------------------------------------------------ *)
(* Step 2: Splitting the random oracle. *)
local clone import DProd.ProdSampling with
  type t1 <- tag,
  type t2 <- key
proof *.

lemma game1_game2 bit &m: Pr[E_GAKE(Game1, A).run(bit) @ &m : res] =  Pr[E_GAKE(Game2, A).run(bit) @ &m : res].
proof.
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
    sp 2 2; match = => // sk.
    match = => //.
    seq 1 1: (#pre /\ ={kp}); 1: by auto.
    sp 1 1; if => //.
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
  sp 2 2; match = => // sk.
  match = => //.
  seq 1 1: (#pre /\ ={kp}); 1: by auto.
  sp 1 1; if => //.
  sp. seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto => />.
  auto => />.
  smt(mem_set).

+ proc; inline.
  sp 1 1; match = => // st.
  match = => // st' pt ir.
  sp. seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto.
  auto => />.
  smt(mem_set).

auto => />.
smt(emptyE).
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

lemma game2_delay bit &m: Pr[E_GAKE(Game2, A).run(bit) @ &m : res] = Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(bit) @ &m : res].
proof. 
byequiv (: ={glob A, glob Red_ROM2} /\ arg{1} = bit /\ arg{2} = bit ==> _)  => //.
proc*.

rewrite equiv [{2} 1 -(ROSc.I2.FullEager.RO_LRO (Red_ROM2(A, ROSc.I1.RO)) _)]; 2: by move => _; exact dkey_ll.

+ inline; wp.
  call (: ={b0, hm, servers, tested, kp_set, bad, hq, tq, badq}(Game2, Red_ROM2.AKE_O)
          /\ Game2.h1m{1} = ROSc.I1.RO.m{2} /\ Game2.h2m{1} = ROSc.I2.RO.m{2}
          /\ (forall h, omap (fun v => c_clear_k v) Game2.c_smap.[h]{1} = Red_ROM2.AKE_O.c_smap.[h]{2})
          /\ (forall h, omap (fun v => s_clear_k v) Game2.s_smap.[h]{1} = Red_ROM2.AKE_O.s_smap.[h]{2})
          /\ (forall i st pt ir, Game2.c_smap{1}.[i] = Some (Pending st pt ir) 
                => (exists b, ir = (b, false, false)))
          /\ (forall i st pt ir, Game2.s_smap{1}.[i] = Some (Pending st pt ir) 
                => ir = (false, false, false))
          /\ (forall i st pt k ir, Game2.c_smap{1}.[i] = Some (Accepted st pt k ir)
                => (exists k', Red_ROM2.AKE_O.c_smap{2}.[i] = Some (Accepted st pt k' ir))
                   /\ ((oget pt.`2).`1 ^ st.`4, st.`2 ^ st.`4, st.`1, st.`3, (oget pt.`2).`1) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[((oget pt.`2).`1 ^ st.`4, st.`2 ^ st.`4, st.`1, st.`3, (oget pt.`2).`1)])
          /\ (forall i st pt k ir, Game2.s_smap{1}.[i] = Some (Accepted st pt k ir)
                => (exists k', Red_ROM2.AKE_O.s_smap{2}.[i] = Some (Accepted st pt k' ir))
                   /\ (pt.`1 ^ oget st.`3, pt.`1 ^ st.`2, st.`1, pt.`1, (oget pt.`2).`1) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[(pt.`1 ^ oget st.`3, pt.`1 ^ st.`2, st.`1, pt.`1, (oget pt.`2).`1)])
          /\ forall x, x \in ROSc.I1.RO.m{2} <=> x \in ROSc.I2.RO.m{2}); last first.
  - by auto => />; smt(map_empty emptyE).

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
    smt(get_setE).
  
  - proc; inline.
    sp; match = => // sk.
    match => //.
    + smt().
    + smt().
    seq 1 1: (#pre /\ ={kp}); 1:by auto.
    sp 1 1; if => //.
    swap {1} ^ts<$ @ 1; swap {1} ^ks<$ @ 2.
    swap {2} ^r0<$ @ 1; swap {2} ^r1<$ @ 2. 
    seq  2  2: (#pre /\ ts{1} = r0{2} /\ ks{1} = r1{2}); 1: by auto=> />.
    sp ^if & -1 ^if & -1; if {1} => //.
      + rcondt {1} ^if; 1: by auto => /#.
        rcondt {2} ^if; 1: by auto => /#.
        rcondt {2} ^if; 1: by auto => /#. 
        auto => /> &1 &2.
        smt(mem_set get_setE).
      + rcondf {1} ^if; 1: by auto => /#.
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
    seq  ^if{3} & -1   ^if{3} & -1: (#pre /\ ={t_A} /\ sk{2} = witness /\ (x0{2} \in ROSc.I1.RO.m{2}) /\ sk{1} =
oget ROSc.I2.RO.m{2}.[m3{2}.`1 ^ sk_ce{2}, pk_b{2} ^ sk_ce{2}, b{2}, pk_ce{2}, m3{2}.`1]).
    + if {1} => //.
      + rcondt {1} ^if; 1: by auto => /#.
        rcondt {2} ^if; 1: by auto => /#.
        rcondt {2} ^if; 1: by auto => /#.
        by auto=> />; smt(mem_set get_setE).
      + rcondf {1} ^if; 1: by auto => /#.
        rcondf {2} ^if; 1: by auto => /#.
        rcondf {2} ^if; 1: by auto => /#.
        by auto=> />; smt(mem_set get_setE).
    if=> //. 
    + auto=> /> &1 &2.
      case _: (Game2.c_smap{1}.[i{2}])=> /> c_smap1_i.
      case _: (Red_ROM2.AKE_O.c_smap.[i]{2})=> /> c_smap2_i.
      move=> c_clear s_clear inv1 inv2 inv3 inv4 eq_dom mem_ro.
      move: c_smap2_i; rewrite -c_clear.
      rewrite c_smap1_i=> />. 
      smt(get_setE).
    + auto=> /> &1 &2.
      case _: (Game2.c_smap{1}.[i{2}])=> /> c_smap1_i.
      case _: (Red_ROM2.AKE_O.c_smap.[i]{2})=> /> c_smap2_i.
      move=> c_clear s_clear inv1 inv2 inv3 eq_dom mem_ro.
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
    + auto=> />. smt(c_eq_partners_ck).
    rcondf{2} ^if; 1: by auto => /#.
    auto => /> &1 &2.
    case _: (Game2.c_smap{1}.[i{2}])=> /> c_smap1_i.
    case _: (Red_ROM2.AKE_O.c_smap.[i]{2})=> /> c_smap2_i.
    move=> c_clear s_clear inv1 inv2 inv3 inv4 eq_dom _ k _. 
    smt(get_setE mem_set).

  - proc; inline.
    sp; match=> //.
    + smt().
    + smt().
    move => stl str.
    match => //; 1..3: smt().
    move => st'l ptl kl irl st'r ptr kr irr.
    if => //.
    + auto=> />. smt(s_eq_partners_ck).
    rcondf{2} ^if; 1: by auto => /#.
    auto => /> &1 &2.
    case _: (Game2.s_smap{1}.[(b, j){2}])=> /> s_smap1_i.
    case _: (Red_ROM2.AKE_O.s_smap.[(b, j)]{2})=> /> s_smap2_i.
    move=> c_clear s_clear inv1 inv2 inv3 inv4 eq_dom _ k _.
    smt(get_setE mem_set).

- proc; inline.
    sp; match => //.
    move => stl str.
    match = => // kp.
    if => //.
    + move => /> &1 &2 hkp _ sstl sstr c_clear s_clear inv1 inv2 inv3 inv4 eq_dom.
      split.
      + move => + j - /(_ j). 
        rewrite !domE -s_clear => />.
        case : (Game2.s_smap.[b{2}, j]{1}) => />.
        smt(s_eq_partners_ck). 
      move => + j - /(_ j). 
      rewrite !domE -s_clear => />.
      case : (Game2.s_smap.[b{2}, j]{1}) => />.
      smt(s_eq_partners_ck).
    auto => />.
  
  - proc; inline.
    sp; match => //.
    + smt().
    + smt().
    move => stl str.
    match => //; 1..3: smt().
    + move => st'l ptl irl st'r ptr irr.
      auto => /> &1 &2 *. 
      smt(c_eq_origins_ck get_setE mem_set).
    move => st'l ptl kl irl st'r ptr kr irr.
    if => //.
    + smt(c_eq_partners_ck).
    auto => /> &1 &2.
    smt(get_setE).

- proc; inline.
    sp; match => //.
    + smt().
    + smt().
    move => stl str.
    match => //; 1..3: smt().
    move => st'l ptl kl irl st'r ptr kr irr.
    if => //.
    + smt(s_eq_partners_ck).
    auto => /> &1 &2.
    smt(get_setE).
  
  - proc; inline.
    sp; if => //. sp; match => //.
    + smt().
    + smt().
    move => stl str.
    match => //; 1..3: smt().
    move => st'l ptl kl irl st'r ptr kr irr.
    if => //.
    + auto => />.
      smt(c_eq_fresh_ck).
    if => //.
    + auto => />.
      smt(get_setE).
    auto => />.
    smt(get_setE).

  - proc; inline.
    sp; if => //. sp; match => //.
    + smt().
    + smt().
    move => stl str.
    match => //; 1..3: smt().
    move => st'l ptl kl irl st'r ptr kr irr.
    if => //.
    + auto => />.
      smt(s_eq_fresh_ck).
    if => //.
    + auto => />.
      smt(get_setE).
    auto => />.
    smt(get_setE).
qed.


lemma sofar &m: `| Pr[E_GAKE(GAKEb(NTOR_S(RO), NTOR_C(RO), RO), A).run(false) @ &m : res] - Pr[E_GAKE(GAKEb(NTOR_S(RO), NTOR_C(RO), RO), A).run(true) @ &m : res]|
  <= `|Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(false) @ &m : res] - Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(true) @ &m : res]|
      + 2%r * ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dkp (mode dkp).
proof.   
rewrite !(gake_game0 _).
apply (StdOrder.RealOrder.ler_trans 
        (`|Pr[E_GAKE(Game1, A).run(false) @ &m : res] - Pr[E_GAKE(Game1, A).run(true) @ &m : res]| + 2%r * ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dkp (mode dkp))).
+ smt(game0_game1 game0_bad).
by rewrite !(game1_game2 _) !game2_delay.
qed. 



lemma interestingbit &m: `|Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(false) @ &m : res] - Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(true) @ &m : res]| <= Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(false) @ &m : Red_ROM2.AKE_O.badq].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Red_ROM2.AKE_O.badq => //; first last.
+ smt().
symmetry; proc; inline.
wp.
call (: Red_ROM2.AKE_O.badq
      , ={servers, c_smap, s_smap, tested, kp_set, hm, bad, hq, tq, badq}(Red_ROM2.AKE_O, Red_ROM2.AKE_O)
        /\ ROSc.I1.RO.m{1} = ROSc.I1.RO.m{2} /\ (Red_ROM2.AKE_O.tq{1} = None => ={ROSc.I2.RO.m})
        /\ (forall x, Red_ROM2.AKE_O.tq{1} = Some x => eq_except (pred1 x) ROSc.I2.RO.m{1} ROSc.I2.RO.m{2})
        /\ (Red_ROM2.AKE_O.tested{1} = false => Red_ROM2.AKE_O.tq{1} = None)
      (*  /\ (Red_ROM2.AKE_O.tq{1} <> None => oget Red_ROM2.AKE_O.tq{1} \in ROSc.I2.RO.m{1}) *)
        /\ (forall i st t k ir, Red_ROM2.AKE_O.c_smap{2}.[i] = Some (Accepted st t k ir) /\ get_ir_test (oget Red_ROM2.AKE_O.c_smap{2}.[i]) <> true
                => Some ((oget t.`2).`1 ^ st.`4, st.`2 ^ st.`4, st.`1, st.`3, (oget t.`2).`1) <> Red_ROM2.AKE_O.tq{2})
        /\ (forall i st t k ir, Red_ROM2.AKE_O.s_smap{2}.[i] = Some (Accepted st t k ir) /\ get_ir_test (oget Red_ROM2.AKE_O.s_smap{2}.[i]) <> true
                => Some (t.`1 ^ oget st.`3, t.`1 ^ st.`2, st.`1, t.`1, (oget t.`2).`1) <> Red_ROM2.AKE_O.tq{2})
        /\ (forall i st t k ir, Red_ROM2.AKE_O.c_smap{2}.[i] = Some (Accepted st t k ir) 
                => forall i' st' k' ir', Red_ROM2.AKE_O.c_smap{2}.[i'] = Some (Accepted st' t k' ir') 
                => i = i')
        /\ (forall i st t k ir, Red_ROM2.AKE_O.s_smap{2}.[i] = Some (Accepted st t k ir) 
                => forall i' st' k' ir', Red_ROM2.AKE_O.s_smap{2}.[i'] = Some (Accepted st' t k' ir') 
                => i = i')
        /\ Red_ROM2.AKE_O.b0{1} = false /\ Red_ROM2.AKE_O.b0{2} = true
        /\ (forall x, x \in ROSc.I2.RO.m{1} <=> x \in ROSc.I2.RO.m{2})
      , ={badq}(Red_ROM2.AKE_O, Red_ROM2.AKE_O)) => //; try sim />.

- exact A_ll.

- proc; inline.  
  sp; seq 1 1: (#pre /\ r{1} = r{2}); 1: by auto=> />.
  if => //.
  + auto => /> &1 &2 badqr hqr *.
    split. move => *. smt(get_setE).
    move => *. split. smt(get_setE).
    move => *. case (Red_ROM2.AKE_O.tq{2} = None) => ?; 1: by smt().
    have: (oget Red_ROM2.AKE_O.tq{2} \notin hqr `|` fset1 x{2}); 1: by smt().
    move => ?.
    have: oget Red_ROM2.AKE_O.tq{2} <> x{2}; 1: by smt(@FSet).
    by smt().
  auto => /> &1 &2 badqr hqr *.
  split; 1: by smt(get_setE).
  move => *. split; 1: by smt(get_setE).
  move => *. case (Red_ROM2.AKE_O.tq{2} = None) => ?; 1: by smt().
  have: (oget Red_ROM2.AKE_O.tq{2} \notin hqr `|` fset1 x{2}); 1: by smt().
  move => ?.
  have: oget Red_ROM2.AKE_O.tq{2} <> x{2}; 1: by smt(@FSet).
  by smt().
- move => &2 badq; proc*; inline. auto => />. 
  rewrite dkey_ll dtag_ll //=. smt().
- move => &1; proc*; inline; auto.
  rewrite dkey_ll dtag_ll //=. smt().

- move => &2 badq.
  proc; if; auto.
  rewrite dkp_ll //=.
- move => &1. 
  proc; if => //.
  auto => />. 
  by rewrite dkp_ll.

- move => &2 badq.
  proc; auto => />.
- move => &1. 
  proc; auto => />. 

- proc; inline.
  sp; if => //.
  sp; match = => // [|st].
  + auto => /> &1 &2 *.
    smt(get_setE).
  match = => // st' pt' ir'.
  auto => /> &1 &2 *.
  smt(get_setE).
- move => &2 bad.
  proc; sp; if => //; sp. 
  match; auto => />.
  + rewrite dkp_ll. smt().
  by smt().
- move => &1. 
  proc; sp; if => //. 
  sp; match; auto => />.
  + by rewrite dkp_ll.
  by smt().
 
- proc; inline.
  sp; match = => // sk.
  match = => //.
  seq 1 1: (#pre /\ ={kp}); 1: by auto=> />.
  sp 1 1; if => //.
  sp; seq 1 1: (#pre /\ ={r0}); 1: by auto=> />.
  if => //.
  + auto => /> &1 &2 kps bad stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 fresh notinm.
    split.
    + move => i st t k ir.
      case (Red_ROM2.AKE_O.tq{2} = None) => tqn.
      + smt().
      case (i = (b, j){2}) => eqi.
      + rewrite eqi get_set_sameE //=. rewrite get_setE //=.
        admit. (* need that traces are unique and there is no collision with tq *)
      by rewrite get_set_neqE /#.
    move => i st t k ir.
    case (i = (b, j){2}) => eqi.
    + rewrite eqi get_set_sameE //=. rewrite get_setE //=.
      move => ? i'.
      case (i' = (b, j){2}) => eqi'; 1: by smt().
      admit. (* need that traces are unique and there is no collision with tq *)
    admit.
  auto => /> &1 &2 kps bad stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 fresh inm.
  split; move => i st t k ir. 
  + case (i = (b, j){2}) => eqi.
    + rewrite eqi get_set_sameE //=.
      admit. (* need that traces are unique and there is no collision with tq *)
    by rewrite get_set_neqE //#.
  case (i = (b, j){2}) => eqi.
  + rewrite eqi get_set_sameE //=.
    admit. (* need that traces are unique and there is no collision with tq *)
  admit.
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
  sp; seq 1 1: (#pre /\ ={r0}); 1: by auto=> />.
  if => //.
  + sp ^if & -1 ^if & -1; if => //.
    + auto => /> &1 &2 map1 stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 notinm tag. 
      split; move => i0 st0 pt0 k ir0.
      + case (i0 = i{2}) => eqi.
        + rewrite eqi get_set_sameE //=.
          admit. (* need that traces are unique and there is no collision with tq *)
        by rewrite get_set_neqE //#.
      case (i0 = i{2}) => eqi.
      + rewrite eqi get_set_sameE //=.
        admit. (* need that traces are unique and there is no collision with tq *)
      admit.
    auto => /> &1 &2 map1 stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 inm tag.
    split; move =>  i0 st0 pt0 k ir0.
    + case (i0 = i{2}) => eqi.
      + by rewrite eqi get_set_sameE //=.
      by rewrite get_set_neqE //#.
    case (i0 = i{2}) => eqi.
    + by rewrite eqi get_set_sameE //=.
    admit.
  auto => /> &1 &2 map1 stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8.
  split; move => tag.
  + split; move => i0 st0 pt0 k ir0.
    + case (i0 = i{2}) => eqi.
      + rewrite eqi get_set_sameE //=.
        admit. (* need that traces are unique and there is no collision with tq *)
      by rewrite get_set_neqE //#.
    case (i0 = i{2}) => eqi.
    + rewrite eqi get_set_sameE //=.
      admit. (* need that traces are unique and there is no collision with tq *)
    admit. 
  split; move => i0 st0 pt0 k ir0.
  + case (i0 = i{2}) => eqi.
    + by rewrite eqi get_set_sameE //=.
    by rewrite get_set_neqE //#.
  admit.
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
  swap{1} ^r<$ @ 1.
  swap{2} ^r<$ @ 1.
  seq 1 1: (#pre /\ r{1} = r{2}); 1: by auto=> />.
  sp 2 2; if => //.
  + smt().
  + auto => /> &1 &2 *.
    smt(get_setE mem_set).
  auto => /> &1 &2 stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 fresh inm.
  have := inv4 i{2} st' t' k' ir'.
  have -> : get_ir_test (oget Red_ROM2.AKE_O.c_smap{2}.[i{2}]) <> true; 1: by smt().
  have -> : (Red_ROM2.AKE_O.c_smap{2}.[i{2}] = Some (Accepted st' t' k' ir')); 1: by smt().
  simplify. 
  move => nottq.
  split; 1: by smt().
  split; move => i0 st0 pt k0 ir.  
  + case (i{2} = i0) => eqi.
    + by rewrite eqi get_set_sameE //=.
    by rewrite get_set_neqE //#.
  admit.
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
  swap{1} ^r<$ @ 1.
  swap{2} ^r<$ @ 1.
  seq 1 1: (#pre /\ r{1} = r{2}); 1: by auto=> />.
  sp 2 2; if => //.
  + smt().
  + auto => /> &1 &2 *.
    smt(get_setE mem_set).
  auto => /> &1 &2 stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 fresh inm.
  have := inv5 (b, j){2} st' t' k' ir'.
  have -> : get_ir_test (oget Red_ROM2.AKE_O.s_smap{2}.[(b, j){2}]) <> true; 1: by smt().
  have -> : (Red_ROM2.AKE_O.s_smap{2}.[(b, j){2}] = Some (Accepted st' t' k' ir')); 1: by smt().
  simplify. 
  move => nottq.
  split; 1: by smt(). 
  split; move => i0 st0 pt k0 ir.  
  + case ((b, j){2} = i0) => eqi.
    + by rewrite eqi get_set_sameE //=.
    by rewrite get_set_neqE //#.
  admit.
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

- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
  sp; match = => // st.
  match = => // [st' pt ir| st' pt k ir].
  + auto => /> &1 &2 stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 unto. 
    split; move => i0 st0 pt0 k ir0.
    + case (i0 = i{2}) => eqi.
      + rewrite eqi get_set_sameE //=.
      by rewrite get_set_neqE //#.
    admit.
  auto => /> &1 &2 stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 fresh. 
  split; move => i0 st0 pt0 k0 ir0.
  + have := inv4 i{2} st' pt k ir.
    case (i0 = i{2}) => eqi.
    + rewrite eqi get_set_sameE /#.
    by rewrite get_set_neqE /#.  
  admit.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
  sp; match = => // st.
  match = => // st' pt k ir.
  auto => /> &1 &2 stm _ stnn _ neqb inv1 inv2 inv3 inv4 inv5 inv6 inv7 inv8 fresh.
  split; move => i0 st0 pt0 k0 ir0.
  + have := inv5 (b, j){2} st' pt k ir.
    case (i0 = (b, j){2}) => eqi.
    + by rewrite eqi get_set_sameE /#.
    by rewrite get_set_neqE /#.
  admit.
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
  move => st' pt' k' ir'.
  if => //.
  rcondt{1} ^if; 1: by auto.
  rcondf{2} ^if; 1: by auto.
  inline{2}. swap {2} ^r0<$ @ 1.
  seq 0 1: (#pre /\ r0{2} \in dkey). auto => />.
  sp 3 4; if{2} => //.
  + sp 0 2.
    seq 4 1: (#pre /\ ={ks} /\ x{1} \in ROSc.I2.RO.m{1}). 
    + rcondt{1} ^if; 1: by auto => /#.
      sp; seq 1 1: (#pre /\ r{1} = ks{2}). auto => />.
      auto => /> &1 &2 *.
      split. admit.
      smt(get_setE mem_set).
    auto => /> &1 &2 *.    
    split.
    smt(get_setE mem_set).
    split. 
    move => i0 st0 pt k0 ir. 
    case (i0 = i{2}) => eqi.
    + rewrite eqi get_set_sameE //=.
    rewrite get_set_neqE //=.
    admit. (* need that traces are unique and there is no collision with tq *)
    split. 
    move => i0 st0 pt k0 ir. 
    admit. (* need that traces are unique and there is no collision with tq *)
    smt(get_setE).
  (* this side is only possible when badq happens since instance cannot be tested or seskey revealed - TODO: could be added as invariant? *)
  sp 0 1.
  seq 4 1: (#pre /\ ={ks} /\ x{1} \in ROSc.I2.RO.m{1}).
  + rcondf{1} ^if; 1: by auto => /#.  
    admit. (* How to prove that the already sampled value has the same distribution as ks? *)
  auto => /> &1 &2 *.
  split; 1: by smt().
  split.
  + move => i0 st0 pt k0 ir. 
    case (i0 = i{2}) => eqi.
    + rewrite eqi get_set_sameE //=.
    rewrite get_set_neqE //=.
    admit. (* need that traces are unique and there is no collision with tq *)
  split; move => i0 st0 pt k0 ir. 
  + admit. (* need that traces are unique and there is no collision with tq *)
  admit.
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
  move => st' pt' k' ir'.
  if => //.
  rcondt{1} ^if; 1: by auto.
  rcondf{2} ^if; 1: by auto.
  admit. (* same as above *)
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

auto => />.
split; 1: by smt(emptyE).
move => injc injs rl rr al bl bql csl hql kpl ssl sl tl tql h1ml h2ml ar br bqr csr hqr kpr ssr sr tr tqr h1mr h2mr. 
by case : (!bqr) => />.
qed.




end section.




