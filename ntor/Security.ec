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



lemma game0_notbad_game1 bit &m: Pr[E_GAKE(Game0, A).run(bit) @ &m : res /\ !Game0.bad] = Pr[E_GAKE_BB(A).run(bit) @ &m : res].
proof. 
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
                       <= `| Pr[E_GAKE_BB(A).run(false) @ &m : res] - Pr[E_GAKE_BB(A).run(true) @ &m : res] | +  ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dkp (mode dkp).
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

lemma red_game3 bit &m: Pr[ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.LRO).distinguish(bit) @ &m : res] = Pr[E_GAKE(Game3, A).run(bit) @ &m : res].
proof.
byequiv => //.
proc*.
inline; wp.
call (: ={b0, hm, servers, c_smap, s_smap, tested, kp_set, bad, hq, tq, badq}(Red_ROM2.AKE_O, Game3) /\ ROSc.I1.RO.m{1} = Game3.h1m{2} /\ ROSc.I2.RO.m{1} = Game3.h2m{2}); 
    try sim />.

+ proc; inline; auto => />.

+ proc; inline.
  sp; match = => // skb.
  match = => //.
  seq 1 1: (#pre /\ ={kp}); 1: by auto.
  sp; if => //; auto => />.

+ proc; inline.
  sp 1 1; match = => // st.
  match = => // st' pt ir.
  sp. seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto.
  auto => />.

+ proc; inline.
  sp 1 1; match = => // st.
  match = => // st' pt k ir.
  if => //.
  sp. seq 1 1: (#pre /\ r{1} = ks{2}); 1: by auto.
  if => //; auto => />; smt(get_setE).

+ proc; inline.
  sp 1 1; match = => // st.
  match = => // st' pt k ir.
  if => //.
  sp. seq 1 1: (#pre /\ r{1} = ks{2}); 1: by auto.
  if => //; auto => />; smt(get_setE).

+ proc; inline.
  sp 1 1; if => //; match = => // st.
  match = => // st' pt k ir.
  if => //; if => //; auto => />; smt(get_setE).

+ proc; inline.
  sp 1 1; if => //; match = => // st.
  match = => // st' pt k ir.
  if => //; if => //; auto => />; smt(get_setE).

auto => />.
qed.


op log : pkey -> pkey -> skey.
op root : skey -> pkey -> pkey.

axiom logC pk sk: log (pk ^ sk) pk = sk.
axiom rootC pk sk: root sk (pk ^ sk) = pk.

axiom sk_uq pk sk sk': (pk, sk) \in dkp /\ (pk, sk') \in dkp => sk = sk'.

op inv_Game3 (tested : bool, 
tq : (pkey * pkey * s_id * pkey * pkey) option, 
badq : bool, 
kp_set : ((pkey * skey)) fset, 
ssm : (s_id * int, pr_st_server instance_state) fmap, 
hq : (pkey * pkey * s_id * pkey * pkey) fset, 
csm : (int, pr_st_client instance_state) fmap, 
h2m : (pkey * pkey * s_id * pkey * pkey, key) fmap) = 
       (!tested <=> tq = None)
        /\ (badq = true <=> (tq <> None /\ oget tq \in hq))
        /\ (forall x, tq = Some x => x \in h2m 
                         /\ ((exists i tag key ir, csm.[i] = Some (Accepted (x.`3, root (log x.`1 x.`5) x.`2, x.`4, (log x.`1 x.`5)) (x.`4, Some (x.`5, tag)) key ir)
                     /\ ir.`3)
                  \/ (exists i tag key ir, ssm.[i] = Some (Accepted (x.`3, (log x.`2 x.`4), Some (log x.`1 x.`4)) (x.`4, Some (x.`5, tag)) key ir)
                     /\ ir.`3)))
        /\ (forall i st t k ir, csm.[i] = Some (Accepted st t k ir) => !tested => !ir.`3)
        /\ (forall i st t k ir, ssm.[i] = Some (Accepted st t k ir) => !tested => !ir.`3)
        /\ (forall kp, kp \in kp_set => kp \in dkp)
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
                => (pt = st.`3) /\ !ir.`3)
        /\ (forall i st t k ir, csm.[i] = Some (Accepted st t k ir)
                => (t.`1 = st.`3) /\ (exists pk tag, (t.`2 = Some (pk, tag))))
      (*  /\ (forall i st t k ir, csm.[i] = Some (Accepted st t k ir)
                => !(ir.`3 \/ untested_partner_c t ssm = Some false) /\ tq <> None 
                => ((oget t.`2).`1 ^ st.`4, st.`2 ^ st.`4, st.`1, st.`3, (oget t.`2).`1) <> oget tq)*)
        /\ (forall i st t k ir, ssm.[i] = Some (Accepted st t k ir)
                => (exists sk, st.`3 = Some sk) /\ (exists pk tag, (t.`2 = Some (pk, tag))))
        /\ (forall x, x \in h2m
                => (exists i tag key ir, csm.[i] = Some (Accepted (x.`3, root (log x.`1 x.`5) x.`2, x.`4, (log x.`1 x.`5))
                                  (x.`4, Some (x.`5, tag)) key ir)
                     /\ (ir.`2 \/ ir.`3))
                  \/ (exists i tag key ir, ssm.[i] = Some (Accepted (x.`3, (log x.`2 x.`4), Some (log x.`1 x.`4))
                                  (x.`4, Some (x.`5, tag)) key ir)
                     /\ (ir.`2 \/ ir.`3))
                  \/ x \in hq).


lemma interestingbit &m: `|Pr[E_GAKE(Game3, A).run(false) @ &m : res] - Pr[E_GAKE(Game3, A).run(true) @ &m : res]| <= Pr[E_GAKE(Game3, A).run(false) @ &m : Game3.badq].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game3.badq => //; first last.
+ smt().
symmetry; proc; inline.
wp.
call (: Game3.badq
      , ={servers, c_smap, s_smap, tested, kp_set, hm, bad, h1m, hq, tq, badq}(Game3, Game3)
        /\ (Game3.tq{1} = None => ={Game3.h2m})
        /\ (forall x, Game3.tq{1} = Some x => eq_except (pred1 x) Game3.h2m{1} Game3.h2m{2})
        /\ Game3.b0{1} = false /\ Game3.b0{2} = true
        /\ (inv_Game3 Game3.tested Game3.tq Game3.badq Game3.kp_set Game3.s_smap Game3.hq Game3.c_smap Game3.h2m){2}
        /\ (forall x, x \in Game3.h2m{1} <=> x \in Game3.h2m{2})
      , ={badq}(Game3, Game3)) => //; last first.

- auto => />.
split; 1: by smt(emptyE in_fset0).
move => ntc nts ninkps injc pkins injs trs pc acc acs inv rl rr al bl bql csl hql kpl ssl sl tl tql h1ml h2ml ar br bqr csr hqr kpr ssr sr tr tqr h1mr h2mr. 
by case : (!bqr) => />. 

- exact A_ll.

- admit. admit. admit. (*
- proc; inline.  
  sp; seq 1 1: (#pre /\ t{1} = t{2}); 1: by auto=> />.
  if => //.
  + sp; seq 1 1: (#pre /\ ={k}); 1: by auto => />.
    if => //; 1: by smt().
    + auto => /> &1 &2 *. smt(get_setE in_fsetU1 mem_set).
    auto => /> &1 &2 *. smt(get_setE in_fsetU1 mem_set).
  seq 1 1: (#pre /\ ={k}); 1: by auto => />.
  if => //; 1: by smt().
  + auto => /> &1 &2 *. smt(get_setE in_fsetU1 mem_set).
  auto => /> &1 &2 *. smt(get_setE in_fsetU1 mem_set).
- move => &2 badq; proc*; inline. auto => />. 
  rewrite dkey_ll dtag_ll //=. smt().
- move => &1; proc*; inline; auto.
  rewrite dkey_ll dtag_ll //=. smt(). *)

- admit. admit. admit. (*
- proc. 
  if => //.
  auto => /> &1 &2 *.
  smt(in_fsetU1).
- move => &2 badq.
  proc; if; auto.
  rewrite dkp_ll //=.
- move => &1. 
  proc; if => //.
  auto => />. 
  by rewrite dkp_ll. *)

- admit. admit. admit. (*
- sim />.
- move => &2 badq.
  proc; auto => />.
- move => &1. 
  proc; auto => />.*)
 
- proc; inline.
  sp; if => //.
  sp; match = => // [|st].
  + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? inv ? ? ? ? ? ? ? ? kp *.
    split; 1: by smt().
    split; 1: by smt(get_setE in_fsetU1).
    split; 1: by smt(get_setE).
    split; 1: by smt(in_fsetU1).
    split.    
    + move => // i0 i'.
      case (i0 = i{2}) => ieq.
      + rewrite ieq get_set_sameE //=.
        case (i' = i{2}) => i'eq; 1: by rewrite i'eq.
        rewrite get_set_neqE //=.
        move => m10 m2 m2' stnn trs.
        have := inv i' None kp.`1.
        rewrite stnn trs //=.
        have : !(exists (sk : skey), (kp.`1, sk) \in Game3.kp_set{2}); rewrite negb_exists.
        + smt(sk_uq).
        smt().
      case (i' = i{2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => stnn.
      rewrite i'eq !get_set_sameE //=.
      smt(sk_uq).
    split; 1: by smt(get_setE in_fsetU1).
    split; 1: by smt(get_setE in_fsetU1).
    split; 1: by smt(get_setE in_fsetU1).
    split; 1: by smt(get_setE in_fsetU1).
    smt(get_setE in_fsetU1).
  match = => // st' pt ir.
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? inv *.
  split; 1: by smt().
  split; 1: by smt(get_setE in_fsetU1).
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
  split; by smt(get_setE in_fsetU1).
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
  seq 1 1: (#pre /\ ={kp} /\ kp{2} \in dkp); 1: by auto=> />.
  sp 1 1; if => //.
  sp; seq 1 1: (#pre /\ ={ts}); 1: by auto=> />.
  if => //.
  + auto => /> &1 &2 kps ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? inv ? inv2 *.
    split; 1: by smt(get_setE in_fsetU1).
    split; 1: by smt(get_setE in_fsetU1).
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
        rewrite stnn trs //=.
        have : !(exists (sk : skey), (kp{2}.`1, sk) \in kps); rewrite negb_exists.
        + smt(sk_uq).
        smt().
      case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
      rewrite get_set_neqE //=.
      move => stnn.
      rewrite i'eq !get_set_sameE //=.
      smt(sk_uq).
    split; 1: by smt(get_setE in_fsetU1).
    smt(get_setE).
  auto => /> &1 &2 kps ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? inv2 ? ? ? inv *.
  split; 1: by smt(get_setE in_fsetU1).
  split; 1: by smt(get_setE in_fsetU1).
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
      rewrite stnn trs //=.
      have : !(exists (sk : skey), (kp{2}.`1, sk) \in kps); rewrite negb_exists.
      + smt(sk_uq).
      smt(). 
    case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => stnn.
    rewrite i'eq !get_set_sameE //=.
    smt(sk_uq).
  split; 1: by smt(get_setE in_fsetU1).
  split; 1: by smt(get_setE in_fsetU1).
  move => x2 x2in.
  have := inv x2.
  have->: x2 \in Game3.h2m{2}; 1: by smt(mem_set). 
  simplify.
  move => [H1|[H2|H3]].
  + smt().
  + right. left.
    move : H2 => [i'] t k ir H2.
    exists i'. 
    smt(get_setE).
  by smt().
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
  + sp ^if & -1 ^if & -1; if => //.
    + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? inv2 ? _ _ *.
      split; 1: by smt(get_setE).
      split. 
      + move => x tqeq.
        have := inv2 x tqeq.
        move => [H1] [H2|H3]. 
        + split; 1: by smt(mem_set).
          left.
          move : H2 => [i'] t k ir'' H2.
          exists i'. 
          by smt(get_setE).     
        smt(mem_set).
      split. smt(get_setE).
      split; 1: by smt(get_setE).
      smt(get_setE).
    auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? ? _ *.
    smt(get_setE).
  sp ^if & -1 ^if & -1; if => //.
  + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? _ *. 
    smt(get_setE).
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? _ *.
  smt(get_setE).
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
  + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? inv2 ? ? ? ? ? ? ? ? ? ? inv *.
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split.
    + split; 1: by smt().
      split. 
      + move => x tqeq.
        have := inv2 x tqeq.
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
      move => x2 x2in.
      case (x2 = ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1)) => x2eq.
      + left.
        exists i{2} (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
        rewrite get_set_sameE //=.
        rewrite x2eq //= logC rootC //=. 
        by smt(). 
      have := inv x2.
      have->: x2 \in Game3.h2m{2}; 1: by smt(mem_set). 
      simplify.
      move => [H1|H2].
      + left. 
        move : H1 => [i'] t k ir H1.
        exists i'. 
        smt(get_setE).
      by smt().
    by smt(get_setE mem_set).
(************ case that the handle was in h2m ************)
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? inv2 ? ? ? ? ? ? ? ? ? ? inv *.
  split.
  + case (Game3.tested{2}) => test; 2: by smt().
    case (Some ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1) = Game3.tq{2}) => tqeq; 2: by smt().
    have := inv2 ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1).
    rewrite //= logC rootC tqeq some_oget //=; 1: smt().
    move => [] tqin [[i0 t k ir [H1 H2]]|[i0 t k ir [H1 H2]]].
    have : get_trace (oget Game3.c_smap{2}.[i0]) = get_trace (oget Game3.c_smap{2}.[i{2}]); smt().
    admit. (* match state of partners *)
  split; 1: by smt().
  split.
  + move => x tqeq.
    have := inv2 x tqeq.
    move => [H1] [H2|H3]. 
    + split; 1: by smt(mem_set).
      left.
      move : H2 => [i'] t k ir'' H2.
      exists i'. 
      by smt(get_setE).     
    smt(mem_set).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  move => x2 x2in.
  case (x2 = ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1)) => x2eq.
  + left.
    exists i{2} (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
    rewrite get_set_sameE //=.
    rewrite x2eq //= logC rootC //=.
    have->: st'.`3 = t'.`1; 1: by smt().
    by smt().
  have := inv x2.
  have->: x2 \in Game3.h2m{2}; 1: by smt(mem_set). 
  simplify.
  move => [H1|H2].
  + left.
    move : H1 => [i'] t k ir H1.
    exists i'.
    by smt(get_setE).
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
  + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? ? ? ? ? ? inv *.
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split; 1: by smt(get_setE mem_set).
    split.
    + split; 1: by smt().
      split. 
      + move => x tqeq.
        have := inv2 x tqeq.
        move => [H1] [H2|H3]; 1: smt(mem_set).
        split; 1: by smt(mem_set).
        right.
        move : H3 => [i'] t k ir'' H3.
        exists i' t k ir''. 
        have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game3.s_smap{2}.[b{2}, j{2}]); 1: by smt().
        by smt(get_setE).
      split; 1: by smt(get_setE).
      split.
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
      move => x2 x2in.
      case (x2 = (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1)) => x2eq.
      + right; left.
        exists (b, j){2} (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
        rewrite get_set_sameE //=.
        rewrite x2eq //= !logC //=. 
        by smt(get_setE). 
      have := inv x2.
      have->: x2 \in Game3.h2m{2}; 1: by smt(mem_set). 
      simplify.
      move => [H1|[H2|H3]].
      + by smt().
      + right; left. 
        move : H2 => [i'] t k ir H2.
        exists i'. 
        smt(get_setE).
      by smt().
    by smt(get_setE mem_set).
(************ case that the handle was in h2m ************)
  auto => /> &1 &2 stbj ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? ? ? ? ? ? inv *.
  split.
  + case (Game3.tested{2}) => test; 2: by smt().
    case (Some (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1) = Game3.tq{2}) => tqeq; 2: by smt().
    have := inv2 (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1).
    rewrite //= !logC tqeq some_oget //=; 1: smt().
    move => [] tqin [[i0 t k ir [H1 H2]]|[i0 t k ir [H1 H2]]].
    admit. (* match state of partners *)
    have : t = (oget t'.`2).`2. admit. move => teq.
    have : get_trace (oget Game3.s_smap{2}.[i0]) = get_trace (oget Game3.s_smap{2}.[(b, j){2}]). smt().
    move => treq.
    have: i0 = (b,j){2}. smt().
    move => i0eq.
    have : ir.`3 = get_ir_test (oget Game3.s_smap{2}.[b{2}, j{2}]). rewrite -i0eq. smt(). smt().
  split; 1: by smt().
  split.
  + move => x tqeq.
    have := inv2 x tqeq.
    move => [H1] [H2|H3]; 1: smt(mem_set).
    split. smt(mem_set).
    right.
    move : H3 => [i'] t k ir'' H3.
    exists i' t k ir''. 
    have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game3.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    by smt(get_setE).
  split; 1: by smt(get_setE).
  split.
  + move => // i0 i'.
    case (i0 = (b, j){2}) => ieq.
    + rewrite ieq get_set_sameE //=.
      case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
      rewrite get_set_neqE //=.
      have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game3.s_smap{2}.[b{2}, j{2}]); 1: by smt().
      smt().
    case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => m1 m2 tag m1' tag' stnn.
    rewrite i'eq !get_set_sameE.
    have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game3.s_smap{2}.[b{2}, j{2}]); 1: by smt().
    smt().
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  move => x2 x2in.
      case (x2 = (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1)) => x2eq.
      + right; left.
        exists (b, j){2} (oget t'.`2).`2 k' (ir'.`1, true, ir'.`3).
        rewrite get_set_sameE //=.
        rewrite x2eq //= !logC //=. 
        by smt(get_setE).
      have := inv x2.
      have->: x2 \in Game3.h2m{2}; 1: by smt(mem_set). 
      simplify.
      move => [H1|[H2|H3]].
      + by smt().
      + right; left. 
        move : H2 => [i'] t k ir H2.
        exists i' t k ir.
        have : get_trace (oget (Some (Accepted st' t' k' (ir'.`1, true, ir'.`3)))) = get_trace (oget Game3.s_smap{2}.[b{2}, j{2}]); 1: by smt().
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

- sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- proc; inline.
  sp; match = => // st.
  match = => // [st' pt ir| st' pt k ir].
  + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? ? ? ? ? ? inv *.
    split; 1: by smt(get_setE).
    split. 
    + move => x tqeq.
      have := inv2 x tqeq.
      move => [H1] [H2|H3]. 
      split. smt().
      left.
      move : H2 => [i'] t k ir' H2.
      exists i'. 
      by smt(get_setE).     
      smt(). 
    split; 1: by smt(get_setE).
    split; 1: by smt(get_setE).
    split; 1: by smt(get_setE).
    split; 1: by smt(get_setE).
    split. smt(get_setE).
    move => x2 x2in.
    have := inv x2.
    rewrite x2in //=.
    move => [H1|H2].
    + left.
      move : H1 => [i'] t k ir' H1.
      exists i'. 
      by smt(get_setE).
    by smt().
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? ? ? ? ? ? inv *. 
  split; 1: by smt(get_setE).
  split.
  + move => x tqeq.
    have := inv2 x tqeq.
    move => [H1] [H2|H3].
    split. smt().
    left.
    move : H2 => [i'] t k' ir' H2.
    exists i'. 
    by smt(get_setE).     
    smt(). 
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split; 1: by smt(get_setE).
  split. smt(get_setE).
  move => x2 x2in.
  have := inv x2.
  rewrite x2in //=.
  move => [H1|H2].
  + left. 
    move : H1 => [i'] t k' ir' H1.
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
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? ? ? ? ? ? inv *.
  split; 1: by smt(get_setE).
  split. 
  + move => x tqeq.
    have := inv2 x tqeq.
    move => [H1] [H2|H3]. 
    smt().
    split. smt().
    right.
    move : H3 => [i'] t k ir'' H3.
    case ((b, j){2} = i') => i'eq.
    + have : Game3.s_smap{2}.[b{2}, j{2}] = Game3.s_smap{2}.[i']; 1: by smt().
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
      by smt().
    case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
    rewrite get_set_neqE //=.
    move => m1 m2 tag m1' tag' stnn.
    rewrite i'eq !get_set_sameE.
    by smt().
  split; 1: by smt(get_setE). 
  split; 1: by smt(get_setE).
  move => x2 x2in.
  have := inv x2.
  rewrite x2in //=.
  move => [H1|[H2|H3]].
  + by smt().
  + right; left.
    move : H2 => [i'] t k'' ir'' H2.
    case ((b, j){2} = i') => i'eq.
      have : Game3.s_smap{2}.[b{2}, j{2}] = Game3.s_smap{2}.[i']; 1: by smt().
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
  case (x{2} \notin Game3.h2m{2}).
  + rcondt {1} ^if. auto => /#.
    rcondt {2} ^if. auto => /#.
    auto => /> &1 &2 badq tq ? ? ? ? ? ? ? ? ? inv2 ? ? _ ? ? ? ? ? ? ? inv *.
    split. smt(get_setE mem_set).
    split. smt(get_setE mem_set).
    split. 
    + split.
      + move => x tqeq.
        split. smt(mem_set).
        left.
        rewrite -tqeq //= logC rootC.
        exists i{2}.
        by smt(get_setE). 
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      move => x2 x2in.
      case (x2 = ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1)) => x2eq.
      + left.
        exists i{2}.
        rewrite x2eq get_set_sameE //= logC rootC //=.
        smt().
      have := inv x2.
      have->: x2 \in Game3.h2m{2}; 1: by smt(mem_set).
      simplify.
      move => [H1|H2].
      + left.
        move : H1 => [i'] t k'' ir'' H1.
        exists i'.
        smt(get_setE).
      by smt().
    smt(get_setE mem_set).
  rcondf {1} ^if. auto => /#.
  rcondf {2} ^if. auto => /#.
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? _ inv2 ? ? ? ? ? ? inv ? ? fresh ? x2in *.
  suff //=:false.
  have := inv ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1).
  rewrite x2in //=.
  rewrite !negb_or.
  split.
  + rewrite logC rootC //=. 
    rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game3.c_smap{2}.[int] = Some (Accepted (st'.`1, st'.`2, st'.`3, st'.`4) (st'.`3, Some ((oget t'.`2).`1, t)) k ir)); 2: by done.
    simplify. 
    move => stint.
    have := inv2 int i{2} t'.`1 (Some ((oget t'.`2).`1, t)) t'.`2.
    smt().
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
    case (Game3.s_smap{2}.[int] = Some (Accepted (st'.`1, log (st'.`2 ^ st'.`4) st'.`3, Some (log ((oget t'.`2).`1 ^ st'.`4) st'.`3)) (st'.`3, Some ((oget t'.`2).`1, t)) k ir)); 2: by done.
    simplify.
    move => stint.
    admit. (* difficult since values come from the partner *)
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
  case (x{2} \notin Game3.h2m{2}).
  + rcondt {1} ^if. auto => /#.
    rcondt {2} ^if. auto => /#.
    auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? _ ? ? ? ? ? ? ? inv *.
    split. smt(get_setE mem_set).
    split. smt(get_setE mem_set).
    split. 
    + split.
      + move => x tqeq.
        split. smt(mem_set).
        right.
        rewrite -tqeq //= !logC.
        exists (b, j){2}.
        by smt(get_setE).
      split.
      + move => // i0 i'.
        case (i0 = (b, j){2}) => ieq.
        + rewrite ieq get_set_sameE //=.
          case (i' = (b, j){2}) => i'eq; 1: by rewrite i'eq.
          rewrite get_set_neqE //=.
          by smt().
        case (i' = (b, j){2}) => i'eq; 2: by smt(get_set_neqE).
        rewrite get_set_neqE //=.
        move => m1 m2 tag m1' tag' stnn.
        rewrite i'eq !get_set_sameE.
        by smt().
      split; 1: by smt(get_setE).
      split; 1: by smt(get_setE).
      move => x2 x2in.
      case (x2 = (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1)) => x2eq.
      + right; left.
        exists (b, j){2}.
        rewrite x2eq get_set_sameE //= !logC //=.
        smt().
      have := inv x2.
      have->: x2 \in Game3.h2m{2}; 1: by smt(mem_set).
      simplify.
      move => [H1|[H2|H3]].
      + smt().      
      + right; left.
        move : H2 => [i'] t k'' ir'' H2.
        exists i' t k'' ir''.
        smt(get_setE).
      by smt().
    by smt(get_setE mem_set).
  rcondf {1} ^if. auto => /#.
  rcondf {2} ^if. auto => /#.
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? _ ? ? inv2 ? ? ? ? inv ? ? fresh ? x2in *.
  suff //=:false.
  have := inv (t'.`1 ^ oget st'.`3, t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1).
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
    case (Game3.c_smap{2}.[int] = Some (Accepted (st'.`1, root (log (t'.`1 ^ oget st'.`3) (oget t'.`2).`1) (t'.`1 ^ st'.`2), t'.`1, log (t'.`1 ^ oget st'.`3) (oget t'.`2).`1) (t'.`1, Some ((oget t'.`2).`1, t)) k ir)); 2: by done.
    simplify. 
    move => stint.
    admit. (* difficult since values come from the partner *)
  split.
  + rewrite !logC //=.
    rewrite negb_exists. 
    move => int.
    rewrite negb_exists.
    move => t.
    rewrite negb_exists.
    move => k.
    rewrite negb_exists.
    move => ir.
    rewrite negb_and.
    case (Game3.s_smap{2}.[int] = Some (Accepted (st'.`1, st'.`2, Some (oget st'.`3)) (t'.`1, Some ((oget t'.`2).`1, t)) k ir)); 2: by done.
    simplify.
    move => stint.
    have : int = (b,j){2}; 1: by have := inv2 int (b,j){2} t'.`1 (oget t'.`2).`1 t t'.`1 (oget t'.`2).`2; smt().
    move => inteq.
    rewrite negb_or.
    split. 
    + have : ir.`2 = get_ir_sess (oget Game3.s_smap{2}.[b{2}, j{2}]); 1: by rewrite -inteq /#.
      smt().
    have : ir.`3 = get_ir_test (oget Game3.s_smap{2}.[b{2}, j{2}]); 1: by rewrite -inteq /#.
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




end section.




