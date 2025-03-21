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
  type input       <= unit,
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

print Game1.
print ROc.


module (Red_ROM_real (D : A_GAKE) : ROc.IdealAll.RO_Distinguisher) (O : ROc.IdealAll.RO) = {
  module AKE_O : GAKE_out = Game1 with {
    proc h [ 
      ^tk<$ ~ {tk <@ O.get(x);}
      ^if -
    ] res ~ (tk)
  }

  proc distinguish() = {
    var b;
    AKE_O.init_mem(false);
    b <@ D(AKE_O).run();
    return b;
  }
}.

(*
print Game2.

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
      ^match#Some.^match#None.^if.^ts<$ -
      ^match#Some.^match#None.^if.^if -
      ^match#Some.^match#None.^if.^t_B<- ~ {t_B <@ O1.get(x); O2.sample(x);}
    ]

    proc send_msg3 [
      ^match#Some.^match#Pending.^ts<$ -
      ^match#Some.^match#Pending.^if -
      ^match#Some.^match#Pending.^t_A<- ~ {t_A <@ O1.get(x); O2.sample(x);}
    ]

    proc c_rev_skey [
      ^match#Some.^match#Accepted.^if.^ks<$ -
      ^match#Some.^match#Accepted.^if.^if -
      ^match#Some.^match#Accepted.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
    ]

    proc s_rev_skey [
      ^match#Some.^match#Accepted.^if.^ks<$ -
      ^match#Some.^match#Accepted.^if.^if -
      ^match#Some.^match#Accepted.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
    ]

    proc c_test [
      ^if.^match#Some.^match#Accepted.^if.^ks<$ -
      ^if.^match#Some.^match#Accepted.^if.^if -
      ^if.^match#Some.^match#Accepted.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
    ]

    proc s_test [
      ^if.^match#Some.^match#Accepted.^if.^ks<$ -
      ^if.^match#Some.^match#Accepted.^if.^if -
      ^if.^match#Some.^match#Accepted.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
    ]  
  }

  proc distinguish() = {
    var b;
    AKE_O.init_mem();
    b <@ D(AKE_O).run();
    return b;
  }
}.*)

(* ------------------------------------------------------------------------------------------ *)
(* Intermediate Bad Game Wrapper *)

(*
print Game3.

module No_Bad_Game = Game3 with {

  proc h [
    1 + ^ (!badq)
  ]

  proc init_s [
    1 + ^ (!badq)
  ]

  proc set_cert [
    ^r<- + (!badq)
  ]

  proc send_msg1 [
    ^r<- + (!badq)
  ]

  proc send_msg2 [
    ^r<- + (!badq)
  ]

  proc send_msg3 [
    ^r<- + (!badq)
  ]

  proc c_rev_skey [
    ^k<- + (!badq)
  ]

  proc s_rev_skey [
    ^k<- + (!badq)
  ]

  proc rev_ltkey [
    ^ltk<- + (!badq)
  ]

  proc c_rev_ephkey [
    ^ek<- + (!badq)
  ]

  proc s_rev_ephkey [
    ^ek<- + (!badq)
  ]

  proc c_test [
    ^k<- + (!badq)
  ]

  proc s_test [
    ^k<- + (!badq)
  ]
}.
*)

(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GAKE {-GAKEb, -Game0, -Game1, -Game2, (*-Game3, -Game4, -Game5, -No_Bad_Game,*) -ROc.IdealAll.RO, -RO, -FRO, -ROSc.I1.RO, -ROSc.I2.RO, -ROSc.I1.FRO, -ROSc.I2.FRO, -Red_Coll_real, -Red_Coll_ideal, -BB.Sample, -Red_ROM_real(*, -Red_ROM2*) }.

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
(* Step 2: Introducing state to keep track of event that adversary queries RO on test session input *)
lemma game1_game2 bit &m: Pr[E_GAKE(Game1, A).run(bit) @ &m : res] = Pr[E_GAKE(Game2, A).run(bit) @ &m : res].
proof.
byequiv => //; sim.
qed.

lemma game2_adv &m: `| Pr[E_GAKE(Game2, A).run(false) @ &m : res] - Pr[E_GAKE(Game2, A).run(true) @ &m : res] | <= Pr[E_GAKE(Game2, A).run(false) @ &m : Game2.badq].
proof. 
admit. 
qed.

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
  by rewrite weight_dprod dkey_ll dtag_ll dkp_ll.

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
lemma game0_split bit &m: Pr[E_GAKE(Game0, A).run(bit) @ &m : res] = Pr[E_GAKE(Game0, A).run(bit) @ &m : res /\ Game0.bad] + Pr[E_GAKE(Game0, A).run(bit) @ &m : res /\ !Game0.bad]. 
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
  by rewrite weight_dprod dkey_ll dtag_ll dkp_ll.

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
rewrite !(game0_split _).
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












(* old code


(* ------------------------------------------------------------------------------------------ *)
(* Step 2: Splitting the random oracle. *)
local clone import DProd.ProdSampling with
  type t1 <- tag,
  type t2 <- key
proof *.

lemma Step2 &m: Pr[E_GAKE(Game1, A).run() @ &m : res] = Pr[ROc.IdealAll.MainD(Red_ROM(A), ROSc.RO_Pair(ROSc.I1.RO,ROSc.I2.RO)).distinguish() @ &m : res].
proof.
byequiv (: ={glob A, glob Red_ROM} ==> _)  => //.
proc*.
outline {1} [1] { r <@ ROc.IdealAll.MainD(Red_ROM(A), ROc.IdealAll.RO).distinguish(); }.

+ inline; wp.
  call (: ={servers, c_smap, s_smap, tested, kp_set, bad}(Game1, Red_ROM.AKE_O) /\ Game1.hm{1} = ROc.IdealAll.RO.m{2}); 
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

by call (ROSc.RO_split (Red_ROM(A))).
qed.


(* ------------------------------------------------------------------------------------------ *)
(* Step 3: Moving sampling of the shared key. *)
print ROSc.

(* Clearing the key out of the state *)
local op s_clear_k (s : pr_st_server instance_state) =
match s with
| Pending _ _ _ => s
| Accepted st t k ir => if ir.`2 \/ ir.`3 then s else Accepted st t witness ir
| Aborted _ _ _ => s
end.

local op c_clear_k (s : pr_st_client instance_state) =
match s with
| Pending _ _ _ => s
| Accepted st t k ir => if ir.`2 \/ ir.`3 then s else Accepted st t witness ir
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


lemma Step3 &m: Pr[ROc.IdealAll.MainD(Red_ROM(A), ROSc.RO_Pair(ROSc.I1.RO,ROSc.I2.RO)).distinguish() @ &m : res] = Pr[E_GAKE(Game2, A).run() @ &m : res].
proof.
byequiv (: ={glob A, glob Red_ROM2} ==> _)  => //.
proc*.

outline {1} [1] { r <@ ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.RO).distinguish(); }.

+ inline*; wp.
  call (: ={hm, servers, tested, kp_set, bad}(Red_ROM.AKE_O, Red_ROM2.AKE_O) /\ ={ROSc.I1.RO.m, ROSc.I2.RO.m}
          /\ (forall h, omap (fun v => c_clear_k v) Red_ROM.AKE_O.c_smap.[h]{1} = Red_ROM2.AKE_O.c_smap.[h]{2})
          /\ (forall h, omap (fun v => s_clear_k v) Red_ROM.AKE_O.s_smap.[h]{1} = Red_ROM2.AKE_O.s_smap.[h]{2})
          /\ (forall i st pt ir, Red_ROM.AKE_O.c_smap{1}.[i] = Some (Pending st pt ir) 
                => (exists b, ir = (b, false, false)))
          /\ (forall i st pt ir, Red_ROM.AKE_O.s_smap{1}.[i] = Some (Pending st pt ir) 
                => ir = (false, false, false))
          /\ (forall i st pt k ir, Red_ROM.AKE_O.c_smap{1}.[i] = Some (Accepted st pt k ir)
                => (exists k', Red_ROM2.AKE_O.c_smap{2}.[i] = Some (Accepted st pt k' ir))
                   /\ ((oget pt.`2).`1 ^ st.`4, st.`2 ^ st.`4, st.`1, st.`3, (oget pt.`2).`1) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[((oget pt.`2).`1 ^ st.`4, st.`2 ^ st.`4, st.`1, st.`3, (oget pt.`2).`1)])
          /\ (forall i st pt k ir, Red_ROM.AKE_O.s_smap{1}.[i] = Some (Accepted st pt k ir)
                => (exists k', Red_ROM2.AKE_O.s_smap{2}.[i] = Some (Accepted st pt k' ir))
                   /\ (pt.`1 ^ oget st.`3, pt.`1 ^ st.`2, st.`1, pt.`1, (oget pt.`2).`1) \in ROSc.I2.RO.m{2}
                   /\ k = oget ROSc.I2.RO.m{2}.[(pt.`1 ^ oget st.`3, pt.`1 ^ st.`2, st.`1, pt.`1, (oget pt.`2).`1)])
          /\ forall x, x \in ROSc.I1.RO.m{1} <=> x \in ROSc.I2.RO.m{1}); last first.
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
    swap {1} ^r0<$ @ 1; swap {1} ^r3<$ @ 2.
    swap {2} ^r0<$ @ 1; swap {2} ^r1<$ @ 2. 
    seq  2  2: (#pre /\ ={r0} /\ r3{1} = r1{2}); 1: by auto=> />.
    sp 4 3; if {1} => //.
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
    swap {1} ^r0<$ @ 1; swap {1} ^r3<$ @ 2.
    swap {2} ^r0<$ @ 1; swap {2} ^r1<$ @ 2.
    seq  2  2: (#pre /\ ={r0} /\ r3{1} = r1{2}); 1: by auto.
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
      case _: (Red_ROM.AKE_O.c_smap{1}.[i{2}])=> /> c_smap1_i.
      case _: (Red_ROM2.AKE_O.c_smap.[i]{2})=> /> c_smap2_i.
      move=> c_clear s_clear inv1 inv2 inv3 inv4 eq_dom mem_ro.
      move: c_smap2_i; rewrite -c_clear.
      rewrite c_smap1_i=> />. 
      smt(get_setE).
    + auto=> /> &1 &2.
      case _: (Red_ROM.AKE_O.c_smap{1}.[i{2}])=> /> c_smap1_i.
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
    case _: (Red_ROM.AKE_O.c_smap{1}.[i{2}])=> /> c_smap1_i.
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
    case _: (Red_ROM.AKE_O.s_smap{1}.[(b, j){2}])=> /> s_smap1_i.
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
        case : (Red_ROM.AKE_O.s_smap.[b{2}, j]{1}) => />.
        smt(s_eq_partners_ck). 
      move => + j - /(_ j). 
      rewrite !domE -s_clear => />.
      case : (Red_ROM.AKE_O.s_smap.[b{2}, j]{1}) => />.
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
    auto => />.
    smt(get_setE).

  - proc; inline.
    sp; if => //; sp; match => //.
    + smt().
    + smt().
    move => stl str.
    match => //; 1..3: smt().
    move => st'l ptl kl irl st'r ptr kr irr.
    if => //.
    + auto => />.
      smt(s_eq_fresh_ck).
    auto => />.
    smt(get_setE).

have ll : forall (c : pkey * pkey * s_id * pkey * pkey), is_lossless dkey by move=> _; exact dkey_ll.
rewrite equiv [{1} 1 (ROSc.I2.FullEager.RO_LRO (Red_ROM2(A, ROSc.I1.RO)) ll)].

inline; wp. 
call (: ={hm, servers, c_smap, s_smap, tested, kp_set, bad}(Red_ROM2.AKE_O, Game2) /\ ROSc.I1.RO.m{1} = Game2.h1m{2} /\ ROSc.I2.RO.m{1} = Game2.h2m{2});
 try sim />.

- by proc; inline; auto => />.

- proc; inline.
  sp. match = => // sk.
  match = => //.
  seq 1 1: (#pre /\ ={kp}); 1: by auto.
  sp 1 1; if => //.
  sp; seq 1 1: (#pre /\ r0{1} = ts{2}); 1: by auto => />.
  auto => />.

- proc; inline.
  sp. match = => // st.
  match = => // st' pt' ir'. 
  auto => />.

- proc; inline.
  sp; match = => // st.
  match = => // st' pt' k' ir'.
  if => //.
  auto => />. 
  smt(get_setE mem_set).

- proc; inline.
  sp; match = => // st.
  match = => // st' pt' k' ir'.
  if => //. auto => />.
  smt(get_setE mem_set).

- proc; inline.
  sp; if => //. sp; match = => // st.
  match = => // st' pt' k' ir'.
  if => //. auto => />.
  smt(get_setE mem_set).

- proc; inline.
  sp; if => //. sp; match = => // st.
  match = => // st' pt' k' ir'.
  if => //. auto => />.
  smt(get_setE mem_set).

auto => />.
qed.

*)

end section.




