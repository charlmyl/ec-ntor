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
  op q <- q_is + q_m1 + q_m2
  proof*.
realize ge0_q by smt(ge0_q_is ge0_q_m1 ge0_q_m2).

module Counter (G : GAKE_out) : GAKE_out_i = {
  var cis, cm1, cm2 : int

  include G[h, set_cert, send_msg3, c_rev_skey, s_rev_skey, rev_ltkey, c_rev_ephkey, s_rev_ephkey, c_test, s_test]

  proc init_mem() = {
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

module (Red_Coll (A : A_GAKE) : BB.Adv) (S : BB.ASampler) = {
  proc a() = {
    var b;
    Red_Coll_O_AKE(S).init_mem();
    Counter(Red_Coll_O_AKE(S)).init_mem();
    b <@ A(Counter(Red_Coll_O_AKE(S))).run();
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* ROM Reductions *)
clone Split as ROc with
  type from    <= pkey * pkey * s_id * pkey * pkey,
  type to   <= tag * key,
  op   sampleto  _ <= dtag `*` dkey,
  type input  <= unit,
  type output <= bool
proof *.

clone ROc.SplitCodom as ROSc with 
  type to1 <- tag,
  type to2 <- key,
  op topair = fun (tk: tag * key) => tk,
  op ofpair = fun (tk: tag * key) => tk,
  op sampleto1 _ <- dtag,
  op sampleto2 _ <- dkey
  proof *.
realize topairK by rewrite /topair /ofpair.
realize ofpairK by rewrite /topair /ofpair.
realize sample_spec by rewrite /ofpair dprodC dmap_comp //=.

print Game1.
print ROc.


module (Red_ROM (D : A_GAKE) : ROc.IdealAll.RO_Distinguisher) (O : ROc.IdealAll.RO) = {
  module AKE_O : GAKE_out = Game1 with {
    proc h [ 
      ^tk<$ ~ {tk <@ O.get(x);}
      ^if -
    ] res ~ (tk)
  }

  proc distinguish() = {
    var b;
    AKE_O.init_mem();
    b <@ D(AKE_O).run();
    return b;
  }
}.

print Game2.

module (Red_ROM2 (D : A_GAKE) (O1 : ROSc.I1.RO) : ROSc.I2.RO_Distinguisher) (O2 : ROSc.I2.RO) = {
  module AKE_O : GAKE_out = Game2 with {
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
      ^match#Some.^match#Accepted.^if.^ks<$ -
      ^match#Some.^match#Accepted.^if.^if -
      ^match#Some.^match#Accepted.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
    ]

    proc s_test [
      ^match#Some.^match#Accepted.^if.^ks<$ -
      ^match#Some.^match#Accepted.^if.^if -
      ^match#Some.^match#Accepted.^if.^k<- ~ {ks <@ O2.get(x); k <- Some ks;}
    ]  
  }

  proc distinguish() = {
    var b;
    AKE_O.init_mem();
    b <@ D(AKE_O).run();
    return b;
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GAKE {-GAKE0, -Game0, -Game1, -Game2, -ROc.IdealAll.RO, -RO, -FRO, -ROSc.I1.RO, -ROSc.I2.RO, -ROSc.I1.FRO, -ROSc.I2.FRO, -Red_Coll, -BB.Sample, -Red_ROM, -Red_ROM2 }.

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
(* Step 3: Moving sampling of the shared key. *)
print ROSc.


lemma Step3 &m: Pr[ROc.IdealAll.MainD(Red_ROM(A), ROSc.RO_Pair(ROSc.I1.RO,ROSc.I2.RO)).distinguish() @ &m : res] = Pr[E_GAKE(Game2, A).run() @ &m : res].
proof.
byequiv (: ={glob A, glob Red_ROM2} ==> _)  => //.
proc*.

outline {1} [1] { r <@ ROSc.I2.MainD(Red_ROM2(A, ROSc.I1.RO), ROSc.I2.RO).distinguish(); }.

inline*. admit.

have ll : forall (c : pkey * pkey * s_id * pkey * pkey), is_lossless dkey by move=> _; exact dkey_ll.
rewrite equiv [{1} 1 (ROSc.I2.FullEager.RO_LRO (Red_ROM2(A, ROSc.I1.RO)) ll)].

admit. 
qed.

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
  call (: ={servers, c_smap, s_smap, kp_set, bad}(Game1, Red_ROM.AKE_O) /\ Game1.hm{1} = ROc.IdealAll.RO.m{2}); 
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
(* Step 0: Inlining everything. *)
lemma Step0 &m :
  Pr[E_GAKE(GAKE0(NTOR_S(RO), NTOR_C(RO), RO), A).run() @ &m : res] = Pr[E_GAKE(Game0, A).run() @ &m : res].
proof. 
byequiv => //.
proc; inline*.
call (: ={servers, c_smap, s_smap}(GAKEb, Game0) /\ RO.m{1} = Game0.hm{2}); try sim />.

- proc; inline*; auto; if => //; auto => /#.

- proc; inline*. 
  sp; if => //.
  sp; match = => // [|st]; 1:by auto.
  by match = => // st' pt' ir'; auto.

- proc; inline*.
  sp; match = => // sk.
  match = => //.
  match Some {1} 4.
  + by auto=> /> _ _ _ _; exists (b{m0}, sk, None).
  match Some {1} ^match=> //; 1: by auto=> /> /#.
  by auto => />.

- proc; inline*; auto=> />.
  sp; match = => //; 1: auto.
  by match = => //; 1: auto.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 1: Remove collisions in ephemeral and long-term keys. *)
lemma Step1 &m: `| Pr[E_GAKE(Game0, A).run() @ &m : res] - Pr[E_GAKE(Game1, A).run() @ &m : res] | <= Pr[E_GAKE(Game0, A).run() @ &m : Game0.bad].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game1.bad => //; first last.
+ by rewrite eq_iff.
symmetry; proc; inline*.
call (: Game1.bad
      , ={servers, c_smap, s_smap, kp_set, hm, bad}(Game0, Game1)
      , ={bad}(Game0, Game1)) => //. 

- exact A_ll.

- by proc; auto.
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

- proc; auto => />.
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

- proc; inline*.
  sp; match = => //. 
  move => sk.
  match = => //.
  + seq 1 1: (#pre /\ ={kp}); 1: by auto.
  sp 0 1; if{2}.
  + by auto => />. 
  auto.
- move => &2 bad.
  proc; inline*; sp; match; auto => />.
  match; auto => />.
  rewrite dkp_ll weight_dprod dkey_ll dtag_ll. 
  by smt().
- move => &1. 
  proc; sp; match; auto => />.
  match; 2: by auto => />. 
  rcondf ^if; 1: by auto => />. 
  auto => />.
  by rewrite dkp_ll.

- sim />.
- move => &2 bad.
  proc; inline*.
  sp; match; auto. 
  match; auto => />.
  by rewrite weight_dprod dkey_ll dtag_ll.
- move => &1.
  proc; inline*; auto => />.
  sp; match; auto.
  match; auto.
  by rewrite weight_dprod dkey_ll dtag_ll.

- sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

- sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  match; auto => />.

auto => />.
move => rl rr al bl csl hml kpl ssl sl ar br csr hmr kpr ssr sr. 
by case : (!br) => />.
qed.


(* ------------------------------------------------------------------------------------------ *)
(* Step 1b: Bound the bad event. *)
lemma Step1b &m: Pr[E_GAKE(Game0, A).run() @ &m : Game0.bad] <= ((q_is + q_m1 + q_m2) ^ 2)%r * mu1 dkp (mode dkp).
proof.
apply (StdOrder.RealOrder.ler_trans Pr[BB.Exp(BB.Sample, Red_Coll(A)).main() @ &m : ! uniq BB.Sample.l]); first last.
+ apply (BB.pr_collision_q2 (Red_Coll(A))).
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
  + by proc; sp; match; 1: auto; match; auto => /#.
  + by proc; sp; match; 1: auto; match; auto => /#.
  auto => /#.
byequiv => //.
proc; inline.
call (:
 ={hm, outs_h, servers, c_smap, s_smap, kp_set, bad, bad_ro}(Game0, Red_Coll_O_AKE(BB.Sample))
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


end section.




