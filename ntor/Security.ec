require import AllCore FSet FMap Distr List NTOR Games.
import GAKEc.
require Birthday.


print mem_set.

(* ------------------------------------------------------------------------------------------ *)
(* Reductions *)
(* ------------------------------------------------------------------------------------------ *)

 module RO_h = {
  var cache : (pkey * pkey * s_id * pkey * pkey, tag * key) fmap 

  proc init(): unit = {
    cache <- empty;
  }

  proc get(x: pkey * pkey * s_id * pkey * pkey) : tag * key = {
    var t, k;

    t <$ dtag;
    k <$ dkey;
    if (x \notin cache) {
      cache.[x] <- (t, k);
    }
    
    return oget cache.[x];
  }
}.


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
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GAKE {-GAKE0, -Game0, -Game1, -Game2, -RO_h, -Red_Coll, -BB.Sample }.

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
(* Step 2: Remove collisions in the random oracle output. *)
lemma Step2 &m: `| Pr[E_GAKE(Game1, A).run() @ &m : res] - Pr[E_GAKE(Game2, A).run() @ &m : res] | <= Pr[E_GAKE(Game1, A).run() @ &m : Game1.bad_ro].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game2.bad_ro => //; first last.
+ by rewrite eq_iff.
symmetry; proc; inline*.
call (: Game2.bad_ro
      , ={servers, c_smap, s_smap, kp_set, hm, outs_h, bad, bad_ro}(Game1, Game2)
      , ={bad_ro}(Game1, Game2)) => //. 

- exact A_ll.

- proc. 
  seq 2 2: (#pre /\ ={t, k}); 1: by auto.
  sp 0 1; if{2}.
  + by sp 2 1; if => //; auto => />.
  by auto => />.
- move => &2 bad; proc; auto => />. 
  rewrite dkey_ll dtag_ll. smt().
- move => &1; proc; auto => />.
  by rewrite dkey_ll dtag_ll.

- proc; if => //; auto => />.
- move => &2 bad.
  proc; if; auto => />.
  by rewrite dkp_ll.
- move => &1. 
  proc; if; auto => />. 
  by rewrite dkp_ll.  

- proc; auto => />.
- move => &2 bad.
  proc; auto => />.
- move => &1. 
  proc; auto => />. 

- proc; sp; if => //; sp; match = => // [|st]. 
  + sim />. 
  match =; auto => />.
- move => &2 bad.
  proc; sp; if; auto => />.
  sp; match.
  + auto => />.  
    by rewrite dkp_ll.
  match; auto => />.
- move => &1. 
  proc; sp; if; auto => />.
  sp; match. 
  + auto => />.
    by rewrite dkp_ll. 
  match; auto => />.

- proc; inline; sp; match = => // sk. 
  match = => //.
  seq 1 1: (#pre /\ ={kp}); 1: by auto.
  sp; if => //.  
  sp.
  seq 2 2: (#pre /\ ={t, k}); 1: by auto => />.
  sp 2 1; if{2}.
  + auto => />.
  auto => />.
- move => &2 bad_ro.
  proc; inline; sp; match; auto => />.
  match.
  + seq 1: (#pre) (1%r) (1%r) (0%r) (1%r) (kp \in dkp) => //. auto.
    - by auto; rewrite dkp_ll.
    - sp; if => //.
      auto => />.
      by rewrite dkey_ll dtag_ll /#.
    - by rnd pred0; skip => />; rewrite mu0.
  by skip => />.
- move => &1. 
  proc; inline; sp; match; auto => />.
  match. 
  + seq 1: (#pre) (1%r) (1%r) (0%r) (1%r) (kp \in dkp) => //. auto.
    - by auto; rewrite dkp_ll.
    - sp; if => //.
      + auto => />.
        by rewrite dkey_ll dtag_ll /#.
      by skip => />.
    - by rnd pred0; skip => />; rewrite mu0.
  by skip => />.

- proc; inline; sp; match = => // prr.
  match = => // st pt ir.
  sp; seq 2 2: (#pre /\ ={t, k}); 1: by auto => />.
  sp 0 1; if{2}.
  + auto => />.
  by auto => />.
- move => &2 bad_ro.
  proc; inline*.
  sp; match; auto => />. 
  match; auto => />.
  by rewrite dkey_ll dtag_ll /#.
- move => &1.
  proc; inline*; auto => />.
  sp; match; auto => />.
  match; auto => />.
  by rewrite dkey_ll dtag_ll.

- by sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  by match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  by match; auto => />.

- by sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  by match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  by match; auto => />.

- by sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  by match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  by match; auto => />.

- by sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  by match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  by match; auto => />.

- by sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  by match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  by match; auto => />.

- by sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  by match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  by match; auto => />.

- by sim />.
- move => &2 bad.
  proc; sp; match; 1: by auto. 
  by match; auto => />.
- move => &1.
  proc; sp; match; 1: by auto. 
  by match; auto => />.

auto => />.
move => rl rr al bl brl csl hml kpl hsl ssl sl ar br brr csr hmr kpr hsr ssr sr. 
by case : (!brr) => />.
qed.



(* ------------------------------------------------------------------------------------------ *)
(* Step 0: Inlining everything. *)
lemma Step0 &m :
  Pr[E_GAKE(GAKE0(NTOR_S(RO_h), NTOR_C(RO_h), RO_h), A).run() @ &m : res] = Pr[E_GAKE(Game0, A).run() @ &m : res].
proof. 
byequiv => //.
proc; inline*.
call (: ={servers, c_smap, s_smap}(GAKE0, Game0) /\ RO_h.cache{1} = Game0.hm{2}); try sim />.

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
  match Some {1} 14=> //; 1: by auto=> /> /#.
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
      , ={servers, c_smap, s_smap, kp_set, hm, outs_h, bad, bad_ro}(Game0, Game1)
      , ={bad}(Game0, Game1)) => //. 

- exact A_ll.

- by proc; auto.
- move => &2 bad; proc; auto => />. 
  by rewrite dkey_ll dtag_ll.
- move => &1; proc; auto.
  by rewrite dkey_ll dtag_ll.

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
  rewrite dkp_ll dkey_ll dtag_ll. 
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
  by rewrite dkey_ll dtag_ll.
- move => &1.
  proc; inline*; auto => />.
  sp; match; auto.
  match; auto.
  by rewrite dkey_ll dtag_ll.

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
move => rl rr al bl brl csl hml kpl hsl ssl sl ar br brr csr hmr kpr hsr ssr sr. 
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




