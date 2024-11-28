require import AllCore FSet FMap Distr NTOR Games.
import GAKEc.

(* ------------------------------------------------------------------------------------------ *)
(* Reductions *)
(* ------------------------------------------------------------------------------------------ *)

    
(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GAKE {-GAKE0, -Game0, -Game1}.

declare axiom A_ll:
forall (G <: GAKE_out{-A}),
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
  islossless G.c_test => islossless G.s_test => islossless A(G).run.


lemma Step0 &m :
  Pr[E_GAKE(GAKE0(NTOR_S, NTOR_C), A).run() @ &m : res] = Pr[E_GAKE(Game0, A).run() @ &m : res].
proof. 
byequiv => //.
proc; inline*.
sim (: ={servers, c_smap, s_smap}(GAKE0, Game0)).

- proc; inline*; by auto => /#.

- proc; inline*.
  sp; match = => //.
  move => sk.
  match = => //.
  match Some {1} 4.
   + by auto; smt(mem_set).
  match Some {1} 10.
  + by auto; smt().
  auto => />.

- proc; inline*. 
  sp; if => //.
  sp; match = => //.
  auto => />. 
  move => st.
  match = => //.
  move => st' pt' ir'.
  auto => />.

- proc; inline*.
  if => //.
  auto => /#.
qed.

lemma Step1 &m: `| Pr[E_GAKE(Game0, A).run() @ &m : res] - Pr[E_GAKE(Game1, A).run() @ &m : res] | <= Pr[E_GAKE(Game1, A).run() @ &m : Game1.bad].
proof.
byequiv (: _ ==> _) : Game0.bad => //; first last.
+ move=> &1 &2.
  by case: (Game1.bad{2}).
proc; inline*.
call (: Game1.bad, ={servers, c_smap, s_smap, kp_set, bad}(Game0, Game1), ={bad}(Game0, Game1)) => //. 

- exact A_ll.

- proc; auto => />.
- move => &2 bad.
  proc; auto => />. 
- move => &1. 
  proc; auto => />.

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

- proc.
  sp; match = => //. 
  move => sk.
  match = => //.
  + seq 1 1: (#pre /\ ={kp}); 1: by auto.
    by sp 0 1; if{2}; auto => />.
- move => &2 bad.
  proc; sp; match; auto => />.
  match; auto => />.
  rewrite dkp_ll. 
  by smt().
- move => &1. 
  proc; sp; match; auto => />.
  match; auto => />.
  by rewrite dkp_ll.

- proc; auto => />. 
  by smt().
- move => &2 bad.
  proc; auto => />.
  by smt().
- move => &1.
  proc; auto => />.
  by smt().

- proc; auto => />. 
  by smt().
- move => &2 bad.
  proc; auto => />.
  by smt().
- move => &1.
  proc; auto => />.
  by smt().

- proc; auto => />. 
  by smt().
- move => &2 bad.
  proc; auto => />.
  by smt().
- move => &1.
  proc; auto => />.
  by smt().

- proc; auto => />. 
  by smt().
- move => &2 bad.
  proc; auto => />.
  by smt().
- move => &1.
  proc; auto => />.
  by smt().

- proc; auto => />. 
  by smt().
- move => &2 bad.
  proc; auto => />.
  by smt().
- move => &1.
  proc; auto => />.
  by smt().

- proc; auto => />. 
  by smt().
- move => &2 bad.
  proc; auto => />.
  by smt().
- move => &1.
  proc; auto => />.
  by smt().

- proc; auto => />. 
  by smt().
- move => &2 bad.
  proc; auto => />.
  by smt().
- move => &1.
  proc; auto => />.
  by smt().

- proc; auto => />. 
  by smt().
- move => &2 bad.
  proc; auto => />.
  by smt().
- move => &1.
  proc; auto => />.
  by smt().

auto => />.
move => rl rr al bl dl pl kpl sl ar br dr pr kpr sr. 
by case : (!br) => />.
qed.

end section.
