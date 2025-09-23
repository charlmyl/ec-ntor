require import AllCore FSet FMap Distr DProd List SplitRO NTOR.
(*   *) import GAKEc HROc.
require (*  *) DiffieHellman.
(*   *) import StdBigop.Bigreal.BRA StdOrder.RealOrder DH.G DH.GP DH.FD DH.GP.ZModE.

(* Introduce stop in original game *)
module GAKEb_st (S: Server) (C: Client) (H : GAKEc.HROc.RO) = {
  var b0 : bool 

  var servers : (s_id, server_state) fmap
  var unreg_ro : (pkey * pkey * s_id * pkey * pkey) fset
  var pk_set : pkey fset
  var stop : bool

  var c_smap: (int, pr_st_client instance_state) fmap
  var s_smap: (s_id * int, pr_st_server instance_state) fmap
  
  var tested: int option

  proc init_mem(b: bool) : unit = {
    b0 <- b;
    H.init();
    unreg_ro <- fset0;
    servers <- empty;
    pk_set <- fset0;
    stop <- false;
    c_smap <- empty;
    s_smap <- empty;
    tested <- None;
  }

  (* random oracle *)
  proc h(x: h_input) = {
    var r;

    if (x.`3 \in servers /\ !get_sr_ltk (oget servers.[x.`3])) {
      stop <- stop \/ x \in unreg_ro;
    } else {
      unreg_ro <- unreg_ro `|` fset1 x; (* do I care about copies in this set? *)
    }

    r <@ H.get(x);

    if (x.`4 \notin pk_set) {
      pk_set <- pk_set `|` fset1 x.`4;
    }
    if (x.`5 \notin pk_set) {
      pk_set <- pk_set `|` fset1 x.`5;
    }

    return r;
  }
  
  (* server management *)
  proc init_s(b: s_id) : pkey option = {
    var kp;

    if (b \notin servers) {
      kp <@ S.keygen();
      stop <- stop \/ kp.`1 \in pk_set;
      pk_set <- pk_set `|` fset1 kp.`1;
      servers.[b] <- Honest kp;
    }
    return omap get_pkey servers.[b];
  }

  proc set_cert(b: s_id, pk: pkey) : unit option = {
    var r <- None;

    if (b \notin servers) {
      servers.[b] <- Dishonest pk;
      pk_set <- pk_set `|` fset1 pk;
      r <- Some ();
    }
    return r;
  }

  proc send_msg1(i: int, m1: s_id) : pkey option = {
    var st, pk_b, st', m2;
    var r <- None;

    st <- c_smap.[i];
    if (m1 \in servers) {
      pk_b <- get_pkey (oget servers.[m1]);
      match st with
      | None => {
          (st', m2) <@ C.new_session(m1, pk_b);
           c_smap.[i] <- Pending st' m2 (false, false, false);
          r <- Some m2;
        }
      | Some st => {
          match st with
          | Pending st pt ir => c_smap.[i] <- Aborted (Some st) (Some (pt, None)) ir;
          | Accepted _ _ _ _ => { }
          | Aborted _ _ _ => { }
          end;
        }
      end;
    }

    if (r <> None) {
      stop <- stop \/ (oget r \in pk_set);
      pk_set <- pk_set `|` fset1 (oget r);
    }

    return r;
  }

  proc send_msg2(b: s_id, j: int, m2: pkey) : (pkey * tag) option = {
    var sko, resp, st', k, m3;
    var r <- None;

    sko <- obind get_skey servers.[b];

    if (sko is Some sk) (* Server was initialised as honest *) {
      match s_smap.[b, j] with
      | None => {
          resp <@ S.respond_session(Some (b, sk, None), m2);
          if (resp is Some r') {
            (st', m3, k) <- r';
            s_smap.[(b, j)] <- Accepted st' (m2, Some m3) k (false, false, false);
            r <- Some m3;
          } else {
            s_smap.[(b, j)] <- Aborted None (Some (m2, None)) (false, false, false);
          }
        }
      | Some st => { (* only completed sessions would be stored, and those can't be aborted; do nothing *) }
      end;
      if (m2 \notin pk_set) {
        pk_set <- pk_set `|` fset1 m2;
      }

      if (r <> None) {
        stop <- stop \/ (oget r).`1 \in pk_set;
        pk_set <- pk_set `|` fset1 (oget r).`1;
      }
    }

    return r;
  }

  proc send_msg3(i: int, m3: pkey * tag) : unit option = {
    var resp, st', k;
    var r <- None;

    if (m3.`1 \notin pk_set) {
      pk_set <- pk_set `|` fset1 m3.`1;
    }

    match c_smap.[i] with
    | None => { } (* Abort? *)
    | Some st => {
        match st with
        | Pending st pt ir => {
            resp <@ C.complete_session(st, m3);
            if (resp is Some r') {
              (st', k) <- r';
              c_smap.[i] <- Accepted st' (pt, Some m3) k ir;
              r <- Some ();
            } else {
              c_smap.[i] <- Aborted (Some st) (Some (pt, Some m3)) ir;
            }
          }
        | Accepted _ _ _ _ => { }
        | Aborted _ _ _ => { }
        end;
      }
    end;
    return r;
  }

  (* reveal and test *)
  proc c_rev_skey(i: int) : key option = {
    var k <- None;

    match c_smap.[i] with
    | None => { }
    | Some st => {
        (* only accepted client instances that are not tested and 
           that not only have tested partners can be sesskey revealed *)
        if (st is Accepted st' t' k' ir') {
          if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_c t' s_smap = Some false)) {
            k <- Some k';
            c_smap.[i] <- set_ir_sess (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }

  proc s_rev_skey(b: s_id, j: int) : key option = {
    var k <- None;


    match s_smap.[(b, j)] with
    | None => { }
    | Some st => {
        (* only accepted server instances that are not tested and 
           that not only have tested partners can be sesskey revealed *)
        if (st is Accepted st' t' k' ir') {
          if (!(get_ir_test (oget s_smap.[b, j]) \/ untested_partner_s t' c_smap = Some false)) {
            k <- Some k';
            s_smap.[(b, j)] <- set_ir_sess (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }

  proc rev_ltkey(b: s_id) : skey option = {
    var ltk <- None;

    match servers.[b] with
    | None => { }
    | Some st => {
        (* a server can be ltkey revealed if no instance of it is ephkey revealed 
           in case that instance or all its partners are tested *) 
        if (st is Honest kp) {
          if (forall j,
                (b, j) \in s_smap (* just checking instances of b *)
                => !(   (   get_ir_test (oget s_smap.[b, j])
                            (* This is always OK (get_trace always Some on server side *)
                         \/ untested_partner_s (oget (get_trace (oget s_smap.[b, j]))) c_smap = Some false)
                     /\ get_ir_eph (oget s_smap.[b,j]))) {
            ltk <- Some kp.`2; 
            servers.[b] <- Corrupt kp; 
          }
        }
      }
    end;
    return ltk;
  }

  proc c_rev_ephkey(i: int) : skey option = {
    var ek <- None;

    match c_smap.[i] with
    | None => { }
    | Some st => {
        match st with
          (* client instances can be ephkey revealed when pending if there isn't 
             a tested origin partner (agreeing on first message *)
        | Pending st pk_e ir => {
            if (untested_origins_c (pk_e, None) s_smap <> Some false) {
              ek <- Some (get_eph_c st);
              c_smap.[i] <- set_ir_eph (Pending st pk_e ir);
            }
          }
          (* accepted client instamces can only be ephkey revealed when not tested and 
             if not all partners are tested *)
        | Accepted st t k ir => {
            if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_c t s_smap = Some false)) {
              ek <- Some (get_eph_c st);
              c_smap.[i] <- set_ir_eph (Accepted st t k ir);
            }
          }
        | Aborted _ _ _ => {  }
        end;
      }
    end;
    return ek;
  }

  proc s_rev_ephkey(b: s_id, j: int) : skey option = {
    var ek <- None;

    match s_smap.[b, j] with
    | None => { }
    | Some st => {
        (* only accepted server instances that are not ltkey revealed in case they 
           or all partners are tested can be ephkey revealed *)
        if (st is Accepted st t k ir) { (* No Pending on Server side *)
          if (!((   get_ir_test (oget s_smap.[b, j])
                 \/ untested_partner_s t c_smap = Some false)
                /\ get_sr_ltk (oget servers.[b]))) {
            ek <- Some (get_eph_s st);
            s_smap.[(b, j)] <- set_ir_eph (Accepted st t k ir);
          }
        }
      }
    end;
    return ek;
  }

  proc c_test(i: int) : key option = {
    var ks;
    var k <- None;

    if (tested = None) {
      match c_smap.[i] with
      | None => { }
      | Some st => {
          (* only accepted client instances that are not sesskey revealed, not ephkey revealed 
             and not all partner instances are unfresh can be tested *)
          if (st is Accepted st' t' k' ir') {
            if (!(   get_ir_sess (oget c_smap.[i]) \/ get_ir_eph (oget c_smap.[i]) 
                  \/ fresh_partner_c t' s_smap servers = Some false)) {
              if (b0 = false) {
                k <- Some k';
                c_smap.[i] <- set_ir_test (Accepted st' t' k' ir');
              } else {
                ks <$ dkey;
                k <- Some ks;
                c_smap.[i] <- set_ir_test (Accepted st' t' k' ir');
              }
              tested <- Some i;
           }
          }
        }
      end;
    }
    return k;
  }

  proc s_test(b: s_id, j: int) : key option = {
    var ks;
    var k <- None;

    if (tested = None) {
      match s_smap.[(b, j)] with
      | None => { }
      | Some st => {
          (* only accepted server instances that are not sesskey revealed, not trivially broken
             and not all partner instances are unfresh can be tested *)
          if (st is Accepted st' t' k' ir') {
            if (!(   get_ir_sess (oget s_smap.[b, j]) 
                  \/ (get_ir_eph (oget s_smap.[b, j]) /\ get_sr_ltk (oget servers.[b]))
                  \/ fresh_partner_s t' c_smap = Some false)) {
              if (b0 = false) {
                k <- Some k';
                s_smap.[(b, j)] <- set_ir_test (Accepted st' t' k' ir');
              } else {
                ks <$ dkey;
                k <- Some ks;
                s_smap.[(b, j)] <- set_ir_test (Accepted st' t' k' ir');
              }
              tested <- Some (pick (get_fresh_partners_s t' c_smap));
            }
          }
        }
      end;
    }
    return k;
  }
}.


(* ------------------------------------------------------------------------------------------ *)
(* Modified game without server ids *)
require import NTOR_nosid.
import GAKE_mod.

op rem_sid_c (s : pr_st_client GAKEc.instance_state) : pr_st_client_mod instance_state =
match s with 
| GAKEc.Pending st pt ir => GAKE_mod.Pending (st.`2, st.`3) pt ir
| GAKEc.Accepted st t k ir => GAKE_mod.Accepted (st.`2, st.`3) t k ir
| GAKEc.Aborted st t ir => GAKE_mod.Aborted (Some ((oget st).`2, (oget st).`3)) t ir
end.

op rem_sid_s (s : pr_st_server GAKEc.instance_state) : pr_st_server_mod instance_state =
match s with 
| GAKEc.Pending st pt ir => GAKE_mod.Pending (st.`2, st.`3) pt ir
| GAKEc.Accepted st t k ir => GAKE_mod.Accepted (st.`2, st.`3) t k ir
| GAKEc.Aborted st t ir => GAKE_mod.Aborted (Some ((oget st).`2, (oget st).`3)) t ir
end.


(* ------------------------------------------------------------------------------------------ *)
(* Reduction preventing collisions and prediction of public keys  *)
type server_state_mod = [
  Inner of pkey
| Outer of pkey
].

op get_pkey_mod s_st =
with s_st = Inner pk => pk
with s_st = Outer pk => pk.

op get_sr_mod s_st : bool =
with s_st = Inner _ => false
with s_st = Outer _ => true.

print GAKEc.GAKE_out.
print GAKE_mod.Pending.
print pr_st_client_mod.

module (Meta_Red (A : GAKEc.A_GAKE) : GAKE_mod.A_GAKE) (O : GAKE_mod.GAKE_out) = {
  module O_GAKE : GAKEc.GAKE_out = {
    var unreg_ro : (pkey * pkey * s_id * pkey * pkey, (tag * key)) fmap

    var dhc_smap : (int, pr_st_client_mod instance_state) fmap
    var c_inst : (int, bool) fmap (* true for honest partner *)
    var hon_p : (int, pkey) fmap

    var sid_pk : (s_id, server_state_mod) fmap
    var pk_set : pkey fset
  (*  var pred_ce : pkey fset
    var pred_se : pkey fset*)
    
    var stop : bool

    proc h(x : GAKEc.h_input) = {
      var pk, tk;
      var r <- (witness, witness);

      if (!stop) {
        if (x.`3 \in sid_pk /\ !get_sr_mod (oget sid_pk.[x.`3])) {
          stop <- stop \/ x \in unreg_ro;
          pk <- get_pkey_mod (oget sid_pk.[x.`3]); 
          r <@ O.h((x.`1, x.`2, pk, x.`4, x.`5));
        } else {
          tk <$ dtag `*` dkey;
          if (x \notin unreg_ro) {
            unreg_ro.[x] <- tk;
          }
          r <- oget unreg_ro.[x];
        }

        if (x.`4 \notin pk_set) {
          pk_set <- pk_set `|` fset1 x.`4;
        }
        if (x.`5 \notin pk_set) {
          pk_set <- pk_set `|` fset1 x.`5;
        }
      }

      return r;
    }

    proc init_s(b : s_id): pkey option = {
      var pko;
      var r <- None;

      if (!stop) {
        if (b \notin sid_pk) {
          pko <@ O.init_s();
          if (pko is Some pk) {
            stop <- stop \/ pk \in pk_set;
            pk_set <- pk_set `|` fset1 pk;
            sid_pk.[b] <- Inner pk;
          } else {
            stop <- stop \/ true; (* there was a collision in sampling *)
          }
        }
        r <- Some (get_pkey_mod (oget sid_pk.[b]));
      }
      return r;
    }

    proc set_cert(b: s_id, pk: pkey) = {
      var r <- None;

      if (!stop /\ b \notin sid_pk) {
        sid_pk.[b] <- Outer pk;
        pk_set <- pk_set `|` fset1 pk;
        r <- Some ();
      }

      return r;
    }

    proc send_msg1(i: int, m1: s_id) = {
      var pk_s, st_dh, st, sk_ce, pk_ce, h_pk; 
      var r <- None;

      if (!stop /\ m1 \in sid_pk) {
        pk_s <- oget sid_pk.[m1];
        match pk_s with 
        | Inner pk => {
            if (c_inst.[i] = Some true \/ i \notin c_inst) {
              r <@ O.send_msg1(i, pk);
              c_inst.[i] <- true;
              hon_p.[i] <- pk;
            } else {
              st_dh <- oget dhc_smap.[i];
              match st_dh with
                  | GAKE_mod.Pending st pt ir => dhc_smap.[i] <- GAKE_mod.Aborted (Some st) (Some (pt, None)) ir;
                  | GAKE_mod.Accepted _ _ _ _ => { }
                  | GAKE_mod.Aborted _ _ _ => { }
              end;
            }
          }
        | Outer pk => {
            if (c_inst.[i] = Some false \/ i \notin c_inst) {
              st <- dhc_smap.[i];
              match st with
              | None => {
                  sk_ce <$ dt;
                  pk_ce <- g ^ sk_ce;
                  r <- Some pk_ce;
                  dhc_smap.[i] <- GAKE_mod.Pending (pk, sk_ce) pk_ce (false, false, false);
                }
              | Some st => {
                  match st with
                  | GAKE_mod.Pending st pt ir => dhc_smap.[i] <- GAKE_mod.Aborted (Some st) (Some (pt, None)) ir;
                  | GAKE_mod.Accepted _ _ _ _ => { }
                  | GAKE_mod.Aborted _ _ _ => { }
                  end;
                }
              end;
              c_inst.[i] <- false;
            } else {
              h_pk <- oget hon_p.[i];
              r <@ O.send_msg1(i, h_pk);
            }
          }
        end;

        if (r <> None) {
          stop <- stop \/ (oget r \in pk_set);
          pk_set <- pk_set `|` fset1 (oget r);
        }
      }

      return r;
    }

    proc send_msg2(b: s_id, j: int, m2: pkey) = {
      var pk_s; 
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        pk_s <- oget sid_pk.[b];
        match pk_s with 
        | Inner pk => {
            r <@ O.send_msg2(pk, j, m2);
            if (m2 \notin pk_set) {
              pk_set <- pk_set `|` fset1 m2;
            }
            if (r <> None) {
              stop <- stop \/ ((oget r).`1 \in pk_set);
              pk_set <- pk_set `|` fset1 (oget r).`1;  
            }
          }
        | Outer pk => {}
        end;
      }

      return r;
    }

    proc send_msg3(i: int, m3: pkey * tag) = {
      var r <- None;

      if (!stop) {
         if (m3.`1 \notin pk_set) {
           pk_set <- pk_set `|` fset1 m3.`1;
         }

         r <@ O.send_msg3(i, m3);
      }

      return r;
    }

    proc c_rev_skey(i: int) = {
      var r <- None;

      if (!stop) {
        r <@ O.c_rev_skey(i);
      }

      return r;
    }

    proc s_rev_skey(b: s_id, j: int) = {
      var pk;
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        pk <- get_pkey_mod (oget sid_pk.[b]);
        r <@ O.s_rev_skey(pk, j);
      }

      return r;     
    }

    proc rev_ltkey(b: s_id) = {
      var pk;
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        pk <- get_pkey_mod (oget sid_pk.[b]);
        r <@ O.rev_ltkey(pk);
        if (r <> None) {
          sid_pk.[b] <- Outer pk; (* Do I need to know that this was honest before? *)
        }
      }

      return r;
    }

    proc c_rev_ephkey(i : int) = {
      var r <- None;

      if (!stop) {
        r <@ O.c_rev_ephkey(i);
      }

      return r;
    }

    proc s_rev_ephkey(b: s_id, j: int) = {
      var pk;
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        pk <- get_pkey_mod (oget sid_pk.[b]);
        r <@ O.s_rev_ephkey(pk, j);
      }

      return r;     
    }

    proc c_test(i : int) = {
      var r <- None;

      if (!stop) {
        r <@ O.c_test(i);
      }

      return r;
    }

    proc s_test(b: s_id, j: int) = {
      var pk;
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        if (! get_sr_mod (oget sid_pk.[b])) {
          pk <- get_pkey_mod (oget sid_pk.[b]);
          r <@ O.s_test(pk, j);
        }
      }

      return r;
    }
  }

  proc run() : bool = {
    var b';

    O_GAKE.unreg_ro <- empty;
    O_GAKE.sid_pk <- empty;
    O_GAKE.pk_set <- fset0;
    O_GAKE.stop <- false;
    O_GAKE.dhc_smap <- empty;
    O_GAKE.c_inst <- empty;
    O_GAKE.hon_p <- empty;

    b' <@ A(O_GAKE).run();

    return b';
  }
}.



(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: GAKEc.A_GAKE {-GAKE_mod.HROc.RO, -GAKEc.HROc.RO, -Meta_Red, -GAKEc.GAKEb, -GAKEb_st, -GAKE_mod.GAKEb }.

declare axiom A_ll (G <: GAKEc.GAKE_out{-A}):
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


lemma gake_st bit &m: Pr[GAKEc.E_GAKE(GAKEc.GAKEb(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), A).run(bit) @ &m : res] =  Pr[GAKEc.E_GAKE(GAKEb_st(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), A).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline.
call (: ={b0, servers, c_smap, s_smap, tested}(GAKEc.GAKEb, GAKEb_st) /\ ={m}(GAKEc.HROc.RO, GAKEc.HROc.RO)); try sim />.

+ proc; inline.
  auto => />.
qed.


lemma gake_st_mod bit &m: `| Pr[GAKEc.E_GAKE(GAKEb_st(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), A).run(bit) @ &m : res] - Pr[GAKE_mod.E_GAKE(GAKE_mod.GAKEb(NTOR_S_mod(GAKE_mod.HROc.RO), NTOR_C_mod(GAKE_mod.HROc.RO), GAKE_mod.HROc.RO), Meta_Red(A)).run(bit) @ &m : res] | <= Pr[GAKEc.E_GAKE(GAKEb_st(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), A).run(bit) @ &m : GAKEb_st.stop].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Meta_Red.O_GAKE.stop => //; first last.
+ smt().
symmetry; proc; inline*.
wp; call (: Meta_Red.O_GAKE.stop
          , ={b0, tested}(GAKEb_st, GAKE_mod.GAKEb) /\ ={pk_set, stop}(GAKEb_st, Meta_Red.O_GAKE)
               /\ (forall x, x \in GAKEc.HROc.RO.m{1} => x.`3 \in Meta_Red.O_GAKE.sid_pk{2} => x \notin Meta_Red.O_GAKE.unreg_ro{2}
                    => GAKEc.HROc.RO.m{1}.[x] = GAKE_mod.HROc.RO.m{2}.[(x.`1, x.`2, get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[x.`3]), x.`4, x.`5)])
               /\ (forall x, x \in GAKEc.HROc.RO.m{1} => x.`3 \notin Meta_Red.O_GAKE.sid_pk{2} \/ get_sr_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[x.`3])
                    => GAKEc.HROc.RO.m{1}.[x] =  Meta_Red.O_GAKE.unreg_ro{2}.[x])
               /\ (forall x, x \notin GAKEc.HROc.RO.m{1} => x.`3 \in Meta_Red.O_GAKE.sid_pk{2} => !get_sr_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[x.`3])
                    => (x.`1, x.`2, get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[x.`3]), x.`4, x.`5) \notin GAKE_mod.HROc.RO.m{2})
               /\ (forall x, x \notin GAKEc.HROc.RO.m{1} => x \notin  Meta_Red.O_GAKE.unreg_ro{2})
              (* /\ (forall x, x \in GAKE_mod.HROc.RO.m{2} => x.`3 \in GAKE_mod.GAKEb.servers{2})*)
               /\ (forall b1 b2, b1 \in Meta_Red.O_GAKE.sid_pk{2} => b2 \in Meta_Red.O_GAKE.sid_pk{2} 
                    => !get_sr_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b1])
                    => oget Meta_Red.O_GAKE.sid_pk{2}.[b1] = oget Meta_Red.O_GAKE.sid_pk{2}.[b2]
                    => b1 = b2)
               /\ (forall i, i \in GAKEb_st.c_smap{1} => i \in Meta_Red.O_GAKE.c_inst{2})
               /\ (forall i, i \in Meta_Red.O_GAKE.c_inst{2} => (Meta_Red.O_GAKE.c_inst{2}.[i] = Some true /\ i \in GAKE_mod.GAKEb.c_smap{2})
                                           \/ (Meta_Red.O_GAKE.c_inst{2}.[i] = Some false /\ i \in Meta_Red.O_GAKE.dhc_smap{2}))
               /\ (forall i, i \in GAKE_mod.GAKEb.c_smap{2} => i \in Meta_Red.O_GAKE.c_inst{2} /\ Meta_Red.O_GAKE.c_inst{2}.[i] = Some true /\ i \in GAKEb_st.c_smap{1}
                                      /\ rem_sid_c (oget GAKEb_st.c_smap{1}.[i]) = oget GAKE_mod.GAKEb.c_smap{2}.[i])
               /\ (forall i, i \in Meta_Red.O_GAKE.dhc_smap{2} => i \in Meta_Red.O_GAKE.c_inst{2} /\ Meta_Red.O_GAKE.c_inst{2}.[i] = Some false /\ i \in GAKEb_st.c_smap{1}
                                      /\ rem_sid_c (oget GAKEb_st.c_smap{1}.[i]) = oget Meta_Red.O_GAKE.dhc_smap{2}.[i])
               /\ (forall i, Meta_Red.O_GAKE.c_inst{2}.[i{2}] = Some true => oget Meta_Red.O_GAKE.hon_p{2}.[i] \in GAKE_mod.GAKEb.servers{2})
               /\ (forall b j, (b, j) \in GAKEb_st.s_smap{1} => b \in Meta_Red.O_GAKE.sid_pk{2} /\ !get_sr_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b])
                                      /\ (get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b]), j) \in GAKE_mod.GAKEb.s_smap{2}
                                      /\ rem_sid_s (oget GAKEb_st.s_smap{1}.[(b, j)]) = oget GAKE_mod.GAKEb.s_smap{2}.[(get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b]), j)])
               /\ (forall b j, (b, j) \notin GAKEb_st.s_smap{1} => b \in Meta_Red.O_GAKE.sid_pk{2} => !get_sr_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b])
                    => (get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b]), j) \notin GAKE_mod.GAKEb.s_smap{2})
               /\ (forall x, x \in GAKEb_st.unreg_ro{1} <=> x \in Meta_Red.O_GAKE.unreg_ro{2})
               /\ (forall b, b \in GAKEb_st.servers{1} <=> b \in Meta_Red.O_GAKE.sid_pk{2})
               /\ (forall b, b \in GAKEb_st.servers{1} => get_pkey (oget GAKEb_st.servers{1}.[b]) = get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b])
                                      /\ get_sr_ltk (oget GAKEb_st.servers{1}.[b]) = get_sr_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b]))
               /\ (forall b, b \in GAKEb_st.servers{1} => obind get_skey GAKEb_st.servers{1}.[b] = None 
                    <=> oget Meta_Red.O_GAKE.sid_pk{2}.[b] = Outer (get_pkey (oget GAKEb_st.servers{1}.[b])))
               /\ (forall b pk, b \in Meta_Red.O_GAKE.sid_pk{2} => oget Meta_Red.O_GAKE.sid_pk{2}.[b] = Inner pk 
                    =>  obind GAKE_mod.get_skey GAKEb.servers{2}.[pk] <> None)
               /\ (forall pk, pk \in GAKE_mod.GAKEb.servers{2} <=> rng Meta_Red.O_GAKE.sid_pk{2} (Inner pk))
               /\ (forall pk, pk \notin GAKE_mod.GAKEb.servers{2} => !rng Meta_Red.O_GAKE.sid_pk{2} (Inner pk))
               /\ (forall b pk, b \in Meta_Red.O_GAKE.sid_pk{2} => pk = get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b{2}]) => pk \in Meta_Red.O_GAKE.pk_set{2})
               /\ (forall pk j x1 x2 x4 x5, pk \notin Meta_Red.O_GAKE.pk_set{2} => pk \notin GAKE_mod.GAKEb.servers{2} /\ (pk, j) \notin GAKE_mod.GAKEb.s_smap{2} /\ (x1, x2, pk, x4, x5) \notin GAKE_mod.HROc.RO.m{2})
               /\ (forall sk, g ^ sk \in GAKEb.servers{2} => obind GAKE_mod.get_skey GAKEb.servers{2}.[g ^ sk] = Some sk)
          , GAKEb_st.stop{1} = Meta_Red.O_GAKE.stop{2}) => //.

- exact A_ll.

- proc; inline.
  sp 0 1; if {2} => //.
  + if => //. auto => /#.
    + sp. seq 1 1 : (#pre /\ ={r0}). auto => />.
      if {1} => //.
      + rcondt {2} ^if. auto => /#.
        sp 2 2; if => //.
        + sp 1 1; if => //.
          + auto => /> &1 &2 *. split. smt(get_setE mem_set in_fsetU in_fset1). 
            move => *. split; smt(get_setE mem_set in_fsetU in_fset1).
          auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
        auto => /> &1 &2 *. 
        split. move => *. split. 
        + smt(get_setE mem_set in_fsetU in_fset1).
        + move => *. do !split; smt(get_setE mem_set in_fsetU in_fset1).
        move => *. split. 
        + smt(get_setE mem_set in_fsetU in_fset1). 
        move => *. do !split; smt(get_setE mem_set in_fsetU in_fset1).
      if {2} => //.
      + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
      auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
    sp; seq 1 1 : (#pre /\ r0{1} = tk{2}). auto => />.
    auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
  auto => /> &1 &2 *.
- move => &2 bad; proc; inline. auto => />.
  by rewrite weight_dprod dkey_ll dtag_ll bad //=.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if {2} => //.
  + if => //.
    + auto => />. smt().
    + sp; seq 1 1 : (#pre /\ ={sk_s}). auto => />.
      sp 2 2; if {2} => //.
      + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
      auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
    auto => /> &1 &2 *. 
    smt().
  if {1} => //; auto => />.
- move => &2 bad; proc; inline. if => //; auto => />.
  by rewrite dt_ll bad //=.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + auto => /> &1 &2 *. smt(mem_set get_setE in_fsetU in_fset1).
  auto => /> &1 &2 *. smt().
- move => &2 bad; proc; inline. auto => />.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  case (Meta_Red.O_GAKE.stop{2}). 
  + rcondf {2} ^if. auto => />.
    sp; if {1} => //. 
    + sp; match {1} => //. 
      + sp; seq 1 0 : (#pre /\ sk_ce{1} \in dt); auto => />. 
      auto => />. 
    auto => />.     
  sp 1 1; if {2} => //.
  + sp 0 1; match {2} => //.
    + if {2} => //.
      + sp 1 4; if => //; 1: by auto => /#.
        + sp 1 0. match; 1..2: smt().
          + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
          move => stl str.
          match {1}.
          + match Pending {2} ^match. auto => /#.
            auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
          + match Accepted {2} ^match. auto => /#.
            auto => />. smt(get_setE mem_set in_fsetU in_fset1).
          match Aborted {2} ^match. auto => /#.
          auto => />. smt(get_setE mem_set in_fsetU in_fset1).
        rcondt {1} ^if. auto => /#.
        auto => />. smt(get_setE mem_set in_fsetU in_fset1).
      rcondt {1} ^if. auto => /#.
      sp 2 1. match Some {1} ^match. auto => /#.
      auto => />. smt(get_setE mem_set in_fsetU in_fset1).
    if {2} => //.
    + rcondt {1} ^if. auto => /#.
      sp. match; 1..2: smt().
      + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
      move => stl str.
      match {1}.
      + match Pending {2} ^match. auto => /#.
        auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
      + match Accepted {2} ^match. auto => /#.
        auto => />. smt(get_setE mem_set in_fsetU in_fset1).
      match Aborted {2} ^match. auto => /#.
      auto => />. smt(get_setE mem_set in_fsetU in_fset1).
    rcondt {1} ^if. auto => /#.
    rcondt {2} ^if. auto => /#.
    sp. match; 1..2: smt().
    + auto => />. smt(get_setE mem_set in_fsetU in_fset1).
    move => stl str.
    auto => />. smt(get_setE mem_set in_fsetU in_fset1).
  rcondf {1} ^if. auto => /#.
  auto => />.
- move => &2 bad; proc; inline.
  sp; if => //. 
  + sp; match. 
    + auto => />.
      by rewrite dt_ll bad //=.
    match; auto => />.
  auto => /#. 
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  case (Meta_Red.O_GAKE.stop{2}). 
  + rcondf {2} ^if. auto => />.
    sp; match {1} => //. 
    + auto => />.
    match {1} => //. 
    sp; match {1} => //.
    + auto => />.
    auto => />.
  sp 1 1; if {2} => //.
  + sp 1 1. match {2}.
    + sp 0 5. match. smt(). smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      + auto => />. smt(get_setE mem_set in_fsetU in_fset1).
      move => skl skr.
      match; 1..2: smt().
      + sp; match; 1..2: smt().
        + auto => />.
        move => stl str.
        sp. seq 1 1 : (#pre /\ ={sk_se}). auto => />. 
        sp; seq 1 1 : (#pre /\ r1{1} = r2{2}). auto => />.
        if => //. admit.
        + auto => /> &1 &2 *. split. move => *. split. smt(get_setE mem_set in_fsetU in_fset1). split.
move => x0.
case (x0 = (m2{2} ^ sk_se{2}, m2{2} ^ skl, b{2}, m2{2}, g ^ sk_se{2})) => x0eq.
rewrite mem_set x0eq get_setE //=.
have-> : get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b{2}]) = g ^ skr. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have ->: skl = skr. smt(get_setE mem_set in_fsetU in_fset1).
rewrite get_set_sameE.
smt(get_setE mem_set in_fsetU in_fset1).
rewrite mem_set x0eq get_set_neqE //=.
have<-: skl = skr. smt(get_setE mem_set in_fsetU in_fset1).
case (x0.`3 = b{2}); 1: by smt(get_setE mem_set in_fsetU in_fset1).
smt(get_setE mem_set in_fsetU in_fset1).

split. smt(get_setE mem_set in_fsetU in_fset1). split. 

move => x0.
case (x0 = (m2{2} ^ sk_se{2}, m2{2} ^ skl, b{2}, m2{2}, g ^ sk_se{2})) => x0eq.
smt(mem_set).
rewrite mem_set x0eq //=.
move => *.
rewrite mem_set negb_or //=.
split. smt(get_setE mem_set in_fsetU in_fset1).
do rewrite negb_and.
have<-: skl = skr. smt(get_setE mem_set in_fsetU in_fset1).
case (x0.`3 = b{2}); 1: by smt(get_setE mem_set in_fsetU in_fset1).
 smt(get_setE mem_set in_fsetU in_fset1).

split. smt(get_setE mem_set in_fsetU in_fset1). split.

move => b1 j1.
case ((b1, j1) = (b, j){2}) => [[] b1eq j1eq|].
rewrite mem_set b1eq j1eq get_set_sameE //=.
have->: pk{2} = (get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b{2}])).
 smt(get_setE mem_set in_fsetU in_fset1).
rewrite mem_set get_set_sameE //=.
rewrite get_setE //=.
rewrite get_setE //=.
have<-: skl = skr. smt(get_setE mem_set in_fsetU in_fset1).
smt(get_setE mem_set in_fsetU in_fset1).
smt(get_setE mem_set in_fsetU in_fset1).

split. smt(get_setE mem_set in_fsetU in_fset1). split. smt(get_setE mem_set in_fsetU in_fset1).

move => pk0 j1 x1 x2 x4 x5 ninpks.
split. smt(get_setE mem_set in_fsetU in_fset1).
split. smt(get_setE mem_set in_fsetU in_fset1).
 


smt(get_setE mem_set in_fsetU in_fset1). 



move => *. split. smt(get_setE mem_set in_fsetU in_fset1). split. admit. split. smt(get_setE mem_set in_fsetU in_fset1). split. admit. split. smt(get_setE mem_set in_fsetU in_fset1). split. admit. split. smt(get_setE mem_set in_fsetU in_fset1). split. admit. smt(get_setE mem_set in_fsetU in_fset1). 
        auto => /> &1 &2 *.
      auto => />. smt(get_setE mem_set in_fsetU in_fset1).
    match None {1} ^match. auto => /#.
    auto => />. 
  match None {1} ^match. auto => /#.
  auto => />.
- move => &2 bad; proc; inline.
  sp; match; 1: by auto => /#.
  match; 2: by auto => />.
  sp; match; 1: by auto => />.
  auto => /> &hr *.
  by rewrite weight_dprod dkey_ll dtag_ll dt_ll bad //=.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + if => //.
    + sp; match; 1..2: admit.
      + auto => /> &1 &2 *. admit. 
      move => stl str. admit.
    sp; match; 1..2: admit.
    + auto => /> &1 &2 *. 
    move => stl str.
    admit.
  if {1} => //. 
  + sp; match {1} => //. match {1} => //. auto => />.
  match {1} => //. match {1} => //. auto => />.
- move => &2 bad; proc; inline.
  sp 1; if {1} => //. 
  + admit. (* match struggles *)
  match; auto => />.
  match; auto => />.
  by rewrite weight_dprod dkey_ll dtag_ll //=.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //; 2: by auto => /#.
  sp; match; 1..2: admit.
  + auto => />.
  move => stl str.
  admit.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. admit.
  match {1} => //. match {1} => //. auto => /#.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match {1} => //. admit. (* only in s_kp if Honest *) admit.
  match {1} => //. match {1} => //. auto => /#.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match {1} => //. 
    + match None {2} ^match; 1: by auto => /#.
      auto => />.
    admit.
  match {1}; auto => />.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match {1} => //. 
    + match None {2} ^match. auto => /> &1 &2 *. admit.
      auto => />.
    match Some {2} ^match. auto => /> &1 &2 *. admit.
    match {1} => //. admit. 
  admit. admit. admit.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. if => //.
    + match => //; 1..2: smt().
      + auto => />.
      move => stl str.
      match => //; 1..3: smt().
      + move => sl ptl irl sr ptr irr.
        auto => />.
      + move => sl tl kl irl sr tr kr irr.
        if => //. 
        + auto => /> &1 &2 *. 
          split.
          + move => [|[|fp]]; 1..2: smt().
            right; right.
            admit. (* relate fresh partner and such *)
          move => [|[]]; 1..2: smt().
          admit. (* relate fresh partner and such *)
        + if => //. 
          + auto => />. smt(get_setE mem_set in_fsetU in_fset1).
          auto => />. smt(get_setE mem_set in_fsetU in_fset1).
        auto => />.
      move => sl tl itl sr tr irr.
      auto => />.
    auto => />.
  if {1} => //; match {1} => //. 
  match {1} => //; if {1} => //.
  if {1} => //; auto => />.
- move => &2 bad; proc; inline. sp; if => //; match; auto => />. 
  match => //; if => //; if; auto => />.
  by rewrite dkey_ll.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. if {2} => //. 
    + sp; if => //.
      + match; 1..2: smt().
        + auto => />.
        + move => stl str.
          + match; 1..3: smt().
            + move => sl ptl irl sr ptr irr.
              auto => />.
            + move => sl tl kl irl sr tr kr irr.
              if => //.
              + auto => /> &1 &2 *. admit. (* relate fresh partner and such *)
              if => //.
              + auto => />. admit.
              auto => />. admit.
            auto => />.
          auto => />.
        auto => />.
      if {1} => //.
      match {1} => //. admit. (* when in state1 then honest *)
  if {1} => //; match {1} => //. 
  match {1} => //; if {1} => //.
  if {1} => //; auto => />; smt(get_setE mem_set in_fsetU in_fset1).
- move => &2 bad; proc; inline. sp; if => //; match; auto => />. 
  match => //; if => //; if; auto => />.
  by rewrite dkey_ll.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

auto => />.
split. smt(emptyE in_fset0).
move => roeq inj csm ssm pkin inv inv2 inv3 inv4 inv5 inv6 inv7 inv8 rl rr al csl pksl ssl sl stl tl url ml ar csr tr pksr huh ssr sr str urr mr.
by case : (!str) => />.
qed.
