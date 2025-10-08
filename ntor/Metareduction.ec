require import AllCore FSet FMap Distr DProd List SplitRO NTOR.
(*   *) import GAKEc HROc.
require (*  *) DiffieHellman.
(*   *) import StdBigop.Bigreal.BRA StdOrder.RealOrder DH.G DH.GP DH.FD DH.GP.ZModE.


(* ------------------------------------------------------------------------------------------ *)
(* Introduce stop in original game *)
module GAKEb_st (S: Server) (C: Client) (H : GAKEc.HROc.RO) : GAKE_out_i = {
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

    if (!x.`3 \in servers \/ get_sr_dh (oget servers.[x.`3])) {
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
    if (m1 \in servers /\ !get_sr_dh (oget servers.[m1])) {
      pk_b <- get_pkey (oget servers.[m1]);
      match st with
      | None => {
          (st', m2) <@ C.new_session(m1, pk_b);
           c_smap.[i] <- Pending st' (m1, m2) (false, false, false);
          r <- Some m2;
        }
      | Some st => { }
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
            s_smap.[(b, j)] <- Accepted st' ((b, m2), Some m3) k (false, false, false);
            r <- Some m3;
          } else {
            s_smap.[(b, j)] <- Aborted None (Some ((b, m2), None)) (false, false, false);
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
              if (m3.`1 \notin pk_set) {
                pk_set <- pk_set `|` fset1 m3.`1;
              }
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
                  \/ fresh_partner_c t' s_smap servers = Some false
                  \/ get_sr_dh (oget servers.[get_name st]))) {
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
(* Modified model with pkeys instead of names *)
require import NTOR_nosid.
import GAKE_mod.

op rem_sid_c (s : pr_st_client GAKEc.instance_state) : pr_st_client_mod instance_state =
match s with 
| GAKEc.Pending st pt ir => GAKE_mod.Pending (st.`2, st.`3) pt.`2 ir
| GAKEc.Accepted st t k ir => GAKE_mod.Accepted (st.`2, st.`3) ((t.`1).`2, t.`2) k ir
| GAKEc.Aborted st t ir => GAKE_mod.Aborted (Some ((oget st).`2, (oget st).`3)) (Some (((oget t).`1).`2, (oget t).`2)) ir
end.

op rem_sid_s (s : pr_st_server GAKEc.instance_state) : pr_st_server_mod instance_state =
match s with 
| GAKEc.Pending st pt ir => GAKE_mod.Pending (st.`2, st.`3) pt.`2 ir
| GAKEc.Accepted st t k ir => GAKE_mod.Accepted (st.`2, st.`3) ((t.`1).`2, t.`2)k ir
| GAKEc.Aborted st t ir => GAKE_mod.Aborted (Some ((oget st).`2, (oget st).`3)) (Some (((oget t).`1).`2, (oget t).`2)) ir
end.


(* ------------------------------------------------------------------------------------------ *)
(* Reduction to honest game that only allows clients to interact with honest servers  *)
type server_state_mod = [
  Inner of pkey & bool
| Outer of pkey
].

op get_pkey_mod s_st =
with s_st = Inner pk _ => pk
with s_st = Outer pk => pk.

op get_sr_out s_st : bool =
with s_st = Inner _ _ => false
with s_st = Outer _ => true.

op get_sr_in s_st : bool =
with s_st = Inner _ bool => bool
with s_st = Outer _ => true.


module Hon_Red (O : GAKEc.GAKE_out_i) : GAKEc.GAKE_out_i = {
  var dh_ro : (pkey * pkey * s_id * pkey * pkey, (tag * key)) fmap
  var c_inst : (int, bool) fmap
  var dhc_smap : (int, pr_st_client GAKEc.instance_state) fmap
  var servers : (s_id, server_state_mod) fmap

  proc init_mem(b: bool) = {
    O.init_mem(b);
    dhc_smap <- empty;
    c_inst <- empty;
    dh_ro <- empty;
    servers <- empty;
  }

  proc h = O.h

  proc init_s(b : s_id): pkey option = {
  var r <- None;

    r <@ O.init_s(b);
    if (b \notin servers) {
      servers.[b] <- Inner (oget r) false;
    }

    return r;
  }

  proc set_cert(b: s_id, pk: pkey) = { 
    var r <- None;

    r <@ O.set_cert(b, pk);
    if (b \notin servers) {
      servers.[b] <- Outer pk;
    }

    return r;
  }

  proc send_msg1(i: int, m1: s_id) = {
    var sk_ce, pk_ce, pk_b; 
    var r <- None;

    if (m1 \in servers) {
      if (!get_sr_out (oget servers.[m1]) /\ i \notin dhc_smap) {
        r <@ O.send_msg1(i, m1);
        if (r <> None) {
          c_inst.[i] <- false;
        }
      } else {
        if (i \notin c_inst) {
          sk_ce <$ dt;
          pk_ce <- g ^ sk_ce;
          pk_b <- get_pkey_mod (oget servers.[m1]);
          r <- Some pk_ce;
          dhc_smap.[i] <- GAKEc.Pending (m1, pk_b, sk_ce) (m1, pk_ce) (false, false, false);
          c_inst.[i] <- true;
        }
      }
    }

    return r;
  }

  proc send_msg2 = O.send_msg2

  proc send_msg3(i: int, m3: pkey * tag) = {
    var pk_b, sk_ce, b, t_A, k;
    var r <- None;

    if (i \notin dhc_smap) {
      r <@ O.send_msg3(i, m3);
    } else {
      match dhc_smap.[i] with 
      | None => { } (* Abort? *)
      | Some st => {
          match st with
          | GAKEc.Pending st pt ir => {
              (b, pk_b, sk_ce) <- st;
              (t_A, k) <@ O.h(m3.`1 ^ sk_ce, pk_b ^ sk_ce, b, g ^ sk_ce, m3.`1);
              if (t_A = m3.`2) {
                dhc_smap.[i] <- GAKEc.Accepted st (pt, Some m3) k ir;
                r <- Some ();
              } else {
                dhc_smap.[i] <- GAKEc.Aborted (Some st) (Some (pt, Some m3)) ir;
              }
            }
          | GAKEc.Accepted _ _ _ _ => { }
          | GAKEc.Aborted _ _ _ => { }
          end;
        }
      end;
    }
    return r;
  }

  proc c_rev_skey(i: int) = {
    var r <- None;

    if (i \notin dhc_smap) {
      r <@ O.c_rev_skey(i);
    } else {
      match dhc_smap.[i] with
      | None => { }
      | Some st => {
          match st with 
          | GAKEc.Pending _ _ _ => { }
          | GAKEc.Accepted st' t' k' ir' => {
              if (!get_ir_test (oget dhc_smap.[i])) { (* removed check on the partner and that they are untested, since an unhonest servers cannot be tested *)
                r <- Some k';
                dhc_smap.[i] <- set_ir_sess (GAKEc.Accepted st' t' k' ir');
              }
            }
          | GAKEc.Aborted _ _ _ => { }
          end;
        }
      end;
    }
    return r;
  }

  proc s_rev_skey(b: s_id, j: int) = {
    var r <- None;

    if (b \in servers /\ !get_sr_out (oget servers.[b])) {
      r <@ O.s_rev_skey(b, j);
    }

    return r;
  }

  proc rev_ltkey(b: s_id) = {
    var r <- None;

    if (b \in servers /\ !get_sr_out (oget servers.[b])) {
      r <@ O.rev_ltkey(b);
    }

    return r;
  }

  proc c_rev_ephkey(i : int) = {
    var r <- None;

    if (i \notin dhc_smap) {
      r <@ O.c_rev_ephkey(i);
    } else {
      match dhc_smap.[i] with
      | None => { }
      | Some st => {
          match st with
          | GAKEc.Pending st pk_e ir => {
              r <- Some (get_eph_c st);
              dhc_smap.[i] <- set_ir_eph (GAKEc.Pending st pk_e ir);
            }
          | GAKEc.Accepted st t k ir => {
              if (!get_ir_test (oget dhc_smap.[i])) {
                r <- Some (get_eph_c st);
                dhc_smap.[i] <- set_ir_eph (GAKEc.Accepted st t k ir);
              }
            }
          | GAKEc.Aborted _ _ _ => {  }
           end;
        }
      end;
    }

    return r;
  }

  proc s_rev_ephkey(b: s_id, j: int) = {
    var r <- None;

    if (b \in servers /\ !get_sr_out (oget servers.[b])) {
      r <@ O.s_rev_ephkey(b, j);
    }

    return r;
  }

  proc c_test(i : int) = {
    var r <- None;


    if (i \notin dhc_smap) {
      r <@ O.c_test(i);
    }

    return r;
  }

  proc s_test(b: s_id, j: int) = {
    var r <- None;

    if (b \in servers /\ !get_sr_out (oget servers.[b])) {
      r <@ O.s_test(b, j);
    }

    return r;
  }
}.


(* ------------------------------------------------------------------------------------------ *)
(* Reduction preventing collisions and prediction of public keys  *)

module (Name_Red (A : GAKEc.A_GAKE) : GAKE_mod.A_GAKE) (O : GAKE_mod.GAKE_out) = {
  module O_GAKE : GAKEc.GAKE_out = {
    var unreg_ro : (pkey * pkey * s_id * pkey * pkey, (tag * key)) fmap

    var sid_pk : (s_id, server_state_mod) fmap
    var pk_set : pkey fset
  (*  var pred_ce : pkey fset
    var pred_se : pkey fset*)
    
    var stop : bool

    proc h(x : GAKEc.h_input) = {
      var pk, tk;
      var r <- (witness, witness);

      if (!stop) {
        if (x.`3 \in sid_pk /\ !get_sr_out (oget sid_pk.[x.`3])) {
          if (x \in unreg_ro) {
            r <- oget unreg_ro.[x];
          } else {
            pk <- get_pkey_mod (oget sid_pk.[x.`3]); 
            r <@ O.h((x.`1, x.`2, pk, x.`4, x.`5));
          }
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
            sid_pk.[b] <- Inner pk false;
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
      var pk_s, pk; 
      var r <- None;

      if (!stop /\ m1 \in sid_pk /\ !get_sr_out (oget sid_pk.[m1])) {
        pk_s <- oget sid_pk.[m1];
        pk <- get_pkey_mod pk_s;
        r <@ O.send_msg1(i, pk);

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
        | Inner pk _ => {
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
        r <@ O.send_msg3(i, m3);
        if (r = Some () /\ m3.`1 \notin pk_set) {
          pk_set <- pk_set `|` fset1 m3.`1;
        }
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
      var pk_s;
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        pk_s <- oget sid_pk.[b];
        match pk_s with 
        | Inner pk _ => {
            r <@ O.s_rev_skey(pk, j);
          }
        | Outer pk => {}
        end;
      }

      return r;     
    }

    proc rev_ltkey(b: s_id) = {
      var pk_s;
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        pk_s <- oget sid_pk.[b];
        match pk_s with 
        | Inner pk _ => {
            r <@ O.rev_ltkey(pk);
            if (r <> None) {
              sid_pk.[b] <- Inner pk true;
            }
          }
        | Outer pk => {(* I can eph key reveal an instance from an corrupted server! do I need to be able to distinguish dishonest from corrupted here? *)}
        end;
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
      var pk_s;
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        pk_s <- oget sid_pk.[b];
        match pk_s with 
        | Inner pk _ => {
            r <@ O.s_rev_ephkey(pk, j);
          }
        | Outer pk => {(* I can eph key reveal an instance from an corrupted server! do I need to be able to distinguish dishonest from corrupted here? *)}
        end;
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
      var pk_s;
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        pk_s <- oget sid_pk.[b];
        match pk_s with 
        | Inner pk _ => {
            r <@ O.s_test(pk, j);
          }
        | Outer pk => {}
        end;
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

    b' <@ A(O_GAKE).run();

    return b';
  }
}.



(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: GAKEc.A_GAKE {-GAKE_mod.HROc.RO, -GAKEc.HROc.RO, -Hon_Red, -Name_Red, -GAKEc.GAKEb, -GAKEc.GAKEb_hon, -GAKEb_st, -GAKE_mod.GAKEb }.

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
 
 
lemma gake_hon bit &m: Pr[GAKEc.E_GAKE(GAKEc.GAKEb(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), A).run(bit) @ &m : res] = Pr[GAKEc.E_GAKE(Hon_Red(GAKEc.GAKEb_hon(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO)), A).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline. admit. (*
wp; call (: ={b0, servers, s_smap, tested}(GAKEc.GAKEb, GAKEc.GAKEb_hon) /\ ={m}(GAKEc.HROc.RO, GAKEc.HROc.RO)
  
              /\ (GAKEc.GAKEb.c_smap{1} = (GAKEc.GAKEb_hon.c_smap{2} + Hon_Red.dhc_smap{2}))
              /\ (forall i, i \in Hon_Red.dhc_smap{2} => i \notin GAKEc.GAKEb_hon.c_smap{2})
              /\ (forall i, i \in GAKEc.GAKEb_hon.c_smap{2} => i \notin Hon_Red.dhc_smap{2})
              /\ (forall b, b \in Hon_Red.servers{2} <=> b \in GAKEc.GAKEb_hon.servers{2})
              /\ (forall b, b \in GAKEc.GAKEb_hon.servers{2} 
                   => get_pkey (oget GAKEc.GAKEb_hon.servers{2}.[b]) = get_pkey_mod (oget Hon_Red.servers{2}.[b])
                                      /\ (get_sr_out (oget Hon_Red.servers{2}.[b]) = get_sr_dh (oget GAKEc.GAKEb_hon.servers{2}.[b])))
              /\ (forall i, i \in GAKEc.GAKEb.c_smap{1} <=> i \in Hon_Red.c_inst{2})
              /\ (forall i, i \in Hon_Red.dhc_smap{2} => get_ir_test (oget Hon_Red.dhc_smap{2}.[i]) = false
                                       /\ get_name (oget Hon_Red.dhc_smap{2}.[i]) \in GAKEb_hon.servers{2}
                                       /\ get_sr_dh (oget GAKEb_hon.servers{2}.[get_name (oget Hon_Red.dhc_smap{2}.[i])]))
              /\ (forall b j , b \notin GAKEc.GAKEb_hon.servers{2} => (b, j) \notin GAKEc.GAKEb_hon.s_smap{2})
              /\ (forall b j, (b, j) \in GAKEc.GAKEb_hon.s_smap{2} => get_name (oget GAKEc.GAKEb_hon.s_smap{2}.[(b, j)]) = b
                                       /\ (exists pk m3, get_trace (oget GAKEc.GAKEb_hon.s_smap{2}.[(b, j)]) = Some ((b, pk), Some m3)))
              /\ (forall b j, b \in GAKEc.GAKEb_hon.servers{2} => get_sr_dh (oget GAKEc.GAKEb_hon.servers{2}.[b])
                   => (b, j) \notin GAKEc.GAKEb_hon.s_smap{2} /\ get_sr_ltk (oget GAKEc.GAKEb_hon.servers{2}.[b]))
              /\ (forall i j, i \in Hon_Red.dhc_smap{2}  
                   => (get_name (oget Hon_Red.dhc_smap{2}.[i]), j) \notin GAKEc.GAKEb_hon.s_smap{2})
              /\ (forall i st pt ir m3, i \in Hon_Red.dhc_smap{2} => Hon_Red.dhc_smap{2}.[i] = Some (Pending st pt ir)
                   => (1 <= card (get_partners_c (pt, Some m3) GAKEc.GAKEb_hon.s_smap{2})) = false)
              /\ (forall i st pt ir, i \in Hon_Red.dhc_smap{2} => Hon_Red.dhc_smap{2}.[i{2}] = Some (Pending st pt ir)
                   => (1 <= card (get_origins_c (pt, None) GAKEc.GAKEb_hon.s_smap{2}) = false))
              /\ (forall i st t k ir, i \in Hon_Red.dhc_smap{2} => Hon_Red.dhc_smap{2}.[i] = Some (Accepted st t k ir)
                   => (1 <= card (get_partners_c t GAKEc.GAKEb_hon.s_smap{2})) = false)).

+ sim />.

+ proc; inline.
  sp 0 2; if => //.
  + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
  auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).

+ proc; inline.
  sp 1 4; if => //.
  + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
  auto => />. smt(get_setE mem_set in_fsetU in_fset1).

+ proc; inline.
  sp 2 1; if => //. smt().
  if {2} => //.
  + rcondt {2} ^if. auto => /#.
    sp; match = => //. auto => /> &2 *. smt(joinE).
    + auto => /> &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1). 
      rewrite -fmap_eqP. smt(joinE get_setE).
    move => st.
    auto => />. 
  sp; match {1} => //.
  + rcondt {2} ^if. auto => /#.
    auto => /> &2 ? ? ? ? ? ? ? ? inv ? ? ? ? ? ? ? sk *. do !split; 2..6: smt(get_setE mem_set in_fsetU in_fset1 joinE).
    + rewrite -fmap_eqP. smt(joinE get_setE).
    + move => i1 st0 pt ir0 m3.
      case (i1 = i{2}) => ieq.
      + rewrite ieq mem_set //=.
        rewrite get_setE //=.
        move => [#] steq pteq ireq.
        rewrite /get_partners_c.
        case ((i{2} \notin Hon_Red.dhc_smap{2})) => indhc; 2: by smt(get_setE mem_set in_fsetU in_fset1 joinE).
        have->: (fdom (filter (fun (_ : s_id * int) (val : pr_st_server GAKEc.instance_state) => get_trace val = Some (pt, Some m3)) GAKEb_hon.s_smap{2})) = fset0.
        + rewrite fsetP.
          move => x.
          rewrite mem_fdom mem_filter.
          have->: !(x \in GAKEb_hon.s_smap{2} /\ (fun (_ : s_id * int) (val : pr_st_server GAKEc.instance_state) =>
              get_trace val = Some (pt, Some m3)) x (oget GAKEb_hon.s_smap{2}.[x])).
          + rewrite negb_and.
            case (x \in GAKEb_hon.s_smap{2}); 2: by smt().
            simplify.
            rewrite -pteq.
            move => xin.
            have := inv x.`1 x.`2.
            by smt(get_setE in_fset0 joinE).
          by smt(get_setE in_fset0 joinE).
        by smt(fcards0).
      by smt(get_setE mem_set in_fsetU in_fset1).
    + move => i1 st0 pt ir.
      case (i1 = i{2}) => ieq.
      + rewrite ieq mem_set//=.
        rewrite get_setE //=.
        move => [#] steq pteq ireq.
        rewrite /get_origins_c.
        case ((i{2} \notin Hon_Red.dhc_smap{2})) => indhc; 2: by smt(get_setE mem_set in_fsetU in_fset1 joinE).
        have->: (fdom (filter (fun (_ : s_id * int) (val : pr_st_server GAKEc.instance_state) 
          => exists (m2o : (pkey * tag) option), get_trace val = Some (pt, m2o)) GAKEb_hon.s_smap{2})) = fset0.
        + rewrite fsetP.
          move => x.
          rewrite mem_fdom mem_filter. 
          have->: !(x \in GAKEb_hon.s_smap{2} /\ (fun (_ : s_id * int) (val : pr_st_server GAKEc.instance_state) =>
              exists (m2o : (pkey * tag) option), get_trace val = Some (pt, m2o)) x (oget GAKEb_hon.s_smap{2}.[x])).
          + rewrite negb_and.
            case (x \in GAKEb_hon.s_smap{2}); 2: by smt().
            simplify.
            rewrite -pteq.
            move => xin. 
            rewrite negb_exists.
            have := inv x.`1 x.`2.
            by smt(get_setE in_fset0 joinE).
          by smt(get_setE in_fset0 joinE).
        by smt(fcards0).
      by smt(get_setE mem_set in_fsetU in_fset1).
    by smt(get_setE mem_set in_fsetU in_fset1).
  rcondf {2} ^if. auto => /#.
  auto => />.

+ proc; inline.
  sp; match = => //.
  move => sk.
  match = => //.
  sp; match = => //.
  + auto => />.
  move => sts.
  sp; seq 1 1 : (#pre /\ ={sk_se}). auto => />.
  sp; seq 1 1 : (#pre /\ ={r1}). auto => />. 
  if => //.
  + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? inv inv2 inv3 *. do !split; 1..4: smt(get_setE mem_set in_fsetU in_fset1).
    + move => i1 st0 pt ir0 m3 iin ipen.
      rewrite get_setE //=.
      rewrite /get_partners_c.
      rewrite filter_set.
      rewrite rem_id. 
      rewrite mem_filter negb_and. smt().
      have := inv i1 st0 pt ir0 m3 iin ipen.
      rewrite /get_partners_c. 
      by smt(get_setE mem_set in_fsetU in_fset1). 
    + move => i1 st0 pt ir0 iin ipen.
      rewrite get_setE //=.
      rewrite /get_origins_c.
      rewrite filter_set.
      rewrite rem_id. 
      rewrite mem_filter negb_and. smt().
      have := inv2 i1 st0 pt ir0 iin ipen.
      rewrite /get_origins_c. 
      by smt(get_setE mem_set in_fsetU in_fset1).   
    move => i1 st0 t k0 ir0 iin ipen.
    rewrite get_setE //=.
    rewrite /get_partners_c.
    rewrite filter_set.
    rewrite rem_id. 
    rewrite mem_filter negb_and. smt().
    have := inv3 i1 st0 t k0 ir0 iin ipen.
    rewrite /get_partners_c. 
    by smt(get_setE mem_set in_fsetU in_fset1).
  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? inv inv2 inv3 *. do !split; 1..4: smt(get_setE mem_set in_fsetU in_fset1).
  + move => i1 st0 pt ir0 m3 iin ipen.
    rewrite /get_partners_c.
    rewrite filter_set.
    rewrite rem_id. 
    rewrite mem_filter negb_and. smt().
    have := inv i1 st0 pt ir0 m3 iin ipen.
    rewrite /get_partners_c. 
    by smt(get_setE mem_set in_fsetU in_fset1).
  + move => i1 st0 pt ir0 iin ipen.
    rewrite /get_origins_c.
    rewrite filter_set.
    rewrite rem_id. 
    rewrite mem_filter negb_and. smt().
    have := inv2 i1 st0 pt ir0 iin ipen.
    rewrite /get_origins_c. 
    by smt(get_setE mem_set in_fsetU in_fset1). 
  move => i1 st0 t k0 ir0 iin ipen.
  rewrite /get_partners_c.
  rewrite filter_set.
  rewrite rem_id. 
  rewrite mem_filter negb_and. smt().
  have := inv3 i1 st0 t k0 ir0 iin ipen.
  rewrite /get_partners_c. 
  by smt(get_setE mem_set in_fsetU in_fset1).

+ proc; inline.
  sp 1 1; if {2} => //.
  + sp; match = => //. auto => />. smt(joinE).
    + auto => />.
    move => sto.
    match = => //.
    + move => s pt ir.
      sp; seq 1 1 : (#pre /\ r1{1} = r3{2}). auto => />.
      if. auto => />.
      + sp 2 2; if => //. auto => /#.
        + auto => /> &1 &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).  
          rewrite -fmap_eqP. have->: sk{1} = sk{2}. smt(get_setE mem_set in_fsetU in_fset1). smt(joinE get_setE).
        auto => /> &1 &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).  
        rewrite -fmap_eqP. smt(joinE get_setE).
      sp 1 1; if => //. auto => /#.
      + auto => /> &1 &2 rol ror *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).  
        rewrite -fmap_eqP. 
        have->: sk{1} = sk{2}. have : (t_A0{2}, sk{2}) = (m3{2}.`2, sk{1}). rewrite ror rol. smt(). smt().
        by smt(joinE get_setE).
      auto => /> &1 &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).  
      rewrite -fmap_eqP. smt(joinE get_setE).
    + move => s t k ir.
      auto => />.
    move => s t ir.
    auto => />.
  match = => //. auto => />. smt(joinE).
  move => st.
  match = => //.
  move => s pt ir.
  sp; seq 1 1 : (#pre /\ ={r1}). auto => />.
  if => //.
  + sp 2 2; if => //. auto => /#.
    + match Some {1} ^match. auto => /#.
      auto => /> &1 &2 *. do !split; 2..9: smt(get_setE mem_set in_fsetU in_fset1).  
      rewrite -fmap_eqP. have->: sk{1} = k{2}. smt(get_setE mem_set in_fsetU in_fset1). smt(joinE get_setE).
    auto => /> &1 &2 *. do !split; 2..9: smt(get_setE mem_set in_fsetU in_fset1). 
    rewrite -fmap_eqP. smt(joinE get_setE).
  sp 1 1; if => //. auto => /#.
  + match Some {1} ^match. auto => /#.
    auto => /> &1 &2 rol ror *. do !split; 2..9: smt(get_setE mem_set in_fsetU in_fset1).  
    rewrite -fmap_eqP. 
    have->: sk{1} = k{2}. have : (t_A{2}, k{2}) = (m3{2}.`2, sk{1}). rewrite ror rol. smt(). smt().
    by smt(joinE get_setE).
  auto => /> &1 &2 *. do !split; 2..9: smt(get_setE mem_set in_fsetU in_fset1).  
  rewrite -fmap_eqP. smt(joinE get_setE).

+ proc; inline.
  sp 1 1; if {2} => //.
  + sp; match = => //. auto => />. smt(joinE).
    + auto => />.
    move => st.    
    match = => //.
    + move => s pt ir.
      auto => />.
    + move => s t k ir.
      if => //.
      + move => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
      + auto => /> &1 &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).  
        rewrite -fmap_eqP. smt(joinE get_setE). 
      auto => />.
    move => s t ir.
    auto => />.
  match = => //. auto => />. smt(joinE).
  move => st.
  match = => //.
  move => s t k ir.
  if => //.
  + auto => /> &1 &2 *.  smt(get_setE mem_set in_fsetU in_fset1).
  auto => /> &1 &2 *. do !split; 2..9: smt(get_setE mem_set in_fsetU in_fset1 joinE).  
  rewrite -fmap_eqP. smt(joinE get_setE).

+ proc; inline.
  sp 1 1; if {2} => //.
  + sp; match = => //.
    + auto => />.
    move => st.
    match = => //.
    + auto => />.
    + move => s t k ir.
      if => //.
      + auto => /> &1 &2 *. 
        rewrite /untested_partner_s.
        rewrite /get_partners_s /get_untested_partners_s.
        have->: (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => get_trace val = Some t) (GAKEb_hon.c_smap{1} + Hon_Red.dhc_smap{1}))) 
            = (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => get_trace val = Some t) GAKEb_hon.c_smap{1})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          by smt(joinE).
        have->: (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => get_trace val = Some t /\ get_ir_test val = false)
             (GAKEb_hon.c_smap{1} + Hon_Red.dhc_smap{1}))) = (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) =>
                get_trace val = Some t /\ get_ir_test val = false) GAKEb_hon.c_smap{1})). 
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          by smt(joinE).
        by smt().
      + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? inv inv2 inv3 *. do !split; 1..4: smt(get_setE mem_set in_fsetU in_fset1). 
        + move => i1 st0 pt ir0 m3 iin ipen.
          rewrite /get_partners_c.
          rewrite filter_set.
          rewrite rem_id. 
          rewrite mem_filter negb_and. smt().
          have := inv i1 st0 pt ir0 m3 iin ipen.
          rewrite /get_partners_c. 
          by smt(get_setE mem_set in_fsetU in_fset1). 
        + move => i1 st0 pt ir0 iin ipen.
          rewrite /get_origins_c.
          rewrite filter_set.
          rewrite rem_id. 
          rewrite mem_filter negb_and. smt().
          have := inv2 i1 st0 pt ir0 iin ipen.
          rewrite /get_origins_c. 
          by smt(get_setE mem_set in_fsetU in_fset1).
        move => i1 st0 t0 k0 ir0 iin ipen.
        rewrite /get_partners_c.
        rewrite filter_set.
        rewrite rem_id. 
        rewrite mem_filter negb_and. smt().
        have := inv3 i1 st0 t0 k0 ir0 iin ipen.
        rewrite /get_partners_c. 
        by smt(get_setE mem_set in_fsetU in_fset1).
      auto => />.
    auto => />.
  auto => /#.

+ proc; inline.
  sp 1 1; if {2} => //.
  + sp; match = => //.
    + auto => />.
    move => st.
    match = => //.
    + move => kp. 
      if => //.
      + auto => /> &2 *.
        have : (forall b j t, (b, j) \in GAKEc.GAKEb_hon.s_smap{2} /\ t = (oget (get_trace (oget GAKEc.GAKEb_hon.s_smap{2}.[b, j])))
            => get_untested_partners_s t (GAKEb_hon.c_smap{2} + Hon_Red.dhc_smap{2}) = get_untested_partners_s t GAKEc.GAKEb_hon.c_smap{2}
            /\ get_partners_s t (GAKEb_hon.c_smap{2} + Hon_Red.dhc_smap{2}) = get_partners_s t GAKEc.GAKEb_hon.c_smap{2}).
        + rewrite /untested_partner_s.
          rewrite /get_partners_s /get_untested_partners_s.
          move => b1 j t [] bjin teq.
          have->: (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => get_trace val = Some t /\ get_ir_test val = false) (GAKEb_hon.c_smap{2} 
              + Hon_Red.dhc_smap{2}))) = (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) 
              => get_trace val = Some t /\ get_ir_test val = false) GAKEb_hon.c_smap{2})).
          + rewrite fsetP.
            move => x.
            do rewrite mem_fdom mem_filter.
            smt(joinE).
          have->: (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => get_trace val = Some t) (GAKEb_hon.c_smap{2} + Hon_Red.dhc_smap{2}))) = 
              (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => get_trace val = Some t) GAKEb_hon.c_smap{2})). 
          + rewrite fsetP.
            move => x.
            do rewrite mem_fdom mem_filter.
            smt(joinE).
          smt().
        smt(joinE).
      + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
      auto => />.
    + auto => />.
    auto => />.
  auto => />. smt(joinE).

+ proc; inline.
  sp 1 1; if {2} => //.
  + sp; match = => //. auto => />. smt(joinE).
    + auto => />.
    move => st.    
    match = => //.
    + move => s pt ir.
      auto => /> &1 &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).  
      rewrite -fmap_eqP. smt(joinE get_setE). 
    + move => s t k ir.
      if => //. auto => />. smt(joinE).
      + auto => /> &1 &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).  
        rewrite -fmap_eqP. smt(joinE get_setE). 
      auto => />.
    move => s t ir.
    auto => />.
  match = => //. auto => />. smt(joinE).
  move => st.
  match = => //.
  + move => s pt ir.
    rcondt {1} ^if. auto => /#.
    auto => /> &2 *. do !split; 2..9: smt(get_setE mem_set in_fsetU in_fset1).  
    rewrite -fmap_eqP. smt(joinE get_setE). 
  move => s t k ir.
  if => //.
  + auto => /> &1 &2 *.
    have->: untested_partner_c t GAKEb_hon.s_smap{1} = None by rewrite /untested_partner_c; smt().
    by smt().
  auto => /> &1 &2 *. do !split; 2..9: smt(get_setE mem_set in_fsetU in_fset1).  
  rewrite -fmap_eqP. smt(joinE get_setE). 

+ proc; inline.
  sp 1 1; if {2} => //.
  + sp; match = => //.
    + auto => />.
    move => st.    
    match = => //.
    + auto => />.
    + move => s t k ir.
      if => //.
      + auto => /> &1 &2 *. 
        rewrite /untested_partner_s.
        rewrite /get_partners_s /get_untested_partners_s.
        have->: (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => get_trace val = Some t) (GAKEb_hon.c_smap{1} + Hon_Red.dhc_smap{1}))) 
          = (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => get_trace val = Some t) GAKEb_hon.c_smap{1})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          by smt(joinE).
        have->: (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => get_trace val = Some t /\ get_ir_test val = false)
             (GAKEb_hon.c_smap{1} + Hon_Red.dhc_smap{1}))) = (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) =>
                get_trace val = Some t /\ get_ir_test val = false) GAKEb_hon.c_smap{1})). 
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          by smt(joinE).
        by smt().
      + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? inv inv2 inv3 *. do !split; 1..4: smt(get_setE mem_set in_fsetU in_fset1).
        + move => i1 st0 pt ir0 m3 iin ipen.
          rewrite /get_partners_c.
          rewrite filter_set.
          rewrite rem_id. 
          rewrite mem_filter negb_and. smt().
          have := inv i1 st0 pt ir0 m3 iin ipen.
          rewrite /get_partners_c. 
          by smt(get_setE mem_set in_fsetU in_fset1).
        + move => i1 st0 pt ir0 iin ipen.
          rewrite /get_origins_c.
          rewrite filter_set.
          rewrite rem_id. 
          rewrite mem_filter negb_and. smt().
          have := inv2 i1 st0 pt ir0 iin ipen.
          rewrite /get_origins_c. 
          by smt(get_setE mem_set in_fsetU in_fset1).
        move => i1 st0 t0 k0 ir0 iin ipen.
        rewrite /get_partners_c.
        rewrite filter_set.
        rewrite rem_id. 
        rewrite mem_filter negb_and. smt().
        have := inv3 i1 st0 t0 k0 ir0 iin ipen.
        rewrite /get_partners_c. 
        by smt(get_setE mem_set in_fsetU in_fset1).
      auto => />.
    auto => />.
  auto => /#.

+ proc; inline.
  sp 1 1; if {2} => //.
  + sp 0 2; if => //.
    + match = => //. auto => />. smt(joinE).
      + auto => />.
      move => st.
      match = => //. auto => />.
      + move => s t k ir.
        if => //.
        + auto => /#.
        + if => //.
          + auto => /> &1 &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).
            rewrite -fmap_eqP. smt(joinE get_setE). 
          auto => /> &1 &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).
          rewrite -fmap_eqP. smt(joinE get_setE). 
        auto => />.
      auto => />.
    auto => />.
  if {1} => //.
  match {1} => //.
  match {1} => //.
  rcondf {1} ^if. auto => />. smt(joinE).
  auto => />.

+ proc; inline.
  sp 1 1; if {2} => //.
  + sp 0 3; if => //.
    + match = => //.
      + auto => />.
      move => st.
      match = => //.
      + move => s pt ir.
        auto => />.
      + move => s t k ir.
        if => //.
        + auto => /> &1 &2 *.
          rewrite /fresh_partner_s.
          rewrite /get_origins_s /get_fresh_partners_s.
          have->: (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) =>
               exists (m2o : (pkey * tag) option), get_trace val = Some (t.`1, m2o)) (GAKEb_hon.c_smap{1} + Hon_Red.dhc_smap{1}))) = (fdom
               (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) => exists (m2o : (pkey * tag) option), get_trace val = Some (t.`1, m2o)) GAKEb_hon.c_smap{1})).
          + rewrite fsetP.
            move => x.
            do rewrite mem_fdom mem_filter.
            by smt(joinE).
          have->: (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) =>
                  (exists (m2o : (pkey * tag) option), get_trace val = Some (t.`1, m2o)) /\ get_ir_test val = false /\ get_ir_sess val = false /\ get_ir_eph val = false)
               (GAKEb_hon.c_smap{1} + Hon_Red.dhc_smap{1}))) = (fdom (filter (fun (_ : int) (val : pr_st_client GAKEc.instance_state) =>
                  (exists (m2o : (pkey * tag) option), get_trace val = Some (t.`1, m2o)) /\ get_ir_test val = false /\ get_ir_sess val = false /\ get_ir_eph val = false)
               GAKEb_hon.c_smap{1})). 
          + rewrite fsetP.
            move => x.
            do rewrite mem_fdom mem_filter.
            by smt(joinE).
          by smt().
        + if => //.
          + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? inv inv2 inv3 *. do !split; 2..5: smt(get_setE mem_set in_fsetU in_fset1). 
            + congr. rewrite /get_fresh_partners_s.
              rewrite fsetP.
              move => x.
              do rewrite mem_fdom mem_filter.
              by smt(joinE).
            + move => i1 st0 pt ir0 m3 iin ipen.
              rewrite /get_partners_c.
              rewrite filter_set.
              rewrite rem_id. 
              rewrite mem_filter negb_and. smt().
              have := inv i1 st0 pt ir0 m3 iin ipen.
              rewrite /get_partners_c. 
              by smt(get_setE mem_set in_fsetU in_fset1).
            + move => i1 st0 pt ir0 iin ipen.
              rewrite /get_origins_c.
              rewrite filter_set.
              rewrite rem_id. 
              rewrite mem_filter negb_and. smt().
              have := inv2 i1 st0 pt ir0 iin ipen.
              rewrite /get_origins_c. 
              by smt(get_setE mem_set in_fsetU in_fset1).
            move => i1 st0 t0 k0 ir0 iin ipen.
            rewrite /get_partners_c.
            rewrite filter_set.
            rewrite rem_id. 
            rewrite mem_filter negb_and. smt().
            have := inv3 i1 st0 t0 k0 ir0 iin ipen.
            rewrite /get_partners_c. 
            by smt(get_setE mem_set in_fsetU in_fset1).
          auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? inv inv2 inv3 *. do !split; 2..5: smt(get_setE mem_set in_fsetU in_fset1).
          + congr. rewrite /get_fresh_partners_s.
            rewrite fsetP.
            move => x.
            do rewrite mem_fdom mem_filter.
            by smt(joinE).
          + move => i1 st0 pt ir0 m3 iin ipen.
            rewrite /get_partners_c.
            rewrite filter_set.
            rewrite rem_id. 
            rewrite mem_filter negb_and. smt().
            have := inv i1 st0 pt ir0 m3 iin ipen.
            rewrite /get_partners_c. 
            by smt(get_setE mem_set in_fsetU in_fset1).
          + move => i1 st0 pt ir0 iin ipen.
            rewrite /get_origins_c.
            rewrite filter_set.
            rewrite rem_id. 
            rewrite mem_filter negb_and. smt().
            have := inv2 i1 st0 pt ir0 iin ipen.
            rewrite /get_origins_c. 
            by smt(get_setE mem_set in_fsetU in_fset1).
          move => i1 st0 t0 k0 ir0 iin ipen.
          rewrite /get_partners_c.
          rewrite filter_set.
          rewrite rem_id. 
          rewrite mem_filter negb_and. smt().
          have := inv3 i1 st0 t0 k0 ir0 iin ipen.
          rewrite /get_partners_c. 
          by smt(get_setE mem_set in_fsetU in_fset1).
        auto => />.
      move => pr t ir.
      auto => />.
    auto => />.
  if {1} => //.
  match None {1} ^match. auto => /#.
  auto => />.

auto => />; smt(fmap_eqP joinE mem_empty emptyE).*)
qed.


lemma gake_st bit &m: Pr[GAKEc.E_GAKE(GAKEb_hon(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), A).run(bit) @ &m : res] 
                = Pr[GAKEc.E_GAKE(GAKEb_st(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), A).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline.
call (: ={b0, servers, c_smap, s_smap, tested}(GAKEb_hon, GAKEb_st) /\ ={m}(GAKEc.HROc.RO, GAKEc.HROc.RO)); try sim />.

+ proc; inline.
  auto => />.
qed.


lemma gake_st_mod bit &m: `| Pr[GAKEc.E_GAKE(GAKEb_st(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), A).run(bit) @ &m : res]
                 - Pr[GAKE_mod.E_GAKE(GAKE_mod.GAKEb(NTOR_S_mod(GAKE_mod.HROc.RO), NTOR_C_mod(GAKE_mod.HROc.RO), GAKE_mod.HROc.RO), Name_Red(A)).run(bit) @ &m : res] | 
                     <= Pr[GAKEc.E_GAKE(GAKEb_st(NTOR_S(GAKEc.HROc.RO), NTOR_C(GAKEc.HROc.RO), GAKEc.HROc.RO), A).run(bit) @ &m : GAKEb_st.stop].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Name_Red.O_GAKE.stop => //; first last.
+ smt().
symmetry; proc; inline*.
wp; call (: Name_Red.O_GAKE.stop
          , ={b0, tested}(GAKEb_st, GAKE_mod.GAKEb) /\ ={pk_set, stop}(GAKEb_st, Name_Red.O_GAKE)

               /\ (forall x, x \in GAKEc.HROc.RO.m{1} => x.`3 \in Name_Red.O_GAKE.sid_pk{2} => !get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[x.`3]) 
                    => x \notin Name_Red.O_GAKE.unreg_ro{2}
                    => GAKEc.HROc.RO.m{1}.[x] = GAKE_mod.HROc.RO.m{2}.[(x.`1, x.`2, get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[x.`3]), x.`4, x.`5)])

               /\ (forall x, x \in GAKEc.HROc.RO.m{1} => (x \in  Name_Red.O_GAKE.unreg_ro{2})
                                      \/ (x.`3 \in Name_Red.O_GAKE.sid_pk{2} /\ !get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[x.`3]) 
                                           /\ (x.`1, x.`2, get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[x.`3]), x.`4, x.`5) \in GAKE_mod.HROc.RO.m{2}))

               /\ (forall x, x \notin GAKEc.HROc.RO.m{1} => x.`3 \in Name_Red.O_GAKE.sid_pk{2} => !get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[x.`3])
                    => (x.`1, x.`2, get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[x.`3]), x.`4, x.`5) \notin GAKE_mod.HROc.RO.m{2})

               /\ (forall x, x \in Name_Red.O_GAKE.unreg_ro{2} => x \in GAKEc.HROc.RO.m{1} /\ Name_Red.O_GAKE.unreg_ro{2}.[x] = GAKEc.HROc.RO.m{1}.[x])

               /\ (forall x, x \in GAKEb_st.unreg_ro{1} <=> x \in Name_Red.O_GAKE.unreg_ro{2})

               /\ (forall x, x \in GAKEc.HROc.RO.m{1} => x.`4 \in Name_Red.O_GAKE.pk_set{2} /\ x.`5 \in Name_Red.O_GAKE.pk_set{2})
               /\ (forall x, x \in GAKE_mod.HROc.RO.m{2} => x.`4 \in Name_Red.O_GAKE.pk_set{2} /\ x.`5 \in Name_Red.O_GAKE.pk_set{2})

               /\ (forall i, i \in GAKEb_st.c_smap{1} <=> i \in GAKE_mod.GAKEb.c_smap{2})

               /\ (forall i, i \in GAKE_mod.GAKEb.c_smap{2} => rem_sid_c (oget GAKEb_st.c_smap{1}.[i]) = oget GAKE_mod.GAKEb.c_smap{2}.[i])

               /\ (forall b j, (b, j) \in GAKEb_st.s_smap{1} => b \in Name_Red.O_GAKE.sid_pk{2} /\ !(get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[b])
                                     /\ (get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b]), j) \in GAKE_mod.GAKEb.s_smap{2}
                                     /\ rem_sid_s (oget GAKEb_st.s_smap{1}.[(b, j)]) = oget GAKE_mod.GAKEb.s_smap{2}.[(get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b]), j)]))

               /\ (forall b j, b \in Name_Red.O_GAKE.sid_pk{2} => !get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[b])
                    => (get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b]), j) \in GAKE_mod.GAKEb.s_smap{2} 
                    <=> (b, j) \in GAKEb_st.s_smap{1})

               /\ (forall b, b \in GAKEb_st.servers{1} <=> b \in Name_Red.O_GAKE.sid_pk{2})

               /\ (forall b, b \in GAKEb_st.servers{1} => get_pkey (oget GAKEb_st.servers{1}.[b]) = get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b])
                                      /\ (get_sr_in (oget Name_Red.O_GAKE.sid_pk{2}.[b]) = get_sr_ltk (oget GAKEb_st.servers{1}.[b]))
                                      /\ (get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[b]) = get_sr_dh (oget GAKEb_st.servers{1}.[b])))

               /\ (forall b kp, b \in GAKEb_st.servers{1} => oget GAKEb_st.servers{1}.[b] = Honest kp
                    => b \in Name_Red.O_GAKE.sid_pk{2} /\ oget Name_Red.O_GAKE.sid_pk{2}.[b] = Inner kp.`1 false 
                                      /\ kp.`1 \in GAKE_mod.GAKEb.servers{2} /\ oget GAKE_mod.GAKEb.servers{2}.[kp.`1] = Honest kp.`2)

               /\ (forall b kp, b \in GAKEb_st.servers{1} => oget GAKEb_st.servers{1}.[b] = Corrupt kp
                    => b \in Name_Red.O_GAKE.sid_pk{2} /\ oget Name_Red.O_GAKE.sid_pk{2}.[b] = Inner kp.`1 true 
                                      /\ kp.`1 \in GAKE_mod.GAKEb.servers{2} /\ oget GAKEb.servers{2}.[kp.`1] = Corrupt kp.`2)

               /\ (forall b pk, b \in GAKEb_st.servers{1} => oget GAKEb_st.servers{1}.[b] = Dishonest pk
                    => b \in Name_Red.O_GAKE.sid_pk{2} /\ oget Name_Red.O_GAKE.sid_pk{2}.[b] = Outer pk)

               /\ (forall b, b \in GAKEb_st.servers{1} => obind get_skey GAKEb_st.servers{1}.[b] = None 
                   <=> oget Name_Red.O_GAKE.sid_pk{2}.[b] = Outer (get_pkey (oget GAKEb_st.servers{1}.[b])))

               /\ (forall b, b \in GAKEb_st.servers{1} => !get_sr_dh (oget GAKEb_st.servers{1}.[b]) => get_pkey (oget GAKEb_st.servers{1}.[b]) \in GAKEb.servers{2})

               /\ (forall pk b sk1 sk2, pk \in GAKEb.servers{2} => obind GAKE_mod.get_skey GAKEb.servers{2}.[pk] = Some sk1 
                    => b \in GAKEb_st.servers{1} => obind GAKEc.get_skey GAKEb_st.servers{1}.[b] = Some sk2 
                    => b \in Name_Red.O_GAKE.sid_pk{2} => get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b]) = pk => sk1 = sk2)

               /\ (forall b, b \in Name_Red.O_GAKE.sid_pk{2} => get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b{2}]) \in Name_Red.O_GAKE.pk_set{2})

               /\ (forall b, b \in Name_Red.O_GAKE.sid_pk{2} => !get_sr_in (oget Name_Red.O_GAKE.sid_pk{2}.[b]) => !get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[b]))

               /\ (forall b pk bool, b \in Name_Red.O_GAKE.sid_pk{2} => oget Name_Red.O_GAKE.sid_pk{2}.[b] = Inner pk bool
                    =>  obind GAKE_mod.get_skey GAKEb.servers{2}.[pk] <> None)

               /\ (forall sk, g ^ sk \in GAKEb.servers{2} => obind GAKE_mod.get_skey GAKEb.servers{2}.[g ^ sk] = Some sk)

               /\ (forall sk pk bool b, b \in Name_Red.O_GAKE.sid_pk{2} => oget Name_Red.O_GAKE.sid_pk{2}.[b] = Inner pk bool
                    => pk \in GAKEb.servers{2} => obind GAKE_mod.get_skey GAKEb.servers{2}.[pk] = Some sk 
                    => pk = g ^ sk)

               /\ (forall pk j x1 x2 x4 x5, pk \notin Name_Red.O_GAKE.pk_set{2} 
                    => pk \notin GAKE_mod.GAKEb.servers{2} /\ (pk, j) \notin GAKE_mod.GAKEb.s_smap{2} /\ (x1, x2, pk, x4, x5) \notin GAKE_mod.HROc.RO.m{2})

               /\ (forall b1 b2, b1 \in Name_Red.O_GAKE.sid_pk{2} => b2 \in Name_Red.O_GAKE.sid_pk{2} 
                    => !get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[b1]) => !get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[b2])  
                    => get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b1]) = get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b2])
                    => b1 = b2)

(*
               /\ (forall b, 

               /\ (forall b j, (b, j) \in GAKEb_st.s_smap{1} => b \in Meta_Red.O_GAKE.sid_pk{2} /\ !get_sr_out (oget Meta_Red.O_GAKE.sid_pk{2}.[b])
                                      /\ (get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b]), j) \in GAKE_mod.GAKEb.s_smap{2}
                                      /\ rem_sid_s (oget GAKEb_st.s_smap{1}.[(b, j)]) = oget GAKE_mod.GAKEb.s_smap{2}.[(get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b]), j)])

               /\ (forall b j, (b, j) \notin GAKEb_st.s_smap{1} => b \in Meta_Red.O_GAKE.sid_pk{2} => !get_sr_out (oget Meta_Red.O_GAKE.sid_pk{2}.[b])
                    => (get_pkey_mod (oget Meta_Red.O_GAKE.sid_pk{2}.[b]), j) \notin GAKE_mod.GAKEb.s_smap{2})

             (*  /\ (forall pk, pk \in GAKE_mod.GAKEb.servers{2} <=> (exists bool, rng Meta_Red.O_GAKE.sid_pk{2} (Inner pk bool)))*)




               /\ (forall pk bool, pk \notin GAKE_mod.GAKEb.servers{2} => !rng Meta_Red.O_GAKE.sid_pk{2} (Inner pk bool))
*)
          , GAKEb_st.stop{1} = Name_Red.O_GAKE.stop{2}) => //.

- exact A_ll.

admit. (*
- proc; inline.
  sp 0 1; if {2} => //.
  + if {1} => //.
    + rcondf {2} ^if. auto => /#.
      sp; seq 1 1 : (#pre /\ r0{1} = tk{2}). auto => />.
      if => //. auto => /> &1 &2 *. split. smt(). smt().
      + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
      auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
    rcondt {2} ^if. auto => /#. 
    if {2} => //.
    + sp 1 0; seq 1 0 : (#pre /\ r0{1} \in (dtag `*` dkey)). auto => />.
      rcondf {1} ^if. auto => /#.
      auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1). 
    sp. seq 1 1 : (#pre /\ ={r0}). auto => />.
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
  auto => /> &1 &2 *.*)
- move => &2 bad; proc; inline. auto => />.
  by rewrite weight_dprod dkey_ll dtag_ll //=.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp; if {2} => //.
  + if => //.
    + auto => />. smt().
    + sp; seq 1 1 : (#pre /\ ={sk_s}). auto => />.
      sp 2 2; if {2} => //.
      + auto => /> &1 &2 *. do !split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
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
  + rcondt {1} ^if. auto => /#.
  + auto => /> &1 &2 *. do !split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
  auto => /> &1 &2 *. smt().
- move => &2 bad; proc; inline. auto => />.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  case (Name_Red.O_GAKE.stop{2}). 
  + rcondf {2} ^if. auto => />.
    sp; if {1} => //. 
    + sp; match {1} => //. 
      + sp; seq 1 0 : (#pre /\ sk_ce{1} \in dt); auto => />. 
      auto => />. 
    auto => />.
  sp 1 1; if {2} => //.
  + sp 1 6; if => //; 1: by auto => /#.
    + sp 1 0. match; 1..2: smt().
      + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
      move => stl str.
      auto => />.
    auto => />.
  rcondf {1} ^if. auto => /#.
  auto => />.
- move => &2 bad; proc; inline.
  sp; if => //. 
  + sp; match. 
    + auto => />.
      by rewrite dt_ll bad //=.
    auto => />.
  auto => />. 
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  case (Name_Red.O_GAKE.stop{2}). 
  + rcondf {2} ^if. auto => />.
    sp; match {1} => //. 
    + auto => />.
    match {1} => //. 
    sp; match {1} => //.
    + auto => />.
    auto => />.
  sp 1 1; if {2} => //.
  + sp 1 1. match {2}.
    + sp 0 5. match. smt(). move => &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      + auto => />. smt(get_setE mem_set in_fsetU in_fset1).
      move => skl skr.
      match; 1..2: smt().
      + sp; match; 1..2: smt().
        + auto => />.
        move => stl str.
        sp. seq 1 1 : (#pre /\ ={sk_se}). auto => />. 
        sp; seq 1 1 : (#pre /\ r1{1} = r2{2}). auto => />.
        if {1} => //. rcondt {2} ^if. auto => /#.
        + auto => /> &1 &2 *. split. move => *. do !split; ~8: smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
move => b1 j1.
case ((b1, j1) = (b,j){2}) => [] bjneq.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite mem_set //=.
do rewrite get_setE //=.
case (j1 = j{2}) => beq; 2: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
simplify.
have->: (b1 <> b{2}). smt().
simplify.
move => bjin.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite negb_and.
case (get_sr_out (oget Name_Red.O_GAKE.sid_pk{2}.[b1])); 2: by smt().
simplify.
admit. (* WHAT *)


          move => *. do !split; ~8: smt(get_setE mem_set in_fsetU in_fset1 pow_bij). admit.
        if {2} => //. 
        + sp; match Some {1} ^match. auto => /#.
          match Some {2} ^match. auto => /#.
          sp 3 4; if => //.
          + auto => /> &1 &2 *. smt().
          auto => /> &1 &2 *. smt().
        auto => />. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
      auto => />. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
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
  + sp; match; 1..2: smt().
    + auto => />.
    move => stl str.
    match {1} => //.
    + match Pending {2} ^match. auto => /#.
      sp; seq 1 1 : (#pre /\ r1{1} = r2{2}). auto => />.
      if {1} => //. rcondt {2} ^if. auto => /> &2 *. admit. (* connect things to state *)
      + sp 2 2; if => //. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
        + sp; match Some {1} ^match. auto => /#.
          match Some {2} ^match. auto => /#.
          auto => /> &1 &2 *. split. move => *. do !split; 4,7,9: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
            admit. admit. admit. admit. admit. admit. admit. move => *. do !split; 4,7: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
            admit. admit. admit. admit. admit. admit. admit.
          sp; match None {1} ^match. auto => /#.
          match None {2} ^match. auto => /#.
          auto => /> &1 &2 *. do !split; 4,7,8: smt(get_setE mem_set in_fsetU in_fset1 pow_bij). admit. admit. admit. admit. admit. admit. admit.
    + match Accepted {2} ^match. auto => /#.
      auto => />.
    match Aborted {2} ^match. auto => /#.
    auto => />.
  match {1} => //.
  match {1} => //.
  auto => />.
- move => &2 bad; proc; inline.
  sp; match => //.
  match => //; auto => />.  
  by rewrite weight_dprod dkey_ll dtag_ll //=.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //; 2: by auto => /#.
  sp; match; 1..2: smt().
  + auto => />.
  move => stl str.
  match {1} => //.
  + match Pending {2} ^match. auto => /#.
    auto => />.
  + match Accepted {2} ^match. auto => /#.
    if => //.
    + auto => /> &1 &2 *. split. rewrite /untested_partner_c. move => [H1|]. smt(). 
case (1 <= card (get_partners_c t'{1} GAKEb_st.s_smap{1})); 2: smt().
case (1 <= card (get_untested_partners_c t'{1} GAKEb_st.s_smap{1}) = false); 2: smt().
move => *.
right.
have<-: (card (get_partners_c t'{1} GAKEb_st.s_smap{1}) = card (get_partners_c t'{2} GAKEb.s_smap{2})).
rewrite /get_partners_c. 
admit.
have<-: (card (get_untested_partners_c t'{1} GAKEb_st.s_smap{1}) = card (get_untested_partners_c t'{2} GAKEb.s_smap{2})). admit.
smt().
 move => [] *. smt(). admit. (* relate untested_partner_c *)
      + auto => />. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      auto => />.
  match Aborted {2} ^match. auto => /#.
  auto => />.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match {2}.
    + sp. match; 1..2: smt(). 
      + auto => />.
      move => stl str.
      match {1}. 
      + match Pending {2} ^match. auto => />.
        auto => />.
      + match Accepted {2} ^match. auto => /#.
        auto => /> &1 &2 *. split.  move => *. split. rewrite negb_or. split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). admit. move => *. split.  smt(get_setE mem_set in_fsetU in_fset1 pow_bij). split. 
move => b1 j1.
case ((b1, j1) = (b, j){2}) => [[] b1eq j1eq | bjneq].
rewrite mem_set b1eq j1eq //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite mem_set bjneq //=.
admit.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij). admit.
      match Aborted {2} ^match. auto => /#.
      auto => />.
    match None {1} ^match. auto => />. admit. (* A dishonest server is never in s_smap *)
    auto => />.
  auto => /#.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match Some {1} ^match. auto => /#.
    match {1} => //.
    + match Inner {2} ^match. auto => /#.
    + match Some {2} ^match. auto => /#.
      match Honest {2} ^match. auto => />. admit.
      sp 0 4; if => //.
      + auto => /> &1 &2 *. admit. (* relate things *)
      + auto => /> &1 &2 *. split. admit. split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). split.
move => x.
case (x.`3 = b{2}).
 smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
 smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). split. 
move => b1 b2.
case (b1 = b{2}) => b1eq.
case (b2 = b{2}) => b2eq. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have: get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b1]) = pk{2}. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
case (b2 = b{2}) => b2eq. 
have: get_pkey_mod (oget Name_Red.O_GAKE.sid_pk{2}.[b2]) = pk{2}. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

split. admit. split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). split. admit. split. admit. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
      auto => />.
    + match Inner {2} ^match. auto => /#.
      match Some {2} ^match. auto => /#.
      match Corrupt {2} ^match. auto => />. admit.
      auto => />.
    match Outer {2} ^match. auto => /#.
    auto => />.
  match {1} => //. match {1} => //. auto => /#.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match; 1..2: smt().
    + auto => />.
    move => stl str.
    match {1} => //.
    + match Pending {2} ^match. auto => /#.
      auto => /> &1 &2 *. split. move => *. split. admit. move => *. split. admit. split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). admit. admit.
    + match Accepted {2} ^match. auto => /#. 
      auto => /> &1 &2 *. admit.
    match Aborted {2} ^match. auto => /#.
    auto => />.
  match {1}; auto => />.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match {2}.
    + sp. match; 1..2: admit. (* same as above *)
      + auto => />.
      move => stl str.
      match {1}. 
      + match Pending {2} ^match. auto => /#.
        auto => />.
      + match Accepted {2} ^match. auto => /#.
        auto => /> &1 &2 *. split. move => *. split. admit. move => *. split. admit. split. admit. smt(get_setE mem_set in_fsetU in_fset1 pow_bij). admit.
      match Aborted {2} ^match. auto => /#.
      auto => />.
    match None {1} ^match. auto => />. admit. (* A dishonest server is never in s_smap *)
    auto => />.
  auto => /#.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp. if => //.
    + match; 1..2: smt().
      + auto => />.
      move => stl str.
      match {1} => //.
      + match Pending {2} ^match. auto => /#.
        auto => />.
      + match Accepted {2} ^match. auto => /#.
        if => //.
        + auto => &1 &2 *. admit.
        + if => //.
          + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
          auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
        auto => />.
      match Aborted {2} ^match. auto => /#.
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
  + sp 0 1; match {2} => //.
    + sp; if => //.
      + match; 1..2: admit. (* same again *)
        + auto => />.
        move => stl str.
        match {1} => //.
        + match Pending {2} ^match. auto => /#.
          auto => />.
        + match Accepted {2} ^match. auto => /#.
          if => //.
          + auto => &1 &2 *. admit.
          + if => //.
            + auto => /> &1 &2 *. split. smt(get_setE mem_set in_fsetU in_fset1). split. admit. admit.
            auto => /> &1 &2 *. split. admit. admit.
          auto => />.
        match Aborted {2} ^match. auto => /#.
        auto => />.
      auto => />.
    if {1} => //.
    match None {1} ^match. auto=> />. admit. 
    auto => />.
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
move => roeq inj csm ssm pkin inv inv2 inv3 inv4 inv5 inv6 inv7 inv8 inv9 inv10 inv11 inv12 inv13 inv14 inv15 rl rr al csl pksl ssl sl stl tl url ml ar csr tr str huh ssr sr pksr urr mr.
by case : (!str) => />.
qed.
