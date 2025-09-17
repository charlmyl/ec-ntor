require import AllCore FSet FMap Distr DProd List SplitRO NTOR Games.
(*   *) import GAKEc HROc.
require (*  *) DiffieHellman.
(*   *) import StdBigop.Bigreal.BRA StdOrder.RealOrder DH.G DH.GP DH.FD DH.GP.ZModE.

(* ------------------------------------------------------------------------------------------ *)
(* Modified protocol and experiment *)
(* ------------------------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------------------------ *)
(* Modified rondom oracle *)
type pr_st_client_mod = pkey * skey.
type pr_st_server_mod = skey * skey option.

type h_mod_input = pkey * pkey * pkey * pkey * pkey.

clone import PROM.FullRO as HRO_mod_c with
  type in_t    <= h_mod_input,
  type out_t   <= tag * key,
  op   dout _  <= dtag `*` dkey,
  type d_in_t  <= unit,
  type d_out_t <= bool
proof *.

module type Server_mod = {
  proc keygen() : pkey * skey
  proc respond_session(st: pr_st_server_mod option, pk: pkey) : (pr_st_server_mod * (pkey * tag) * key) option
}.

module type Client_mod = {
  proc new_session(pk: pkey) : pr_st_client_mod * pkey
  proc complete_session(st: pr_st_client_mod, m: pkey * tag) : (pr_st_client_mod * key) option
}.

(* ------------------------------------------------------------------------------------------ *)
(* Protocol using all public values as input *)
module NTOR_S_mod (H : RO) : Server_mod = {
  proc keygen() : (pkey * skey) = {
    var sk_s, pk_s;

    sk_s <$ dt;
    pk_s <- g ^ sk_s;

    return (pk_s, sk_s);
  }

  proc respond_session(st : pr_st_server_mod option, m2: pkey) : (pr_st_server_mod * (pkey * tag) * key) option = {
    var sk_b, pk_se, sk_se, sko;
    var sk, t_B;
    var r <- None;
    
    match st with 
    | None => {}
    | Some st => {
        (sk_b, sko) <- st;
        sk_se <$ dt;
        pk_se <- g ^ sk_se;
        
        (t_B, sk) <@ H.get(m2 ^ sk_se, m2 ^ sk_b, g ^ sk_b, m2, pk_se);
        r <- Some ((sk_b, Some sk_se), (pk_se, t_B), sk);
      }
    end;
    return r;
  }
}.

module NTOR_C_mod (H : RO) : Client_mod = {
  proc new_session(pk) : pr_st_client_mod * pkey = {
    var pk_ce, sk_ce;

    sk_ce <$ dt;
    pk_ce <- g ^ sk_ce;

    return ((pk, sk_ce), pk_ce);
  }

  proc complete_session(st: pr_st_client_mod, m3: pkey * tag) : (pr_st_client_mod * key) option = {
    var r <- None;
    var pk_b, sk_ce, sk, t_A;

    (pk_b, sk_ce) <- st;
    (t_A, sk) <@ H.get(m3.`1 ^ sk_ce, pk_b ^ sk_ce, pk_b, g ^ sk_ce, m3.`1);
    if (t_A = m3.`2) {
      r <- Some (st, sk);
    }
    return r;
  }
}.

(********************************************************************************)
(* helping operators for getting a set of all partners (with some specific revealed status *)
op get_partners_mod_c (t: trace) (fmap: (pkey * int, pr_st_server_mod instance_state) fmap) : (pkey * int) fset =
fdom (
  filter
  (fun bj (val: pr_st_server_mod instance_state) =>
       get_trace val = Some t (* Partners share the same trace *)
  )
  fmap
).

op get_partners_mod_s (t: trace) (fmap: (int, pr_st_client_mod instance_state) fmap) : int fset =
fdom (
  filter
  (fun i (val: pr_st_client_mod instance_state) =>
       get_trace val = Some t (* Partners share the same trace *)
  )
  fmap
).

op get_origins_mod_c (t: trace) (fmap: (pkey * int, pr_st_server_mod instance_state) fmap) : (pkey * int) fset =
fdom (
  filter
  (fun bj (val: pr_st_server_mod instance_state) =>
       (exists m2o, get_trace val = Some (fst t, m2o)) (* Partners share the same (partial) trace *)
  )
  fmap
).

op get_origins_mod_s (t: trace) (fmap: (int, pr_st_client_mod instance_state) fmap) : int fset =
fdom (
  filter
  (fun i (val: pr_st_client_mod instance_state) =>
       (exists m2o, get_trace val = Some (fst t, m2o)) (* Partners share the same (partial) trace *)
  )
  fmap
).

op get_untested_partners_mod_c (t: trace) (fmap: (pkey * int, pr_st_server_mod instance_state) fmap) : (pkey * int) fset =
fdom (
  filter
  (fun bj (val: pr_st_server_mod instance_state) =>
       get_trace val = Some t  (* Partners share the same trace *)
    /\ get_ir_test val = false (* Partner is not tested *)
  )
  fmap
).

op get_untested_partners_mod_s (t: trace) (fmap: (int, pr_st_client_mod instance_state) fmap) : int fset =
fdom (
  filter
  (fun i (val: pr_st_client_mod instance_state) =>
       get_trace val = Some t  (* Partners share the same trace *)
    /\ get_ir_test val = false (* Partner is not tested *)
  )
  fmap
).

op get_untested_origins_mod_c (t: trace) (fmap: (pkey * int, pr_st_server_mod instance_state) fmap) : (pkey * int) fset =
fdom (
  filter
  (fun bj (val: pr_st_server_mod instance_state) =>
       (exists m2o, get_trace val = Some (fst t, m2o)) (* Partners share the same (partial) trace *)
    /\ get_ir_test val = false                         (* Partner is not tested *)
  )
  fmap
).


op get_fresh_partners_mod_c (t: trace) (fmap1: (pkey * int, pr_st_server_mod instance_state) fmap) (fmap2: (pkey, skey option) fmap) : (pkey * int) fset =
fdom (
  filter
  (fun bj (val: pr_st_server_mod instance_state) =>
       get_trace val = Some t                                    (* Partners share the same trace *)
    /\ get_ir_test val = false                                   (* Partner is not tested *)
    /\ get_ir_sess val = false                                   (* Partner is not revealed *)
    /\ (get_ir_eph val = false \/ (oget fmap2.[fst bj]) <> None) (* Partner is not trivially broken *)
  )
  fmap1
).

(* since ephkey reveal is permitted on Pending client instances we need to consider partial traces for partnering *)
op get_fresh_partners_mod_s (t : trace) (fmap: (int, pr_st_client_mod instance_state) fmap) : int fset =
fdom (
  filter
  (fun i (val: pr_st_client_mod instance_state) =>
       (* CHECK: we consider *any* client that has sent this first message to be a pre-partner *)
       (exists m2o, get_trace val = Some (fst t, m2o)) (* Partners share the same (partial) trace *)
    /\ get_ir_test val = false                         (* Partner is not tested *)
    /\ get_ir_sess val = false                         (* Partner is not revealed *)
    /\ get_ir_eph val = false                          (* Partner is not trivially broken *)
  )
  fmap
).

(* operators that return None if there is no partner, true if there is an untested/fresh partner or false if all partners are tested/unfresh *)
op untested_origins_mod_c (t: trace) (fmap: (pkey * int, pr_st_server_mod instance_state) fmap) : bool option =
if 1 <= card (get_origins_mod_c t fmap) then Some (1 <= card (get_untested_origins_mod_c t fmap)) else None.

op untested_partner_mod_c (t: trace) (fmap: (pkey * int, pr_st_server_mod instance_state) fmap) : bool option =
if 1 <= card (get_partners_mod_c t fmap) then Some (1 <= card (get_untested_partners_mod_c t fmap)) else None.

op fresh_partner_mod_c (t: trace) (fmap1: (pkey * int, pr_st_server_mod instance_state) fmap) (fmap2: (pkey, skey option) fmap) : bool option =
if 1 <= card (get_origins_mod_c t fmap1) then Some (1 <= card (get_fresh_partners_mod_c t fmap1 fmap2)) else None.

op untested_partner_mod_s (t: trace) (fmap: (int, pr_st_client_mod instance_state) fmap) : bool option =
if 1 <= card (get_partners_mod_s t fmap) then Some (1 <= card (get_untested_partners_mod_s t fmap)) else None.

op fresh_partner_mod_s (t: trace) (fmap: (int, pr_st_client_mod instance_state) fmap) : bool option =
if 1 <= card (get_origins_mod_s t fmap) then Some (1 <= card (get_fresh_partners_mod_s t fmap)) else None.


(* Modified GAKE game *)
module type GAKE_mod_out = {
  proc h(input: h_mod_input) : tag * key

  proc init_s() : pkey
  proc set_cert(pk: pkey) : unit option

  proc send_msg1(i: int, m1: pkey) : pkey option
  proc send_msg2(b: pkey, j: int, m2: pkey) : (pkey * tag) option

  proc s_rev_skey(b: pkey, j: int) : key option
  proc rev_ltkey(b: pkey) : skey option
  proc s_rev_ephkey(b: pkey, j: int) : skey option
  proc s_test(b: pkey, j: int) : key option

  include GAKE_out [send_msg3, c_rev_skey, c_rev_ephkey, c_test]
}.

module type GAKE_mod_out_i = {
  include GAKE_mod_out

  proc init_mem(b : bool) : unit
}.

module GAKEb_mod (S: Server_mod) (C: Client_mod) (H : RO) : GAKE_mod_out = {
  var b0 : bool 

  var s_kp : (pkey, skey option) fmap
  var c_smap : (int, pr_st_client_mod instance_state) fmap
  var s_smap : (pkey * int, pr_st_server_mod instance_state) fmap
  
  var tested : int option

  proc init_mem(b: bool) : unit = {
    b0 <- b;
    H.init();
    s_kp <- empty;
    c_smap <- empty;
    s_smap <- empty;
    tested <- None;
  }

  (* random oracle *)
  proc h = H.get
  
  (* server management *)
  proc init_s() : pkey = {
    var kp;

    kp <@ S.keygen();
    s_kp.[kp.`1] <- Some kp.`2;

    return kp.`1;
  }

  proc set_cert(pk: pkey) : unit option = {
    var r <- None;

    s_kp.[pk] <- None;
    r <- Some ();

    return r;
  }

  proc send_msg1(i: int, m1: pkey) : pkey option = {
    var st, st', m2;
    var r <- None;

    st <- c_smap.[i];
    if (m1 \in s_kp) {
      match st with
      | None => {
          (st', m2) <@ C.new_session(m1);
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
    return r;
  }

  proc send_msg2(b: pkey, j: int, m2: pkey) : (pkey * tag) option = {
    var sko, resp, st', k, m3;
    var r <- None;

    sko <- oget s_kp.[b];
    if (sko is Some sk) (* Server was initialised as honest *) {
      match s_smap.[b, j] with
      | None => {
          resp <@ S.respond_session(Some (sk, None), m2);
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
          if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_mod_c t' s_smap = Some false)) {
            k <- Some k';
            c_smap.[i] <- set_ir_sess (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }

  proc s_rev_skey(b: pkey, j: int) : key option = {
    var k <- None;

    match s_smap.[(b, j)] with
    | None => { }
    | Some st => {
        (* only accepted server instances that are not tested and 
           that not only have tested partners can be sesskey revealed *)
        if (st is Accepted st' t' k' ir') {
          if (!(get_ir_test (oget s_smap.[b, j]) \/ untested_partner_mod_s t' c_smap = Some false)) {
            k <- Some k';
            s_smap.[(b, j)] <- set_ir_sess (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }

  proc rev_ltkey(b: pkey) : skey option = {
    var ltk <- None;

    match s_kp.[b] with
    | None => { }
    | Some sk => {
        (* a server can be ltkey revealed if no instance of it is ephkey revealed 
           in case that instance or all its partners are tested *) 
        if (forall j,
              (b, j) \in s_smap (* just checking instances of b *)
              => !(   (   get_ir_test (oget s_smap.[b, j])
                          (* This is always OK (get_trace always Some on server side *)
                       \/ untested_partner_mod_s (oget (get_trace (oget s_smap.[b, j]))) c_smap = Some false)
                   /\ get_ir_eph (oget s_smap.[b,j]))) {
          ltk <- sk; 
      (*    servers.[b] <- Corrupt kp; *)
          s_kp.[b] <- None; 
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
            if (untested_origins_mod_c (pk_e, None) s_smap <> Some false) {
              ek <- Some (st.`2);
              c_smap.[i] <- set_ir_eph (Pending st pk_e ir);
            }
          }
          (* accepted client instamces can only be ephkey revealed when not tested and 
             if not all partners are tested *)
        | Accepted st t k ir => {
            if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_mod_c t s_smap = Some false)) {
              ek <- Some (st.`2);
              c_smap.[i] <- set_ir_eph (Accepted st t k ir);
            }
          }
        | Aborted _ _ _ => {  }
        end;
      }
    end;
    return ek;
  }

  proc s_rev_ephkey(b: pkey, j: int) : skey option = {
    var ek <- None;

    match s_smap.[b, j] with
    | None => { }
    | Some st => {
        (* only accepted server instances that are not ltkey revealed in case they 
           or all partners are tested can be ephkey revealed *)
        if (st is Accepted st t k ir) { (* No Pending on Server side *)
          if (!((   get_ir_test (oget s_smap.[b, j])
                 \/ untested_partner_mod_s t c_smap = Some false)
                /\ oget s_kp.[b] = None)) {
            ek <- st.`2;
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
                  \/ fresh_partner_mod_c t' s_smap s_kp = Some false)) {
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

  proc s_test(b: pkey, j: int) : key option = {
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
                  \/ (get_ir_eph (oget s_smap.[b, j]) /\ s_kp.[b] = None)
                  \/ fresh_partner_mod_s t' c_smap = Some false)) {
              if (b0 = false) {
                k <- Some k';
                s_smap.[(b, j)] <- set_ir_test (Accepted st' t' k' ir');
              } else {
                ks <$ dkey;
                k <- Some ks;
                s_smap.[(b, j)] <- set_ir_test (Accepted st' t' k' ir');
              }
              tested <- Some (pick (get_fresh_partners_s t' GAKEb.c_smap));
            }
          }
        }
      end;
    }
    return k;
  }
}.


(********************************************************************************)
(* Adversary and Experiment for modified GAKE game *)
module type A_GAKE_mod (O : GAKE_mod_out) = {
  proc run() : bool
}.

module E_GAKE_mod (O: GAKE_mod_out_i) (A : A_GAKE_mod) = {

  proc run(b: bool) : bool = {
    var b' : bool;

    O.init_mem(b);
    
    b' <@ A(O).run();
    
    return b';
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* Reduction preventing collisions and prediction of public keys  *)
type server_state_mod = [
  Honest_mod    of pkey
| Corrupt_mod   of pkey
| Dishonest_mod of pkey
].

op get_pkey_mod s_st =
with s_st = Honest_mod    pk => pk
with s_st = Corrupt_mod   pk => pk
with s_st = Dishonest_mod pk => pk.

op get_sr_mod s_st : bool =
with s_st = Honest_mod    _ => false
with s_st = Corrupt_mod   _ => true
with s_st = Dishonest_mod _ => true.

module (Meta_Red (A : A_GAKE) : A_GAKE_mod) (O : GAKE_mod_out) = {
  module O_GAKE : GAKE_out = {
    var unreg_ro : (pkey * pkey * s_id * pkey * pkey, (tag * key)) fmap

    var servers : (s_id, server_state_mod) fmap
    var pk_set : pkey fset
  (*  var pred_ce : pkey fset
    var pred_se : pkey fset*)
    
    var stop : bool

    proc h(x : h_input) = {
      var pk, tk;
      var r <- (witness, witness);

      if (!stop) {
        if (x.`3 \in servers /\ !get_sr_mod (oget servers.[x.`3])) {
          stop <- stop \/ x \in unreg_ro;
          pk <- get_pkey_mod (oget servers.[x.`3]); 
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

    proc init_s(b: s_id) = {
      var pk;
      var r <- None;

      if (!stop) {
        if (b \notin servers) {
          pk <@ O.init_s();
          stop <- stop \/ pk \in pk_set;
          servers.[b] <- Honest_mod pk;
          pk_set <- pk_set `|` fset1 pk;

        }
        r <- Some (get_pkey_mod (oget servers.[b]));
      }

      return r;
    }

    proc set_cert(b: s_id, pk: pkey) = {
      var r <- None;

      if (!stop /\ b \notin servers) {
        r <@ O.set_cert(pk);
        servers.[b] <- Dishonest_mod pk;
        pk_set <- pk_set `|` fset1 pk;
      }

      return r;
    }

    proc send_msg1(i: int, m1: s_id) = {
      var pk; 
      var r <- None;

      if (!stop /\ m1 \in servers) {
        pk <- get_pkey_mod (oget servers.[m1]);
        r <@ O.send_msg1(i, pk);
       if (r <> None) {
         stop <- stop \/ (oget r \in pk_set);
         pk_set <- pk_set `|` fset1 (oget r);
       }
      }

      return r;
    }

    proc send_msg2(b: s_id, j: int, m2: pkey) = {
      var pk; 
      var r <- None;

      if (!stop /\ b \in servers) {
        if (m2 \notin pk_set) {
          pk_set <- pk_set `|` fset1 m2;
        }

        pk <- get_pkey_mod (oget servers.[b]);
        r <@ O.send_msg2(pk, j, m2);
        if (r <> None) {
          stop <- stop \/ ((oget r).`1 \in pk_set);
          pk_set <- pk_set `|` fset1 (oget r).`1;  
        }
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

      if (!stop /\ b \in servers) {
        pk <- get_pkey_mod (oget servers.[b]);
        r <@ O.s_rev_skey(pk, j);
      }

      return r;     
    }

    proc rev_ltkey(b: s_id) = {
      var pk;
      var r <- None;

      if (!stop /\ b \in servers) {
        pk <- get_pkey_mod (oget servers.[b]);
        r <@ O.rev_ltkey(pk);
        if (r <> None) {
          servers.[b] <- Corrupt_mod pk;
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

      if (!stop /\ b \in servers) {
        pk <- get_pkey_mod (oget servers.[b]);
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

      if (!stop /\ b \in servers) {
        pk <- get_pkey_mod (oget servers.[b]);
        r <@ O.s_test(pk, j);
      }

      return r;
    }
  }

  proc run() : bool = {
    var b';

    O_GAKE.unreg_ro <- empty;
    O_GAKE.servers <- empty;
    O_GAKE.pk_set <- fset0;
    O_GAKE.stop <- false;

    b' <@ A(O_GAKE).run();

    return b';
  }
}.


(* Introduce stop in original game *)
module GAKEb_st (S: Server) (C: Client) (H : HROc.RO) = {
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
    if (m2 \notin pk_set) {
      pk_set <- pk_set `|` fset1 m2;
    }

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
    }

    if (r <> None) {
      stop <- stop \/ (oget r).`1 \in pk_set;
      pk_set <- pk_set `|` fset1 (oget r).`1;
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
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GAKE {-RO, -HROc.RO, -Meta_Red, -GAKEb, -GAKEb_st, -GAKEb_mod }.

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


lemma gake_st bit &m: Pr[E_GAKE(GAKEb(NTOR_S(HROc.RO), NTOR_C(HROc.RO), HROc.RO), A).run(bit) @ &m : res] =  Pr[E_GAKE(GAKEb_st(NTOR_S(HROc.RO), NTOR_C(HROc.RO), HROc.RO), A).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline.
call (: ={b0, servers, c_smap, s_smap, tested}(GAKEb, GAKEb_st) /\ ={m}(HROc.RO, HROc.RO)); try sim />.

+ proc; inline.
  auto => />.
qed.


op rem_sid_c (s : pr_st_client instance_state) : pr_st_client_mod instance_state =
match s with 
| Pending st pt ir => Pending (st.`2, st.`3) pt ir
| Accepted st t k ir => Accepted (st.`2, st.`3) t k ir
| Aborted st t ir => Aborted (Some ((oget st).`2, (oget st).`3)) t ir
end.

op rem_sid_s (s : pr_st_server instance_state) : pr_st_server_mod instance_state =
match s with 
| Pending st pt ir => Pending (st.`2, st.`3) pt ir
| Accepted st t k ir => Accepted (st.`2, st.`3) t k ir
| Aborted st t ir => Aborted (Some ((oget st).`2, (oget st).`3)) t ir
end.

lemma gake_st_mod bit &m: `| Pr[E_GAKE(GAKEb_st(NTOR_S(HROc.RO), NTOR_C(HROc.RO), HROc.RO), A).run(bit) @ &m : res] - Pr[E_GAKE_mod(GAKEb_mod(NTOR_S_mod(RO), NTOR_C_mod(RO), RO), Meta_Red(A)).run(bit) @ &m : res] | <= Pr[E_GAKE(GAKEb_st(NTOR_S(HROc.RO), NTOR_C(HROc.RO), HROc.RO), A).run(bit) @ &m : GAKEb_st.stop].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Meta_Red.O_GAKE.stop => //; first last.
+ smt().
symmetry; proc; inline*.
wp; call (: Meta_Red.O_GAKE.stop
          , ={b0, tested}(GAKEb_st, GAKEb_mod) /\ ={pk_set, stop}(GAKEb_st, Meta_Red.O_GAKE)
               /\ (forall x, x \in HROc.RO.m{1} => x.`3 \in Meta_Red.O_GAKE.servers{2} => x \notin Meta_Red.O_GAKE.unreg_ro{2}
                    => HROc.RO.m{1}.[x] = RO.m{2}.[(x.`1, x.`2, get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[x.`3]), x.`4, x.`5)])
               /\ (forall x, x \in HROc.RO.m{1} => x.`3 \notin Meta_Red.O_GAKE.servers{2} \/ get_sr_mod (oget Meta_Red.O_GAKE.servers{2}.[x.`3])
                    => HROc.RO.m{1}.[x] =  Meta_Red.O_GAKE.unreg_ro{2}.[x])
               /\ (forall x, x \notin HROc.RO.m{1} => x.`3 \in Meta_Red.O_GAKE.servers{2} => !get_sr_mod (oget Meta_Red.O_GAKE.servers{2}.[x.`3])
                    => (x.`1, x.`2, get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[x.`3]), x.`4, x.`5) \notin RO.m{2})
               /\ (forall x, x \notin HROc.RO.m{1} => x \notin  Meta_Red.O_GAKE.unreg_ro{2})
               /\ (forall b1 b2, b1 \in Meta_Red.O_GAKE.servers{2} => b2 \in Meta_Red.O_GAKE.servers{2} 
                    => !get_sr_mod (oget Meta_Red.O_GAKE.servers{2}.[b1])
                    => oget Meta_Red.O_GAKE.servers{2}.[b1] = oget Meta_Red.O_GAKE.servers{2}.[b2] 
                    => b1 = b2)
               /\ (forall i, i \in GAKEb_st.c_smap{1} <=> i \in GAKEb_mod.c_smap{2})
               /\ (forall i, i \in GAKEb_st.c_smap{1} => rem_sid_c (oget GAKEb_st.c_smap{1}.[i]) = oget GAKEb_mod.c_smap{2}.[i])
               /\ (forall b j, (b, j) \in GAKEb_st.s_smap{1} => b \in Meta_Red.O_GAKE.servers{2}
                                      /\ (get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[b]), j) \in GAKEb_mod.s_smap{2}
                                      /\ rem_sid_s (oget GAKEb_st.s_smap{1}.[(b, j)]) = oget GAKEb_mod.s_smap{2}.[(get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[b]), j)])
               /\ (forall b j, (b, j) \notin GAKEb_st.s_smap{1} => b \in Meta_Red.O_GAKE.servers{2} => !get_sr_mod (oget Meta_Red.O_GAKE.servers{2}.[b])
                    => (get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[b]), j) \notin GAKEb_mod.s_smap{2})
               /\ (forall b j, (get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[b]), j) \in GAKEb_mod.s_smap{2} => get_sr_mod (oget Meta_Red.O_GAKE.servers{2}.[b])
                    => (exists b2, get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[b]) = get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[b2])
                                      /\ !get_sr_mod (oget Meta_Red.O_GAKE.servers{2}.[b2])))
               /\ (forall x, x \in GAKEb_st.unreg_ro{1} <=> x \in Meta_Red.O_GAKE.unreg_ro{2})
               /\ (forall b, b \in GAKEb_st.servers{1} <=> b \in Meta_Red.O_GAKE.servers{2})
               /\ (forall b, b \in GAKEb_st.servers{1} => get_pkey (oget GAKEb_st.servers{1}.[b]) = get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[b])
                                      /\ get_sr_ltk (oget GAKEb_st.servers{1}.[b]) = get_sr_mod (oget Meta_Red.O_GAKE.servers{2}.[b]))
               /\ (forall pk x1 x2 x4 x5, pk \notin GAKEb_mod.s_kp{2} => !rng Meta_Red.O_GAKE.servers{2} (Honest_mod pk) /\ (x1, x2, pk, x4, x5) \notin RO.m{2})
               /\ (forall b, b \in Meta_Red.O_GAKE.servers{2} => get_pkey_mod (oget Meta_Red.O_GAKE.servers{2}.[b]) \in GAKEb_mod.s_kp{2})
               /\ (forall pk j, pk \notin Meta_Red.O_GAKE.pk_set{2} => pk \notin GAKEb_mod.s_kp{2} /\ (pk, j) \notin GAKEb_mod.s_smap{2})
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
          + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
          auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
        auto => /> &1 &2 *. split. smt(get_setE mem_set in_fsetU in_fset1). smt(get_setE mem_set in_fsetU in_fset1).
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
    + auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? inv ? ? ? ? ? ? ? sk *. split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. 
move => b0 j.
case (b0 = b{2}) => b0eq.
admit. 
rewrite get_set_neqE //=.
move =>  insm nh.
have := inv b0 j insm nh. 
smt(mem_set get_setE in_fsetU in_fset1). smt(mem_set get_setE in_fsetU in_fset1).
    auto => /> &1 &2 *. 
    smt().
  if {1} => //; auto => />.
- move => &2 bad; proc; inline. if => //; auto => />.
  by rewrite dt_ll bad //=.
- move => &1; proc; inline.
  rcondf ^if; auto => />.
                
- proc; inline.
  sp 1 1; if {2} => //.
  auto => /> &1 &2 *. split. smt(mem_set get_setE in_fsetU in_fset1). move => *. split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. smt(mem_set get_setE in_fsetU in_fset1). split. 


smt(mem_set get_setE in_fsetU in_fset1).
  auto => /> &1 &2 *. smt().
- move => &2 bad; proc; inline. auto => />.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + sp 1 5. if => //; 1: by auto => /#.
    + sp 1 0; match; 1..2: smt().
      + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
      move => stl str.
      match; 1..3: smt().
      + move => sl ptl irl sr ptr irr.
        auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
      + move => sl tl kl irl sr tr kr irr. 
        auto => />.
      move => sl tl irl sr tr irr.
      auto => />.
    auto => />.
  rcondf {1} ^if. auto => /#.
  auto => /> &1 &2 *.
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
  sp 1 1; if {2} => //.
  + sp 1 0; if => //.
    + sp 1 7. match = => //. 
      + auto => /> &1 &2 *. admit.
      + auto => />. smt(get_setE mem_set in_fsetU in_fset1).
      auto => />. smt(get_setE mem_set in_fsetU in_fset1).
      admit. (* match struggles *)
    admit. (* match struggles *)
  admit.
- move => &2 bad; proc; inline.
  sp; match. 
  + auto => /#.
  admit. (* match struggles *)
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  sp 1 1; if {2} => //.
  + if => //.
    + sp; match; 1..2: smt().
      + auto => /> &1 &2 *. admit. 
      move => stl str.
      match; 1..3: smt().
      + move => sl ptl irl sr ptr irr.
        auto => /> &1 &2 *. admit.
      + move => sl tl kl irl sr tr kr irr. 
        auto => /> &1 &2 *. admit.
      move => sl tl irl sr tr irr.
      auto => /> &1 &2 *. admit.
    sp; match; 1..2: smt().
    + auto => /> &1 &2 *. 
    move => stl str.
    match; 1..3: smt().
    + move => sl ptl irl sr ptr irr.
      auto => /> &1 &2 *. admit.
    + move => sl tl kl irl sr tr kr irr. 
      auto => />.
    move => sl tl irl sr tr irr.
    auto => />.
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
  sp; match; 1..2: smt().
  + auto => />.
  move => stl str.
  match; 1..3: smt().
  + move => sl ptl irl sr ptr irr.
    auto => />.
  + move => sl tl kl irl sr tr kr irr.
    auto => /> &1 &2 *. admit.
  move => sl tl irl sr tr irr.
  auto => />.
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
    match Some {2} ^match; 1: by auto => /#.
    match {1} => //.
    + match Pending {2} ^match; 1: by auto => /#.
      if => //. admit. 
      + auto => /> &1 &2 *. admit. 
      auto => />.
    + match Accepted {2} ^match; 1: by auto => /#.
      if => //. admit.
      + auto => /> &1 &2 *. split. admit. smt(get_setE mem_set in_fsetU in_fset1).
      auto => />. 
    match Aborted {2} ^match; 1: by auto => /#.
    auto => />.
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
    match {1} => //.
    + match Pending {2} ^match; 1: by auto => /#.
      auto => />.
    + match Accepted {2} ^match; 1: by auto => /#.
      if => //. admit.
      + auto => /> &1 &2 *. admit.
      auto => />. 
    match Aborted {2} ^match; 1: by auto => /#.
    auto => />.
  match {1} => //. match {1} => //. auto => /> &1 &2 *. admit.
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
  + sp. if => //.
    + match.
      + move => /> &1 &2 ? ? ? ? ? ? ? ? ? inv *.
        split. smt(). smt().
        do rewrite -domNE.
        case (get_sr_mod (oget Meta_Red.O_GAKE.servers{2}.[b{2}])); 2: by smt().

        smt().
     
        + have := inv b{2} j{2}.

      + match None {2} ^match.
       
        auto => />.
      match Some {2} ^match. admit.
      match {1} => //.
      + match Pending {2} ^match. auto => /#.
        auto => />.
      + match Accepted {2} ^match. auto => /#.
        if => //. 
        + auto => /> &1 &2 *. admit. (* relate fresh partner and such *)
        + if => //. 
          + auto => />. admit.
          auto => />. admit.
        auto => />.
      match Aborted {2} ^match. auto => /#.
      auto => />.
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
move => roeq inj csm ssm pkin inv inv2 inv3 inv4 inv5 inv6 inv7 inv8 rl rr al csl pksl ssl sl stl tl url ml ar csr tr pksr huh ssr sr str urr mr.
by case : (!str) => />.
qed.
