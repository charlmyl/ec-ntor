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

module NTOR_C (H : RO) : Client_mod = {
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

  proc init_s() : pkey option
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
  proc init_s() : pkey option = {
    var kp;
    var r <- None;

    kp <@ S.keygen();
    if (kp.`1 \notin s_kp) {
      s_kp.[kp.`1] <- Some kp.`2;
      r <- Some kp.`1;
    }

    return r;
  }

  proc set_cert(pk: pkey) : unit option = {
    var r <- None;

    if (pk \notin s_kp) {
      s_kp.[pk] <- None;
      r <- Some ();
    }
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

module (Meta_Red (A : A_GAKE) : A_GAKE_mod) (O : GAKE_mod_out) = {
  module O_GAKE : GAKE_out = {
    var b0 : bool 

    var servers : (s_id, server_state) fmap

    var c_smap: (int, pr_st_client instance_state) fmap
    var s_smap: (s_id * int, pr_st_server instance_state) fmap
  
    var tested: int option

    proc h(x : h_input) = {
      var pk, r;

      pk <- get_pkey (oget servers.[x.`3]); (* what do I do with unregisted keys? *)
      r <@ O.h((x.`1, x.`2, pk, x.`4, x.`5));

      return r;
    }

    proc init_s(b: s_id) = {
      var r;

      r <@ O.init_s();

      return r;
    }

    proc set_cert(b: s_id, pk: pkey) = {
      var r;

      r <@ O.set_cert(pk);

      return r;
    }

    proc send_msg1(i: int, m1: s_id) = {
      var pk; 
      var r <- None;

      if (m1 \in servers) {
        pk <- get_pkey (oget servers.[m1]);
        r <@ O.send_msg1(i, pk);
      }

      return r;
    }

    proc send_msg2(b: s_id, j: int, m2: pkey) = {
      var pk; 
      var r <- None;

      if (b \in servers) {
        pk <- get_pkey (oget servers.[b]);
        r <@ O.send_msg2(pk, j, m2);
      }

      return r;
    }

    proc send_msg3 = O.send_msg3

    proc c_rev_skey = O.c_rev_skey 

    proc s_rev_skey(b: s_id, j: int) = {
      var pk;
      var r <- None;

      if (b \in servers) {
        pk <- get_pkey (oget servers.[b]);
        r <@ O.s_rev_skey(pk, j);
      }

      return r;     
    }

    proc rev_ltkey(b: s_id) = {
      var pk;
      var r <- None;

      if (b \in servers) {
        pk <- get_pkey (oget servers.[b]);
        r <@ O.rev_ltkey(pk);
      }

      return r;
    }

    proc c_rev_ephkey = O.c_rev_ephkey

    proc s_rev_ephkey(b: s_id, j: int) = {
      var pk;
      var r <- None;

      if (b \in servers) {
        pk <- get_pkey (oget servers.[b]);
        r <@ O.s_rev_ephkey(pk, j);
      }

      return r;     
    }

    proc c_test = O.c_test

    proc s_test(b: s_id, j: int) = {
      var pk;
      var r <- None;

      if (b \in servers) {
        pk <- get_pkey (oget servers.[b]);
        r <@ O.s_test(pk, j);
      }

      return r;
    }
  }

  proc run() : bool = {
    var b';

    b' <@ A(O_GAKE).run();

    return b';
  }
}.



(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GAKE {-GAKEb, -Game0, -Game1, -Game2, -Game3, -Game4, -GameDDH, -ROc.IdealAll.RO, -RO, -FRO, -ROSc.I1.RO, -ROSc.I2.RO, -ROSc.I1.FRO, -ROSc.I2.FRO, -Red_Coll_real, -Red_Coll_ideal, -BB.Sample, -Red_ROM, -Red_ROM2 }.

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



end section.
