require import AllCore FSet FMap Distr DProd List SplitRO.
(*   *) import StdBigop.Bigreal.BRA StdOrder.RealOrder.

require NTOR_nosid.
clone import NTOR_nosid as NTOR_mod.
import NTORc GAKE_mod GAKEc HROc HRO_mod_c DH.G DH.GP DH.FD.

(* ------------------------------------------------------------------------------------------ *)
(* Introduce stop in original game *)
module GAKEb_st (S: Server) (C: Client) (H : GAKEc.HROc.RO) : GAKEc.GAKE_nodhs_i = {
  var b0 : bool 

  var servers : (s_id, GAKEc.server_state) fmap
  var unreg_ro : (pkey * pkey * s_id * pkey * pkey) fset
  var pk_set : pkey fset
  var stop : bool

  var c_smap: (int, GAKEc.pr_st_client GAKEc.instance_state) fmap
  var s_smap: (s_id * int, GAKEc.pr_st_server GAKEc.instance_state) fmap
  
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

    if (!x.`3 \in servers) {
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
      kp <@ S(H).keygen();
      stop <- stop \/ kp.`1 \in pk_set;
      pk_set <- pk_set `|` fset1 kp.`1;
      servers.[b] <- GAKEc.Honest kp;
    }
    return omap get_pkey servers.[b];
  }

  proc send_msg1(i: int, m1: s_id) : pkey option = {
    var st, pk_b, st', m2;
    var r <- None;

    st <- c_smap.[i];
    if (m1 \in servers /\ !get_sr_dh (oget servers.[m1])) {
      pk_b <- get_pkey (oget servers.[m1]);
      match st with
      | None => {
          (st', m2) <@ C(H).new_session(m1, pk_b);
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

    sko <- obind GAKEc.get_skey servers.[b];

    if (sko is Some sk) (* Server was initialised as honest *) {
      match s_smap.[b, j] with
      | None => {
          resp <@ S(H).respond_session(Some (b, sk, None), m2);
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
            resp <@ C(H).complete_session(st, m3);
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
    if (m3.`1 \notin pk_set) {
      pk_set <- pk_set `|` fset1 m3.`1;
    }

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
              ek <- Some (st.`3);
              c_smap.[i] <- set_ir_eph (Pending st pk_e ir);
            }
          }
          (* accepted client instamces can only be ephkey revealed when not tested and 
             if not all partners are tested *)
        | Accepted st t k ir => {
            if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_c t s_smap = Some false)) {
              ek <- Some (st.`3);
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
        if (st is GAKEc.Accepted st t k ir) { (* No Pending on Server side *)
          if (!((   get_ir_test (oget s_smap.[b, j])
                 \/ untested_partner_s t c_smap = Some false)
                /\ get_sr_ltk (oget servers.[b]))) {
            ek <- Some (oget st.`3);
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

module (Hon_Red (A : GAKEc.A_GAKE) (C: GAKEc.Client) (H : HROc.RO) : GAKEc.A_GAKE) (O : GAKEc.GAKE) = {
  module O_GAKE : GAKEc.GAKE = {
    var dh_ro : (pkey * pkey * s_id * pkey * pkey, (tag * key)) fmap
    var c_inst : (int, bool) fmap
    var dhc_smap : (int, GAKEc.pr_st_client GAKEc.instance_state) fmap
    var servers : (s_id, server_state_mod) fmap

    proc h = H.get

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
      var st', m2, pk_b; 
      var r <- None;
  
      if (m1 \in servers) {
        if (!get_sr_out (oget servers.[m1]) /\ i \notin dhc_smap) {
          r <@ O.send_msg1(i, m1);
          if (r <> None) {
            c_inst.[i] <- false;
          }
        } else {
          if (i \notin c_inst) {
            pk_b <- get_pkey_mod (oget servers.[m1]);
            (st', m2) <@ C(H).new_session(m1, pk_b);
            dhc_smap.[i] <- GAKEc.Pending st' (m1, m2) (false, false, false);
            r <- Some m2;
            c_inst.[i] <- true;
          }
        }
      }
  
      return r;
    }
  
    proc send_msg2 = O.send_msg2
  
    proc send_msg3(i: int, m3: pkey * tag) = {
      var resp, st', k;
      var r <- None;
  
      if (i \notin dhc_smap) {
        r <@ O.send_msg3(i, m3);
      } else {
        match dhc_smap.[i] with 
        | None => { } (* Abort? *)
        | Some st => {
            match st with
            | GAKEc.Pending st pt ir => {
                resp <@ C(H).complete_session(st, m3);
                if (resp is Some r') {
                  (st', k) <- r';
                  dhc_smap.[i] <- Accepted st' (pt, Some m3) k ir;
                  r <- Some ();
                } else {
                  dhc_smap.[i] <- Aborted (Some st) (Some (pt, Some m3)) ir;
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
                r <- Some (st.`3);
                dhc_smap.[i] <- set_ir_eph (GAKEc.Pending st pk_e ir);
              }
            | GAKEc.Accepted st t k ir => {
                if (!get_ir_test (oget dhc_smap.[i])) {
                  r <- Some (st.`3);
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
  }

  proc run() : bool = {
    var b';

    O_GAKE.dhc_smap <- empty;
    O_GAKE.c_inst <- empty;
    O_GAKE.dh_ro <- empty;
    O_GAKE.servers <- empty;

    b' <@ A(O_GAKE).run();

    return b';
  }
}.

module (Hon_s_Red (A : GAKEc.A_GAKE) : GAKEc.A_GAKE_nodhs) (O : GAKEc.GAKE_nodhs) = {
  module O_GAKE : GAKEc.GAKE = {
    var servers : (s_id, (bool * pkey option)) fmap

    include O [-init_s]

    proc init_s(b : s_id) = {
      var r;

      if (b \notin servers) {
        r <@ O.init_s(b);
        servers.[b] <- (false, r);
      }

      return (oget servers.[b]).`2;
    }

    proc set_cert(b: s_id, pk: pkey) = { 
      var r <- None;
  
      if (b \notin servers) {
        servers.[b] <- (true, Some pk);
        r <- Some ();
      }
  
      return r;
    }
  }

  proc run() : bool = {
    var b';

    O_GAKE.servers <- empty;

    b' <@ A(O_GAKE).run();

    return b';
  }
}.


(* ------------------------------------------------------------------------------------------ *)
(* Reduction from restricted to non-restricted model  *)
module (Dh_Red (A : GAKEc.A_GAKE_nodhs) (C: GAKEc.Client) : GAKEc.A_GAKE) (O : GAKEc.GAKE) = {
  module O_GAKE : GAKEc.GAKE_nodhs = {
   include O [-set_cert]
  }

  proc run() : bool = {
    var b';

    b' <@ A(O_GAKE).run();

    return b';
  }
}.


(* ------------------------------------------------------------------------------------------ *)
(* Reduction preventing collisions and prediction of public keys  *)
module (Name_Red (A : GAKEc.A_GAKE_nodhs) : GAKE_mod.A_GAKE_nodhs) (O : GAKE_mod.GAKE_nodhs) = {
  module O_GAKE : GAKEc.GAKE_nodhs = {
    var unreg_ro : (pkey * pkey * s_id * pkey * pkey, (tag * key)) fmap

    var sid_pk : (s_id, pkey) fmap
    var pk_set : pkey fset
  (*  var pred_ce : pkey fset
    var pred_se : pkey fset*)
    
    var stop : bool

    proc h(x : GAKEc.h_input) = {
      var pk_s, tk;
      var r <- (witness, witness);

      if (!stop) {
        if (x.`3 \in sid_pk) {
          if (x \in unreg_ro) {
            r <- oget unreg_ro.[x];
          } else {
            pk_s <- (oget sid_pk.[x.`3]); 
            r <@ O.h((x.`1, x.`2, pk_s, x.`4, x.`5));
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
            sid_pk.[b] <- pk;
          } else {
            stop <- stop \/ true; (* there was a collision in sampling *)
          }
        }
        r <- sid_pk.[b];
      }
      return r;
    }

    proc send_msg1(i: int, m1: s_id) = {
      var pk_s; 
      var r <- None;

      if (!stop /\ m1 \in sid_pk) {
        pk_s <- oget sid_pk.[m1];
        r <@ O.send_msg1(i, pk_s);

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
        r <@ O.send_msg2(pk_s, j, m2);
        if (m2 \notin pk_set) {
          pk_set <- pk_set `|` fset1 m2;
        }
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
        r <@ O.send_msg3(i, m3);
        if (m3.`1 \notin pk_set) {
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
        r <@ O.s_rev_skey(pk_s, j);
      }

      return r;     
    }

    proc rev_ltkey(b: s_id) = {
      var pk_s;
      var r <- None;

      if (!stop /\ b \in sid_pk) {
        pk_s <- oget sid_pk.[b];
        r <@ O.rev_ltkey(pk_s);
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
        r <@ O.s_rev_ephkey(pk_s, j);
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
        r <@ O.s_test(pk_s, j);
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

declare module S <: GAKEc.Server {-GAKEb, -GAKEb_hon, -GAKEb_nodhs, -GAKEb_st, -GAKE_mod.GAKEb_nodhs, -Hon_Red, -Hon_s_Red, -Name_Red, -HROc.RO, -GAKE_mod.HROc.RO }.
declare module C <: GAKEc.Client {-GAKEb, -GAKEb_hon, -GAKEb_nodhs, -GAKEb_st, -GAKE_mod.GAKEb_nodhs, -Hon_Red, -Hon_s_Red, -Name_Red, -HROc.RO, -GAKE_mod.HROc.RO, -S }.

declare module A <: GAKEc.A_GAKE {-C, -S, -GAKE_mod.HROc.RO, -GAKEc.HROc.RO, -Hon_Red, -Hon_s_Red, -Name_Red, -GAKEc.GAKEb, -GAKEc.GAKEb_hon, -GAKEc.GAKEb_nodhs, -GAKEb_st, -GAKE_mod.GAKEb_nodhs }.

declare module A_mod <: GAKEc.A_GAKE_nodhs {-C, -S, -GAKE_mod.HROc.RO, -GAKEc.HROc.RO, -Hon_Red, -Hon_s_Red, -Name_Red, -GAKEc.GAKEb, -GAKEc.GAKEb_hon, -GAKEc.GAKEb_nodhs, -GAKEb_st, -GAKE_mod.GAKEb_nodhs }.

declare axiom A_ll (G <: GAKEc.GAKE{-A}):
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


lemma gake_extend bit &m: Pr[GAKEc.E_GAKE_nodhs(GAKEc.GAKEb_nodhs(S, C, HROc.RO), A_mod).run(bit) @ &m : res] = Pr[GAKEc.E_GAKE(GAKEc.GAKEb(S, C, HROc.RO), Dh_Red(A_mod, C)).run(bit) @ &m : res].
proof. 
byequiv => //.
proc; inline.
wp; call (: ={glob S, glob C} /\ ={b0, servers, c_smap, s_smap, tested}(GAKEb_nodhs, GAKEc.GAKEb) /\ ={m}(GAKEc.HROc.RO, GAKEc.HROc.RO)
              /\ (forall i s pt ir, i \in GAKEb.c_smap{2} => GAKEb.c_smap{2}.[i] = Some (Pending s pt ir)
                   => pt.`1 \in GAKEb.servers{2})
              /\ (forall i s t k ir, i \in GAKEb.c_smap{2} => GAKEb.c_smap{2}.[i] = Some (Accepted s t k ir) 
                   => t.`1.`1 \in GAKEb.servers{2})
              /\ (forall b, b \in GAKEb.servers{2} => ! get_sr_dh (oget GAKEb.servers{2}.[b]))); try sim />.

+ proc; inline.
  if => //.
  seq 1 1: (#pre /\ ={kp}). sim />.
  auto => />. smt(get_setE mem_set). 

+ proc; inline.
  sp 2 2; if => //. auto => /#. 
  sp; match = => //.
  seq 1 1: (#pre /\ ={st', m2}). sim />.
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp; match = => // st.
  match = => // s pt ir.
  seq 1 1: (#pre /\ ={resp}). sim />. 
  match = => //; auto => />; smt(get_setE mem_set).

+ proc; inline.
  sp; match = => // st.
  match = => // kp.
  auto => />. smt(get_setE).

+ proc; inline.
  sp; match = => // st.
  match = => // kp.
  auto => />. smt(get_setE).

+ proc; inline.
  sp; match = => // st.
  match = => // [s pt ir|s t k ir]; auto => />; smt(get_setE).

+ proc; inline.
  sp 1 1; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //. auto => /#.
  if => //; auto => />; smt(get_setE).

auto => />.
smt(emptyE mem_empty).
qed.



lemma gake_restrict bit &m: Pr[GAKEc.E_GAKE(GAKEc.GAKEb(S, C, HROc.RO), A).run(bit) @ &m : res] = Pr[GAKEc.E_GAKE(GAKEc.GAKEb_hon(S, C, HROc.RO), Hon_Red(A, C, HROc.RO)).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline.
wp; call (: ={glob S, glob C} /\ ={b0, servers, s_smap, tested}(GAKEc.GAKEb, GAKEc.GAKEb_hon) /\ ={m}(GAKEc.HROc.RO, GAKEc.HROc.RO)
              /\ (GAKEc.GAKEb.c_smap{1} = (GAKEc.GAKEb_hon.c_smap{2} + Hon_Red.O_GAKE.dhc_smap{2}))
              /\ (forall i, i \in Hon_Red.O_GAKE.dhc_smap{2} => i \notin GAKEc.GAKEb_hon.c_smap{2})
              /\ (forall i, i \in GAKEc.GAKEb_hon.c_smap{2} => i \notin Hon_Red.O_GAKE.dhc_smap{2})
              /\ (forall b, b \in Hon_Red.O_GAKE.servers{2} <=> b \in GAKEc.GAKEb_hon.servers{2})
              /\ (forall b, b \in GAKEc.GAKEb_hon.servers{2} 
                   => get_pkey (oget GAKEc.GAKEb_hon.servers{2}.[b]) = get_pkey_mod (oget Hon_Red.O_GAKE.servers{2}.[b])
                                      /\ (get_sr_out (oget Hon_Red.O_GAKE.servers{2}.[b]) = get_sr_dh (oget GAKEc.GAKEb_hon.servers{2}.[b])))
              /\ (forall i, i \in GAKEc.GAKEb.c_smap{1} <=> i \in Hon_Red.O_GAKE.c_inst{2})
              /\ (forall i, i \in Hon_Red.O_GAKE.dhc_smap{2} => get_ir_test (oget Hon_Red.O_GAKE.dhc_smap{2}.[i]) = false
                                       /\ get_name (oget Hon_Red.O_GAKE.dhc_smap{2}.[i]) \in GAKEb_hon.servers{2}
                                       /\ get_sr_dh (oget GAKEb_hon.servers{2}.[get_name (oget Hon_Red.O_GAKE.dhc_smap{2}.[i])]))
              /\ (forall b j , b \notin GAKEc.GAKEb_hon.servers{2} => (b, j) \notin GAKEc.GAKEb_hon.s_smap{2})
              /\ (forall b j, (b, j) \in GAKEc.GAKEb_hon.s_smap{2} => (*get_name (oget GAKEc.GAKEb_hon.s_smap{2}.[(b, j)]) = b
                                       /\*) (exists pk m3, get_trace (oget GAKEc.GAKEb_hon.s_smap{2}.[(b, j)]) = Some ((b, pk), m3)))
              /\ (forall b j, b \in GAKEc.GAKEb_hon.servers{2} => get_sr_dh (oget GAKEc.GAKEb_hon.servers{2}.[b])
                   => (b, j) \notin GAKEc.GAKEb_hon.s_smap{2} /\ get_sr_ltk (oget GAKEc.GAKEb_hon.servers{2}.[b]))
              /\ (forall i j, i \in Hon_Red.O_GAKE.dhc_smap{2}  
                   => (get_name (oget Hon_Red.O_GAKE.dhc_smap{2}.[i]), j) \notin GAKEc.GAKEb_hon.s_smap{2})
              /\ (forall i st pt ir m3, i \in Hon_Red.O_GAKE.dhc_smap{2} => Hon_Red.O_GAKE.dhc_smap{2}.[i] = Some (Pending st pt ir)
                   => (1 <= card (get_partners_c (pt, Some m3) GAKEc.GAKEb_hon.s_smap{2})) = false)
              /\ (forall i st pt ir, i \in Hon_Red.O_GAKE.dhc_smap{2} => Hon_Red.O_GAKE.dhc_smap{2}.[i{2}] = Some (Pending st pt ir)
                   => (1 <= card (get_origins_c (pt, None) GAKEc.GAKEb_hon.s_smap{2}) = false))
              /\ (forall i st t k ir, i \in Hon_Red.O_GAKE.dhc_smap{2} => Hon_Red.O_GAKE.dhc_smap{2}.[i] = Some (Accepted st t k ir)
                   => (1 <= card (get_partners_c t GAKEc.GAKEb_hon.s_smap{2})) = false)).

+ sim />.

+ proc; inline.
  sp 0 2; if => //.
  + seq 1 1: (#pre /\ ={kp}). sim />.
    auto => /> &2 *. smt(get_setE mem_set).
  auto => /> &2 *. smt(get_setE mem_set).

+ proc; inline.
  sp 1 4; if => //.
  + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
  auto => />. smt(get_setE mem_set in_fsetU in_fset1).

+ proc; inline.
  sp 2 1; if => //. smt().
  if {2} => //.
  + rcondt {2} ^if. auto => /#.
    sp; match = => //. auto => /> &2 *. smt(joinE).
    + seq 1 1 : (#pre /\ st'{1} = st'0{2} /\ m2{1} = m20{2}). sim />.
      auto => /> &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1). 
      rewrite -fmap_eqP. smt(joinE get_setE).
    move => st.
    auto => />. 
  sp; match {1} => //.
  + rcondt {2} ^if. auto => /#.
    sp. seq 1 1: (#pre /\ ={st', m2}). sim />. smt(get_setE mem_set in_fsetU in_fset1 joinE).
    auto => /> &2 ? ? ? ? ? ? ? ? inv *. do !split; 2..6: smt(get_setE mem_set in_fsetU in_fset1 joinE).
    + rewrite -fmap_eqP. smt(joinE get_setE).
    + move => i1 st0 pt ir0 m3.
      case (i1 = i{2}) => ieq.
      + rewrite ieq mem_set //=.
        rewrite get_setE //=.
        move => [#] steq pteq ireq.
        rewrite /get_partners_c.
        case ((i{2} \notin Hon_Red.O_GAKE.dhc_smap{2})) => indhc; 2: by smt(get_setE mem_set in_fsetU in_fset1 joinE).
        have->: (fdom (filter (fun (_ : s_id * int) (val : GAKEc.pr_st_server GAKEc.instance_state) => get_trace val = Some (pt, Some m3)) GAKEb_hon.s_smap{2})) = fset0.
        + rewrite fsetP.
          move => x.
          rewrite mem_fdom mem_filter.
          have->: !(x \in GAKEb_hon.s_smap{2} /\ (fun (_ : s_id * int) (val : GAKEc.pr_st_server GAKEc.instance_state) =>
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
        case ((i{2} \notin Hon_Red.O_GAKE.dhc_smap{2})) => indhc; 2: by smt(get_setE mem_set in_fsetU in_fset1 joinE).
        have->: (fdom (filter (fun (_ : s_id * int) (val : GAKEc.pr_st_server GAKEc.instance_state) 
          => exists (m2o : (pkey * tag) option), get_trace val = Some (pt, m2o)) GAKEb_hon.s_smap{2})) = fset0.
        + rewrite fsetP.
          move => x.
          rewrite mem_fdom mem_filter. 
          have->: !(x \in GAKEb_hon.s_smap{2} /\ (fun (_ : s_id * int) (val : GAKEc.pr_st_server GAKEc.instance_state) =>
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
  seq 1 1: (#pre /\ ={resp}). sim />.
  match = => //.
  + auto => /> &2 14? inv inv2 inv3 *. do !split; ~2,5..7: smt(get_setE mem_set in_fsetU in_fset1).
    + move => b0 j0.
      case ((b0 = b{2}) /\ j0 = j{2}) => [[] beq jeq|]; 2: by smt(get_setE mem_set in_fsetU in_fset1). 
      rewrite mem_set beq jeq //=.
      rewrite get_setE //=.
      exists m2{2} None.
      smt(get_setE).
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
    move => i1 st0 t k ir0 iin iacc.
    rewrite /get_partners_c.
    rewrite filter_set.
    rewrite rem_id. 
    rewrite mem_filter negb_and. smt().
    have := inv3 i1 st0 t k ir0 iin iacc.
    rewrite /get_partners_c. 
    by smt(get_setE mem_set in_fsetU in_fset1).
  move => sts.
  auto => /> &2 14? inv inv2 inv3 *. do !split; ~2,5..7: smt(get_setE mem_set in_fsetU in_fset1).
  + move => b0 j0.
    case ((b0 = b{2}) /\ j0 = j{2}) => [[] beq jeq|]; 2: by smt(get_setE mem_set in_fsetU in_fset1). 
    rewrite mem_set beq jeq //=.
    exists m2{2} (Some sts.`2).
    smt(get_setE).
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
  move => i1 st0 t k ir0 iin iacc.
  rewrite /get_partners_c.
  rewrite filter_set.
  rewrite rem_id. 
  rewrite mem_filter negb_and. smt().
  have := inv3 i1 st0 t k ir0 iin iacc.
  rewrite /get_partners_c. 
  by smt(get_setE mem_set in_fsetU in_fset1). 

+ proc; inline.
  sp 1 1; if {2} => //.
  + sp; match = => //. auto => />. smt(joinE).
    + auto => />.
    move => sto.
    match = => //.
    + move => s pt ir.
      sp; seq 1 1 : (#pre /\ resp{1} = resp0{2}). sim />.
      match = => //.
      + auto => /> &1 &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).
        rewrite -fmap_eqP. smt(joinE get_setE).
      move => r'.
      auto => /> &2 *. do !split; 2..4: smt(get_setE mem_set in_fsetU in_fset1).
      rewrite -fmap_eqP. smt(joinE get_setE).
    + move => s t k ir.
      auto => />.
    move => s t ir.
    auto => />.
  match = => //. auto => />. smt(joinE).
  move => st.
  match = => //.
  move => s pt ir.
  sp; seq 1 1 : (#pre /\ ={resp}). sim />.
  match = => //.
  + auto => /> &2 *. do !split; 2..9: smt(get_setE mem_set in_fsetU in_fset1).
    rewrite -fmap_eqP. smt(joinE get_setE).
  move => r'.
  auto => /> &2 *. do !split; 2..9: smt(get_setE mem_set in_fsetU in_fset1).
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
        have->: (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => get_trace val = Some t) (GAKEb_hon.c_smap{1} + Hon_Red.O_GAKE.dhc_smap{1}))) 
            = (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => get_trace val = Some t) GAKEb_hon.c_smap{1})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          by smt(joinE).
        have->: (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => get_trace val = Some t /\ get_ir_test val = false)
             (GAKEb_hon.c_smap{1} + Hon_Red.O_GAKE.dhc_smap{1}))) = (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) =>
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
            => get_untested_partners_s t (GAKEb_hon.c_smap{2} + Hon_Red.O_GAKE.dhc_smap{2}) = get_untested_partners_s t GAKEc.GAKEb_hon.c_smap{2}
            /\ get_partners_s t (GAKEb_hon.c_smap{2} + Hon_Red.O_GAKE.dhc_smap{2}) = get_partners_s t GAKEc.GAKEb_hon.c_smap{2}).
        + rewrite /untested_partner_s.
          rewrite /get_partners_s /get_untested_partners_s.
          move => b1 j t [] bjin teq.
          have->: (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => get_trace val = Some t /\ get_ir_test val = false) (GAKEb_hon.c_smap{2} 
              + Hon_Red.O_GAKE.dhc_smap{2}))) = (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) 
              => get_trace val = Some t /\ get_ir_test val = false) GAKEb_hon.c_smap{2})).
          + rewrite fsetP.
            move => x.
            do rewrite mem_fdom mem_filter.
            smt(joinE).
          have->: (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => get_trace val = Some t) (GAKEb_hon.c_smap{2} + Hon_Red.O_GAKE.dhc_smap{2}))) = 
              (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => get_trace val = Some t) GAKEb_hon.c_smap{2})). 
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
        have->: (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => get_trace val = Some t) (GAKEb_hon.c_smap{1} + Hon_Red.O_GAKE.dhc_smap{1}))) 
          = (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => get_trace val = Some t) GAKEb_hon.c_smap{1})).
        + rewrite fsetP.
          move => x.
          do rewrite mem_fdom mem_filter.
          by smt(joinE).
        have->: (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => get_trace val = Some t /\ get_ir_test val = false)
             (GAKEb_hon.c_smap{1} + Hon_Red.O_GAKE.dhc_smap{1}))) = (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) =>
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
          have->: (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) =>
               exists (m2o : (pkey * tag) option), get_trace val = Some (t.`1, m2o)) (GAKEb_hon.c_smap{1} + Hon_Red.O_GAKE.dhc_smap{1}))) = (fdom
               (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) => exists (m2o : (pkey * tag) option), get_trace val = Some (t.`1, m2o)) GAKEb_hon.c_smap{1})).
          + rewrite fsetP.
            move => x.
            do rewrite mem_fdom mem_filter.
            by smt(joinE).
          have->: (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                  (exists (m2o : (pkey * tag) option), get_trace val = Some (t.`1, m2o)) /\ get_ir_test val = false /\ get_ir_sess val = false /\ get_ir_eph val = false)
               (GAKEb_hon.c_smap{1} + Hon_Red.O_GAKE.dhc_smap{1}))) = (fdom (filter (fun (_ : int) (val : GAKEc.pr_st_client GAKEc.instance_state) =>
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

auto => />; smt(fmap_eqP joinE mem_empty emptyE).
qed.

lemma gake_rem_dhs bit &m: Pr[GAKEc.E_GAKE(GAKEb_hon(S, C, GAKEc.HROc.RO), A).run(bit) @ &m : res] = 
  Pr[GAKEc.E_GAKE_nodhs(GAKEc.GAKEb_nodhs(S, C, GAKEc.HROc.RO), Hon_s_Red(A)).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline.
wp; call (: ={glob S, glob C} /\ ={b0, c_smap, s_smap, tested}(GAKEb_hon, GAKEc.GAKEb_nodhs) /\ ={m}(GAKEc.HROc.RO, GAKEc.HROc.RO)
               /\ (forall b, b \in GAKEb_hon.servers{1} <=> b \in Hon_s_Red.O_GAKE.servers{2})
               /\ (forall b, b \notin Hon_s_Red.O_GAKE.servers{2} => b \notin GAKEc.GAKEb_nodhs.servers{2})
               /\ (forall b, b \in GAKEb_hon.servers{1} => ! get_sr_dh (oget GAKEb_hon.servers{1}.[b])
                   => GAKEb_hon.servers{1}.[b] = GAKEc.GAKEb_nodhs.servers{2}.[b])
               /\ (forall b, b \in GAKEc.GAKEb_nodhs.servers{2} => ! get_sr_dh (oget GAKEc.GAKEb_nodhs.servers{2}.[b])
                   /\ ! get_sr_dh (oget GAKEb_hon.servers{1}.[b])
                   /\ (! get_sr_ltk (oget GAKEc.GAKEb_nodhs.servers{2}.[b]) <=> ! get_sr_ltk (oget GAKEb_hon.servers{1}.[b])))
               /\ (forall b, get_sr_dh (oget GAKEb_hon.servers{1}.[b]) => get_sr_ltk (oget GAKEb_hon.servers{1}.[b]))
               /\ (forall b, get_sr_dh (oget GAKEc.GAKEb_nodhs.servers{2}.[b]) => get_sr_ltk (oget GAKEc.GAKEb_nodhs.servers{2}.[b]))
               /\ (forall b, b \in Hon_s_Red.O_GAKE.servers{2} => omap get_pkey GAKEb_hon.servers{1}.[b] = (oget Hon_s_Red.O_GAKE.servers{2}.[b]).`2)
               /\ (forall i, i \in GAKEc.GAKEb_nodhs.c_smap{2} => get_name (oget GAKEc.GAKEb_nodhs.c_smap{2}.[i]) \in GAKEc.GAKEb_nodhs.servers{2})
               /\ (forall b j, (b, j) \in GAKEc.GAKEb_nodhs.s_smap{2} => b \in GAKEc.GAKEb_nodhs.servers{2})
      ); 1: sim />.

+ proc; inline.
  if => //. auto => /#.
  + rcondt {2} ^if. auto => /#.
    sp; seq 1 1: (#pre /\ ={kp}). sim />. 
    auto => />; smt(get_setE mem_set).
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp 1 1; if => //. auto => /#.
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp 2 2; if => //. auto => /#.
  sp; match => //.
  seq 1 1: (#pre /\ ={st', m2}). sim />. smt(get_setE mem_set).
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp; match = => //; 1: auto => /#.
  move => sk.
  match = => //.
  seq 1 1: (#pre /\ ={resp}). sim />.
  sp; match = => //.
  + auto => />. smt(get_setE mem_set).
  move => st.
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp; match = => // st.
  match = => // s pt ir.
  seq 1 1: (#pre /\ ={resp}). sim />.
  match = => //.
  + auto => />. smt(get_setE mem_set).
  move => r'.
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp; match {1} => //.
  + match None {2} ^match; 1: auto => /#.
    auto => />.
  match {1} => //.
  + match Some {2} ^match; 1: auto => /#.
    match Honest {2} ^match; 1: auto => /#.
    auto => />. smt(get_setE mem_set).
  + match Some {2} ^match; 1: auto => /#.
    match Corrupt {2} ^match; 1: auto => /#.
    auto => />.
  match {2}.
  + auto => />.
  match Dishonest {2} ^match; 1: auto => /#.
  auto => />.

+ proc; inline.
  sp; match = => // st.
  match = => // [s pt ir|s t k ir].
  + auto => /> &1 &2 str _ inv inv2 inv3 inv4 inv5 inv6 inv7 inv8 inv9 untori. 
    move => i0.
    case (i0 = i{2}) => ieq; 2: smt(get_setE mem_set).
    have := inv8 i{2}.
    smt(get_setE mem_set).
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp; match = => // st.
  match = => // s t k ir.
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp 1 1; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //.
  + auto => &1 &2 *.
    do rewrite negb_or.
    rewrite /fresh_partner_c.
    rewrite /get_fresh_partners_c.
    have->: (fdom (filter (fun (bj : s_id * int) (val : GAKEc.pr_st_server GAKEc.instance_state) => get_trace val = Some t /\ get_ir_test val = false 
                /\ get_ir_sess val = false /\ (get_ir_eph val = false \/ get_sr_ltk (oget GAKEb_hon.servers{1}.[bj.`1]) = false)) GAKEb_hon.s_smap{1})) 
              = (fdom (filter (fun (bj : s_id * int) (val : GAKEc.pr_st_server GAKEc.instance_state) => get_trace val = Some t /\ get_ir_test val = false 
                /\ get_ir_sess val = false /\ (get_ir_eph val = false \/ get_sr_ltk (oget GAKEc.GAKEb_nodhs.servers{2}.[bj.`1]) = false)) GAKEc.GAKEb_nodhs.s_smap{2})).
    + rewrite fsetP. 
      move => x.
      do rewrite mem_fdom mem_filter. smt(get_setE mem_set).
    by smt(get_setE mem_set).
  if => //.
  + auto => />. smt(get_setE mem_set).
  auto => />. smt(get_setE mem_set).

+ proc; inline.
  sp 1 1; if => //.
  match = => // st.
  match = => // s t k ir.
  if => //.
  + auto => /#.
  if => //.
  + auto => />. smt(get_setE mem_set).
  auto => />. smt(get_setE mem_set).

auto => />. smt(mem_empty emptyE).
qed.


(************************************************************************************************************)
(* Relation between name-based and public key only model *)

(* introducing stop in original game *)
lemma gake_st bit &m: Pr[GAKEc.E_GAKE_nodhs(GAKEc.GAKEb_nodhs(S, C, GAKEc.HROc.RO), Hon_s_Red(A)).run(bit) @ &m : res] 
                = Pr[GAKEc.E_GAKE_nodhs(GAKEb_st(S, C, GAKEc.HROc.RO), Hon_s_Red(A)).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline.
wp; call (: ={glob S, glob C} /\ ={b0, servers, c_smap, s_smap, tested}(GAKEc.GAKEb_nodhs, GAKEb_st) /\ ={servers}(Hon_s_Red.O_GAKE, Hon_s_Red.O_GAKE)
               /\ ={m}(GAKEc.HROc.RO, GAKEc.HROc.RO)); try sim />.

+ proc; inline.
  auto => />.
qed.


(* formulating lemma pointwise - needed to relate the partnering notions on server side *)
lemma inj_fcard_image_pw (f : 'a -> 'b) (A : 'a fset) :
      (forall x y, x \in A => y \in A => f x = f y => x = y) => card (image f A) = card A.
proof.
move => inj_f_at.
have/oflist_uniq uniq_f : uniq (map f (elems A)).
apply map_inj_in_uniq => * ; [|exact uniq_elems].
by apply inj_f_at; 1..2:rewrite memE //.
by rewrite /image /card -(perm_eq_size _ _ uniq_f) size_map.
qed.


(* operators removing the server name from the states *)
op rem_sid_c (s : GAKEc.pr_st_client GAKEc.instance_state) : GAKE_mod.pr_st_client GAKE_mod.instance_state =
match s with 
| Pending st pt ir => Pending_mod (st.`2, st.`3) (st.`2, pt.`2) ir
| Accepted st t k ir => Accepted_mod (st.`2, st.`3) ((st.`2, (t.`1).`2), t.`2) k ir
| Aborted st t ir => Aborted_mod (Some ((oget st).`2, (oget st).`3)) (Some (((oget st).`2, ((oget t).`1).`2), (oget t).`2)) ir
end.

op rem_sid_s (s : GAKEc.pr_st_server GAKEc.instance_state) : GAKE_mod.pr_st_server GAKE_mod.instance_state =
match s with 
| Pending st pt ir => Pending_mod (st.`2, st.`3) (g ^ st.`2, pt.`2) ir
| Accepted st t k ir => Accepted_mod (st.`2, st.`3) ((g ^ st.`2, (t.`1).`2), t.`2) k ir
| Aborted st t ir => Aborted_mod (Some ((oget st).`2, (oget st).`3)) (Some ((g ^ (oget st).`2, ((oget t).`1).`2), (oget t).`2)) ir
end.

declare module H <: GAKE_mod.HROc.RO.

op get_sid : pkey -> (s_id, pkey) fmap -> s_id.
op h_in : GAKEc.h_input -> (s_id, pkey) fmap -> GAKE_mod.h_input.

axiom h_in_eq (x1, x2 : GAKEc.h_input) (m : (s_id, pkey) fmap) : h_in x1 m = h_in x2 m => x1 = x2.

print GAKEc.HROc.RO.

module T_H (H : GAKE_mod.HROc.RO) : GAKEc.HROc.RO = {
  proc init = H.init 
  
  proc get(x : GAKEc.h_input) : tag * key = {
    var h, r;

    h <- h_in x Name_Red.O_GAKE.sid_pk;
    r <@ H.get(h);

    return r;
  } 
  
  proc set(x : GAKEc.h_input, y : tag * key) : unit = {
    var h, r;

    h <- h_in x Name_Red.O_GAKE.sid_pk;
    r <@ H.set(h, y);

    return r;
  } 
  
  proc rem(x : GAKEc.h_input) : unit = {
    var h, r;

    h <- h_in x Name_Red.O_GAKE.sid_pk;
    r <@ H.rem(h);

    return r;
  } 
  
  proc sample(x : GAKEc.h_input) : unit = {
    var h, r;

    h <- h_in x Name_Red.O_GAKE.sid_pk;
    r <@ H.sample(h);

    return r;
  }
}.

module (T_S (S : GAKEc.Server) : GAKE_mod.Server) (H : GAKE_mod.HROc.RO) = {
  proc keygen = S(T_H(H)).keygen

  proc respond_session(st: GAKE_mod.pr_st_server option, pk: pkey) : (GAKE_mod.pr_st_server * (pkey * tag) * key) option = {
    var b, v;
    var r <- None;

    b <- get_sid (g ^ (oget st).`1) Name_Red.O_GAKE.sid_pk;
    v <@ S(T_H(H)).respond_session(Some (b, (oget st).`1, (oget st).`2), pk);
    if (r <> None) {
      r <- Some (((oget v).`1.`2, (oget v).`1.`3), (oget v).`2, (oget v).`3);
    }

    return r;
  }
}.

module (T_C (C : GAKEc.Client) : GAKE_mod.Client) (H : GAKE_mod.HROc.RO) = {
  proc new_session(pk: pkey) : GAKE_mod.pr_st_client * pkey = {
    var b, st, m1;

    b <- get_sid pk Name_Red.O_GAKE.sid_pk;
    (st, m1) <@ C(T_H(H)).new_session(b, pk);

    return ((st.`2, st.`3), m1);
  }

  proc complete_session(st: GAKE_mod.pr_st_client, m: pkey * tag) : (GAKE_mod.pr_st_client * key) option = {
    var b, v;
    var r <- None;

    b <- get_sid st.`1 Name_Red.O_GAKE.sid_pk;
    v <@ C(T_H(H)).complete_session((b, st.`1, st.`2), m);
    if (v <> None) {
      r <- Some (((oget v).`1.`2, (oget v).`1.`3), (oget v).`2);
    }

    return r;
  }
}.


lemma gake_name_pkonly bit &m: `| Pr[GAKEc.E_GAKE_nodhs(GAKEb_st(S, C, T_H(H)), Hon_s_Red(A)).run(bit) @ &m : res]
     - Pr[GAKE_mod.E_GAKE_nodhs(GAKE_mod.GAKEb_nodhs(T_S(S), T_C(C), H), Name_Red(Hon_s_Red(A))).run(bit) @ &m : res] | 
                 <= Pr[GAKEc.E_GAKE_nodhs(GAKEb_st(S, C, GAKEc.HROc.RO), Hon_s_Red(A)).run(bit) @ &m : GAKEb_st.stop].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Name_Red.O_GAKE.stop => //; first last.
+ smt().
symmetry; proc; inline*.
wp; call (: Name_Red.O_GAKE.stop
          , ={glob S, glob C} /\ ={b0, tested}(GAKEb_st, GAKE_mod.GAKEb_nodhs) /\ ={pk_set, stop}(GAKEb_st, Name_Red.O_GAKE) /\ ={servers}(Hon_s_Red.O_GAKE, Hon_s_Red.O_GAKE)
               /\ (forall x, x \in HROc.RO.m{1} => GAKE_mod.HROc.RO.m{2}.[(h_in x Name_Red.O_GAKE.sid_pk{2})] = HROc.RO.m{1}.[x]) 
               /\ (forall x, x \in HROc.RO.m{1} <=> (h_in x Name_Red.O_GAKE.sid_pk{2}) \in GAKE_mod.HROc.RO.m{2})

           (*    /\ (forall x, x \in GAKEc.HROc.RO.m{1} => x.`3 \notin Name_Red.O_GAKE.sid_pk{2} => x \in Name_Red.O_GAKE.unreg_ro{2})
               /\ (forall x, x \notin GAKEc.HROc.RO.m{1} => x.`3 \in Name_Red.O_GAKE.sid_pk{2}
                    => (x.`1, x.`2, (oget Name_Red.O_GAKE.sid_pk{2}.[x.`3]), x.`4, x.`5) \notin GAKE_mod.HROc.RO.m{2})
               /\ (forall x, x \in Name_Red.O_GAKE.unreg_ro{2} => x \in GAKEc.HROc.RO.m{1} /\ Name_Red.O_GAKE.unreg_ro{2}.[x] = GAKEc.HROc.RO.m{1}.[x])
               /\ (forall x, x \in GAKEb_st.unreg_ro{1} <=> x \in Name_Red.O_GAKE.unreg_ro{2})
               /\ (forall x, x \in GAKEc.HROc.RO.m{1} => x \in Name_Red.O_GAKE.unreg_ro{2} 
                         \/ (x.`3 \in Name_Red.O_GAKE.sid_pk{2} /\ (x.`1, x.`2, (oget Name_Red.O_GAKE.sid_pk{2}.[x.`3]), x.`4, x.`5) \in GAKE_mod.HROc.RO.m{2}))
               /\ (forall x, x \in Name_Red.O_GAKE.unreg_ro{2} => x.`3 \in Name_Red.O_GAKE.sid_pk{2} 
                    => (x.`1, x.`2, (oget Name_Red.O_GAKE.sid_pk{2}.[x.`3]), x.`4, x.`5) \notin GAKE_mod.HROc.RO.m{2})
               /\ (forall x, x \in GAKE_mod.HROc.RO.m{2} => (exists b, b \in Name_Red.O_GAKE.sid_pk{2} /\ Name_Red.O_GAKE.sid_pk{2}.[b] = Some x.`3 
                                    /\ (x.`1, x.`2, b, x.`4, x.`5) \notin Name_Red.O_GAKE.unreg_ro{2}))
               /\ (forall x, x \in GAKEc.HROc.RO.m{1} => x.`4 \in Name_Red.O_GAKE.pk_set{2} /\ x.`5 \in Name_Red.O_GAKE.pk_set{2})
               /\ (forall x, x \in GAKE_mod.HROc.RO.m{2} => x.`4 \in Name_Red.O_GAKE.pk_set{2} /\ x.`5 \in Name_Red.O_GAKE.pk_set{2})
               /\ (forall x, x \in Name_Red.O_GAKE.unreg_ro{2} => x.`4 \in Name_Red.O_GAKE.pk_set{2} /\ x.`5 \in Name_Red.O_GAKE.pk_set{2})*)
               /\ (forall i, omap rem_sid_c GAKEb_st.c_smap{1}.[i] = GAKE_mod.GAKEb_nodhs.c_smap{2}.[i])
               /\ (forall i b pk m3, i \in GAKEb_st.c_smap{1} => get_trace (oget GAKEb_st.c_smap{1}.[i]) = Some ((b, pk), m3)
                   => b \in Name_Red.O_GAKE.sid_pk{2}
                                     /\ get_trace (rem_sid_c (oget GAKEb_st.c_smap{1}.[i])) 
                                         = Some ((oget Name_Red.O_GAKE.sid_pk{2}.[b], pk), m3))
               /\ (forall i pk_s pk m3, i \in GAKE_mod.GAKEb_nodhs.c_smap{2} => get_trace (oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[i]) = Some ((pk_s, pk), m3)
                    => pk_s \in Name_Red.O_GAKE.pk_set{2})
               /\ (forall i pk_s b pk m3, i \in GAKE_mod.GAKEb_nodhs.c_smap{2} => get_trace (rem_sid_c (oget GAKEb_st.c_smap{1}.[i])) = Some ((pk_s, pk), m3)
                    => b \in Name_Red.O_GAKE.sid_pk{2} => pk_s = oget Name_Red.O_GAKE.sid_pk{2}.[b]
                    => get_trace (oget GAKEb_st.c_smap{1}.[i]) = Some ((b, pk), m3))
               /\ (forall i st pt ir x1 x2 x5, i \in GAKEb_st.c_smap{1} => GAKEb_st.c_smap{1}.[i] = Some (Pending st pt ir) 
                    => st.`1 \in GAKEb_st.servers{1} /\ get_pkey (oget GAKEb_st.servers{1}.[st.`1]) = st.`2
                                     /\ st.`1 = pt.`1
                                     /\ g ^ st.`3 \in Name_Red.O_GAKE.pk_set{2} 
                                     /\ (x1, x2, st.`1, g ^ st.`3, x5) \notin GAKEb_st.unreg_ro{1})
               /\ (forall i st t k ir, i \in GAKEb_st.c_smap{1} => GAKEb_st.c_smap{1}.[i] = Some (Accepted st t k ir)
                    => st.`1 \in Name_Red.O_GAKE.sid_pk{2} /\ (oget Name_Red.O_GAKE.sid_pk{2}.[st.`1]) = st.`2 /\ st.`1 = t.`1.`1 /\ t.`2 <> None)
               /\ (forall b j, (b, j) \in GAKEb_st.s_smap{1} => b \in Name_Red.O_GAKE.sid_pk{2}
                                     /\ ((oget Name_Red.O_GAKE.sid_pk{2}.[b]), j) \in GAKE_mod.GAKEb_nodhs.s_smap{2}
                                     /\ rem_sid_s (oget GAKEb_st.s_smap{1}.[(b, j)]) = oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[(oget Name_Red.O_GAKE.sid_pk{2}.[b]), j])
               /\ (forall b j, b \in Name_Red.O_GAKE.sid_pk{2}
                    => (oget Name_Red.O_GAKE.sid_pk{2}.[b], j) \in GAKE_mod.GAKEb_nodhs.s_smap{2} <=> (b, j) \in GAKEb_st.s_smap{1})
               /\ (forall b j st t k ir, (b, j) \in GAKEb_st.s_smap{1} => GAKEb_st.s_smap{1}.[(b, j)] = Some (Accepted st t k ir)
                    => t.`1.`1 = b /\ t.`2 <> None /\ Name_Red.O_GAKE.sid_pk{2}.[b] = Some (g ^ st{1}.`2))
               /\ (forall pk j st t k ir, (pk, j) \in GAKE_mod.GAKEb_nodhs.s_smap{2} => GAKE_mod.GAKEb_nodhs.s_smap{2}.[(pk, j)] = Some (Accepted_mod st t k ir)
                    => t.`1.`1 = pk)
               /\ (forall pk_s j, (pk_s, j) \in GAKE_mod.GAKEb_nodhs.s_smap{2} => (exists pk m3, get_trace (oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[pk_s, j]) = Some ((pk_s, pk), m3)))
               /\ (forall bj pk m3, bj \in GAKEb_st.s_smap{1} => get_trace (oget GAKEb_st.s_smap{1}.[bj]) = Some ((bj.`1, pk), m3)
                    => bj.`1 \in Name_Red.O_GAKE.sid_pk{2}
                                     /\ get_trace (rem_sid_s (oget GAKEb_st.s_smap{1}.[bj])) 
                                         = Some ((oget Name_Red.O_GAKE.sid_pk{2}.[bj.`1], pk), m3))
               /\ (forall b j pk_s pk m3, (pk_s, j) \in GAKE_mod.GAKEb_nodhs.s_smap{2} => get_trace (oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[(pk_s,j)]) = Some ((pk_s, pk), m3)
                    => b \in Name_Red.O_GAKE.sid_pk{2} => pk_s = oget Name_Red.O_GAKE.sid_pk{2}.[b]
                    => get_trace (oget GAKEb_st.s_smap{1}.[(b, j)]) = Some ((b, pk), m3))
               /\ (forall b, b \in GAKEb_st.servers{1} <=> b \in Name_Red.O_GAKE.sid_pk{2})
               /\ (forall b, b \in GAKEb_st.servers{1} => get_pkey (oget GAKEb_st.servers{1}.[b]) = (oget Name_Red.O_GAKE.sid_pk{2}.[b])
                                     /\ !get_sr_dh (oget GAKEb_st.servers{1}.[b])
                                     /\ get_pkey (oget GAKEb_st.servers{1}.[b]) \in GAKE_mod.GAKEb_nodhs.servers{2}
                                     /\ (get_sr_ltk (oget GAKEb_st.servers{1}.[b]) 
                                         <=> get_sr_ltk (oget GAKE_mod.GAKEb_nodhs.servers{2}.[oget Name_Red.O_GAKE.sid_pk{2}.[b]])))
               /\ (forall pk b sk1 sk2, pk \in GAKE_mod.GAKEb_nodhs.servers{2} => obind GAKE_mod.get_skey GAKE_mod.GAKEb_nodhs.servers{2}.[pk] = Some sk1 
                    => b \in GAKEb_st.servers{1} => obind GAKEc.get_skey GAKEb_st.servers{1}.[b] = Some sk2 
                    => b \in Name_Red.O_GAKE.sid_pk{2} => (oget Name_Red.O_GAKE.sid_pk{2}.[b]) = pk => sk1 = sk2)
               /\ (forall b, b \in Name_Red.O_GAKE.sid_pk{2} => (oget Name_Red.O_GAKE.sid_pk{2}.[b{2}]) \in Name_Red.O_GAKE.pk_set{2})
               /\ (forall b pk, b \in Name_Red.O_GAKE.sid_pk{2} => oget Name_Red.O_GAKE.sid_pk{2}.[b] = pk
                    =>  obind GAKE_mod.get_skey GAKE_mod.GAKEb_nodhs.servers{2}.[pk] <> None)
              (* /\ (forall sk, g ^ sk \in GAKE_mod.GAKEb_nodhs.servers{2} => obind GAKE_mod.get_skey GAKE_mod.GAKEb_nodhs.servers{2}.[g ^ sk] = Some sk)
               /\ (forall sk pk b, b \in Name_Red.O_GAKE.sid_pk{2} => oget Name_Red.O_GAKE.sid_pk{2}.[b] = pk
                    => pk \in GAKE_mod.GAKEb_nodhs.servers{2} => obind GAKE_mod.get_skey GAKE_mod.GAKEb_nodhs.servers{2}.[pk] = Some sk 
                    => pk = g ^ sk)*)
               /\ (forall pk j x1 x2 x4 x5, pk \notin Name_Red.O_GAKE.pk_set{2} 
                    => pk \notin GAKE_mod.GAKEb_nodhs.servers{2} /\ (pk, j) \notin GAKE_mod.GAKEb_nodhs.s_smap{2} /\ (x1, x2, pk, x4, x5) \notin GAKE_mod.HROc.RO.m{2})
               /\ (forall b1 b2, b1 \in Name_Red.O_GAKE.sid_pk{2} => b2 \in Name_Red.O_GAKE.sid_pk{2} 
                    => (oget Name_Red.O_GAKE.sid_pk{2}.[b1]) = (oget Name_Red.O_GAKE.sid_pk{2}.[b2])
                    => b1 = b2)
          , GAKEb_st.stop{1} = Name_Red.O_GAKE.stop{2}) => //.

- exact A_ll. 

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
  auto => /> &1 &2 *.
- move => &2 bad; proc; inline. auto => />.
  by rewrite weight_dprod dkey_ll dtag_ll //=.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

- proc; inline.
  if => //.
  sp; if {2} => //.
  + if => //.
    + auto => />. smt().
    + sp; seq 1 1 : (#pre /\ kp{1} = (pk, sk){2}). 
      call (: (forall x, x \in HROc.RO.m{1} => GAKE_mod.HROc.RO.m{2}.[(h_in x)] = HROc.RO.m{1}.[x]) /\ (forall x, x \in HROc.RO.m{1} <=> (h_in x) \in GAKE_mod.HROc.RO.m{2})). 

proc; inline. auto => />.  
smt(emptyE).
proc; inline. 
sp; seq 1 1 : (#pre /\ r{1} = r0{2}). auto => />.
if => //. auto => /#. 
+ auto => /> &1 &2 *. smt(get_setE mem_set h_in_eq). 
auto => /> &1 &2 *. smt(get_setE mem_set h_in_eq).
proc; inline.  
auto => /> &1 &2 *. smt(get_setE mem_set h_in_eq).
proc; inline.  
auto => /> &1 &2 *. smt(remE mem_rem h_in_eq).
proc; inline.
sp; seq 1 1 : (#pre /\ r{1} = r0{2}). auto => />.
if => //. auto => /#. 
auto => /> &1 &2 *. smt(get_setE mem_set h_in_eq).
skip => /> &1 &2 *. split.

      if {2} => //.
      + match Some {2} ^match. auto => /#.
        auto => /> &1 &2 *. do !split; 1: smt(get_setE mem_set in_fsetU in_fset1). move => *. do !split; ~15,25: smt(get_setE mem_set in_fsetU in_fset1). 
move => i1 b1 pk0 m3 iin.
case (b{2} = b1) => beq; 2: by smt(get_setE mem_set in_fsetU in_fset1).
rewrite beq get_setE //=.
have<-: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[i1] = rem_sid_c (oget GAKEb_st.c_smap{1}.[i1]). smt().
smt(get_setE mem_set in_fsetU in_fset1).
move => b1 sk1 sk2.
case (b{2} = b1) => beq; 2: by smt(get_setE mem_set in_fsetU in_fset1).
rewrite beq !get_setE //=.
rewrite mem_set /get_as_Some //=.
      match None {2} ^match. auto => /#.
      auto => /> &1 &2 *. smt(). 
    auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
  if {1} => //; auto => />.
  call{1} (_: true ==> true).
  + admit.
  auto => />.
- move => &2 bad; proc; inline. if => //; sp; if => //; auto => />.
  islossless. smt().
  admit.
- move => &1; proc; inline.
  if => //.
  rcondf ^if; auto => />.

- sim />.
- move => &2 bad; proc; inline; auto => />.
- move => &1; proc; inline; auto => />.

- proc; inline.
  case (Name_Red.O_GAKE.stop{2}). 
  + rcondf {2} ^if. auto => />.
    sp; if {1} => //. 
    + sp; match {1} => //. 
      + sp; seq 1 0 : (#pre /\ sk_ce{1} \in dt); auto => />. 
      auto => />. 
    auto => />.
  sp 1 1; if {2} => //.
  + sp 1 5; if => //; 1: by auto => /#.
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
  + sp 1 6. match = => //. auto => /> &1 &2 *. smt(get_setE mem_set).
    + auto => />. smt(get_setE mem_set in_fsetU in_fset1).
    move => sk.
    match; 1..2: smt().
    + sp; match; 1..2: smt().
      + auto => />.
      move => stl str.
      sp. seq 1 1 : (#pre /\ ={sk_se}). auto => />. 
      sp; seq 1 1 : (#pre /\ r1{1} = r2{2}). auto => />.
      if {1} => //. rcondt {2} ^if. auto => /#.
      + auto => /> &1 &2 *. split. move => *. do !split; ~14,20: smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
move => b1 j1.
do rewrite get_setE //=.
case (b1 = b{2} /\ j1 = j{2}) => bjeq.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => b1 j1 pk m30.
case ((b1 = b{2}) /\ (j1 = j{2})) => [[] beq jeq|].
rewrite beq jeq mem_set //=.
rewrite !get_setE //=.
rewrite /rem_sid_s.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
          move => *. do !split; ~14,20: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => b1 j1.
do rewrite get_setE //=.
case (b1 = b{2} /\ j1 = j{2}) => bjeq.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
move => b1 j1 pk m30.
case ((b1 = b{2}) /\ (j1 = j{2})) => [[] beq jeq|].
rewrite beq jeq mem_set //=.
rewrite !get_setE //=.
rewrite /rem_sid_s.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      if {2} => //. 
      + sp; match Some {1} ^match. auto => /#.
        match Some {2} ^match. auto => /#.
        sp 3 4; if => //.
        + auto => /> &1 &2 *. smt().
        auto => /> &1 &2 *. smt().
      auto => />. smt(get_setE mem_set). 
    auto => />. smt(get_setE mem_set in_fsetU in_fset1). 
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
    + auto => />. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
    move => stl str.
    match {1} => //.
    + match Pending_mod {2} ^match. auto => /#.
      sp; seq 1 1 : (#pre /\ r1{1} = r2{2}). auto => />.
      if => //.  auto => /> &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? inv *.
have := inv i{2}.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      + sp 2 2; if => //. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
        + sp; match Some {1} ^match. auto => /#.
          match Some {2} ^match. auto => /#.
          sp 3 4; if => //.
          + auto => /> &1 &2 *. do !split; ~11,12,14: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => i0.
case (i0 = i{2}) => ieq; 2: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite !get_setE ieq //=.
rewrite /rem_sid_c //=.
do !split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => i1 b0 pk m32.
case (i1 = i{2}) => ieq; 2: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite !mem_set ieq get_setE //=.
move => [] pteq m3eq.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite /rem_sid_c //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => i1 b0 pk m32.
case (i1 = i{2}) => ieq; 2: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite !mem_set ieq get_setE //=.
move => [] //= [] pkbeq pteq m3eq.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
          auto => /> &1 &2 *. do !split; ~1,10..12: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => x.
case (x = (m3{2}.`1 ^ sk_ce{1}, pk_b{1} ^ sk_ce{1}, b{1}, g ^ sk_ce{1}, m3{2}.`1)) => xeq; 1: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite mem_set xeq //=.
rewrite get_set_neqE //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => i0.
case (i0 = i{2}) => ieq; 2: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite !get_setE ieq //=.
rewrite /rem_sid_c //=.
do !split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => i1 b0 pk m32.
case (i1 = i{2}) => ieq; 2: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite !mem_set ieq get_setE //=.
move => [] pteq m3eq.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite /rem_sid_c //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => i1 b0 pk m32.
case (i1 = i{2}) => ieq; 2: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite ieq mem_set get_setE //=.
move => [] //= pteq m3eq.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
        sp; match None {1} ^match. auto => /#.
        match None {2} ^match. auto => /#.
        sp 1 2; if => //.
        + auto => /> &1 &2 *. do !split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
        auto => /> &1 &2 *. do !split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      sp 1 1; if => //. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      + sp; match Some {1} ^match. auto => /#.
        match Some {2} ^match. auto => /#.
        sp 3 4; if => //.
        + auto => /> &1 &2 *.  do !split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
        auto => /> &1 &2 ? ? roxl roxr ? ? ? inv *.  do !split; ~1: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => i0.
case (i0 = i{2}) => ieq; 2: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
rewrite !get_setE ieq //=.
rewrite /rem_sid_c //=.
        do split; 1..3,5: smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
        have : Name_Red.O_GAKE.sid_pk{2}.[b{1}] = Some pk_b{2}. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
        move => bpk.
have : (t_A{2}, sk{2}) = (m3{2}.`2, sk{1}).
        have := inv (m3{2}.`1 ^ sk_ce{1}, pk_b{1} ^ sk_ce{1}, b{1}, g ^ sk_ce{1}, m3{2}.`1). 

have-> : (m3{2}.`1 ^ sk_ce{1}, pk_b{1} ^ sk_ce{1}, b{1}, g ^ sk_ce{1}, m3{2}.`1) \in
 HROc.RO.m{1} by smt().
have-> :  b{1} \in Name_Red.O_GAKE.sid_pk{2} by smt().
have-> :  (m3{2}.`1 ^ sk_ce{1}, pk_b{1} ^ sk_ce{1}, b{1}, g ^ sk_ce{1}, m3{2}.`1) \notin
 Name_Red.O_GAKE.unreg_ro{2} by smt().
rewrite roxl roxr.

         smt(get_setE mem_set in_fsetU in_fset1 pow_bij). smt().

      sp; match None {1} ^match. auto => /#.
      match None {2} ^match. auto => /#.
      sp 1 2; if => //.
      + auto => /> &1 &2 *. do !split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      auto => /> &1 &2 *. do !split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
    + match Accepted_mod {2} ^match. auto => /#.
      auto => />. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
    match Aborted_mod {2} ^match. auto => /#.
    auto => />. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
  match {1} => //. auto => />.
  match {1} => //; auto => />.
- move => &2 bad; proc; inline.
  sp; match => //; 1: auto => />.
  match => //; auto => />.  
  by rewrite weight_dprod dkey_ll dtag_ll //=.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

(* c_rev_skey *)
- proc; inline.
  sp 1 1; if {2} => //; 2: by auto => /#.
  sp; match; 1..2: smt().
  + auto => />.
  move => stl str.
  match {1} => //.
  + match Pending_mod {2} ^match. auto => /#.
    auto => />.
  + match Accepted_mod {2} ^match. auto => /#.
    if => //.
    + auto => /> &1 &2 25? inv inv2 *. rewrite /untested_partner_c. 
have<-: (card (get_partners_c t'{1} GAKEb_st.s_smap{1}) = card (get_partners_c t'{2} GAKE_mod.GAKEb_nodhs.s_smap{2})).
rewrite /get_partners_c.
rewrite -(inj_fcard_image_pw (fun (bj : s_id * int) => (oget Name_Red.O_GAKE.sid_pk{2}.[bj.`1], bj.`2))).
move => x y.
rewrite !mem_fdom !mem_filter //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
congr.
rewrite fsetP.
move => x.
print imageP.
rewrite imageP //=.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [a] [].
rewrite !mem_fdom !mem_filter //=.
move => [] ain tra ax.
split.
smt(get_setE mem_set).
have->: oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[x] = rem_sid_s (oget GAKEb_st.s_smap{1}.[a]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_c (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
have v := inv a t'{1}.`1.`2 t'{1}.`2 ain.
rewrite v.
rewrite tra.
smt().
smt().

have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_c (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin trx.
exists (t'{1}.`1.`1, x.`2).
rewrite mem_fdom mem_filter //=.
have : st'{1}.`2 = x.`1. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => x1eq.
split. split.
have : t'{1}.`1.`1 \in Name_Red.O_GAKE.sid_pk{2}. smt().
smt(get_setE mem_set).
have v := inv2 t'{1}.`1.`1 x.`2 st'{1}.`2 t'{1}.`1.`2 t'{1}.`2.
rewrite v; smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

have<-: (card (get_untested_partners_c t'{1} GAKEb_st.s_smap{1}) = card (get_untested_partners_c t'{2} GAKE_mod.GAKEb_nodhs.s_smap{2})).
rewrite /get_untested_partners_c.
rewrite -(inj_fcard_image_pw (fun (bj : s_id * int) => (oget Name_Red.O_GAKE.sid_pk{2}.[bj.`1], bj.`2))).
move => x y.
rewrite !mem_fdom !mem_filter //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
congr.
rewrite fsetP.
move => x.
print imageP.
rewrite imageP //=.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [a] [].
rewrite !mem_fdom !mem_filter //=.
move => [] ain tra ax.
split.
smt(get_setE mem_set).
have->: oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[x] = rem_sid_s (oget GAKEb_st.s_smap{1}.[a]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_c (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
have v := inv a t'{1}.`1.`2 t'{1}.`2 ain.
rewrite v.
rewrite tra.
smt().
smt().

have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_c (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin trx.
exists (t'{1}.`1.`1, x.`2).
rewrite mem_fdom mem_filter //=.
have : st'{1}.`2 = x.`1. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => x1eq.
split. split.
have : t'{1}.`1.`1 \in Name_Red.O_GAKE.sid_pk{2}. smt().
smt(get_setE mem_set).
have v := inv2 t'{1}.`1.`1 x.`2 st'{1}.`2 t'{1}.`1.`2 t'{1}.`2.
rewrite v; smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
smt().
      + auto => /> &1 &2 *. do split; smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      auto => />.
  match Aborted_mod {2} ^match. auto => /#.
  auto => />.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

(* s_rev_skey *)
- proc; inline.
  sp 1 1; if {2} => //.
    + sp. match; 1..2: smt(). 
      + auto => />.
      move => stl str.
      match {1}. 
      + match Pending_mod {2} ^match. auto => />. auto => /#.
        auto => />.
      + match Accepted_mod {2} ^match. auto => />. auto => /#.
        if => //.
        + auto => /> &1 &2 15? inv ? inv2 *.
rewrite /untested_partner_s.
rewrite /get_partners_s.
have-> : (fdom
          (filter
             (fun (_ : int)
                (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                get_trace val = Some t'{1}) GAKEb_st.c_smap{1})) = (fdom
          (filter
             (fun (_ : int)
                (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                get_trace val = Some t'{2}) GAKE_mod.GAKEb_nodhs.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [] xin trx.
split.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.

have v := inv x b{2} t'{1}.`1.`2 t'{1}.`2 xin.
rewrite v.
rewrite trx.
have{1}<- : t'{1}.`1.`1 = b{2}. smt().
smt().

smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
move => trx.
have v := inv2 x (g ^ st'{1}.`2) b{2} t'{1}.`1.`2 t'{1}.`2.
rewrite v.
smt().
rewrite trx. smt().
smt().
smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

rewrite /get_untested_partners_s.
have->: (fdom
            (filter
               (fun (_ : int)
                  (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                  get_trace val = Some t'{1} /\ get_ir_test val = false)
               GAKEb_st.c_smap{1})) = (fdom
            (filter
               (fun (_ : int)
                  (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                  get_trace val = Some t'{2} /\ get_ir_test val = false)
               GAKE_mod.GAKEb_nodhs.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [] xin [] trx xnt.
split.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.

have v := inv x b{2} t'{1}.`1.`2 t'{1}.`2 xin.
rewrite v.
rewrite trx.
have{1}<- : t'{1}.`1.`1 = b{2}. smt().
smt().
clear inv inv2.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
move => trx.
have v := inv2 x (g ^ st'{1}.`2) b{2} t'{1}.`1.`2 t'{1}.`2.
rewrite v; smt().
smt().
        + auto => /> &1 &2 *. do !split; ~2: smt(get_setE mem_set in_fsetU in_fset1 pow_bij). 
          move => b0 j0.
          case ((b0 = b{2}) /\ (j0 = j{2})); 2: smt(get_setE mem_set).
          move => [] beq jeq.
          rewrite beq jeq mem_set //=.
          smt(mem_set get_setE).
        auto => />.
      match Aborted_mod {2} ^match. auto => />. auto => /#.
      auto => />.
    match None {1} ^match. auto => />. auto => /#.
    auto => />.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

(* rev_ltkey *)
- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match; 1..2: smt().
    + auto => />.
    move => stl str.
    match {1} => //.
    + match Honest_mod {2} ^match. auto => /#.
      if => //.
      + auto => /> &1 &2 15? inv ? inv2*.
split.
move => + j pkin - /(_ j).
have : (b{2}, j) \in GAKEb_st.s_smap{1} by smt().
move => bjin //=.
rewrite /untested_partner_s.
rewrite /get_partners_s /get_untested_partners_s.
have->: (fdom
             (filter
                (fun (_ : int)
                   (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                   get_trace val =
                   Some
                     (oget
                        (get_trace
                           (oget
                              GAKE_mod.GAKEb_nodhs.s_smap{2}.[oget
                                           Name_Red.O_GAKE.sid_pk{2}.[b{2}], j]))))
                GAKE_mod.GAKEb_nodhs.c_smap{2})) = (fdom
                    (filter
                       (fun (_ : int)
                          (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                          get_trace val =
                          Some
                            (oget
                               (get_trace (oget GAKEb_st.s_smap{1}.[b{2}, j]))))
                       GAKEb_st.c_smap{1})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
smt().
have->: (fdom (filter (fun (_ : int) (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                     get_trace val =
                     Some (oget (get_trace (oget
                                GAKE_mod.GAKEb_nodhs.s_smap{2}.[oget Name_Red.O_GAKE.sid_pk{2}.[b{2}], j]))) /\
                     get_ir_test val = false) GAKE_mod.GAKEb_nodhs.c_smap{2})) = (fdom
                      (filter
                         (fun (_ : int)
                            (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                            get_trace val =
                            Some
                              (oget
                                 (get_trace
                                    (oget GAKEb_st.s_smap{1}.[b{2}, j]))) /\
                            get_ir_test val = false) GAKEb_st.c_smap{1})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split.
move => [#] xin trx.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
rewrite /rem_sid_c.
move => xnt.
do split; smt().
move => [#] xin trx xnt.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
rewrite /rem_sid_c.
do split; smt().
smt().
move => + j pkin - /(_ j).
have : (b{2}, j) \in GAKEb_st.s_smap{1} by smt().
move => bjin //=.
rewrite /untested_partner_s.
rewrite /get_partners_s /get_untested_partners_s.
have<-: (fdom
             (filter
                (fun (_ : int)
                   (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                   get_trace val =
                   Some
                     (oget
                        (get_trace
                           (oget
                              GAKE_mod.GAKEb_nodhs.s_smap{2}.[oget
                                           Name_Red.O_GAKE.sid_pk{2}.[b{2}], j]))))
                GAKE_mod.GAKEb_nodhs.c_smap{2})) = (fdom
                    (filter
                       (fun (_ : int)
                          (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                          get_trace val =
                          Some
                            (oget
                               (get_trace (oget GAKEb_st.s_smap{1}.[b{2}, j]))))
                       GAKEb_st.c_smap{1})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
smt().
have->: (fdom (filter (fun (_ : int) (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                     get_trace val =
                     Some (oget (get_trace (oget
                                GAKE_mod.GAKEb_nodhs.s_smap{2}.[oget Name_Red.O_GAKE.sid_pk{2}.[b{2}], j]))) /\
                     get_ir_test val = false) GAKE_mod.GAKEb_nodhs.c_smap{2})) = (fdom
                      (filter
                         (fun (_ : int)
                            (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                            get_trace val =
                            Some
                              (oget
                                 (get_trace
                                    (oget GAKEb_st.s_smap{1}.[b{2}, j]))) /\
                            get_ir_test val = false) GAKEb_st.c_smap{1})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split.
move => [#] xin trx.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
rewrite /rem_sid_c.
move => xnt.
do split; smt().
move => [#] xin trx xnt.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
rewrite /rem_sid_c.
do split; smt().
smt().
      + auto => /> &1 &2 *. do !split; smt(get_setE mem_set). 
      auto => />.
    + match Corrupt_mod {2} ^match. auto => /#.
      auto => />.
    match Dishonest_mod {2} ^match. auto => /#.
    auto => />.
  match {1} => //. match {1} => //. auto => /#.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

(* c_rev_ephkey *)
- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match; 1..2: smt().
    + auto => />.
    move => stl str.
    match {1} => //.
    + match Pending_mod {2} ^match. auto => /#.
      if => //.
      + auto => /> &1 &2 25? inv inv2 *. rewrite /untested_origins_c. 
have<-: (card (get_origins_c (pk_e{1}, None) GAKEb_st.s_smap{1}) = card (get_origins_c (pk_e{2}, None) GAKE_mod.GAKEb_nodhs.s_smap{2})).
rewrite /get_origins_c. 
rewrite -(inj_fcard_image_pw (fun (bj : s_id * int) => (oget Name_Red.O_GAKE.sid_pk{2}.[bj.`1], bj.`2))).
move => x y.
rewrite !mem_fdom !mem_filter //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
congr.
rewrite fsetP.
move => x.
rewrite imageP //=.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [a] [].
rewrite !mem_fdom !mem_filter //=.
move => [] ain [m2o] tra xeq.
split. smt(get_setE).
have->: oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[x] = rem_sid_s (oget GAKEb_st.s_smap{1}.[a]). smt().
have : (Pending_mod st{2} pk_e{2} ir{2}) = rem_sid_c (Pending st{1} pk_e{1} ir{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq pteq ireq.
rewrite pteq.
have v := inv a pk_e{1}.`2 m2o ain.
exists m2o.
rewrite v; smt().

have : (Pending_mod st{2} pk_e{2} ir{2}) = rem_sid_c (Pending st{1} pk_e{1} ir{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq pteq ireq.
rewrite pteq.
move => [] xin [m2o] tra. 

exists (pk_e{1}.`1, x.`2).
rewrite mem_fdom mem_filter //=.
have : st{1}.`2 = x.`1. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => x1eq.
split. split.
have : pk_e{1}.`1 \in Name_Red.O_GAKE.sid_pk{2}. smt().
smt(get_setE mem_set).
have v := inv2 pk_e{1}.`1 x.`2 st{1}.`2 pk_e{1}.`2 m2o.
rewrite v; smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

have<-: (card (get_untested_origins_c (pk_e{1}, None) GAKEb_st.s_smap{1}) = card (get_untested_origins_c (pk_e{2}, None) GAKE_mod.GAKEb_nodhs.s_smap{2})).
rewrite -(inj_fcard_image_pw (fun (bj : s_id * int) => (oget Name_Red.O_GAKE.sid_pk{2}.[bj.`1], bj.`2))).
move => x y.
rewrite !mem_fdom !mem_filter //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
congr.
rewrite fsetP.
move => x.
rewrite imageP //=.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [a] [].
rewrite !mem_fdom !mem_filter //=.
move => [] ain [] [m2o] tra ant xeq.
split. smt(get_setE).
have->: oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[x] = rem_sid_s (oget GAKEb_st.s_smap{1}.[a]). smt().
have : (Pending_mod st{2} pk_e{2} ir{2}) = rem_sid_c (Pending st{1} pk_e{1} ir{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq pteq ireq.
rewrite pteq.
have v := inv a pk_e{1}.`2 m2o ain.
split; 2: by smt().
exists m2o.
rewrite v; smt().

have : (Pending_mod st{2} pk_e{2} ir{2}) = rem_sid_c (Pending st{1} pk_e{1} ir{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq pteq ireq.
rewrite pteq.
move => [] xin [] [m2o] trx xnt. 

exists (pk_e{1}.`1, x.`2).
rewrite mem_fdom mem_filter //=.
have : st{1}.`2 = x.`1. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => x1eq.
split. split.
have : pk_e{1}.`1 \in Name_Red.O_GAKE.sid_pk{2}. smt().
smt(get_setE mem_set).
have v := inv2 pk_e{1}.`1 x.`2 st{1}.`2 pk_e{1}.`2 m2o.
rewrite v; smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
smt().
      + auto => /> &1 &2 *. smt(get_setE mem_set).
      auto => />.
    + match Accepted_mod {2} ^match. auto => /#.
      if => //.
      + auto => /> &1 &2 25? inv inv2 *. rewrite /untested_partner_c. 
have<-: (card (get_partners_c t{1} GAKEb_st.s_smap{1}) = card (get_partners_c t{2} GAKE_mod.GAKEb_nodhs.s_smap{2})).
rewrite /get_partners_c.
rewrite -(inj_fcard_image_pw (fun (bj : s_id * int) => (oget Name_Red.O_GAKE.sid_pk{2}.[bj.`1], bj.`2))).
move => x y.
rewrite !mem_fdom !mem_filter //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
congr.
rewrite fsetP.
move => x.
print imageP.
rewrite imageP //=.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [a] [].
rewrite !mem_fdom !mem_filter //=.
move => [] ain tra ax.
split.
smt(get_setE mem_set).
have->: oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[x] = rem_sid_s (oget GAKEb_st.s_smap{1}.[a]). smt().
have : (Accepted_mod st{2} t{2} k{2} ir{2}) = rem_sid_c (Accepted st{1} t{1} k{1} ir{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
have v := inv a t{1}.`1.`2 t{1}.`2 ain.
rewrite v.
rewrite tra.
smt().
smt().

have : (Accepted_mod st{2} t{2} k{2} ir{2}) = rem_sid_c (Accepted st{1} t{1} k{1} ir{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin trx.
exists (t{1}.`1.`1, x.`2).
rewrite mem_fdom mem_filter //=.
have : st{1}.`2 = x.`1. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => x1eq.
split. split.
have : t{1}.`1.`1 \in Name_Red.O_GAKE.sid_pk{2}. smt().
smt(get_setE mem_set).
have v := inv2 t{1}.`1.`1 x.`2 st{1}.`2 t{1}.`1.`2 t{1}.`2.
rewrite v; smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

have<-: (card (get_untested_partners_c t{1} GAKEb_st.s_smap{1}) = card (get_untested_partners_c t{2} GAKE_mod.GAKEb_nodhs.s_smap{2})).
rewrite /get_untested_partners_c.
rewrite -(inj_fcard_image_pw (fun (bj : s_id * int) => (oget Name_Red.O_GAKE.sid_pk{2}.[bj.`1], bj.`2))).
move => x y.
rewrite !mem_fdom !mem_filter //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
congr.
rewrite fsetP.
move => x.
print imageP.
rewrite imageP //=.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [a] [].
rewrite !mem_fdom !mem_filter //=.
move => [] ain tra ax.
split.
smt(get_setE mem_set).
have->: oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[x] = rem_sid_s (oget GAKEb_st.s_smap{1}.[a]). smt().
have : (Accepted_mod st{2} t{2} k{2} ir{2}) = rem_sid_c (Accepted st{1} t{1} k{1} ir{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
have v := inv a t{1}.`1.`2 t{1}.`2 ain.
rewrite v.
rewrite tra.
smt().
smt().

have : (Accepted_mod st{2} t{2} k{2} ir{2}) = rem_sid_c (Accepted st{1} t{1} k{1} ir{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin trx.
exists (t{1}.`1.`1, x.`2).
rewrite mem_fdom mem_filter //=.
split. split.
have : t{1}.`1.`1 \in Name_Red.O_GAKE.sid_pk{2}. smt().
smt(get_setE mem_set).
have v := inv2 t{1}.`1.`1 x.`2 st{1}.`2 t{1}.`1.`2 t{1}.`2.
rewrite v; smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
smt().

      + auto => /> &1 &2 *. smt(get_setE mem_set).
      auto => />.
    match Aborted_mod {2} ^match. auto => /#.
    auto => />.
  match {1}; auto => />.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

(* s_rev_epkhkey *)
- proc; inline.
  sp 1 1; if {2} => //.
  + sp. match; 1..2: smt().
    + auto => />.
    move => stl str.
    match {1}. 
    + match Pending_mod {2} ^match. auto => /#.
      auto => />.
    + match Accepted_mod {2} ^match. auto => /#.
      if => //.
      + auto => /> &1 &2 15? inv ? inv2 *.
rewrite /untested_partner_s.
rewrite /get_partners_s.
have-> : (fdom
          (filter
             (fun (_ : int)
                (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                get_trace val = Some t{1}) GAKEb_st.c_smap{1})) = (fdom
          (filter
             (fun (_ : int)
                (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                get_trace val = Some t{2}) GAKE_mod.GAKEb_nodhs.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [] xin trx.
split.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
have : (Accepted_mod st{2} t{2} k{2} ir{2}) = rem_sid_s (Accepted st{1} t{1} k{1} ir{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.

have v := inv x b{2} t{1}.`1.`2 t{1}.`2 xin.
rewrite v.
rewrite trx.
have{1}<- : t{1}.`1.`1 = b{2}. smt().
smt().

smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

have : (Accepted_mod st{2} t{2} k{2} ir{2}) = rem_sid_s (Accepted st{1} t{1} k{1} ir{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
move => trx.
have v := inv2 x (g ^ st{1}.`2) b{2} t{1}.`1.`2 t{1}.`2.
rewrite v.
smt().
rewrite trx. smt().
smt().
smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

rewrite /get_untested_partners_s.
have->: (fdom
            (filter
               (fun (_ : int)
                  (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                  get_trace val = Some t{1} /\ get_ir_test val = false)
               GAKEb_st.c_smap{1})) = (fdom
            (filter
               (fun (_ : int)
                  (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                  get_trace val = Some t{2} /\ get_ir_test val = false)
               GAKE_mod.GAKEb_nodhs.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [] xin trx.
split.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
have : (Accepted_mod st{2} t{2} k{2} ir{2}) = rem_sid_s (Accepted st{1} t{1} k{1} ir{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.

have v := inv x b{2} t{1}.`1.`2 t{1}.`2 xin.
rewrite v.
rewrite trx.
have{1}<- : t{1}.`1.`1 = b{2}. smt().
smt().
clear inv inv2.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

have : (Accepted_mod st{2} t{2} k{2} ir{2}) = rem_sid_s (Accepted st{1} t{1} k{1} ir{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
move => trx.
have v := inv2 x (g ^ st{1}.`2) b{2} t{1}.`1.`2 t{1}.`2.
rewrite v; smt().
smt().
      + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
      auto => />.
    match Aborted_mod {2} ^match. auto => /#.
    auto => />.
  match None {1} ^match. auto => /#.
  auto => />.
- move => &2 bad; proc; inline. sp; match; auto => />. 
  auto => /#.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

(* c_test *)
- proc; inline.
  sp 1 1; if {2} => //.
  + sp. if => //.
    + match; 1..2: smt().
      + auto => />.
      move => stl str.
      match {1} => //.
      + match Pending_mod {2} ^match. auto => /#.
        auto => />.
      + match Accepted_mod {2} ^match. auto => /#.
        if => //.
        + auto => /> &1 &2 25? inv inv2 *. 
rewrite /fresh_partner_c.
have<-: (card (get_origins_c t'{1} GAKEb_st.s_smap{1}) = card (get_origins_c t'{2} GAKE_mod.GAKEb_nodhs.s_smap{2})).
rewrite /get_origins_c. 
rewrite -(inj_fcard_image_pw (fun (bj : s_id * int) => (oget Name_Red.O_GAKE.sid_pk{2}.[bj.`1], bj.`2))).
move => x y.
rewrite !mem_fdom !mem_filter //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
congr.
rewrite fsetP.
move => x.
rewrite imageP //=.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [a] [].
rewrite !mem_fdom !mem_filter //=.
move => [] ain [m2o] tra xeq.
split. smt(get_setE).
have->: oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[x] = rem_sid_s (oget GAKEb_st.s_smap{1}.[a]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_c (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
have v := inv a t'{1}.`1.`2 m2o ain.
exists m2o.
rewrite v; smt().

have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_c (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin [m2o] tra. 

exists (t'{1}.`1.`1, x.`2).
rewrite mem_fdom mem_filter //=.
have : st'{1}.`2 = x.`1. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => x1eq.
split. split.
have : t'{1}.`1.`1 \in Name_Red.O_GAKE.sid_pk{2}. smt().
smt(get_setE mem_set).
have v := inv2 t'{1}.`1.`1 x.`2 st'{1}.`2 t'{1}.`1.`2 m2o.
rewrite v; smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).

have<-: (card (get_fresh_partners_c t'{1} GAKEb_st.s_smap{1} GAKEb_st.servers{1}) = card (get_fresh_partners_c t'{2} GAKE_mod.GAKEb_nodhs.s_smap{2} GAKE_mod.GAKEb_nodhs.servers{2})).
rewrite -(inj_fcard_image_pw (fun (bj : s_id * int) => (oget Name_Red.O_GAKE.sid_pk{2}.[bj.`1], bj.`2))).
move => x y.
rewrite !mem_fdom !mem_filter //=.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
congr.
rewrite fsetP.
move => x.
rewrite imageP //=.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [a] [].
rewrite !mem_fdom !mem_filter //=.
move => [#] ain tra ant ansr antb xeq.
split. smt(get_setE).
have->: oget GAKE_mod.GAKEb_nodhs.s_smap{2}.[x] = rem_sid_s (oget GAKEb_st.s_smap{1}.[a]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_c (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
have v := inv a t'{1}.`1.`2 t'{1}.`2 ain.
rewrite v; smt().

have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_c (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_c //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [#] xin trx xnt xnsr xntb. 

exists (t'{1}.`1.`1, x.`2).
rewrite mem_fdom mem_filter //=.
have : st'{1}.`2 = x.`1. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
move => x1eq.
split. split.
have : t'{1}.`1.`1 \in Name_Red.O_GAKE.sid_pk{2}. smt().
smt(get_setE mem_set).
have v := inv2 t'{1}.`1.`1 x.`2 st'{1}.`2 t'{1}.`1.`2 t'{1}.`2.
clear inv inv2.
rewrite v; smt().
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
smt().

        + if => //.
          + auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
          auto => /> &1 &2 *. smt(get_setE mem_set in_fsetU in_fset1).
        auto => />.
      match Aborted_mod {2} ^match. auto => /#.
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
 
(* s_test *)
- proc; inline.
  sp 1 1; if {2} => //.
  + sp; if => //.
    + match; 1..2: smt().
      + auto => />.
      move => stl str.
      match {1} => //.
      + match Pending_mod {2} ^match. auto => /#.
        auto => />.
      + match Accepted_mod {2} ^match. auto => /#.
        if => //.
        + auto => /> &1 &2 15? inv ? inv2 *. 
rewrite /fresh_partner_s.
rewrite /get_origins_s.
have-> : (fdom
            (filter
               (fun (_ : int)
                  (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                  exists (m2o : (pkey * tag) option),
                    get_trace val = Some (t'{1}.`1, m2o)) GAKEb_st.c_smap{1}))
 = fdom
            (filter
               (fun (_ : int)
                  (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                  exists (m2o : (pkey * tag) option),
                    get_trace val = Some (t'{2}.`1, m2o)) GAKE_mod.GAKEb_nodhs.c_smap{2}).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [] xin.

have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [m2o] trx.
have v := inv x b{2} t'{1}.`1.`2 m2o.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
exists m2o.
rewrite v; smt().

have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
move => [m2o] trx.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have v := inv2 x (g ^ st'{1}.`2) b{2} t'{1}.`1.`2 m2o.
rewrite v; smt().
rewrite /get_fresh_partners_s.
have->: (fdom
            (filter
               (fun (_ : int)
                  (val : GAKEc.pr_st_client GAKEc.instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (t'{1}.`1, m2o)) /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\ get_ir_eph val = false)
               GAKEb_st.c_smap{1})) = (fdom
            (filter
               (fun (_ : int)
                  (val : GAKE_mod.pr_st_client GAKE_mod.instance_state) =>
                  (exists (m2o : (pkey * tag) option),
                     get_trace val = Some (t'{2}.`1, m2o)) /\
                  get_ir_test val = false /\
                  get_ir_sess val = false /\ get_ir_eph val = false)
               GAKE_mod.GAKEb_nodhs.c_smap{2})).
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [] xin.

have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] [m2o] trx xfresh.
have v := inv x b{2} t'{1}.`1.`2 m2o.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
split.
exists m2o.
rewrite v; smt(). 
clear inv inv2.
smt().


have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
move => [] [m2o] trx xfresh.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have v := inv2 x (g ^ st'{1}.`2) b{2} t'{1}.`1.`2 m2o.
split.
exists m2o.
rewrite v; smt().
rewrite /rem_sid_c //= in xfresh. clear inv inv2.
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
        + if => //.
          + auto => /> &1 &2 15? inv ? inv2 *. do !split; ~2: smt(get_setE mem_set). 
congr.
rewrite /get_fresh_partners_s.
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [] xin.

have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] [m2o] trx xfresh.
have v := inv x b{2} t'{1}.`1.`2 m2o.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
split.
exists m2o.
rewrite v; smt().
clear inv inv2. smt().


have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
move => [] [m2o] trx xfresh.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have v := inv2 x (g ^ st'{1}.`2) b{2} t'{1}.`1.`2 m2o.
split.
exists m2o.
rewrite v; smt().
rewrite /rem_sid_c //= in xfresh. clear inv inv2.
smt(get_setE mem_set).
          auto => /> &1 &2 15? inv ? inv2 *. do !split; ~1: smt(get_setE mem_set).
congr.
rewrite /get_fresh_partners_s.
rewrite fsetP.
move => x.
rewrite !mem_fdom !mem_filter //=.
split. 
move => [] xin.

have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] [m2o] trx xfresh.
have v := inv x b{2} t'{1}.`1.`2 m2o.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
split.
exists m2o.
rewrite v; smt().
clear inv inv2.
smt().


have : (Accepted_mod st'{2} t'{2} k'{2} ir'{2}) = rem_sid_s (Accepted st'{1} t'{1} k'{1} ir'{1}). smt().
rewrite /rem_sid_s //=.
move => [#] steq teq keq ireq.
rewrite teq.
move => [] xin.
have->: oget GAKE_mod.GAKEb_nodhs.c_smap{2}.[x] = rem_sid_c (oget GAKEb_st.c_smap{1}.[x]). smt().
move => [] [m2o] trx xfresh.
split. smt(get_setE mem_set in_fsetU in_fset1 pow_bij).
have v := inv2 x (g ^ st'{1}.`2) b{2} t'{1}.`1.`2 m2o.
split.
exists m2o.
rewrite v; smt().
rewrite /rem_sid_c //= in xfresh. clear inv inv2.
smt(get_setE mem_set).

        auto => />.
      match Aborted_mod {2} ^match. auto => /#.
      auto => />.
    auto => />.
  if {1} => //.
  match None {1} ^match. auto=> /#. 
  auto => />.
- move => &2 bad; proc; inline. sp; if => //; match; auto => />. 
  match => //; if => //; if; auto => />.
  by rewrite dkey_ll.
- move => &1; proc; inline.
  rcondf ^if; auto => />.

auto => />.
split. smt(emptyE in_fset0).
move => roeq inj csm ssm pkin inv inv2 inv3 inv4 inv5 inv6 inv7 inv8 inv9 inv10 inv11 inv12 inv13 inv14 inv15 inv16 inv17 inv18 inv19 inv20 inv21 inv22 inv23 inv24 inv25 inv26 inv27 rl rr al hsl csl pksl ssl sl stl tl url ml ar hsr csr tr str huh ssr sr pksr urr mr.
by case : (!str) => />.
qed.
