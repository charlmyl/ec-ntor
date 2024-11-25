(* Intermediate Games *)
require import AllCore FMap FSet Distr NTOR.
import GAKEc.

(* Proof:
- Step 0: inline everathing;
- Step 1: prevent collisions in and between long-term and ephemeral
  keys;
- Step 2: prevent collisions in random oracle output;
  + IN THEORY: "at most one partner" is possible here; consider it?
- Step 3: "reduction" if the adversary wins, it must be because they
  directly queried H on the right input before the test session;
  + Question: do we want to first hybrid over the instance the
    adversary tests? Francois thinks yes.
- Step 4: case split: is the test session a client or a server?
  + Client: case split: (check Stebila et al)
    * is the server's long-term key compromised? => Gap-DH one way;
    * if not => Gap-DH another way.
  + Server: case split:
    * is the server's long-term key compromised? => Gap-DH one way;
    * if not => Gap-DH another way.
*)

(* Removing key collisions *)
module Game1 = {
  var servers : (s_id, server_state) fmap

  var c_smap : (int, pr_st_client instance_state) fmap
  var s_smap : (s_id * int, pr_st_server instance_state) fmap
  
  var keypairs : ((pkey * skey)) fset

  proc init_mem() : unit = {
    servers <- empty;
    c_smap <- empty;
    s_smap <- empty;
  }
  
  proc set_cert(b: s_id, pk: pkey) : unit option = {
    var r <- None;

    if (b \notin servers) {
      servers.[b] <- Dishonest pk;
      r <- Some ();
    }
    return r;
  }


  proc init_s(b: s_id) : pkey option = {
    var kp;

    if (b \notin servers) {
      kp <$ dkp;
      servers.[b] <- Honest kp;
    }
    return omap get_pkey servers.[b];
  }

  proc send_msg1(i: int, m1: s_id) : pkey option = {
    var st, pk_b, kp;
    var r <- None;

    st <- c_smap.[i];
    if (m1 \in servers) {
      pk_b <- get_pkey (oget servers.[m1]);
      match st with
      | None => {
          kp <$ dkp;
          c_smap.[i] <- Pending (m1, pk_b, fst kp, snd kp) (fst kp) (false, false, false);
          r <- Some (fst kp);
        }
      | Some st => {
          match st with
          | Pending st _ ir => c_smap.[i] <- Aborted (Some st) None ir;
          | Accepted _ _ _ _ => { }
          | Aborted _ _ _ => { }
          end;
        }
      end;
    }
    return r;
  }

  proc send_msg2(b: s_id, j: int, m2: pkey) : (pkey * tag) option = {
    var sko, pk_se, sk_se, t_B, sk;
    var r <- None;

    sko <- obind get_skey servers.[b];
    if (sko is Some sk_b) (* Server was initialised as honest *) {
      match s_smap.[b, j] with
      | None => {
          (pk_se, sk_se) <$ dkp;
          (t_B, sk) <- hash_ntor (m2 ^ sk_se) (m2 ^ sk_b) b m2 pk_se;
          s_smap.[(b, j)] <- Accepted (b, sk_b, Some sk_se) (m2, Some (pk_se, t_B)) sk (false, false, false);
          r <- Some (pk_se, t_B);
        }
      | Some st => { (* only completed sessions would be stored, and those can't be aborted; do nothing *) }
      end;
    }

    return r;
  }

  proc send_msg3(i: int, m3: pkey * tag) : unit option = {
    var b, pk_b, pk_ce, sk_ce, t_A, sk;
    var r <- None;

    match c_smap.[i] with
    | None => { } (* Abort? *)
    | Some _ => {
        match oget c_smap.[i] with
        | Pending st pt ir => {
            (b, pk_b, pk_ce, sk_ce) <- st;
            (t_A, sk) <- hash_ntor (m3.`1 ^ sk_ce) (pk_b ^ sk_ce) b pk_ce m3.`1;
            if (t_A = m3.`2) {
              c_smap.[i] <- Accepted st (pt, Some m3) sk ir;
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
    | Some _ => {
        if (oget c_smap.[i] is Accepted st' t' k' ir') {
          if (!get_ir_test (oget c_smap.[i]) /\ untested_partner_c t' s_smap <> Some false) {
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
    | Some _ => {
        if (oget s_smap.[b, j] is Accepted st' t' k' ir') {
          if (!get_ir_test (oget s_smap.[b, j]) /\ untested_partner_s t' c_smap <> Some false) {
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
    | Some _ => {
        if (oget servers.[b] is Honest kp) {
          if (forall j,
                (b, j) \in s_smap
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
    | Some _ => {
        match oget c_smap.[i] with
        | Pending st pk_e ir => {
            if (untested_partner_c (pk_e, None) s_smap <> Some false) {
              ek <- Some (get_eph_c st);
              c_smap.[i] <- set_ir_eph (Pending st pk_e ir);
            }
          }
        | Accepted st t k ir => {
            if (!get_ir_test (oget c_smap.[i]) /\ untested_partner_c t s_smap <> Some false) {
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
    | Some _ => {
        if (oget s_smap.[b, j] is Accepted st t k ir) { (* No Pending on Server side *)
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
    var k <- None;

    match c_smap.[i] with
    | None => { }
    | Some _ => {
        if (oget c_smap.[i] is Accepted st' t' k' ir') {
          if (   !get_ir_sess (oget c_smap.[i]) /\ !get_ir_eph (oget c_smap.[i]) 
              /\ fresh_partner_c t' s_smap servers <> Some false) {
            k <- Some k';
            c_smap.[i] <- set_ir_test (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }

  proc s_test(b: s_id, j: int) : key option = {
    var k <- None;

    match s_smap.[(b, j)] with
    | None => { }
    | Some _ => {
        if (oget s_smap.[b, j] is Accepted st' t' k' ir') {
          if (   !get_ir_sess (oget s_smap.[b, j]) 
              /\ !(get_ir_eph (oget s_smap.[b, j]) /\ get_sr_ltk (oget servers.[b]))
              /\ fresh_partner_s t' c_smap <> Some false) {
            k <- Some k';
            s_smap.[(b, j)] <- set_ir_test (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }
}.
