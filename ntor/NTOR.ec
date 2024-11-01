require import AllCore Distr List.

type s_id, state.

type pkey, skey.
op dkp : (pkey * skey) distr.

op (^) : pkey -> skey -> pkey.

type key_mac, key_sess, tag.
type trace = pkey * (pkey * tag).

type ir_status = { ir_ephemeral: bool; ir_session: bool }.

type instance_state = [
  CPending  of s_id & pkey & pkey & skey & ir_status
| CAccepted of s_id & trace & key_sess & ir_status
| SAccepted of trace & key_sess & ir_status
| Aborted of ir_status
].

op hash_ntor: pkey -> pkey -> s_id -> pkey -> pkey -> key_mac * key_sess.
op hash_mac: key_mac -> s_id -> pkey -> pkey -> tag.

module type PKI = {
  proc set_cert(b: s_id, pk: pkey): bool
  proc get_pkey(b : s_id): pkey option
}.

module Server (P: PKI) = {
  proc init(b: s_id) : (pkey * skey) option = {
    var sk_s, pk_s;
    var r <- false;

    (pk_s, sk_s) <$ dkp;
    r <@ P.set_cert(b, pk_s);

    return if r then Some (pk_s, sk_s) else None;
  }

  proc respond_session(st : instance_state, b, pk_ce, sk_b) : (instance_state * (pkey * tag)) option = {
    var pk_se, sk_se;
    var sk', sk, t_B, tr, st';
    var r <- None;
    
    if (Some st = None) {
      (pk_se, sk_se) <$ dkp;
      (sk', sk) <- hash_ntor (pk_ce ^ sk_se) (pk_ce ^ sk_b) b pk_ce pk_se;
      t_B <- hash_mac sk' b pk_se pk_ce;
      tr <- (pk_ce, (pk_se, t_B));
      st' <- SAccepted tr sk {| ir_ephemeral = false; ir_session = false |};
      r <- Some (st', (pk_se, t_B));
    }

    return r;
  }
}.

module Client (P : PKI) = {
  proc new_session(st: instance_state, b) : (instance_state * pkey) option = {
    var r <- None;
    var cert, pk_ce, sk_ce, st';

    cert <@ P.get_pkey(b);
    if (cert is Some pk_b) {
      if (Some st = None) {
        (pk_ce, sk_ce) <$ dkp;
        st' <- CPending b pk_b pk_ce sk_ce {| ir_ephemeral = false; ir_session = false |};
        r <- Some (st', pk_ce);
      }
    }

    return r;
  }

  proc complete_session(st: instance_state, pk_se, t_B) : instance_state option = {
    var r <- None;
    var sk', sk, t_A, tr, st';

    if (st is CPending b pk_b pk_ce sk_ce ir) {
      (sk', sk) <- hash_ntor (pk_se ^ sk_ce) (pk_b ^ sk_ce) b pk_ce pk_se;
      t_A <- hash_mac sk' b pk_se pk_ce;
      if (t_A = t_B) {
        tr <- (pk_ce, (pk_se, t_B));
        st' <- CAccepted b tr sk ir;
        r <- Some st';
      }
    }
    return r;
  }
}.
