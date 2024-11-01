require import AllCore Distr List.

type s_id, state.

type pkey, skey.
op dkp : (pkey * skey) distr.

op (^) : pkey -> skey -> pkey.

type key_mac, key_sess, tag.
type trace = pkey * (pkey * tag).

type cr_status = { cr_ephemeral: bool; cr_session: bool }.
type sr_status = { sr_longterm: bool; sr_ephemeral: bool; sr_session: bool }.

type instance_state = [
  CPending  of s_id & pkey & pkey & skey & cr_status
| CAccepted of s_id & trace & key_sess & cr_status
| SAccepted of trace & key_sess & sr_status
| Aborted
].

op hash_ntor: pkey -> pkey -> s_id -> pkey -> pkey -> key_mac * key_sess.
op hash_mac: key_mac -> s_id -> pkey -> pkey -> tag.

module type PKI = {
  proc set_cert(b: s_id, pk: pkey): bool
  proc get_pkey(b : s_id): pkey option
}.

module type Server = {
  proc init(b: s_id) : pkey option
  proc respond_session(st: instance_state option, b: s_id, pk: pkey) : (instance_state * (pkey * tag)) option
}.

module type Client = {
  proc new_session(st: instance_state option, b: s_id) : (instance_state * pkey) option
  proc complete_session(st: instance_state option, pk: pkey, t: tag) : instance_state option
}.

print cr_status.

module Server (P: PKI) = {
  proc init(b: s_id) : pkey option = {
    var sk_s, pk_s;
    var r <- false;

    (pk_s, sk_s) <$ dkp;
    r <@ P.set_cert(b, pk_s);

    return if r then Some pk_s else None;
  }

  proc respond_session(st : instance_state , b, pk_ce) : (instance_state * (pkey * tag)) option = {
    var pk_se, sk_se;
    var sk', sk, t_B, tr, sr, st';
    var r <- None;
    
    if (Some st = None) {
      (pk_se, sk_se) <$ dkp;
      (sk', sk) <- hash_ntor (pk_ce ^ sk_se) (pk_ce ^ sk_se) b pk_ce pk_se; (* where is private ltk coming from *)
      t_B <- hash_mac sk' b pk_se pk_ce;
      tr <- (pk_ce, (pk_se, t_B));
      sr <- {| sr_ephemeral = false; sr_session = false; sr_longterm = false |};
      st' <- SAccepted tr sk sr; (* Not true I need to know if there is an longterm key reveal before that point *)
      r <- Some (st', (pk_se, t_B));
    }

    return r;
  }
}.

module Client (P : PKI) = {
  proc new_session(st: instance_state, b) : (instance_state * pkey) option = {
    var r <- None;
    var cert, pk_ce, sk_ce, cr, st';

    cert <@ P.get_pkey(b);
    if (cert is Some pk_b) {
      if (Some st = None) {
        (pk_ce, sk_ce) <$ dkp;
        cr <- {| cr_ephemeral = false; cr_session = false |};
        st' <- CPending b pk_b pk_ce sk_ce cr;
        r <- Some (st', pk_ce);
      }
    }

    return r;
  }

  proc complete_session(st: instance_state, pk_se, t_B) : instance_state option = {
    var r <- None;
    var sk', sk, t_A, tr, st';

    if (st is CPending b pk_b pk_ce sk_ce cr) {
      (sk', sk) <- hash_ntor (pk_se ^ sk_ce) (pk_b ^ sk_ce) b pk_ce pk_se;
      t_A <- hash_mac sk' b pk_se pk_ce;
      if (t_A = t_B) {
        tr <- (pk_ce, (pk_se, t_B));
        st' <- CAccepted b tr sk cr;
        r <- Some st';
      }
    }
    return r;
  }
}.
