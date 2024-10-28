require import AllCore Distr List.

type id, state.

type pkey, skey.
op dkp : (pkey * skey) distr.

op (^) : pkey -> skey -> pkey.

type key_mac, key_sess, tag.

op hash_ntor: pkey -> pkey -> id -> pkey -> pkey -> key_mac * key_sess.
op hash_mac: key_mac -> id -> pkey -> pkey -> tag.

module type PKI = {
  proc set_cert(b: id, pk: pkey): bool
  proc get_pkey(b : id): pkey option
}.

module Server (P: PKI) = {
  proc init(b: id) = {
    var sk_s, pk_s;
    var r <- false;

    (pk_s, sk_s) <$ dkp;
    r <@ P.set_cert(b, pk_s);

    return if r then Some (pk_s, sk_s) else None;
  }

  proc respond_session(st, b, pk_ce) : (pkey * tag) option * key_sess option = {
    var pk_se, sk_se, sk_s;
    var sk', sk, t_B;
    var r <- (None, None);
    
    sk_s <- st;
    if (sk_s <> None) {
      (pk_se, sk_se) <$ dkp;
      (sk', sk) <- hash_ntor (pk_ce ^ sk_se) (pk_ce ^ oget sk_s) b pk_ce pk_se;
      t_B <- hash_mac sk' b pk_se pk_ce;
      r <- (Some (pk_se, t_B), Some sk);
    }

    return r;
  }
}.

module Client (P : PKI) = {
  proc new_session(st: state, b) : (pkey * skey) option = {
    var r <- None;
    var cert, pk_ce, sk_ce;

    cert <@ P.get_pkey(b);
    if (cert is Some pk_b) {
      if (Some st = None) {
        (pk_ce, sk_ce) <$ dkp;
        r <- Some (pk_ce, sk_ce);
      }
    }

    return r;
  }

  proc complete_session(st, pk_se, t_B) : (key_sess * id) option = {
    var r <- None;
    var b, pk_b, sk_ce, pk_ce, sk', sk, t_A;

    (b, pk_b, sk_ce, pk_ce) <- st;
    (sk', sk) <- hash_ntor (pk_se ^ sk_ce) (pk_b ^ sk_ce) b pk_ce pk_se;
    t_A <- hash_mac sk' b pk_se pk_ce;
    if (t_A = t_B) {
      r <- Some (sk, b);
    }
    return r;
  }
}.
