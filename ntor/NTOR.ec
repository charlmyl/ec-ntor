require import AllCore Distr List.

type id, sid.

type pkey, skey.
op dkp : (pkey * skey) distr.

op (^) : pkey -> skey -> pkey.

type key_mac, key_sess, tag.

op hash_sid: pkey -> sid.
op hash_ntor: pkey -> pkey -> id -> pkey -> pkey -> key_mac * key_sess.
op hash_mac: key_mac -> id -> pkey -> pkey -> tag.

module Server = {
  proc init() = {
    var sk, pk;

    (pk, sk) <$ dkp;
    return (pk, sk);
  }

  proc respond_session(b, pk_s, sk_s, pk_ce) : sid * (pkey * tag) * (key_sess * id option * pkey list list) = {
    var pk_se, sk_se;
    var sid, sk', sk, t_B;

    (pk_se, sk_se) <$ dkp;
    sid <- hash_sid pk_se;
    (sk', sk) <- hash_ntor (pk_ce ^ sk_se) (pk_ce ^ sk_s) b pk_ce pk_se;
    t_B <- hash_mac sk' b pk_se pk_ce;
    return (sid, (pk_se, t_B), (sk, None, [[pk_ce]; [pk_se; pk_s]]));
  }
}.

module type PKI = {
  proc get_pkey(b : id): pkey option
}.

module Client (P : PKI) = {
  proc new_session(b) = {
    var r <- None;
    var cert, pk_ce, sk_ce, sid;

    cert <@ P.get_pkey(b);
    if (cert is Some pk_b) {
      (pk_ce, sk_ce) <$ dkp;
      sid <- hash_sid pk_ce;
      r <- Some (sid, (b, pk_ce), (b, pk_b, sk_ce, pk_ce));
    }

    return r;
  }

  proc complete_session(st, pk_se, t_B) = {
    var r <- None;
    var b, pk_b, sk_ce, pk_ce, sk', sk, t_A;

    (b, pk_b, sk_ce, pk_ce) <- st;
    (sk', sk) <- hash_ntor (pk_se ^ sk_ce) (pk_b ^ sk_ce) b pk_ce pk_se;
    t_A <- hash_mac sk' b pk_se pk_ce;
    if (t_A = t_B) {
      r <- Some (None<:sid>, None<:id * pkey>, (sk, b, [[pk_ce]; [pk_se; pk_b]]));
    }
    return r;
  }
}.
