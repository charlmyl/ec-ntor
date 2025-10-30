require import AllCore Distr List.
require GAKE DiffieHellman.

clone DiffieHellman as DH.
import DH.DDH DH.G DH.GP DH.FD.

type s_id.
type pkey = group.
type skey = exp.

type key_mac, key, tag.

op [lossless] dtag : tag distr.
op [lossless] dkey : key distr.

clone import GAKE as GAKEc with
  type s_id <- s_id,
  type pkey <- pkey,
  type skey <- skey,
  type key <- key,
  type tag <- tag,
  op dskey <- dt,
  op dkey <- dkey,
  op dtag <- dtag.

import HROc.


module (NTOR_S : Server) (H : RO) = {
  proc keygen() : (pkey * skey) = {
    var sk_s, pk_s;

    sk_s <$ dt;
    pk_s <- g ^ sk_s;

    return (pk_s, sk_s);
  }

  proc respond_session(st : pr_st_server option, m2: pkey) : (pr_st_server * (pkey * tag) * key) option = {
    var b, sk_b, pk_se, sk_se, sko;
    var sk, t_B;
    var r <- None;
    
    match st with 
    | None => {}
    | Some st => {
        (b, sk_b, sko) <- st;
        sk_se <$ dt;
        pk_se <- g ^ sk_se;
        
        (t_B, sk) <@ H.get(m2 ^ sk_se, m2 ^ sk_b, b, m2, pk_se);
        r <- Some ((b, sk_b, Some sk_se), (pk_se, t_B), sk);
      }
    end;
    return r;
  }
}.

module (NTOR_C : Client) (H : RO) = {
  proc new_session(b, pk) : pr_st_client * pkey = {
    var pk_ce, sk_ce;

    sk_ce <$ dt;
    pk_ce <- g ^ sk_ce;

    return ((b, pk, sk_ce), pk_ce);
  }

  proc complete_session(st: pr_st_client, m3: pkey * tag) : (pr_st_client * key) option = {
    var r <- None;
    var b, pk_b, sk_ce, sk, t_A;

    (b, pk_b, sk_ce) <- st;
    (t_A, sk) <@ H.get(m3.`1 ^ sk_ce, pk_b ^ sk_ce, b, g ^ sk_ce, m3.`1);
    if (t_A = m3.`2) {
      r <- Some (st, sk);
    }
    return r;
  }
}.
