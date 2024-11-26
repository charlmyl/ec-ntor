require import AllCore Distr List.
require GAKE.

type s_id, pkey, skey.
op dkp : (pkey * skey) distr.

op (^) : pkey -> skey -> pkey.

type key_mac, key, tag.
type trace = pkey * (pkey * tag).
type sid = (s_id * pkey) * trace.

type pr_st_client = s_id * pkey * pkey * skey.
type pr_st_server = s_id * skey * skey option.

clone import GAKE as GAKEc with
  type s_id <- s_id,
  type pkey <- pkey,
  type skey <- skey,
  type key <- key,
  type pr_st_client <- pr_st_client,
  type pr_st_server <- pr_st_server,
  op dkp <- dkp.


op hash_ntor: pkey -> pkey -> s_id -> pkey -> pkey -> tag * key.

module Server : Server = {
  proc keygen() : (pkey * skey) = {
    var sk_s, pk_s;

    (pk_s, sk_s) <$ dkp;

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
       (pk_se, sk_se) <$ dkp;
        (t_B, sk) <- hash_ntor (m2 ^ sk_se) (m2 ^ sk_b) b m2 pk_se;
        r <- Some ((b, sk_b, Some sk_se), (pk_se, t_B), sk);
      }
    end;
    return r;
  }
}.

module Client : Client = {
  proc new_session(b, pk) : pr_st_client * pkey = {
    var pk_ce, sk_ce;

    (pk_ce, sk_ce) <$ dkp;

    return ((b, pk, pk_ce, sk_ce), pk_ce);
  }

  proc complete_session(st: pr_st_client, m3: pkey * tag) : (pr_st_client * key) option = {
    var r <- None;
    var b, pk_b, pk_ce, sk_ce, sk, t_A;

    (b, pk_b, pk_ce, sk_ce) <- st;
    (t_A, sk) <- hash_ntor (m3.`1 ^ sk_ce) (pk_b ^ sk_ce) b pk_ce m3.`1;
    if (t_A = m3.`2) {
      r <- Some (st, sk);
    }
    return r;
  }
}.
