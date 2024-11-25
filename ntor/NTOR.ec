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


op hash_ntor: pkey -> pkey -> s_id -> pkey -> pkey -> key_mac * key.
op hash_mac: key_mac -> s_id -> pkey -> pkey -> tag.

module Server : Server = {
  proc keygen() : (pkey * skey) = {
    var sk_s, pk_s;

    (pk_s, sk_s) <$ dkp;

    return (pk_s, sk_s);
  }

  proc respond_session(st : pr_st_server option, m2: pkey) : (pr_st_server * (pkey * tag) * key) option = {
    var b, sk_b, pk_se, sk_se, sko;
    var sk', sk, t_B, tr;
    var r <- None;
    
    match st with 
    | None => {}
    | Some st => {
       (b, sk_b, sko) <- st;
       (pk_se, sk_se) <$ dkp;
        (sk', sk) <- hash_ntor (m2 ^ sk_se) (m2 ^ sk_b) b m2 pk_se;
        t_B <- hash_mac sk' b pk_se m2;
        tr <- (m2, (pk_se, t_B));
        r <- Some ((b, sk_b, Some sk_se), (pk_se, t_B), sk);
      }
    end;
    return r;
  }
}.

module Client : Client = {
  proc new_session(b, pk) : (pr_st_client * pkey) option = {
    var r;
    var pk_ce, sk_ce;

    (pk_ce, sk_ce) <$ dkp;
    r <- Some ((b, pk, pk_ce, sk_ce), pk_ce);

    return r;
  }

  proc complete_session(st: pr_st_client, m3: pkey * tag) : (pr_st_client * key) option = {
    var r <- None;
    var b, pk_b, pk_ce, sk_ce, sk', sk, t_A, tr;

    (b, pk_b, pk_ce, sk_ce) <- st;
    (sk', sk) <- hash_ntor (m3.`1 ^ sk_ce) (pk_b ^ sk_ce) b pk_ce m3.`1;
    t_A <- hash_mac sk' b m3.`1 pk_ce;
    if (t_A = m3.`2) {
      tr <- (pk_ce, m3);
      r <- Some (st, sk);
    }
    return r;
  }
}.
