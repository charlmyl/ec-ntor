require import AllCore Distr List NTOR.
require GAKE_nosid DiffieHellman.

import DH.DDH DH.G DH.GP DH.FD.


(* ------------------------------------------------------------------------------------------ *)
(* Modified protocol *)
(* ------------------------------------------------------------------------------------------ *)
type pr_st_client_mod = pkey * skey.
type pr_st_server_mod = skey * skey option.

clone import GAKE_nosid as GAKE_mod with
  type trace <- trace,
  type pkey <- pkey,
  type skey <- skey,
  type key <- key,
  type tag <- tag,
  type pr_st_client <- pr_st_client_mod,
  type pr_st_server <- pr_st_server_mod,
  op dskey <- dt,
  op dkey <- dkey,
  op dtag <- dtag.


(* ------------------------------------------------------------------------------------------ *)
(* Modified rondom oracle *)
clone import PROM.FullRO as HRO_mod_c with
  type in_t    <= h_input,
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

module NTOR_C_mod (H : RO) : Client = {
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
