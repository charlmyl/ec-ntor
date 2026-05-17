require import AllCore Distr List.
require GAKE_nosid NTOR.

clone import NTOR as NTORc.
import UAKEc DH.DDH DH.G DH.GP DH.FD.

(* ------------------------------------------------------------------------------------------ *)
(* Modified protocol *)
(* ------------------------------------------------------------------------------------------ *)
clone import GAKE_nosid as UAKE_mod with
  type pkey <- pkey,
  type skey <- skey,
  type key <- key,
  type tag <- tag,
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

(* ------------------------------------------------------------------------------------------ *)
(* Protocol using all public values as input *)
module (S : UAKE_mod.Server) (H : RO) = {
  proc keygen() : (pkey * skey) = {
    var sk_s, pk_s;

    sk_s <$ dt;
    pk_s <- g ^ sk_s;

    return (pk_s, sk_s);
  }

  proc respond_session(st : s_state option, m2: pkey) : (s_state * (pkey * tag) * key) option = {
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

module (C : UAKE_mod.Client) (H : RO) = {
  proc new_session(pk) : c_state * pkey = {
    var pk_ce, sk_ce;

    sk_ce <$ dt;
    pk_ce <- g ^ sk_ce;

    return ((pk, sk_ce), pk_ce);
  }

  proc complete_session(st: c_state, m3: pkey * tag) : (c_state * key) option = {
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
