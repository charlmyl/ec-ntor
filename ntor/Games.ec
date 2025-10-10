(* Intermediate Games *)
require import AllCore FMap FSet Distr NTOR NTOR_nosid.
import GAKE_mod HRO_mod_c DH.DDH DH.G DH.GP DH.FD.


(* Proof:
- Step 0: inline everathing;
- Step 1: prevent collisions in and between long-term and ephemeral
  keys;
- Step 2: prevent collisions in random oracle output;
  + IN THEORY: "at most one partner" is possible here; consider it?
- Step 3: split the random oracle so that tag and key are sampled
  separately;
- Step 3.5: delay the sampling of the session key to reveal or test;
  (use Eager/Lazy, replacing the RO call in msg2 + msg3 with sample)
- Step 4: "reduction" if the adversary wins, it must be because they
  directly queried H on the right input before the test session;
  + Question: do we want to first hybrid over the instance the
    adversary tests? Francois thinks yes.
- Step 5: case split: is the test session a client or a server?
  + Client: case split: (check Stebila et al)
    * is the server's long-term key compromised? => Gap-DH one way;
    * if not => Gap-DH another way.
  + Server: case split:
    * is the server's long-term key compromised? => Gap-DH one way;
    * if not => Gap-DH another way.
  
Steps done:
- Step 0: inline everathing;
- Step 1: prevent collisions in and between long-term and ephemeral
  keys;
- Step 2: split the random oracle so that tag and key are sampled
  separately;
- Step 3: delay the sampling of the session key to reveal or test;
  (use Eager/Lazy, replacing the RO call in msg2 + msg3 with sample)
- Step 4: 

*)

print pr_st_client.
(* Step0 inlining everything and adding bad event *)
module Game0 : GAKE_nodhs_i = {
  (* This is not aligned with the sequence above *)
  var b0 : bool 

  var hm : (pkey * pkey * pkey * pkey * pkey, tag * key) fmap

  var servers : (pkey, server_state) fmap

  var c_smap : (int, pr_st_client instance_state) fmap
  var s_smap : (pkey * int, pr_st_server instance_state) fmap
  
  var tested : int option
  
  var kp_set : pkey fset
  var bad : bool


  proc init_mem(b: bool) : unit = {
    b0 <- b;
    hm <- empty;
    servers <- empty;
    c_smap <- empty;
    s_smap <- empty;
    tested <- None;
    kp_set <- fset0;
    bad <- false;
  }
  
  (* random oracle *)
  proc h(x: pkey * pkey * pkey * pkey * pkey) : tag * key = {
    var tk;

    tk <$ dtag `*` dkey;
    if (x \notin hm) {
      hm.[x] <- tk;
    }
    
    return oget hm.[x];
  }

  (* server management *)
  proc init_s() : pkey option = {
    var sk, pk;
    var r <- None;

    sk <$ dt;
    pk <- g ^ sk;
    if (pk \notin servers) {
      bad <- bad \/ pk \in kp_set;
      kp_set <- kp_set `|` fset1 pk;
      servers.[pk] <- Honest sk;
      r <- Some pk;
    }
    return r;
  }

  proc send_msg1(i: int, m1: pkey) : pkey option = {
    var st, pk, sk;
    var r <- None;

    st <- c_smap.[i];
    if (m1 \in servers) {
      match st with
      | None => {
          sk <$ dt;
          pk <- g ^ sk;
          bad <- bad \/ pk \in kp_set;
          kp_set <- kp_set `|` fset1 pk;
          c_smap.[i] <- Pending (m1, sk) (m1, pk) (false, false, false);
          r <- Some pk;
        }
      | Some st => { (*
          match st with
          | Pending st pt ir => c_smap.[i] <- Aborted (Some st) (Some (pt, None)) ir;
          | Accepted _ _ _ _ => { }
          | Aborted _ _ _ => { }
          end;*)
        }
      end;
    }
    return r;
  }

  proc send_msg2(b: pkey, j: int, m2: pkey) : (pkey * tag) option = {
    var sko, sk, pk, t_B, key;
    var r <- None;

    sko <- obind get_skey servers.[b];
    if (sko is Some sk_b) (* Server was initialised as honest *) {
      match s_smap.[b, j] with
      | None => {
          sk <$ dt;
          pk <- g ^ sk;
          bad <- bad \/ pk \in kp_set;
          kp_set <- kp_set `|` fset1 pk;
          (t_B, key) <@ h(m2 ^ sk, m2 ^ sk_b, g ^ sk_b, m2, pk);
          s_smap.[(b, j)] <- Accepted (sk_b, Some sk) ((b, m2), Some (pk, t_B)) key (false, false, false);
          r <- Some (pk, t_B);
        }
      | Some st => { (* only completed sessions would be stored, and those can't be aborted; do nothing *) }
      end;
    }

    return r;
  }

  proc send_msg3(i: int, m3: pkey * tag) : unit option = {
    var b, sk_ce, t_A, key;
    var r <- None;

    match c_smap.[i] with
    | None => { } (* Abort? *)
    | Some st => {
        match st with
        | Pending st pt ir => {
            (b, sk_ce) <- st;
            (t_A, key) <@ h(m3.`1 ^ sk_ce, b ^ sk_ce, b, g ^ sk_ce, m3.`1);
            if (t_A = m3.`2) {
              c_smap.[i] <- Accepted st (pt, Some m3) key ir;
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
    | Some st => {
        (* only accepted client instances that are not tested and 
           that not only have tested partners can be sesskey revealed *)
        if (st is Accepted st' t' k' ir') {
          if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_c t' s_smap = Some false)) {
            k <- Some k';
            c_smap.[i] <- set_ir_sess (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }

  proc s_rev_skey(b: pkey, j: int) : key option = {
    var k <- None;

    match s_smap.[(b, j)] with
    | None => { }
    | Some st => {
        (* only accepted server instances that are not tested and 
           that not only have tested partners can be sesskey revealed *)
        if (st is Accepted st' t' k' ir') {
          if (!(get_ir_test (oget s_smap.[b, j]) \/ untested_partner_s t' c_smap = Some false)) {
            k <- Some k';
            s_smap.[(b, j)] <- set_ir_sess (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }

  proc rev_ltkey(b: pkey) : skey option = {
    var ltk <- None;

    match servers.[b] with
    | None => { }
    | Some st => {
        (* a server can be ltkey revealed if no instance of it is ephkey revealed 
           in case that instance or all its partners are tested *) 
        if (st is Honest sk) {
          if (forall j,
                (b, j) \in s_smap (* just checking instances of b *)
                => !(   (   get_ir_test (oget s_smap.[b, j])
                            (* This is always OK (get_trace always Some on server side *)
                         \/ untested_partner_s (oget (get_trace (oget s_smap.[b, j]))) c_smap = Some false)
                     /\ get_ir_eph (oget s_smap.[b,j]))) {
            ltk <- Some sk; 
            servers.[b] <- Corrupt sk; 
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
    | Some st => {
        match st with
          (* client instances can be ephkey revealed when pending if there isn't 
             a tested origin partner (agreeing on first message *)
        | Pending st pk_e ir => {
            if (untested_origins_c (pk_e, None) s_smap <> Some false) {
              ek <- Some (get_eph_c st);
              c_smap.[i] <- set_ir_eph (Pending st pk_e ir);
            }
          }
          (* accepted client instamces can only be ephkey revealed when not tested and 
             if not all partners are tested *)
        | Accepted st t k ir => {
            if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_c t s_smap = Some false)) {
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

  proc s_rev_ephkey(b: pkey, j: int) : skey option = {
    var ek <- None;

    match s_smap.[b, j] with
    | None => { }
    | Some st => {
        (* only accepted server instances that are not ltkey revealed in case they 
           or all partners are tested can be ephkey revealed *)
        if (st is Accepted st t k ir) { (* No Pending on Server side *)
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
    var ks;
    var k <- None;

    if (tested = None) {
      match c_smap.[i] with
      | None => { }
      | Some st => {
          (* only accepted client instances that are not sesskey revealed, not ephkey revealed 
             and not all partner instances are unfresh can be tested *)
          if (st is Accepted st' t' k' ir') {
            if (!(   get_ir_sess (oget c_smap.[i]) \/ get_ir_eph (oget c_smap.[i]) 
                  \/ fresh_partner_c t' s_smap servers = Some false)) {
              if (b0 = false) {
                k <- Some k';
                c_smap.[i] <- set_ir_test (Accepted st' t' k' ir');
              } else {
                ks <$ dkey;
                k <- Some ks;
                c_smap.[i] <- set_ir_test (Accepted st' t' k' ir');
              }
              tested <- Some i;
           }
          }
        }
      end;
    }
    return k;
  }

  proc s_test(b: pkey, j: int) : key option = {
    var ks;
    var k <- None;

    if (tested = None) {
      match s_smap.[(b, j)] with
      | None => { }
      | Some st => {
          (* only accepted server instances that are not sesskey revealed, not trivially broken
             and not all partner instances are unfresh can be tested *)
          if (st is Accepted st' t' k' ir') {
            if (!(   get_ir_sess (oget s_smap.[b, j]) 
                  \/ (get_ir_eph (oget s_smap.[b, j]) /\ get_sr_ltk (oget servers.[b]))
                  \/ fresh_partner_s t' c_smap = Some false)) {
              if (b0 = false) {
                k <- Some k';
                s_smap.[(b, j)] <- set_ir_test (Accepted st' t' k' ir');
              } else {
                ks <$ dkey;
                k <- Some ks;
                s_smap.[(b, j)] <- set_ir_test (Accepted st' t' k' ir');
              }
              tested <- Some (pick (get_fresh_partners_s t' c_smap));
            }
          }
        }
      end;
    }
    return k;
  }
}.

print Game0.


(* Step1: Removing key collisions *)
module Game1 = Game0 with {
  proc init_s [
    [^if.^bad<- - ^servers<-] + (!bad)
  ]

  proc send_msg1 [
    [^if.^match#None.^bad<- - ^r<-] + (!bad)
  ]

  proc send_msg2 [
    [^match#Some.^match#None.^bad<- - ^r<-] + (!bad)
  ]
}.

print Game1.


(* Step2: Splitting the random oracle and tracking bad event of overlap between RO queries and test query *)
module Game2 = Game1 with {
  var h1m : (pkey * pkey * pkey * pkey * pkey, tag) fmap
  var h2m : (pkey * pkey * pkey * pkey * pkey, key) fmap
  var hq : (pkey * pkey * pkey * pkey * pkey) fset
  var tq : (pkey * pkey * pkey * pkey * pkey) option
  var badq : bool
  var tags : (pkey * pkey * pkey * pkey * pkey, tag) fmap
  var badt : bool

  proc init_mem [
    -1 + { h1m <- empty; h2m <- empty; hq <- fset0; tq <- None; badq <- false; tags <- empty; badt <- false; }
  ]

  proc h [
    var t : tag
    var k : key
    ^tk<$ ~ {t <$ dtag; if (x \notin h1m) {h1m.[x] <- t;} k <$ dkey; if (x \notin h2m) {h2m.[x] <- k;} }
    ^if -
    1 + ^ {hq <- hq `|` fset1 x; badq <- badq \/ (tq <> None /\ oget tq \in hq);}
  ] res ~ ((oget h1m.[x], oget h2m.[x]))

  proc send_msg2 [
    var ts : tag
    var ks : key
    var x : pkey * pkey * pkey * pkey * pkey
    ^match#Some.^match#None.^if.2 ~ { x <- (m2 ^ sk, m2 ^ sk_b, g ^ sk_b, m2, pk);
                                      ts <$ dtag;
                                      if (x \notin h1m) {h1m.[x] <- ts;} 
                                      t_B <- oget h1m.[x];
                                      ks <$ dkey;
                                      if (x \notin h2m) {h2m.[x] <- ks;} 
                                      key <- oget h2m.[x]; 
                                      tags.[x] <- t_B; }
  ]

  proc send_msg3 [
    var ts : tag
    var ks : key
    var x : pkey * pkey * pkey * pkey * pkey
    ^match#Some.^match#Pending.2 ~ { x <- (m3.`1 ^ sk_ce, b ^ sk_ce, b, g ^ sk_ce, m3.`1);
                                     ts <$ dtag;
                                     if (x \notin h1m) {h1m.[x] <- ts;} 
                                     t_A <- oget h1m.[x];
                                     ks <$ dkey;
                                     if (x \notin h2m) {h2m.[x] <- ks;} 
                                     key <- oget h2m.[x];
                                     badt <- badt \/ x \notin tags; }

  ]
  


  proc c_test [
    var x : pkey * pkey * pkey * pkey * pkey
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- + ^ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
    ^if.^match#Some.^match#Accepted.^if.^if?^ks<$ + ^ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
  ]

  proc s_test [
    var x : pkey * pkey * pkey * pkey * pkey
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- + ^ {x <- ((t'.`1).`2 ^ (oget st'.`2), (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, g ^ (oget st'.`2)); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
    ^if.^match#Some.^match#Accepted.^if.^if?^ks<$ + ^ {x <- ((t'.`1).`2 ^ (oget st'.`2), (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, g ^ (oget st'.`2)); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
  ]
}.

print Game2. 


(* Step3: Removing case of adversary guessing the right tag *)
module Game3 = Game2 with {
  proc send_msg3 [
    [^match#Some.^match#Pending.^badt<- - 3] + (!badt)
  ]
}.

print Game3.


(* Step4: Replacing key computation on real side with sampling *)
module Game4 = Game3 with {
  var counti : int
  var handles_c : (int, int) fmap
  var test_ephrev_s : bool option
  var b_test : pkey option
  var j_test : int option

  proc init_mem [
    -1 + { counti <- 0; handles_c <- empty; test_ephrev_s <- None; b_test <- None; j_test <- None; }
  ]

  proc send_msg1 [
    ^if.^match#None.^if.^r<- + {counti <- counti + 1; handles_c.[counti] <- i;}
  ]

  proc send_msg2 [
    ^match#Some.^match#None.^if.^ks<$ ~ {key <- witness;}
    [^match#Some.^match#None.^if.^if{2} - ^key<-] -
  ]

  proc send_msg3 [
    ^match#Some.^match#Pending.^ks<$ ~ {key <- witness;}
    [^match#Some.^match#Pending.^if{2} - ^key<-] -
  ]

  proc c_rev_skey [
    var ks : key
    var x : pkey * pkey * pkey * pkey * pkey
    ^match#Some.^match#Accepted.^if.^k<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1); 
                                            ks <$ dkey;
                                            if (x \notin h2m) {h2m.[x] <- ks;} 
                                            k <- h2m.[x];}
  ]

  proc s_rev_skey [
    var ks : key
    var x : pkey * pkey * pkey * pkey * pkey
    ^match#Some.^match#Accepted.^if.^k<- ~ {x <- ((t'.`1).`2 ^ (oget st'.`2), (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, g ^ (oget st'.`2));
                                            ks <$ dkey;
                                            if (x \notin h2m) {h2m.[x] <- ks;} 
                                            k <- h2m.[x];}
  ]

  proc c_test [
    var ks2 : key
    var p : (pkey * int)
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- ~ {ks <$ dkey; if (x \notin h2m) {h2m.[x] <- ks;} k <- h2m.[x]; 
                                                    p <- pick (get_fresh_partners_c t' s_smap servers); 
                                                    test_ephrev_s <- Some (get_ir_eph (oget s_smap.[p]));
                                                    b_test <- Some p.`1; j_test <- Some p.`2;}
    ^if.^match#Some.^match#Accepted.^if.^if?^ks<$ + ^ {ks2 <$ dkey; if (x \notin h2m) {h2m.[x] <- ks2;} k <- h2m.[x];
                                                       p <- pick (get_fresh_partners_c t' s_smap servers); 
                                                       test_ephrev_s <- Some (get_ir_eph (oget s_smap.[p]));
                                                       b_test <- Some p.`1; j_test <- Some p.`2;}

  ]

  proc s_test [
    var ks2 : key
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- ~ {ks <$ dkey; if (x \notin h2m) {h2m.[x] <- ks;} k <- h2m.[x]; test_ephrev_s <- Some ir'.`1; b_test <- Some b; j_test <- Some j;}
    ^if.^match#Some.^match#Accepted.^if.^if?^ks<$ + ^ {ks2 <$ dkey; if (x \notin h2m) {h2m.[x] <- ks2;} k <- h2m.[x]; test_ephrev_s <- Some ir'.`1; b_test <- Some b; j_test <- Some j;}
  ]
}.


module DDH_valid = {
  proc ddh_input(x : group * group * group * group * group) : (group option * group option) = {
    var r <- (Some x.`1, Some x.`2);
    var ddh1, ddh2;

    ddh1 <- (x.`4 ^ (loge x.`5) = x.`1);
    ddh2 <- (x.`4 ^ (loge x.`3) = x.`2);
    if (ddh1 /\ ddh2) {
      r <- (None, None);
    }

    return r;
  }
}.


print Game4.

module GameDDH = Game4 with {
  var stop : bool
  var h1mDDH : (pkey option * pkey option * pkey * pkey * pkey, tag) fmap
  var h2mDDH : (pkey option * pkey option * pkey * pkey * pkey, key) fmap

  proc init_mem [
    -1 + { h1mDDH <- empty; h2mDDH <- empty; stop <- false; }
  ]
  
  proc h [
    var x1, x2 : group option
    var rt : tag
    var rk : key
    
    ^badq<- + {(x1, x2) <@ DDH_valid.ddh_input(x);
               stop <- stop \/ ((x1, x2) = (None, None));}
    ^if ~ ((x1, x2, x.`3, x.`4, x.`5) \notin h1mDDH)
    ^if.^h1m<- ~ {h1mDDH.[(x1, x2, x.`3, x.`4, x.`5)] <- t;}
    ^if + {rt <- oget h1mDDH.[(x1, x2, x.`3, x.`4, x.`5)];}
    ^if{2} ~ ((x1, x2, x.`3, x.`4, x.`5) \notin h2mDDH)
    ^if{2}.^h2m<- ~ {h2mDDH.[(x1, x2, x.`3, x.`4, x.`5)] <- k;}
    ^if{2} + {rk <- oget h2mDDH.[(x1, x2, x.`3, x.`4, x.`5)];}
    
    
    ] res ~ (rt, rk)

  proc send_msg2 [
    ^match#Some.^match#None.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h1mDDH)
    ^match#Some.^match#None.^if.^if.^h1m<- ~ {h1mDDH.[(None, None, x.`3, x.`4, x.`5)] <- ts;}
    ^match#Some.^match#None.^if.^t_B<- ~ {t_B <- oget h1mDDH.[(None, None, x.`3, x.`4, x.`5)];} 
  ]

  proc send_msg3 [
    ^match#Some.^match#Pending.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h1mDDH)
    ^match#Some.^match#Pending.^if.^h1m<- ~ {h1mDDH.[(None, None, x.`3, x.`4, x.`5)] <- ts;}
    ^match#Some.^match#Pending.^t_A<- ~ {t_A <- oget h1mDDH.[(None, None, x.`3, x.`4, x.`5)];}
  ]

  proc c_rev_skey [
    ^match#Some.^match#Accepted.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2mDDH)
    ^match#Some.^match#Accepted.^if.^if.^h2m<- ~ {h2mDDH.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
    ^match#Some.^match#Accepted.^if.^k<- ~ {k <- h2mDDH.[(None, None, x.`3, x.`4, x.`5)];}
  ]

  proc s_rev_skey [
    ^match#Some.^match#Accepted.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2mDDH)
    ^match#Some.^match#Accepted.^if.^if.^h2m<- ~ {h2mDDH.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
    ^match#Some.^match#Accepted.^if.^k<- ~ {k <- h2mDDH.[(None, None, x.`3, x.`4, x.`5)];} 
  ]

  proc c_test [
    ^if.^match#Some.^match#Accepted.^if.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2mDDH)
    ^if.^match#Some.^match#Accepted.^if.^if.^if.^h2m<- ~ {h2mDDH.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- ~ {k <- h2mDDH.[(None, None, x.`3, x.`4, x.`5)];} 
    ^if.^match#Some.^match#Accepted.^if.^if?^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2mDDH)
    ^if.^match#Some.^match#Accepted.^if.^if?^if.^h2m<- ~ {h2mDDH.[(None, None, x.`3, x.`4, x.`5)] <- ks2;}
    ^if.^match#Some.^match#Accepted.^if.^if?^k<- ~ {k <- h2mDDH.[(None, None, x.`3, x.`4, x.`5)];}
  ]

  proc s_test [
    ^if.^match#Some.^match#Accepted.^if.^if.^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2mDDH)
    ^if.^match#Some.^match#Accepted.^if.^if.^if.^h2m<- ~ {h2mDDH.[(None, None, x.`3, x.`4, x.`5)] <- ks;}
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- ~ {k <- h2mDDH.[(None, None, x.`3, x.`4, x.`5)];} 
    ^if.^match#Some.^match#Accepted.^if.^if?^if ~ ((None, None, x.`3, x.`4, x.`5) \notin h2mDDH)
    ^if.^match#Some.^match#Accepted.^if.^if?^if.^h2m<- ~ {h2mDDH.[(None, None, x.`3, x.`4, x.`5)] <- ks2;}
    ^if.^match#Some.^match#Accepted.^if.^if?^k<- ~ {k <- h2mDDH.[(None, None, x.`3, x.`4, x.`5)];}
  ]

}.

print GameDDH.
