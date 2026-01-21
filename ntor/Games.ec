(* Intermediate Games *)
require import AllCore FMap FSet Distr.

require NTOR_nosid.
clone import NTOR_nosid as NTOR_nosid_c.
import NTORc GAKE_mod DH.G DH.GP DH.FD.


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
  
  var b_set, x_set, y_set, pk_set, m1_set, m2_set : pkey fset
  var bad1, bad2 : bool


  proc init_mem(b: bool) : unit = {
    b0 <- b;
    hm <- empty;
    servers <- empty;
    c_smap <- empty;
    s_smap <- empty;
    tested <- None;
    pk_set <- fset0;
    m1_set <- fset0;
    m2_set <- fset0;
    b_set <- fset0;
    x_set <- fset0;
    y_set <- fset0;
    bad1 <- false;
    bad2 <- false;
  }
  
  (* random oracle *)
  proc h(x: pkey * pkey * pkey * pkey * pkey) : tag * key = {
    var tk;

    tk <$ dtag `*` dkey;
    if (x \notin hm) {
      hm.[x] <- tk;
    }

    if (x.`3 \notin pk_set /\ x.`3 \notin b_set) {
      b_set <- b_set `|` fset1 x.`3;
    }
    if (x.`4 \notin m1_set /\ x.`4 \notin x_set) {
      x_set <- x_set `|` fset1 x.`4;
    }
    if (x.`5 \notin m2_set /\ x.`5 \notin y_set) {
      y_set <- y_set `|` fset1 x.`5;
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
      bad2 <- bad2 \/ pk \in b_set;
      bad1 <- bad1 \/ pk \in pk_set \/ pk \in m1_set \/ pk \in m2_set;
      pk_set <- pk_set `|` fset1 pk;
      servers.[pk] <- Honest_mod sk;
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
          bad2 <- bad2 \/ pk \in x_set;
          bad1 <- bad1 \/ pk \in pk_set \/ pk \in m1_set \/ pk \in m2_set;
          c_smap.[i] <- Pending_mod (m1, sk) (m1, pk) (false, false, false);
          m1_set <- m1_set `|` fset1 pk;
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
          bad2 <- bad2 \/ pk \in y_set;
          bad1 <- bad1 \/ pk \in pk_set \/ pk \in m1_set \/ pk \in m2_set;
          m2_set <- m2_set `|` fset1 pk;
          (t_B, key) <@ h(m2 ^ sk, m2 ^ sk_b, g ^ sk_b, m2, pk);
          s_smap.[(b, j)] <- Accepted_mod (sk_b, Some sk) ((b, m2), Some (pk, t_B)) key (false, false, false);
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
        | Pending_mod st pt ir => {
            (b, sk_ce) <- st;
            (t_A, key) <@ h(m3.`1 ^ sk_ce, b ^ sk_ce, b, g ^ sk_ce, m3.`1);
            if (t_A = m3.`2) {
              c_smap.[i] <- Accepted_mod st (pt, Some m3) key ir;
              r <- Some ();
            } else {
              c_smap.[i] <- Aborted_mod (Some st) (Some (pt, Some m3)) ir;
            }
          }
        | Accepted_mod _ _ _ _ => { }
        | Aborted_mod _ _ _ => { }
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
        if (st is Accepted_mod st' t' k' ir') {
          if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_c t' s_smap = Some false)) {
            k <- Some k';
            c_smap.[i] <- set_ir_sess (Accepted_mod st' t' k' ir');
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
        if (st is Accepted_mod st' t' k' ir') {
          if (!(get_ir_test (oget s_smap.[b, j]) \/ untested_partner_s t' c_smap = Some false)) {
            k <- Some k';
            s_smap.[(b, j)] <- set_ir_sess (Accepted_mod st' t' k' ir');
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
        if (st is Honest_mod sk) {
          if (forall j,
                (b, j) \in s_smap (* just checking instances of b *)
                => !(   (   get_ir_test (oget s_smap.[b, j])
                            (* This is always OK (get_trace always Some on server side *)
                         \/ untested_partner_s (oget (get_trace (oget s_smap.[b, j]))) c_smap = Some false)
                     /\ get_ir_eph (oget s_smap.[b,j]))
                /\ !tested_pot_partner_c b c_smap s_smap) {
            ltk <- Some sk; 
            servers.[b] <- Corrupt_mod sk; 
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
        | Pending_mod st pk_e ir => {
            if (untested_origins_c (pk_e, None) s_smap <> Some false) {
              ek <- Some (st.`2);
              c_smap.[i] <- set_ir_eph (Pending_mod st pk_e ir);
            }
          }
          (* accepted client instamces can only be ephkey revealed when not tested and 
             if not all partners are tested *)
        | Accepted_mod st t k ir => {
            if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_c t s_smap = Some false)) {
              ek <- Some (st.`2);
              c_smap.[i] <- set_ir_eph (Accepted_mod st t k ir);
            }
          }
        | Aborted_mod _ _ _ => {  }
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
        if (st is Accepted_mod st t k ir) { (* No Pending on Server side *)
          if (!((   get_ir_test (oget s_smap.[b, j])
                 \/ untested_partner_s t c_smap = Some false)
                /\ get_sr_ltk (oget servers.[b]))) {
            ek <- Some (oget st.`2);
            s_smap.[(b, j)] <- set_ir_eph (Accepted_mod st t k ir);
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
          if (st is Accepted_mod st' t' k' ir') {
            if (!(   get_ir_sess (oget c_smap.[i]) \/ get_ir_eph (oget c_smap.[i]) 
                  \/ (fresh_partner_c t' s_smap servers = Some false)
                  \/ (card (get_partners_c t' s_smap) = 0 /\ get_sr_ltk (oget servers.[t'.`1.`1])))) {
              if (b0 = false) {
                k <- Some k';
                c_smap.[i] <- set_ir_test (Accepted_mod st' t' k' ir');
              } else {
                ks <$ dkey;
                k <- Some ks;
                c_smap.[i] <- set_ir_test (Accepted_mod st' t' k' ir');
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
          if (st is Accepted_mod st' t' k' ir') {
            if (!(   get_ir_sess (oget s_smap.[b, j]) 
                  \/ (get_ir_eph (oget s_smap.[b, j]) /\ get_sr_ltk (oget servers.[b]))
                  \/ fresh_partner_s t' c_smap <> Some true)) {
              if (b0 = false) {
                k <- Some k';
                s_smap.[(b, j)] <- set_ir_test (Accepted_mod st' t' k' ir');
              } else {
                ks <$ dkey;
                k <- Some ks;
                s_smap.[(b, j)] <- set_ir_test (Accepted_mod st' t' k' ir');
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
  proc h [
     1 + ^ {tk <- (witness, witness);}
     [1 - ^if{3} & + 1] + ^ (!bad1)
     ^if{1} + {tk <- oget hm.[x];}
  ] res ~ (tk)

  proc init_s [
    [^r<- - ^if] + (!bad1)
    [^if.^pk_set<- - ^r<-] + (!bad1)
  ]

  proc send_msg1 [
    [^r<- - ^if] + (!bad1)
    [^if.^match#None.^bad1<- - ^c_smap<-] + (!bad1)
  ]

  proc send_msg2 [
    [^r<- - ^match] + (!bad1)
    [^match#Some.^match#None.^bad1<- - ^r<-] + (!bad1)
  ]

  proc send_msg3 [
    [^r<- - ^match] + (!bad1)
  ]

  proc c_rev_skey [
    [^k<- - ^match] + (!bad1)
  ]

  proc s_rev_skey [
    [^k<- - ^match] + (!bad1)
  ]

  proc rev_ltkey [
    [^ltk<- - ^match] + (!bad1)
  ]

  proc c_rev_ephkey [
    [^ek<- - ^match] + (!bad1)
  ]

  proc s_rev_ephkey [
    [^ek<- - ^match] + (!bad1)
  ]

  proc c_test [
    [^k<- - ^if] + (!bad1)
  ]

  proc s_test [
    [^k<- - ^if] + (!bad1)
  ]
}.

print Game1.

module Game2 = Game1 with {
  proc h [
    ^if ~ (!bad1 /\ !bad2)
  ]

  proc init_s [
    ^if ~ (!bad1 /\ !bad2)
    ^if.^if.^if ~ (!bad1 /\ !bad2)
  ]

  proc send_msg1 [
    ^if ~ (!bad1 /\ !bad2)
    ^if.^if.^match#None.^if ~ (!bad1 /\ !bad2)
  ]

  proc send_msg2 [
    ^if ~ (!bad1 /\ !bad2)
    ^if.^match#Some.^match#None.^if ~ (!bad1 /\ !bad2)
  ]

  proc send_msg3 [
    ^if ~ (!bad1 /\ !bad2)
  ]

  proc c_rev_skey [
    ^if ~ (!bad1 /\ !bad2)
  ]

  proc s_rev_skey [
    ^if ~ (!bad1 /\ !bad2)
  ]

  proc rev_ltkey [
    ^if ~ (!bad1 /\ !bad2)
  ]

  proc c_rev_ephkey [
    ^if ~ (!bad1 /\ !bad2)
  ]

  proc s_rev_ephkey [
    ^if ~ (!bad1 /\ !bad2)
  ]

  proc c_test [
    ^if ~ (!bad1 /\ !bad2)
  ]

  proc s_test [
    ^if ~ (!bad1 /\ !bad2)
  ]
}.

print Game2.

(* Step2: Splitting the random oracle and tracking bad event of overlap between RO queries and test query *)
module Game3 = Game2 with {
  var h1m : (pkey * pkey * pkey * pkey * pkey, tag) fmap
  var h2m : (pkey * pkey * pkey * pkey * pkey, key) fmap
  var hq : (pkey * pkey * pkey * pkey * pkey) fset
  var tq : (pkey * pkey * pkey * pkey * pkey) option
  var badq : bool

  proc init_mem [
    -1 + { h1m <- empty; h2m <- empty; hq <- fset0; tq <- None; badq <- false;}
  ]

  proc h [
    var t : tag
    var k : key
    ^if.^tk<- ~ {tk <- ((oget h1m.[x], oget h2m.[x]));}
    ^if.^tk<$ ~ {t <$ dtag; if (x \notin h1m) {h1m.[x] <- t;} k <$ dkey; if (x \notin h2m) {h2m.[x] <- k;} }
    ^if.^if -
    ^if.^tk<$ + ^ {hq <- hq `|` fset1 x; badq <- badq \/ (tq <> None /\ oget tq \in hq);}
  ]

  proc send_msg2 [
    var ts : tag
    var ks : key
    var x : pkey * pkey * pkey * pkey * pkey
    ^if.^match#Some.^match#None.^if.2 ~ { x <- (m2 ^ sk, m2 ^ sk_b, g ^ sk_b, m2, pk);
                                      ts <$ dtag;
                                      if (x \notin h1m) {h1m.[x] <- ts;} 
                                      t_B <- oget h1m.[x];
                                      ks <$ dkey;
                                      if (x \notin h2m) {h2m.[x] <- ks;} 
                                      key <- oget h2m.[x]; 
                                      if (m2 \notin m1_set /\ m2 \notin x_set) {x_set <- x_set `|` fset1 m2;}}
  ]

  proc send_msg3 [
    var ts : tag
    var ks : key
    var x : pkey * pkey * pkey * pkey * pkey
    ^if.^match#Some.^match#Pending_mod.2 ~ { x <- (m3.`1 ^ sk_ce, b ^ sk_ce, b, g ^ sk_ce, m3.`1);
                                     ts <$ dtag;
                                     if (x \notin h1m) {h1m.[x] <- ts;} 
                                     t_A <- oget h1m.[x];
                                     ks <$ dkey;
                                     if (x \notin h2m) {h2m.[x] <- ks;} 
                                     key <- oget h2m.[x]; 
                                     if (g ^ sk_ce \notin m1_set /\ g ^ sk_ce \notin x_set) {x_set <- x_set `|` fset1 (g ^ sk_ce);}
                                     if (m3.`1 \notin m2_set /\ m3.`1 \notin y_set) {y_set <- y_set `|` fset1 m3.`1;}}

  ]

  proc c_test [
    var x : pkey * pkey * pkey * pkey * pkey
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- + ^ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^ks<$ + ^ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
  ]

  proc s_test [
    var x : pkey * pkey * pkey * pkey * pkey
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- + ^ {x <- ((t'.`1).`2 ^ (oget st'.`2), (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, g ^ (oget st'.`2)); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^ks<$ + ^ {x <- ((t'.`1).`2 ^ (oget st'.`2), (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, g ^ (oget st'.`2)); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
  ]
}.

print Game3. 

(* Step3: Moving the sampling of keys *)
module Game4 = Game3 with {
  var test_ephrev_s : bool
  var test_ltkrev : bool

  proc init_mem [
    -1 + { test_ephrev_s <- false; test_ltkrev <- false; }
  ]

  proc send_msg2 [
    ^if.^match#Some.^match#None.^if.^ks<$ ~ {key <- witness;}
    [^if.^match#Some.^match#None.^if.^if{2} - ^key<-] -
  ]

  proc send_msg3 [
    ^if.^match#Some.^match#Pending_mod.^ks<$ ~ {key <- witness;}
    ^if.^match#Some.^match#Pending_mod.^if{2} ~ (pt.`2 \notin m1_set /\ pt.`2 \notin x_set)
    ^if.^match#Some.^match#Pending_mod.^if{2}.^x_set<- ~ {x_set <- x_set `|` fset1 pt.`2;}
    [^if.^match#Some.^match#Pending_mod.^if{2} - ^key<-] -
  ]

  proc c_rev_skey [
    var ks : key
    var x : pkey * pkey * pkey * pkey * pkey
    ^if.^match#Some.^match#Accepted_mod.^if.^k<- ~ {x <- ((oget t'.`2).`1 ^ st'.`2, st'.`1 ^ st'.`2, st'.`1, g ^ st'.`2, (oget t'.`2).`1); 
                                            ks <$ dkey;
                                            if (x \notin h2m) {h2m.[x] <- ks;} 
                                            k <- h2m.[x];}
  ]

  proc s_rev_skey [
    var ks : key
    var x : pkey * pkey * pkey * pkey * pkey
    ^if.^match#Some.^match#Accepted_mod.^if.^k<- ~ {x <- ((t'.`1).`2 ^ (oget st'.`2), (t'.`1).`2 ^ st'.`1, g ^ st'.`1, (t'.`1).`2, g ^ (oget st'.`2));
                                            ks <$ dkey;
                                            if (x \notin h2m) {h2m.[x] <- ks;} 
                                            k <- h2m.[x];}
  ]

  proc rev_ltkey [
    ^if.^match#Some.^match#Honest_mod.^if.^ltk<- + ^ {if (exists (j : int), (b, j) \in s_smap => get_ir_test (oget s_smap.[b, j]) \/
                                                             (untested_partner_s (oget (get_trace (oget s_smap.[b, j]))) c_smap = Some false)) {test_ltkrev <- test_ltkrev \/ true;}}

  ]

  proc s_rev_ephkey [
    ^if.^match#Some.^match#Accepted_mod.^if.^ek<- + ^ {if (ir.`3 \/ untested_partner_s t c_smap = Some false) {test_ephrev_s <- test_ephrev_s \/ true;}}
  ]

  proc c_test [
    var ks2 : key
    var p : (pkey * int)
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^x<- + ^ {p <- pick (get_fresh_partners_c t' s_smap servers); 
                                                  test_ephrev_s <- (test_ephrev_s \/ get_ir_eph (oget s_smap.[p]));
                                                    test_ltkrev <- (test_ltkrev \/ get_sr_ltk (oget servers.[t'.`1.`1]));}
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- ~ {ks <$ dkey; if (x \notin h2m) {h2m.[x] <- ks;} k <- h2m.[x];}
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^x<- + ^ {p <- pick (get_fresh_partners_c t' s_smap servers); 
                                                  test_ephrev_s <- (test_ephrev_s \/ get_ir_eph (oget s_smap.[p]));
                                                    test_ltkrev <- (test_ltkrev \/ get_sr_ltk (oget servers.[t'.`1.`1]));}
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^ks<$ + ^ {ks2 <$ dkey; if (x \notin h2m) {h2m.[x] <- ks2;} k <- h2m.[x];}
  ]

  proc s_test [
    var ks2 : key
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^x<- + ^ {test_ephrev_s <- test_ephrev_s \/ ir'.`1; test_ltkrev <- (test_ltkrev \/ get_sr_ltk (oget servers.[b]));}
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^k<- ~ {ks <$ dkey; if (x \notin h2m) {h2m.[x] <- ks;} k <- h2m.[x];}
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^x<- + ^ {test_ephrev_s <- test_ephrev_s \/ ir'.`1; test_ltkrev <- (test_ltkrev \/ get_sr_ltk (oget servers.[b]));}
    ^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^ks<$ + ^ {ks2 <$ dkey; if (x \notin h2m) {h2m.[x] <- ks2;} k <- h2m.[x];}
  ]
}.

print Game4.

module Game4Ltk = Game4 with {
  proc h [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
  ]

  proc init_s [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
  ]

  proc send_msg1 [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
  ]

  proc send_msg2 [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
  ]

  proc send_msg3 [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
  ]

  proc c_rev_skey [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
  ]

  proc s_rev_skey [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
  ]

  proc rev_ltkey [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
    [^if.^match#Some.^match#Honest_mod.^if.^if - ^servers<-] + (!test_ltkrev)
  ]

  proc c_rev_ephkey [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
  ]

  proc s_rev_ephkey [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
  ]

  proc c_test [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
    [^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^test_ltkrev<- - ^c_smap<-] + (!test_ltkrev)
    [^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^test_ltkrev<- - ^c_smap<-] + (!test_ltkrev)
    
  ]

  proc s_test [
    ^if ~ (!bad1 /\ !bad2 /\ !test_ltkrev)
    [^if.^if.^match#Some.^match#Accepted_mod.^if.^if.^test_ltkrev<- - ^s_smap<-] + (!test_ltkrev)
    [^if.^if.^match#Some.^match#Accepted_mod.^if.^if?^test_ltkrev<- - ^s_smap<-] + (!test_ltkrev)
  ]
}.

print Game4Ltk.
