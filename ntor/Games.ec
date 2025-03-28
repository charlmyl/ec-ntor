(* Intermediate Games *)
require import AllCore FMap FSet Distr NTOR.
import GAKEc HROc.

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

(* Step0 inlining everything and adding bad event *)
module Game0 : GAKE_out_i = {
  (* This is not aligned with the sequence above *)
  var b0 : bool 

  var hm : (pkey * pkey * s_id * pkey * pkey, tag * key) fmap

  var servers : (s_id, server_state) fmap

  var c_smap : (int, pr_st_client instance_state) fmap
  var s_smap : (s_id * int, pr_st_server instance_state) fmap
  
  var tested : bool
  
  var kp_set : ((pkey * skey)) fset
  var bad : bool


  proc init_mem(b: bool) : unit = {
    b0 <- b;
    hm <- empty;
    servers <- empty;
    c_smap <- empty;
    s_smap <- empty;
    tested <- false;
    kp_set <- fset0;
    bad <- false;
  }
  
  (* random oracle *)
  proc h(x: pkey * pkey * s_id * pkey * pkey) : tag * key = {
    var tk;

    tk <$ dtag `*` dkey;
    if (x \notin hm) {
      hm.[x] <- tk;
    }
    
    return oget hm.[x];
  }

  (* server management *)
  proc init_s(b: s_id) : pkey option = {
    var kp;

    if (b \notin servers) {
      kp <$ dkp;
      bad <- bad \/ kp \in kp_set;
      kp_set <- kp_set `|` fset1 kp;
      servers.[b] <- Honest kp;
    }
    return omap get_pkey servers.[b];
  }
  
  proc set_cert(b: s_id, pk: pkey) : unit option = {
    var r <- None;

    if (b \notin servers) {
      servers.[b] <- Dishonest pk;
      r <- Some ();
    }
    return r;
  }

  proc send_msg1(i: int, m1: s_id) : pkey option = {
    var st, pk_b, kp;
    var r <- None;

    st <- c_smap.[i];
    if (m1 \in servers) {
      pk_b <- get_pkey (oget servers.[m1]);
      match st with
      | None => {
          kp <$ dkp;
          bad <- bad \/ kp \in kp_set;
          kp_set <- kp_set `|` fset1 kp;
          c_smap.[i] <- Pending (m1, pk_b, fst kp, snd kp) (fst kp) (false, false, false);
          r <- Some (fst kp);
        }
      | Some st => {
          match st with
          | Pending st pt ir => c_smap.[i] <- Aborted (Some st) (Some (pt, None)) ir;
          | Accepted _ _ _ _ => { }
          | Aborted _ _ _ => { }
          end;
        }
      end;
    }
    return r;
  }

  proc send_msg2(b: s_id, j: int, m2: pkey) : (pkey * tag) option = {
    var sko, kp, t_B, sk;
    var r <- None;

    sko <- obind get_skey servers.[b];
    if (sko is Some sk_b) (* Server was initialised as honest *) {
      match s_smap.[b, j] with
      | None => {
          kp <$ dkp;
          bad <- bad \/ kp \in kp_set;
          kp_set <- kp_set `|` fset1 kp;
          (t_B, sk) <@ h(m2 ^ kp.`2, m2 ^ sk_b, b, m2, kp.`1);
          s_smap.[(b, j)] <- Accepted (b, sk_b, Some kp.`2) (m2, Some (kp.`1, t_B)) sk (false, false, false);
          r <- Some (kp.`1, t_B);
        }
      | Some st => { (* only completed sessions would be stored, and those can't be aborted; do nothing *) }
      end;
    }

    return r;
  }

  proc send_msg3(i: int, m3: pkey * tag) : unit option = {
    var b, pk_b, pk_ce, sk_ce, t_A, sk;
    var r <- None;

    match c_smap.[i] with
    | None => { } (* Abort? *)
    | Some _ => {
        match oget c_smap.[i] with
        | Pending st pt ir => {
            (b, pk_b, pk_ce, sk_ce) <- st;
            (t_A, sk) <@ h(m3.`1 ^ sk_ce, pk_b ^ sk_ce, b, pk_ce, m3.`1);
            if (t_A = m3.`2) {
              c_smap.[i] <- Accepted st (pt, Some m3) sk ir;
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
    | Some _ => {
        (* only accepted client instances that are not tested and 
           that not only have tested partners can be sesskey revealed *)
        if (oget c_smap.[i] is Accepted st' t' k' ir') {
          if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_c t' s_smap = Some false)) {
            k <- Some k';
            c_smap.[i] <- set_ir_sess (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }

  proc s_rev_skey(b: s_id, j: int) : key option = {
    var k <- None;

    match s_smap.[(b, j)] with
    | None => { }
    | Some _ => {
        (* only accepted server instances that are not tested and 
           that not only have tested partners can be sesskey revealed *)
        if (oget s_smap.[b, j] is Accepted st' t' k' ir') {
          if (!(get_ir_test (oget s_smap.[b, j]) \/ untested_partner_s t' c_smap = Some false)) {
            k <- Some k';
            s_smap.[(b, j)] <- set_ir_sess (Accepted st' t' k' ir');
          }
        }
      }
    end;
    return k;
  }

  proc rev_ltkey(b: s_id) : skey option = {
    var ltk <- None;

    match servers.[b] with
    | None => { }
    | Some _ => {
        (* a server can be ltkey revealed if no instance of it is ephkey revealed 
           in case that instance or all its partners are tested *) 
        if (oget servers.[b] is Honest kp) {
          if (forall j,
                (b, j) \in s_smap (* just checking instances of b *)
                => !(   (   get_ir_test (oget s_smap.[b, j])
                            (* This is always OK (get_trace always Some on server side *)
                         \/ untested_partner_s (oget (get_trace (oget s_smap.[b, j]))) c_smap = Some false)
                     /\ get_ir_eph (oget s_smap.[b,j]))) {
            ltk <- Some kp.`2; 
            servers.[b] <- Corrupt kp; 
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
    | Some _ => {
        match oget c_smap.[i] with
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

  proc s_rev_ephkey(b: s_id, j: int) : skey option = {
    var ek <- None;

    match s_smap.[b, j] with
    | None => { }
    | Some _ => {
        (* only accepted server instances that are not ltkey revealed in case they 
           or all partners are tested can be ephkey revealed *)
        if (oget s_smap.[b, j] is Accepted st t k ir) { (* No Pending on Server side *)
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

    if (!tested) {
      match c_smap.[i] with
      | None => { }
      | Some _ => {
          (* only accepted client instances that are not sesskey revealed, not ephkey revealed 
             and not all partner instances are unfresh can be tested *)
          if (oget c_smap.[i] is Accepted st' t' k' ir') {
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
              tested <- true;
           }
          }
        }
      end;
    }
    return k;
  }

  proc s_test(b: s_id, j: int) : key option = {
    var ks;
    var k <- None;

    if (!tested) {
      match s_smap.[(b, j)] with
      | None => { }
      | Some _ => {
          (* only accepted server instances that are not sesskey revealed, not trivially broken
             and not all partner instances are unfresh can be tested *)
          if (oget s_smap.[b, j] is Accepted st' t' k' ir') {
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
              tested <- true;
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
  var h1m : (pkey * pkey * s_id * pkey * pkey, tag) fmap
  var h2m : (pkey * pkey * s_id * pkey * pkey, key) fmap
  var hq : (pkey * pkey * s_id * pkey * pkey) fset
  var tq : (pkey * pkey * s_id * pkey * pkey) option
  var badq : bool

  proc init_mem [
    -1 + { h1m <- empty; h2m <- empty; hq <- fset0; tq <- None; badq <- false; }
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
    var x : pkey * pkey * s_id * pkey * pkey
    ^match#Some.^match#None.^if.2 ~ { x <- (m2 ^ kp.`2, m2 ^ sk_b, b, m2, kp.`1);
                                      ts <$ dtag;
                                      if (x \notin h1m) {h1m.[x] <- ts;} 
                                      t_B <- oget h1m.[x];
                                      ks <$ dkey;
                                      if (x \notin h2m) {h2m.[x] <- ks;} 
                                      sk <- oget h2m.[x];}
  ]

  proc send_msg3 [
    var ts : tag
    var ks : key
    var x : pkey * pkey * s_id * pkey * pkey
    ^match#Some.^match#Pending.2 ~ { x <- (m3.`1 ^ sk_ce, pk_b ^ sk_ce, b, pk_ce, m3.`1);
                                     ts <$ dtag;
                                     if (x \notin h1m) {h1m.[x] <- ts;} 
                                     t_A <- oget h1m.[x];
                                     ks <$ dkey;
                                     if (x \notin h2m) {h2m.[x] <- ks;} 
                                     sk <- oget h2m.[x];}

  ]
  


  proc c_test [
    var x : pkey * pkey * s_id * pkey * pkey
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- + ^ {x <- ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
    ^if.^match#Some.^match#Accepted.^if.^if?^ks<$ + ^ {x <- ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
  ]

  proc s_test [
    var x : pkey * pkey * s_id * pkey * pkey
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- + ^ {x <- (t'.`1 ^ (oget st'.`3), t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
    ^if.^match#Some.^match#Accepted.^if.^if?^ks<$ + ^ {x <- (t'.`1 ^ (oget st'.`3), t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1); tq <- Some x; badq <- badq \/ (oget tq \in hq);}
  ]
}.

print Game2. 

(* Step3: Replacing key computation on real side with sampling *)
module Game3 = Game2 with {
  proc c_test [
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- ~ {ks <$ dkey; k <- Some ks;}
    ^if.^match#Some.^match#Accepted.^if.^if.^c_smap<- ~ {c_smap.[i] <- set_ir_test (Accepted st' t' ks ir');}
  ]

  proc s_test [
    ^if.^match#Some.^match#Accepted.^if.^if.^k<- ~ {ks <$ dkey; k <- Some ks;}
    ^if.^match#Some.^match#Accepted.^if.^if.^s_smap<- ~ {s_smap.[(b, j)] <- set_ir_test (Accepted st' t' ks ir');}
  ]
}.

print Game3.

(* TO DO : Fix following game definitions!

module Game2 = Game1 with {
  var hq : (pkey * pkey * s_id * pkey * pkey) fset
  var tq : (pkey * pkey * s_id * pkey * pkey) option
  var badq : bool

  proc init_mem [
    -1 + { hq <- fset0; tq <- None; badq <- false;}
  ]

  proc h [
    1 + ^ {hq <- hq `|` fset1 x; badq <- (tq <> None /\ oget tq \in hq);}
  ]

  proc c_test [
    ^if.^match#Some.^match#Accepted.^if.^tested<- + {tq <- Some ((oget t'.`2).`1 ^ st'.`4, st'.`2 ^ st'.`4, st'.`1, st'.`3, (oget t'.`2).`1); badq <- (oget tq \in hq);}
  ]

  proc s_test [
    ^if.^match#Some.^match#Accepted.^if.^tested<- + {tq <- Some  (t'.`1 ^ (oget st'.`3), t'.`1 ^ st'.`2, st'.`1, t'.`1, (oget t'.`2).`1); badq <- (oget tq \in hq);}
  ]
}.

print Game2.


module Game3 = Game2 with {
  var hq : (pkey * pkey * s_id * pkey * pkey) fset
  var tq : (pkey * pkey * s_id * pkey * pkey) option
  var badq : bool

  proc init_mem [
    -1 + { hq <- fset0; tq <- None; badq <- false;}
  ]

  proc h [
    1 + ^ {hq <- hq `|` fset1 x; badq <- (tq <> None /\ oget tq \in hq);}
  ]

  proc c_test [
    ^if.^match#Some.^match#Accepted.^if.^x<- + {tq <- Some x; badq <- (oget tq \in hq);}
  ]

  proc s_test [
    ^if.^match#Some.^match#Accepted.^if.^x<- + {tq <- Some x; badq <- (oget tq \in hq);}
  ]
}.

print Game3.


module Game4 = Game3 with {

  proc c_test [
    ^if.^match#Some.^match#Accepted.^if.^if -
    ^if.^match#Some.^match#Accepted.^if.^k<- ~ {k <- Some ks;}
  ]

  proc s_test [
    ^if.^match#Some.^match#Accepted.^if.^if -
    ^if.^match#Some.^match#Accepted.^if.^k<- ~ {k <- Some ks;}
  ]

}.

module Game5 : GAKE_out_i = {
  var hm : (pkey * pkey * s_id * pkey * pkey, tag * key) fmap

  var servers : (s_id, server_state) fmap

  var c_smap : (int, pr_st_client instance_state) fmap
  var s_smap : (s_id * int, pr_st_server instance_state) fmap
  
  var tested : bool
  
  var kp_set : ((pkey * skey)) fset
  var bad : bool


  proc init_mem() : unit = {
    hm <- empty;
    servers <- empty;
    c_smap <- empty;
    s_smap <- empty;
    tested <- false;
    kp_set <- fset0;
    bad <- false;
  }
  
  (* random oracle *)
  proc h(x: pkey * pkey * s_id * pkey * pkey) : tag * key = {
    var tk;

    tk <$ dtag `*` dkey;
    if (x \notin hm) {
      hm.[x] <- tk;
    }
    
    return oget hm.[x];
  }

  (* server management *)
  proc init_s(b: s_id) : pkey option = {
    var kp;

    if (b \notin servers) {
      kp <$ dkp;
      bad <- bad \/ kp \in kp_set;
      if (!bad) {
        kp_set <- kp_set `|` fset1 kp;
        servers.[b] <- Honest kp;
      }
    }
    return omap get_pkey servers.[b];
  }
  
  proc set_cert(b: s_id, pk: pkey) : unit option = {
    var r <- None;

    if (b \notin servers) {
      servers.[b] <- Dishonest pk;
      r <- Some ();
    }
    return r;
  }

  proc send_msg1(i: int, m1: s_id) : pkey option = {
    var st, pk_b, kp;
    var r <- None;

    st <- c_smap.[i];
    if (m1 \in servers) {
      pk_b <- get_pkey (oget servers.[m1]);
      match st with
      | None => {
          kp <$ dkp;
          bad <- bad \/ kp \in kp_set;
          if (!bad) {
            kp_set <- kp_set `|` fset1 kp;
            c_smap.[i] <- Pending (m1, pk_b, fst kp, snd kp) (fst kp) (false, false, false);
            r <- Some (fst kp);
          }
        }
      | Some st => {
          match st with
          | Pending st pt ir => c_smap.[i] <- Aborted (Some st) (Some (pt, None)) ir;
          | Accepted _ _ _ _ => { }
          | Aborted _ _ _ => { }
          end;
        }
      end;
    }
    return r;
  }

  proc send_msg2(b: s_id, j: int, m2: pkey) : (pkey * tag) option = {
    var sko, kp, t_B, sk;
    var r <- None;

    sko <- obind get_skey servers.[b];
    if (sko is Some sk_b) (* Server was initialised as honest *) {
      match s_smap.[b, j] with
      | None => {
          kp <$ dkp;
          bad <- bad \/ kp \in kp_set;
          if (!bad) {
            kp_set <- kp_set `|` fset1 kp;
            (t_B, sk) <@ h(m2 ^ kp.`2, m2 ^ sk_b, b, m2, kp.`1);
            s_smap.[(b, j)] <- Accepted (b, sk_b, Some kp.`2) (m2, Some (kp.`1, t_B)) sk (false, false, false);
            r <- Some (kp.`1, t_B);
          }
        }
      | Some st => { (* only completed sessions would be stored, and those can't be aborted; do nothing *) }
      end;
    }

    return r;
  }

  proc send_msg3(i: int, m3: pkey * tag) : unit option = {
    var b, pk_b, pk_ce, sk_ce, t_A, sk;
    var r <- None;

    match c_smap.[i] with
    | None => { } (* Abort? *)
    | Some _ => {
        match oget c_smap.[i] with
        | Pending st pt ir => {
            (b, pk_b, pk_ce, sk_ce) <- st;
            (t_A, sk) <@ h(m3.`1 ^ sk_ce, pk_b ^ sk_ce, b, pk_ce, m3.`1);
            if (t_A = m3.`2) {
              c_smap.[i] <- Accepted st (pt, Some m3) sk ir;
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
    | Some _ => {
        (* only accepted client instances that are not tested and 
           that not only have tested partners can be sesskey revealed *)
        if (oget c_smap.[i] is Accepted st' t' k' ir') {
          if (!(get_ir_test (oget c_smap.[i]) \/ untested_partner_c t' s_smap = Some false)) {
            k <- Some k';
            c_smap.[i] <- set_ir_sess (Accepted st' t' (oget k) ir');
          }
        }
      }
    end;
    return k;
  }

  proc s_rev_skey(b: s_id, j: int) : key option = {
    var k <- None;

    match s_smap.[(b, j)] with
    | None => { }
    | Some _ => {
        (* only accepted server instances that are not tested and 
           that not only have tested partners can be sesskey revealed *)
        if (oget s_smap.[b, j] is Accepted st' t' k' ir') {
          if (!(get_ir_test (oget s_smap.[b, j]) \/ untested_partner_s t' c_smap = Some false)) {
            k <- Some k';
            s_smap.[(b, j)] <- set_ir_sess (Accepted st' t' (oget k) ir');
          }
        }
      }
    end;
    return k;
  }

  proc rev_ltkey(b: s_id) : skey option = {
    var ltk <- None;

    match servers.[b] with
    | None => { }
    | Some _ => {
        (* a server can be ltkey revealed if no instance of it is ephkey revealed 
           in case that instance or all its partners are tested *) 
        if (oget servers.[b] is Honest kp) {
          if (forall j,
                (b, j) \in s_smap (* just checking instances of b *)
                => !(   (   get_ir_test (oget s_smap.[b, j])
                            (* This is always OK (get_trace always Some on server side *)
                         \/ untested_partner_s (oget (get_trace (oget s_smap.[b, j]))) c_smap = Some false)
                     /\ get_ir_eph (oget s_smap.[b,j]))) {
            ltk <- Some kp.`2; 
            servers.[b] <- Corrupt kp; 
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
    | Some _ => {
        match oget c_smap.[i] with
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

  proc s_rev_ephkey(b: s_id, j: int) : skey option = {
    var ek <- None;

    match s_smap.[b, j] with
    | None => { }
    | Some _ => {
        (* only accepted server instances that are not ltkey revealed in case they 
           or all partners are tested can be ephkey revealed *)
        if (oget s_smap.[b, j] is Accepted st t k ir) { (* No Pending on Server side *)
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
    var k <- None;
    var ks;

    if (!tested) {
      match c_smap.[i] with
      | None => { }
      | Some _ => {
          (* only accepted client instances that are not sesskey revealed, not ephkey revealed 
             and not all partner instances are unfresh can be tested *)
          if (oget c_smap.[i] is Accepted st' t' k' ir') {
            if (!(   get_ir_sess (oget c_smap.[i]) \/ get_ir_eph (oget c_smap.[i]) 
                  \/ fresh_partner_c t' s_smap servers = Some false)) {
              ks <$ dkey;
              k <- Some ks;
              c_smap.[i] <- set_ir_test (Accepted st' t' ks ir');
              tested <- true;
            }
          }
        }
      end;
    }
    return k;
  }

  proc s_test(b: s_id, j: int) : key option = {
    var k <- None;
    var ks;

    if (!tested) {
      match s_smap.[(b, j)] with
      | None => { }
      | Some _ => {
          (* only accepted server instances that are not sesskey revealed, not trivially broken
             and not all partner instances are unfresh can be tested *)
          if (oget s_smap.[b, j] is Accepted st' t' k' ir') {
            if (!(   get_ir_sess (oget s_smap.[b, j]) 
                  \/ (get_ir_eph (oget s_smap.[b, j]) /\ get_sr_ltk (oget servers.[b]))
                  \/ fresh_partner_s t' c_smap = Some false)) {
              ks <$ dkey;
              k <- Some ks;
              s_smap.[(b, j)] <- set_ir_test (Accepted st' t' ks ir');
              tested <- true;
            }
          }
        }
      end;
    }
    return k;
  }
}.


print Game4.
*)
