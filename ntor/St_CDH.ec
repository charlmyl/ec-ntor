require import AllCore Distr List FSet FMap.
require GAKE DiffieHellman.

clone DiffieHellman as DH.
import DH.DDH DH.G DH.GP DH.FD.

module type Oracle = {
  proc ddh(x y z : group) : bool
  proc gen1() : group
  proc gen2() : group
  proc corrupt1(i : int) : exp option
  proc corrupt2(j : int) : exp option
}.

module type Oracle_i = {
  include Oracle

  proc init_mem() : unit
}.

module St_CDH_O : Oracle_i = {
  var win : bool
  var n, m : int
  var cr1, cr2 : int fset
  var x_map : (int, exp) fmap
  var y_map : (int, exp) fmap

  proc init_mem() : unit = {
    win <- false;
    n <- 0;
    m <- 0;
    cr1 <- fset0;
    cr2 <- fset0;
    x_map <- empty;
    y_map <- empty;
  }

  proc ddh(x y z : group) : bool = {
    var r <- false;

    if (exists i, i \in x_map /\ x = g ^ (oget x_map.[i]) /\ z = y ^ (oget x_map.[i]) /\ i \notin cr1) {
      if (exists j, j \in y_map /\ y = g ^ (oget y_map.[j]) /\ j \notin cr2) {
         win <- true;
         r <- true;
      }
    } elif (exists j, j \in y_map /\ y = g ^ (oget y_map.[j]) /\ z = x ^ (oget y_map.[j])) {
         r <- true;
    }

    return r;
  }

  proc gen1() : group = {
    var x_n;

    n <- n + 1;
    x_n <$ dt;
    x_map.[n] <- x_n;

    return (g ^ x_n);
  }

  proc gen2() : group = {
    var y_m;

    m <- m + 1;
    y_m <$ dt;
    y_map.[m] <- y_m;

    return (g ^ y_m);
  }

  proc corrupt1(i : int) : exp option = {
    var r <- None;

    if (i \in x_map) {
      cr1 <- cr1 `|` fset1 i;
      r <- x_map.[i];
    }

    return r;
  }

  proc corrupt2(j : int) : exp option = {
    var r <- None;

    if (j \in y_map) {
      cr2 <- cr2 `|` fset1 j;
      r <- y_map.[j];
    }

    return r;
  }
}.

module type Adversary (O : Oracle) = {
  proc solve() : unit
}.

(*
module St_CDH (A : Adversary) (O : Oracle_i) = {
  proc main(): bool = {
    
    r <@ A.solve(O);
    return (r = g ^ (x * y));
  }
}.*)
