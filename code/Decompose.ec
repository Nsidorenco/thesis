(* Formalization of MPC Phi decomposition *)
require import AllCore Distr SmtMap List.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

type phi = (int -> int).

type input = int.
type output = int.
type view = int list.

type input_wires = [
    UNARY of int
  | BINARY of (int * int)
].

type gate = [
  | ADDC of (int * (int -> int))
  | MULTC of (int * (int -> int))
  | MULT of (int * int)
  | ADD of (int * int)
].

type circuit = gate list.
type state = int list.
(* type input_map = (int, input_wires) fmap. *)

op plus_gate (x y : int) = x + y.
op mult_gate (x y : int) = x * y.

op eval_gate (h : input, g : gate, s : state) : output =
with g = MULT inputs => let (i, j) = inputs in
                        let x = (nth 0 s i) in
                        let y = (nth 0 s j) in x * y
with g = ADD inputs =>  let (i, j) = inputs in
                        let x = (nth 0 s i) in
                        let y = (nth 0 s j) in x + y
with g = ADDC inputs => let (i, f) = inputs in
                        let x = (nth 0 s i) in f x
with g = MULTC inputs => let (i, f) = inputs in
                         let x = (nth 0 s i) in f x.

(* Circuit example: *)
(* x *)
(* | \*)
(* +2 \ *)
(* |  / *)
(* | / *)
(* * *)

const circuit_ex = [ADDC (0, fun x => 2 + x); MULT(0,1)].
const s' : state = [10].

op eval_circuit(x : input, c : circuit, s : state) : output =
    with c = [] => last 0 s
    with c = g :: gs => let r = eval_gate x g s in eval_circuit x gs (rcons s r).

lemma circuit_ex_test : (eval_circuit 10 circuit_ex s') = 120 by trivial.

module Tester = {
  proc main(x : input, c : circuit, s : state) = {
    return eval_circuit x c s;
  }
}.

lemma test &m:
    Pr[Tester.main(10, circuit_ex, s') @ &m : res = 120] = 1%r.
proof. byphoare(: x = 10 /\ c = circuit_ex /\ s = s' ==> _)=>//.
proc. skip. progress. qed.

(** Phi protocol **)

(* define decomposed circuit function *)
op phi_decomp (h : input, g : gate, p : int, w : state list) : output =
with g = ADDC inputs =>
    let (i, f) = inputs in
    let state = (nth s' w (p - 1)) in
    let x = (nth 0 state i) in
    if p = 1 then f x else x
with g = MULTC inputs =>
    let (i, f) = inputs in
    let state = (nth s' w (p - 1)) in
    let x = (nth 0 state i) in f x
with g = ADD inputs =>
    let (i, j) = inputs in
    let state = (nth s' w (p - 1)) in
    let x = (nth 0 state i) in
    let y = (nth 0 state j) in x + y
with g = MULT inputs =>
    let (i, j) = inputs in
    let statep = (nth s' w (p - 1)) in
    let xp = (nth 0 statep i) in
    let yp = (nth 0 statep j) in
    let p = if p = 3 then 0 else p in
    let statep' = (nth s' w (p)) in
    let xp' = (nth 0 statep' i) in
    let yp' = (nth 0 statep' j) in
    xp * yp + xp' * yp + xp * yp' + 1 - 1.

(* secret sharing distribution *)
op dinput : {input distr | is_lossless dinput /\ is_funiform dinput} as dinput_llfuni.

lemma dinput_ll : is_lossless dinput by have []:= dinput_llfuni.
lemma dinput_funi : is_funiform dinput by have []:= dinput_llfuni.
lemma dinput_fu : is_full dinput by apply/funi_ll_full; [exact/dinput_funi|exact/dinput_ll].

(* Random Oracle *)

module Phi = {
  proc main(x : input, c : circuit) = {
    var x1, x2, x3, w1, w2, w3, y1, y2, y3, r1, r2, r3;
    var g : gate;
    x1 <$ dinput;
    x2 <$ dinput;
    x3 = x - x1 - x2;
    w1 = [x1];
    w2 = [x2];
    w3 = [x3];
    while (c <> []) {
      g = head (ADD(0,0)) c;
      r1 = phi_decomp x g 1 [w1;w2;w3];
      r2 = phi_decomp x g 2 [w1;w2;w3];
      r3 = phi_decomp x g 3 [w1;w2;w3];
      w1 = rcons w1 r1;
      w2 = rcons w2 r2;
      w3 = rcons w3 r3;
      c = behead c;
    }
    y1 = last 0 w1;
    y2 = last 0 w2;
    y3 = last 0 w3;
    (* return (w1, w2, w3, y1, y2, y3); *)
    return y1 + y2 + y3;
  }
}.

lemma decomp_test &m:
    Pr[Phi.main(10, circuit_ex) @ &m : res = 120] = 1%r.
proof.
    byphoare(: x = 10 /\ c = circuit_ex ==> _)=>//.
    proc. auto.
    seq 3 : (x = x1 + x2 + x3 /\ #pre). auto. auto. progress. apply dinput_ll. algebra.
    sp. rewrite /circuit_ex.
    rcondt 1. auto.
    sp. elim*. progress.
    rcondt 1. auto.
    sp. elim*. progress.
    rcondf 1. auto.
    auto. progress.
    smt().
    hoare. auto. progress. algebra. progress.
qed.
