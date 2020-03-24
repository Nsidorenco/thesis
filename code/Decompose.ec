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
  | ADDC of (int * int)
  | MULTC of (int * int)
  | MULT of (int * int)
  | ADD of (int * int)
].

type circuit = gate list.
type state = int list.
(* type input_map = (int, input_wires) fmap. *)

op plus_gate (x y : int) = x + y.
op mult_gate (x y : int) = x * y.

op eval_gate (g : gate, s : state) : output =
with g = MULT inputs => let (i, j) = inputs in
                        let x = (nth 0 s i) in
                        let y = (nth 0 s j) in x * y
with g = ADD inputs =>  let (i, j) = inputs in
                        let x = (nth 0 s i) in
                        let y = (nth 0 s j) in x + y
with g = ADDC inputs => let (i, c) = inputs in
                        let x = (nth 0 s i) in x + c
with g = MULTC inputs => let (i, c) = inputs in
                         let x = (nth 0 s i) in x * c.

(* Circuit example: *)
(* x *)
(* | \*)
(* +2 \ *)
(* |  / *)
(* | / *)
(* * *)

const circuit_ex = [ADDC (0, 2); MULT(0,1)].
const s' : state = [10].

(* op eval_circuit(c : circuit, s : state) : output = *)
(*     with c = [] => last 0 s *)
(*     with c = g :: gs => let r = eval_gate g s in eval_circuit gs (rcons s r). *)

op eval_circuit_aux(c : circuit, s : state) : state =
    with c = [] => s
    with c = g :: gs =>
     let r = eval_gate g s in
     eval_circuit_aux gs (rcons s r).

op eval_circuit (c : circuit, s : state) : output =
    last 0 (eval_circuit_aux c s).

(* lemma eval_circuit_step g gs s: *)
(*     eval_circuit (g :: gs) s = eval_circuit gs (rcons s (eval_gate g s)). *)
(* proof. trivial. qed. *)

lemma circuit_ex_test : (eval_circuit circuit_ex [10]) = 120.
    proof. by rewrite /eval_circuit /circuit_ex /rev /catrev; simplify. qed.

(** Phi protocol **)

(* define decomposed circuit function *)
type random_tape = int list list.
op phi_decomp (g : gate, p : int, w : view list, R : random_tape) : output =
with g = ADDC inputs =>
    let (i, c) = inputs in
    let state = (nth s' w (p - 1)) in
    let x = (nth 0 state i) in
    if p = 1 then x + c else x
with g = MULTC inputs =>
    let (i, c) = inputs in
    let state = (nth s' w (p - 1)) in
    let x = (nth 0 state i) in x * c
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
    let rp = (nth 0 (nth [] R (p-1)) (size w)) in
    let p = if p = 3 then 0 else p in
    let statep' = (nth s' w (p)) in
    let xp' = (nth 0 statep' i) in
    let yp' = (nth 0 statep' j) in
    let rp' = (nth 0 (nth [] R p) (size w)) in
    xp * yp + xp' * yp + xp * yp' + rp - rp'.

op phi_circuit_aux (c : circuit, w : view list, R : random_tape) : view list =
    with c = [] => w
    with c = g::gs =>
    let w1 = nth [] w 0 in
    let w2 = nth [] w 1 in
    let w3 = nth [] w 2 in
    let r1 = phi_decomp g 1 w R in
    let r2 = phi_decomp g 2 w R in
    let r3 = phi_decomp g 3 w R in
    phi_circuit_aux gs [(rcons w1 r1);(rcons w2 r2);(rcons w3 r3)] R.

op phi_circuit (c : circuit, w1, w2, w3 : view, R : random_tape) : output =
    let w = phi_circuit_aux c [w1;w2;w3] R in
    let w1 = nth [] w 0 in
    let w2 = nth [] w 1 in
    let w3 = nth [] w 2 in
    last 0 w1 + last 0 w2 + last 0 w3.


lemma phi_circuit_ex_test R : (phi_circuit circuit_ex [2] [3] [5] R) = 120.
    proof. rewrite /phi_circuit /circuit_ex /rev.
    simplify. algebra. qed.


(* secret sharing distribution *)
op dinput : {input distr | is_lossless dinput /\ is_funiform dinput} as dinput_llfuni.

lemma dinput_ll : is_lossless dinput by have []:= dinput_llfuni.
lemma dinput_funi : is_funiform dinput by have []:= dinput_llfuni.
lemma dinput_fu : is_full dinput by apply/funi_ll_full; [exact/dinput_funi|exact/dinput_ll].

(* Random Oracle *)
op dtape : {input list distr | is_lossless dtape /\ is_funiform dtape} as dtape_llfuni.

lemma dtape_ll : is_lossless dtape by have []:= dtape_llfuni.
lemma dtape_funi : is_funiform dtape by have []:= dtape_llfuni.
lemma dtape_fu : is_full dtape by apply/funi_ll_full; [exact/dtape_funi|exact/dtape_ll].

module Oracle = {
  proc init(n : int) = {
    var k, x, tape;
    tape = [];
    k = 0;
    while (k < n) {
      x <$ dinput;
      tape = (x::tape);
      k = k+1;
    }
    return tape;
  }

  proc stepped(n : int) = {
    var x, tape;
    tape = init(n-1);
    if (0 < n) {
      x <$ dinput;
      tape = (x::tape);
    }
    return tape;
  }
}.

equiv init_stepped_equiv:
    Oracle.init ~ Oracle.stepped : ={n} /\ 0 < n{1} /\ 0 < n{2} ==> ={res}.
proof.
  proc. inline *. sp.
  splitwhile{1} 1 : k < n - 1.
  unroll{1} 2.
  seq 1 2 : (={tape, k, n} /\ k{1} = n{1} - 1 /\ 0 < n{1}). auto.
  while (tape0{2} = tape{1} /\ ={k, n} /\ n0{2} = n{1} - 1 /\ k{1} - 1 < n{1} - 1);
  auto; progress; smt().

  rcondf{1} 2. auto. if. auto. progress.
  if. progress. smt().
  auto. progress.
qed.

module Phi = {
  proc main(h : input, c : circuit) = {
    var x1, x2, x3, y, k1, k2, k3;
    x1 <$ dinput;
    x2 <$ dinput;
    x3 = h - x1 - x2;
    k1 = Oracle.init((size c));
    k2 = Oracle.init((size c));
    k3 = Oracle.init((size c));
    y = phi_circuit c [x1] [x2] [x3] [k1;k2;k3];
    return y;
  }
}.

module SampleTest = {
  proc main() = {
    var x;
    x <$ dinput;
    return x;
  }
}.

lemma oracle_ll_pr:
    hoare[Oracle.init : true ==> true].
proof. proc. auto. qed.

lemma oracle_succedes_pr:
    (forall (m : int), 0 <= m =>
    (forall &m, Pr[Oracle.init(m) @ &m : (size res) = m /\ (forall j, j < (size res) /\ 0 <= j => (nth 0 res j) \in dinput) ] = 1%r)).
proof.
  elim /intind; progress.
  - byphoare (: n = 0 ==>)=>//. proc. sp. rcondf 1. auto. auto. progress. smt().
  have -> :
    Pr[Oracle.init(i+1) @ &m :
      size res = i+1 /\
      forall (j : int), j < size res /\ 0 <= j => nth 0 res j \in dinput] =
    Pr[Oracle.stepped(i+1) @ &m :
      size res = i+1 /\
      forall (j : int), j < size res /\ 0 <= j => nth 0 res j \in dinput].
  byequiv=>//.
  proc. inline *. sp.
  splitwhile{1} 1 : k < n - 1.
  unroll{1} 2.
  seq 1 2 : (={tape, k, n} /\ k{1} = n{1} - 1 /\ 0 < n{1}). auto.
  while (tape0{2} = tape{1} /\ ={k, n} /\ n0{2} = n{1} - 1 /\ k{1} - 1 < n{1} - 1);
  auto; progress; smt().
  rcondf{1} 2. auto. if. auto. progress.
  if. progress. smt().
  auto. progress.
  have Hph: phoare[Oracle.init : (n = i) ==>
                size res = i /\
                forall (j : int), j < size res /\ 0 <= j => nth 0 res j \in dinput] = 1%r.
  bypr. progress. apply (H0 &m0).
  byphoare (: n = i + 1 ==>)=>//.
  proc. case (0 < n).
  rcondt 2. call oracle_ll_pr. auto.
  auto.
  call Hph. auto. progress.
  apply dinput_ll.
  smt().
  smt().

  rcondf 2. call oracle_ll_pr. auto.
  call Hph. auto.
  smt().
qed.


lemma oracle_succedes:
    forall m,
    0 <= m =>
    phoare[Oracle.init : (n = m)
            ==> (size res) = m /\ (forall j, j < (size res) /\ 0 <= j => (nth 0 res j) \in dinput) ] = 1%r.
proof.
  progress. bypr.
  progress. by have := (oracle_succedes_pr n{m} H &m).
qed.

lemma decomp_test &m:
    Pr[Phi.main(10, circuit_ex) @ &m : res = 120] = 1%r.
proof.
    byphoare(: h = 10 /\ c = circuit_ex ==> _)=>//.
    proc. auto.
    have Hsize : 0 <= size circuit_ex by trivial.
    have H := (oracle_succedes (size circuit_ex) Hsize).
    call H. call H. call H.
    auto. progress. apply dinput_ll.
    rewrite /circuit_ex /phi_circuit /rev. simplify.
    algebra.
qed.

lemma decompo_circuit_ex_equiv &m x':
    Pr[Phi.main(x', circuit_ex) @ &m : res = eval_circuit circuit_ex [x'] ] = 1%r.
proof.
    byphoare(: h = x' /\ c = circuit_ex ==> _)=>//.
    proc.  auto.
    have Hsize : 0 <= size circuit_ex by trivial.
    have H := (oracle_succedes (size circuit_ex) Hsize).
    call H. call H. call H.
    auto. progress. apply dinput_ll.
    rewrite /circuit_ex /phi_circuit /rev /eval_circuit. simplify.
    algebra.
qed.

lemma circuit_concat gs gs' :
    (forall s, eval_circuit_aux (gs++gs') s = eval_circuit_aux gs' (eval_circuit_aux gs s)).
proof. elim gs; progress. by rewrite H. qed.

lemma phi_concat gs gs' R:
    (forall w, phi_circuit_aux (gs++gs') w R = phi_circuit_aux gs' (phi_circuit_aux gs w R) R).
proof. elim gs; progress. by rewrite H. qed.

lemma decomp_equiv g (x x1 x2 x3 : input) (w1 w2 w3 : view) s R:
    (x = x1 + x2 + x3 /\ [w1;w2;w3] = phi_circuit_aux [g] [[x1];[x2];[x3]] R /\
    s = eval_circuit_aux [g] [x]) =>
    (forall i, (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i)).
proof.
  elim g; progress.
  - smt().
  - smt().
  - elim x0=> x01 x02; case (i = 0); case (i - 1 = 0); case (x01 = 0); case(x02 = 0); progress.
    algebra. case (x02 = 0). progress. algebra. progress. algebra. case (x01 = 0). progress. algebra.
    progress. algebra. case (x01 = 0); case (x02 = 0); progress. algebra. algebra.
    algebra. algebra.
  - elim x0=> x01 x02; case (i = 0); case (i - 1 = 0); case (x01 = 0); case(x02 = 0); progress.
    algebra. case (x02 = 0). progress. algebra. progress. case (x01 = 0). progress. algebra.
    progress. case (x01 = 0); case (x02 = 0); progress. algebra.
qed.

lemma phi_gate_equiv' g:
    (forall w1 w2 w3 w1' w2' w3' s' s R,
      size s = size w1 /\
      size s = size w2 /\
      size s = size w3
      /\ (forall i, (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i))
      /\ [w1';w2';w3'] = phi_circuit_aux [g] [w1;w2;w3] R
      /\ s' = eval_circuit_aux [g] s =>
      (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s' i))).
proof.
   elim g; progress;
   elim x=> x1 x2;
   rewrite !nth_rcons;
   case (i < size w1);
   case (i < size w2);
   case (i < size w3);
   case (i < size s); progress; smt().
qed.

lemma phi_equiv_ind gs:
    (forall w1 w2 w3 w1' w2' w3' s' s R,
      size s = size w1 /\
      size s = size w2 /\
      size s = size w3
      /\ (forall i, (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i))
      /\ [w1';w2';w3'] = phi_circuit_aux gs [w1;w2;w3] R
      /\ s' = eval_circuit_aux gs s =>
      (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s' i))).
proof.
  elim gs. progress. move=> x l H w1 w2 w3 w1' w2' w3' s' s R.
  move=> [Hs1 [Hs2 [Hs3 [Hrel [Hphi Hcircuit]]]]].
  have : [w1'; w2'; w3'] = phi_circuit_aux l (phi_circuit_aux [x] [w1;w2;w3] R) R by smt().
  move=> Hphi'.
  have : s' = eval_circuit_aux l (eval_circuit_aux [x] s) by smt().
  move=> Hcircuit'.
  apply (H (rcons w1 (phi_decomp x 1 [w1;w2;w3] R))
           (rcons w2 (phi_decomp x 2 [w1;w2;w3] R))
           (rcons w3 (phi_decomp x 3 [w1;w2;w3] R)) (eval_circuit_aux [x] s) R).
  do split=>//.
  smt. smt. smt.
  have :
      (forall (i : int),
        (nth 0 (rcons w1 (phi_decomp x 1 [w1; w2; w3] R)) i +
        nth 0 (rcons w2 (phi_decomp x 2 [w1; w2; w3] R)) i +
        nth 0 (rcons w3 (phi_decomp x 3 [w1; w2; w3] R)) i =
        nth 0 (eval_circuit_aux [x] s) i) =
        (if (i < size w1) then
            nth 0 w1 i +
            nth 0 w2 i +
            nth 0 w3 i =
            nth 0 s i
         else if (i = size w1) then
            nth 0 (rcons w1 (phi_decomp x 1 [w1; w2; w3] R)) i +
            nth 0 (rcons w2 (phi_decomp x 2 [w1; w2; w3] R)) i +
            nth 0 (rcons w3 (phi_decomp x 3 [w1; w2; w3] R)) i =
            nth 0 (eval_circuit_aux [x] s) i
         else 0 = 0)).
    progress.  clear H.
    rewrite !nth_rcons. subst.
    have <- : (size w1 = size w2) by smt().
    have <- : (size w1 = size w3) by smt().
    case (i < size w1); progress.
    case (i = size w1); progress.
    smt().
    smt().
    smt().
    progress.
    rewrite H0.
    case (i < size w1); progress. apply Hrel.
    have Hgate := (phi_gate_equiv' x).
    apply (Hgate w1 w2 w3 s R).
    progress.
qed.

lemma w_eq_length gs:
    (forall w1 w2 w3 w1' w2' w3' R,
      size w1 = size w2 /\ size w2 = size w3 /\
      [w1';w2';w3'] = phi_circuit_aux gs [w1;w2;w3] R =>
      size w1' = size w2' /\ size w2' = size w3').
proof.
  elim gs; progress; smt.
  (* have Hnew := (H (rcons w1 (phi_decomp x 1 [w1;w2;w3])) *)
  (*                 (rcons w2 (phi_decomp x 2 [w1;w2;w3])) *)
  (*                 (rcons w3 (phi_decomp x 3 [w1;w2;w3])) *)
  (*                 w1' w2' w3'). *)
qed.

lemma w_s_eq_length gs:
    (forall w1 w2 w3 w1' w2' w3' s s' R,
      size w1 = size s /\
      [w1';w2';w3'] = phi_circuit_aux gs [w1;w2;w3] R /\
      s'  = eval_circuit_aux gs s =>
      size w1' = size s').
proof.
  elim gs; progress; smt.
qed.


lemma always_three_views gs:
    (forall w1 w2 w3 R, exists w1' w2' w3',
      [w1';w2';w3'] = phi_circuit_aux gs [w1;w2;w3] R).
proof.
  elim gs; progress; [smt | apply H].
qed.


lemma phi_circuit_equiv &m x' c':
    Pr[Phi.main(x', c') @ &m : res = eval_circuit c' [x'] ] = 1%r.
proof.
    byphoare(: h = x' /\ c = c' ==> _)=>//.
    proc. auto.
    have Hsize : 0 <= (size c') by smt.
    have Horacle := (oracle_succedes (size c') Hsize).
    do ? (call Horacle); auto; progress.
    apply dinput_ll.
    rewrite /eval_circuit /phi_circuit /rev.
    clear Horacle Hsize.
    have : exists w, (w = (phi_circuit_aux c{hr} [[v]; [v0]; [h{hr} - v - v0]] [result;result0;result1])) by smt().
    have := always_three_views c{hr} [v] [v0] [h{hr} - v - v0] [result;result0;result1].
    have : exists w, w = (phi_circuit_aux c{hr} [[v]; [v0]; [h{hr} - v - v0]] [result;result0;result1]) by smt.
    progress.
    have -> : (nth [] (phi_circuit_aux c{hr} [[v]; [v0]; [h{hr} - v - v0]] [result;result0;result1]) 0) = w1' by smt().
    have -> : (nth [] (phi_circuit_aux c{hr} [[v]; [v0]; [h{hr} - v - v0]] [result;result0;result1]) 1) = w2' by smt().
    have -> : (nth [] (phi_circuit_aux c{hr} [[v]; [v0]; [h{hr} - v - v0]] [result;result0;result1]) 2) = w3' by smt().
    progress.
    have :
      (forall i,
        (nth 0 w1') i +
        (nth 0 w2') i +
        (nth 0 w3') i =
        (nth 0 (eval_circuit_aux c{hr} [h{hr}]) i)) =>
      (last 0 w1' +
       last 0 w2' +
       last 0 w3' =
       last 0 (eval_circuit_aux c{hr} [h{hr}])).
    progress.
    have Hlast := (last_nth 0 0).
    rewrite !Hlast.
    have Heq_len := (w_eq_length c{hr} [v] [v0] [h{hr} - v - v0] w1' w2' w3').
    have <- : size w1' = size w2' by smt().
    have <- : size w1' = size w3' by smt().
    have <- : size w1' = size (eval_circuit_aux c{hr} [h{hr}]).
    have Hws_len := w_s_eq_length c{hr} [v] [v0] [h{hr} - v - v0] w1' w2' w3' [h{hr}] (eval_circuit_aux c{hr} [h{hr}]) [result;result0;result1].
    apply Hws_len. smt().
    smt().
    progress. apply H12. clear H12.
    have Hrel := (phi_equiv_ind c{hr} [v] [v0] [h{hr} - v - v0] w1' w2' w3' (eval_circuit_aux c{hr} [h{hr}]) [h{hr}] [result;result0;result1]).
    apply Hrel. smt().
qed.
