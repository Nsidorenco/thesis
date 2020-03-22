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

const circuit_ex = rev [ADDC (0, 2); MULT(0,1)].
const s' : state = [10].

(* op eval_circuit(c : circuit, s : state) : output = *)
(*     with c = [] => last 0 s *)
(*     with c = g :: gs => let r = eval_gate g s in eval_circuit gs (rcons s r). *)

op eval_circuit_aux(c : circuit, s : state) : state =
    with c = [] => s
    with c = g :: gs =>
     let s' = eval_circuit_aux gs s in
     let r = eval_gate g s' in (rcons s' r).

op eval_circuit (c : circuit, s : state) : output =
    last 0 (eval_circuit_aux c s).

(* lemma eval_circuit_step g gs s: *)
(*     eval_circuit (g :: gs) s = eval_circuit gs (rcons s (eval_gate g s)). *)
(* proof. trivial. qed. *)

lemma circuit_ex_test : (eval_circuit circuit_ex [10]) = 120.
    proof. by rewrite /eval_circuit /circuit_ex /rev /catrev; simplify. qed.

(** Phi protocol **)

(* define decomposed circuit function *)
op phi_decomp (g : gate, p : int, w : state list) : output =
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
    let p = if p = 3 then 0 else p in
    let statep' = (nth s' w (p)) in
    let xp' = (nth 0 statep' i) in
    let yp' = (nth 0 statep' j) in
    xp * yp + xp' * yp + xp * yp' + 1 - 1.

op phi_circuit_aux (c : circuit, w1 w2 w3 : view) : (view * view * view) =
    with c = [] => (w1, w2, w3)
    with c = g::gs =>
    let (w1, w2, w3) = phi_circuit_aux gs w1 w2 w3 in
    let r1 = phi_decomp g 1 [w1;w2;w3] in
    let r2 = phi_decomp g 2 [w1;w2;w3] in
    let r3 = phi_decomp g 3 [w1;w2;w3] in
    (rcons w1 r1, rcons w2 r2, rcons w3 r3).

op phi_circuit (c : circuit, w1, w2, w3 : view) : output =
    let (w1, w2, w3) = phi_circuit_aux c w1 w2 w3 in
    last 0 w1 + last 0 w2 + last 0 w3.


lemma phi_circuit_ex_test : (phi_circuit circuit_ex [2] [3] [5]) = 120.
    proof. by rewrite /phi_circuit /circuit_ex /rev. qed.


(* secret sharing distribution *)
op dinput : {input distr | is_lossless dinput /\ is_funiform dinput} as dinput_llfuni.

lemma dinput_ll : is_lossless dinput by have []:= dinput_llfuni.
lemma dinput_funi : is_funiform dinput by have []:= dinput_llfuni.
lemma dinput_fu : is_full dinput by apply/funi_ll_full; [exact/dinput_funi|exact/dinput_ll].

(* Random Oracle *)

module Phi = {
  (* proc compute(c : circuit, w1 w2 w3 : view) = { *)
  (*   var g, r1, r2, r3; *)
  (*   while (c <> []) { *)
  (*     g = last (ADDC(0,42)) c; *)
  (*     r1 = phi_decomp g 1 [w1;w2;w3]; *)
  (*     r2 = phi_decomp g 2 [w1;w2;w3]; *)
  (*     r3 = phi_decomp g 3 [w1;w2;w3]; *)
  (*     w1 = rcons w1 r1; *)
  (*     w2 = rcons w2 r2; *)
  (*     w3 = rcons w3 r3; *)
  (*     c = rev (behead (rev c)); *)
  (*   } *)
  (*   return (w1, w2, w3); *)
  (* } *)
  (* proc compute_stepped(g : gate, c' : circuit, w1 w2 w3 : view) = { *)
  (*   (w1, w2, w3) = compute(c', w1, w2, w3); *)
  (*   (w1, w2, w3) = compute([g], w1, w2, w3); *)
  (*   return (w1, w2, w3); *)
  (* } *)
  proc main(h : input, c : circuit) = {
    var x1, x2, x3, y;
    x1 <$ dinput;
    x2 <$ dinput;
    x3 = h - x1 - x2;
    y = phi_circuit c [x1] [x2] [x3];
    return y;
  }
}.

lemma decomp_test &m:
    Pr[Phi.main(10, circuit_ex) @ &m : res = 120] = 1%r.
proof.
    byphoare(: h = 10 /\ c = circuit_ex ==> _)=>//.
    proc. auto.
    rewrite /circuit_ex /rev. progress.
    apply dinput_ll.
    rewrite /phi_circuit /rev. simplify. algebra.
qed.

lemma decompo_circuit_ex_equiv &m x':
    Pr[Phi.main(x', circuit_ex) @ &m : res = eval_circuit circuit_ex [x'] ] = 1%r.
proof.
    byphoare(: h = x' /\ c = circuit_ex ==> _)=>//.
    proc.  auto.
    rewrite /circuit_ex /rev. progress.
    apply dinput_ll.
    rewrite /eval_circuit /phi_circuit /rev. simplify. algebra.
qed.

lemma decomp_equiv_ind g gs (x x1 x2 x3 : input) (w1 w2 w3 : view) r1 r2 r3:
    r1 = phi_decomp g 1 [w1;w2;w3] /\
    r2 = phi_decomp g 2 [w1;w2;w3] /\
    r3 = phi_decomp g 3 [w1;w2;w3] =>
    ((rcons w1 r1), (rcons w2 r2), (rcons w3 r3)) = phi_circuit_aux (g::gs) [x1] [x2] [x3]
    <=> (w1, w2, w3) = phi_circuit_aux gs [x1] [x2] [x3].
proof.
  progress.
  - smt.
  - elim g; progress; rewrite - H.
    + elim x0; progress. smt().
    + elim x0; progress. smt().
qed.

lemma circuit_equiv_ind g gs (x : input) s r:
    r = eval_gate g s =>
    (rcons s r) = eval_circuit_aux (g::gs) [x]
    <=> s = eval_circuit_aux gs [x].
proof.
  progress. smt.
qed.

lemma decomp_equiv g (x x1 x2 x3 : input) (w1 w2 w3 : view) s:
    (x = x1 + x2 + x3 /\ (w1, w2, w3) = phi_circuit_aux [g] [x1] [x2] [x3] /\
    s = eval_circuit_aux [g] [x]) =>
    (forall i, (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i)).
proof.
  elim g; progress.
  - smt().
  - smt().
  - elim x0=> x01 x02; case (i = 0); case (i - 1 = 0); case (x01 = 0); case(x02 = 0); progress.
    algebra. case (x02 = 0). progress. algebra. progress. case (x01 = 0). progress. algebra.
    progress. case (x01 = 0); case (x02 = 0); progress. algebra.
  - elim x0=> x01 x02; case (i = 0); case (i - 1 = 0); case (x01 = 0); case(x02 = 0); progress.
    algebra. case (x02 = 0). progress. algebra. progress. case (x01 = 0). progress. algebra.
    progress. case (x01 = 0); case (x02 = 0); progress. algebra.
qed.

lemma decomp_equiv_ind gs (x x1 x2 x3 : input) (w1 w2 w3 : view) s:
    (x = x1 + x2 + x3 /\ (w1, w2, w3) = phi_circuit_aux gs [x1] [x2] [x3] /\
    s = eval_circuit_aux gs [x]) =>
    (forall i, (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i)).
proof.
   elim gs; progress. smt().
   have : (w1, w2, w3) = phi_circuit_aux (x0::l) [x1] [x2] [x3].
   smt.
   clear H0.
   have -> : (rcons (eval_circuit_aux l [x1 + x2 + x3]) (eval_gate x0 (eval_circuit_aux l [x1 + x2 + x3]))) = eval_circuit_aux (x0::l) [x1+x2+x3].
   smt.
   move=> H1.
   progress.
   smt.


lemma decompo_circuit_ex_equiv &m x' c':
    Pr[Phi.main(x', c') @ &m : res = eval_circuit c' [x'] ] = 1%r.
proof.
    elim c'.
    byphoare(: h = x' /\ c = [] ==> _)=>//.
    proc.  auto.
    rewrite /circuit_ex /rev. progress.
    apply dinput_ll.
    rewrite /eval_circuit /phi_circuit /rev. simplify.
    algebra.
    progress.
    byphoare(: h = x' /\ c = (x::l) ==> _)=>//.
    proc. auto.
    rewrite /circuit_ex /rev. progress.
    apply dinput_ll.
qed.


lemma decomp_gate_equiv g w1' w2' w3' s':
    (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s' i)) =>
    phoare[Phi.compute : (c = [g] /\ w1 = w1' /\ w2 = w2' /\ w3 = w3' )
            ==> let (w1, w2, w3) = res in last 0 w1 + last 0 w2 + last 0 w3 = eval_circuit [g] s'] = 1%r.
proof.
  move=> invariant.
  proc. inline *. wp.
  rcondt 1. auto.
  sp. elim*. auto.
  rcondf 1. auto.
  elim g; rewrite /rev; progress.
  elim g; rewrite /rev; auto; progress.
  - case x. progress.
    rewrite /rcons /last /eval_circuit. simplify.
    rewrite !last_rcons.
    rewrite - invariant.
    algebra.
  - case x. progress.
    rewrite /rcons /last /eval_circuit. simplify.
    rewrite !last_rcons.
    rewrite - invariant.
    algebra.
  - case x. progress.
    rewrite /rcons /last /eval_circuit. simplify.
    rewrite !last_rcons.
    rewrite - invariant.
    smt().
  - case x. progress.
    rewrite /rcons /last /eval_circuit. simplify.
    rewrite !last_rcons.
    rewrite - invariant.
    smt().
qed.

lemma decomp_gate_equiv &m c' (x1 x2 x3 : input):
    (* (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s' i)) => *)
    phoare[Phi.compute : (c = c' /\ w1 = [x1] /\ w2 = [x2] /\ w3 = [x3] )
      ==> let (w1, w2, w3) = res in
          let s = eval_circuit_aux c' [x1 + x2 + x3] in
            (forall i, (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i))] = 1%r.
proof.
    elim c'.
    proc.  rcondf 1. auto. auto. progress. smt().
    progress.

lemma compute_circuit_equiv &m x' g c':
    phoare[Phi.compute : (x = x' /\ c = c') ==>
      let (w1, w2, w3) = res in last 0 w1 + last 0 w2 + last 0 w3 = eval_circuit c' [x']] = 1%r =>
    phoare[Phi.compute : (x = x' /\ c = (g::c')) ==>
      let (w1, w2, w3) = res in last 0 w1 + last 0 w2 + last 0 w3 = eval_circuit (g::c') [x']] = 1%r.
proof. move=> H.
   proc. unroll 1.
   rcondt 1. auto.
   sp. elim*. progress.
   conseq H.


lemma decompo_circuit_equiv &m x' c':
    phoare[Phi.main : (x = x' /\ c = c') ==> res = eval_circuit c' [x']] = 1%r.
proof.
  proc. auto.
  seq 3 : (x = x1 + x2 + x3 /\ #pre). auto. auto. progress. apply dinput_ll. algebra.
  exists* x1. exists* x2. exists* x3. elim*=> x1 x2 x3.
  call (: w1 = [x1] /\ w2 = [x2] /\ w3 =  [x3] /\ x' = x1 + x2 + x3 /\ c = c' ==> let (w1, w2, w3) = res in last 0 w1 + last 0 w2 + last 0 w3 = eval_circuit c' [x']).
  proc. elim c'.
  (* call (: Phi.w1 = x1 + x2 + x3). elim c'. *)
  * rcondf 1; auto.
  * progress. rcondt 1. auto.
    sp. elim*. auto. admit.
  * hoare. auto. progress. algebra.
  * progress.
qed.
