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
type random_tape = int list.
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
    let rp = (nth 0 R (p-1)) in
    let p = if p = 3 then 0 else p in
    let statep' = (nth s' w (p)) in
    let xp' = (nth 0 statep' i) in
    let yp' = (nth 0 statep' j) in
    let rp' = (nth 0 R p) in
    xp * yp + xp' * yp + xp * yp' + rp - rp'.

op simulator_eval (g : gate, p : int, w : view list, R : random_tape) =
with g = MULT inputs =>
   if (p = 2) then (nth 0 R p) else phi_decomp g p w R
with g = ADDC inputs => phi_decomp g p w R
with g = MULTC inputs => phi_decomp g p w R
with g = ADD inputs => phi_decomp g p w R.



(* secret sharing distribution *)
op dinput : {input distr | is_lossless dinput /\ is_funiform dinput} as dinput_llfuni.

lemma dinput_ll : is_lossless dinput by have []:= dinput_llfuni.
lemma dinput_funi : is_funiform dinput by have []:= dinput_llfuni.
lemma dinput_fu : is_full dinput by apply/funi_ll_full; [exact/dinput_funi|exact/dinput_ll].


module Phi = {
  proc share(x) = {
    var x1, x2, x3;
    x1 <$ dinput;
    x2 <$ dinput;
    x3 = x - x1 - x2;
    return (x1, x2, x3);
  }
  proc output(view) = {
    var y;
    y = last 0 view;
    return y;
  }
  proc reconstruct(s1 s2 s3 : int) = {
    return s1 + s2 + s3;
  }
  proc compute(c : circuit, w1 w2 w3 : view) = {
    var g, k1, k2, k3, r1, r2, r3;
    while (c <> []) {
      g = head (ADDC(0,0)) c;
      k1 <$ dinput;
      k2 <$ dinput;
      k3 <$ dinput;
      r1 = phi_decomp g 1 [w1;w2;w3] [k1;k2;k3];
      r2 = phi_decomp g 2 [w1;w2;w3] [k1;k2;k3];
      r3 = phi_decomp g 3 [w1;w2;w3] [k1;k2;k3];
      w1 = (rcons w1 r1);
      w2 = (rcons w2 r2);
      w3 = (rcons w3 r3);
      c = behead c;
    }
    return (w1, w2, w3);
  }
  proc compute_stepped(c : circuit, w1 w2 w3 : view) = {
    (w1, w2, w3) = compute([head (ADDC(0,0)) c], w1, w2, w3);
    c = behead c;
    (w1, w2, w3) = compute(c, w1, w2, w3);
    return (w1, w2, w3);

  }
  proc main(h : input, c : circuit) = {
    var x1, x2, x3, y, w1, w2, w3, y1, y2, y3;
    (x1, x2, x3) = share(h);
    (w1, w2, w3) = compute(c, [x1], [x2], [x3]);
    y1 = output(w1);
    y2 = output(w2);
    y3 = output(w3);
    y = reconstruct(y1, y2, y3);
    return y;
  }
}.

module Simulator = {
  proc compute(c : circuit, w1 w2 : view) = {
    var g, k1, k2, k3, r1, r2;
    while (c <> []) {
      g = head (ADDC(0,0)) c;
      k1 <$ dinput;
      k2 <$ dinput;
      k3 <$ dinput;
      r1 = simulator_eval g 1 [w1;w2] [k1;k2;k3];
      r2 = simulator_eval g 2 [w1;w2] [k1;k2;k3];
      w1 = (rcons w1 r1);
      w2 = (rcons w2 r2);
      c = behead c;
    }

    return (w1, w2);
  }
  proc compute_stepped(c : circuit, w1 w2 : view) = {
    (w1, w2) = compute([head (ADDC(0,0)) c], w1, w2);
    c = behead c;
    (w1, w2) = compute(c, w1, w2);
    return (w1, w2);

  }
}.

module Privacy = {
  proc real(h : input, c : circuit, e : int) = {
    var x1, x2, x3, w1, w2, w3, y1, y2, y3, ret;
    (x1, x2, x3) = Phi.share(h);
    (w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3]);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);
    if (e = 1) {
      ret = ((w1, w2), y3);
    } else {
      if (e = 2) {
        ret = ((w2, w3), y1);
      } else {
        ret = ((w3, w1), y2);
      }
    }

    return ret;
  }

  proc ideal(y : output, c : circuit, e : int) = {
    var x1, x2, w1, w2, y1, y2, y3;
    x1 <$ dinput;
    x2 <$ dinput;
    (w1, w2) = Simulator.compute(c, [x1], [x2]);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = y - (y1 + y2);

    return ((w1, w2), y3);
  }
}.


lemma compute_gate_correct g:
    (forall w1' w2' w3' s s',
      size s = size w1' /\
      size s = size w2' /\
      size s = size w3' /\
      s' = eval_circuit_aux [g] s =>
      phoare[Phi.compute : (c = [g] /\ w1 = w1' /\ w2 = w2' /\ w3 = w3' /\
        (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s i)))
        ==> let (w1res, w2res, w3res) = res in
        (forall i, (nth 0 w1res i) + (nth 0 w2res i) + (nth 0 w3res i) = (nth 0 s' i))
        /\ exists R, w1res = (rcons w1' (phi_decomp g 1 [w1';w2';w3'] R)) /\
                     w2res = (rcons w2' (phi_decomp g 2 [w1';w2';w3'] R)) /\
                     w3res = (rcons w3' (phi_decomp g 3 [w1';w2';w3'] R))] = 1%r).
proof.
  progress. proc.
  rcondt 1. progress.
  sp. rcondf 11. auto. auto. progress.
  apply dinput_ll.
  have Hgoal :
      (forall (i : int),
        (nth 0 (rcons w1{hr} (phi_decomp g 1 [w1{hr}; w2{hr}; w3{hr}] [v; v0; v1])) i +
        nth 0 (rcons w2{hr} (phi_decomp g 2 [w1{hr}; w2{hr}; w3{hr}] [v; v0; v1])) i +
        nth 0 (rcons w3{hr} (phi_decomp g 3 [w1{hr}; w2{hr}; w3{hr}] [v; v0; v1])) i =
        nth 0 (rcons s (eval_gate g s)) i) =
        (if (i < size w1{hr}) then
            nth 0 w1{hr} i +
            nth 0 w2{hr} i +
            nth 0 w3{hr} i =
            nth 0 s i
        else if (i = size w1{hr}) then
          nth 0 (rcons w1{hr} (phi_decomp g 1 [w1{hr}; w2{hr}; w3{hr}] [v; v0; v1])) i +
          nth 0 (rcons w2{hr} (phi_decomp g 2 [w1{hr}; w2{hr}; w3{hr}] [v; v0; v1])) i +
          nth 0 (rcons w3{hr} (phi_decomp g 3 [w1{hr}; w2{hr}; w3{hr}] [v; v0; v1])) i =
          nth 0 (rcons s (eval_gate g s)) i
        else 0 = 0)).
  progress.
  rewrite !nth_rcons. subst.
  have <- : (size w1{hr} = size w2{hr}) by smt().
  have <- : (size w1{hr} = size w3{hr}) by smt().
  case (i < size w1{hr}); progress.
  case (i = size w1{hr}); progress.
  smt().
  smt().
  smt().
  have -> := (Hgoal i); clear Hgoal.
  progress. apply H2.
  elim g; progress.
  - (* ADDC *)
    elim x=> x1 x2. simplify.
    smt.
  - (* MULTC *)
    elim x=> x1 x2. simplify.
    smt.
  - (* ADD *)
    elim x=> x1 x2. simplify.
    rewrite !nth_rcons. simplify. smt.
  - (* MULD *)
    elim x=> x1 x2. simplify.
    rewrite !nth_rcons. simplify. smt.
  by exists [v;v0;v1].
qed.

lemma eval_circuit_aux_size g s:
    size (eval_circuit_aux [g] s) = size s + 1 by smt.

lemma compute_circuit_correct c':
    (forall w1' w2' w3' s s',
      size s = size w1' /\
      size s = size w2' /\
      size s = size w3' /\
      s' = eval_circuit_aux c' s =>
        phoare[Phi.compute : ( c = c' /\ w1 = w1' /\ w2 = w2' /\ w3 = w3' /\
                              (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s i)))
        ==>  let (w1', w2', w3') = res in
        (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s' i))
        /\ size s' = size w1' /\ size w1' = size w2' /\ size w2' = size w3'] = 1%r).
proof.
  elim c'.
  - progress. proc. rcondf 1; progress. auto. progress; smt().
  - move=> x l Hind w1' w2' w3' s s'.
    move=> [Hs1 [Hs2 [Hs3 Hs'rel]]].
    bypr=> &m. progress.
    have -> :
      Pr[Phi.compute(c{m}, w1{m}, w2{m}, w3{m}) @ &m :
        let (w1', w2', w3') = res in
        (forall (i : int),
            nth 0 w1' i + nth 0 w2' i + nth 0 w3' i =
          nth 0 s' i)
        /\ size s' = size w1' /\ size w1' = size w2' /\ size w2' = size w3'] =
      Pr[Phi.compute_stepped(x::l, w1{m}, w2{m}, w3{m}) @ &m :
        let (w1', w2', w3') = res in
        (forall (i : int),
            nth 0 w1' i + nth 0 w2' i + nth 0 w3' i =
          nth 0 s' i)
        /\ size s' = size w1' /\ size w1' = size w2' /\ size w2' = size w3'].
      + byequiv=>//. clear Hind.
        proc. inline *. sp.
        unroll{1} 1; unroll{2} 1.
        if; progress. smt().
        + sp. seq 3 3 : (#pre /\ ={k1, k2, k3}); auto.
          sp. elim *. progress.
          rcondf{2} 1. progress. sp. elim*. progress.
          while (c1{2} = c{1} /\ w11{2} = w1{1} /\ w21{2} = w2{1} /\ w31{2} = w3{1}); auto.
          progress;smt().
        + exfalso; smt().
    byphoare(: c = (x::l) /\ w1 = w1{m} /\ w2 = w2{m} /\ w3 = w3{m} ==>)=>//.
    proc.
    have Hgate := (compute_gate_correct x w1{m} w2{m} w3{m} s (eval_circuit_aux [x] s) _).
    do ? split=>//.
    seq 1 : (
        (exists R, w1 = rcons w1{m} (phi_decomp x 1 [w1{m}; w2{m}; w3{m}] R) /\
                   w2 = rcons w2{m} (phi_decomp x 2 [w1{m}; w2{m}; w3{m}] R) /\
                   w3 = rcons w3{m} (phi_decomp x 3 [w1{m}; w2{m}; w3{m}] R)) /\
        forall (i : int),
          nth 0 w1 i + nth 0 w2 i + nth 0 w3 i =
          nth 0 (eval_circuit_aux [x] s) i /\ c = x :: l).
    auto. call Hgate.
    auto. progress.
    have H' :
      (let (w1res, w2res, w3res) = result in
        (forall (i : int),
          nth 0 w1res i + nth 0 w2res i + nth 0 w3res i =
          nth 0 (rcons s (eval_gate x s)) i) /\
        exists (R : random_tape),
          w1res = rcons w1{m} (phi_decomp x 1 [w1{m}; w2{m}; w3{m}] R) /\
          w2res = rcons w2{m} (phi_decomp x 2 [w1{m}; w2{m}; w3{m}] R) /\
          w3res = rcons w3{m} (phi_decomp x 3 [w1{m}; w2{m}; w3{m}] R)) =>
      exists (R : random_tape),
        result.`1 = rcons w1{m} (phi_decomp x 1 [w1{m}; w2{m}; w3{m}] R) /\
        result.`2 = rcons w2{m} (phi_decomp x 2 [w1{m}; w2{m}; w3{m}] R) /\
        result.`3 = rcons w3{m} (phi_decomp x 3 [w1{m}; w2{m}; w3{m}] R) by smt().
    apply H'. clear H'. assumption.
    have H' :
      (let (w1res, w2res, w3res) = result in
        (forall (i : int),
          nth 0 w1res i + nth 0 w2res i + nth 0 w3res i =
          nth 0 (rcons s (eval_gate x s)) i) /\
        exists (R : random_tape),
          w1res = rcons w1{m} (phi_decomp x 1 [w1{m}; w2{m}; w3{m}] R) /\
          w2res = rcons w2{m} (phi_decomp x 2 [w1{m}; w2{m}; w3{m}] R) /\
          w3res = rcons w3{m} (phi_decomp x 3 [w1{m}; w2{m}; w3{m}] R)) =>
      nth 0 result.`1 i + nth 0 result.`2 i + nth 0 result.`3 i =
      nth 0 (rcons s (eval_gate x s)) i by smt().
    apply H'. clear H'. assumption.
    elim*. progress.
    have Hind' := (Hind (rcons w1{m} (phi_decomp x 1 [w1{m}; w2{m}; w3{m}] R))
                        (rcons w2{m} (phi_decomp x 2 [w1{m}; w2{m}; w3{m}] R))
                        (rcons w3{m} (phi_decomp x 3 [w1{m}; w2{m}; w3{m}] R)) (eval_circuit_aux [x] s) s' _).
    do ? split=>//.
    smt(eval_circuit_aux_size size_rcons).
    smt(eval_circuit_aux_size size_rcons).
    smt(eval_circuit_aux_size size_rcons).
    call Hind'. clear Hgate Hind Hind'.
    auto. progress. smt(). smt(). smt().
    have H' :
      (let (w1', w2', w3') = result in
      (forall (i : int), nth 0 w1' i + nth 0 w2' i + nth 0 w3' i = nth 0 s' i) /\
      size s' = size w1' /\ size w1' = size w2' /\ size w2' = size w3') =>
      size s' = size result.`1.
    smt(). apply H'. assumption.
    have H' :
      (let (w1', w2', w3') = result in
      (forall (i : int), nth 0 w1' i + nth 0 w2' i + nth 0 w3' i = nth 0 s' i) /\
      size s' = size w1' /\ size w1' = size w2' /\ size w2' = size w3') =>
      size result.`1 = size result.`2.
    smt(). apply H'. assumption.
    have H' :
      (let (w1', w2', w3') = result in
      (forall (i : int), nth 0 w1' i + nth 0 w2' i + nth 0 w3' i = nth 0 s' i) /\
      size s' = size w1' /\ size w1' = size w2' /\ size w2' = size w3') =>
      size result.`2 = size result.`3.
    smt(). apply H'. assumption.
    + hoare. inline *. sp.
      rcondt 1. progress.
      auto. rcondf 12. progress.
      auto. auto. progress. smt().
      clear Hgate H Hs'rel. elim x; progress;
      elim x; move=> x1 x2; rewrite !nth_rcons; smt().
    trivial.
qed.


lemma phi_sim_equiv_mult x1 x2:
    (forall w1' w2' w3' s s',
      size s = size w1' /\
      size s = size w2' /\
      size s = size w3' /\
      s' = eval_circuit_aux [(MULT(x1, x2))] s =>
      equiv[Phi.compute ~ Simulator.compute :
            (={c, w1, w2} /\ c{1} = [(MULT(x1, x2))] /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{1} = w3') /\
             (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s i))
            ==>
            (let (phi_w1, phi_w2, phi_w3) = res{1} in
              (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 s' i))) /\
            (exists w',
                let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2, w') = res{1})]).
proof.
    progress.
    proc.
    rcondt{1} 1. auto.
    rcondt{2} 1. auto.
    rcondf{1} 12. auto.
    rcondf{2} 10. auto.
    sp. wp.
    seq 2 2 : (#pre /\ ={k1, k2}). auto.
    rnd (fun z => (nth 0 w2{2} x1 * nth 0 w2{2} x2 + nth 0 w3{1} x1 * nth 0 w2{2} x2 + nth 0 w2{2} x1 * nth 0 w3{1} x2 + k2{2} - z)).
    (* if k = then cancel out, else nothing? *)
    skip. progress.
    algebra.
    apply dinput_funi. smt().
    algebra.
    (* apply dinput_fu. smt(). *)
    rewrite !nth_rcons.
    have <- : size w1{2} = size w2{2} by smt().
    have <- : size w1{2} = size w3{1} by smt().
    rewrite H.
    case (i < size w1{2}); progress.
    apply H2.
    case (i = size w1{2}); progress.
    smt().

    exists (rcons w3{1}
      (nth 0 w3{1} x1 * nth 0 w3{1} x2 + nth 0 w1{2} x1 * nth 0 w3{1} x2 +
      nth 0 w3{1} x1 * nth 0 w1{2} x2 + k3L - k1{2})).
    do ? split.
qed.


lemma phi_sim_equiv g:
    (forall w1' w2' w3' s s',
      size s = size w1' /\
      size s = size w2' /\
      size s = size w3' /\
      s' = eval_circuit_aux [g] s =>
      equiv[Phi.compute ~ Simulator.compute :
            (={c, w1, w2} /\ c{1} = [g] /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{1} = w3') /\
             (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s i))
            ==>
            (let (phi_w1, phi_w2, phi_w3) = res{1} in
              (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 s' i)) /\
              (exists R, phi_w1 = (rcons w1' (phi_decomp g 1 [w1';w2';w3'] R)) /\
                         phi_w2 = (rcons w2' (phi_decomp g 2 [w1';w2';w3'] R)) /\
                         phi_w3 = (rcons w3' (phi_decomp g 3 [w1';w2';w3'] R)))) /\
            (exists w',
                let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2, w') = res{1})]).
proof.
    progress.
    proc.
    have Hs1 : size w1' = size w2' by smt().
    have Hs2 : size w1' = size w3' by smt().
    rcondt{1} 1. auto.
    rcondt{2} 1. auto.
    rcondf{1} 12. auto.
    rcondf{2} 10. auto.
    sp. wp.
    seq 2 2 : (#pre /\ ={k1, k2}). auto.
    elim g; progress; last first.
    (* Discharge trivial case: ADDC MULTC ADD *)
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    - (* MULT *)
      elim x=> x1 x2.
      rnd (fun z => (nth 0 w2{2} x1 * nth 0 w2{2} x2 + nth 0 w3{1} x1 * nth 0 w2{2} x2 + nth 0 w2{2} x1 * nth 0 w3{1} x2 + k2{2} - z)).
      skip. progress.
      algebra.
      apply dinput_funi. smt().
      algebra.
      smt(nth_rcons).
      exists [k1{2};k2{2};k3L].
      smt().
      smt().
qed.


lemma phi_sim__circuit_equiv c':
    (forall w1' w2' w3' s s',
      size s = size w1' /\
      size s = size w2' /\
      size s = size w3' /\
      s' = eval_circuit_aux c' s =>
      equiv[Phi.compute ~ Simulator.compute :
            (={c, w1, w2} /\ c{1} = c' /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{1} = w3') /\
             (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s i))
            ==>
            (let (phi_w1, phi_w2, phi_w3) = res{1} in
              size s' = size phi_w1 /\ size phi_w1 = size phi_w2 /\ size phi_w2 = size phi_w3 /\
              (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 s' i)) /\
              let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w1, phi_w2))]).
proof.
  elim c'.
  - (* empty circuit *)
    progress.
    proc.
    rcondf{1} 1. progress.
    rcondf{2} 1. progress.
    skip; progress. smt(). smt().
  - (* Inductive case *)
    move=> x l IH.
    move=> w1' w2' w3' s s'.
    move=> [Hs1 [Hs2 [Hs3 Hs']]].
    transitivity
      Phi.compute_stepped
      (={c, w1, w2, w3} /\
      c{1} = (x::l) /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{1} = w3'
      ==> ={res})
      (={c, w1, w2} /\
        c{1} = (x::l) /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{1} = w3' /\
      forall (i : int),
        nth 0 w1' i + nth 0 w2' i + nth 0 w3' i = nth 0 s i ==>
      let (phi_w1, phi_w2, phi_w3) = res{1} in
        size s' = size phi_w1 /\ size phi_w1 = size phi_w2 /\ size phi_w2 = size phi_w3 /\
        (forall (i : int),
            nth 0 phi_w1 i + nth 0 phi_w2 i + nth 0 phi_w3 i =
            nth 0 s' i) /\
        let (sim_w1, sim_w2) = res{2} in
      sim_w1 = phi_w1 /\ sim_w2 = phi_w2).
    + progress; smt().
    + progress; smt().
    + (* proof Phi.compute ~ Phi.compute_stepped *)
      clear IH. proc. inline *. sp.
      unroll{1} 1; unroll{2} 1.
      if; progress.
      sp. seq 3 3 : (#pre /\ ={k1, k2, k3}); auto.
      rcondf{2} 8. auto.
      sp. elim *; progress.
      while (c1{2} = c{1} /\ w11{2} = w1{1} /\ w21{2} = w2{1} /\ w31{2} = w3{1}); auto.
      rcondf{1} 1. progress.
      rcondf{2} 1. progress.
      rcondf{2} 7. auto.
      auto.
  symmetry.
  transitivity
    Simulator.compute_stepped
    (={c, w1, w2} /\
      c{1} = (x::l) /\ w1{1} = w1' /\ w2{1} = w2'
     ==>
     ={res})
    (={c, w1, w2} /\
    c{1} = (x::l) /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{2} = w3' /\
    forall (i : int),
      nth 0 w1' i + nth 0 w2' i + nth 0 w3' i = nth 0 s i ==>
    (let (phi_w1, phi_w2, phi_w3) = res{2} in
      size s' = size phi_w1 /\ size phi_w1 = size phi_w2 /\ size phi_w2 = size phi_w3 /\
      (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 s' i)) /\
      let (sim_w1, sim_w2) = res{1} in (sim_w1, sim_w2) = (phi_w1, phi_w2))).
  + progress; smt.
  + progress; smt.
  + (* proof Simulator.compute ~ Simulator.compute_stepped *)
    clear IH. proc. inline *. sp.
    unroll{1} 1; unroll{2} 1.
    if; progress.
    sp. seq 3 3 : (#pre /\ ={k1, k2, k3}); auto.
    rcondf{2} 6. auto.
    sp. elim *; progress.
    while (c1{2} = c{1} /\ w11{2} = w1{1} /\ w21{2} = w2{1}); auto.
    rcondf{1} 1. progress.
    rcondf{2} 1. progress.
    sp. elim*. progress.
    rcondf{2} 1. progress.
    auto.
  (* main proof *)
  proc.
  symmetry.
  seq 1 1 : (
      (exists R,  w1{1} = rcons w1' (phi_decomp x 1 [w1'; w2'; w3'] R) /\
                  w2{1} = rcons w2' (phi_decomp x 2 [w1'; w2'; w3'] R) /\
                  w3{1} = rcons w3' (phi_decomp x 3 [w1'; w2'; w3'] R)) /\
      forall (i : int),
        nth 0 w1{1} i + nth 0 w2{1} i + nth 0 w3{1} i =
        nth 0 (eval_circuit_aux [x] s) i /\ c{1} = x :: l /\ ={c, w1, w2}).
   + have Hgate := phi_sim_equiv x w1' w2' w3' s (eval_circuit_aux [x] s) _. smt().
     call Hgate. clear Hgate. clear IH.
     skip; progress.
     have Hgoal:
        (let (phi_w1, phi_w2, phi_w3) = result_L in
        (forall (i : int),
          nth 0 phi_w1 i + nth 0 phi_w2 i + nth 0 phi_w3 i =
          nth 0 (rcons s (eval_gate x s)) i) /\
        exists (R : random_tape),
          phi_w1 = rcons w1{1} (phi_decomp x 1 [w1{1}; w2{1}; w3{1}] R) /\
          phi_w2 = rcons w2{1} (phi_decomp x 2 [w1{1}; w2{1}; w3{1}] R) /\
          phi_w3 = rcons w3{1} (phi_decomp x 3 [w1{1}; w2{1}; w3{1}] R)) =>
        (exists (R : random_tape),
          result_L.`1 = rcons w1{1} (phi_decomp x 1 [w1{1}; w2{1}; w3{1}] R) /\
          result_L.`2 = rcons w2{1} (phi_decomp x 2 [w1{1}; w2{1}; w3{1}] R) /\
          result_L.`3 = rcons w3{1} (phi_decomp x 3 [w1{1}; w2{1}; w3{1}] R)) by smt().
    apply Hgoal. clear Hgoal. assumption.
    have Hgoal :
        (let (phi_w1, phi_w2, phi_w3) = result_L in
        (forall (i : int),
          nth 0 phi_w1 i + nth 0 phi_w2 i + nth 0 phi_w3 i =
          nth 0 (rcons s (eval_gate x s)) i) /\
        exists (R : random_tape),
          phi_w1 = rcons w1{1} (phi_decomp x 1 [w1{1}; w2{1}; w3{1}] R) /\
          phi_w2 = rcons w2{1} (phi_decomp x 2 [w1{1}; w2{1}; w3{1}] R) /\
          phi_w3 = rcons w3{1} (phi_decomp x 3 [w1{1}; w2{1}; w3{1}] R)) =>
        nth 0 result_L.`1 i + nth 0 result_L.`2 i + nth 0 result_L.`3 i =
        nth 0 (rcons s (eval_gate x s)) i by smt().
    apply Hgoal; clear Hgoal. assumption.
    rewrite pairS in H2. smt().
    rewrite pairS in H2. smt().
  elim*. progress.
  have IH' := (IH (rcons w1' (phi_decomp x 1 [w1'; w2'; w3'] R))
                  (rcons w2' (phi_decomp x 2 [w1'; w2'; w3'] R))
                  (rcons w3' (phi_decomp x 3 [w1'; w2'; w3'] R)) (eval_circuit_aux [x] s) s' _).
  smt(eval_circuit_aux_size size_rcons).
  call IH'. clear IH IH'.
  auto; progress.
  smt().
  smt().
  smt().
  smt().
  smt().
  have : result_L = (result_L.`1, result_L.`2, result_L.`3) by smt(). smt().
  have : result_L = (result_L.`1, result_L.`2, result_L.`3) by smt(). smt().
  have : result_L = (result_L.`1, result_L.`2, result_L.`3) by smt(). smt().
  have : result_L = (result_L.`1, result_L.`2, result_L.`3) by smt(). smt().
  have : result_L = (result_L.`1, result_L.`2, result_L.`3) by smt().
  rewrite pairS in H2. smt().
  have : result_L = (result_L.`1, result_L.`2, result_L.`3) by smt().
  rewrite pairS in H2. smt().
qed.


lemma privacy c' x' y':
    y' = eval_circuit c' [x'] =>
      equiv[Privacy.real ~ Privacy.ideal : (={c, e} /\ c{1} = c' /\ h{1} = x' /\ y{2} = y')
            ==> ={res}].
proof.
  progress.
  proc. inline Phi.output Phi.share.
  auto.
  seq 5 2 : (#pre /\ ={x1, x2} /\ x' = x1{1} + x2{1} + x3{1}).
  auto. progress. algebra.
  exists* x1{1}; exists* x2{1}; exists* x3{1}; elim*; progress.
  have Heq := phi_sim__circuit_equiv c' [x1_L] [x2_L] [x3_L] [x'] (eval_circuit_aux c' [x']) _.
  smt().
  call Heq. clear Heq. skip; progress.
  smt().
  have :
    (let (phi_w1, phi_w2, phi_w3) = result_L in
    (forall (i : int),
       nth 0 phi_w1 i + nth 0 phi_w2 i + nth 0 phi_w3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i) /\
    let (sim_w1, sim_w2) = result_R in sim_w1 = phi_w1 /\ sim_w2 = phi_w2)
    =>
    ((forall (i : int),
       nth 0 result_L.`1 i + nth 0 result_L.`2 i + nth 0 result_L.`3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i) /\
    result_R.`1 = result_L.`1 /\ result_R.`2 = result_L.`2).
  smt. progress.
  have : (forall (i : int),
       nth 0 result_L.`1 i + nth 0 result_L.`2 i + nth 0 result_L.`3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i) /\
    result_R.`1 = result_L.`1 /\ result_R.`2 = result_L.`2.
  smt().
  smt().
  have :
    (let (phi_w1, phi_w2, phi_w3) = result_L in
    (forall (i : int),
       nth 0 phi_w1 i + nth 0 phi_w2 i + nth 0 phi_w3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i) /\
    let (sim_w1, sim_w2) = result_R in sim_w1 = phi_w1 /\ sim_w2 = phi_w2)
    =>
    ((forall (i : int),
       nth 0 result_L.`1 i + nth 0 result_L.`2 i + nth 0 result_L.`3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i) /\
    result_R.`1 = result_L.`1 /\ result_R.`2 = result_L.`2).
  smt. progress.
  have : (forall (i : int),
       nth 0 result_L.`1 i + nth 0 result_L.`2 i + nth 0 result_L.`3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i) /\
    result_R.`1 = result_L.`1 /\ result_R.`2 = result_L.`2.
  smt().
  smt().
  have :
    (let (phi_w1, phi_w2, phi_w3) = result_L in
    (forall (i : int),
       nth 0 phi_w1 i + nth 0 phi_w2 i + nth 0 phi_w3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i) /\
    let (sim_w1, sim_w2) = result_R in sim_w1 = phi_w1 /\ sim_w2 = phi_w2)
    =>
    (forall (i : int),
       nth 0 result_L.`1 i + nth 0 result_L.`2 i + nth 0 result_L.`3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i).
  smt. progress.
  have : (forall (i : int),
       nth 0 result_L.`1 i + nth 0 result_L.`2 i + nth 0 result_L.`3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i).
  smt(). clear H1.
  progress.
  have:
    last 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) =
    last 0 result_L.`1 + last 0 result_L.`2 + last 0 result_L.`3.
  have Hlast := last_nth 0.
  rewrite !Hlast.
  simplify.
  have :
    let (phi_w1, phi_w2, phi_w3) = result_L in
    size (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) = size phi_w1 /\
    size phi_w1 = size phi_w2 /\
    size phi_w2 = size phi_w3 =>
    (size (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}])) = (size result_L.`1) /\
    (size result_L.`2) = (size result_L.`1) /\
    (size result_L.`3) = (size result_L.`1).
  smt().
  have :
    let (phi_w1, phi_w2, phi_w3) = result_L in
    size (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) = size phi_w1 /\
    size phi_w1 = size phi_w2 /\
    size phi_w2 = size phi_w3 /\
    (forall (i : int),
       nth 0 phi_w1 i + nth 0 phi_w2 i + nth 0 phi_w3 i =
       nth 0 (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) i) /\
    let (sim_w1, sim_w2) = result_R in sim_w1 = phi_w1 /\ sim_w2 = phi_w2 =>
    let (phi_w1, phi_w2, phi_w3) = result_L in
    size (eval_circuit_aux c{2} [x1{2} + x2{2} + x3{1}]) = size phi_w1 /\
    size phi_w1 = size phi_w2 /\
    size phi_w2 = size phi_w3.
  smt().
  smt().
  progress.
  rewrite /eval_circuit.
  rewrite H2. smt().

  rewrite nth_cat.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.

  elim c'; progress.
  - proc. inline Phi.output Phi.share.
    auto. 
    have Hgate := compute_circuit_correct [] [x1_L] [x2_L] [x3_L] [x'] (eval_circuit_aux [] [x']) _.
    trivial. 
    call{1} Hgate.
    inline *.
    sp. rcondf{2} 1. progress. auto.
    progress. smt().
    have :
      nth 0 result.`1 0 + nth 0 result.`2 0 + nth 0 result.`3 0 = x1{2} + x2{2} + x3{1}
        => result = ([x1{2}], [x2{2}], [x3{1}]).
    progress. 
    case ()

    case (e{1} = 1). progress.
    auto. progress. 
    progress. apply dinput_ll.
    elim


lemma phi_circuit_equiv &m x' c':
    Pr[Phi.main(x', c') @ &m : res = eval_circuit c' [x'] ] = 1%r.
proof.
    byphoare(: h = x' /\ c = c' ==> _)=>//.
    proc. inline Phi.reconstruct Phi.output Phi.share. auto.
    have Hsize : 0 <= (size c') by smt.
    seq 4 : (#pre /\ x' = x10 + x20 + x30).
    - auto.
    - auto. progress. apply dinput_ll. algebra.
    sp.
    exists* x1; exists* x2; exists* x3; elim*. progress.
    have Hcompute := compute_circuit_correct c' [x1] [x2] [x3] [x'] (eval_circuit_aux c' [x']) _.
    smt().
    call Hcompute. clear Hcompute.
    auto.
    progress.
    smt().
    have Hgoal :
      (forall i,
        (nth 0 result.`1) i +
        (nth 0 result.`2) i +
        (nth 0 result.`3) i =
        (nth 0 (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}]) i)) =>
      (last 0 result.`1 +
       last 0 result.`2 +
       last 0 result.`3 = eval_circuit c{hr} [x10{hr} + x20{hr} + x30{hr}]).
      progress. have Hlast := last_nth 0 0. rewrite !Hlast. clear Hlast.
      have Hsizes : size (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}]) = size result.`1 /\
    size result.`1 = size result.`2 /\ size result.`2 = size result.`3. 
      have H':
        (let (w1', w2', w3') = result in
            (forall (i : int),
              nth 0 w1' i + nth 0 w2' i + nth 0 w3' i =
              nth 0 (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}]) i) /\
            size (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}]) = size w1' /\
            size w1' = size w2' /\ size w2' = size w3')
              => size (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}]) = size result.`1 /\
            size result.`1 = size result.`2 /\ size result.`2 = size result.`3 by smt().
      apply H'. clear H'. assumption.
      have : (size result.`1) = (size (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}])) by smt().
      have : (size result.`1) = (size result.`2) by smt().
      have : (size result.`2) = (size result.`3) by smt().
      progress. smt().
      apply Hgoal. clear Hgoal. 
      progress. 
      have Hcorrect: 
        (forall (i : int),
          nth 0 result.`1 i + nth 0 result.`2 i + nth 0 result.`3 i =
          nth 0 (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}]) i).
      have H':
        (let (w1', w2', w3') = result in
            (forall (i : int),
              nth 0 w1' i + nth 0 w2' i + nth 0 w3' i =
              nth 0 (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}]) i) /\
            size (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}]) = size w1' /\
            size w1' = size w2' /\ size w2' = size w3') =>
        (forall (i : int),
          nth 0 result.`1 i + nth 0 result.`2 i + nth 0 result.`3 i =
          nth 0 (eval_circuit_aux c{hr} [x10{hr} + x20{hr} + x30{hr}]) i) by smt().
      apply H'. clear H'. assumption.
      apply Hcorrect.

    hoare. auto. progress. algebra.
    trivial.
qed.
