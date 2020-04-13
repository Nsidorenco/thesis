(* Formalization of MPC Phi decomposition *)
require import AllCore Distr List.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

type input = int.
type output = int.
type view = int list.

type gate = [
  | ADDC of (int * int)
  | MULTC of (int * int)
  | MULT of (int * int)
  | ADD of (int * int)
].

type circuit = gate list.
type state = int list.

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

op eval_circuit_aux(c : circuit, s : state) : state =
    with c = [] => s
    with c = g :: gs =>
     let r = eval_gate g s in
     eval_circuit_aux gs (rcons s r).

op eval_circuit (c : circuit, s : state) : output =
    last 0 (eval_circuit_aux c s).

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

op simulator_eval (g : gate, p : int, e : int, w : view list, R : random_tape) =
with g = MULT inputs =>
  if (e = 1) then (if (p = 2) then (nth 0 R 2) else phi_decomp g 1 w R)
  else if (e = 2) then (if (p = 2) then (nth 0 R 0) else phi_decomp g 2 ([[]] ++ w) R)
  else (if (p = 2) then (nth 0 R 1) else phi_decomp g 3 ([(last [] w)]++[[]]++[(head [] w)]) R)
with g = ADDC inputs =>
    if (e = 1) then phi_decomp g p w R else
    if (e = 2) then phi_decomp g (p+1) ([[]] ++ w) R else
    if (p = 1) then phi_decomp g 3 ([(last [] w)]++[[]]++[(head [] w)]) R else
    phi_decomp g 1 ([(last [] w)]++[[]]++[(head [] w)]) R
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
  proc compute(c : circuit, e : int, w1 w2 : view) = {
    var g, k1, k2, k3, r1, r2;
    while (c <> []) {
      g = head (ADDC(0,0)) c;
      k1 <$ dinput;
      k2 <$ dinput;
      k3 <$ dinput;
      r1 = simulator_eval g 1 e [w1;w2] [k1;k2;k3];
      r2 = simulator_eval g 2 e [w1;w2] [k1;k2;k3];
      w1 = (rcons w1 r1);
      w2 = (rcons w2 r2);
      c = behead c;
    }

    return (w1, w2);
  }
  proc compute_stepped(c : circuit, e : int, w1 w2 : view) = {
    (w1, w2) = compute([head (ADDC(0,0)) c], e, w1, w2);
    c = behead c;
    (w1, w2) = compute(c, e, w1, w2);
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
    (w1, w2) = Simulator.compute(c, e, [x1], [x2]);
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
  rewrite !nth_rcons.
  have <- : (size w1{hr} = size w2{hr}) by smt().
  have <- : (size w1{hr} = size w3{hr}) by smt().
  rewrite H.
  case (i < size w1{hr}); progress.
  apply H2.
  case (i = size w1{hr}); progress.
  elim g; progress; smt().
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
    + auto. call Hgate. clear Hgate.
      skip. move=> *.
      split; smt().

      elim*; progress.
      have Hind' := (Hind (rcons w1{m} (phi_decomp x 1 [w1{m}; w2{m}; w3{m}] R))
                          (rcons w2{m} (phi_decomp x 2 [w1{m}; w2{m}; w3{m}] R))
                          (rcons w3{m} (phi_decomp x 3 [w1{m}; w2{m}; w3{m}] R)) (eval_circuit_aux [x] s) s' _).
      do ? split=>//; smt(eval_circuit_aux_size size_rcons).
      call Hind'. clear Hind Hind'.
      auto. move=> ? ?.
      split; smt().
    + hoare. inline *. sp.
      rcondt 1. progress.
      auto. rcondf 12. progress.
      auto. auto. progress. smt().
      clear Hgate H Hs'rel. elim x; progress;
      elim x; move=> x1 x2; rewrite !nth_rcons; smt().
    trivial.
qed.


lemma phi_sim_equiv g e':
    (forall w1' w2' w3' s s',
      size s = size w1' /\
      size s = size w2' /\
      size s = size w3' /\
      s' = eval_circuit_aux [g] s =>
      equiv[Phi.compute ~ Simulator.compute :
            (if (e' = 1) then ={w1, w2}
              else
              (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2}
                else w3{1} = w1{2} /\ w1{1} = w2{2})) /\
             ={c} /\ e{2} = e' /\ c{1} = [g] /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{1} = w3' /\
             (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s i))
            ==>
            (let (phi_w1, phi_w2, phi_w3) = res{1} in
              (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 s' i)) /\
              (exists R, phi_w1 = (rcons w1' (phi_decomp g 1 [w1';w2';w3'] R)) /\
                         phi_w2 = (rcons w2' (phi_decomp g 2 [w1';w2';w3'] R)) /\
                         phi_w3 = (rcons w3' (phi_decomp g 3 [w1';w2';w3'] R))) /\
            (if e' = 1 then
              let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w1, phi_w2)
            else
              (if e' = 2 then
                let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w2, phi_w3)
              else
                let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w3, phi_w1))))]).
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
    case (e' = 1); progress.
    seq 2 2 : (#pre /\ ={k1, k2}). auto; smt().
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
      smt().
    case (e' = 2); progress.
    (* rnd. rnd. rnd. auto. *)
    swap 1 2.
    seq 2 2 : (#pre /\ ={k2, k3}). auto; smt().
    elim g; progress; last first.
    (* Discharge trivial case: ADDC MULTC ADD *)
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    - (* MULT *)
      elim x=> x1 x2.
      rnd (fun z => (nth 0 w3{1} x1 * nth 0 w3{1} x2 + nth 0 w1{1} x1 * nth 0 w3{1} x2 + nth 0 w3{1} x1 * nth 0 w1{1} x2 + k3{2} - z)).
      skip. progress.
      algebra.
      apply dinput_funi. smt().
      algebra.
      smt(nth_rcons).
      exists [k1L;k2{2};k3{2}].
      smt().
      smt().
      smt().
    swap 2 1.
    seq 2 2 : (#pre /\ ={k1, k3}). auto; smt().
    elim g; progress; last first.
    (* Discharge trivial case: ADDC MULTC ADD *)
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    - (* MULT *)
      elim x=> x1 x2.
      rnd (fun z => (nth 0 w1{1} x1 * nth 0 w1{1} x2 + nth 0 w2{1} x1 * nth 0 w1{1} x2 + nth 0 w1{1} x1 * nth 0 w2{1} x2 + k1{2} - z)).
      skip. progress.
      algebra.
      apply dinput_funi. smt().
      algebra.
      smt(nth_rcons).
      exists [k1{2};k2L;k3{2}].
      smt().
      smt().
      smt().
      smt().
      smt().
      smt().
      smt().
qed.


lemma phi_sim__circuit_equiv c' e':
    (forall w1' w2' w3' s s',
      size s = size w1' /\
      size s = size w2' /\
      size s = size w3' /\
      s' = eval_circuit_aux c' s =>
      equiv[Phi.compute ~ Simulator.compute :
            (if (e' = 1) then ={w1, w2}
              else
              (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2}
                else w3{1} = w1{2} /\ w1{1} = w2{2})) /\
             ={c} /\ e{2} = e' /\ c{1} = c' /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{1} = w3' /\
             (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s i))
            ==>
            (let (phi_w1, phi_w2, phi_w3) = res{1} in
              (size phi_w1) = (size phi_w2) /\ (size phi_w2 = size phi_w3) /\
              (size phi_w1) = (size s') /\
              (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 s' i)) /\
            (if e' = 1 then
              let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w1, phi_w2)
            else
              (if e' = 2 then
                let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w2, phi_w3)
              else
                let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w3, phi_w1))))]).
proof.
  elim c'.
  - (* empty circuit *)
    progress.
    proc.
    rcondf{1} 1. progress.
    rcondf{2} 1. progress.
    skip; progress; smt().
  - (* Inductive case *)
    move=> x l IH.
    move=> w1' w2' w3' s s'.
    move=> [Hs1 [Hs2 [Hs3 Hs']]].
    transitivity
      Phi.compute_stepped
      (={c, w1, w2, w3} /\
      c{1} = (x::l) /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{1} = w3'
      ==> ={res})
      ((if (e' = 1) then ={w1, w2}
        else
        (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2}
          else w3{1} = w1{2} /\ w1{1} = w2{2})) /\
        ={c} /\ e{2} = e' /\ c{1} = (x::l) /\ w1{1} = w1' /\ w2{1} = w2' /\ w3{1} = w3' /\
        (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s i)) ==>
          (let (phi_w1, phi_w2, phi_w3) = res{1} in
            (size phi_w1) = (size phi_w2) /\ (size phi_w2 = size phi_w3) /\
            (size phi_w1) = (size s') /\
            (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 s' i)) /\
          (if e' = 1 then
            let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w1, phi_w2)
          else
            (if e' = 2 then
              let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w2, phi_w3)
            else
              let (sim_w1, sim_w2) = res{2} in (sim_w1, sim_w2) = (phi_w3, phi_w1))))).
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
    (* (={c, e, w1, w2} /\ *)
    (*   c{1} = (x::l) /\ w1{1} = w1' /\ w2{1} = w2' /\ e{1} = e' *)
    (={c, w1, w2, e} /\ c{1} = (x::l)
     ==>
     ={res})
    ((if (e' = 1) then ={w1, w2}
       else
       (if (e' = 2) then w2{2} = w1{1} /\ w3{2} = w2{1}
         else w3{2} = w1{1} /\ w1{2} = w2{1})) /\
       ={c} /\ e{1} = e' /\ c{2} = (x::l) /\ w1{2} = w1' /\ w2{2} = w2' /\ w3{2} = w3' /\
       (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 s i))
     ==>
     (let (phi_w1, phi_w2, phi_w3) = res{2} in
       (size phi_w1) = (size phi_w2) /\ (size phi_w2 = size phi_w3) /\
       (size phi_w1) = (size s') /\
       (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 s' i)) /\
     (if e' = 1 then
       let (sim_w1, sim_w2) = res{1} in (sim_w1, sim_w2) = (phi_w1, phi_w2)
     else
       (if e' = 2 then
         let (sim_w1, sim_w2) = res{1} in (sim_w1, sim_w2) = (phi_w2, phi_w3)
       else
         let (sim_w1, sim_w2) = res{1} in (sim_w1, sim_w2) = (phi_w3, phi_w1))))).
  + progress; smt.
  + progress; smt.
  + (* proof Simulator.compute ~ Simulator.compute_stepped *)
    clear IH. proc. inline *. sp.
    unroll{1} 1; unroll{2} 1.
    if; progress.
    sp. seq 3 3 : (#pre /\ ={k1, k2, k3}); auto.
    rcondf{2} 6. auto.
    sp. elim *; progress.
    while (c1{2} = c{1} /\ e1{2} = e{1} /\ w11{2} = w1{1} /\ w21{2} = w2{1}); auto.
    rcondf{1} 1. progress.
    rcondf{2} 1. progress.
    sp. elim*. progress.
    rcondf{2} 1. progress.
    auto.
  (* main proof *)
  symmetry.
  proc.
  seq 1 1 : (
      (exists R,  w1{1} = rcons w1' (phi_decomp x 1 [w1'; w2'; w3'] R) /\
                  w2{1} = rcons w2' (phi_decomp x 2 [w1'; w2'; w3'] R) /\
                  w3{1} = rcons w3' (phi_decomp x 3 [w1'; w2'; w3'] R)) /\
      (forall (i : int),
        nth 0 w1{1} i + nth 0 w2{1} i + nth 0 w3{1} i =
        nth 0 (eval_circuit_aux [x] s) i /\ c{1} = x :: l) /\
      (if (e' = 1) then ={w1, w2}
        else
        (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2}
          else w3{1} = w1{2} /\ w1{1} = w2{2})) /\
        ={c} /\ e{2} = e' /\ c{1} = (x::l)).
   + have Hgate := phi_sim_equiv x e' w1' w2' w3' s (eval_circuit_aux [x] s) _. smt().
     call Hgate. clear Hgate. clear IH.
     skip. move=> *.
     split; smt().
  elim*. progress.
  have IH' := (IH (rcons w1' (phi_decomp x 1 [w1'; w2'; w3'] R))
                  (rcons w2' (phi_decomp x 2 [w1'; w2'; w3'] R))
                  (rcons w3' (phi_decomp x 3 [w1'; w2'; w3'] R)) (eval_circuit_aux [x] s) s' _).
  smt(eval_circuit_aux_size size_rcons).
  call IH'. clear IH IH'.
  auto. move => *.
  split; smt().
qed.


lemma privacy c' x' y' e':
    y' = eval_circuit c' [x'] =>
      equiv[Privacy.real ~ Privacy.ideal : (={c, e} /\ c{1} = c' /\ h{1} = x' /\ y{2} = y' /\ e{1} = e')
            ==> ={res}].
proof.
  progress.
  proc. inline Phi.output Phi.share.
  auto.

  case (e' = 1).
  - seq 5 2 : (#pre /\ ={x1, x2} /\ x' = x1{1} + x2{1} + x3{1}).
    auto; progress; algebra.
    exists* x1{1}; exists* x2{1}; exists* x3{1}; elim*; progress.
    have Heq := phi_sim__circuit_equiv c' e' [x1_L] [x2_L] [x3_L] [x'] (eval_circuit_aux c' [x']) _.
    smt().
    call Heq. clear Heq.
    skip. move=> *.
    have Hlast := last_nth 0.
    rewrite /eval_circuit.
    split; smt().

  case (e' = 2).
  - seq 5 2 : (#pre /\ x1{2} = x2{1} /\ x3{1} = x2{2} /\ x' = x1{1} + x2{1} + x3{1}).
    sp; wp.
    swap{1} 2 - 1.
    rnd (fun z => h{1} - x20{1} - z).
    rnd.
    skip; smt(dinput_funi dinput_fu).
    exists* x1{1}; exists* x2{1}; exists* x3{1}; elim*; progress.
    have Heq := phi_sim__circuit_equiv c' e' [x1_L] [x2_L] [x3_L] [x'] (eval_circuit_aux c' [x']) _.
    smt().
    call Heq. clear Heq.
    skip. move=> *.
    have Hlast := last_nth 0.
    rewrite /eval_circuit.
    split; smt().

 (* case e' = 3 *)
  - seq 5 2 : (#pre /\ x1{2} = x3{1} /\ x1{1} = x2{2} /\ x' = x1{1} + x2{1} + x3{1}).
    sp; wp.
    swap{2} 2 - 1.
    rnd (fun z => h{1} - x10{1} - z).
    rnd.
    skip; smt(dinput_funi dinput_fu).
    exists* x1{1}; exists* x2{1}; exists* x3{1}; elim*; progress.
    have Heq := phi_sim__circuit_equiv c' e' [x1_L] [x2_L] [x3_L] [x'] (eval_circuit_aux c' [x']) _.
    smt().
    call Heq. clear Heq.
    skip. move=> *.
    have Hlast := last_nth 0.
    rewrite /eval_circuit.
    split; smt().
qed.
