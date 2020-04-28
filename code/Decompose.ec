(* Formalization of MPC Phi decomposition *)
require import AllCore Distr List IntDiv.
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

op phi_decomp (g : gate, p : int, w1 w2 : view, k1 k2 : int) : output =
with g = ADDC inputs =>
    let (i, c) = inputs in
    let x = (nth 0 w1 i) in
    if p = 1 then x + c else x
with g = MULTC inputs =>
    let (i, c) = inputs in
    let x = (nth 0 w1 i) in x * c
with g = ADD inputs =>
    let (i, j) = inputs in
    let x = (nth 0 w1 i) in
    let y = (nth 0 w1 j) in x + y
with g = MULT inputs =>
    let (i, j) = inputs in
    let xp = (nth 0 w1 i) in
    let yp = (nth 0 w1 j) in
    let xp' = (nth 0 w2 i) in
    let yp' = (nth 0 w2 j) in
    xp * yp + xp' * yp + xp * yp' + k1 - k2.

op simulator_eval (g : gate, p : int, e : int, w1 w2 : view, k1 k2 k3: int) =
with g = MULT inputs =>
  if (p - e %% 3 = 1) then k3 else phi_decomp g p w1 w2 k1 k2
  (* if p = 1 then phi_decomp g p w1 w2 k1 k2 else *)
  (* if p = 2 then phi_decomp g p w1 w2 k2 k3 else *)
with g = ADDC inputs =>
    phi_decomp g p w1 w2 k1 k2
with g = MULTC inputs => phi_decomp g p w1 w2 k1 k2
with g = ADD inputs => phi_decomp g p w1 w2 k1 k2.


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
  proc compute(c : circuit, w1 w2 w3 : view, k1 k2 k3 : random_tape) = {
    var g, r1, r2, r3, v1, v2, v3;
    while (c <> []) {
      g = oget (ohead c);
      r1 <$ dinput;
      r2 <$ dinput;
      r3 <$ dinput;
      v1 = phi_decomp g 1 w1 w2 r1 r2;
      v2 = phi_decomp g 2 w2 w3 r2 r3;
      v3 = phi_decomp g 3 w3 w1 r3 r1;
      w1 = (rcons w1 v1);
      w2 = (rcons w2 v2);
      w3 = (rcons w3 v3);
      k1 = (rcons k1 r1);
      k2 = (rcons k2 r2);
      k3 = (rcons k3 r3);
      c = behead c;
    }
    return (k1, k2, k3, w1, w2, w3);
  }
  proc compute_stepped(c : circuit, w1 w2 w3 : view, k1 k2 k3 : random_tape) = {
    (k1, k2, k3, w1, w2, w3) = compute([head (ADDC(0,0)) c], w1, w2, w3, k1, k2, k3);
    c = behead c;
    (k1, k2, k3, w1, w2, w3) = compute(c, w1, w2, w3, k1, k2, k3);
    return (k1, k2, k3, w1, w2, w3);

  }
  proc main(h : input, c : circuit) = {
    var x1, x2, x3, y, w1, w2, w3, y1, y2, y3, k1, k2, k3;
    (x1, x2, x3) = share(h);
    k1 = [];
    k2 = [];
    k3 = [];
    (k1, k2, k3, w1, w2, w3) = compute(c, [x1], [x2], [x3], k1, k2, k3);
    y1 = output(w1);
    y2 = output(w2);
    y3 = output(w3);
    y = reconstruct(y1, y2, y3);
    return y;
  }
}.

module Simulator = {
  proc compute(c : circuit, e : int, w1 w2 : view, k1 k2 : random_tape) = {
    var g, r1, r2, r3, v1, v2, p1, p2;
    if (e = 1) {
      p1 = 1;
      p2 = 2;
    } else {
      if (e = 2) {
        p1 = 2;
        p2 = 3;
      } else {
        p1 = 3;
        p2 = 1;
      }
    }
    while (c <> []) {
      g = oget (ohead c);
      r1 <$ dinput;
      r2 <$ dinput;
      r3 <$ dinput;
      v1 = simulator_eval g p1 e w1 w2 r1 r2 r3;
      v2 = simulator_eval g p2 e w2 w1 r1 r2 r3;
      w1 = (rcons w1 v1);
      w2 = (rcons w2 v2);
      k1 = (rcons k1 r1);
      k2 = (rcons k2 r2);
      c = behead c;
    }

    return (k1, k2, w1, w2);
  }
  proc compute_stepped(c : circuit, e : int, w1 w2 : view, k1 k2 : random_tape) = {
    (k1, k2, w1, w2) = compute([head (ADDC(0,0)) c], e, w1, w2, k1, k2);
    c = behead c;
    (k1, k2, w1, w2) = compute(c, e, w1, w2, k1, k2);
    return (k1, k2, w1, w2);

  }
}.

module Privacy = {
  proc real(h : input, c : circuit, e : int) = {
    var x1, x2, x3, w1, w2, w3, y1, y2, y3, ret, k1, k2, k3;
    (x1, x2, x3) = Phi.share(h);
    k1 = [];
    k2 = [];
    k3 = [];
    (k1, k2, k3, w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3], k1, k2, k3);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);
    if (e = 1) {
      ret = ((k1, w1, k2, w2), y3);
    } else {
      if (e = 2) {
        ret = ((k2, w2, k3, w3), y1);
      } else {
        ret = ((k3, w3, k1, w1), y2);
      }
    }

    return ret;
  }

  proc ideal(y : output, c : circuit, e : int) = {
    var x1, x2, w1, w2, y1, y2, y3, k1, k2;
    x1 <$ dinput;
    x2 <$ dinput;
    k1 = [];
    k2 = [];
    (k1, k2, w1, w2) = Simulator.compute(c, e, [x1], [x2], k1, k2);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = y - (y1 + y2);

    return ((k1, w1, k2, w2), y3);
  }
}.

lemma compute_gate_correct g:
    (forall s,
      phoare[Phi.compute :
        (c = [g] /\ size s = size w1 /\ size s = size w2 /\ size s = size w3 /\
        (forall i, (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i)))
        ==>
        let (k1, k2, k3, w1res, w2res, w3res) = res in
          let s' = (eval_circuit_aux [g] s) in
        (forall i, (nth 0 w1res i) + (nth 0 w2res i) + (nth 0 w3res i) = (nth 0 s' i))
         /\ size s' = size w1res /\ size s' = size w2res /\ size s' = size w3res]=1%r).
proof.
  progress. proc.
  rcondt 1. progress.
  sp. rcondf 14. auto. auto. progress.
  apply dinput_ll.
  rewrite !nth_rcons.
  have <- : (size w1{hr} = size w2{hr}) by smt().
  have <- : (size w1{hr} = size w3{hr}) by smt().
  case (i < size w1{hr}); progress.
  rewrite H0. smt().
  case (i = size w1{hr}); progress.
  rewrite H.
  simplify.
  elim g; progress; smt().
  smt().
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
qed.

lemma eval_circuit_aux_size g s:
    size (eval_circuit_aux [g] s) = size s + 1 by smt.

lemma compute_circuit_correct c':
    (forall s,
      phoare[Phi.compute :
        ( c = c' /\ size s = size w1 /\ size s = size w2  /\ size s = size w3 /\
        (forall i, (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i)))
        ==>  let (k1', k2', k3', w1', w2', w3') = res in
        (forall i, (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 (eval_circuit_aux c' s) i))
        /\ size (eval_circuit_aux c' s) = size w1' /\ size w1' = size w2' /\ size w2' = size w3'] = 1%r).
proof.
  elim c'.
  - progress. proc. rcondf 1; progress. auto. progress; smt().
  - move=> x l Hind s.
    (* move=> [Hs1 [Hs2 [Hs3 Hs'rel]]]. *)
    bypr=> &m. progress.
    have -> :
      Pr[Phi.compute(c{m}, w1{m}, w2{m}, w3{m}, k1{m}, k2{m}, k3{m}) @ &m :
        let (k1', k2', k3, w1', w2', w3') = res in
        (forall (i : int),
            nth 0 w1' i + nth 0 w2' i + nth 0 w3' i =
          nth 0 (eval_circuit_aux (x::l) s) i)
        /\ size (eval_circuit_aux l (rcons s (eval_gate x s))) = size w1' /\ size w1' = size w2' /\ size w2' = size w3'] =
      Pr[Phi.compute_stepped(x::l, w1{m}, w2{m}, w3{m}, k1{m}, k2{m}, k3{m}) @ &m :
        let (k1', k2', k3, w1', w2', w3') = res in
        (forall (i : int),
            nth 0 w1' i + nth 0 w2' i + nth 0 w3' i =
          nth 0 (eval_circuit_aux (x::l) s) i)
        /\ size (eval_circuit_aux l (rcons s (eval_gate x s))) = size w1' /\ size w1' = size w2' /\ size w2' = size w3'].
      + byequiv=>//. clear Hind.
        proc. inline *. sp.
        unroll{1} 1; unroll{2} 1.
        if; progress. smt().
        + wp.
          rcondf{2} 15; auto.
          while (c1{2} = c{1} /\ w11{2} = w1{1} /\ w21{2} = w2{1} /\ w31{2} = w3{1} /\ k1{1} = k11{2});
          auto; smt().
        + exfalso; smt().
    byphoare(: c = (x::l) /\ w1 = w1{m} /\ w2 = w2{m} /\ w3 = w3{m} /\ k1 = k1{m} /\ k2 = k2{m} /\ k3 = k3{m} ==>)=>//.
    proc.
    have Hgate := compute_gate_correct x s.
    have Hind' := (Hind (eval_circuit_aux [x] s)).
    call Hind'. wp.
    call Hgate. clear Hind Hind' Hgate.
    skip; progress.
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
qed.

lemma correctness h' c' &m:
    Pr[Phi.main(h', c') @ &m : res = eval_circuit c' [h']] = 1%r.
proof.
  byphoare(: h = h' /\ c = c' ==> _)=>//.
  proc.
  inline Phi.output Phi.reconstruct Phi.share. auto.
  have H := compute_circuit_correct c' [h'].
  call H. clear H.
  auto; progress.
  apply dinput_ll.
  smt().
  have Hlast := last_nth 0.
  rewrite !Hlast.
  have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  smt().
qed.

lemma phi_sim_equiv g e':
    0 < e' /\ e' <= 3 =>
    (forall s,
      equiv[Phi.compute ~ Simulator.compute :
            size s = size w1{1} /\
            size s = size w2{1} /\
            size s = size w3{1} /\
            (if (e' = 1) then ={w1, w2, k1, k2}
              else
              (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
                else w3{1} = w1{2} /\ w1{1} = w2{2} /\ k3{1} = k1{2} /\ k1{1} = k2{2})) /\
             ={c} /\ e{2} = e' /\ c{1} = [g] /\
             (forall i, (nth 0 w1{1} i) + (nth 0 w2{1} i) + (nth 0 w3{1} i) = (nth 0 s i))
            ==>
            (let (k1, k2, k3, phi_w1, phi_w2, phi_w3) = res{1} in
              size (eval_circuit_aux [g] s) = size phi_w1 /\
              size (eval_circuit_aux [g] s) = size phi_w2 /\
              size (eval_circuit_aux [g] s) = size phi_w3 /\
              (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 (eval_circuit_aux [g] s) i)) /\
              (* (exists (k1, k2, k3), phi_w1 = (rcons w1{1} (phi_decomp g 1 w1' w2' k1 k2)) /\ *)
              (*                       phi_w2 = (rcons w2{1} (phi_decomp g 2 w2' w3' k2 k3)) /\ *)
              (*                       phi_w3 = (rcons w3{1} (phi_decomp g 3 w3' w1' k3 k1))) /\ *)
            (if e' = 1 then
              let (sim_k1, sim_k2, sim_w1, sim_w2) = res{2} in (sim_k1, sim_k2, sim_w1, sim_w2) = (k1, k2, phi_w1, phi_w2)
            else
              (if e' = 2 then
                let (sim_k1, sim_k2, sim_w1, sim_w2) = res{2} in (sim_k1, sim_k2, sim_w1, sim_w2) = (k2, k3, phi_w2, phi_w3)
              else
                let (sim_k1, sim_k2, sim_w1, sim_w2) = res{2} in (sim_k1, sim_k2, sim_w1, sim_w2) = (k3, k1, phi_w3, phi_w1))))]).
proof.
    progress.
    proc.
    (* have Hs1 : size w1' = size w2' by smt(). *)
    (* have Hs2 : size w1' = size w3' by smt(). *)
    rcondt{1} 1. auto.
    rcondt{2} 2. auto.
    rcondf{1} 15. auto.
    rcondf{2} 13. auto.
    case (e' = 1); progress.
    rcondt{2} 1. auto.
    sp. wp.
    seq 2 2 : (#pre /\ ={r1, r2}). auto; smt().
    elim g; progress; last first.
    (* Discharge trivial case: ADDC MULTC ADD *)
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    - (* MULT *)
      elim x=> x1 x2.
      rnd (fun z => (nth 0 w2{2} x1 * nth 0 w2{2} x2 + nth 0 w3{1} x1 * nth 0 w2{2} x2 + nth 0 w2{2} x1 * nth 0 w3{1} x2 + r2{2} - z)).
      skip. progress.
      algebra.
      apply dinput_funi. smt().
      algebra.
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
      smt(nth_rcons).
      smt().
      smt().
      smt().
      smt().
    case (e' = 2); progress.
    (* rnd. rnd. rnd. auto. *)
    rcondf{2} 1. auto.
    rcondt{2} 1. auto.
    wp. sp.
    swap{1} 1 2.
    seq 2 2 : (#pre /\ r2{1} = r1{2} /\ r3{1} = r2{2}). auto; smt().
    elim g; progress; last first.
    (* Discharge trivial case: ADDC MULTC ADD *)
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    - (* MULT *)
      elim x=> x1 x2.
      rnd (fun z => (nth 0 w3{1} x1 * nth 0 w3{1} x2 + nth 0 w1{1} x1 * nth 0 w3{1} x2 + nth 0 w3{1} x1 * nth 0 w1{1} x2 + r2{2} - z)).
      skip. progress.
      algebra.
      apply dinput_funi. smt().
      algebra.
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
      smt(nth_rcons).
      smt().
      smt().
      smt().
      smt().

    case (e' = 3).
    rcondf{2} 1. auto.
    rcondf{2} 1. auto.
    wp. sp.
    swap{1} [1..2] 1.
    seq 2 2 : (#pre /\ r3{1} = r1{2} /\ r1{1} = r2{2}). auto; smt().
    elim g; progress; last first.
    (* Discharge trivial case: ADDC MULTC ADD *)
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    rnd; skip; progress; smt(nth_rcons size_rcons).
    - (* MULT *)
      elim x=> x1 x2.
      rnd (fun z => (nth 0 w1{1} x1 * nth 0 w1{1} x2 + nth 0 w2{1} x1 * nth 0 w1{1} x2 + nth 0 w1{1} x1 * nth 0 w2{1} x2 + r2{2} - z)).
      skip. progress.
      algebra.
      apply dinput_funi. smt().
      algebra.
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
      smt(nth_rcons).
      smt().
      smt().
      smt().
      smt().
  exfalso. smt().
qed.


lemma phi_sim_circuit_equiv c' e':
    0 < e' /\ e' <= 3 =>
    (forall s,
      (* s' = eval_circuit_aux c' s => *)
      equiv[Phi.compute ~ Simulator.compute :
            size s = size w1{1} /\
            size s = size w2{1} /\
            size s = size w3{1} /\
            (if (e' = 1) then ={w1, w2, k1, k2}
              else
              (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
                else w3{1} = w1{2} /\ w1{1} = w2{2} /\ k3{1} = k1{2} /\ k1{1} = k2{2})) /\
             ={c} /\ e{2} = e' /\ c{1} = c' /\
             (forall i, (nth 0 w1{1} i) + (nth 0 w2{1} i) + (nth 0 w3{1} i) = (nth 0 s i))
            ==>
            (let (k1, k2, k3, phi_w1, phi_w2, phi_w3) = res{1} in
              (size phi_w1) = (size phi_w2) /\ (size phi_w2 = size phi_w3) /\
              (size phi_w1) = (size (eval_circuit_aux c' s)) /\
              (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 (eval_circuit_aux c' s) i)) /\
            (if e' = 1 then
              res{2} = (k1, k2, phi_w1, phi_w2)
            else
              (if e' = 2 then
                res{2} = (k2, k3, phi_w2, phi_w3)
              else
                res{2} = (k3, k1, phi_w3, phi_w1))))]).
proof.
  move=> e_range.
  elim c'.
  - (* empty circuit *)
    progress.
    proc. sp.
    rcondf{1} 1. auto. smt().
    rcondf{2} 1. auto.
    auto. smt().
    auto. smt().
  - (* Inductive case *)
    move=> x l IH.
    move=> s.
    transitivity
      Phi.compute_stepped
      (={c, w1, w2, w3, k1, k2, k3} /\
      c{1} = (x::l)
      ==> ={res})
     (size s = size w1{1} /\
      size s = size w2{1} /\
      size s = size w3{1} /\
      (if (e' = 1) then ={w1, w2, k1, k2}
        else
        (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
          else w3{1} = w1{2} /\ w1{1} = w2{2} /\ k3{1} = k1{2} /\ k1{1} = k2{2})) /\
        ={c} /\ e{2} = e' /\ c{1} = (x::l) /\
        (forall i, (nth 0 w1{1} i) + (nth 0 w2{1} i) + (nth 0 w3{1} i) = (nth 0 s i)) ==>
          (let (k1, k2, k3, phi_w1, phi_w2, phi_w3) = res{1} in
            (size phi_w1) = (size phi_w2) /\ (size phi_w2 = size phi_w3) /\
            (size phi_w1) = (size (eval_circuit_aux (x::l) s)) /\
            (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 (eval_circuit_aux (x::l) s) i)) /\
          (if e' = 1 then
            res{2} = (k1, k2, phi_w1, phi_w2)
          else
            (if e' = 2 then
              res{2} = (k2, k3, phi_w2, phi_w3)
            else
              res{2} = (k3, k1, phi_w3, phi_w1))))).
    + progress; smt().
    + progress; smt().
    + (* proof Phi.compute ~ Phi.compute_stepped *)
      clear IH. proc. inline *. sp.
        unroll{1} 1; unroll{2} 1.
        if; progress.
        + wp.
          rcondf{2} 15; auto.
          while (c1{2} = c{1} /\ w11{2} = w1{1} /\ w21{2} = w2{1} /\ w31{2} = w3{1} /\ k1{1} = k11{2} /\ k2{1} = k21{2} /\ k3{1} = k31{2}).
          auto; progress.
          auto; progress.
        exfalso. smt().
  symmetry.
  transitivity
    Simulator.compute_stepped
    (* (={c, e, w1, w2} /\ *)
    (*   c{1} = (x::l) /\ w1{1} = w1' /\ w2{1} = w2' /\ e{1} = e' *)
    (={c, w1, w2, e, k1, k2} /\ c{1} = (x::l)
     ==>
     ={res})
    (size s = size w1{2} /\
     size s = size w2{2} /\
     size s = size w3{2} /\
    (if (e' = 1) then ={w1, w2, k1, k2}
      else
      (if (e' = 2) then w2{2} = w1{1} /\ w3{2} = w2{1} /\ k2{2} = k1{1} /\ k3{2} = k2{1}
        else w3{2} = w1{1} /\ w1{2} = w2{1} /\ k3{2} = k1{1} /\ k1{2} = k2{1})) /\
       ={c} /\ e{1} = e' /\ c{2} = (x::l) /\
       (forall i, (nth 0 w1{2} i) + (nth 0 w2{2} i) + (nth 0 w3{2} i) = (nth 0 s i))
     ==>
     (let (k1, k2, k3, phi_w1, phi_w2, phi_w3) = res{2} in
       (size phi_w1) = (size phi_w2) /\ (size phi_w2 = size phi_w3) /\
       (size phi_w1) = (size (eval_circuit_aux (x::l) s)) /\
       (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 (eval_circuit_aux (x::l) s) i)) /\
     (if e' = 1 then
       res{1} = (k1, k2, phi_w1, phi_w2)
     else
       (if e' = 2 then
         res{1} = (k2, k3, phi_w2, phi_w3)
       else
         res{1} = (k3, k1, phi_w3, phi_w1))))).
  + progress; smt.
  + progress; smt.
  + (* proof Simulator.compute ~ Simulator.compute_stepped *)
    clear IH. proc. inline *. sp.
    unroll{1} 1; unroll{2} 1.
    if; progress. smt(). smt().
    rcondf{2} 12. auto. smt().
    (* sp. elim *; progress. *)
    wp.
    while (c1{2} = c{1} /\ w11{2} = w1{1} /\ w21{2} = w2{1} /\ k1{1} = k11{2} /\ k2{1} = k21{2} /\ p1{1} = p10{2} /\ p2{1} = p20{2} /\ e{1} = e1{2}).
    auto. progress.
    auto. smt().

    exfalso. smt().
  (* main proof *)
  symmetry.
  proc. auto.
  seq 1 1 : (
      size (rcons s (eval_gate x s)) = size w1{1} /\
      size (rcons s (eval_gate x s)) = size w2{1} /\
      size (rcons s (eval_gate x s)) = size w3{1} /\
      (forall (i : int),
        nth 0 w1{1} i + nth 0 w2{1} i + nth 0 w3{1} i =
        nth 0 (eval_circuit_aux [x] s) i /\ c{1} = x :: l) /\
      (if (e' = 1) then ={w1, w2, k1, k2}
        else
        (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
          else w3{1} = w1{2} /\ w1{1} = w2{2} /\ k3{1} = k1{2} /\ k1{1} = k2{2})) /\
        ={c} /\ e{2} = e' /\ c{1} = (x::l)).
   + have Hgate := phi_sim_equiv x e' _ s.
      - smt().
     call Hgate. clear Hgate. auto.
     smt().
  have IH' := IH (eval_circuit_aux [x] s).
  call IH'. clear IH' IH.
  auto. progress.
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
  have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
  have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
  smt().
qed.


lemma privacy c' x' y' e':
    0 < e' /\ e' <= 3 =>
    y' = eval_circuit c' [x'] =>
      equiv[Privacy.real ~ Privacy.ideal : (={c, e} /\ c{1} = c' /\ h{1} = x' /\ y{2} = y' /\ e{1} = e')
            ==> ={res}].
proof.
  progress.
  proc. inline Phi.output Phi.share.
  auto.

  case (e' = 1).
  - have Heq := phi_sim_circuit_equiv c' e' _ [x'].
    smt().
    call Heq. clear Heq.
    auto. progress.
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    have Hlast := last_nth 0.
    rewrite /eval_circuit.
    smt().

  case (e' = 2).
  - seq 5 2 : (#pre /\ x1{2} = x2{1} /\ x3{1} = x2{2} /\ x' = x1{1} + x2{1} + x3{1}).
    sp; wp.
    swap{1} 2 - 1.
    rnd (fun z => h{1} - x20{1} - z).
    rnd.
    skip; smt(dinput_funi dinput_fu).
    exists* x1{1}; exists* x2{1}; exists* x3{1}; elim*; progress.
    have Heq := phi_sim_circuit_equiv c' e' _ [x'].
    smt().
    call Heq. clear Heq.
    auto; progress.
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    have Hlast := last_nth 0.
    rewrite /eval_circuit.
    smt().

 (* case e' = 3 *)
  - seq 5 2 : (#pre /\ x1{2} = x3{1} /\ x1{1} = x2{2} /\ x' = x1{1} + x2{1} + x3{1}).
    sp; wp.
    swap{2} 2 - 1.
    rnd (fun z => h{1} - x10{1} - z).
    rnd.
    skip; smt(dinput_funi dinput_fu).
    exists* x1{1}; exists* x2{1}; exists* x3{1}; elim*; progress.
    have Heq := phi_sim_circuit_equiv c' e' _ [x'].
    smt().
    call Heq. clear Heq.
    auto; progress.
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    smt().
    have : (result_L.`1, result_L.`2, result_L.`3, result_L.`4, result_L.`5, result_L.`6) = result_L by smt().
    have : (result_R.`1, result_R.`2, result_R.`3, result_R.`4) = result_R by smt().
    have Hlast := last_nth 0.
    rewrite /eval_circuit.
    smt().
qed.
