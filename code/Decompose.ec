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

(* lemma valid_tester : *)
(*     valid_circuit circuit_ex (size s'). *)
(*     rewrite /circuit_ex /s' /valid_circuit. *)
(*     progress. *)
(*     case (i = 0). *)
(*     progress. rewrite oget_some. trivial. *)
(*     case (i = 1). *)
(*     progress. rewrite oget_some. trivial. *)
(*     progress. smt(). *)
(* qed. *)


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

op phi_decomp (g : gate, idx, p : int, w1 w2 : view, k1 k2 : int list) : output =
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
    let r1 = (nth 0 k1 idx) in
    let r2 = (nth 0 k2 idx) in
    xp * yp + xp' * yp + xp * yp' + r1 - r2.

op simulator_eval (g : gate, idx, p : int, e : int, w1 w2 : view, k1 k2 k3: int list) =
with g = MULT inputs =>
  if (p - e %% 3 = 1) then (nth 0 k3 idx) else phi_decomp g idx p w1 w2 k1 k2
  (* if p = 1 then phi_decomp g p w1 w2 k1 k2 else *)
  (* if p = 2 then phi_decomp g p w1 w2 k2 k3 else *)
with g = ADDC inputs =>
    phi_decomp g idx p w1 w2 k1 k2
with g = MULTC inputs => phi_decomp g idx p w1 w2 k1 k2
with g = ADD inputs => phi_decomp g idx p w1 w2 k1 k2.


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
      k1 = (rcons k1 r1);
      k2 = (rcons k2 r2);
      k3 = (rcons k3 r3);
      v1 = phi_decomp g (size w1 - 1) 1 w1 w2 k1 k2;
      v2 = phi_decomp g (size w1 - 1) 2 w2 w3 k2 k3;
      v3 = phi_decomp g (size w1 - 1) 3 w3 w1 k3 k1;
      w1 = (rcons w1 v1);
      w2 = (rcons w2 v2);
      w3 = (rcons w3 v3);
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
  proc compute_stepped_reversed(c : circuit, g : gate, w1 w2 w3 : view, k1 k2 k3 : random_tape) = {
    (k1, k2, k3, w1, w2, w3) = compute(c, w1, w2, w3, k1, k2, k3);
    (k1, k2, k3, w1, w2, w3) = compute([g], w1, w2, w3, k1, k2, k3);
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
  proc compute(c : circuit, e : int, w1 w2 : view, k1 k2 k3 : random_tape) = {
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
      k1 = (rcons k1 r1);
      k2 = (rcons k2 r2);
      k3 = (rcons k3 r3);
      v1 = simulator_eval g (size w1 - 1) p1 e w1 w2 k1 k2 k3;
      v2 = simulator_eval g (size w1 - 1) p2 e w2 w1 k1 k2 k3;
      w1 = (rcons w1 v1);
      w2 = (rcons w2 v2);
      c = behead c;
    }

    return (k1, k2, k3, w1, w2);
  }
  proc compute_stepped(c : circuit, e : int, w1 w2 : view, k1 k2 k3 : random_tape) = {
    (k1, k2, k3, w1, w2) = compute([head (ADDC(0,0)) c], e, w1, w2, k1, k2, k3);
    c = behead c;
    (k1, k2, k3, w1, w2) = compute(c, e, w1, w2, k1, k2, k3);
    return (k1, k2, k3, w1, w2);
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
    var x1, x2, w1, w2, y1, y2, y3, k1, k2, k3;
    x1 <$ dinput;
    x2 <$ dinput;
    k1 = [];
    k2 = [];
    k3 = [];
    (k1, k2, k3, w1, w2) = Simulator.compute(c, e, [x1], [x2], k1, k2, k3);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = y - (y1 + y2);

    return ((k1, w1, k2, w2), y3);
  }
}.

lemma eval_gate_aux_size g s:
    size (eval_circuit_aux [g] s) = size s + 1 by smt.

lemma eval_circuit_aux_size c:
    (forall s,
      size (eval_circuit_aux c s) = size s + size c).
proof.
    elim c; progress.
    elim x; progress;
    case x=> x1 x2.
    simplify.
    smt.
    smt.
    smt.
    smt.
qed.

lemma eval_circuit_rcons c:
  (forall s g,
    (rcons (eval_circuit_aux c s) (eval_gate g (eval_circuit_aux c s))
    =
    eval_circuit_aux (rcons c g) s)).
proof.
  elim c; smt.
qed.

op highest_inwire (g : gate) =
  with g = MULT inputs => let (i, j) = inputs in max i j
  with g = ADD inputs =>  let (i, j) = inputs in max i j
  with g = ADDC inputs => let (i, c) = inputs in i
  with g = MULTC inputs => let (i, c) = inputs in i.


pred valid_gate (g : gate) idx =
  0 <= highest_inwire g /\ highest_inwire g <= idx.

pred valid_circuit (c : circuit) =
  forall i, (0 <= i /\ i < size c) =>
    valid_gate (oget (onth c i)) i.

lemma valid_circuit_rcons_head g c:
    valid_circuit (rcons c g) => valid_circuit c.
proof.
    rewrite /valid_circuit.
    progress.
    have := H i _. smt(size_rcons).
    have -> := onth_nth (ADDC(0,0)) (rcons c g) i _. smt(size_rcons).
    have -> := onth_nth (ADDC(0,0)) c i _. smt(size_rcons).
    rewrite nth_rcons.
    case (i < size c); move => Hi.
    smt().
    smt().
    have := H i _. smt(size_rcons).
    have -> := onth_nth (ADDC(0,0)) (rcons c g) i _. smt(size_rcons).
    have -> := onth_nth (ADDC(0,0)) c i _. smt(size_rcons).
    rewrite nth_rcons.
    case (i < size c); move => Hi.
    smt().
    smt().
qed.

lemma valid_circuit_rcons_tail g c:
    valid_circuit (rcons c g) => valid_gate g (size c).
proof.
    rewrite /valid_circuit /valid_gate.
    progress.
    have H' := H (size c) _.
    smt(size_ge0 size_rcons).
    smt.
    have H' := H (size c) _.
    smt(size_ge0 size_rcons).
    smt.
qed.

lemma gate_computation_order g i (p : int) (w1 w2 w1' w2' : view) k1 k2 k1' k2' :
    0 <= i /\ (i + 1 < size w1) /\ size w1 = size w2 /\ size k1 = size k2 /\ (size k1 = size w1 \/ size k1 = size w1 - 1) /\ valid_gate g i =>
    phi_decomp g i p w1 w2 k1 k2 = phi_decomp g i p (w1++w1') (w2++w2') (k1++k1') (k2++k2').
proof.
  elim g;
  move=> x; case x=> x1 x2;
  rewrite /valid_gate; progress;
  rewrite !nth_cat;
  smt().
qed.

lemma gate_computation_order_eq g i (p : int) (w1 w2 w1' w2' : view) k1 k2:
    (i = size w1 - 1) /\ size w1 = size w2 /\ size k1 = size k2 /\ size k1 = size w1 /\ valid_gate g i =>
    phi_decomp g i p w1 w2 k1 k2 = phi_decomp g i p (w1++w1') (w2++w2') k1 k2.
proof.
  elim g;
  move=> x; case x=> x1 x2;
  rewrite /valid_gate; progress;
  rewrite !nth_cat;
  smt().
qed.

lemma circuit_computation_order c:
    (forall i p w1 w2 w1' w2' k1 k2 k1' k2',
      0 <= i /\ size w1 = size w2 /\ i + 1 < size w1 /\ size k1 = size k2 /\ (size k1 = size w1 - 1 \/ size k1 = size w1) /\
      valid_circuit c =>
      phi_decomp (nth (ADDC(0,0)) c i) i p w1 w2 k1 k2 =
      phi_decomp (nth (ADDC(0,0)) c i) i p (w1++w1') (w2++w2') (k1++k1') (k2++k2')).
proof.
  elim /last_ind c; progress.
  smt().
  rewrite nth_rcons.
  case (i < size s); move=> Hi.
  progress.
  have H' := H i p w1 w2 w1' w2' k1 k2 k1' k2' _.
  smt(valid_circuit_rcons_head).
  apply H'.
  case (i = size s); move=> />.
  have Hgate := gate_computation_order x (size s) p w1 w2 w1' w2' k1 k2 k1' k2' _.
  smt(valid_circuit_rcons_tail size_ge0).
  apply Hgate.
  progress.
  smt().
qed.


(* TODO: change this lemma to preserve property *)
lemma compute_gate_correct g:
    (forall cprev s,
      phoare[Phi.compute :
        (c = [g] /\ size s = size w1 /\ size s = size w2 /\ size s = size w3 /\
          valid_gate g (size cprev) /\ valid_circuit cprev /\
          size cprev = size w1 - 1 /\
          size k1 = size k2 /\ size k1 = size w1 - 1 /\ size k1 = size k3 /\
          (forall i, 0 <= i /\ i < size w1 =>
            (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i)) /\
          (forall i, 0 <= i /\ i + 1 < size w1 =>
            (nth 0 w1 (i + 1)) = phi_decomp (nth (ADDC(0,0)) cprev i) i 1 w1 w2 k1 k2))
        ==>
        let (k1, k2, k3, w1res, w2res, w3res) = res in
          let s' = (eval_circuit_aux [g] s) in
        (forall i, 0 <= i /\ i < size w1res =>
          (nth 0 w1res i) + (nth 0 w2res i) + (nth 0 w3res i) = (nth 0 s' i)) /\
        (forall i, 0 <= i /\ i + 1 < size w1res =>
          (nth 0 w1res (i + 1)) = phi_decomp (nth (ADDC(0,0)) (cprev++[g]) i) i 1 w1res w2res k1 k2)
         /\ size (cprev ++ [g]) = size w1res - 1 /\ valid_gate g (size w1res - 1)
         /\ size k1 = size w1res - 1 /\ size k2 = size k1 /\ size k3 = size k1
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
  rewrite oget_some.
  have := H5.
  clear H14 H2 H15 H3 H16 H18 H19 H20.
  elim g; move=>x; case x=> i c; smt(nth_rcons nth_out).
  smt().
  rewrite !nth_rcons.
  rewrite nth_cat.
  case (i < size w1{hr}); progress.
  case (i < size cprev); progress.
  rewrite - !cats1.
  have Hvalid := gate_computation_order (nth (ADDC(0,0)) cprev i) i 1 w1{hr} w2{hr}
                                 [phi_decomp g (size w1{hr} - 1) 1 w1{hr} w2{hr} (k1{hr} ++ [v]) (k2{hr} ++ [v0])]
                                 [phi_decomp g (size w1{hr} - 1) 2 w2{hr} w3{hr} (k2{hr} ++ [v0]) (k3{hr} ++ [v4])]
                                 k1{hr} k2{hr} [v] [v0] _.
                                 rewrite /valid_circuit in H3.
                                 have := H3 i _. smt().
                                 have -> := onth_nth (ADDC(0,0)) cprev i _. smt().
                                 smt().

  rewrite - Hvalid.
  have : i + 1 < size w1{hr}. smt().
  progress.
  have := H8 i _. smt().
  smt(last_cat).
  have -> : i + 1 = size w1{hr}. smt().
  have : i = size cprev. smt().
  progress.
  rewrite oget_some - !cats1 - H4.
  have Hvalid := gate_computation_order_eq g (size cprev) 1 w1{hr} w2{hr}
                                 [phi_decomp g (size cprev) 1 w1{hr} w2{hr} (k1{hr} ++ [v]) (k2{hr} ++ [v0])]
                                 [phi_decomp g (size cprev) 2 w2{hr} w3{hr} (k2{hr} ++ [v0]) (k3{hr} ++ [v4])]
                                 (k1{hr}++[v]) (k2{hr}++[v0]) _. smt(size_cat).

  smt.
  case (i + 1 < size w1{hr}); progress.
  have := H8 i _. smt().
  case (i = size cprev); progress.
  rewrite oget_some - !cats1.
  have Hvalid := gate_computation_order_eq g (size cprev) 1 w1{hr} w2{hr}
                                 [phi_decomp g (size w1{hr} - 1) 1 w1{hr} w2{hr} (k1{hr} ++ [v]) (k2{hr} ++ [v0])]
                                 [phi_decomp g (size w1{hr} - 1) 2 w2{hr} w3{hr} (k2{hr} ++ [v0]) (k3{hr} ++ [v4])]
                                 (k1{hr}++[v]) (k2{hr}++[v0]) _. smt(size_cat).

  smt.
  smt().
  smt.
  smt(size_cat size_rcons).
  smt(size_cat size_rcons).
  smt(size_cat size_rcons).
  smt(size_cat size_rcons).
  smt(size_cat size_rcons).
  smt(size_cat size_rcons).
  smt(size_cat size_rcons).
  smt(size_cat size_rcons).
  smt(size_cat size_rcons).
qed.


lemma compute_circuit_correct c':
    (forall s cprev,
      phoare[Phi.compute :
        ( c = c' /\ size s = size w1 /\ size s = size w2  /\ size s = size w3 /\
          size k1 = size k2 /\ size k1 = size k3 /\ size k1 = size w1 - 1/\
          valid_circuit (cprev++c') /\ 0 < size s /\ size cprev = size w1 - 1 /\
          (forall i, 0 <= i /\ i < size w1 =>
              (nth 0 w1 i) + (nth 0 w2 i) + (nth 0 w3 i) = (nth 0 s i)) /\
          (forall i, 0 <= i /\ i + 1 < size w1 =>
              (nth 0 w1 (i + 1)) = phi_decomp (nth (ADDC(0,0)) (cprev) i) i 1 w1 w2 k1 k2))
        ==>  let (k1', k2', k3', w1', w2', w3') = res in
        (forall i, 0 <= i /\ i < size w1' =>
             (nth 0 w1' i) + (nth 0 w2' i) + (nth 0 w3' i) = (nth 0 (eval_circuit_aux c' s) i)) /\
        (forall i, 0 <= i /\ i + 1 < size w1' =>
            (nth 0 w1' (i + 1)) = phi_decomp (nth (ADDC(0,0)) (cprev++c') i) i 1 w1' w2' k1' k2')
        /\ size (cprev ++ c') = size w1' - 1
        /\ size k1' = size w1' - 1 /\ size k2' = size k1' /\ size k3' = size k1'
        /\ size (eval_circuit_aux c' s) = size w1' /\ size w1' = size w2' /\ size w2' = size w3'] = 1%r).
proof.
  elim /last_ind c'.
  - progress. proc; rcondf 1; progress; auto; smt(cats0).
  - move=> x l Hind s cprev.
    bypr=> &m. progress.
    rewrite H.
    have -> :
        Pr[Phi.compute(rcons x l, w1{m}, w2{m}, w3{m}, k1{m}, k2{m}, k3{m}) @ &m :
          let (k1', k2', k3', w1', w2', w3') = res in
          (forall (i : int),
              0 <= i /\ i < size w1' =>
              nth 0 w1' i + nth 0 w2' i + nth 0 w3' i =
              nth 0 (eval_circuit_aux (rcons x l) s) i) /\
          (forall (i : int),
              0 <= i /\ i + 1 < size w1' =>
              nth 0 w1' (i + 1) =
              phi_decomp (nth (ADDC (0, 0)) (cprev ++ rcons x l) i) i 1 w1' w2' k1'
                k2') /\
          size (cprev ++ rcons x l) = size w1' - 1 /\
          size k1' = size w1' - 1 /\
          size k2' = size k1' /\
          size k3' = size k1' /\
          size (eval_circuit_aux (rcons x l) s) = size w1' /\
          size w1' = size w2' /\ size w2' = size w3'] =
        Pr[Phi.compute_stepped_reversed(x, l, w1{m}, w2{m}, w3{m}, k1{m}, k2{m}, k3{m}) @ &m :
          let (k1', k2', k3', w1', w2', w3') = res in
          (forall (i : int),
              0 <= i /\ i < size w1' =>
              nth 0 w1' i + nth 0 w2' i + nth 0 w3' i =
              nth 0 (eval_circuit_aux (rcons x l) s) i) /\
          (forall (i : int),
              0 <= i /\ i + 1 < size w1' =>
              nth 0 w1' (i + 1) =
              phi_decomp (nth (ADDC (0, 0)) (cprev ++ rcons x l) i) i 1 w1' w2' k1'
                k2') /\
          size (cprev ++ rcons x l) = size w1' - 1 /\
          size k1' = size w1' - 1 /\
          size k2' = size k1' /\
          size k3' = size k1' /\
          size (eval_circuit_aux (rcons x l) s) = size w1' /\
          size w1' = size w2' /\ size w2' = size w3'].
      + byequiv=>//. clear Hind H.
        proc. inline *. sp.
        splitwhile{1} 1 : 1 < size c.
        sim : (={w1, w2, w3, k1, k2, k3}).
        (* sim : (={w1, w2, w3, k1, k2, k3}). *)
        (* Invariant that behead c{1} = [l] *)
        wp.
        while (c{1} = rcons c0{2} l /\ w10{2} = w1{1} /\ w20{2} = w2{1} /\ w30{2} = w3{1} /\ k1{1} = k10{2} /\ k2{1} = k20{2} /\ k3{1} = k30{2});
        auto; progress; smt(size_rcons size_ge0).
    byphoare(: c = x /\ g = l /\ w1 = w1{m} /\ w2 = w2{m} /\ w3 = w3{m} /\ k1 = k1{m} /\ k2 = k2{m} /\ k3 = k3{m} ==>)=>//.
    proc.
    have Hgate := compute_gate_correct l (cprev ++ x) (eval_circuit_aux x s).
    call Hgate.
    have Hind' := Hind s cprev.
    call Hind'.
    clear Hind Hind' Hgate.
    skip; progress.
    (* smt(valid_circuit_rcons_head rcons_cat nth_cat size_rcons size_cat size_ge0 eval_circuit_rcons oget_some cats1 catA eval_circuit_rcons). *)
    smt(valid_circuit_rcons_head rcons_cat).
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    rewrite /valid_circuit in H6.
    have := H6 (size cprev + size c{m} - 1) _. smt(size_cat size_rcons size_ge0).
    rewrite H.  simplify.
    have -> := onth_nth (ADDC(0,0)) (cprev ++ rcons c{hr} g{hr}) (size cprev + size (rcons c{hr} g{hr}) - 1) _.
      smt(size_cat size_rcons size_ge0).
    rewrite oget_some.
    rewrite nth_cat.
    rewrite size_rcons.
    smt(size_ge0 nth_rcons).
    rewrite /valid_circuit in H6.
    have := H6 (size cprev + size c{m} - 1) _. smt(size_cat size_rcons size_ge0).
    rewrite H.  simplify.
    have -> := onth_nth (ADDC(0,0)) (cprev ++ rcons c{hr} g{hr}) (size cprev + size (rcons c{hr} g{hr}) - 1) _.
      smt(size_cat size_rcons size_ge0).
    rewrite oget_some.
    rewrite nth_cat.
    rewrite size_rcons.
    smt(size_ge0 nth_rcons size_cat).

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

    have : 0 <= i /\ i + 1 < size result.`4 =>
           nth 0 result.`4 (i + 1) =
           phi_decomp (nth (ADDC (0, 0)) (cprev ++ c{hr}) i) i 1 result.`4 result.`5 result.`1 result.`2.
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    smt().

    have : nth 0 result0.`4 i + nth 0 result0.`5 i + nth 0 result0.`6 i =
            nth 0 (rcons (eval_circuit_aux c{hr} s)
             (eval_gate g{hr} (eval_circuit_aux c{hr} s))) i.
    have : (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) = result0 by smt().
    smt().

    smt(eval_circuit_rcons).

    have : 0 <= i /\ i + 1 < size result0.`4 =>
            nth 0 result0.`4 (i + 1) = phi_decomp (nth (ADDC (0, 0)) (cprev ++ c{hr} ++ [g{hr}]) i) i 1 result0.`4 result0.`5 result0.`1 result0.`2.
    have : (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) = result0 by smt().
    smt().
    smt(cats1 catA).

    rewrite size_cat size_rcons.
    rewrite H8 - H0.
    simplify.
    have :
     size
       (rcons (eval_circuit_aux c{hr} s)
          (eval_gate g{hr} (eval_circuit_aux c{hr} s))) =
     size result0.`4.
    have : (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) = result0 by smt().
    smt().

    rewrite size_rcons.
    have -> := eval_circuit_aux_size c{hr} s.
    smt().

    have : (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) = result0 by smt().
    smt(size_rcons).
    have : (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) = result0 by smt().
    smt(size_rcons).
    have : (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) = result0 by smt().
    smt(size_rcons).

    have :
     size
       (rcons (eval_circuit_aux c{hr} s)
          (eval_gate g{hr} (eval_circuit_aux c{hr} s))) =
     size result0.`4.
    have : (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) = result0 by smt().
    smt().
    smt(size_rcons eval_circuit_rcons).

    have : (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) = result0 by smt().
    smt(size_rcons).
    have : (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) = result0 by smt().
    smt(size_rcons).

qed.

lemma correctness h' c' &m:
    valid_circuit c' =>
    Pr[Phi.main(h', c') @ &m : res = eval_circuit c' [h']] = 1%r.
proof.
  move=> c_valid.
  byphoare(: h = h' /\ c = c' ==> _)=>//.
  proc.
  inline Phi.output Phi.reconstruct Phi.share. auto.
  have H := compute_circuit_correct c' [h'] [].
  call H. clear H.
  auto; progress.
  apply dinput_ll.
  smt().
  smt().
  have Hlast := nth_last 0.
  rewrite - !Hlast.
  have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  smt(size_ge0).
qed.

lemma phi_sim_equiv g e':
    0 < e' /\ e' <= 3 =>
    (forall s,
      equiv[Phi.compute ~ Simulator.compute :
            size s = size w1{1} /\
            size s = size w2{1} /\
            size s = size w3{1} /\
            size k1{1} = size w1{1} - 1 /\
            size k2{1} = size k1{1} /\
            size k3{1} = size k1{1} /\
            size k1{1} = size k1{2} /\
            size k2{1} = size k2{2} /\
            size k3{1} = size k3{2} /\
            (if (e' = 1) then ={w1, w2, k1, k2}
              else
              (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
                else w3{1} = w1{2} /\ w1{1} = w2{2} /\ k3{1} = k1{2} /\ k1{1} = k2{2})) /\
             ={c} /\ e{2} = e' /\ c{1} = [g] /\
             (forall i, (nth 0 w1{1} i) + (nth 0 w2{1} i) + (nth 0 w3{1} i) = (nth 0 s i))
            ==>
            (let (k1, k2, k3, phi_w1, phi_w2, phi_w3) = res{1} in
              let (sim_k1, sim_k2, sim_k3, sim_w1, sim_w2) = res{2} in
              size k1 = size phi_w1 - 1 /\
              size k2 = size k1 /\
              size k3 = size k1 /\
              size sim_k1 = size k1 /\
              size sim_k2 = size k2 /\
              size sim_k3 = size k3 /\
              size (eval_circuit_aux [g] s) = size phi_w1 /\
              size (eval_circuit_aux [g] s) = size phi_w2 /\
              size (eval_circuit_aux [g] s) = size phi_w3 /\
              (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 (eval_circuit_aux [g] s) i)) /\
              (* (exists (k1, k2, k3), phi_w1 = (rcons w1{1} (phi_decomp g 1 w1' w2' k1 k2)) /\ *)
              (*                       phi_w2 = (rcons w2{1} (phi_decomp g 2 w2' w3' k2 k3)) /\ *)
              (*                       phi_w3 = (rcons w3{1} (phi_decomp g 3 w3' w1' k3 k1))) /\ *)
            (if e' = 1 then
              (sim_k1, sim_k2, sim_w1, sim_w2) = (k1, k2, phi_w1, phi_w2)
            else
              (if e' = 2 then
                (sim_k1, sim_k2, sim_w1, sim_w2) = (k2, k3, phi_w2, phi_w3)
              else
                (sim_k1, sim_k2, sim_w1, sim_w2) = (k3, k1, phi_w3, phi_w1))))]).
proof.
    progress.
    proc.
    (* have Hs1 : size w1' = size w2' by smt(). *)
    (* have Hs2 : size w1' = size w3' by smt(). *)
    rcondt{1} 1. auto.
    rcondt{2} 2. auto.
    rcondf{1} 15. auto.
    rcondf{2} 14. auto.
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
      skip. progress; smt(dinput_funi size_rcons nth_rcons oget_some).

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
      skip. progress; smt(dinput_funi size_rcons nth_rcons oget_some).

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
      skip. progress; smt(dinput_funi size_rcons nth_rcons oget_some).

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
            size k1{1} = size w1{1} - 1 /\
            size k2{1} = size k1{1} /\
            size k3{1} = size k1{1} /\
            size k1{1} = size k1{2} /\
            size k2{1} = size k2{2} /\
            size k3{1} = size k3{2} /\
            (if (e' = 1) then ={w1, w2, k1, k2}
              else
              (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
                else w3{1} = w1{2} /\ w1{1} = w2{2} /\ k3{1} = k1{2} /\ k1{1} = k2{2})) /\
             ={c} /\ e{2} = e' /\ c{1} = c' /\
             (forall i, (nth 0 w1{1} i) + (nth 0 w2{1} i) + (nth 0 w3{1} i) = (nth 0 s i))
            ==>
            (let (k1, k2, k3, phi_w1, phi_w2, phi_w3) = res{1} in
              let (sim_k1, sim_k2, sim_k3, sim_w1, sim_w2) = res{2} in
              (size phi_w1) = (size phi_w2) /\ (size phi_w2 = size phi_w3) /\
              (size phi_w1) = (size (eval_circuit_aux c' s)) /\
              size k1 = size phi_w1 - 1 /\
              size k1 = size sim_k1 /\
              size k2 = size sim_k2 /\
              size k3 = size sim_k3 /\
              (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 (eval_circuit_aux c' s) i)) /\
            (if e' = 1 then
              (sim_k1, sim_k2, sim_w1, sim_w2) = (k1, k2, phi_w1, phi_w2)
            else
              (if e' = 2 then
                (sim_k1, sim_k2, sim_w1, sim_w2) = (k2, k3, phi_w2, phi_w3)
              else
                (sim_k1, sim_k2, sim_w1, sim_w2) = (k3, k1, phi_w3, phi_w1))))]).
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
      size k1{1} = size w1{1} - 1 /\
      size k2{1} = size k1{1} /\
      size k3{1} = size k1{1} /\
      size k1{1} = size k1{2} /\
      size k2{1} = size k2{2} /\
      size k3{1} = size k3{2} /\
      c{1} = (x::l)
      ==> ={res})
     (size s = size w1{1} /\
      size s = size w2{1} /\
      size s = size w3{1} /\
      size k1{1} = size w1{1} - 1 /\
      size k2{1} = size k1{1} /\
      size k3{1} = size k1{1} /\
      size k1{1} = size k1{2} /\
      size k2{1} = size k2{2} /\
      size k3{1} = size k3{2} /\
      (if (e' = 1) then ={w1, w2, k1, k2}
        else
        (if (e' = 2) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
          else w3{1} = w1{2} /\ w1{1} = w2{2} /\ k3{1} = k1{2} /\ k1{1} = k2{2})) /\
        ={c} /\ e{2} = e' /\ c{1} = (x::l) /\
        (forall i, (nth 0 w1{1} i) + (nth 0 w2{1} i) + (nth 0 w3{1} i) = (nth 0 s i)) ==>
          (let (k1, k2, k3, phi_w1, phi_w2, phi_w3) = res{1} in
            let (sim_k1, sim_k2, sim_k3, sim_w1, sim_w2) = res{2} in
            (size phi_w1) = (size phi_w2) /\ (size phi_w2 = size phi_w3) /\
            (size phi_w1) = (size (eval_circuit_aux (x::l) s)) /\
            size k1 = size phi_w1 - 1 /\
            size k1 = size sim_k1 /\
            size k2 = size sim_k2 /\
            size k3 = size sim_k3 /\
            (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 (eval_circuit_aux (x::l) s) i)) /\
          (if e' = 1 then
            (sim_k1, sim_k2, sim_w1, sim_w2) = (k1, k2, phi_w1, phi_w2)
          else
            (if e' = 2 then
              (sim_k1, sim_k2, sim_w1, sim_w2) = (k2, k3, phi_w2, phi_w3)
            else
              (sim_k1, sim_k2, sim_w1, sim_w2) = (k3, k1, phi_w3, phi_w1))))).
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
    (={c, w1, w2, e, k1, k2, k3} /\ c{1} = (x::l) /\
    size k1{1} = size w1{1} - 1 /\
    size k2{1} = size k1{1} /\
    size k3{1} = size k1{1} /\
    size k1{1} = size k1{2} /\
    size k2{1} = size k2{2} /\
    size k3{1} = size k3{2}
     ==>
     ={res})
    (size s = size w1{2} /\
     size s = size w2{2} /\
     size s = size w3{2} /\
     size k1{2} = size w1{2} - 1 /\
     size k2{2} = size k1{2} /\
     size k3{2} = size k1{2} /\
     size k1{2} = size k1{1} /\
     size k2{2} = size k2{1} /\
     size k3{2} = size k3{1} /\
    (if (e' = 1) then ={w1, w2, k1, k2}
      else
      (if (e' = 2) then w2{2} = w1{1} /\ w3{2} = w2{1} /\ k2{2} = k1{1} /\ k3{2} = k2{1}
        else w3{2} = w1{1} /\ w1{2} = w2{1} /\ k3{2} = k1{1} /\ k1{2} = k2{1})) /\
       ={c} /\ e{1} = e' /\ c{2} = (x::l) /\
       (forall i, (nth 0 w1{2} i) + (nth 0 w2{2} i) + (nth 0 w3{2} i) = (nth 0 s i))
     ==>
      (let (k1, k2, k3, phi_w1, phi_w2, phi_w3) = res{2} in
        let (sim_k1, sim_k2, sim_k3, sim_w1, sim_w2) = res{1} in
        (size phi_w1) = (size phi_w2) /\ (size phi_w2 = size phi_w3) /\
        (size phi_w1) = (size (eval_circuit_aux (x::l) s)) /\
        size k1 = size phi_w1 - 1 /\
        size k1 = size sim_k1 /\
        size k2 = size sim_k2 /\
        size k3 = size sim_k3 /\
        (forall i, (nth 0 phi_w1 i) + (nth 0 phi_w2 i) + (nth 0 phi_w3 i) = (nth 0 (eval_circuit_aux (x::l) s) i)) /\
      (if e' = 1 then
        (sim_k1, sim_k2, sim_w1, sim_w2) = (k1, k2, phi_w1, phi_w2)
      else
        (if e' = 2 then
          (sim_k1, sim_k2, sim_w1, sim_w2) = (k2, k3, phi_w2, phi_w3)
        else
              (sim_k1, sim_k2, sim_w1, sim_w2) = (k3, k1, phi_w3, phi_w1))))).
  + progress; smt().
  + progress; smt().
  + (* proof Simulator.compute ~ Simulator.compute_stepped *)
    clear IH. proc. inline *. sp.
    unroll{1} 1; unroll{2} 1.
    sim.
    if; progress. smt(). smt().
    - rcondf{2} 13. auto. smt().
      auto. smt().
    - exfalso. smt().
  (* main proof *)
  symmetry.
  proc. auto.
  have IH' := IH (eval_circuit_aux [x] s).
  have Hgate := phi_sim_equiv x e' _ s. smt().
  call IH'. wp. call Hgate.
  clear IH IH' Hgate.
  auto; smt().
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
    auto; smt(nth_last).

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
    auto; smt(nth_last).

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
    auto; smt(nth_last).
qed.
