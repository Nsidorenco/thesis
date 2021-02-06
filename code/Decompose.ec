(* Formalization of MPC Phi decomposition *)
require import AllCore Distr List IntDiv DList DInterval Folding.
require (*--*) MPC.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

type input  = int.
type output = int.
type share  = int.
type random = int list.
type gate   = [| ADDC of (int * int)
               | MULTC of (int * int)
               | MULT of (int * int)
               | ADD of (int * int)].
type circuit = gate list.
type view    = share list * random.
type projected_view = view.

(* secret sharing distribution *)
op dinput : {input distr | is_lossless dinput /\ is_funiform dinput} as dinput_llfuni.

lemma dinput_ll : is_lossless dinput by have []:= dinput_llfuni.
lemma dinput_funi : is_funiform dinput by have []:= dinput_llfuni.
lemma dinput_fu : is_full dinput by apply/funi_ll_full; [exact/dinput_funi|exact/dinput_ll].

op eval_gate (g : gate, s : int list) : output =
  with g = MULT inputs => let (i, j) = inputs in
                          let x = (nth witness s i) in
                          let y = (nth witness s j) in x * y
  with g = ADD inputs =>  let (i, j) = inputs in
                          let x = (nth witness s i) in
                          let y = (nth witness s j) in x + y
  with g = ADDC inputs => let (i, c) = inputs in
                          let x = (nth witness s i) in x + c
  with g = MULTC inputs => let (i, c) = inputs in
                          let x = (nth witness s i) in x * c.

op eval_circuit_aux(c : circuit, s : int list) : int list =
    with c = [] => s
    with c = g :: gs =>
     let r = eval_gate g s in
     eval_circuit_aux gs (rcons s r).

op eval_circuit (c : circuit, s : int) : output =
    last witness (eval_circuit_aux c [s]).

op nth_looping (vs : 'a list) (i : int) =
  nth witness vs (i %% 3).

clone import MPC as MPC' with
  type input <- input,
  type output <- output,
  type share <- share,
  type gate <- gate,
  type random <- random,
  type projected_view <- projected_view,
  op n = 3,
  op d = 2,
  op challenge = [0..2],
  op circuit_eval = eval_circuit,
  op output (v : view) = last witness (fst v),
  op in_dom_f n (e : challenge) i =
    if (e + d <= n) then i \in [e..e+d-1] else (i \in [e..n-1] \/ i \in [0..d-(n - e)-1]),
  op proj_mapping (i e : int) = (i - e) %% 3,
  op reconstruct (ss : share list) = (foldr (fun (s : share) (acc : int), acc + s) 0 ss),
  op f (vs : view list, e : int) =
    let v1 = (nth_looping vs e) in
    let v2 = (nth_looping vs (e+1)) in
    [v1; v2],
  op f_inv = (fun x => x),
  op drandom = dlist dinput 3
  proof *.
  realize n_pos by []. 
  realize d_pos by [].
  realize d_leq_n by [].
  realize drandom_lluni. split.
      - rewrite /drandom.
        apply /dlist_ll /dinput_ll.
      - rewrite /drandom.
        smt.
  qed.
  realize f_inv_correct.
      rewrite /challenge.
      rewrite /f_inv /f /nth_looping /in_dom_f /n /d.
      progress.
      case (e = 0); progress.
      - smt.
      case (e = 1); progress.
      - smt.
      case (e = 2); progress.
      - smt.
     smt.
  qed.
  realize f_inv_hom.
      smt.
  qed.

op phi_decomp (g : gate, idx, p : int, w1 w2 : int list, k1 k2 : int list) : output =
with g = ADDC inputs =>
    let (i, c) = inputs in
    let x = (nth witness w1 i) in
    if p = 0 then x + c else x
with g = MULTC inputs =>
    let (i, c) = inputs in
    let x = (nth witness w1 i) in x * c
with g = ADD inputs =>
    let (i, j) = inputs in
    let x = (nth witness w1 i) in
    let y = (nth witness w1 j) in x + y
with g = MULT inputs =>
    let (i, j) = inputs in
    let xp = (nth witness w1 i) in
    let yp = (nth witness w1 j) in
    let xp' = (nth witness w2 i) in
    let yp' = (nth witness w2 j) in
    let r1 = (nth witness k1 idx) in
    let r2 = (nth witness k2 idx) in
    xp * yp + xp' * yp + xp * yp' + r1 - r2.

op simulator_eval (g : gate, idx, p : int, e : int, w1 w2 : int list, k1 k2 k3: int list) =
with g = MULT inputs =>
  if ((p + 1) - e %% 3 = 1) then (nth witness k3 idx) else phi_decomp g idx p w1 w2 k1 k2
  (* if p = 1 then phi_decomp g p w1 w2 k1 k2 else *)
  (* if p = 2 then phi_decomp g p w1 w2 k2 k3 else *)
with g = ADDC inputs =>
    phi_decomp g idx p w1 w2 k1 k2
with g = MULTC inputs => phi_decomp g idx p w1 w2 k1 k2
with g = ADD inputs => phi_decomp g idx p w1 w2 k1 k2.


op valid_view_op (p : int) (view view2 : view) (c : circuit) =
  (foldr (fun i acc,
            acc /\ (nth witness view.`1 (i + 1)) = phi_decomp (nth witness c i) i p view.`1 view2.`1 view.`2 view2.`2)
    true (range 0 (size view.`1 - 1))).

pred valid_view (p : int) (view view2 : view) (c : circuit) =
    forall i, 0 <= i < size view.`1 => (nth witness view.`1 (i + 1)) = phi_decomp (nth witness c i) i p view.`1 view2.`1 view.`2 view2.`2.

lemma valid_view_reflect: valid_view_op = valid_view.
    rewrite fun_ext2=>p view.
    rewrite fun_ext2=>view2 c.
    rewrite /valid_view_op /valid_view.
    simplify.

    rewrite foldr_range.
    elim c.
    - simplify. 
admitted.

module Circuit = {
  proc eval(c, s) = {
    return eval_circuit c s;
  }
}.

lemma eval_circuit_module_fail c' s' y &m:
    y <> eval_circuit c' s' => Pr[Circuit.eval(c', s') @ &m : res = y] = 0%r.
proof.
    progress.
    byphoare(: c = c' /\ s = s' ==> res = y )=>//.
    hoare.
    proc.
    skip. smt().
qed.

lemma eval_circuit_module c' s' y &m:
    y = eval_circuit c' s' <=> Pr[Circuit.eval(c', s') @ &m : res = y] = 1%r.
proof.
    split.
    - progress.
      byphoare(: c = c' /\ s = s' ==> _ )=>//.
      by proc.
    - case (y = eval_circuit c' s').
      trivial.
      progress.
      have := eval_circuit_module_fail c' s' y &m.
      progress. smt().
qed.

lemma eval_circuit c' s' &m:
    Pr[Circuit.eval(c', s') @ &m : res = eval_circuit c' s'] = 1%r.
proof.
    by rewrite - eval_circuit_module.
qed.

module Phi = {

  proc share(x) = {
    var x1, x2, x3;
    x1 <$ dinput;
    x2 <$ dinput;
    x3 <- x - x1 - x2;
    return (x1, x2, x3);
  }
  proc sample_tapes(n : int) : random list = {
    return [];
  }

  proc gate_eval(g : gate, w1 w2 w3, k1 k2 k3) = {
    var r1, r2, r3, v1, v2, v3;
    r1 <$ dinput;
    r2 <$ dinput;
    r3 <$ dinput;
    k1 <- (rcons k1 r1);
    k2 <- (rcons k2 r2);
    k3 <- (rcons k3 r3);
    v1 <- phi_decomp g (size w1 - 1) 0 w1 w2 k1 k2;
    v2 <- phi_decomp g (size w1 - 1) 1 w2 w3 k2 k3;
    v3 <- phi_decomp g (size w1 - 1) 2 w3 w1 k3 k1;
    w1 <- (rcons w1 v1);
    w2 <- (rcons w2 v2);
    w3 <- (rcons w3 v3);

    return (k1, k2, k3, w1, w2, w3);
  }

  proc compute(c : circuit, w1 w2 w3, k1 k2 k3) = {
    while (c <> []) {
     (k1, k2, k3, w1, w2, w3) <- gate_eval(head witness c, w1, w2, w3, k1, k2, k3);
     c <- behead c;
    }
    return (k1, k2, k3, w1, w2, w3);
  }

  proc compute_fixed(c : circuit, w1 w2 w3 : share list, k1 k2 k3 : random) = {
    var g, v1, v2, v3;
    while (c <> []) {
      g <- (head witness c);
      v1 <- phi_decomp g (size w1 - 1) 0 w1 w2 k1 k2;
      v2 <- phi_decomp g (size w1 - 1) 1 w2 w3 k2 k3;
      v3 <- phi_decomp g (size w1 - 1) 2 w3 w1 k3 k1;
      w1 <- (rcons w1 v1);
      w2 <- (rcons w2 v2);
      w3 <- (rcons w3 v3);
      c <- behead c;
    }
    return (k1, k2, k3, w1, w2, w3);
  }

  proc compute_stepped(c : circuit, w1 w2 w3, k1 k2 k3) = {
    (k1, k2, k3, w1, w2, w3) <- compute([head (ADDC(0,0)) c], w1, w2, w3, k1, k2, k3);
    c <- behead c;
    (k1, k2, k3, w1, w2, w3) <- compute(c, w1, w2, w3, k1, k2, k3);

    return (k1, k2, k3, w1, w2, w3);
  }
  proc compute_stepped_reversed(c : circuit, g : gate, w1 w2 w3, k1 k2 k3) = {
    (k1, k2, k3, w1, w2, w3) <- compute(c, w1, w2, w3, k1, k2, k3);
    (k1, k2, k3, w1, w2, w3) <- compute([g], w1, w2, w3, k1, k2, k3);

    return (k1, k2, k3, w1, w2, w3);
  }

  proc decomp_global(c : circuit, x : input, rs : random list) = {
    var x1, x2, x3, r1, r2, r3, w1, w2, w3;
    (x1, x2, x3) <- share(x);
    r1 <- head witness rs;
    rs <- behead rs;
    r2 <- head witness rs;
    rs <- behead rs;
    r3 <- head witness rs;
    rs <- behead rs;

    (r1, r2, r3, w1, w2, w3) <- compute_fixed(c, [x1], [x2], [x3], r1, r2, r3);

    return [(w1, r1); (w2, r2); (w3, r3)];
  }

  proc decomp(c : circuit, x : input, rs : random list) = {
    var x1, x2, x3, k1, k2, k3, w1, w2, w3;
    (x1, x2, x3) <- share(x);

    (k1, k2, k3, w1, w2, w3) <- compute(c, [x1], [x2], [x3], [], [], []);

    return [(w1, k1); (w2, k2); (w3, k3)];
  }
  proc decomp_fixed(c : circuit, x1 x2 x3, rs : random list) = {
    var k1, k2, k3, w1, w2, w3;
    (k1, k2, k3, w1, w2, w3) <- compute(c, [x1], [x2], [x3], [], [], []);

    return [(w1, k1); (w2, k2); (w3, k3)];
  }

  proc decomp_fixed_tape(c : circuit, x1 x2 x3, rs : random list) = {
    var k1, k2, k3, w1, w2, w3;
    k1 <- nth witness rs 0;
    k2 <- nth witness rs 1;
    k3 <- nth witness rs 2;
    (k1, k2, k3, w1, w2, w3) <- compute_fixed(c, [x1], [x2], [x3], k1, k2, k3);

    return [(w1, k1); (w2, k2); (w3, k3)];
  }

  proc main(c : circuit, x : input) = {
    var rs, ws;
    rs <- sample_tapes(size c);
    ws <- decomp(c, x, rs);
    return reconstruct (map output ws);
  }

  proc main_fixed(c : circuit, x1 x2 x3, rs) = {
    var ws;
    ws <- decomp_fixed_tape(c, x1, x2, x3, rs);
    return reconstruct (map output ws);
  }

  proc verify(c : circuit, vs : verification_input, e : int, ys : share list) = {
    var y1, y2, y3, ver, w1, w2, w3;

    y1 <- nth witness ys 0;
    y2 <- nth witness ys 1;
    y3 <- nth witness ys 2;

    ver <- true;

    if (e = 0) {
      w1 <- nth witness vs 0;
      w2 <- nth witness vs 1;
      ver <- ver /\ (output w1 = y1);
      ver <- ver /\ (output w2 = y2);
      ver <- ver /\ valid_view_op 0 w1 w2 c;
    } else {
      if (e = 1) {
        w2 <- nth witness vs 0;
        w3 <- nth witness vs 1;
        ver <- ver /\ (output w2 = y2);
        ver <- ver /\ (output w3 = y3);
        ver <- ver /\ valid_view_op 1 w2 w3 c;
      } else{
        w3 <- nth witness vs 0;
        w1 <- nth witness vs 1;
        ver <- ver /\ (output w3 = y3);
        ver <- ver /\ (output w1 = y1);
        ver <- ver /\ valid_view_op 2 w3 w1 c;
      }
    }
    w1 <- nth witness vs 0;
    w2 <- nth witness vs 1;
    
    return ver /\ size w1.`1 = size w2.`1 /\ size w1.`1 = size c + 1
               /\ size w1.`2 = size w2.`2 /\ size w1.`2 = size c;
  }

  proc simulate(c : circuit, e : int, w1 w2 : int list, k1 k2 k3 : random) = {
    var g, r1, r2, r3, v1, v2, p1, p2;
    if (e = 0) {
      p1 <- 0;
      p2 <- 1;
    } else {
      if (e = 1) {
        p1 <- 1;
        p2 <- 2;
      } else {
        p1 <- 2;
        p2 <- 0;
      }
    }
    while (c <> []) {
      g <- head witness c;
      r1 <$ dinput;
      r2 <$ dinput;
      r3 <$ dinput;
      k1 <- (rcons k1 r1);
      k2 <- (rcons k2 r2);
      k3 <- (rcons k3 r3);
      v1 <- simulator_eval g (size w1 - 1) p1 (e+1) w1 w2 k1 k2 k3;
      v2 <- simulator_eval g (size w1 - 1) p2 (e+1) w2 w1 k1 k2 k3;
      w1 <- (rcons w1 v1);
      w2 <- (rcons w2 v2);
      c <- behead c;
    }

    return (k1, k2, k3, w1, w2);
  }
  proc simulate_stepped(c : circuit, e : int, w1 w2 : int list, k1 k2 k3 : random) = {
    (k1, k2, k3, w1, w2) <- simulate([head (ADDC(0,0)) c], e, w1, w2, k1, k2, k3);
    c <- behead c;
    (k1, k2, k3, w1, w2) <- simulate(c, e, w1, w2, k1, k2, k3);
    return (k1, k2, k3, w1, w2);
  }

  proc simulator(c : circuit, y : output, e : int) = {
    var x1, x2, k1, k2, k3, w1, w2, y1, y2, y3, vs';
    x1 <$ dinput;
    x2 <$ dinput;
    (k1, k2, k3, w1, w2) <- simulate(c, e, [x1], [x2], [], [], []);
    y1 <- last 0 w1;
    y2 <- last 0 w2;
    y3 <- y - (y1 + y2);

    vs' <- ([(w1, k1); (w2, k2)]);
    return (vs', [y1;y2;y3]);
  }

  proc extractor(vs : verification_input list) = {
    var v1, v2, v3, w1, w2, w3, k1, k2, k3, ret;
    var w1', w2', w3', k1', k2', k3';
    v1 <- nth witness vs 0;
    v2 <- nth witness vs 1;
    v3 <- nth witness vs 2;

    (w1, k1) <- (nth witness v1 0);
    (w2, k2) <- (nth witness v1 1);
    (w2', k2') <- (nth witness v2 0);
    (w3, k3) <- (nth witness v2 1);
    (w3', k3') <- (nth witness v3 0);
    (w1', k1') <- (nth witness v3 1);
    ret <- Some( (nth witness w1 0) + (nth witness w2 0) + (nth witness w3 0) );

    return ret;
  }

}.

op highest_inwire (g : gate) =
  with g = MULT inputs => let (i, j) = inputs in max i j
  with g = ADD inputs =>  let (i, j) = inputs in max i j
  with g = ADDC inputs => let (i, c) = inputs in i
  with g = MULTC inputs => let (i, c) = inputs in i.

op lowest_inwire (g : gate) =
  with g = MULT inputs => let (i, j) = inputs in min i j
  with g = ADD inputs =>  let (i, j) = inputs in min i j
  with g = ADDC inputs => let (i, c) = inputs in i
  with g = MULTC inputs => let (i, c) = inputs in i.


pred valid_gate (g : gate) idx =
  0 <= lowest_inwire g /\ highest_inwire g <= idx.

pred valid_circuit (c : circuit) =
  forall i, (0 <= i /\ i < size c) =>
    valid_gate (nth witness c i) i.

lemma valid_circuit_rcons_head g c:
    valid_circuit (rcons c g) => valid_circuit c.
proof.
    rewrite /valid_circuit.
    progress.
    have := H i _. smt(size_rcons).
    (* have -> := onth_nth (ADDC(0,0)) (rcons c g) i _. smt(size_rcons). *)
    (* have -> := onth_nth (ADDC(0,0)) c i _. smt(size_rcons). *)
    rewrite nth_rcons.
    case (i < size c); move => Hi.
    smt().
    smt().
    have := H i _. smt(size_rcons).
    (* have -> := onth_nth (ADDC(0,0)) (rcons c g) i _. smt(size_rcons). *)
    (* have -> := onth_nth (ADDC(0,0)) c i _. smt(size_rcons). *)
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

lemma gate_computation_order g i (p : int) (w1 w2 w1' w2' : share list) k1 k2 k1' k2' :
    0 <= i /\ (i + 1 < size w1) /\ size w1 = size w2 /\ size k1 = size k2 /\ (size k1 = size w1 \/ size k1 = size w1 - 1) /\ valid_gate g i =>
    phi_decomp g i p w1 w2 k1 k2 = phi_decomp g i p (w1++w1') (w2++w2') (k1++k1') (k2++k2').
proof.
  elim g;
  move=> x; case x=> x1 x2;
  rewrite /valid_gate; progress;
  rewrite !nth_cat;
  smt().
qed.

lemma gate_computation_order_tape g i (p : int) (w1 w2 : share list) k1 k2 k1' k2' :
    0 <= i /\ (i < size k1) /\ size w1 = size w2 /\ size k1 = size k2 /\ size w1 <= size k1 + 1 /\ valid_gate g i =>
    phi_decomp g i p w1 w2 k1 k2 = phi_decomp g i p w1 w2 (k1++k1') (k2++k2').
proof.
  elim g;
  move=> x; case x=> x1 x2;
  rewrite /valid_gate; progress;
  rewrite !nth_cat;
  smt().
qed.

lemma gate_computation_order_eq g i (p : int) (w1 w2 w1' w2' : share list) k1 k2:
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

equiv compute_fixed_output_eq:
     Phi.compute ~ Phi.compute_fixed :
     ={c, w1, w2, w3} /\ size w1{2} = size w2{2} /\ size w1{2} = size w3{2}==>
     let (k1, k2, k3, w1, w2, w3) = res{1} in
     let (k1', k2', k3', w1', w2', w3') = res{2} in
     last witness w1 + last witness w2 + last witness w3 = last witness w1' + last witness w2' + last witness w3'.
proof.
    proc.
    inline Phi.gate_eval.
    while (={c} /\ size w1{1} = size w1{2}
                /\ size w2{1} = size w2{2}
                /\ size w3{1} = size w3{2}
                /\ size w1{1} = size w2{1}
                /\ size w1{1} = size w3{1}
                /\ size w1{2} = size w2{2}
                /\ size w1{2} = size w3{2}
                /\ forall i, nth witness w1{1} i + nth witness w2{1} i + nth witness w3{1} i = nth witness w1{2} i + nth witness w2{2} i + nth witness w3{2} i).
    auto.
    progress.
    apply dinput_ll.
    smt(size_rcons).
    smt(size_rcons).
    smt(size_rcons).
    smt(size_rcons).
    smt(size_rcons).
    smt(size_rcons).
    smt(size_rcons).
    rewrite !nth_rcons - H - H0 - H1 - H2 - H3.
    case (i < size w1{1}); progress.
    smt.
    case (i = size w1{1}); progress.
    elim (head witness c{2}); move=>x; case x=> x1 x2.
    smt().
    smt().
    smt().
    smt().
    auto.
    progress.
    smt.
qed.

lemma size_behead (l : 'a list):
    size l <= 1 => behead l = [].
proof.
    elim l.
    smt().
    smt().
qed.

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

lemma eval_circuit_cat c c':
  (forall s,
    (eval_circuit_aux (c ++ c') s)
    =
    eval_circuit_aux c' (eval_circuit_aux c s)).
proof.
  elim c; smt.
qed.

lemma compute_gate_correct g:
    (forall cprev s,
      phoare[Phi.compute :
        (c = [g] /\ size s = size w1 /\ size s = size w2 /\ size s = size w3 /\
          valid_gate g (size cprev) /\ valid_circuit cprev /\
          size cprev = size w1 - 1 /\
          size k1 = size k2 /\ size k1 = size w1 - 1 /\ size k1 = size k3 /\
          (forall i, 0 <= i /\ i < size w1 =>
            (nth witness w1 i) + (nth witness w2 i) + (nth witness w3 i) = (nth witness s i)) /\
          (forall i, 0 <= i /\ i + 1 < size w1 =>
            (nth witness w1 (i + 1)) = phi_decomp (nth witness (cprev) i) i 0 w1 w2 k1 k2 /\
            (nth witness w2 (i + 1)) = phi_decomp (nth witness (cprev) i) i 1 w2 w3 k2 k3 /\
            (nth witness w3 (i + 1)) = phi_decomp (nth witness (cprev) i) i 2 w3 w1 k3 k1))
        ==>
        let (k1, k2, k3, w1, w2, w3) = res in
        let s' = (eval_circuit_aux [g] s) in
        (forall i, 0 <= i /\ i < size w1 =>
          (nth witness w1 i) + (nth witness w2 i) + (nth witness w3 i) = (nth witness s' i)) /\
        (forall i, 0 <= i /\ i + 1 < size w1 =>
          (nth witness w1 (i + 1)) = phi_decomp (nth witness (cprev++[g]) i) i 0 w1 w2 k1 k2 /\
          (nth witness w2 (i + 1)) = phi_decomp (nth witness (cprev++[g]) i) i 1 w2 w3 k2 k3 /\
          (nth witness w3 (i + 1)) = phi_decomp (nth witness (cprev++[g]) i) i 2 w3 w1 k3 k1)
         /\ size (cprev ++ [g]) = size w1 - 1 /\ valid_gate g (size w1 - 1)
         /\ size k1 = size w1 - 1 /\ size k2 = size k1 /\ size k3 = size k1
         /\ size s' = size w1 /\ size s' = size w2 /\ size s' = size w3]=1%r).
proof.
  progress. proc. sp.
  rcondt 1. progress.
  rcondf 3. inline Phi.gate_eval. auto. 
  inline Phi.gate_eval.
  auto; progress.
  apply dinput_ll.
  rewrite !nth_rcons.
  have <- : (size w1{hr} = size w2{hr}) by smt().
  have <- : (size w1{hr} = size w3{hr}) by smt().
  case (i < size w1{hr}); progress.
  rewrite H0. smt().
  case (i = size w1{hr}); progress.
  rewrite H.
  simplify.
  have := H5. progress.
  move: H2 H20.
  rewrite /valid_gate.
  elim g; move=>x; case x=> i c; smt(nth_rcons nth_out).
  smt.
  rewrite !nth_rcons.
  rewrite nth_cat.
  case (i < size w1{hr}); progress.
  case (i < size cprev); progress.
  rewrite - !cats1.
  case (i + 1 < size w1{hr}). progress.
  smt.
  progress. smt.
  have -> : i + 1 = size w1{hr}. smt().
  have : i = size cprev. smt().
  progress.
  rewrite - !cats1 - H4.
  smt.
  case (i + 1 < size w1{hr}); progress.
  have := H8 i _. smt().
  case (i = size cprev); progress.
  rewrite - !cats1.
  smt. smt().
  smt(size_cat size_rcons).

  rewrite !nth_rcons.
  rewrite nth_cat.
  case (i < size w1{hr}); progress.
  case (i < size cprev); progress.
  rewrite - !cats1.
  progress. case (i + 1 < size w2{hr}).
  progress. smt.
  smt().
  have -> : i + 1 = size w1{hr}. smt().
  have : i = size cprev. smt().
  progress.
  rewrite - !cats1 - H4.
  smt.
  case (i + 1 < size w1{hr}); progress.
  have := H8 i _. smt().
  case (i = size cprev); progress.
  rewrite - !cats1.
  smt. smt().
  smt(size_cat size_rcons).

  rewrite !nth_rcons.
  rewrite nth_cat.
  case (i < size w1{hr}); progress.
  case (i < size cprev); progress.
  rewrite - !cats1.
  case (i + 1 < size w3{hr}).
  smt.
  smt().
  have -> : i + 1 = size w1{hr}. smt().
  have : i = size cprev. smt().
  progress.
  rewrite - !cats1 - H4.
  smt.
  case (i + 1 < size w1{hr}); progress.
  have := H8 i _. smt().
  case (i = size cprev); progress.
  rewrite - !cats1.
  smt. smt().
  smt(size_cat size_rcons).

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
              (nth witness w1 i) + (nth witness w2 i) + (nth witness w3 i) = (nth witness s i)) /\
          (forall i, 0 <= i /\ i + 1 < size w1 =>
              (nth witness w1 (i + 1)) = phi_decomp (nth witness (cprev) i) i 0 w1 w2 k1 k2 /\
              (nth witness w2 (i + 1)) = phi_decomp (nth witness (cprev) i) i 1 w2 w3 k2 k3 /\
              (nth witness w3 (i + 1)) = phi_decomp (nth witness (cprev) i) i 2 w3 w1 k3 k1))
        ==>  
        let (k1, k2, k3, w1, w2, w3) = res in
        (forall i, 0 <= i /\ i < size w1 =>
             (nth witness w1 i) + (nth witness w2 i) + (nth witness w3 i) = (nth witness (eval_circuit_aux c' s) i)) /\
        (forall i, 0 <= i /\ i + 1 < size w1 =>
            (nth witness w1 (i + 1)) = phi_decomp (nth witness (cprev++c') i) i 0 w1 w2 k1 k2 /\
            (nth witness w2 (i + 1)) = phi_decomp (nth witness (cprev++c') i) i 1 w2 w3 k2 k3 /\
            (nth witness w3 (i + 1)) = phi_decomp (nth witness (cprev++c') i) i 2 w3 w1 k3 k1)
        /\ size (cprev ++ c') = size w1 - 1
        /\ size k1 = size w1 - 1 /\ size k2 = size k1 /\ size k3 = size k1
        /\ size (eval_circuit_aux c' s) = size w1 /\ size w1 = size w2 /\ size w2 = size w3] = 1%r).
proof.
  elim /last_ind c'.
  - progress. proc; sp; rcondf 1; progress; auto; smt(cats0).
  - move=> x l Hind s cprev.
    bypr=> &m. progress.
    rewrite H.
    have -> :
        Pr[Phi.compute(rcons x l, w1{m}, w2{m}, w3{m}, k1{m}, k2{m}, k3{m}) @ &m :
          let (k1, k2, k3, w1, w2, w3) = res in
          (forall (i : int),
              0 <= i /\ i < size w1 =>
              nth witness w1 i + nth witness w2 i + nth witness w3 i =
              nth witness (eval_circuit_aux (rcons x l) s) i) /\
          (forall (i : int),
              0 <= i /\ i + 1 < size w1 =>
              nth witness w1 (i + 1) =
              phi_decomp (nth witness (cprev ++ rcons x l) i) i 0 w1 w2 k1
                k2 /\
              nth witness w2 (i + 1) =
              phi_decomp (nth witness (cprev ++ rcons x l) i) i 1 w2 w3 k2
                k3 /\
              nth witness w3 (i + 1) =
              phi_decomp (nth witness (cprev ++ rcons x l) i) i 2 w3 w1 k3
                k1) /\
          size (cprev ++ rcons x l) = size w1 - 1 /\
          size k1 = size w1 - 1 /\
          size k2 = size k1 /\
          size k3 = size k1 /\
          size (eval_circuit_aux (rcons x l) s) = size w1 /\
          size w1 = size w2 /\ size w2 = size w3] =
        Pr[Phi.compute_stepped_reversed(x, l, w1{m}, w2{m}, w3{m}, k1{m}, k2{m}, k3{m}) @ &m :
          let (k1, k2, k3, w1, w2, w3) = res in
          (forall (i : int),
              0 <= i /\ i < size w1 =>
              nth witness w1 i + nth witness w2 i + nth witness w3 i =
              nth witness (eval_circuit_aux (rcons x l) s) i) /\
          (forall (i : int),
              0 <= i /\ i + 1 < size w1 =>
              nth witness w1 (i + 1) =
              phi_decomp (nth witness (cprev ++ rcons x l) i) i 0 w1 w2 k1
                k2 /\
              nth witness w2 (i + 1) =
              phi_decomp (nth witness (cprev ++ rcons x l) i) i 1 w2 w3 k2
                k3 /\
              nth witness w3 (i + 1) =
              phi_decomp (nth witness (cprev ++ rcons x l) i) i 2 w3 w1 k3
                k1) /\
          size (cprev ++ rcons x l) = size w1 - 1 /\
          size k1 = size w1 - 1 /\
          size k2 = size k1 /\
          size k3 = size k1 /\
          size (eval_circuit_aux (rcons x l) s) = size w1 /\
          size w1 = size w2 /\ size w2 = size w3].
      + byequiv=>//. clear Hind H.
        proc. inline *. sp.
        splitwhile{1} 1 : 1 < size c.
        sim : (={w1, w2, w3, k1, k2, k3}).
        (* sim : (={w1, w2, w3, k1, k2, k3}). *)
        (* Invariant that behead c{1} = [l] *)
        wp.
        while (c{1} = rcons c0{2} l /\ w10{2} = w1{1} /\ w20{2} = w2{1} /\ w30{2} = w3{1} /\ k1{1} = k10{2} /\ k2{1} = k20{2} /\ k3{1} = k30{2}).
        auto; progress; smt(nth_rcons size_rcons size_ge0).
        auto. smt(nth_rcons size_rcons size_ge0).
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
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    rewrite /valid_circuit in H6.
    have := H6 (size cprev + size c{m} - 1) _. smt(size_cat size_rcons size_ge0).
    rewrite H.  simplify.
    (* have -> := onth_nth (ADDC(0,0)) (cprev ++ rcons c{hr} g{hr}) (size cprev + size (rcons c{hr} g{hr}) - 1) _. *)
      (* smt(size_cat size_rcons size_ge0). *)
    (* rewrite oget_some. *)
    rewrite nth_cat.
    rewrite size_rcons.
    smt(size_ge0 nth_rcons).
    rewrite /valid_circuit in H6.
    have := H6 (size cprev + size c{m} - 1) _. smt(size_cat size_rcons size_ge0).
    rewrite H.  simplify.
    (* have -> := onth_nth (ADDC(0,0)) (cprev ++ rcons c{hr} g{hr}) (size cprev + size (rcons c{hr} g{hr}) - 1) _. *)
    (*   smt(size_cat size_rcons size_ge0). *)
    (* rewrite oget_some. *)
    rewrite nth_cat.
    rewrite size_rcons.
    smt(size_ge0 nth_rcons size_cat).

    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    smt().
    have : result = (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) by smt().
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    smt(eval_circuit_rcons).
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    rewrite - cats1.
    have <- : cprev ++ c{hr} ++ [g{hr}] = cprev ++ (c{hr} ++ [g{hr}]) by smt.
    smt().
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    rewrite - cats1.
    have <- : cprev ++ c{hr} ++ [g{hr}] = cprev ++ (c{hr} ++ [g{hr}]) by smt.
    smt().
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    rewrite - cats1.
    have <- : cprev ++ c{hr} ++ [g{hr}] = cprev ++ (c{hr} ++ [g{hr}]) by smt.
    smt().
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    smt(size_rcons size_cat).
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    smt().
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    smt().
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    smt().
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    smt(eval_circuit_rcons).
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    smt().
    have : result0 = (result0.`1, result0.`2, result0.`3, result0.`4, result0.`5, result0.`6) by smt().
    smt().
qed.


lemma valid_view_fold (c : circuit) w1 w2 k1 k2 n p:
  0 <= n <= size w1 /\
  valid_circuit c /\ size w2 = size k1 + 1 /\ size w1 - 1 = size k1 /\ size k1 = size k2 /\
  (forall (i : int),
      0 <= i /\ i + 1 < n =>
      nth 0 w1 (i + 1) =
    phi_decomp (nth (ADDC (0, 0)) c i) i p w1 w2 k1 k2)
    =>
  (foldr
    (fun (i : int) (acc : bool) =>
      acc /\
      nth 0 w1 (i + 1) =
      phi_decomp (nth (ADDC (0, 0)) c i) i p w1 w2 k1 k2) true
    (range 0 (n - 1))) = true.
proof.
  elim /natind n.
  - smt(range_geq).
  - progress.
    have IH := H0 _. smt(size_rcons size_ge0). clear H0.
    progress.
    case (0 <= n - 1)=> Hn.
    have -> := range_cat (n - 1) 0 n _ _. smt(). smt().
    rewrite foldr_cat.
    have -> :(foldr
     (fun (i : int) (acc : bool) =>
        acc /\
        nth 0 w1 (i + 1) = phi_decomp (nth (ADDC (0, 0)) c i) i p w1 w2 k1 k2)
     true (range (n-1) n)) = true.
    rewrite rangeS.
    simplify. have -> := H7 (n - 1). smt().
    done.
    smt().
    have : n = 0. smt().
    progress. rewrite range_geq. smt().
    smt().
qed.

lemma verifiability c' x' e' &m:
    valid_circuit c' /\ e' \in challenge =>
    Pr[Verifiability(Phi).main(c', x', e') @ &m : res] = 1%r.
proof.
  progress.
  byphoare(: w = x' /\ c = c' /\ e = e' ==> _)=>//.
  proc.
  inline Phi.decomp Phi.verify Phi.share Phi.sample_tapes.
  auto.
  auto; progress.
  have Hcir := compute_circuit_correct c' [x'] [].
  call Hcir. clear Hcir.
  auto.
  progress.
  apply dinput_ll.
  smt().
  smt().
  smt().
  smt().
  by rewrite /f /nth_looping /output.
  by rewrite /f /nth_looping /output.
  rewrite /f /nth_looping /valid_view_op.
  simplify.
  rewrite foldr_range.
  have ->: 
foldr
  (fun (i : int) (acc : bool) =>
     (0 <= i && i < size result.`4 - 1) /\
     (fun (i0 : int) (acc0 : bool) =>
        acc0 /\
        nth witness result.`4 (i0 + 1) =
        phi_decomp (nth witness c{hr} i0) i0 0 result.`4 result.`5
          result.`1 result.`2) i acc) true (range 0 (size result.`4 - 1)) =
foldr
  (fun (i : int) (acc : bool) =>
     (0 <= i && i < size result.`4 - 1) /\
     (fun (i0 : int) (acc0 : bool) =>
        acc0) i acc) true (range 0 (size result.`4 - 1)).
  congr.
  rewrite rel_ext /(===).
  progress.
  case (0 <= x4 && x4 < size result.`4 - 1); progress.
  clear H0.
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  smt().
  by rewrite - foldr_range foldr_id.

  rewrite /f /nth_looping /valid_view_op.
  simplify.
  clear H8 H9 H0 H1 H2 H3 H4 H5 H5 H7 H H6. 
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().

  rewrite /circuit_eval /eval_circuit /eval_circuit_aux.
  rewrite /reconstruct /output -! nth_last. simplify.
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  progress. clear H8 H9.
  rewrite H16 -H18 -H17.
  have <- := H10 (size result.`4 - 1) _. smt(size_ge0).
  smt().
  
  by rewrite /output /f /nth_looping.
  by rewrite /output /f /nth_looping.

  rewrite /f /nth_looping /valid_view_op. simplify.
  rewrite foldr_range.
  have -> :
foldr
  (fun (i : int) (acc : bool) =>
     (0 <= i && i < size result.`5 - 1) /\
     (fun (i0 : int) (acc0 : bool) =>
        acc0 /\
        nth witness result.`5 (i0 + 1) =
        phi_decomp (nth witness c{hr} i0) i0 1 result.`5 result.`6
          result.`2 result.`3) i acc) true (range 0 (size result.`5 - 1)) =
foldr
  (fun (i : int) (acc : bool) =>
     (0 <= i && i < size result.`5 - 1) /\
     (fun (i0 : int) (acc0 : bool) =>
        acc0) i acc) true (range 0 (size result.`5 - 1)).
  congr.
  rewrite rel_ext /(===).
  progress.
  case (0 <= x4 && x4 < size result.`5 - 1); progress.
  move : H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  clear H0. smt().
  by rewrite -foldr_range foldr_id.

  rewrite /f /nth_looping /valid_view_op.
  simplify.
  clear H8 H9 H0 H1 H2 H3 H4 H5 H5 H7 H H6. 
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().

  rewrite /reconstruct /output /circuit_eval /eval_circuit -!nth_last.
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  progress.
  smt(size_ge0).
  have -> : e{hr} = 2 by smt.
  by rewrite /output /f /nth_looping.
  have -> : e{hr} = 2 by smt.
  by rewrite /output /f /nth_looping.
  have -> : e{hr} = 2 by smt.
  rewrite /f /nth_looping /valid_view_op.
  simplify.
  rewrite foldr_range.
  have ->:
foldr
  (fun (i : int) (acc : bool) =>
     (0 <= i && i < size result.`6 - 1) /\
     (fun (i0 : int) (acc0 : bool) =>
        acc0 /\
        nth witness result.`6 (i0 + 1) =
        phi_decomp (nth witness c{hr} i0) i0 2 result.`6 result.`4
          result.`3 result.`1) i acc) true (range 0 (size result.`6 - 1))=
foldr
  (fun (i : int) (acc : bool) =>
     (0 <= i && i < size result.`6 - 1) /\
     (fun (i0 : int) (acc0 : bool) =>
        acc0) i acc) true (range 0 (size result.`6 - 1)).
  congr.
  rewrite rel_ext /(===).
  progress.
  case (0 <= x4 && x4 < size result.`6 - 1); progress.
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  clear H0. smt().
  by rewrite -foldr_range foldr_id.

  rewrite /f /nth_looping /valid_view_op.
  simplify.
  clear H8 H9 H0 H1 H2 H3 H4 H5 H5 H7 H H6. 
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().
  move: H10.
  have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  simplify=> [[_ [_ ?]]].
  smt().

  rewrite /reconstruct /output /circuit_eval /eval_circuit -!nth_last.
  simplify.
  have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
  clear H0. smt(size_ge0).
qed.

lemma correctness_module:
    equiv[Phi.main ~ Circuit.eval : ={c} /\ valid_circuit c{1} /\ x{1} = s{2} ==> ={res}].
proof.
  proc.
  inline Phi.sample_tapes Phi.decomp Phi.share.
  wp.
  exists* c{1}; elim*=> c.
  exists* x{1}; elim*=> x.
  have Hcir := compute_circuit_correct c [x] [].
  call{1} Hcir. clear Hcir.
  auto. progress.
  - apply dinput_ll.
  - smt().
  - smt().
  - smt().
  - smt().
  - rewrite /reconstruct /output /eval_circuit /eval_circuit_aux - !nth_last.
    simplify.
    move: H7.
    have <- : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt(size_ge0).
qed.

lemma correctness_fixed :
equiv[Phi.main ~ Phi.main_fixed : ={c}  /\ valid_circuit c{1} /\ x1{2} + x2{2} + x3{2} = x{1}
                                        /\ size (nth witness rs{2} 0) = size c{2}
                                        /\ size (nth witness rs{2} 1) = size c{2}
                                        /\ size (nth witness rs{2} 2) = size c{2}
      ==> ={res}].
proof.
  proc.
  inline Phi.decomp_fixed_tape Phi.decomp Phi.sample_tapes Phi.share Phi.compute Phi.compute_fixed.
  auto.
  while (
  ={c1} /\
  (forall i, i < size w10{1} =>
    (nth witness w10{1} i + nth witness w20{1} i + nth witness w30{1} i
     = nth witness w10{2} i + nth witness w20{2} i + nth witness w30{2} i))
  /\ size w10{1} = size w20{1}
  /\ size w10{1} = size w30{1}
  /\ size w10{1} = size w10{2}
  /\ size w10{2} = size w20{2}
  /\ size w10{2} = size w30{2}
  /\ size k10{1} = size c{2} - size c1{2}
  /\ size k20{1} = size c{2} - size c1{2}
  /\ size k30{1} = size c{2} - size c1{2}
  /\ size k10{2} = size c{2}
  /\ size k20{2} = size c{2}
  /\ size k30{2} = size c{2}
  ).
  - inline Phi.gate_eval.
    auto; progress.
    + apply dinput_ll.
    + rewrite !nth_rcons.
      rewrite -H4 -H3 -H2 -H1 -H0.
      case (i < size w10{1}).
      + progress; smt().
      + progress; have -> : i = size w10{1} by smt(size_rcons size_ge0).
        simplify.
        elim (head witness c1{2}); move=>x; case x=> a b; smt(nth_rcons nth_out).
      + smt(size_rcons).
      + smt(size_rcons).
      + smt(size_rcons).
      + smt(size_rcons).
      + smt(size_rcons).
      + smt(size_rcons).
      + smt(size_rcons).
      + smt(size_rcons).
  auto.
  progress.
  + apply dinput_ll.
  + smt().
  - rewrite /reconstruct /output /eval_circuit /eval_circuit_aux - !nth_last.
    simplify.
    smt().
qed.
  

equiv verify_properties c' vs' e' ys':
    Phi.verify ~ Phi.verify :
    ={c, vs, ys, e} /\ e{1} = e' /\ vs{1} = vs' /\ ys{1} = ys' /\ c{1} = c' /\ e' \in challenge
    ==>
      res{1} <=> valid_view_op e' (nth_looping vs' 0) (nth_looping vs' 1) c' /\ output (nth_looping vs' 0) = nth_looping ys' e' /\ output (nth_looping vs' 1) = nth_looping ys' (e'+1)
      /\ size (fst (nth_looping vs' 0)) = size (fst (nth_looping vs' 1)) /\ size (fst (nth_looping vs' 0)) = size c' + 1
      /\ size (snd (nth_looping vs' 0)) = size (snd (nth_looping vs' 1)) /\ size (snd (nth_looping vs' 0)) = size c'.
proof.
  proc.
  auto.
  smt.
qed.

lemma verify_properties_phoare c' vs' e' ys':
    phoare[Phi.verify : c = c' /\ vs = vs' /\ e = e' /\ ys = ys' /\ e \in challenge ==> res] = 1%r =>
    phoare[Phi.verify : c = c' /\ vs = vs' /\ e = e' /\ ys = ys' /\ e \in challenge ==>
    valid_view_op e' (nth_looping vs' 0) (nth_looping vs' 1) c' /\
    size (fst (nth_looping vs' 0)) = size (fst (nth_looping vs' 1)) /\ size (fst (nth_looping vs' 0)) = size c' + 1 /\
    size (snd (nth_looping vs' 0)) = size (snd (nth_looping vs' 1)) /\ size (snd (nth_looping vs' 0)) = size c' /\
    output (nth_looping vs' 0) = nth_looping ys' e' /\ output (nth_looping vs' 1) = nth_looping ys' (e'+1)] = 1%r.
proof.
    progress.
    bypr=> &m=>/>=> e_challenge.
    have : 
      Pr[Phi.verify(c{m}, vs{m}, e{m}, ys{m}) @ &m : res] =
      Pr[Phi.verify(c{m}, vs{m}, e{m}, ys{m}) @ &m :
        valid_view_op e{m} ((nth_looping vs{m} 0))
          ((nth_looping vs{m} 1)) c{m} /\
        size (fst (nth_looping vs{m} 0)) = size (fst (nth_looping vs{m} 1)) /\ size (fst (nth_looping vs{m} 0)) = size c{m} + 1 /\
        size (snd (nth_looping vs{m} 0)) = size (snd (nth_looping vs{m} 1)) /\ size (snd (nth_looping vs{m} 0)) = size c{m} /\
        output ((nth_looping vs{m} 0)) = (nth_looping ys{m} e{m}) /\
        output ((nth_looping vs{m} 1)) = (nth_looping ys{m} (e{m} + 1))].
    byequiv=>//.
    have Hver := verify_properties c{m} vs{m} e{m} ys{m}.
    conseq Hver.
    progress.
    progress.
    move=><-.
    byphoare(: c = c{m} /\ vs = vs{m} /\ e = e{m} /\ ys = ys{m} /\ e \in challenge ==> _)=>//.
qed.

module Soundness_Inter = {
  proc main(c, vs', es, ys) = {
    var v1, v2, v3, w1, w2, w3, k1, k2, k3, xopt, e1, e2, e3, ret;
    var w1', w2', w3', k1', k2', k3';
    v1 <- nth witness vs' 0;
    v2 <- nth witness vs' 1;
    v3 <- nth witness vs' 2;
    e1 <- nth witness es 0;
    e2 <- nth witness es 1;
    e3 <- nth witness es 2;
    (w1, k1) <- nth witness v1 0;
    (w2, k2) <- nth witness v1 1;
    (w2', k2') <- nth witness v2 0;
    (w3, k3) <- nth witness v2 1;
    (w3', k3') <- nth witness v3 0;
    (w1', k1') <- nth witness v3 1;

    Phi.verify(c, v1, e1, ys);
    Phi.verify(c, v2, e2, ys);
    Phi.verify(c, v3, e3, ys);

    if (fully_consistent vs' es) {
      xopt <- Phi.extractor(vs');
      ret <- xopt <> None /\ circuit_eval c (oget xopt) = reconstruct ys;
    } else {
      ret <- false;
    }
    
    return ret;
  }
}.

equiv soundness_inter:
    Soundness(Phi).main ~ Soundness_Inter.main : ={c, vs', ys, es} /\ size vs'{1} = 3 /\ valid_circuit c{1} ==> ={res}.
proof.
  proc.
  sp.
  inline Phi.decomp Phi.decomp_global Phi.sample_tapes.
  swap{1} 2 -1.
  swap{2} 4 -3.
  auto.
  rcondt{1} 2. auto. if; auto. call (:true); auto; progress; smt(size_ge0).
  - progress. smt(size_ge0).
  rcondt{1} 7. auto; call (:true); auto. if; auto. call (:true); auto. 
  - smt(size_ge0).
  - smt(size_ge0).
  rcondt{1} 12. auto; call (:true); auto; call (:true); auto. if; auto. call (:true); auto. 
  - smt(size_ge0).
  - smt(size_ge0).
  rcondf{1} 17. auto; call (:true); auto; call (:true); auto; call (:true); auto. if; auto. call (:true); auto. 
  - smt(size_ge0).
  - smt(size_ge0).
  auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  if; auto.
  call (:true);
  auto.
qed.

lemma witness_extraction vs' c' y' &m:
    phoare[Phi.extractor : 
            valid_circuit c' /\
            vs = vs' /\
            let v1 = nth witness vs' 0 in
            let v2 = nth witness vs' 1 in
            let v3 = nth witness vs' 2 in 
            let (w1, k1) = nth witness v1 0 in
            let (w2, k2) = nth witness v1 1 in
            let (w2', k2') = nth witness v2 0 in
            let (w3, k3) = nth witness v2 1 in
            let (w3', k3') = nth witness v3 0 in
            let (w1', k1') = nth witness v3 1 in
            size w1 = size w2 /\ size w1 = size w3  /\ size w1 = size c' + 1 /\
            size k1 = size k2 /\ size k1 = size k3  /\ size k1 = size c' /\
            y' = reconstruct (map output [(w1,k1); (w2,k2); (w3,k3)]) /\
            w1 = w1' /\ w2 = w2' /\ w3 = w3' /\ k1 = k1' /\ k2 = k2' /\ k3 = k3 /\
            valid_view 0 (w1, k1) (w2, k2) c' /\
            valid_view 1 (w2, k2) (w3, k3) c' /\
            valid_view 2 (w3, k3) (w1, k1) c'
            ==> res <> None /\ (eval_circuit c' (oget res) = y')
            ] = 1%r.
proof.
  progress. proc.
  auto.
  pose tpl1 := nth witness (nth witness vs' 0) 0.
  pose tpl2 := nth witness (nth witness vs' 0) 1.
  pose tpl3 := nth witness (nth witness vs' 1) 0.
  pose tpl4 := nth witness (nth witness vs' 1) 1.
  pose tpl5 := nth witness (nth witness vs' 2) 0.
  pose tpl6 := nth witness (nth witness vs' 2) 1.
  have <- : (tpl1.`1, tpl1.`2) = tpl1 by smt().
  have <- : (tpl2.`1, tpl2.`2) = tpl2 by smt().
  have <- : (tpl3.`1, tpl3.`2) = tpl3 by smt().
  have <- : (tpl4.`1, tpl4.`2) = tpl4 by smt().
  have <- : (tpl5.`1, tpl5.`2) = tpl5 by smt().
  have <- : (tpl6.`1, tpl6.`2) = tpl6 by smt().
  simplify.
  progress.
  have H' := eval_circuit_module c' (nth witness (nth witness (nth witness vs{hr} 0) 0).`1 0 +
   nth witness (nth witness (nth witness vs{hr} 0) 1).`1 0 +
   nth witness (nth witness (nth witness vs{hr} 1) 1).`1 0) (reconstruct [output (tpl1.`1, tpl1.`2); output (tpl2.`1, tpl2.`2); output (tpl4.`1, tpl4.`2)]) &m.
  rewrite eq_sym. apply H'. clear H'.
  have <- :
Pr[Phi.main(c',
                nth witness (nth witness (nth witness vs{hr} 0) 0).`1 0 +
                nth witness (nth witness (nth witness vs{hr} 0) 1).`1 0 +
                nth witness (nth witness (nth witness vs{hr} 1) 1).`1 0) @ &m :
  res = reconstruct [output (tpl1.`1, tpl1.`2); output (tpl2.`1, tpl2.`2); output (tpl4.`1, tpl4.`2)]] =
Pr[Circuit.eval(c',
                nth witness (nth witness (nth witness vs{hr} 0) 0).`1 0 +
                nth witness (nth witness (nth witness vs{hr} 0) 1).`1 0 +
                nth witness (nth witness (nth witness vs{hr} 1) 1).`1 0) @ &m :
  res = reconstruct [output (tpl1.`1, tpl1.`2); output (tpl2.`1, tpl2.`2); output (tpl4.`1, tpl4.`2)]].

  byequiv correctness_module=>//.

  have -> : 
Pr[Phi.main(c',
            nth witness (nth witness (nth witness vs{hr} 0) 0).`1 0 +
            nth witness (nth witness (nth witness vs{hr} 0) 1).`1 0 +
            nth witness (nth witness (nth witness vs{hr} 1) 1).`1 0) @ &m :
  res = reconstruct [output (tpl1.`1, tpl1.`2); output (tpl2.`1, tpl2.`2); output (tpl4.`1, tpl4.`2)]] =
Pr[Phi.main_fixed(c',
            nth witness (nth witness (nth witness vs{hr} 0) 0).`1 0,
            nth witness (nth witness (nth witness vs{hr} 0) 1).`1 0,
            nth witness (nth witness (nth witness vs{hr} 1) 1).`1 0,
            [(nth witness (nth witness vs{hr} 0) 0).`2;
             (nth witness (nth witness vs{hr} 0) 1).`2;
             (nth witness (nth witness vs{hr} 1) 1).`2]) @ &m :
  res = reconstruct [output (tpl1.`1, tpl1.`2); output (tpl2.`1, tpl2.`2); output (tpl4.`1, tpl4.`2)]].

  byequiv correctness_fixed=>//.
  progress.
  - smt(). 
  - smt(). 
  - smt().

  byphoare(: c = c' /\ x1 = nth witness tpl1.`1 0
                    /\ x2 = nth witness tpl2.`1 0
                    /\ x3 = nth witness tpl4.`1 0
                    /\ rs = [tpl1.`2; tpl2.`2; tpl4.`2]
           ==> _ )=>//.
  proc. 
  inline Phi.decomp_fixed_tape Phi.compute_fixed Phi.gate_eval.
  sp. auto.
    while (
      size w10 = size tpl1.`1 - size c1 /\
         size w20 = size w10 /\
         size w30 = size w10 /\
         size c = size c1 + size w10 - 1 /\
         k10 = tpl1.`2 /\
         k20 = tpl2.`2 /\
         k30 = tpl4.`2 /\
         0 < size w10 /\
         0 < size w20 /\
         0 < size w30 /\
         (forall i, 0 <= i < size c1 => (nth witness c1 i = nth witness c' (size w10 - 1 + i) /\ (size w10 -1 + i) < size c')) /\
         (forall i, i < size w10 => nth witness tpl1.`1 i = nth witness w10 i) /\
         (forall i, i < size w20 => nth witness tpl2.`1 i = nth witness w20 i) /\
         (forall i, i < size w30 => nth witness tpl4.`1 i = nth witness w30 i))
        (size c1).
  progress.
  auto.
  progress.
  - smt(size_rcons).
  - smt(size_rcons).
  - smt(size_rcons).
  - smt(size_rcons).
  - smt(size_rcons).
  - smt(size_rcons).
  - smt(size_rcons).
  - rewrite size_rcons.
    have -> := nth_behead witness c1{hr0} i _. smt().
    smt().
  - smt(size_rcons).
  - rewrite !nth_rcons.
    case (i < size w10{hr0}); progress.
    + smt().
    + have -> : i = size w10{hr0} by smt(size_rcons size_ge0).
      simplify.
      rewrite /valid_view in H11.
      have := H11 (size w10{hr0} - 1) _. smt.
      have <- : nth witness c' (size w10{hr0} - 1) = head witness c1{hr0}.
      + smt(nth0_head size_ge0).
      rewrite /valid_circuit /valid_gate in H.
      have Hcir := H (size w10{hr0} - 1). clear H.
      (* have Hcir := H23 (size w10{hr0} - 1). clear H23. *)
      progress.
      have Hbounds := Hcir _. smt. clear Hcir.
      move: Hbounds.
      rewrite H.
      elim (nth witness c' (size w10{hr0} - 1)); move=>x; case x=> x1 x2; smt().

  - rewrite !nth_rcons.
    case (i < size w10{hr0}); progress.
    + smt().
    + have -> : i = size w10{hr0} by smt(size_rcons size_ge0).
      simplify.
      rewrite /valid_view in H12.
      have := H12 (size w20{hr0} - 1) _. smt.
      have <- : nth witness c' (size w10{hr0} - 1) = head witness c1{hr0}.
      + smt(nth0_head size_ge0).
      rewrite /valid_circuit /valid_gate in H.
      have Hcir := H (size w10{hr0} - 1). clear H.
      progress.
      have Hbounds := Hcir _. smt. clear Hcir.
      move: Hbounds.
      have <- : size w20{hr0} = size w10{hr0} by smt(). simplify.
      rewrite H.
      elim (nth witness c' (size w20{hr0} - 1)); move=>x; case x=> x1 x2; smt().

  - rewrite !nth_rcons.
    case (i < size w10{hr0}); progress.
    + smt().
    + have -> : i = size w10{hr0} by smt(size_rcons size_ge0).
      simplify.
      rewrite /valid_view in H13.
      have := H13 (size w30{hr0} - 1) _. smt.
      have <- : nth witness c' (size w10{hr0} - 1) = head witness c1{hr0}.
      + smt(nth0_head size_ge0).
      rewrite /valid_circuit /valid_gate in H.
      have Hcir := H (size w10{hr0} - 1). clear H.
      progress.
      have Hbounds := Hcir _. smt. clear Hcir.
      move: Hbounds.
      have <- : size w30{hr0} = size w10{hr0} by smt(). simplify.
      rewrite H.
      elim (nth witness c' (size w30{hr0} - 1)); move=>x; case x=> x1 x2; smt().
      
  - smt(size_behead).

  auto; progress.
  - smt().
  - smt.
  - smt.
  - smt.
  - smt.
  - rewrite /output /reconstruct.
    simplify.
    have <- := nth_last witness w100.
    have <- := nth_last witness w200.
    have <- := nth_last witness w300.
    have <- := nth_last witness tpl4.`1.
    have <- := nth_last witness tpl1.`1.
    have <- := nth_last witness tpl2.`1.
    rewrite H16 H15 H14.
    have -> := H22 (size tpl1.`1 - 1)  _. smt().
    have -> := H23 (size tpl2.`1 - 1)  _. smt().
    have -> := H24 (size tpl4.`1 - 1)  _. smt().
    by rewrite -H1 H0.
qed.

lemma list_size_elems (l : 'a list):
    size l = 3 => l = [nth witness l 0; nth witness l 1; nth witness l 2].
proof.
  smt.
qed.

lemma list_size_challenge (l : challenge list):
    size l = 3 /\ undup l = l /\
    (forall i, 0 <= i < size l => nth witness l i \in challenge) => 0 \in l /\ 1 \in l /\ 2 \in l.
proof.
  progress.
  have -> := (list_size_elems l H).
  case (nth witness l 0 = 0).
  - case (nth witness l 1 = 1).
    + have : nth witness l 2 = 2 \/ nth witness l 2 = 0 \/ nth witness l 2 = 1. smt.
      progress.
      have -> : nth witness l 2 = 2. smt.
      smt.
  - case (nth witness l 1 = 2).
    + smt. 
  case (nth witness l 0 = 1).
  - smt.
  case (nth witness l 0 = 2).
  - smt.
  smt.
  smt.
  have -> := (list_size_elems l H).
  case (nth witness l 0 = 0).
  - case (nth witness l 1 = 1).
    + have : nth witness l 2 = 2 \/ nth witness l 2 = 0 \/ nth witness l 2 = 1. smt.
      progress.
      have -> : nth witness l 2 = 2. smt.
      smt.
  - case (nth witness l 1 = 2).
    + smt. 
  case (nth witness l 0 = 1).
  - smt.
  case (nth witness l 0 = 2).
  - smt.
  smt.
  smt.
  have -> := (list_size_elems l H).
  case (nth witness l 0 = 0).
  - case (nth witness l 1 = 1).
    + have : nth witness l 2 = 2 \/ nth witness l 2 = 0 \/ nth witness l 2 = 1. smt.
      progress.
      have -> : nth witness l 2 = 2. smt.
      smt.
  - case (nth witness l 1 = 2).
    + smt. 
  case (nth witness l 0 = 1).
  - smt.
  case (nth witness l 0 = 2).
  - smt.
  smt.
  smt.
qed.


lemma soundness c' vs'' es' ys' &m:
    (forall i, 0 <= i < n => phoare[Phi.verify : c = c' /\ vs = nth witness vs'' i /\ e = i /\ ys = ys' /\ e \in challenge ==> res] = 1%r) /\
    size vs'' = size es' /\ undup es' = es' /\ size es' = 3 /\ es' = [0;1;2] /\
    (forall i, 0 <= i < size es' => nth witness es' i \in challenge) /\
    valid_circuit c' /\
    fully_consistent vs'' es' /\ size ys' = n =>
    (* (forall i, 0 <= i < n => in_doms_f n es i) (* Must reveal all views *) => *)
      Pr[Soundness(Phi).main(c', vs'', es', ys') @ &m : res] = 1%r.
proof.
   (* Change precondition *)
   progress.
   have Hver :
  forall i, 0 <= i < n => phoare[Phi.verify : c = c' /\ vs = nth witness vs'' i /\ e = i /\ ys = ys' /\ e \in challenge ==>
    valid_view_op i (nth_looping (nth witness vs'' i) 0) (nth_looping (nth witness vs'' i) 1) c' /\
         size ((nth_looping (nth witness vs'' i) 0)).`1 =
         size ((nth_looping (nth witness vs'' i) 1)).`1 /\
         size ((nth_looping (nth witness vs'' i) 0)).`1 = size c' + 1 /\
         size ((nth_looping (nth witness vs'' i) 0)).`2 =
         size ((nth_looping (nth witness vs'' i) 1)).`2 /\
         size ((nth_looping (nth witness vs'' i) 0)).`2 = size c' /\
    output (nth_looping (nth witness vs'' i) 0) = nth_looping ys' i /\ output (nth_looping (nth witness vs'' i) 1) = nth_looping ys' (i+1)] = 1%r.
   progress.
   have Ht := verify_properties_phoare c' (nth witness vs'' i) i ys'.
   by have H' := Ht (H i _); progress.

   (* Rewrite to intermediate game *)
   have -> : Pr[Soundness(Phi).main(c', vs'', [0;1;2], ys') @ &m : res]
           = Pr[Soundness_Inter.main(c', vs'', [0;1;2], ys') @ &m : res].
   - byequiv soundness_inter=>//.

   (* Prove intermediate game *)
   byphoare(: c = c' /\ vs' = vs'' /\ ys = ys' /\ es = [0;1;2] ==>)=>//.
   proc.
   sp. auto.
   conseq (: v1 = nth witness vs' 0 /\
             v2 = nth witness vs' 1 /\
             v3 = nth witness vs' 2 /\
             es = [0;1;2] /\
             (w1, k1) = nth witness v1 0 /\
             (w2, k2) = nth witness v1 1 /\
             (w2', k2') = nth witness v2 0 /\
             (w3, k3) = nth witness v2 1 /\
             (w3', k3') = nth witness v3 0 /\
             (w1', k1') = nth witness v3 1 /\ c = c' /\ vs' = vs'' /\ ys = ys' /\ 
             w1 = w1' /\ w2 = w2' /\ w3 = w3' /\ k1 = k1' /\ k2 = k2' /\ k3 = k3'
             /\ e1 = 0 /\ e2 = 1 /\ e3 = 2 /\ size ys = 3
             ==> _).
   - rewrite /fully_consistent in H5.
     progress; clear Hver.
     have := H5 2 0 0 _. split. smt(). split. smt(). split; smt.
     smt().

     have := H5 0 1 1 _. split. smt(). split. smt(). split; smt.
     smt().

     have := H5 1 2 2 _. split. smt(). split. smt(). split; smt.
     smt().

     have := H5 2 0 0 _. split. smt(). split. smt(). split; smt.
     smt().

     have := H5 0 1 1 _. split. smt(). split. smt(). split; smt.
     smt().

     have := H5 1 2 2 _. split. smt(). split. smt(). split; smt.
     smt().
     smt().

  inline Phi.decomp_global Phi.compute_fixed.
  auto.
  have := witness_extraction vs'' c' (reconstruct ys') &m.
  progress.
  rcondt 4. 
  - inline *. auto. 
  wp.
  call H7.

  have Hver2 := Hver 2 _; trivial.
  have Hver1 := Hver 1 _; trivial.
  have Hver0 := Hver 0 _; trivial.
  call Hver2.
  call Hver1.
  call Hver0. clear Hver2 Hver1 Hver0 Hver H6 H.
  auto. 
  progress.
  smt().
  smt.
  smt.
  smt().
  smt().
  smt().
  smt().
  smt().
  smt().
  clear H7. rewrite -H37.
  rewrite /nth_looping in H19. move: H19.
  simplify=>->.
  rewrite -H38.
  rewrite /nth_looping in H20. move: H20.
  simplify=>->.
  rewrite -H40.
  rewrite /nth_looping in H28. move: H28.
  simplify=>->.
  rewrite /output /reconstruct.
  simplify.
  by have -> : ys{hr} = [nth witness ys{hr} 0; nth witness ys{hr} 1; nth witness ys{hr} 2] by smt(list_size_elems).
  
  smt().
  smt().
  smt().
  smt().
  smt().

  rewrite -valid_view_reflect.
  rewrite -H37 -H38.
  smt().
  smt.
  smt.
  assumption.
qed.

lemma phi_sim_equiv g e':
    (forall cprev s,
      equiv[Phi.compute ~ Phi.simulate :
            c{1} = [g] /\ size s = size w1{1} /\ size s = size w2{1} /\ size s = size w3{1} /\
            valid_gate g (size cprev) /\ valid_circuit cprev /\
            size cprev = size w1{1} - 1 /\
            size s = size w1{1} /\
            size s = size w2{1} /\
            size s = size w3{1} /\
            size k1{1} = size w1{1} - 1 /\
            size k2{1} = size k1{1} /\
            size k3{1} = size k1{1} /\
            size k1{1} = size k1{2} /\
            size k2{1} = size k2{2} /\
            size k3{1} = size k3{2} /\
            e' \in challenge /\
            (if (e' = 0) then ={w1, w2, k1, k2}
              else
              (if (e' = 1) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
                else w3{1} = w1{2} /\ w1{1} = w2{2} /\ k3{1} = k1{2} /\ k1{1} = k2{2})) /\
             ={c} /\ e{2} = e' /\ c{1} = [g] /\
             (forall i, 0 <= i < size w1{1} => (nth witness w1{1} i) + (nth witness w2{1} i) + (nth witness w3{1} i) = (nth witness s i))
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
              (forall i, 0 <= i < size phi_w1 => (nth witness phi_w1 i) + (nth witness phi_w2 i) + (nth witness phi_w3 i) = (nth witness (eval_circuit_aux [g] s) i)) /\
              (* (exists (k1, k2, k3), phi_w1 = (rcons w1{1} (phi_decomp g 1 w1' w2' k1 k2)) /\ *)
              (*                       phi_w2 = (rcons w2{1} (phi_decomp g 2 w2' Phi.w3 k2 k3)) /\ *)
              (*                       phi_w3 = (rcons w3{1} (phi_decomp g 3 w3' w1' k3 k1))) /\ *)
            (if e' = 0 then
              (sim_k1, sim_k2, sim_w1, sim_w2) = (k1, k2, phi_w1, phi_w2)
            else
              (if e' = 1 then
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
    rcondf{2} 14. auto.
    rcondf{1} 3. auto. call (:true). auto. auto.
    progress.
    case (e' = 0); progress.
    rcondt{2} 1. auto.
    inline Phi.gate_eval. sp.
    seq 2 2 : (#pre /\ ={r1, r2}). auto; smt().
    wp.
    elim g; progress; last first.
    (* Discharge trivial case: ADDC MULTC ADD *)
    rnd; skip; smt(nth_rcons size_rcons).
    rnd; skip; smt(nth_rcons size_rcons).
    rnd; skip; progress.
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    rewrite /valid_gate in H2.
    rewrite !nth_rcons.
    rewrite -H1 -H0 -H.
    case (i < size s).
    smt().
    progress.
    case (i = size s).
    - progress.
      have <- : (x.`1, x.`2) = x by smt().
      simplify.
      have <- := H16 x.`1 _. smt().
      smt().
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).

    - (* MULT *)
      elim x=> x1 x2.
      rnd (fun z => (nth witness w2{2} x1 * nth witness w2{2} x2 + nth witness w3{1} x1 * nth witness w2{2} x2 + nth witness w2{2} x1 * nth witness w3{1} x2 + r2{2} - z)).
      skip. smt(dinput_funi size_rcons nth_rcons oget_some).
      (* skip. progress. smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* smt(dinput_funi size_rcons nth_rcons oget_some). *)
      (* rewrite /valid_gate in H2. *)
      (* rewrite !nth_rcons. *)
      (* rewrite -H1 -H0 -H. *)
      (* case (i < size s). *)
      (* smt(). *)
      (* progress. *)
      (* have -> : i = size s by smt(size_rcons). *)
      (* simplify. *)
      (* rewrite H8 H9 H10 H8 -H5. *)
      (* simplify. *)
      (* have <- := H16 x1 _. smt(). *)
      (* have <- := H16 x2 _. smt(). *)
      (* smt(). *)
      (* smt(size_rcons). *)
      (* smt(size_rcons). *)
      (* smt(size_rcons). *)
      (* have := H15; progress. *)
      (* congr.  *)
      (* rewrite !nth_rcons. *)
      (* rewrite H9 H8 H13. *)
      (* by have -> : size w1{2} - 1 = size k3{2} by smt(). *)

    case (e' = 1); progress.
    (* rnd. rnd. rnd. auto. *)
    rcondf{2} 1. auto.
    rcondt{2} 1. auto.
    inline Phi.gate_eval.
    wp. sp.
    swap{1} 1 2.
    seq 2 2 : (#pre /\ r2{1} = r1{2} /\ r3{1} = r2{2}). auto; smt().
    elim g; progress; last first.
    (* Discharge trivial case: ADDC MULTC ADD *)
    rnd; skip; smt(nth_rcons size_rcons).
    rnd; skip; smt(nth_rcons size_rcons).
    rnd; skip; progress.
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    rewrite /valid_gate in H2.
    rewrite !nth_rcons.
    rewrite -H1 -H0 -H.
    case (i < size s).
    smt().
    progress.
    case (i = size s).
    - progress.
      have <- : (x.`1, x.`2) = x by smt().
      simplify.
      have <- := H16 x.`1 _. smt().
      smt().
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).

    - (* MULT *)
      elim x=> x1 x2.
      rnd (fun z => (nth witness w3{1} x1 * nth witness w3{1} x2 + nth witness w1{1} x1 * nth witness w3{1} x2 + nth witness w3{1} x1 * nth witness w1{1} x2 + r2{2} - z)).
      skip. smt(dinput_funi size_rcons nth_rcons oget_some).

    case (e' = 2).
    rcondf{2} 1. auto.
    rcondf{2} 1. auto.
    inline Phi.gate_eval.
    wp. sp.
    swap{1} [1..2] 1.
    seq 2 2 : (#pre /\ r3{1} = r1{2} /\ r1{1} = r2{2}). auto; smt().
    elim g; progress; last first.
    (* Discharge trivial case: ADDC MULTC ADD *)
    rnd; skip; smt(nth_rcons size_rcons).
    rnd; skip; smt(nth_rcons size_rcons).
    rnd; skip; progress.
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    smt(nth_rcons size_rcons).
    rewrite /valid_gate in H2.
    rewrite !nth_rcons.
    rewrite -H1 -H0 -H.
    case (i < size s).
    smt().
    progress.
    case (i = size s).
    - progress.
      have <- : (x.`1, x.`2) = x by smt().
      simplify.
      have <- := H16 x.`1 _. smt().
      smt().
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
      smt(size_rcons).
    - (* MULT *)
      elim x=> x1 x2.
      rnd (fun z => (nth 0 w1{1} x1 * nth 0 w1{1} x2 + nth 0 w2{1} x1 * nth 0 w1{1} x2 + nth 0 w1{1} x1 * nth 0 w2{1} x2 + r2{2} - z)).
      skip. smt(dinput_funi size_rcons nth_rcons oget_some).

  exfalso. smt.
qed.


lemma phi_sim_circuit_equiv c' e':
    (forall s,
      (* s' = eval_circuit_aux c' s => *)
      equiv[Phi.compute ~ Phi.simulate :
            size s = size w1{1} /\
            size s = size w2{1} /\
            size s = size w3{1} /\
            e' \in challenge /\
            size k1{1} = size w1{1} - 1 /\
            size k2{1} = size k1{1} /\
            size k3{1} = size k1{1} /\
            size k1{1} = size k1{2} /\
            size k2{1} = size k2{2} /\
            size k3{1} = size k3{2} /\
            (if (e' = 0) then ={w1, w2, k1, k2}
              else
              (if (e' = 1) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
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
            (if e' = 0 then
              (sim_k1, sim_k2, sim_w1, sim_w2) = (k1, k2, phi_w1, phi_w2)
            else
              (if e' = 1 then
                (sim_k1, sim_k2, sim_w1, sim_w2) = (k2, k3, phi_w2, phi_w3)
              else
                (sim_k1, sim_k2, sim_w1, sim_w2) = (k3, k1, phi_w3, phi_w1))))]).
proof.
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
      e' \in challenge /\
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
      e' \in challenge /\
      (if (e' = 0) then ={w1, w2, k1, k2}
        else
        (if (e' = 1) then w2{1} = w1{2} /\ w3{1} = w2{2} /\ k2{1} = k1{2} /\ k3{1} = k2{2}
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
          (if e' = 0 then
            (sim_k1, sim_k2, sim_w1, sim_w2) = (k1, k2, phi_w1, phi_w2)
          else
            (if e' = 1 then
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
          rcondf{2} 22; auto.
          while (c1{2} = c{1} /\ w11{2} = w1{1} /\ w21{2} = w2{1} /\ w31{2} = w3{1} /\ k1{1} = k11{2} /\ k2{1} = k21{2} /\ k3{1} = k31{2}).
          auto; progress.
          auto; progress.
        exfalso. smt().
  symmetry.
  transitivity
    Phi.simulate_stepped
    (* (={c, e, w1, w2} /\ *)
    (*   c{1} = (x::l) /\ w1{1} = w1' /\ w2{1} = w2' /\ e{1} = e' *)
    (={c, w1, w2, e, k1, k2, k3} /\ c{1} = (x::l) /\
    size k1{1} = size w1{1} - 1 /\
    size k2{1} = size k1{1} /\
    size k3{1} = size k1{1} /\
    size k1{1} = size k1{2} /\
    size k2{1} = size k2{2} /\
    size k3{1} = size k3{2} /\
    e' \in challenge
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
     e' \in challenge /\
    (if (e' = 0) then ={w1, w2, k1, k2}
      else
      (if (e' = 1) then w2{2} = w1{1} /\ w3{2} = w2{1} /\ k2{2} = k1{1} /\ k3{2} = k2{1}
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
      (if e' = 0 then
        (sim_k1, sim_k2, sim_w1, sim_w2) = (k1, k2, phi_w1, phi_w2)
      else
        (if e' = 1 then
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
  have Hgate := phi_sim_equiv x e' s.
  have IH' := IH (eval_circuit_aux [x] s).
  call IH'. wp. call Hgate.
  clear IH IH' Hgate.
  auto; smt().
qed.

lemma privacy:
    equiv[Privacy(Phi).real ~ Privacy(Phi).ideal : ={c, e} /\ e{1} \in challenge /\ eval_circuit c{1} x{1} = y{2} ==> ={res}].
proof.
  proc.
  inline Phi.sample_tapes Phi.decomp Phi.share Phi.simulator.
  sp; auto.
  exists*c{1}. elim*=> c'.
  exists*e{1}. elim*=> e'.
  exists*x{1}. elim*=> x'.
  have phi_equiv := phi_sim_circuit_equiv c' e' [x'].

  case (e' = 0).
  - call phi_equiv; clear phi_equiv.
    auto; smt(nth_last).

  case (e' = 1).
  - seq 4 2 : (#pre /\ x1{2} = x20{1} /\ x30{1} = x2{2} /\ x' = x10{1} + x20{1} + x30{1}).
    sp; wp.
    swap{1} 2 - 1.
    rnd (fun z => x{1} - x20{1} - z).
    rnd.
    skip; smt(dinput_funi dinput_fu).
    exists* x1{1}; exists* x2{1}; exists* x3{1}; elim*; progress.
    call phi_equiv; clear phi_equiv.
    auto; smt(nth_last).

  
 
  

module Privacy' = {
  proc real(h : input, c : circuit, e : int, rs : random list) = {
    var w1, w2, w3, y1, y2, y3, ret, vs, vs';
    vs = Phi.decomp(c, h, rs);
    w1 = nth ([], []) vs 0;
    w2 = nth ([], []) vs 1;
    w3 = nth ([], []) vs 2;

    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);
    vs' = f vs e;
    if (e = 1) {
      ret = ([w1; w2], y3, vs');
    } else {
      if (e = 2) {
        ret = ([w2; w3], y1, vs');
      } else {
        ret = ([w3; w1], y2, vs');
      }
    }

    return ret;
  }
  proc real_local(h : input, c : circuit, e : int, rs : random list) = {
    var w1, w2, w3, y1, y2, y3, ret, vs, vs';
    vs = Phi.decomp_local(c, h);
    w1 = nth ([], []) vs 0;
    w2 = nth ([], []) vs 1;
    w3 = nth ([], []) vs 2;

    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);
    vs' = f vs e;
    if (e = 1) {
      ret = ([w1; w2], y3, vs');
    } else {
      if (e = 2) {
        ret = ([w2; w3], y1, vs');
      } else {
        ret = ([w3; w1], y2, vs');
      }
    }

    return ret;
  }
}.

(* TODO: Make global simulator *)
lemma privacy c' x' y' e':
    0 < e' /\ e' <= 3 =>
    y' = eval_circuit c' x' =>
      equiv[Privacy.real_local ~ Phi.simulator : (={c, e} /\ c{1} = c' /\ h{1} = x' /\ y{2} = y' /\ e{1} = e')
            ==> ={res, glob Phi}].
proof.
  progress.
  proc. inline Phi.output Phi.share Phi.decomp_local.
  auto.

  case (e' = 1).
  - have Heq := phi_sim_circuit_equiv c' 1 [x'].
    call Heq. clear Heq.
    auto; smt(nth_last).

  case (e' = 2).
  - sp.
    seq 3 2 : (#pre /\ x1{2} = x20{1} /\ x30{1} = x2{2} /\ x' = x10{1} + x20{1} + x30{1}).
    sp; wp.
    swap{1} 2 - 1.
    rnd (fun z => h{1} - x20{1} - z).
    rnd.
    skip; smt(dinput_funi dinput_fu).
    exists* x1{1}; exists* x2{1}; exists* x3{1}; elim*; progress.
    have Heq := phi_sim_circuit_equiv c' e' [x'].
    call Heq. clear Heq.
    auto; smt(nth_last).

 (* case e' = 3 *)
  - sp.
    seq 3 2 : (#pre /\ x1{2} = x30{1} /\ x10{1} = x2{2} /\ x' = x10{1} + x20{1} + x30{1}).
    sp; wp.
    swap{2} 2 - 1.
    rnd (fun z => h{1} - x10{1} - z).
    rnd.
    skip; smt(dinput_funi dinput_fu).
    exists* x1{1}; exists* x2{1}; exists* x3{1}; elim*; progress.
    have Heq := phi_sim_circuit_equiv c' e' [x'].
    call Heq. clear Heq.
    auto; smt(nth_last).
qed.
