(* Formalization of ZKBoo Sigma-protocol *)
require import AllCore Distr List DInterval DList Decompose DBool.
require (****) SigmaProtocols.
require import IdealCommitment.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

clone import IdealCommitment as Commit with
  type message <- (view * random_tape).

print Com.

type statement  = (circuit * int).
type witness    = int.
type message    = output * output * output * Commit.commitment * Commit.commitment * Commit.commitment.
type challenge  = int.
type response   = (random_tape * view * random_tape * view).

axiom challenge_size (c : challenge) : 0 < c <= 3.

op R_DL h w     = let (c, y) = h in (y = eval_circuit c [w]).

clone import SigmaProtocols as Sigma with
  type statement <- statement,
  type witness <- witness,
  type message <- message,
  type challenge <- challenge,
  type response <- response,

  op R = R_DL,
  op dchallenge = [1..3]
  proof *.
  realize dchallenge_llfuni.
      (* TODO: by [dt_ll, dt_funi] *)
      split. apply dinter_ll. trivial. apply is_full_funiform.
      rewrite /is_full.
      progress.
      case (0 < x <= 3).
      smt.
      move=> H.
      have : 0 < x <= 3. apply challenge_size.
      smt().
      apply dinter_uni.
  qed.
export Sigma.

pred valid_view p (view view2 : view) (c : circuit) (k1 k2 : random_tape) =
  (forall i, 0 <= i /\ i + 1 < size view =>
    (nth 0 view (i + 1)) = phi_decomp (nth (ADDC(0,0)) c i) i p view view2 k1 k2).

op valid_view_op p (view view2 : view) (c : circuit) (k1 k2 : random_tape) =
  (foldr (fun i acc,
            acc /\ (nth 0 view (i + 1)) = phi_decomp (nth (ADDC(0,0)) c i) i p view view2 k1 k2)
    true (range 0 (size view - 1))).

lemma foldr_range_forall i j p b:
    (foldr (fun k b, b /\ p k) b (range i j)) =
     (b /\ forall k, i <= k <= j-1 => p k).
proof.
   case (i < j)=> i_j_rel; last smt.
   pose n := j - i; cut ->: j = n + i by smt.
   cut: 0 <= n by smt.
   elim /intind n; first by smt.
   progress.
   pose k := i + i0.
   have : range i (i0 + 1 + i) = range i (k + 1) by smt().
   rewrite rangeSr. smt(). progress; subst.
   rewrite H1.
   rewrite - cats1.
   rewrite foldr_cat.
   simplify.
   have -> : (range i k) = range i (i0 + i) by smt().
   cut ->: i0 + 1 + i - 1 = i0 + i by smt.
admitted.

lemma valid_view_equiv p w1 w2 c k1 k2:
    valid_view p w1 w2 c k1 k2 <=> valid_view_op p w1 w2 c k1 k2.
proof.
  split.
  simplify valid_view valid_view_op.
  rewrite foldr_range_forall.
  progress.
  smt.
  simplify valid_view valid_view_op.
  rewrite foldr_range_forall.
  progress.
  smt.
qed.

op valid_view_output y w = last 0 w = y.

op valid_output_shares (y y1 y2 y3 : int) = y = y1 + y2 + y3.

module ZKBoo(C : Committer) : SProtocol = {
  var w1, w2, w3 : view
  var k1, k2, k3 : view
  proc gen() : statement * witness = {
    return (([], 0),0);
  }
  proc init(h : statement, w : witness) = {
    var x1,x2,x3,y,c,c1,c2,c3,y1,y2,y3;
    (c, y) = h;
    (x1, x2, x3) = Phi.share(w);
    k1 = [];
    k2 = [];
    k3 = [];
    (k1, k2, k3, w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3], k1, k2, k3);
    c1 = C.commit((w1, k1));
    c2 = C.commit((w2, k2));
    c3 = C.commit((w3, k3));
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);

    return (y1,y2,y3,c1,c2,c3);
  }

  proc response(h : statement, w : witness, m : message, e : challenge) = {
    var ret;
    if (e = 1) {
      ret = (k1, w1, k2, w2);
    } else {
      if (e = 2) {
        ret = (k2, w2, k3, w3);
      } else {
        ret = (k3, w3, k1, w1);
      }
    }
    return ret;
  }

  proc verify(h : statement, m : message, e : challenge, z : response) = {
    var c, open, y1, y2, y3, c1, c2, c3, y, valid_com1, valid_com2;
    var valid_share1, valid_share2, valid, valid_length;
    var w1', w2', w3', k1', k2', k3';
    open = z;
    (y1, y2, y3, c1, c2, c3) = m;
    (c, y) = h;

    if (e = 1) {
      (k1', w1', k2', w2') = open;
      valid_com1 = verify (w1', k1') c1;
      valid_com2 = verify (w2', k2') c2;
      valid_share1 = valid_view_output y1 w1';
      valid_share2 = valid_view_output y2 w2';
      valid = valid_view_op 1 w1' w2' c k1' k2';
      valid_length = size c = size w1' - 1 /\ size w1' = size w2';
    } else {
      if (e = 2) {
        (k2', w2', k3', w3') = open;
        valid_com1 = verify (w2', k2') c2;
        valid_com2 = verify (w3', k3') c3;
        valid_share1 = valid_view_output y2 w2';
        valid_share2 = valid_view_output y3 w3';
        valid = valid_view_op 2 w2' w3' c k2' k3';
        valid_length = size c = size w2' - 1 /\ size w2' = size w3';
      } else {
        (k3', w3', k1', w1') = open;
        valid_com2 = verify (w1', k1') c1;
        valid_com1 = verify (w3', k3') c3;
        valid_share1 = valid_view_output y3 w3';
        valid_share2 = valid_view_output y1 w1';
        valid = valid_view_op 3 w3' w1' c k3' k1';
        valid_length = size c = size w3' - 1 /\ size w3' = size w1';
      }
    }

    (*TODO: Add circuit validation? *)
    return valid_output_shares y y1 y2 y3 /\ valid_com1 /\ valid_com2 /\ valid_share1 /\ valid_share2 /\ valid /\ valid_length;

  }

  proc witness_extractor(h : statement, a : message,
                         e : challenge list, z : response list) = {
    var c, y, open, ret;
    var w1'', w2'', w3'';
    var w1', w2', w3';
    var k1'', k2'', k3'';
    var k1', k2', k3';
    (c, y) = h;
    open = oget (onth z 0);
    (k1'', w1'', k2'', w2'') = open;
    open = oget (onth z 1);
    (k2', w2', k3'', w3'') = open;
    open = oget (onth z 2);
    (k3', w3', k1', w1') = open;

    if (k1'' = k1' /\ w1'' = w1' /\ k2'' = k2' /\ w2'' = w2' /\ k3'' = k3' /\ w3'' = w3') {
      ret = Some( (oget (onth w1' 0)) + (oget (onth w2' 0)) + (oget (onth w3' 0)) );
    } else {
      ret = None;
    }

    return ret;


  }

  proc simulator(h : statement, e : challenge) = {
    var c, y, views, a, z;
    var w1, w2, w3, y1, y2, y3;
    var c1, c2, c3;
    var k1, k2;
    (c, y) = h;
    if (e = 1) {
      (views, y3) = Privacy.ideal(y, c, e);
      (k1, w1, k2, w2) = views;
      w3 <$ dlist dinput (size w1);
      k3 <$ dlist dinput (size k1);
      y1 = Phi.output(w1);
      y2 = Phi.output(w2);

      c1 = C.commit((w1, k1));
      c2 = C.commit((w2, k2));
      c3 = C.commit((w3, k3));
      z = (k1, w1, k2, w2);
    } else {
      if (e = 2) {
        (views, y1) = Privacy.ideal(y, c, e);
        (k2, w2, k3, w3) = views;
        w1 <$ dlist dinput (size w2);
        k1 <$ dlist dinput (size k2);
        y2 = Phi.output(w2);
        y3 = Phi.output(w3);

        c1 = C.commit((w1, k1));
        c2 = C.commit((w2, k2));
        c3 = C.commit((w3, k3));
        z = (k2, w2, k3, w3);
      } else {
        (views, y2) = Privacy.ideal(y, c, e);
        (k3, w3, k1, w1) = views;
        w2 <$ dlist dinput (size w3);
        k2 <$ dlist dinput (size k3);
        y3 = Phi.output(w3);
        y1 = Phi.output(w1);

        c1 = C.commit((w1, k1));
        c2 = C.commit((w2, k2));
        c3 = C.commit((w3, k3));
        z = (k3, w3, k1, w1);
      }
    }
    a = (y1, y2, y3, c1, c2, c3);

    return (a, z);
  }

}.

section Protocol.

declare module Com : Commit.Committer{ZKBoo}.

(* Assume security of Com *)
(* axiom Com_correct &m a : Pr[Correctness(Com).main(a) @ &m : res] = 1%r. *)
const binding_prob : real.

axiom Com_correct :
    phoare[Correctness(Com).main : true ==> res] = 1%r.
axiom Com_hiding_alt :
  equiv[Com.commit ~ Com.commit : ={glob Com} ==> ={res, glob Com}].
axiom Com_binding_pr c m1 m2 &m:
  Pr[BindingGame(Com).main(c, m1, m2) @ &m : ! res] = binding_prob.
lemma Com_binding :
  phoare[BindingGame(Com).main : true ==> ! res] = binding_prob by bypr=> &m H; smt(Com_binding_pr).
axiom Com_ll: islossless Com.commit.

axiom bind_three_equiv c1 c2 c3 a1 a1' a2 a2' a3 a3' &m:
    Pr[BindingGame(Com).bind_three(c1, c2, c3, a1, a1', a2, a2', a3, a3') @ &m : ! res] = binding_prob.

lemma Com_binding_three :
    phoare[BindingGame(Com).bind_three : true ==> ! res] = binding_prob.
proof.
    bypr=> &m Pre.
    smt(bind_three_equiv).
qed.

lemma binding_pred_implies_cons c1 c2 c3 m1 m1' m2 m2' m3 m3' &m:
    Pr[BindingGame(Com).bind_three(c1, c2, c3, m1, m1', m2, m2', m3, m3') @ &m : !res] =
    Pr[BindingGame(Com).bind_three(c1, c2, c3, m1, m1', m2, m2', m3, m3') @ &m :
      !(verify m1 c1 /\
        verify m1' c1 /\
        verify m2 c2 /\
        verify m2' c2 /\
        verify m3 c3 /\
        verify m3' c3 /\
        ((m1 = m1') /\ (m2 = m2') /\ (m3 = m3')))].
proof.
   byequiv=>//.
   proc*.
   inline *. auto.
qed.

lemma binding_three_cons_pr c1 c2 c3 a1 a1' a2 a2' a3 a3' &m:
    Pr[BindingGame(Com).bind_three(c1, c2, c3, a1, a1', a2, a2', a3, a3') @ &m :
      !(verify a1 c1 /\
        verify a1' c1 /\
        verify a2 c2 /\
        verify a2' c2 /\
        verify a3 c3 /\
        verify a3' c3 /\
        ((a1 = a1') /\ (a2 = a2') /\ (a3 = a3')))] = binding_prob.
proof.
    have Hbind := bind_three_equiv c1 c2 c3 a1 a1' a2 a2' a3 a3' &m.
    have <- := Com_binding_pr c1 a1 a1' &m.
    have <- := binding_pred_implies_cons c1 c2 c3 a1 a1' a2 a2' a3 a3' &m.
    smt.
qed.

lemma binding_three_cons c1' c2' c3' a1 a1' a2 a2' a3 a3':
    islossless BindingGame(Com).bind_three =>
    phoare[BindingGame(Com).bind_three : c1 = c1' /\ c2 = c2' /\ c3 = c3' /\ m1 = a1 /\ m1' = a1' /\ m2 = a2 /\ m2' = a2' /\ m3 = a3 /\ m3' = a3'
          ==> !(verify a1 c1' /\
                verify a1' c1' /\
                verify a2 c2' /\
                verify a2' c2' /\
                verify a3 c3' /\
                verify a3' c3' /\
                ((a1 = a1') /\ (a2 = a2') /\ (a3 = a3')))] = binding_prob.
proof.
    move=> bg_ll.
    bypr=> &m Pre.
    smt(binding_three_cons_pr).
qed.

lemma Com_binding_three_valid :
    islossless BindingGame(Com).bind_three =>
    phoare[BindingGame(Com).bind_three : true ==> res] = (1%r - binding_prob).
proof.
    move=> bg_ll.
    phoare split ! (1%r) binding_prob.
    proc*. call bg_ll.
    auto.
    bypr=> &m Pre.
    by have <- := bind_three_equiv c1{m} c2{m} c3{m} m1{m} m1'{m} m2{m} m2'{m} m3{m} m3'{m} &m.
qed.

lemma binding_valid_pred_implies_cons c1 c2 c3 m1 m1' m2 m2' m3 m3' &m:
    Pr[BindingGame(Com).bind_three(c1, c2, c3, m1, m1', m2, m2', m3, m3') @ &m : res] =
    Pr[BindingGame(Com).bind_three(c1, c2, c3, m1, m1', m2, m2', m3, m3') @ &m :
       (verify m1 c1 /\
        verify m1' c1 /\
        verify m2 c2 /\
        verify m2' c2 /\
        verify m3 c3 /\
        verify m3' c3 /\
        ((m1 = m1') /\ (m2 = m2') /\ (m3 = m3')))].
proof.
   byequiv=>//.
   proc*.
   inline *. auto.
qed.

lemma binding_three_cons_valid c1' c2' c3' a1 a1' a2 a2' a3 a3':
    islossless BindingGame(Com).bind_three =>
    phoare[BindingGame(Com).bind_three : c1 = c1' /\ c2 = c2' /\ c3 = c3' /\ m1 = a1 /\ m2 = a2 /\ m3 = a3 /\ m1' = a1' /\ m2' = a2' /\ m3' = a3'
           ==> (verify a1 c1' /\
                verify a1' c1' /\
                verify a2 c2' /\
                verify a2' c2' /\
                verify a3 c3' /\
                verify a3' c3' /\
                ((a1 = a1') /\ (a2 = a2') /\ (a3 = a3')))] = (1%r - binding_prob).
proof.
    move=> bg_ll.
    phoare split ! (1%r) binding_prob.
    proc.
    call (:true).
    auto.
    call (:true).
    auto.
    call (:true).
    auto. auto.

    have Hvalid := binding_three_cons c1' c2' c3' a1 a1' a2 a2' a3 a3' bg_ll.
    proc*. call Hvalid.
    auto.
qed.

local module Intermediate = {
  module ComCorrectness = Correctness(Com)

  proc main(h : statement, w : witness, e : challenge) = {
    var x1,x2,x3,y1,y2,y3,k1,k2,k3;
    var c,y,w1,w2,w3,valid_com1,valid_com2,valid_share1,valid_share2,valid,valid_length;
    (c, y) = h;
    (x1, x2, x3) = Phi.share(w);
    k1 = [];
    k2 = [];
    k3 = [];
    (k1, k2, k3, w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3], k1, k2, k3);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);
    if (e = 1) {
      valid_com1 = ComCorrectness.main((w1, k1));
      valid_com2 = ComCorrectness.main((w2, k2));
      Com.commit((w3, k3));
      valid_share1 = valid_view_output y1 w1;
      valid_share2 = valid_view_output y2 w2;
      valid = valid_view_op 1 w1 w2 c k1 k2;

      (*NOTE: Difference from paper : we need this information *)
      valid_length = size c = size w1 - 1 /\ size w1 = size w2;
    } else {
      if (e = 2) {
        Com.commit((w1, k1));
        valid_com1 = ComCorrectness.main((w2, k2));
        valid_com2 = ComCorrectness.main((w3, k3));
        valid_share1 = valid_view_output y2 w2;
        valid_share2 = valid_view_output y3 w3;
        valid = valid_view_op 2 w2 w3 c k2 k3;
        valid_length = size c = size w2 - 1 /\ size w2 = size w3;
      } else {
        valid_com2 = ComCorrectness.main((w1, k1));
        Com.commit((w2, k2));
        valid_com1 = ComCorrectness.main((w3, k3));
        valid_share1 = valid_view_output y3 w3;
        valid_share2 = valid_view_output y1 w1;
        valid = valid_view_op 3 w3 w1 c k3 k1;
        valid_length = size c = size w3 - 1 /\ size w3 = size w1;
      }
    }

    return valid_output_shares y y1 y2 y3 /\ valid_com1 /\ valid_com2 /\ valid_share1 /\ valid_share2 /\ valid /\ valid_length;
  }
}.

local lemma inter_completeness h' w' e' &m:
    R h' w' /\ valid_circuit h'.`1 =>
    Pr[Intermediate.main(h', w', e') @ &m : res] = 1%r.
proof.
  rewrite /R /R_DL. rewrite pairS.
  progress.
  byphoare(: (h = h' /\ w = w' /\ e = e') ==>)=>//; last first. smt().
  proc.
  case (e' = 1).
    rcondt 10. auto. do ? call(:true); auto.
    inline *.
    auto.
    inline Phi.output Phi.share.
    sp. wp.
    call Com_ll.
    call Com_correct.
    call Com_correct.
    auto.
    have Hcircuit := compute_circuit_correct h'.`1 [w'] [].
    call Hcircuit. clear Hcircuit.
    auto; progress.
    apply dinput_ll.
    smt().
    smt().
    smt().
    smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt(nth_last size_ge0).
    rewrite /valid_view_op.
    rewrite foldr_range_forall.
    progress.
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
  case (e' = 2).
    rcondf 10. auto. do ? call(:true); auto.
    inline *.
    auto.
    rcondt 10. auto. do ? call(:true); auto.
    inline Phi.output Phi.share.
    auto.
    inline Phi.output Phi.share.
    sp. wp.
    call Com_correct.
    call Com_correct.
    call Com_ll.
    auto.
    have Hcircuit := compute_circuit_correct h'.`1 [w'] [].
    call Hcircuit.
    auto; progress.
    apply dinput_ll.
    smt().
    smt().
    smt().
    smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt(nth_last size_ge0).
    rewrite /valid_view_op.
    rewrite foldr_range_forall.
    progress.
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
  (* case (e' = 2) *)
    rcondf 10. auto. do ? call(:true); auto.
    inline Phi.output Phi.share.
    auto.
    rcondf 10. auto. do ? call(:true); auto.
    inline Phi.output Phi.share.
    auto.
    inline Phi.output Phi.share.
    sp. wp.
    call Com_correct.
    call Com_ll.
    call Com_correct.
    auto.
    have Hcircuit := compute_circuit_correct h'.`1 [w'] [].
    call Hcircuit.
    auto; progress.
    apply dinput_ll.
    smt().
    smt().
    smt().
    smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt(nth_last size_ge0).
    rewrite /valid_view_op.
    rewrite foldr_range_forall.
    progress.
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
qed.

local equiv inter_equiv :
    Sigma.Completeness(ZKBoo(Com)).special ~ Intermediate.main :
    ={h, w, e, glob Com} /\ R h{1} w{1} ==> ={res}.
proof.
  proc.
  inline ZKBoo(Com).init ZKBoo(Com).response ZKBoo(Com).verify.
  sp.
  case (e{1} = 1).
  rcondt{1} 17. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondt{2} 9. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondt{1} 26. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  inline Phi.reconstruct Intermediate.ComCorrectness.main.
  swap{2} [6..8] 9.
  auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto. sim.
  call (:true); auto.

  case (e{1} = 2).
  rcondf{1} 17. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondt{1} 17. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondf{2} 9. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondt{2} 9. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{1} 26. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondt{1} 26. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  inline Phi.reconstruct Intermediate.ComCorrectness.main.
  swap{2} [6..8] 9.
  wp.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto. sim.
  call (:true); auto.

  (* case e = 3 *)
  rcondf{1} 17. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondf{1} 17. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondf{2} 9. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{2} 9. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{1} 26. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondf{1} 26. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  inline Phi.reconstruct Intermediate.ComCorrectness.main.
  swap{2} [6..8] 9.
  wp.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto. sim.
  call (:true); auto.
qed.

lemma zkboo_completeness h' w' e' &m:
    R h' w' /\ valid_circuit h'.`1 =>
    Pr[Sigma.Completeness(ZKBoo(Com)).special(h', w', e') @ &m : res] = 1%r.
proof.
  move=> rel.
  have -> : Pr[Completeness(ZKBoo(Com)).special(h', w', e') @ &m : res] =
            Pr[Intermediate.main(h', w', e') @ &m : res].
  - byequiv inter_equiv=>/#.
  by have := inter_completeness h' w' e' &m rel.
qed.

(* module type Distinguisher = { *)
(*   proc * get(h : statement) : challenge *)
(*   proc guess(a : message, e : challenge, z : response) : bool *)
(* }. *)

(* local module ZKBooSHVZKGame (D : Distinguisher) = { *)
(*   module SHVZKGames = SHVZK(ZKBoo(Com)) *)

(*   proc main(h : statement, w : witness) = { *)
(*     var b, b', a, e, z, trans; *)
(*     b <$ dbool; *)
(*     e = D.get(h); *)
(*     if (b) { *)
(*       trans = SHVZKGames.real(h, w, e); *)
(*       (a, e, z) = oget trans; *)
(*     } else { *)
(*       trans = SHVZKGames.ideal(h, e); *)
(*       (a, e, z) = oget trans; *)
(*     } *)
(*     b' = D.guess(a, e, z); *)

(*     return (b = b'); *)
(*   } *)
(* }. *)

(* local module ZKBooSHVZKGame' (D : Distinguisher) = { *)
(*   module ZK = ZKBoo(Com) *)
(*   module SHVZKGames = SHVZK(ZK) *)

(*   proc main(h : statement, w : witness) = { *)
(*     var b, b', a, e, z, trans; *)
(*     b <$ dbool; *)
(*     e = D.get(h); *)
(*     if (b) { *)
(*       a = ZK.init(h, w); *)
(*       z = ZK.response(h, w, a, e); *)
(*     } else { *)
(*       trans = SHVZKGames.ideal(h, e); *)
(*       (a, e, z) = oget trans; *)
(*     } *)
(*     b' = D.guess(a, e, z); *)

(*     return (b = b'); *)
(*   } *)
(* }. *)

(* local equiv inter_shvzk (D <: Distinguisher): *)
(*     ZKBooSHVZKGame(D).main ~ ZKBooSHVZKGame'(D).main : *)
(*     ={h, w} ==> ={res}. *)
(* proof. *)
(*     proc. *)
(*     sim. *)
(*     seq 2 2 : (#pre /\ ={b, e}). *)
(*     call (:true). *)
(*     auto. *)
(*     if; progress. *)
(*     - auto. *)
(*       inline ZKBooSHVZKGame(D).SHVZKGames.real. *)
(*       sp. wp. *)
(*       inline ZKBoo(Com).verify. *)
(*       inline Phi.reconstruct. *)
(*       auto. *)
(*       case (e{1} = 1). *)
(*       rcondt{1} 10. auto. *)
(*       call (:true). auto. *)
(*       call (:true). auto. *)
(*       auto. *)
(*       inline ZKBoo(Com).valid_output_share Phi.output. *)
(*       auto. *)
(*       call (:true). sim. *)

(* local lemma zkboo_shvzk (D <: Distinguisher) (A <: HidingAdv) h w &m: *)
(*     Pr[ZKBooSHVZKGame(D).main(h, w) @ &m : res] <= *)
(*     Pr[HidingGame(Com, A).main() @ &m : res]. *)
(* proof. *)
(*     byequiv=>//. *)
(*     proc. *)
(*     inline ZKBooSHVZKGame(D).SHVZKGames.real. *)


equiv zkboo_shvzk:
    SHVZK(ZKBoo(Com)).real ~ SHVZK(ZKBoo(Com)).ideal :
    ={h, e, glob Com} /\ h{1}.`2 = eval_circuit h{1}.`1 [w{1}] /\ e{2} \in dchallenge ==> ={res}.
proof.
  proc.
  auto.
  exists* h{1}.`1. elim*=> c.
  exists* e{2}. elim*=> e.
  exists* w{1}. elim*=> w.
  call (:true). sim.
  progress.
  inline ZKBoo(Com).simulator.
  inline ZKBoo(Com).response.
  inline ZKBoo(Com).init.
  auto.
  case (e = 1).
    rcondt{2} 4. auto.
    swap{2} [8..9] 4.
    swap{1} 14 -2.
    auto.
    call (:true). sim.
    call (:true). sim.
    inline Phi.output. auto.
    call Com_hiding_alt.
    call (:true).
    call (:true).
    wp. sp.
    inline Privacy.ideal Phi.share Phi.output. auto.
    have Hsim := phi_sim_circuit_equiv c e [w].
    call Hsim. clear Hsim.
    auto. smt(dlist_ll dinput_ll nth_last).
  case (e = 2).
    rcondf{2} 4. auto.
    rcondt{2} 4. auto.
    swap{2} [8..9] 4.
    call (:true). sim.
    call (:true). sim.
    inline Phi.output. auto.
    call (:true).
    call (:true).
    call Com_hiding_alt.
    wp. sp.
    inline Privacy.ideal Phi.share Phi.output. auto.
    have Hsim := phi_sim_circuit_equiv c e [w].
    call Hsim. clear Hsim.
    wp. sp.
    swap{1} 1 1.
    rnd (fun x => (w - x20{1}) - x).
    rnd.
    auto. smt(dlist_ll dinput_ll dinput_funi dinput_fu nth_last).
  case (e = 3).
    rcondf{2} 4. auto.
    rcondf{2} 4. auto.
    swap{2} [8..9] 4.
    swap{1} 12 2.
    call (:true). sim.
    call (:true). sim.
    inline Phi.output. auto.
    call (:true).
    call Com_hiding_alt.
    call (:true).
    wp. sp.
    inline Privacy.ideal Phi.share Phi.output. auto.
    have Hsim := phi_sim_circuit_equiv c e [w].
    call Hsim. clear Hsim.
    wp. sp.
    swap{2} 1 1.
    rnd (fun x => (w - x2{2}) - x).
    rnd.
    auto. smt(dlist_ll dinput_ll dinput_funi dinput_fu nth_last).

    exfalso. smt.
qed.

(* special soundness section *)
(* Two proofs: *)
(*  1) proof that all opened views are equal to the views in the first message *)
(*  2) witness can be reconstructed from the three views*)

(* Notes: *)
(* What is a? *)
(* what is z? *)
(* Properties I need: *)
(* 1. View w1 in a commitment *)
(* 2. \forall i w[i] = phi_decomp*)

local module SoundnessInter = {
  module ZK = ZKBoo(Com)
  module BGame = BindingGame(Com)
  proc extract_views(h : statement, m : message, z1 z2 z3 : response) = {
    var k1,k2,k3,k1',k2',k3';
    var w1,w2,w3,w1',w2',w3';
    var cons, v1, v2, v3;
    var y1, y2, y3, c1, c2, c3;

    v1 = ZK.verify(h, m, 1, z1);
    v2 = ZK.verify(h, m, 2, z2);
    v3 = ZK.verify(h, m, 3, z3);

    (k1, w1, k2, w2) = z1;
    (k2', w2', k3, w3) = z2;
    (k3', w3', k1', w1') = z3;
    (y1, y2, y3, c1, c2, c3) = m;
    cons = BGame.bind_three(c1, c2, c3, (w1, k1), (w1', k1'), (w2, k2), (w2', k2'), (w3, k3), (w3', k3'));

    return v1 /\ v2 /\ v3;
  }

  proc main(h : statement, m : message, z1 z2 z3 : response) = {
    var v, w, w_get, ret;
    v = extract_views(h, m, z1, z2, z3);
    w = ZK.witness_extractor(h, m, [1;2;3], [z1;z2;z3]);

    if (w = None) {
      ret = false;
    } else{
      w_get = oget w;
      ret = v /\ R h w_get;
    }
    return ret;
  }
}.

local equiv soundness_inter :
  Sigma.SpecialSoundness(ZKBoo(Com)).main ~ SoundnessInter.main :
  ={h, m} /\ c{1} = [1;2;3] /\ z{1} = [z1{2};z2{2};z3{2}] ==> ={res}.
proof.
  proc.
  sp.
  swap{2} 1 1.
  rcondt{1} 1. auto.
  rcondt{1} 7. auto. call (:true). auto. auto.
  rcondt{1} 13. auto. call (:true). auto. auto. call (:true). auto. auto.
  rcondf{1} 19. auto. call (:true). auto. auto. call (:true). auto. auto. call (:true). auto. auto.
  inline SoundnessInter.extract_views.
  swap{2} [7..9] 5.
  swap{2} 1 13.
  sp.
  wp. call (:true). sim.
  wp. call (:true). sim.
  wp. call (:true). sim.
  wp. call (:true). sim.
  auto; progress.
  inline *.
  auto; smt().
qed.

pred validate_response w1 w2 w3 w1' w2' w3' y y1 y2 y3 c' k1 k2 k3 k1' k2' k3' =
    w1 = w1' /\ w2 = w2' /\ w3 = w3' /\
    k1 = k1' /\ k2 = k2' /\ k3 = k3'
            /\ valid_output_shares y y1 y2 y3
            /\ valid_view 1 w1 w2 c' k1 k2
            /\ valid_view 2 w2 w3 c' k2 k3
            /\ valid_view 3 w3 w1 c' k3 k1
            /\ valid_view_output y1 w1
            /\ valid_view_output y2 w2
            /\ valid_view_output y3 w3
            /\ valid_circuit c'
            /\ size c' = size w1 - 1
            /\ size w1 = size w2
            /\ size w1 = size w3.

local lemma extraction_success
      c' y y1 y2 y3 c1 c2 c3
      w1 w2 w3 w1' w2' w3'
      k1 k2 k3 k1' k2' k3':
  islossless BindingGame(Com).bind_three =>
  phoare[ZKBoo(Com).verify :
      h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k1, w1, k2, w2) ==>
      res /\ valid_output_shares y y1 y2 y3 /\ valid_view 1 w1 w2 c' k1 k2 /\ valid_view_output y1 w1 /\ valid_view_output y2 w2
      /\ valid_circuit c'
      /\ size c' = size w1 - 1 /\ size w1 = size w2 /\ verify (w1, k1) c1 /\ verify (w2,k2) c2] = 1%r =>
  phoare[ZKBoo(Com).verify :
      h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k2', w2', k3, w3) ==>
      res /\ valid_output_shares y y1 y2 y3 /\ valid_view 2 w2' w3 c' k2' k3 /\ valid_view_output y2 w2' /\ valid_view_output y3 w3
      /\ valid_circuit c'
      /\ size c' = size w2' - 1 /\ size w2' = size w3 /\ verify (w2', k2') c2 /\ verify (w3, k3) c3] = 1%r =>
  phoare[ZKBoo(Com).verify :
      h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k3', w3', k1', w1') ==>
      res /\ valid_output_shares y y1 y2 y3 /\ valid_view 3 w3' w1' c' k3' k1' /\ valid_view_output y3 w3' /\ valid_view_output y1 w1'
      /\ valid_circuit c'
      /\ size c' = size w3' - 1 /\ size w3' = size w1' /\ verify (w3', k3') c3 /\ verify (w1', k1') c1] = 1%r =>
  phoare[SoundnessInter.extract_views :
      h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z1 = (k1, w1, k2, w2) /\ z2 = (k2', w2', k3, w3) /\ z3 = (k3', w3', k1', w1')
      ==> res /\ (validate_response w1 w2 w3 w1' w2' w3' y y1 y2 y3 c' k1 k2 k3 k1' k2' k3')] = (1%r - binding_prob).
proof.
    move=> bg_ll accept1 accept2 accept3.
    proc.
    auto.
    have Hcons := binding_three_cons_valid c1 c2 c3 (w1, k1) (w1', k1') (w2, k2) (w2', k2') (w3, k3) (w3', k3') bg_ll.
    call Hcons. clear Hcons.
    auto.
    call accept3.
    call accept2.
    call accept1.
    auto.
    progress.
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
qed.

lemma zkboo_soundness_if_consistent
      c' y y1 y2 y3 c1 c2 c3
      k1' k2' k3' w1 w2 w3 &m:
  phoare[ZKBoo(Com).witness_extractor :
          valid_output_shares y y1 y2 y3
          /\ valid_view 1 w1 w2 c' k1' k2'
          /\ valid_view 2 w2 w3 c' k2' k3'
          /\ valid_view 3 w3 w1 c' k3' k1'
          /\ valid_view_output y1 w1
          /\ valid_view_output y2 w2
          /\ valid_view_output y3 w3
          /\ size c' = size w1 - 1
          /\ size w1 = size w2
          /\ size w1 = size w3
          /\ valid_circuit c' /\ h = (c',y) /\ a = (y1,y2,y3,c1,c2,c3) /\ z = [(k1', w1, k2', w2);(k2', w2, k3', w3);(k3', w3, k1', w1)]
         ==> res <> None /\ R (c',y) (oget res)] = 1%r.
proof.
  proc.
  auto.
  rewrite /valid_output_share /valid_view_output; progress.
  rewrite !oget_some.
  clear H7 H8 H9 H10 H11 H12.
  rewrite /R /R_DL.
  progress.
  rewrite /valid_output_shares in H.
  rewrite /valid_view in H0.
  rewrite /valid_view in H1.
  rewrite /valid_view in H2.
  have H' := eval_circuit_module c' [oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0)] y &m.
  apply H'. clear H'.
  have <- :
    Pr[Phi.main(oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0), c') @ &m :
      res = y] =
    Pr[Circuit.eval(c', [oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0)]) @ &m :
      res = y].
  byequiv correctness_module=>//.
  have -> :
    Pr[Phi.main(oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0), c') @ &m :
      res = y] =
    Pr[Phi.main_fixed_input_and_tape(oget (onth w1 0), oget (onth w2 0), oget (onth w3 0), c' , k1', k2', k3') @ &m :
      res = y].
  byequiv main_fixed_equiv=>//.
  rewrite H.
  byphoare(: valid_circuit c' /\ c = c' /\ k1 = k1' /\ k2 = k2' /\ k3 = k3' /\ x1 = (oget (onth w1 0)) /\ x2 = (oget (onth w2 0)) /\ x3 = (oget (onth w3 0)) ==> res = last 0 w1 + last 0 w2 + last 0 w3)=>//.
  proc.
  inline Phi.reconstruct Phi.output.
  wp.
  inline *.
  auto.
  while (size w10 = size w1 - size c0 /\
         size w20 = size w2 - size c0 /\
         size w30 = size w3 - size c0 /\
         size c' = size c0 + size w10 - 1 /\
         k10 = k1' /\
         k20 = k2' /\
         k30 = k3' /\
         0 < size w10 /\
         0 < size w20 /\
         0 < size w30 /\
         (forall i, 0 <= i < size c0 => (nth (ADDC(0,0)) c0 i = nth (ADDC(0,0)) c' (size w10 - 1 + i) /\ (size w10 -1 + i) < size c')) /\
         (forall i, i < size w10 => nth 0 w1 i = nth 0 w10 i) /\
         (forall i, i < size w20 => nth 0 w2 i = nth 0 w20 i) /\
         (forall i, i < size w30 => nth 0 w3 i = nth 0 w30 i))
        (size c0).
  auto.
  progress.
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  have H14' := H14 (i + 1) _. smt().
  rewrite size_rcons.
  have -> := nth_behead (ADDC(0,0)) c0{hr0} i _. smt().
  smt.
  smt(size_rcons).

  rewrite !nth_rcons.
  case (i < size w10{hr0});progress.
  smt.
  case (i = size w10{hr0}); progress.
  have -> := H0 (size w10{hr0} - 1) _. smt.
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H18.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w10{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H6.
  have := H6 (size w10{hr0} - 1) _. smt.
  have -> := onth_nth (ADDC(0,0)) c' (size w10{hr0} - 1). smt.
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w10{hr0} - 1)); move=>x; case x=> x1 x2.
  simplify.
        smt.
        smt.
        simplify.
        progress.
        have : x1 < size w10{hr0}. smt.
        smt.
        smt.
        smt.
  rewrite !nth_rcons.
  case (i < size w20{hr0});progress.
  smt.
  case (i = size w20{hr0}); progress.
  have -> := H1 (size w20{hr0} - 1) _. smt.
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H18.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w20{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H6.
  have := H6 (size w20{hr0} - 1) _. smt.
  have -> := onth_nth (ADDC(0,0)) c' (size w20{hr0} - 1). smt.
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w20{hr0} - 1)); move=>x; case x=> x1 x2.
  simplify.
        smt.
        smt.
        simplify.
        progress.
        have : x1 < size w20{hr0}. smt.
        smt.
        smt.
        smt.
  rewrite !nth_rcons.
  case (i < size w30{hr0});progress.
  smt.
  case (i = size w30{hr0}); progress.
  have -> := H2 (size w30{hr0} - 1) _. smt.
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H18.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w30{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H6.
  have := H6 (size w30{hr0} - 1) _. smt.
  have -> := onth_nth (ADDC(0,0)) c' (size w30{hr0} - 1). smt.
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w30{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).
  smt(size_rcons head_behead).
  auto.
  progress.
  apply dinput_ll.
  smt().
  smt().
  smt().
  case (i = 0); progress.
  smt(onth_nth oget_some size_ge0).
  smt.
  case (i = 0); progress.
  smt(onth_nth oget_some size_ge0).
  smt.
  case (i = 0); progress.
  smt(onth_nth oget_some size_ge0).
  smt.
  smt.
  smt(nth_last).
qed.


local lemma zkboo_inter_soundness
    c' y y1 y2 y3 c1 c2 c3
    w1 w2 w3 w1' w2' w3'
    k1 k2 k3 k1' k2' k3' &m:
    islossless BindingGame(Com).bind_three =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k1, w1, k2, w2) ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 1 w1 w2 c' k1 k2 /\ valid_view_output y1 w1 /\ valid_view_output y2 w2
        /\ valid_circuit c'
        /\ size c' = size w1 - 1 /\ size w1 = size w2 /\ verify (w1, k1) c1 /\ verify (w2,k2) c2] = 1%r =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k2', w2', k3, w3) ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 2 w2' w3 c' k2' k3 /\ valid_view_output y2 w2' /\ valid_view_output y3 w3
        /\ valid_circuit c'
        /\ size c' = size w2' - 1 /\ size w2' = size w3 /\ verify (w2', k2') c2 /\ verify (w3, k3) c3] = 1%r =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k3', w3', k1', w1') ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 3 w3' w1' c' k3' k1' /\ valid_view_output y3 w3' /\ valid_view_output y1 w1'
        /\ valid_circuit c'
        /\ size c' = size w3' - 1 /\ size w3' = size w1' /\ verify (w3', k3') c3 /\ verify (w1', k1') c1] = 1%r =>
    phoare[SoundnessInter.main :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z1 = (k1, w1, k2, w2) /\ z2 = (k2', w2', k3, w3) /\ z3 = (k3', w3', k1', w1')
        ==> res] = (1%r - binding_prob).
proof.
  move=> bg_ll accept1 accept2 accept3.
  (* phoare split (1%r - binding_prob) binding_prob : (validate_response w1 w2 w3 w1' w2' w3' y y1 y2 y3 c' k1 k2 k3 k1' k2' k3'). *)
  proc.
  inline SoundnessInter.ZK.witness_extractor.
  auto.
  inline SoundnessInter.extract_views.
  (* call (: validate_response w1 w2 w3 w1' w2' w3' y y1 y2 y3 c' k1 k2 k3 k1' k2' k3'). *)


  auto.
  have Hcons := binding_three_cons_valid c1 c2 c3 (w1, k1) (w1', k1') (w2, k2) (w2', k2') (w3, k3) (w3', k3') bg_ll.
  call Hcons. clear Hcons.
  auto.
  call accept3.
  call accept2.
  call accept1.
  auto.
  rewrite /valid_output_share /valid_view_output; progress.
  rewrite !oget_some.
  clear accept1 accept2 accept3 H25 H31 H32 H33 H34 H35 H36 H37 H26 H30 H8 H17 H20 H10 H19 H27 H24.
  rewrite /R /R_DL.
  progress.
  rewrite /valid_output_shares in H0.
  rewrite /valid_view in H1.
  rewrite /valid_view in H18.
  rewrite /valid_view in H9.
  clear H29 H28 H15 H6 H14 H11 H21 H5.
  have H' := eval_circuit_module c' [oget (onth w1' 0) + oget (onth w2' 0) + oget (onth w3' 0)] y &m.
  apply H'. clear H'.
  have <- :
    Pr[Phi.main(oget (onth w1' 0) + oget (onth w2' 0) + oget (onth w3' 0), c') @ &m :
      res = y] =
    Pr[Circuit.eval(c', [oget (onth w1' 0) + oget (onth w2' 0) + oget (onth w3' 0)]) @ &m :
      res = y].
  byequiv correctness_module=>//.
  have -> :
    Pr[Phi.main(oget (onth w1' 0) + oget (onth w2' 0) + oget (onth w3' 0), c') @ &m :
      res = y] =
    Pr[Phi.main_fixed_input_and_tape(oget (onth w1' 0), oget (onth w2' 0), oget (onth w3' 0), c' , k1', k2', k3') @ &m :
      res = y].
  byequiv main_fixed_equiv=>//.
  rewrite H0.
  byphoare(: valid_circuit c' /\ c = c' /\ k1 = k1' /\ k2 = k2' /\ k3 = k3' /\ x1 = (oget (onth w1' 0)) /\ x2 = (oget (onth w2' 0)) /\ x3 = (oget (onth w3' 0)) ==> res = last 0 w1' + last 0 w2' + last 0 w3')=>//.
  proc.
  inline Phi.reconstruct Phi.output.
  wp.
  inline *.
  auto.
  while (size w10 = size w1' - size c0 /\
         size w20 = size w2' - size c0 /\
         size w30 = size w3' - size c0 /\
         size c' = size c0 + size w10 - 1 /\
         k10 = k1' /\
         k20 = k2' /\
         k30 = k3' /\
         0 < size w10 /\
         0 < size w20 /\
         0 < size w30 /\
         (forall i, 0 <= i < size c0 => (nth (ADDC(0,0)) c0 i = nth (ADDC(0,0)) c' (size w10 - 1 + i) /\ (size w10 -1 + i) < size c')) /\
         (forall i, i < size w10 => nth 0 w1' i = nth 0 w10 i) /\
         (forall i, i < size w20 => nth 0 w2' i = nth 0 w20 i) /\
         (forall i, i < size w30 => nth 0 w3' i = nth 0 w30 i))
        (size c0).
  auto.
  progress.
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(nth_behead size_rcons).
  smt(size_rcons).

  rewrite !nth_rcons.
  case (i < size w10{hr0}); first smt().
  case (i = size w10{hr0}); progress.
  have -> := H1 (size w10{hr0} - 1) _. smt(size_ge0).
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H24.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w10{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H2.
  have := H2 (size w10{hr0} - 1) _. smt(size_ge0).
  have -> := onth_nth (ADDC(0,0)) c' (size w10{hr0} - 1). smt(size_ge0).
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w10{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).

  rewrite !nth_rcons.
  case (i < size w20{hr0}); first smt().
  case (i = size w20{hr0}); progress.
  have -> := H9 (size w20{hr0} - 1) _. smt(size_ge0).
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H24.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w20{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H2.
  have := H2 (size w20{hr0} - 1) _. smt(size_ge0).
  have -> := onth_nth (ADDC(0,0)) c' (size w20{hr0} - 1). smt(size_ge0).
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w20{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).

  rewrite !nth_rcons.
  case (i < size w30{hr0}); first smt().
  case (i = size w30{hr0}); progress.
  have -> := H18 (size w30{hr0} - 1) _. smt(size_ge0).
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H24.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w30{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H2.
  have := H2 (size w30{hr0} - 1) _. smt(size_ge0).
  have -> := onth_nth (ADDC(0,0)) c' (size w30{hr0} - 1). smt(size_ge0).
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w30{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).
  smt().

  auto.
  smt(onth_nth oget_some size_ge0 dinput_ll nth_out nth_last).
  smt(nth_last).
  smt(nth_last).
  smt(nth_last).
  smt(nth_last).
  smt(nth_last).
  smt(nth_last).
qed.


lemma zkboo_soundness
    c' y y1 y2 y3 c1 c2 c3
    w1 w2 w3 w1' w2' w3'
    k1 k2 k3 k1' k2' k3' &m:
    islossless BindingGame(Com).bind_three =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k1, w1, k2, w2) ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 1 w1 w2 c' k1 k2 /\ valid_view_output y1 w1 /\ valid_view_output y2 w2
        /\ valid_circuit c'
        /\ size c' = size w1 - 1 /\ size w1 = size w2 /\ verify (w1, k1) c1 /\ verify (w2,k2) c2] = 1%r =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k2', w2', k3, w3) ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 2 w2' w3 c' k2' k3 /\ valid_view_output y2 w2' /\ valid_view_output y3 w3
        /\ valid_circuit c'
        /\ size c' = size w2' - 1 /\ size w2' = size w3 /\ verify (w2', k2') c2 /\ verify (w3, k3) c3] = 1%r =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k3', w3', k1', w1') ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 3 w3' w1' c' k3' k1' /\ valid_view_output y3 w3' /\ valid_view_output y1 w1'
        /\ valid_circuit c'
        /\ size c' = size w3' - 1 /\ size w3' = size w1' /\ verify (w3', k3') c3 /\ verify (w1', k1') c1] = 1%r =>
    Pr[Sigma.SpecialSoundness(ZKBoo(Com)).main((c',y), (y1,y2,y3,c1,c2,c3), [1;2;3], [(k1, w1, k2, w2); (k2', w2', k3, w3); (k3', w3', k1', w1')]) @ &m :res]
        = (1%r - binding_prob).
proof.
  move=> bg_ll accept1 accept2 accept3.
  have -> :
    Pr[SpecialSoundness(ZKBoo(Com)).main((c', y), (y1, y2, y3, c1, c2, c3), [1; 2; 3], [(k1, w1, k2, w2); (k2', w2', k3, w3); (k3', w3', k1', w1')]) @ &m : res] =
    Pr[SoundnessInter.main((c', y), (y1, y2, y3, c1, c2, c3), (k1, w1, k2, w2), (k2', w2', k3, w3), (k3', w3', k1', w1') ) @ &m : res].
  byequiv soundness_inter=>//.

  byphoare(: h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z1 = (k1, w1, k2, w2) /\ z2 = (k2', w2', k3, w3) /\ z3 = (k3', w3', k1', w1') ==> _)=>//.
  proc*.
  have Hsuccess := zkboo_inter_soundness c' y y1 y2 y3 c1 c2 c3 w1 w2 w3 w1' w2' w3' k1 k2 k3 k1' k2' k3' &m bg_ll accept1 accept2 accept3.
  call Hsuccess.
  skip. progress.
qed.


end section Protocol.
