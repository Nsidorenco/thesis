(* Formalization of ZKBoo Sigma-protocol *)
require import AllCore Distr List DInterval DList Decompose DBool.
require (****) SigmaProtocols.
require import Commitment.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

clone import Commitment as Commit with
  type message <- view.

print Com.

type statement  = (circuit * int).
type witness    = int.
type message    = public_key * output * output * output * Commit.commitment * Commit.commitment * Commit.commitment.
type challenge  = int.
type response   = ((random_tape * view) * randomness) * ((random_tape * view) * randomness).

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
  var r1, r2, r3 : randomness
  var w1, w2, w3 : view
  var k1, k2, k3 : view
  proc gen() : statement * witness = {
    return (([], 0),0);
  }
  proc init(h : statement, w : witness) = {
    var x1,x2,x3,y,c,c1,c2,c3,sk,pk,y1,y2,y3;
    (c, y) = h;
    (sk, pk) = C.key_gen();
    (x1, x2, x3) = Phi.share(w);
    k1 = [];
    k2 = [];
    k3 = [];
    (k1, k2, k3, w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3], k1, k2, k3);
    (c1, r1) = C.commit(sk, w1);
    (c2, r2) = C.commit(sk, w2);
    (c3, r3) = C.commit(sk, w3);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);

    return (pk,y1,y2,y3,c1,c2,c3);
  }

  proc response(h : statement, w : witness, m : message, e : challenge) = {
    var ret;
    if (e = 1) {
      ret = (((k1, w1), r1), ((k2, w2), r2));
    } else {
      if (e = 2) {
        ret = (((k2, w2), r2), ((k3, w3), r3));
      } else {
        ret = (((k3, w3), r3), ((k1, w1), r1));
      }
    }
    return ret;
  }

  proc verify(h : statement, m : message, e : challenge, z : response) = {
    var c, pk, open, y1, y2, y3, c1, c2, c3, y, valid_com1, valid_com2;
    var valid_share1, valid_share2, valid;
    var w1', w2', w3', r1', r2', r3', o1, o2, k1', k2', k3';
    open = z;
    (pk, y1, y2, y3, c1, c2, c3) = m;
    (c, y) = h;

    if (e = 1) {
      (o1, r1') = fst open;
      (o2, r2') = snd open;
      (k1', w1') = o1;
      (k2', w2') = o2;
      valid_com1 = verify pk w1' c1 r1';
      valid_com2 = verify pk w2' c2 r2';
      valid_share1 = valid_view_output y1 w1';
      valid_share2 = valid_view_output y2 w2';
      valid = valid_view_op 1 w1' w2' c k1' k2';
    } else {
      if (e = 2) {
        (o1, r2') = fst open;
        (o2, r3') = snd open;
        (k2', w2') = o1;
        (k3', w3') = o2;
        valid_com1 = verify pk w2' c2 r2';
        valid_com2 = verify pk w3' c3 r3';
        valid_share1 = valid_view_output y2 w2';
        valid_share2 = valid_view_output y3 w3';
        valid = valid_view_op 2 w2' w3' c k2' k3';
      } else {
        (o1, r3') = fst open;
        (o2, r1') = snd open;
        (k3', w3') = o1;
        (k1', w1') = o2;
        valid_com2 = verify pk w1' c1 r1';
        valid_com1 = verify pk w3' c3 r3';
        valid_share1 = valid_view_output y3 w3';
        valid_share2 = valid_view_output y1 w1';
        valid = valid_view_op 3 w3' w1' c k3' k1';
      }
    }

    return valid_output_shares y y1 y2 y3 /\ valid_com1 /\ valid_com2 /\ valid_share1 /\ valid_share2 /\ valid;

  }

  proc witness_extractor(h : statement, a : message,
                         e : challenge list, z : response list) = {
    var c, y, open, ret;
    var w1, w2, w3, r1, r2, r3;
    var w1', w2', w3', r1', r2', r3';
    var o1, o2, o3, k1, k2, k3;
    var o1', o2', o3', k1', k2', k3';
    (c, y) = h;
    open = oget (onth z 0);
    (o1, r1) = fst open;
    (o2, r2) = snd open;
    (k1, w1) = o1;
    (k2, w2) = o2;
    open = oget (onth z 1);
    (o2', r2') = fst open;
    (o3, r3) = snd open;
    (k2', w2') = o2';
    (k3, w3) = o3;
    open = oget (onth z 2);
    (o3', r3') = fst open;
    (o1', r1') = snd open;
    (k3', w3') = o3';
    (k1', w1') = o1';

    if (k1 = k1' /\ w1 = w1' /\ k2 = k2' /\ w2 = w2' /\ k3 = k3' /\ w3 = w3') {
      ret = Some( (oget (onth w1 0)) + (oget (onth w2 0)) + (oget (onth w3 0)) );
    } else {
      ret = None;
    }

    return ret;


  }

  proc simulator(h : statement, e : challenge) = {
    var c, y, views, sk, pk, a, z;
    var w1, w2, w3, y1, y2, y3;
    var c1, c2, c3, r1, r2, r3;
    var k1, k2;
    (c, y) = h;
    (sk, pk) = C.key_gen();
    if (e = 1) {
      (views, y3) = Privacy.ideal(y, c, e);
      (k1, w1, k2, w2) = views;
      w3 <$ dlist dinput (size w1);
      y1 = Phi.output(w1);
      y2 = Phi.output(w2);

      (c1, r1) = C.commit(sk, w1);
      (c2, r2) = C.commit(sk, w2);
      (c3, r3) = C.commit(sk, w3);
      z = (((k1, w1), r1), ((k2, w2), r2));
    } else {
      if (e = 2) {
        (views, y1) = Privacy.ideal(y, c, e);
        (k2, w2, k3, w3) = views;
        w1 <$ dlist dinput (size w2);
        y2 = Phi.output(w2);
        y3 = Phi.output(w3);

        (c1, r1) = C.commit(sk, w1);
        (c2, r2) = C.commit(sk, w2);
        (c3, r3) = C.commit(sk, w3);
        z = (((k2, w2), r2), ((k3, w3), r3));
      } else {
        (views, y2) = Privacy.ideal(y, c, e);
        (k3, w3, k1, w1) = views;
        w2 <$ dlist dinput (size w3);
        y3 = Phi.output(w3);
        y1 = Phi.output(w1);

        (c1, r1) = C.commit(sk, w1);
        (c2, r2) = C.commit(sk, w2);
        (c3, r3) = C.commit(sk, w3);
        z = (((k3, w3), r3), ((k1, w1), r1));
      }
    }
    a = (pk, y1, y2, y3, c1, c2, c3);

    return (a, z);
  }

}.

section Protocol.

declare module Com : Commit.Committer{ZKBoo}.

(* Assume security of Com *)
(* axiom Com_correct &m a : Pr[Correctness(Com).main(a) @ &m : res] = 1%r. *)

axiom key_gen_correct :
    phoare[Com.key_gen : true ==> valid_key res] = 1%r.
axiom Com_correct :
    phoare[Correctness(Com).key_fixed : valid_key (sk, pk) ==> res] = 1%r.
axiom Com_hiding &m (A <: HidingAdv):
  Pr[HidingGame(Com, A).main() @ &m : res] = 1%r.
axiom Com_hiding_alt :
  equiv[Com.commit ~ Com.commit : ={sk, glob Com} ==> ={res, glob Com}].
axiom Com_binding &m (A <: BindingAdv):
  Pr[BindingGame(Com, A).main() @ &m : res] = 1%r.
axiom commit_ll : islossless Com.commit.


local module Intermediate = {
  module ComCorrectness = Correctness(Com)

  proc main(h : statement, w : witness, e : challenge) = {
    var x1,x2,x3,sk,pk,y1,y2,y3,k1,k2,k3;
    var c,y,w1,w2,w3,valid_com1,valid_com2,valid_share1,valid_share2,valid;
    (c, y) = h;
    (x1, x2, x3) = Phi.share(w);
    k1 = [];
    k2 = [];
    k3 = [];
    (k1, k2, k3, w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3], k1, k2, k3);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);
    (sk, pk) = Com.key_gen();
    if (e = 1) {
      valid_com1 = ComCorrectness.key_fixed(w1, sk, pk);
      valid_com2 = ComCorrectness.key_fixed(w2, sk, pk);
      Com.commit(sk, w3);
      valid_share1 = valid_view_output y1 w1;
      valid_share2 = valid_view_output y2 w2;
      valid = valid_view_op 1 w1 w2 c k1 k2;
    } else {
      if (e = 2) {
        Com.commit(sk, w1);
        valid_com1 = ComCorrectness.key_fixed(w2, sk, pk);
        valid_com2 = ComCorrectness.key_fixed(w3, sk, pk);
        valid_share1 = valid_view_output y2 w2;
        valid_share2 = valid_view_output y3 w3;
        valid = valid_view_op 2 w2 w3 c k2 k3;
      } else {
        valid_com2 = ComCorrectness.key_fixed(w1, sk, pk);
        Com.commit(sk, w2);
        valid_com1 = ComCorrectness.key_fixed(w3, sk, pk);
        valid_share1 = valid_view_output y3 w3;
        valid_share2 = valid_view_output y1 w1;
        valid = valid_view_op 3 w3 w1 c k3 k1;
      }
    }

    return valid_output_shares y y1 y2 y3 /\ valid_com1 /\ valid_com2 /\ valid_share1 /\ valid_share2 /\ valid;
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
    rcondt 11. auto. do ? call(:true); auto.
    inline *.
    auto.
    inline Phi.output Phi.share.
    sp. wp.
    call commit_ll.
    call Com_correct.
    call Com_correct.
    call key_gen_correct.
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
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt(nth_last size_ge0).
    rewrite /valid_view_op.
    rewrite foldr_range_forall.
    progress.
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
  case (e' = 2).
    rcondf 11. auto. do ? call(:true); auto.
    inline *.
    auto.
    rcondt 11. auto. do ? call(:true); auto.
    inline Phi.output Phi.share.
    auto.
    inline Phi.output Phi.share.
    sp. wp.
    call Com_correct.
    call Com_correct.
    call commit_ll.
    call key_gen_correct.
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
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt(nth_last size_ge0).
    rewrite /valid_view_op.
    rewrite foldr_range_forall.
    progress.
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt().
  (* case (e' = 2) *)
    rcondf 11. auto. do ? call(:true); auto.
    inline Phi.output Phi.share.
    auto.
    rcondf 11. auto. do ? call(:true); auto.
    inline Phi.output Phi.share.
    auto.
    inline Phi.output Phi.share.
    sp. wp.
    call Com_correct.
    call commit_ll.
    call Com_correct.
    call key_gen_correct.
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
    smt().
    have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt().
    smt(nth_last size_ge0).
    rewrite /valid_view_op.
    rewrite foldr_range_forall.
    progress.
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
  rcondt{1} 18. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  rcondt{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondt{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  inline Phi.reconstruct Intermediate.ComCorrectness.key_fixed.
  swap{2} 9 - 8.
  swap{2} [7..9] 13.
  (* swap{2} [17..18] 4. *)
  (* swap{2} [11..12] 8. *)
  auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto. sim.
  call (:true); auto.
  call (:true); auto.

  case (e{1} = 2).
  rcondf{1} 18. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  rcondt{1} 18. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  rcondf{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondt{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  rcondt{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  inline Phi.reconstruct.
  inline Intermediate.ComCorrectness.key_fixed.
  swap{2} [6..8] 14.
  swap{2} 6 - 5.
  swap{2} [18..19] 3.
  swap{2} [12..13] 7.
  wp.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto. sim.
  call (:true); auto.
  call (:true); auto.

  (* case e = 3 *)
  rcondf{1} 18. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  rcondf{1} 18. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  rcondf{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  rcondf{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *. auto. call (:true). auto.
  inline Phi.reconstruct.
  inline Intermediate.ComCorrectness.key_fixed.
  swap{2} [6..8] 14.
  swap{2} 6 - 5.
  swap{2} [18..19] 3.
  swap{2} [11..12] 8.
  wp.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto. sim.
  call (:true); auto.
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
  inline ZKBoo(Com).simulator.
  inline ZKBoo(Com).response.
  inline ZKBoo(Com).init.
  auto.
  case (e = 1).
    rcondt{2} 5. auto. call (:true). auto.
    swap{2} [8..9] 4.
    swap{1} 15 -2.
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
    auto. call (:true).
    auto. smt(dlist_ll dinput_ll nth_last).
  case (e = 2).
    rcondf{2} 5. auto. call (:true). auto.
    rcondt{2} 5. auto. call (:true). auto.
    swap{2} [8..9] 4.
    call (:true). sim.
    call (:true). sim.
    inline Phi.output. auto.
    call (:true).
    call (:true).
    call Com_hiding_alt.
    (* swap{1} 4 5. *)
    wp. sp.
    inline Privacy.ideal Phi.share Phi.output. auto.
    have Hsim := phi_sim_circuit_equiv c e [w].
    call Hsim. clear Hsim.
    wp. sp.
    swap{1} 3 1.
    rnd (fun x => (w - x20{1}) - x).
    rnd.
    wp. call (:true).
    auto. smt(dlist_ll dinput_ll dinput_funi dinput_fu nth_last).
  case (e = 3).
    rcondf{2} 5. auto. call (:true). auto.
    rcondf{2} 5. auto. call (:true). auto.
    swap{2} [8..9] 4.
    swap{1} 13 2.
    call (:true). sim.
    call (:true). sim.
    inline Phi.output. auto.
    call (:true).
    call Com_hiding_alt.
    call (:true).
    (* swap{1} 4 5. *)
    wp. sp.
    inline Privacy.ideal Phi.share Phi.output. auto.
    have Hsim := phi_sim_circuit_equiv c e [w].
    call Hsim. clear Hsim.
    wp. sp.
    swap{2} 5 1.
    rnd (fun x => (w - x2{2}) - x).
    rnd.
    wp. call (:true).
    auto. smt(dlist_ll dinput_ll dinput_funi dinput_fu nth_last).

    exfalso. smt.
qed.

(* special soundness section *)
(* Two proofs: *)
(*  1) proof that all opened views are equal to the views in the first message *)
(*  2) witness can be reconstructed from the three views*)

lemma zkboo_verify_success h' a' e' z' &m:
    Pr[ZKBoo(Com).verify(h', a', e', z') @ &m : res] =
    Pr[ZKBoo(Com).verify(h', a', e', z') @ &m : res].
admitted.

(* Notes: *)
(* What is a? *)
(* what is z? *)
(* Properties I need: *)
(* 1. View w1 in a commitment *)
(* 2. \forall i w[i] = phi_decomp*)

local module SoundnessInter = {
  module ZK = ZKBoo(Com)
  var v1, v2, v3 : bool
  proc extract_views(h : statement, m : message, z1 z2 z3 : response) = {
    v1 = ZK.verify(h, m, 1, z1);
    v2 = ZK.verify(h, m, 2, z2);
    v3 = ZK.verify(h, m, 3, z3);

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
      ret = v1 /\ v2 /\ v3 /\ R h w_get;
    }
    return ret;
  }

  proc verify_views(pk : public_key, c : commitment, y, w1 w2 : view, r1 r2 : randomness) = {
    var v1, v2, v_share1, v_share2;
    v1 = verify pk w1 c r1;
    v2 = verify pk w2 c r2;
    v_share1 = valid_view_output y w1;
    v_share2 = valid_view_output y w2;

    return v1 /\ v2 /\ v_share1 /\ v_share2;
  }

  proc extract_views_inlined(h : statement, m : message, z1 z2 z3 : response) = {
    var c, pk, open1, open2, open3, y1, y2, y3, c1, c2, c3, y;
    var o11, o21, o12, o22, o13, o23;
    var k11, w11, k21, w21;
    var k22, w22, k32, w32;
    var k33, w33, k13, w13;
    var r11, r21;
    var r22, r32;
    var r33, r13;
    var valid_w1, valid_w2, valid_w3;

    open1 = z1;
    open2 = z2;
    open3 = z3;
    (pk, y1, y2, y3, c1, c2, c3) = m;
    (c, y) = h;

    (* open z1 *)
    (o11, r11) = fst open1;
    (o21, r21) = snd open1;
    (k11, w11) = o11;
    (k21, w21) = o21;

    (* open z2 *)
    (o12, r22) = fst open2;
    (o22, r32) = snd open2;
    (k22, w22) = o12;
    (k32, w32) = o22;

    (* open z3 *)
    (o13, r33) = fst open3;
    (o23, r13) = snd open3;
    (k33, w33) = o13;
    (k13, w13) = o23;

    valid_w1 = verify_views(pk, c1, y1, w11, w13, r11, r13);
    valid_w2 = verify_views(pk, c2, y2, w21, w22, r21, r22);
    valid_w3 = verify_views(pk, c3, y3, w32, w33, r32, r33);

    return valid_output_shares y y1 y2 y3 /\ valid_w1 /\ valid_w2 /\ valid_w3;

  }
}.


(* Proof idea: *)
(* If responses differ, then they can be used as the binding adversary *)
(* This will break the assumption of binding *)

(* local equiv extracted_views : *)
(*   SoundnessInter.extract_views ~ SoundnessInter.extract_views_inlined : *)
(*   ={h, m, z1, z2, z3} ==> ={res}. *)
(* proof. *)
(*   proc. *)
(*   inline *. auto. *)
(*   smt(). *)
(* qed. *)

(* local lemma verify_view pk' c' y' w1' w2' r1' r2': *)
(*   phoare[SoundnessInter.verify_view : *)
(*          pk = pk' /\ c = c' /\ w1 = w1' /\ w2 = w2' /\ r1 = r1' /\ r2 = r2' *)
(*          ==> res /\ y = ] *)


local equiv soundness_inter :
  Sigma.SpecialSoundness(ZKBoo(Com)).main ~ SoundnessInter.main :
  ={h, m} /\ c{1} = [1;2;3] /\ z{1} = [z1{2};z2{2};z3{2}] ==> ={res}.
proof.
  proc.
  sp.
  rcondt{1} 1. auto.
  rcondt{1} 7. auto. call (:true). auto. auto.
  rcondt{1} 13. auto. call (:true). auto. auto. call (:true). auto. auto.
  rcondf{1} 19. auto. call (:true). auto. auto. call (:true). auto. auto. call (:true). auto. auto.
  inline SoundnessInter.extract_views.
  wp. call (:true). sim.
  wp. call (:true). sim.
  wp. call (:true). sim.
  wp. call (:true). sim.
  auto; progress.
  smt().
qed.

local lemma zkboo_inter_views
      c' y y1 y2 y3 c1 c2 c3 pk
      k1 k2 k3 w1 w2 w3 r1 r2 r3 &m:
  phoare[SoundnessInter.extract_views :
         h = (c',y) /\ m = (pk,y1,y2,y3,c1,c2,c3) /\ z1 = (((k1, w1), r1), ((k2, w2), r2)) /\ z2 = (((k2, w2), r2), ((k3, w3), r3)) /\ z3 = (((k3, w3), r3), ((k1, w1), r1))
          ==> res /\ valid_output_shares y y1 y2 y3
                  /\ valid_view 1 w1 w2 c' k1 k2
                  /\ valid_view 2 w2 w3 c' k2 k3
                  /\ valid_view 3 w3 w1 c' k3 k1
                  /\ valid_view_output y1 w1
                  /\ valid_view_output y2 w2
                  /\ valid_view_output y3 w3
                  /\ size c' = size w1 - 1
                  /\ size w1 = size w2
                  /\ size w1 = size w3] = 1%r.
proof.
  (* proc. *)
  (* inline *. *)
  (* rcondt 8. auto. *)
  (* rcondf 38. auto. call (:true). auto. *)
  (* rcondt 38. auto. call (:true). auto. *)
  (* rcondf 68. auto. call (:true). auto. *)
  (* rcondf 68. auto. call (:true). auto. *)
  (* auto. *)
  (* call (:true). auto. *)
admitted.

local lemma zkboo_inter_views
      c' y y1 y2 y3 c1 c2 c3 pk
      k1' k2' k3' w1 w2 w3 r1 r2 r3 &m:
  phoare[SoundnessInter.main :
         valid_circuit c' /\ h = (c',y) /\ m = (pk,y1,y2,y3,c1,c2,c3) /\ z1 = (((k1', w1), r1), ((k2', w2), r2)) /\ z2 = (((k2', w2), r2), ((k3', w3), r3)) /\ z3 = (((k3', w3), r3), ((k1', w1), r1))
         ==> res] = 1%r.
proof.
  proc.
  inline SoundnessInter.ZK.witness_extractor.
  auto.
  have H := zkboo_inter_views c' y y1 y2 y3 c1 c2 c3 pk k1' k2' k3' w1 w2 w3 r1 r2 r3 &m.
  call H. clear H.
  skip; rewrite /valid_output_share /valid_view_output; progress.
  admit.
  admit.
  admit.
  rewrite !oget_some.
  clear H8 H9 H10 H11 H12 H13.
  rewrite /R /R_DL.
  progress.
  rewrite /valid_output_shares in H1.
  rewrite /valid_view in H2.
  rewrite /valid_view in H3.
  rewrite /valid_view in H4.
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
    Pr[Phi.main_fixed(oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0), c' , k1', k2', k3') @ &m :
      res = y].
  byequiv main_fixed_equiv=>//.
  rewrite H1.
  byphoare(: valid_circuit c' /\ c = c' /\ k1 = k1' /\ k2 = k2' /\ k3 = k3' /\ h = oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0) ==> res = last 0 w1 + last 0 w2 + last 0 w3)=>//.
  proc.
  inline Phi.reconstruct Phi.output.
  wp.
  inline *.
  auto.
  (* while ((forall i, *)
  (*           nth 0 w1 i + nth 0 w2 i + nth 0 w3 i = nth 0 w10 i + nth 0 w20 i + nth 0 w30 i) *)
  (*         /\ size w10 = size w20 *)
  (*         /\ size w10 = size w30 *)
  (*         /\ size w10 = size w1 - size c0 - 1 *)
  (*         /\ size w20 = size w2 - size c0 - 1 *)
  (*         /\ size w30 = size w3 - size c0 - 1) *)
  (*       (size c0). *)
  while ((forall i, nth (ADDC(0,0)) c0 i = nth (ADDC(0,0)) c' (size w10 - 1 + i)) /\
         size w10 = size w1 - size c0 /\
         size w20 = size w2 - size c0 /\
         size w30 = size w3 - size c0 /\
         k10 = k1' /\
         k20 = k2' /\
         k30 = k3' /\
         0 < size w10 /\
         0 < size w20 /\
         0 < size w30 /\
         (forall i, i < size w10 => nth 0 w1 i = nth 0 w10 i) /\
         (forall i, i < size w20 => nth 0 w2 i = nth 0 w20 i) /\
         (forall i, i < size w30 => nth 0 w3 i = nth 0 w30 i))
        (size c0).
  auto.
  progress.
  rewrite size_rcons.
  have H18' := H8 i.
  admit.
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  rewrite !nth_rcons.
  case (i < size w10{hr0});progress.
  smt.
  case (i = size w10{hr0}); progress.
  have -> := H2 (size w10{hr0} - 1) _. smt.
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H18.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w10{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head).
  rewrite /valid_circuit /valid_gate in H.
  have := H (size w10{hr0} - 1) _. smt.
  have -> := onth_nth (ADDC(0,0)) c' (size w10{hr0} - 1). smt.
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w10{hr0} - 1)); move=>x; case x=> x1 x2.
  (* elim (head  (ADDC(0,0)) c0{hr0}); move=>x; case x=> x1 x2. *)
  simplify.
        smt.
        smt.
        simplify.
        progress.
        have : x1 < size w10{hr0}. smt.
        smt.
        smt.
        smt.
  admit.
  admit.
  smt(size_rcons head_behead).
  auto.
  progress.
  apply dinput_ll.
  smt().
  smt().
  smt().
        rewrite /predT in H11.
        smt.

  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  rewrite !nth_rcons - H9 - H10.
  case (i < size w10{hr0}); progress.
  smt.
  case (i = size w10{hr0}); progress.
  have -> := H2 (size w10{hr0} - 1) _. admit.
  have -> := H3 (size w10{hr0} - 1) _. admit.
  have -> := H4 (size w10{hr0} - 1) _. admit.
  elim
  smt.


  apply dinput_ll.
  have -> := ohead_head (ADDC(0,0)) c0{hr0} _; trivial.
  rewrite nth_rcons.
  case (i < size w10{hr0}); progress.
  smt.
  case (i = size w10{hr0}); progress.
  rewrite oget_some.
  smt.
  smt.
  smt(size_rcons head_behead).
  smt(size_rcons head_behead).
  smt(size_rcons head_behead).
  smt(size_rcons head_behead).
  auto.
  progress.
  apply dinput_ll.
  smt.
  smt.
  smt.
  smt().
  smt().
  smt().
  smt.
  have <- := nth_last 0 w100.
  have <- := nth_last 0 w200.
  have <- := nth_last 0 w300.
  have <- := nth_last 0 w1.
  have <- := nth_last 0 w2.
  have <- := nth_last 0 w3.
  have := H15 (size w100 -1) _. smt.
  smt.

  byphoare.
  byphoare(: valid_circuit c' /\ c = c' /\ h = oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0) ==> res = eval_circuit c' [oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0)])=>//.
    admit.
    smt().
                  (* TODO: lift eval_circuit to a Pr[statement] *)


local lemma zkboo_inter_soundness
      c' y y1 y2 y3 c1 c2 c3 pk
      k11 k21 w11 w21 r11 r21
      k22 k32 w22 w32 r22 r32
      k33 k13 w33 w13 r33 r13 &m:
    phoare[ZKBoo(Com, Ver).verify : h = (c', y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z =  (pk, (((k11, w11), r11), ((k21, w21), r21))) ==> res ] = 1%r =>
    phoare[ZKBoo(Com, Ver).verify : h = (c', y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z =  (pk, (((k22, w22), r22), ((k32, w32), r32))) ==> res ] = 1%r =>
    phoare[ZKBoo(Com, Ver).verify : h = (c', y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z =  (pk, (((k33, w33), r33), ((k13, w13), r13))) ==> res ] = 1%r =>
    Pr[SoundnessInter(ZKBoo(Com, Ver)).main((c', y), (y1,y2,y3,c1,c2,c3), (pk, (((k11, w11), r11), ((k21, w21), r21))), (pk, (((k22, w22), r22), ((k32, w32), r32))), (pk, (((k33, w33), r33), ((k13, w13), r13)))) @ &m : res] = 1%r.
proof.
  move=> accept1 accept2 accept3.
  byphoare(: h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z1 = (pk, (((k11, w11), r11), ((k21, w21), r21))) /\ z2 = (pk, (((k22, w22), r22), ((k32, w32), r32))) /\ z3 = (pk, (((k33, w33), r33), ((k13, w13), r13))) ==>)=>//.
  proc.
  inline ZKBoo(Com, Ver).witness_extractor.
  wp.
  call accept3.
  call accept2.
  call accept1.
  skip; progress.
  rewrite /R /R_DL.
  rewrite /eval_circuit.



lemma zkboo_soundness c' y y1 y2 y3 c1 c2 c3 pk
      k11 k21 w11 w21 r11 r21
      k22 k32 w22 w32 r22 r32
      k33 k13 w33 w13 r33 r13 &m:
    Pr[Sigma.SpecialSoundness(ZKBoo(Com, Ver)).main((c', y), (y1,y2,y3,c1,c2,c3), [1;2;3], [(pk, (((k11, w11), r11), ((k21, w21), r21))); (pk, (((k22, w22), r22), ((k32, w32), r32))); (pk, (((k33, w33), r33), ((k13, w13), r13)))]) @ &m : res] = 1%r.
proof.
  byphoare(: h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ c = [1;2;3] /\ z = [(pk, (((k11, w11), r11), ((k21, w21), r21))); (pk, (((k22, w22), r22), ((k32, w32), r32))); (pk, (((k33, w33), r33), ((k13, w13), r13)))] ==>)=>//.
  proc.
  sp.
  seq 1 : (#pre /\ k11 = k13 /\ w11 = w13).
  - auto.
  - rcondt 1. inline *. auto.
    rcondt 7. inline *. auto.
    rcondf 13. inline *. wp.
    progress. smt().
  (* inline ZKBoo(Com).verify ZKBoo(Com).witness_extractor. *)
  inline *.
  auto.
  progress.
  wp. call accept3.
  wp. call accept2.
  wp. call accept1.
  skip; progress.
  rewrite /R /R_DL.
  (* need more information from res in accept(1|2|3) *)
  (* namely, view reconstruct *)


end section Protocol.
