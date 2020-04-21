(* Formalization of ZKBoo Sigma-protocol *)
require import AllCore Distr List DInterval DList Decompose.
require (****) SigmaProtocols.
require import Commitment.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

(* TODO index into view *)
(* TODO constuct random tape *)
(* pred valid_view w1 w2 k1 k2 = forall j, w1 = phi_decomp *)
op valid_view w = w /\ true.

clone import Commitment as Commit with
  type message <- view.

print Com.

type statement  = (circuit * int).
type witness    = int.
type message    = output * output * output * Commit.commitment * Commit.commitment * Commit.commitment.
type challenge  = int.
type response   = public_key * ((view * randomness) * (view * randomness)).

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

module ZKBoo(Com : Protocol) : SProtocol = {
  var pk : public_key
  var r1, r2, r3 : randomness
  var w1, w2, w3 : view
  proc gen() : statement * witness = {
    return (([], 0),0);
  }
  proc init(h : statement, w : witness) = {
    var x1,x2,x3,y,c,c1,c2,c3,sk,y1,y2,y3;
    (c, y) = h;
    (sk, pk) <$ Commit.dkey;
    (x1, x2, x3) = Phi.share(w);
    (w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3]);
    (c1, r1) = Com.commit(sk, w1);
    (c2, r2) = Com.commit(sk, w2);
    (c3, r3) = Com.commit(sk, w3);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);

    return (y1,y2,y3,c1,c2,c3);
  }

  proc response(h : statement, w : witness, m : message, e : challenge) = {
    var ret;
    if (e = 1) {
      ret = ((w1, r1), (w2, r2));
    } else {
      if (e = 2) {
        ret = ((w2, r2), (w3, r3));
      } else {
        ret = ((w3, r3), (w1, r1));
      }
    }
    return (pk, ret);
  }

  proc valid_output_share(y : output, w : view) : bool = {
    var share;
    share = Phi.output(w);
    return y = share;
  }

  (* proc valid_view(w w' : view, k k' : random_tape) = { *)
  (*   while (w <> []) { *)
  (*     s = head w; *)
  (*     s' = head w'; *)
  (*     r = head k; *)
  (*     r' = head k'; *)

  (*     (* TODO *) *)

  (*     w = behead w; *)
  (*     w' = behead w'; *)
  (*     k = behead k; *)
  (*     k' = behead k'; *)
  (*   } *)
  (* } *)

  proc verify(h : statement, m : message, e : challenge, z : response) = {
    var c, pk, open, y1, y2, y3, c1, c2, c3, y, y', valid_com1, valid_com2;
    var valid_share1, valid_share2;
    var w1', w2', w3', r1', r2', r3';
    (pk, open) = z;
    (y1, y2, y3, c1, c2, c3) = m;
    (c, y) = h;

    if (e = 1) {
      (w1', r1') = fst open;
      (w2', r2') = snd open;
      valid_com1 = Commit.verify pk w1' c1 r1';
      valid_com2 = Commit.verify pk w2' c2 r2';
      valid_share1 = valid_output_share(y1, w1');
      valid_share2 = valid_output_share(y2, w2');
    } else {
      if (e = 2) {
        (w2', r2') = fst open;
        (w3', r3') = snd open;
        valid_com1 = Commit.verify pk w2' c2 r2';
        valid_com2 = Commit.verify pk w3' c3 r3';
        valid_share1 = valid_output_share(y2, w2');
        valid_share2 = valid_output_share(y3, w3');
      } else {
        (w3', r3') = fst open;
        (w1', r1') = snd open;
        valid_com1 = Commit.verify pk w3' c3 r3';
        valid_com2 = Commit.verify pk w1' c1 r1';
        valid_share1 = valid_output_share(y3, w3');
        valid_share2 = valid_output_share(y1, w1');

      }
    }

    y' = Phi.reconstruct(y1, y2, y3);

    return y' = y /\ valid_com1 /\ valid_com2 /\ valid_share1 /\ valid_share2;

  }

  proc witness_extractor(h : statement, m : message, e e' : challenge, z z' : response) = {
    return 0;
  }

  proc simulator(h : statement, e : challenge) = {
    var c, y, views, sk, pk, a, z;
    var w1, w2, y1, y2, y3;
    var c1, c2, c3, r1, r2, r3;
    (c, y) = h;
    (views, y3) = Privacy.ideal(y, c, e);
    (w1, w2) = views;
    w3 <$ dlist dinput (size w1);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);

    (sk, pk) <$ Commit.dkey;
    (c1, r1) = Com.commit(sk, w1);
    (c2, r2) = Com.commit(sk, w2);
    (c3, r3) = Com.commit(sk, w3);
    a = (y1, y2, y3, c1, c2, c3);
    z = (pk, ((w1, r1), (w2, r2)));

    return (a, z);
  }

}.

section Protocol.

declare module Com : Commit.Protocol{ZKBoo}.

(* Assume security of Com *)
(* axiom Com_correct &m a : Pr[Correctness(Com).main(a) @ &m : res] = 1%r. *)

axiom Com_correct :
    phoare[Correctness(Com).key_fixed : (sk, pk) \in Commit.dkey ==> res] = 1%r.
axiom Com_hiding &m (A <: HidingAdv):
  Pr[HidingGame(Com, A).main() @ &m : res] = 1%r.
axiom Com_binding &m (A <: BindingAdv):
  Pr[BindingGame(Com, A).main() @ &m : res] = 1%r.
axiom commit_ll : islossless Com.commit.


local module Intermediate = {
  module ComCorrectness = Correctness(Com)
  proc valid_output_share(y : output, w : view) : bool = {
    var share;
    share = Phi.output(w);
    return y = share;
  }

  proc main(h : statement, w : witness, e : challenge) = {
    var x1,x2,x3,sk,pk,y1,y2,y3,y';
    var c,y,w1,w2,w3,valid_com1,valid_com2,valid_share1,valid_share2;
    (c, y) = h;
    (x1, x2, x3) = Phi.share(w);
    (w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3]);
    y1 = Phi.output(w1);
    y2 = Phi.output(w2);
    y3 = Phi.output(w3);
    (sk, pk) <$ Commit.dkey;
    if (e = 1) {
      valid_com1 = ComCorrectness.key_fixed(w1, sk, pk);
      valid_com2 = ComCorrectness.key_fixed(w2, sk, pk);
      Com.commit(sk, w3);
      valid_share1 = valid_output_share(y1, w1);
      valid_share2 = valid_output_share(y2, w2);
    } else {
      if (e = 2) {
        Com.commit(sk, w1);
        valid_com1 = ComCorrectness.key_fixed(w2, sk, pk);
        valid_com2 = ComCorrectness.key_fixed(w3, sk, pk);
        valid_share1 = valid_output_share(y2, w2);
        valid_share2 = valid_output_share(y3, w3);
      } else {
        valid_com2 = ComCorrectness.key_fixed(w1, sk, pk);
        Com.commit(sk, w2);
        valid_com1 = ComCorrectness.key_fixed(w3, sk, pk);
        valid_share1 = valid_output_share(y3, w3);
        valid_share2 = valid_output_share(y1, w1);
      }
    }

    y' = Phi.reconstruct(y1,y2,y3);
    return y' = y /\ valid_com1 /\ valid_com2 /\ valid_share1 /\ valid_share2;
  }
}.

local lemma inter_completeness h' w' e' &m:
    R h' w' =>
    Pr[Intermediate.main(h', w', e') @ &m : res] = 1%r.
proof.
  rewrite /R /R_DL. rewrite pairS.
  progress.
  byphoare(: (h = h' /\ w = w' /\ e = e') ==>)=>//; last first. smt().
  proc.
  case (e' = 1).
    rcondt 8. auto. do ? call(:true); auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    sp. wp.
    call commit_ll.
    call Com_correct.
    call Com_correct.
    auto.
    call (compute_circuit_correct h'.`1 [w']).
    auto; progress.
    apply dinput_ll.
    smt().
    apply Commit.dkey_ll.
    smt().
    have : (result.`1, result.`2, result.`3) = result by smt().
    rewrite /eval_circuit in H.
    have Hlast := last_nth 0.
    smt().
  case (e' = 2).
    rcondf 8. auto. do ? call(:true); auto.
    rcondt 8. auto. do ? call(:true); auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    sp. wp.
    call Com_correct.
    call Com_correct.
    call commit_ll.
    auto.
    call (compute_circuit_correct h'.`1 [w']).
    auto; progress.
    apply dinput_ll.
    smt().
    apply Commit.dkey_ll.
    smt().
    have : (result.`1, result.`2, result.`3) = result by smt().
    rewrite /eval_circuit in H.
    have Hlast := last_nth 0.
  (* case (e' = 2) *)
    smt().
    rcondf 8. auto. do ? call(:true); auto.
    rcondf 8. auto. do ? call(:true); auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    sp. wp.
    call Com_correct.
    call commit_ll.
    call Com_correct.
    auto.
    call (compute_circuit_correct h'.`1 [w']).
    auto; progress.
    apply dinput_ll.
    smt().
    apply Commit.dkey_ll.
    smt().
    have : (result.`1, result.`2, result.`3) = result by smt().
    rewrite /eval_circuit in H.
    have Hlast := last_nth 0.
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
  rcondt{1} 15. progress.
    auto; do ? call (:true); auto.
  rcondt{2} 7. progress.
    auto; do ? call (:true); auto.
  rcondt{1} 24. progress.
    auto; do ? call (:true); auto.
  inline Phi.reconstruct.
  inline ZKBoo(Com).valid_output_share Intermediate.valid_output_share.
  inline Intermediate.ComCorrectness.key_fixed.
  swap{2} [11..12] 5.
  swap{2} [15..18] 1.
  swap{2} [3..5] 10.
  swap{2} 2 1.
  swap{1} 1 1.
  auto.
  sim.
  auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true). sim.
  auto.
  call (:true). sim.
  skip; progress.
  case (e{1} = 2).
  rcondf{1} 15. progress.
    auto; do ? call (:true); auto.
  rcondt{1} 15. progress.
    auto; do ? call (:true); auto.
  rcondf{2} 7. progress.
    auto; do ? call (:true); auto.
  rcondt{2} 7. progress.
    auto; do ? call (:true); auto.
  rcondf{1} 24. progress.
    auto; do ? call (:true); auto.
  rcondt{1} 24. progress.
    auto; do ? call (:true); auto.
  inline Phi.reconstruct.
  inline ZKBoo(Com).valid_output_share Intermediate.valid_output_share.
  inline Intermediate.ComCorrectness.key_fixed.
  auto. sim. auto.
  swap{2} [12..13] 4.
  wp.
  swap{2} [3..5] 10.
  swap{2} 2 1.
  swap{1} 1 1.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true). sim.
  auto.
  call (:true). sim.
  skip; progress.

  (* case e = 3 *)
  rcondf{1} 15. progress.
    auto; do ? call (:true); auto.
  rcondf{1} 15. progress.
    auto; do ? call (:true); auto.
  rcondf{2} 7. progress.
    auto; do ? call (:true); auto.
  rcondf{2} 7. progress.
    auto; do ? call (:true); auto.
  rcondf{1} 24. progress.
    auto; do ? call (:true); auto.
  rcondf{1} 24. progress.
    auto; do ? call (:true); auto.
  inline Phi.reconstruct.
  inline ZKBoo(Com).valid_output_share Intermediate.valid_output_share.
  inline Intermediate.ComCorrectness.key_fixed.
  auto. sim. auto.
  swap{2} [11..12] 5. wp.
  swap{2} [3..5] 10.
  swap{2} 2 1.
  swap{1} 1 1.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true). sim.
  auto.
  call (:true). sim.
  skip; progress.
qed.

lemma zkboo_completeness h' w' e' &m:
    R h' w' =>
    Pr[Sigma.Completeness(ZKBoo(Com)).special(h', w', e') @ &m : res] = 1%r.
proof.
  move=> rel.
  have -> : Pr[Completeness(ZKBoo(Com)).special(h', w', e') @ &m : res] =
            Pr[Intermediate.main(h', w', e') @ &m : res].
  - byequiv inter_equiv=>//.
  by have := inter_completeness h' w' e' &m rel.
qed.


(* idea: reduce to Phi.main; Com.correctness *)
lemma zkboo_complete &m h' w' e':
    R h' w' =>
    Pr[Sigma.Completeness(ZKBoo(Com)).special(h', w', e') @ &m : res] = 1%r.
proof.
  rewrite /R /R_DL.
  move=> rel.
  byphoare(: h = h' /\ w = w' /\ e = e' ==> _)=>//.
  proc.
  inline Completeness(ZKBoo(Com)).special.
  inline ZKBoo(Com).init.
  swap 4 2.
  swap [6..9] 3.
  inline Phi.share. sp.
  seq 3 : (#pre /\ exists (x1' x2' x3' : input), x1' = x10 /\ x2' = x20 /\ x3' = x30 /\ x1' + x2' + x3' = w'); last first; last first.
    - hoare. auto. progress. smt().
    - progress.
    - auto. auto. progress.
      apply dinput_ll. smt().
  sp. elim *. progress.
  have Hcompute := compute_circuit_correct (fst h') [x1'] [x2'] [x3'] [w'] (eval_circuit_aux (fst h') [w']) _.
   - smt().
  inline ZKBoo(Com).response.
  inline ZKBoo(Com).verify.
  case (e' = 1).
    auto. rcondt 23.
    auto.
    call (:true).
    call (:true).
    call (:true).
    call (:true).
    call (:true). auto.
    call (:true). auto.
    call (:true). auto.
    call (:true). auto.
    auto.
  rcondt 14.
    auto.
    call (:true).
    call (:true).
    call (:true).
    call (:true).
    call (:true); auto.
    call (:true); auto.
    call (:true); auto.
    call (:true); auto.
  inline Phi.reconstruct. auto.
  inline ZKBoo(Com).valid_output_share Phi.output.
  auto.
  sp.
  swap 1 2.



end section Protocol.
