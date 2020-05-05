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
type message    = output * output * output * Commit.commitment * Commit.commitment * Commit.commitment.
type challenge  = int.
type response   = public_key * (((random_tape * view) * randomness) * ((random_tape * view) * randomness)).

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

pred valid_view (view view2 : view) (c : circuit) (k1 k2 : random_tape) =
  (forall i, 0 <= i /\ i + 1 < size view =>
    (nth 0 view (i + 1)) = phi_decomp (nth (ADDC(0,0)) c i) i 1 view view2 k1 k2).

module ZKBoo(Com : Protocol) : SProtocol = {
  var pk : public_key
  var r1, r2, r3 : randomness
  var w1, w2, w3 : view
  var k1, k2, k3 : view
  proc gen() : statement * witness = {
    return (([], 0),0);
  }
  proc init(h : statement, w : witness) = {
    var x1,x2,x3,y,c,c1,c2,c3,sk,y1,y2,y3;
    (c, y) = h;
    (sk, pk) <$ Commit.dkey;
    (x1, x2, x3) = Phi.share(w);
    k1 = [];
    k2 = [];
    k3 = [];
    (k1, k2, k3, w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3], k1, k2, k3);
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
      ret = (((k1, w1), r1), ((k2, w2), r2));
    } else {
      if (e = 2) {
        ret = (((k2, w2), r2), ((k3, w3), r3));
      } else {
        ret = (((k3, w3), r3), ((k1, w1), r1));
      }
    }
    return (pk, ret);
  }

  proc valid_output_share(y : output, w : view) : bool = {
    var share;
    share = Phi.output(w);
    return y = share;
  }

  proc verify(h : statement, m : message, e : challenge, z : response) = {
    var c, pk, open, y1, y2, y3, c1, c2, c3, y, y', valid_com1, valid_com2;
    var valid_share1, valid_share2;
    var w1', w2', w3', r1', r2', r3', o1, o2, k1', k2', k3';
    (pk, open) = z;
    (y1, y2, y3, c1, c2, c3) = m;
    (c, y) = h;

    if (e = 1) {
      (o1, r1') = fst open;
      (o2, r2') = snd open;
      (k1', w1') = o1;
      (k2', w2') = o2;
      valid_com1 = Commit.verify pk w1' c1 r1';
      valid_com2 = Commit.verify pk w2' c2 r2';
      valid_share1 = valid_output_share(y1, w1');
      valid_share2 = valid_output_share(y2, w2');
      (* valid = valid_view w1' w2' c k1' k2'; *)
    } else {
      if (e = 2) {
        (o1, r2') = fst open;
        (o2, r3') = snd open;
        (k2', w2') = o1;
        (k3', w3') = o2;
        valid_com1 = Commit.verify pk w2' c2 r2';
        valid_com2 = Commit.verify pk w3' c3 r3';
        valid_share1 = valid_output_share(y2, w2');
        valid_share2 = valid_output_share(y3, w3');
        (* valid = valid_view w2' w3' c k2' k3'; *)
      } else {
        (o1, r3') = fst open;
        (o2, r1') = snd open;
        (k3', w3') = o1;
        (k1', w1') = o2;
        valid_com1 = Commit.verify pk w3' c3 r3';
        valid_com2 = Commit.verify pk w1' c1 r1';
        valid_share1 = valid_output_share(y3, w3');
        valid_share2 = valid_output_share(y1, w1');
        (* valid_view = valid_view w3' w1' c k3' k1'; *)
      }
    }

    y' = Phi.reconstruct(y1, y2, y3);

    return y' = y /\ valid_com1 /\ valid_com2 /\ valid_share1 /\ valid_share2;

  }

  proc witness_extractor(h : statement, a : message,
                         e : challenge list, z : response list) = {
    var c, y, w1, w2, w3, r1, r2, r3, pk, open;
    var o1, o2, o3, k1, k2, k3;
    (c, y) = h;
    (pk, open) = oget (onth z 0);
    (o1, r1) = fst open;
    (k1, w1) = o1;
    (pk, open) = oget (onth z 1);
    (o2, r2) = fst open;
    (k2, w2) = o2;
    (pk, open) = oget (onth z 2);
    (o3, r3) = fst open;
    (k3, w3) = o3;

    return (oget (onth w1 0)) + (oget (onth w2 0)) + (oget (onth w3 0));

  }

  proc simulator(h : statement, e : challenge) = {
    var c, y, views, sk, pk, a, z;
    var w1, w2, w3, y1, y2, y3;
    var c1, c2, c3, r1, r2, r3;
    var k1, k2;
    (c, y) = h;
    (sk, pk) <$ Commit.dkey;
    if (e = 1) {
      (views, y3) = Privacy.ideal(y, c, e);
      (k1, w1, k2, w2) = views;
      w3 <$ dlist dinput (size w1);
      y1 = Phi.output(w1);
      y2 = Phi.output(w2);

      (c1, r1) = Com.commit(sk, w1);
      (c2, r2) = Com.commit(sk, w2);
      (c3, r3) = Com.commit(sk, w3);
      z = (pk, (((k1, w1), r1), ((k2, w2), r2)));
    } else {
      if (e = 2) {
        (views, y1) = Privacy.ideal(y, c, e);
        (k2, w2, k3, w3) = views;
        w1 <$ dlist dinput (size w2);
        y2 = Phi.output(w2);
        y3 = Phi.output(w3);

        (c1, r1) = Com.commit(sk, w1);
        (c2, r2) = Com.commit(sk, w2);
        (c3, r3) = Com.commit(sk, w3);
        z = (pk, (((k2, w2), r2), ((k3, w3), r3)));
      } else {
        (views, y2) = Privacy.ideal(y, c, e);
        (k3, w3, k1, w1) = views;
        w2 <$ dlist dinput (size w3);
        y3 = Phi.output(w3);
        y1 = Phi.output(w1);

        (c1, r1) = Com.commit(sk, w1);
        (c2, r2) = Com.commit(sk, w2);
        (c3, r3) = Com.commit(sk, w3);
        z = (pk, (((k3, w3), r3), ((k1, w1), r1)));
      }
    }
    a = (y1, y2, y3, c1, c2, c3);

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
axiom Com_hiding_alt :
  equiv[Com.commit ~ Com.commit : ={sk, glob Com} ==> ={res, glob Com}].
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
    var x1,x2,x3,sk,pk,y1,y2,y3,y',k1,k2,k3;
    var c,y,w1,w2,w3,valid_com1,valid_com2,valid_share1,valid_share2;
    (c, y) = h;
    (x1, x2, x3) = Phi.share(w);
    k1 = [];
    k2 = [];
    k3 = [];
    (k1, k2, k3, w1, w2, w3) = Phi.compute(c, [x1], [x2], [x3], k1, k2, k3);
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
    R h' w' /\ valid_circuit h'.`1 =>
    Pr[Intermediate.main(h', w', e') @ &m : res] = 1%r.
proof.
  rewrite /R /R_DL. rewrite pairS.
  progress.
  byphoare(: (h = h' /\ w = w' /\ e = e') ==>)=>//; last first. smt().
  proc.
  case (e' = 1).
    rcondt 11. auto. do ? call(:true); auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    sp. wp.
    call commit_ll.
    call Com_correct.
    call Com_correct.
    auto.
    have Hcircuit := compute_circuit_correct h'.`1 [w'] [].
    call Hcircuit.
    auto; smt(dinput_ll Commit.dkey_ll nth_last size_ge0).
  case (e' = 2).
    rcondf 11. auto. do ? call(:true); auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    auto.
    rcondt 11. auto. do ? call(:true); auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    sp. wp.
    call Com_correct.
    call Com_correct.
    call commit_ll.
    auto.
    have Hcircuit := compute_circuit_correct h'.`1 [w'] [].
    call Hcircuit.
    auto; smt(dinput_ll Commit.dkey_ll nth_last size_ge0).
  (* case (e' = 2) *)
    rcondf 11. auto. do ? call(:true); auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    auto.
    rcondf 11. auto. do ? call(:true); auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    auto.
    inline Intermediate.valid_output_share Phi.output Phi.reconstruct Phi.share.
    sp. wp.
    call Com_correct.
    call commit_ll.
    call Com_correct.
    auto.
    have Hcircuit := compute_circuit_correct h'.`1 [w'] [].
    call Hcircuit.
    auto; smt(dinput_ll Commit.dkey_ll nth_last size_ge0).
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
    inline *. auto.
  rcondt{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  rcondt{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *. auto.
  inline Phi.reconstruct.
  inline ZKBoo(Com).valid_output_share Intermediate.valid_output_share.
  inline Intermediate.ComCorrectness.key_fixed.
  swap{2} [6..8] 14.
  swap{2} 6 - 5.
  auto. sim.
  wp.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto.
  call (:true); auto. sim.
  call (:true); auto.

  case (e{1} = 2).
  rcondf{1} 18. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondt{1} 18. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondt{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondt{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  inline Phi.reconstruct.
  inline ZKBoo(Com).valid_output_share Intermediate.valid_output_share.
  inline Intermediate.ComCorrectness.key_fixed.
  swap{2} [6..8] 14.
  swap{2} 6 - 5.
  auto. sim.
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
  rcondf{1} 18. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{1} 18. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{2} 10. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  rcondf{1} 27. progress.
    auto; do ? call (:true); auto.
    inline *; auto.
  inline Phi.reconstruct.
  inline ZKBoo(Com).valid_output_share Intermediate.valid_output_share.
  inline Intermediate.ComCorrectness.key_fixed.
  swap{2} [6..8] 14.
  swap{2} 6 - 5.
  auto. sim.
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
  inline ZKBoo(Com).simulator.
  inline ZKBoo(Com).response.
  inline ZKBoo(Com).init.
  auto.
  case (e = 1).
    rcondt{2} 5. auto.
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
    auto. smt(dlist_ll dinput_ll nth_last).
  case (e = 2).
    rcondf{2} 5. auto.
    rcondt{2} 5. auto.
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
    auto. smt(dlist_ll dinput_ll dinput_funi dinput_fu nth_last).
  case (e = 3).
    rcondf{2} 5. auto.
    rcondf{2} 5. auto.
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
    auto. smt(dlist_ll dinput_ll dinput_funi dinput_fu nth_last).

    exfalso. smt.
qed.

lemma zkboo_verify_success h' a' e' z' &m:
    Pr[ZKBoo(Com).verify(h', a', e', z') @ &m : res] =
    Pr[ZKBoo(Com).verify(h', a', e', z') @ &m : res].

(* Notes: *)
(* What is a? *)
(* what is z? *)
(* Properties I need: *)
(* 1. View w1 in a commitment *)
(* 2. \forall i w[i] = phi_decomp*)

lemma zkboo_soundness h' a' z1 z2 z3 &m:
    Pr[ZKBoo(Com).verify(h', a', 1, z1) @ &m : res] = 1%r =>
    Pr[ZKBoo(Com).verify(h', a', 2, z2) @ &m : res] = 1%r =>
    Pr[ZKBoo(Com).verify(h', a', 3, z3) @ &m : res] = 1%r =>
    Pr[Sigma.SpecialSoundness(ZKBoo(Com)).main(h', a', [1;2;3], [z1;z2;z3]) @ &m : res] = 1%r.
proof.
  move=> accept1 accept2 accept3.
  byphoare(: h = h' /\ m = a' /\ c = [1;2;3] /\ z = [z1;z2;z3] ==>)=>//.
  proc.
  sp.
  rcondt 1; auto.
  rcondt 7. inline *. auto.
  rcondt 13. inline *. auto.
  rcondf 19. inline *. auto.
  sp.
  inline ZKBoo(Com).witness_extractor.
  wp. call accept3.
  wp. call accept2.
  wp. call accept1.
  skip; progress.
  rewrite /R /R_DL.
  (* need more information from res in accept(1|2|3) *)
  (* namely, view reconstruct *)


end section Protocol.
