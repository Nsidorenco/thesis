(* Formalization of Sigma Protocols *)
require import AllCore Distr DBool.

require SigmaProtocols.

(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.


theory ORProtocol.
  type statement1.
  type statement2.
  type witness.
  type message1.
  type message2.
  type randomness.
  type challenge.
  type response1.
  type response2.

  type statement = (statement1 * statement2).
  type message = (message1 * message2).
  type response = (challenge * response1  * challenge * response2).

  type transcript = message * challenge * response.

  (* define the relations *)
  op R1 (x : statement1, w : witness) : bool.
  op R2 (x : statement2, w : witness) : bool.
  op R = fun x w => (R1 (fst x) w) \/ (R2 (snd x) w).

  op dchallenge : {challenge distr | is_lossless dchallenge /\ is_funiform dchallenge} as dchallenge_llfuni.

  op (^^) (c1 : challenge, c2 : challenge) : challenge.
  axiom xorK x c1 : (x ^^ c1) ^^ c1 = x.
  axiom xorA x y : x ^^ y = y ^^ x.

  clone SigmaProtocols as S1 with
    type SigmaProtocols.statement <- statement1,
    type SigmaProtocols.witness <- witness,
    type SigmaProtocols.message <- message1,
    type SigmaProtocols.randomness <- randomness,
    type SigmaProtocols.challenge <- challenge,
    type SigmaProtocols.response <- response1,

    op SigmaProtocols.R = R1,
    op SigmaProtocols.dchallenge = dchallenge
    proof *.
    realize SigmaProtocols.dchallenge_llfuni by apply dchallenge_llfuni.

  clone SigmaProtocols as S2 with
    type SigmaProtocols.statement <- statement2,
    type SigmaProtocols.witness <- witness,
    type SigmaProtocols.message <- message2,
    type SigmaProtocols.randomness <- randomness,
    type SigmaProtocols.challenge <- challenge,
    type SigmaProtocols.response <- response2,

    op SigmaProtocols.R = R2,
    op SigmaProtocols.dchallenge = dchallenge
    proof *.
    realize SigmaProtocols.dchallenge_llfuni by apply dchallenge_llfuni.

  clone SigmaProtocols as Sigma with
    type SigmaProtocols.statement <- (statement1 * statement2),
    type SigmaProtocols.witness <- witness,
    type SigmaProtocols.message <- message,
    type SigmaProtocols.randomness <- randomness,
    type SigmaProtocols.challenge <- challenge,
    type SigmaProtocols.response <- response,

    op SigmaProtocols.R = R,
    op SigmaProtocols.dchallenge = dchallenge
    proof *.
    realize SigmaProtocols.dchallenge_llfuni by apply dchallenge_llfuni.
  export Sigma.



  module ORProtocol (P1 : S1.SigmaProtocols.SProtocol, P2 : S2.SigmaProtocols.SProtocol) : Sigma.SigmaProtocols.SProtocol = {
    var e1 : challenge
    var e2 : challenge
    var z1 : response1
    var z2 : response2

    proc gen() : (statement * witness) = {
      var h1, h2, w1, w2, b, ret;
      (h1, w1) = P1.gen();
      (h2, w2) = P2.gen();
      b <$ DBool.dbool;
      if (b) {
        ret = ((h1, h2), w1);
      } else {
        ret = ((h1, h2), w2);
      }
      return ret;
    }

    proc init(h : statement, w : witness) : message * randomness = {
      var h1, h2, r, ret, a1, a2;
      (h1, h2) = h;

      if (R1 h1 w) {
        (a1, r) = P1.init(h1, w);
        e2 <$ dchallenge;
        (a2, z2) = P2.simulator(h2, e2);
        ret = ((a1, a2), r);
      } else {
        (a2, r) = P2.init(h2, w);
        e1 <$ dchallenge;
        (a1, z1) = P1.simulator(h1, e1);
        ret = ((a1, a2), r);
      }
      return ret;
    }

    proc response(h : statement, w : witness, m : message, r : randomness, s : challenge) : response = {
      var m1, m2, h1, h2;
      (m1, m2) = m;
      (h1, h2) = h;

      if (R1 h1 w) {
        e1 = s ^^ e2;
        z1 = P1.response(h1, w, m1, r, e1);
      } else {
        e2 = s ^^ e1;
        z2 = P2.response(h2, w, m2, r, e2);
      }
      return (e1, z1, e2, z2);
    }

    proc verify(h : statement, m : message, e : challenge, z : response) : bool = {
      var h1, h2, m1, m2, z1, z2, v, v';
      (h1, h2) = h;
      (m1, m2) = m;
      (e1, z1, e2, z2) = z;

      v = P1.verify(h1, m1, e1, z1);
      v' = P2.verify(h2, m2, e2, z2);

      return ((e = e1 ^^ e2) /\ v /\ v');

    }

    proc witness_extractor(h : statement, m : message,
                           e : challenge, e' : challenge,
                           z : response, z' : response) : witness = {
      var h1, h2, m1, m2, w, e1, e2, e1', e2', z1, z2, z1', z2';
      (h1, h2) = h;
      (m1, m2) = m;
      (e1, z1, e2, z2) = z;
      (e1', z1', e2', z2') = z';
      if (e1 <> e1') {
        w = P1.witness_extractor(h1, m1, e1, e1', z1, z1');
      } else {
        w = P2.witness_extractor(h2, m2, e2, e2', z2, z2');
      }
      return w;
    }

    proc simulator(h : statement, c : challenge) : message * response = {
      var h1, h2, a1, a2, z1, z2, c1, c2;
      (h1, h2) = h;

      c2 <$ dchallenge;
      c1 = c ^^ c2;

      (a1, z1) = P1.simulator(h1, c1);
      (a2, z2) = P2.simulator(h2, c2);

      return ((a1, a2), (c1, z1, c2, z2));
    }

  }.
section Security.
declare module SP1 : S1.SigmaProtocols.SProtocol{ORProtocol}.
declare module SP2 : S2.SigmaProtocols.SProtocol{ORProtocol,SP1}.

local module C1 = S1.SigmaProtocols.Completeness(SP1).
local module C2 = S2.SigmaProtocols.Completeness(SP2).

local module SHVZK1 = S1.SigmaProtocols.SHVZK(SP1).
local module SHVZK2 = S2.SigmaProtocols.SHVZK(SP2).

  axiom completeness_protocol1 h w &m : (R1 h w) => Pr[S1.SigmaProtocols.Completeness(SP1).main(h, w) @ &m : res] = 1%r.
  axiom completeness_protocol2 h w &m : (R2 h w) => Pr[S2.SigmaProtocols.Completeness(SP2).main(h, w) @ &m : res] = 1%r.

  axiom shvzk1_equiv h' w':
    equiv[S1.SigmaProtocols.SHVZK(SP1).real ~ S1.SigmaProtocols.SHVZK(SP1).ideal : (={h} /\ h{2} = h' /\ w{1} = w' /\ (R1 h' w')) ==> ={res}].
  axiom shvzk2_equiv h' w':
    equiv[S2.SigmaProtocols.SHVZK(SP2).real ~ S2.SigmaProtocols.SHVZK(SP2).ideal : (={h} /\ h{2} = h' /\ w{1} = w' /\ (R2 h' w')) ==> ={res}].

  local lemma shvzk1_equiv_pr h' w' &m:
      (R1 h' w') =>
      Pr[S1.SigmaProtocols.SHVZK(SP1).real(h', w') @ &m : (res <> None)] =
      Pr[S1.SigmaProtocols.SHVZK(SP1).ideal(h') @ &m : (res <> None)].
  proof. move=>rel.
  by byequiv (shvzk1_equiv h' w'). qed.

  (* local lemma shvzk1_ideal_never_fails_pr h' &m: *)
  (*     Pr[S1.SigmaProtocols.SHVZK(SP1).ideal(h') @ &m : (res <> None)] = 1%r. *)
  (* proof. *)
  (*    have eq := (shvzk1_equiv h'). *)
  (*    have H := (completeness_protocol1 h'). *)


  (* local lemma shvzk1_ideal_completeness h' w' &m: *)
  (*     Pr[S1.SigmaProtocols.SHVZK(SP1).ideal(h') @ &m : (res <> None)] = *)
  (*     Pr[C1.main(h', w') @ &m : res]. *)
  (* proof. have H := (shvzk1 h' w' &m). *)
  (*   rewrite -H. *)
  (*   have -> := (S1.SigmaProtocols.shvzk_real_never_fail SP1 h' w' &m). *)
  (*   byequiv=>//. proc. sim. qed. *)

  (* NOTE: proof idea... *)
  (* Pr[ideal] = (forall w, (R h w), Pr[real])*)

  axiom shvzk1_ideal_never_fails_pr h' &m:
      Pr[S1.SigmaProtocols.SHVZK(SP1).ideal(h') @ &m : (res <> None)] = 1%r.
  axiom shvzk2_ideal_never_fails_pr h' &m:
      Pr[S2.SigmaProtocols.SHVZK(SP2).ideal(h') @ &m : (res <> None)] = 1%r.

  local lemma shvzk1_ideal_never_fails h':
        phoare[S1.SigmaProtocols.SHVZK(SP1).ideal : (h = h') ==> (res <> None)] = 1%r.
  proof. have H := (shvzk1_ideal_never_fails_pr h'). bypr. progress. apply (H &m). qed.

  local lemma shvzk2_ideal_never_fails h':
        phoare[S2.SigmaProtocols.SHVZK(SP2).ideal : (h = h') ==> (res <> None)] = 1%r.
  proof. have H := (shvzk2_ideal_never_fails_pr h'). bypr. progress. apply (H &m). qed.

  local lemma shvzk1_real_never_fails h' w':
        phoare[S1.SigmaProtocols.SHVZK(SP1).real : (h = h' /\ w = w' /\ (R1 h' w')) ==> (res <> None)] = 1%r.
  proof.
  bypr. progress.
  have -> := (S1.SigmaProtocols.shvzk_real_never_fail SP1 h{m} w{m} &m).
  by have := (completeness_protocol1 h{m} w{m} &m H).
  qed.

  local lemma shvzk2_real_never_fails h' w':
        phoare[S2.SigmaProtocols.SHVZK(SP2).real : (h = h' /\ w = w' /\ (R2 h' w')) ==> (res <> None)] = 1%r.
  proof.
  bypr. progress.
  have -> := (S2.SigmaProtocols.shvzk_real_never_fail SP2 h{m} w{m} &m).
  by have := (completeness_protocol2 h{m} w{m} &m H).
  qed.

  (* Converting the ambient logic to the pHoare logic *)
local lemma SP1_completeness_pr h' w' : phoare[C1.main : (h = h' /\ w = w' /\ (R1 h' w')) ==> res] = 1%r.
    proof. bypr. progress. by apply (completeness_protocol1 &m) in H. qed.
local lemma SP2_completeness_pr h' w' : phoare[C2.main : (h = h' /\ w = w' /\ (R2 h' w')) ==> res] = 1%r.
    proof. bypr. progress. by apply (completeness_protocol2 &m) in H. qed.

local module Completeness' = {
  var e1 : challenge
  var e2 : challenge
  var e  : challenge
  proc fake1 (h1 : statement1) = {
      var a1, z1, v1;
      e1 <$ dchallenge;

      (a1, z1) = SP1.simulator(h1, e1);
      v1 = SP1.verify(h1, a1, e1, z1);
      return v1;
  }

  proc fake2 (h2 : statement2) = {
      var a2, z2, v2;
      e2 <$ dchallenge;

      (a2, z2) = SP2.simulator(h2, e2);
      v2 = SP2.verify(h2, a2, e2, z2);
      return v2;
  }

  proc real1 (h1 : statement1, w : witness) : bool = {
      var a1, r, z1, v1;
      (a1, r) = SP1.init(h1, w);

      e <$ Sigma.SigmaProtocols.dchallenge;
      e1 = e ^^ e2;

      z1 = SP1.response(h1, w, a1, r, e1);
      v1 = SP1.verify(h1, a1, e1, z1);
      return (e = e1 ^^ e2) /\ v1;
  }

  proc real2 (h2 : statement2, w : witness) : bool = {
      var a2, r, z2, v2;
      (a2, r) = SP2.init(h2, w);

      e <$ Sigma.SigmaProtocols.dchallenge;
      e2 = e ^^ e1;

      z2 = SP2.response(h2, w, a2, r, e2);
      v2 = SP2.verify(h2, a2, e2, z2);
      return (e = e1 ^^ e2) /\ v2;
  }

  proc main(h : statement, w : witness) : bool = {
    var h1, h2, v1, v2;
    (h1, h2) = h;
    if (R1 h1 w) {
      v2 = fake2(h2);
      v1 = real1(h1, w);
    } else {
      v1 = fake1(h1);
      v2 = real2(h2, w);
    }
    return (e = e1 ^^ e2) /\ v1 /\ v2;
  }
}.

local module FakeIdeal = {
  proc fake1(h1 : statement1) = {
    var opt;
      opt = SHVZK1.ideal(h1);
      return (opt <> None);
  }
  proc fake2(h2 : statement2) = {
    var opt;
      opt = SHVZK2.ideal(h2);
      return (opt <> None);
  }
}.

  local lemma fake1_ideal_equiv h' &m:
      Pr[Completeness'.fake1(h') @ &m : res] =
      Pr[FakeIdeal.fake1(h') @ &m : res].
  proof.
    byequiv=>//. proc. inline *. sp. wp.
    do ? call (: true). rnd. progress.
  qed.

  local lemma fake2_ideal_equiv h' &m:
      Pr[Completeness'.fake2(h') @ &m : res] =
      Pr[FakeIdeal.fake2(h') @ &m : res].
  proof.
    byequiv=>//. proc. inline *. sp. wp.
    do ? call (: true). rnd. progress.
  qed.

  local lemma fake1_ideal_equiv' h' &m:
      Pr[FakeIdeal.fake1(h') @ &m : res] = 1%r.
  proof.
    byphoare (: h1 = h' ==> _)=>//. proc.
    by call (shvzk1_ideal_never_fails h').
  qed.

  local lemma fake2_ideal_equiv' h' &m:
      Pr[FakeIdeal.fake2(h') @ &m : res] = 1%r.
  proof.
    byphoare (: h2 = h' ==> _)=>//. proc. by call (shvzk2_ideal_never_fails h').
  qed.

  local lemma completeness_sim_equiv h' w' &m:
      Pr[Sigma.SigmaProtocols.Completeness(ORProtocol(SP1,SP2)).main(h', w') @ &m : res] =
      Pr[Completeness'.main(h', w') @ &m : res].
  proof.
    byequiv=>//. proc. inline *. sp. wp.
    case (R1 (fst h') w').
      - rcondt{1} 1. progress.
      - rcondt{2} 1. progress.
      - rcondt{1} 14. progress. auto. call (: true). rnd. call (: true). auto.
    swap{2} [6..8] -4. sp.
    swap{2} [4..5] 5. swap{1} 6 -2. sim. wp.
    call (: true). wp. call (: true). wp. rnd.
    call (: true). rnd. call (: true). auto.
    progress. rewrite xorK. done.
    (* case (R1 (fst h') w') = false *)
      - rcondf{1} 1. progress.
      - rcondf{2} 1. progress.
      - rcondf{1} 14. progress. auto. call (: true). rnd. call (: true). auto.
    swap{2} [6..8] -4. sp.
    swap{2} [4..5] 3. swap{1} 6 -2. sim. wp.
    call (: true). wp. call (: true). wp. call (: true).
    wp. rnd. call (: true). rnd. call(: true). auto.
    progress. rewrite xorA xorK. done.
  qed.


    local lemma real1_completeness1_equiv h' w' &m:
        Pr[Completeness'.real1(h', w') @ &m : res /\ (Completeness'.e = Completeness'.e1 ^^ Completeness'.e2 )] =
        Pr[C1.main(h', w') @ &m : res].
    proof.
      byequiv=> //. proc.
      do ? call (: true).
      wp. rnd (fun z => z ^^ Completeness'.e2{1}).
      call (: true). auto. progress.
      by rewrite xorK.
      apply Sigma.SigmaProtocols.dchallenge_funi.
      apply Sigma.SigmaProtocols.dchallenge_fu.
      by rewrite xorK.
    qed.

    local lemma real1_true h' w' &m:
        (R1 h' w') =>
        Pr[Completeness'.real1(h', w') @ &m : res /\ (Completeness'.e = Completeness'.e1 ^^ Completeness'.e2 )] = 1%r.
    proof. move=> rel. have H := (completeness_protocol1 h' w' &m).
    apply H in rel. rewrite - rel. smt. qed.

    local lemma real1_true' h' w':
        phoare[Completeness'.real1 : (h1 = h' /\ w = w' /\ (R1 h' w')) ==> res /\ (Completeness'.e = Completeness'.e1 ^^ Completeness'.e2 )] = 1%r.
    proof. bypr. progress. have H1 := (real1_true h1{m} w{m} &m).
    exact (H1 H). qed.

    local lemma real2_completeness2_equiv h' w' &m:
        Pr[Completeness'.real2(h', w') @ &m : res /\ (Completeness'.e = Completeness'.e1 ^^ Completeness'.e2 )] =
        Pr[C2.main(h', w') @ &m : res].
    proof.
      byequiv=> //. proc.
      do ? call (: true).
      wp. rnd (fun z => z ^^ Completeness'.e1{1}).
      call (: true). auto. progress.
      by rewrite xorK.
      apply Sigma.SigmaProtocols.dchallenge_funi.
      apply Sigma.SigmaProtocols.dchallenge_fu.
      by rewrite xorK.
      by rewrite xorA xorK.
      by rewrite xorA xorK.
    qed.

    local lemma real2_true h' w' &m:
        (R2 h' w') =>
        Pr[Completeness'.real2(h', w') @ &m : res /\ (Completeness'.e = Completeness'.e1 ^^ Completeness'.e2 )] = 1%r.
    proof. move=> rel. have H := (completeness_protocol2 h' w' &m).
    apply H in rel. rewrite - rel. smt. qed.

    local lemma real2_true' h' w':
        phoare[Completeness'.real2 : (h2 = h' /\ w = w' /\ (R2 h' w')) ==> res /\ (Completeness'.e = Completeness'.e1 ^^ Completeness'.e2 )] = 1%r.
    proof. bypr. progress. have H2 := (real2_true h2{m} w{m} &m).
    apply H2 in H. apply H. qed.

    local lemma fake1_true h':
        phoare[Completeness'.fake1 : h1 = h' ==> res] = 1%r.
    proof. bypr. progress. have -> := (fake1_ideal_equiv h1{m} &m).
    by have -> := (fake1_ideal_equiv' h1{m} &m). qed.

    local lemma fake2_true h':
        phoare[Completeness'.fake2 : h2 = h' ==> res] = 1%r.
    proof. bypr. progress. have -> := (fake2_ideal_equiv h2{m} &m).
    by have -> := (fake2_ideal_equiv' h2{m} &m). qed.

    local lemma completeness'_true h' w' &m:
        (Sigma.SigmaProtocols.R h' w') =>
        Pr[Completeness'.main(h', w') @ &m : res] = 1%r.
      proof. move=> rel.
      case (R1 (fst h') w') => R.
      byphoare (: h = h' /\ w = w' ==> _)=>//. proc. sp.
      rcondt 1. auto.
      have Hreal1 := (real1_true' (fst h') w'). call Hreal1.
      have Hfake2 := (fake2_true (snd h')). call Hfake2. auto.
      byphoare (: h = h' /\ w = w' ==> _)=>//. proc. sp.
      rcondf 1. auto.
      have Hreal2 := (real2_true' (snd h') w'). call Hreal2.
      have Hfake1 := (fake1_true (fst h')). call Hfake1. auto. smt().
    qed.

    lemma or_completeness h' w' &m:
        (Sigma.SigmaProtocols.R h' w') =>
        Pr[Sigma.SigmaProtocols.Completeness(ORProtocol(SP1,SP2)).main(h', w') @ &m : res] = 1%r.
    proof.
      move=> rel. have -> := (completeness_sim_equiv h' w' &m).
      have Htrue := (completeness'_true h' w' &m).
      apply Htrue in rel. apply rel.
    qed.

    local module SHVZK' = {
        proc real(h, w) : transcript option = {
          var h1, h2, a1, a2, z1, z2, e1, e2, ret, t1, t2;
          (h1, h2) = h;
          if (R1 h1 w) {
            t1 = SHVZK1.real(h1, w);
            t2 = SHVZK2.ideal(h2);
            if (t1 = None \/ t2 = None) {
              ret = None;
            } else {
              (a1, e1, z1) = oget(t1);
              (a2, e2, z2) = oget(t2);
              ret = Some ((a1, a2), (e1^^e2), (e1, z1, e2, z2));
            }
          } else {
            t2 = SHVZK2.real(h2, w);
            t1 = SHVZK1.ideal(h1);
            if (t1 = None \/ t2 = None) {
              ret = None;
            } else {
              (a1, e1, z1) = oget(t1);
              (a2, e2, z2) = oget(t2);
              ret = Some ((a1, a2), (e2^^e1), (e1, z1, e2, z2));
            }
          }
          return ret;
        }
        proc ideal(h) : transcript option = {
          var h1, h2, a1, a2, z1, z2, e1, e2, ret, t1, t2;
          (h1, h2) = h;
          t1 = SHVZK1.ideal(h1);
          t2 = SHVZK2.ideal(h2);
          if (t1 = None \/ t2 = None) {
            ret = None;
          } else {
            (a1, e1, z1) = oget(t1);
            (a2, e2, z2) = oget(t2);
            ret = Some ((a1, a2), e1^^e2, (e1, z1, e2, z2));
          }
          return ret;
        }
      }.

      local equiv real_real'_equiv h' w':
        SHVZK'.real ~ Sigma.SigmaProtocols.SHVZK(ORProtocol(SP1, SP2)).real :
        (h{2} = h' /\ w{2} = w' /\ (R h' w') /\ ={h, w, glob SP1, glob SP2}) ==> ={res}.
      proof.
      proc. inline *. sp. case (R1 (fst h') w').
      (* case: relation is true *)
      rcondt{1} 1. progress.
      rcondt{2} 1. progress.
      rcondt{2} 14. progress. auto. call (:true). rnd. call(:true). progress.
      sp. auto. call (:true). swap{1} [8..10] -5.
      swap{2} 11 2. swap{2} [13..14] -6.
      auto.
      call (:true). swap{2} [6..8] -3.
      auto. call (:true).
      auto. call (:true). swap{1} 4 -2. wp.
      rnd (fun z => z ^^ e0{1}) (fun q => q ^^ ORProtocol.e2{2}).
      rnd. call (:true).
      auto. progress=>//.
      - by rewrite xorK.
      - apply S1.SigmaProtocols.dchallenge_funi.
      - apply S1.SigmaProtocols.dchallenge_fu.
      - by rewrite xorK.
      - apply : contra H12. progress. by rewrite xorK xorA.
     (* case: relation is false *)
      rcondf{1} 1. progress.
      rcondf{2} 1. progress.
      rcondf{2} 14. progress. auto. call (:true). rnd. call(:true). progress.
      sp. auto. swap{2} 24 1. call (:true). swap{1} [8..10] -5.
      swap{2} 11 2. swap{2} [13..14] -6.
      auto.
      call (:true). swap{2} [6..8] -3.
      auto. call (:true).
      auto. call (:true). swap{1} 4 -2. wp.
      rnd (fun z => z ^^ e4{1}) (fun q => q ^^ ORProtocol.e1{2}).
      rnd. call (:true).
      auto. progress=>//.
      - by rewrite xorK.
      - apply S1.SigmaProtocols.dchallenge_funi.
      - apply S1.SigmaProtocols.dchallenge_fu.
      - by rewrite xorK.
      - apply : contra H12. progress. by rewrite xorK xorA.
      qed.

      local equiv ideal_ideal'_equiv h':
        SHVZK'.ideal ~ Sigma.SigmaProtocols.SHVZK(ORProtocol(SP1, SP2)).ideal :
        (={h, glob SP1, glob SP2} /\ h{2} = h') ==> ={res}.
      proof.
      proc. inline *.
      sp. auto. call (:true).
      swap{1} [3..6] 3. auto.
      call (:true). auto.
      call (:true).
      swap{1} 2 2. call (:true).
      swap{1} 3 -2. swap{2} 5 -4. wp.
      rnd (fun z => z ^^ e0{1}) (fun q => q ^^ c2{2}).
      auto. progress=>//.
      - by rewrite xorK.
      - apply SigmaProtocols.dchallenge_funi.
      - apply SigmaProtocols.dchallenge_fu.
      - by rewrite xorK.
      - apply : contra H10. progress. by rewrite xorK xorA.
      qed.

  equiv or_shvzk h' w' &m:
      Sigma.SigmaProtocols.SHVZK(ORProtocol(SP1, SP2)).real ~
      Sigma.SigmaProtocols.SHVZK(ORProtocol(SP1, SP2)).ideal :
      (h{1} = h' /\ h{2} = h' /\ ={h, glob SP1, glob SP2} /\ w{1} = w' /\ (R h' w')) ==> ={res}.
  proof.
  bypr (res{1}) (res{2}).
  progress. progress.
    have <- : Pr[SHVZK'.real(h{1}, w{1}) @ &1 : res = a] =
              Pr[SigmaProtocols.SHVZK(ORProtocol(SP1, SP2)).real(h{1}, w{1}) @ &1 : res = a].
      - byequiv (real_real'_equiv h{1} w{1})=>//.
    have <- : Pr[SHVZK'.ideal(h{2}) @ &2 : res = a] =
              Pr[SigmaProtocols.SHVZK(ORProtocol(SP1, SP2)).ideal(h{2}) @ &2 : res = a].
      - byequiv (ideal_ideal'_equiv h{2})=>//.
  case (R1 (fst h{1}) w{1})=> rel_true.
  byequiv=>//.
  proc.
  auto. rcondt{1} 2. auto. sp.
  auto. inline SHVZK2.ideal.
  auto. do ? call (:true). auto.
  call (shvzk1_equiv (fst h{1}) w{1}). auto. progress; smt().
  (* case: relation is false *)
  byequiv=>//. proc.
  auto. rcondf{1} 2. auto. sp.
  auto. swap{1} 1 1.
  call (shvzk2_equiv (snd h{1}) w{1}).
  inline SHVZK1.ideal.
  auto. do ? call (:true). auto. progress; smt.
  qed.

  lemma or_special_soundness &m:


end section Security.
end ORProtocol.
