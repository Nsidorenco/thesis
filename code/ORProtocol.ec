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

  op dchallenge : {challenge distr | is_lossless dchallenge /\ is_funiform dchallenge} as dchallenge_llfuni.

  op (^^) (c1 : challenge, c2 : challenge) : challenge.
  axiom xorK x c1 : (x ^^ c1) ^^ c1 = x.
  axiom xorA x y : x ^^ y = y ^^ x.

  clone SigmaProtocols as Sigma with
    type SigmaProtocols.statement <- (statement1 * statement2),
    type SigmaProtocols.witness <- witness,
    type SigmaProtocols.message <- message,
    type SigmaProtocols.randomness <- randomness,
    type SigmaProtocols.challenge <- challenge,
    type SigmaProtocols.response <- response,

    op SigmaProtocols.R = fun x w => (R1 (fst x) w) \/ (R2 (snd x) w),
    op SigmaProtocols.dchallenge = dchallenge
    proof *.
    realize SigmaProtocols.dchallenge_llfuni by apply dchallenge_llfuni.

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
      var h', w;
      (h', w) = gen();
      return w;
    }

    proc simulator(h : statement, e : challenge) : message * response = {
      var h1, h2, a1, a2, z1, z2;
      (h1, h2) = h;

      (a1, z1) = P1.simulator(h1, e);
      (a2, z2) = P2.simulator(h2, e);

      return ((a1, a2), (e1, z1, e2, z2));
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

local lemma SP1_completeness_pr h' w' : phoare[C1.main : (h = h' /\ w = w' /\ (R1 h' w')) ==> res] = 1%r.
    proof. bypr. progress. apply (completeness_protocol1 &m) in H. assumption. qed.
local lemma SP2_completeness_pr h' w' : phoare[C2.main : (h = h' /\ w = w' /\ (R2 h' w')) ==> res] = 1%r.
    proof. bypr. progress. apply (completeness_protocol2 &m) in H. assumption. qed.

axiom shvzk1_ideal_never_fails h':
      phoare[S1.SigmaProtocols.SHVZK(SP1).ideal : (h = h') ==> (res <> None)] = 1%r.
axiom shvzk2_ideal_never_fails h':
      phoare[S2.SigmaProtocols.SHVZK(SP2).ideal : (h = h') ==> (res <> None)] = 1%r.

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
    byphoare (: h1 = h' ==> _)=>//. proc. by call (shvzk1_ideal_never_fails h').
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
    apply H1 in H. apply H. qed.

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
        (R1 (fst h') w') \/ (R2 (snd h') w') =>
        Pr[Completeness'.main(h', w') @ &m : res] = 1%r.
      proof. move=> rel. case (R1 (fst h') w') => R.
      byphoare (: h = h' /\ w = w' ==> _)=>//. proc. sp.
      rcondt 1. auto.
      have Hreal1 := (real1_true' (fst h') w'). call Hreal1.
      have Hfake2 := (fake2_true (snd h')). call Hfake2. auto.
      byphoare (: h = h' /\ w = w' ==> _)=>//. proc. sp.
      rcondf 1. auto.
      have Hreal2 := (real2_true' (snd h') w'). call Hreal2.
      have Hfake1 := (fake1_true (fst h')). call Hfake1. auto. smt().
    qed.

    local lemma or_completeness h' w' &m:
        (R1 (fst h') w') \/ (R2 (snd h') w') =>
        Pr[Sigma.SigmaProtocols.Completeness(ORProtocol(SP1,SP2)).main(h', w') @ &m : res] = 1%r.
    proof.
      move=> rel. have -> := (completeness_sim_equiv h' w' &m).
      have Htrue := (completeness'_true h' w' &m).
      apply Htrue in rel. apply rel.
    qed.

end section Security.
end ORProtocol.
