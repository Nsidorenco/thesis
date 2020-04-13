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
    type statement <- statement1,
    type witness <- witness,
    type message <- message1,
    type challenge <- challenge,
    type response <- response1,

    op R = R1,
    op dchallenge = dchallenge
    proof *.
    realize dchallenge_llfuni by apply dchallenge_llfuni.

  clone SigmaProtocols as S2 with
    type statement <- statement2,
    type witness <- witness,
    type message <- message2,
    type challenge <- challenge,
    type response <- response2,

    op R = R2,
    op dchallenge = dchallenge
    proof *.
    realize dchallenge_llfuni by apply dchallenge_llfuni.

  clone SigmaProtocols as Sigma with
    type statement <- (statement1 * statement2),
    type witness <- witness,
    type message <- message,
    type challenge <- challenge,
    type response <- response,

    op R = R,
    op dchallenge = dchallenge
    proof *.
    realize dchallenge_llfuni by apply dchallenge_llfuni.
  export Sigma.



  module ORProtocol (P1 : S1.SProtocol, P2 : S2.SProtocol) : Sigma.SProtocol = {
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

    proc init(h : statement, w : witness) : message = {
      var h1, h2, ret, a1, a2;
      (h1, h2) = h;

      if (R1 h1 w) {
        a1 = P1.init(h1, w);
        e2 <$ dchallenge;
        (a2, z2) = P2.simulator(h2, e2);
        ret = (a1, a2);
      } else {
        a2 = P2.init(h2, w);
        e1 <$ dchallenge;
        (a1, z1) = P1.simulator(h1, e1);
        ret = (a1, a2);
      }
      return ret;
    }

    proc response(h : statement, w : witness, m : message, s : challenge) : response = {
      var m1, m2, h1, h2;
      (m1, m2) = m;
      (h1, h2) = h;

      if (R1 h1 w) {
        e1 = s ^^ e2;
        z1 = P1.response(h1, w, m1, e1);
      } else {
        e2 = s ^^ e1;
        z2 = P2.response(h2, w, m2, e2);
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
declare module SP1 : S1.SProtocol{ORProtocol}.
declare module SP2 : S2.SProtocol{ORProtocol,SP1}.

local module C1 = S1.Completeness(SP1).
local module C2 = S2.Completeness(SP2).

local module SHVZK1 = S1.SHVZK(SP1).
local module SHVZK2 = S2.SHVZK(SP2).

  axiom completeness_protocol1 h w e &m : (R1 h w) => Pr[S1.Completeness(SP1).special(h, w, e) @ &m : res] = 1%r.
  axiom completeness_protocol2 h w e &m : (R2 h w) => Pr[S2.Completeness(SP2).special(h, w, e) @ &m : res] = 1%r.

  axiom shvzk1_equiv h' w' e':
    equiv[S1.SHVZK(SP1).real ~ S1.SHVZK(SP1).ideal : (={h, e} /\ e{1} = e' /\ h{2} = h' /\ w{1} = w' /\ (R1 h' w')) ==> ={res}].
  axiom shvzk2_equiv h' w' e':
    equiv[S2.SHVZK(SP2).real ~ S2.SHVZK(SP2).ideal : (={h, e} /\ e{1} = e' /\ h{2} = h' /\ w{1} = w' /\ (R2 h' w')) ==> ={res}].

  local lemma shvzk1_equiv_pr h' w' e' a &m:
      (R1 h' w') =>
      Pr[S1.SHVZK(SP1).real(h', w', e') @ &m : (res = a)] =
      Pr[S1.SHVZK(SP1).ideal(h', e') @ &m : (res = a)].
  proof. move=>rel.
  by byequiv (shvzk1_equiv h' w' e'). qed.

  axiom shvzk1_ideal_never_fails_pr h' e' &m:
      Pr[S1.SHVZK(SP1).ideal(h', e') @ &m : (res <> None)] = 1%r.
  axiom shvzk2_ideal_never_fails_pr h' e' &m:
      Pr[S2.SHVZK(SP2).ideal(h', e') @ &m : (res <> None)] = 1%r.

  local lemma shvzk1_ideal_never_fails h' e':
        phoare[S1.SHVZK(SP1).ideal : (h = h' /\ e = e') ==> (res <> None)] = 1%r.
  proof. have H := (shvzk1_ideal_never_fails_pr h' e'). bypr. progress. apply (H &m). qed.

  local lemma shvzk2_ideal_never_fails h' e':
        phoare[S2.SHVZK(SP2).ideal : (h = h' /\ e = e') ==> (res <> None)] = 1%r.
  proof. have H := (shvzk2_ideal_never_fails_pr h' e'). bypr. progress. apply (H &m). qed.

  local lemma shvzk1_real_never_fails h' w' e':
        phoare[S1.SHVZK(SP1).real : (h = h' /\ e = e' /\ w = w' /\ (R1 h' w')) ==> (res <> None)] = 1%r.
  proof.
  bypr. progress.
  have -> := (S1.shvzk_real_never_fail SP1 h{m} w{m} e{m} &m).
  by have := (completeness_protocol1 h{m} w{m} e{m} &m H).
  qed.

  local lemma shvzk2_real_never_fails h' w' e':
        phoare[S2.SHVZK(SP2).real : (h = h' /\ e = e' /\ w = w' /\ (R2 h' w')) ==> (res <> None)] = 1%r.
  proof.
  bypr. progress.
  have -> := (S2.shvzk_real_never_fail SP2 h{m} w{m} e{m} &m).
  by have := (completeness_protocol2 h{m} w{m} e{m} &m H).
  qed.

  (* Converting the ambient logic to the pHoare logic *)
local lemma SP1_completeness_pr h' w' e' : phoare[C1.special : (h = h' /\ e = e' /\ w = w' /\ (R1 h' w')) ==> res] = 1%r.
    proof. bypr. progress. by have := (completeness_protocol1 h{m} w{m} e{m} &m H). qed.
local lemma SP2_completeness_pr h' w' e' : phoare[C2.special : (h = h' /\ e = e' /\ w = w' /\ (R2 h' w')) ==> res] = 1%r.
    proof. bypr. progress. by have := (completeness_protocol2 h{m} w{m} e{m} &m H). qed.

local module Completeness' = {
  proc ideal1 (h1 : statement1, e1 : challenge) = {
      var a1, z1, v1;

      (a1, z1) = SP1.simulator(h1, e1);
      v1 = SP1.verify(h1, a1, e1, z1);
      return v1;
  }

  proc ideal2 (h2 : statement2, e2 : challenge) = {
      var a2, z2, v2;

      (a2, z2) = SP2.simulator(h2, e2);
      v2 = SP2.verify(h2, a2, e2, z2);
      return v2;
  }

  proc real1 (h1 : statement1, w : witness, e1 : challenge) : bool = {
      var a1, z1, v1;

      a1 = SP1.init(h1, w);
      z1 = SP1.response(h1, w, a1, e1);
      v1 = SP1.verify(h1, a1, e1, z1);
      return v1;
  }

  proc real2 (h2 : statement2, w : witness, e2) : bool = {
      var a2, z2, v2;

      a2 = SP2.init(h2, w);
      z2 = SP2.response(h2, w, a2, e2);
      v2 = SP2.verify(h2, a2, e2, z2);
      return v2;
  }

  proc main(h : statement, w : witness, e : challenge) : bool = {
    var h1, h2, v1, v2, e1, e2;
    (h1, h2) = h;

    if (R1 h1 w) {
      e2 <$ dchallenge;
      v2 = ideal2(h2, e2);
      e1 = e ^^ e2;
      v1 = real1(h1, w, e1);
    } else {
      e1 <$ dchallenge;
      v1 = ideal1(h1, e1);
      e2 = e ^^ e1;
      v2 = real2(h2, w, e2);
    }
    return (e = e1 ^^ e2) /\ v1 /\ v2;
  }
}.

  local lemma ideal1_success h' e1':
      phoare[Completeness'.ideal1 : (h1 = h' /\ e1 = e1') ==> res] = 1%r.
  proof.
    bypr=> &m hrel.
    have <- := (shvzk1_ideal_never_fails_pr h1{m} e1{m} &m).
    byequiv=>//. proc. inline *. wp.
    by do ? call (: true).
  qed.

  local lemma ideal2_success h' e2':
      phoare[Completeness'.ideal2 : (h2 = h' /\ e2 = e2') ==> res] = 1%r.
  proof.
    bypr=> &m hrel.
    have <- := (shvzk2_ideal_never_fails_pr h2{m} e2{m} &m).
    byequiv=>//. proc. inline *. wp.
    by do ? call (: true).
  qed.

  local lemma completeness_sim_equiv h' w' e' &m:
      Pr[Sigma.Completeness(ORProtocol(SP1,SP2)).special(h', w', e') @ &m : res] =
      Pr[Completeness'.main(h', w', e') @ &m : res].
  proof.
    byequiv=>//. proc. inline *. sp. wp.
    case (R1 (fst h') w').
      - rcondt{1} 1. progress.
      - rcondt{2} 1. progress.
      - rcondt{1} 12. progress. auto. call (: true). rnd. call (: true). auto.
    swap{2} [5..6] 7.
    swap{2} [5..9] -1.
    swap{1} 1 1.
    sim.
    do ? (wp; call (:true)).
    auto.
    (* case: R2 is true *)
      - rcondf{1} 1. progress.
      - rcondf{2} 1. progress.
      - rcondf{1} 12. progress. auto. call (: true). rnd. call (: true). auto.
    swap{2} [5..6] 6.
    swap{2} [5..9] -1.
    swap{1} 1 1.
    sim.
    do ? (wp; call (:true)).
    auto.
  qed.

  local lemma real1_success h' w' e1':
      phoare[Completeness'.real1 : (h1 = h' /\ e1 = e1' /\ w = w' /\ (R1 h' w')) ==> res] = 1%r.
  proof.
    bypr=> &m [hrel [erel [wrel rel]]].
    have <- := (completeness_protocol1 h' w' e1' &m rel).
    byequiv=> //. proc.
    by do ? call (: true).
  qed.

  local lemma real2_success h' w' e2':
      phoare[Completeness'.real2 : (h2 = h' /\ e2 = e2' /\ w = w' /\ (R2 h' w')) ==> res] = 1%r.
  proof.
    bypr=> &m [hrel [erel [wrel rel]]].
    have <- := (completeness_protocol2 h' w' e2' &m rel).
    byequiv=> //. proc.
    by do ? call (: true).
  qed.

  local lemma completeness'_true h' w' e' &m:
      R h' w' =>
      Pr[Completeness'.main(h', w', e') @ &m : res] = 1%r.
  proof.
    move=> rel.
    byphoare (: h = h' /\ e = e' /\ w = w' ==> _)=>//. proc. sp.
    if.
    - seq 1 : (#pre /\ e2 = e2). auto. auto. progress. apply Sigma.dchallenge_ll.
      exists* e2. elim*=> e2.
      call (real1_success (fst h') w' (e' ^^ e2)). wp.
      call (ideal2_success (snd h') e2). auto. progress.
      by rewrite xorK.
      hoare. auto. progress.
    - seq 1 : (#pre /\ e1 = e1). auto. auto. progress. apply Sigma.dchallenge_ll.
      exists* e1. elim*=> e1.
      call (real2_success (snd h') w' (e' ^^ e1)). wp.
      call (ideal1_success (fst h') e1). auto. progress.
      smt().
      by rewrite xorA xorK.
      hoare. auto. progress.
  qed.

  lemma or_completeness h' w' e' &m:
      (Sigma.R h' w') =>
      Pr[Sigma.Completeness(ORProtocol(SP1,SP2)).special(h', w', e') @ &m : res] = 1%r.
  proof.
    move=> rel.
    have -> := (completeness_sim_equiv h' w' e' &m).
    by have := (completeness'_true h' w' e' &m rel).
  qed.

  local module SHVZK' = {
      proc real(h, w, e) : transcript option = {
        var h1, h2, a1, a2, z1, z2, e1, e2, ret, t1, t2;
        (h1, h2) = h;
        if (R1 h1 w) {
          e2 <$ dchallenge;
          e1 = e ^^ e2;
          t1 = SHVZK1.real(h1, w, e1);
          t2 = SHVZK2.ideal(h2, e2);
          if (t1 = None \/ t2 = None) {
            ret = None;
          } else {
            (a1, e1, z1) = oget(t1);
            (a2, e2, z2) = oget(t2);
            ret = Some ((a1, a2), e, (e1, z1, e2, z2));
          }
        } else {
          e1 <$ dchallenge;
          e2 = e ^^ e1;
          t2 = SHVZK2.real(h2, w, e2);
          t1 = SHVZK1.ideal(h1, e1);
          if (t1 = None \/ t2 = None) {
            ret = None;
          } else {
            (a1, e1, z1) = oget(t1);
            (a2, e2, z2) = oget(t2);
            ret = Some ((a1, a2), e, (e1, z1, e2, z2));
          }
        }
        return ret;
      }
      proc ideal(h, e) : transcript option = {
        var h1, h2, a1, a2, z1, z2, e1, e2, ret, t1, t2;
        (h1, h2) = h;
        e2 <$ dchallenge;
        e1 = e ^^ e2;
        t1 = SHVZK1.ideal(h1, e1);
        t2 = SHVZK2.ideal(h2, e2);
        if (t1 = None \/ t2 = None) {
          ret = None;
        } else {
          (a1, e1, z1) = oget(t1);
          (a2, e2, z2) = oget(t2);
          ret = Some ((a1, a2), e, (e1, z1, e2, z2));
        }
        return ret;
      }
    }.

  local equiv real_real'_equiv h' w' e':
    Sigma.SHVZK(ORProtocol(SP1, SP2)).real ~ SHVZK'.real :
    (h{2} = h' /\ w{2} = w' /\ e{2} = e' /\ (R h' w') /\ ={h, w, e, glob SP1, glob SP2}) ==> ={res}.
  proof.
  proc. inline *. sp. case (R1 (fst h') w').
  (* case: relation is true *)
  rcondt{1} 1. progress.
  rcondt{2} 1. progress.
  rcondt{1} 12. auto. call (:true). rnd. call(:true). progress.
  sp.
  swap{2} [9..11] 5; swap{1} 2 -1; swap{1} [3..5] 2; swap{2} [9..11] -2.
  do ? (wp; call (: true)).
  auto. progress.
  - by rewrite xorK.
  (* case: relation is false *)
  rcondf{1} 1. progress.
  rcondf{2} 1. progress.
  rcondf{1} 12. auto. call (:true). rnd. call(:true). progress.
  sp.
  swap{2} [9..11] 5; swap{2} 8 4; swap{2} [8..10] -1; swap{1} 2 -1.
  do ? (wp; call (:true)).
  auto. progress.
  - by rewrite xorA xorK.
  qed.

  local equiv ideal_ideal'_equiv h' e':
    SHVZK'.ideal ~ Sigma.SHVZK(ORProtocol(SP1, SP2)).ideal :
    (h{2} = h' /\ e{2} = e' /\ ={h, e, glob SP1, glob SP2}) ==> ={res}.
  proof.
  proc. inline *. sp.
  swap{1} [10..12] -4.
  do ? (wp; call (:true)).
  auto. progress.
  apply : contra H2. by rewrite xorK.
  qed.

  equiv or_shvzk h' w' e' &m:
      Sigma.SHVZK(ORProtocol(SP1, SP2)).real ~
      Sigma.SHVZK(ORProtocol(SP1, SP2)).ideal :
      (h{2} = h' /\ e{2} = e' /\ ={h, e, glob SP1, glob SP2} /\ w{1} = w' /\ (R h' w')) ==> ={res}.
  proof.
    have ? := (real_real'_equiv h' w' e').
    have ? := (ideal_ideal'_equiv h' e').
    transitivity SHVZK'.real
      (h{2} = h' /\ w{2} = w' /\ e{2} = e' /\ (R h' w') /\ ={h, w, e, glob SP1, glob SP2} ==> ={res})
      (h{2} = h' /\ e{2} = e' /\ w{1} = w' /\ (R h' w') /\ ={h, e, glob SP1, glob SP2} ==> ={res})=>//.
    - smt().
    transitivity SHVZK'.ideal
      (h{2} = h' /\ e{2} = e' /\ w{1} = w' /\ (R h' w') /\ ={h, e, glob SP1, glob SP2} ==> ={res})
      (h{2} = h' /\ e{2} = e' /\ ={h, e, glob SP1, glob SP2} ==> ={res})=>//.
    - smt().

    case (R1 (fst h') w')=> rel_true.
    proc.
    rcondt{1} 2. auto.
    inline SHVZK2.ideal. sim. sp.
    seq 1 1 : (#pre /\ e2{1} = e2{2}). auto.
    exists* e2{2}. elim*. progress.
    call (shvzk1_equiv (fst h') w' (e' ^^ e2_R)); auto.

    proc.
    auto. rcondf{1} 2. auto. sp.
    auto. swap{2} 3 1. inline SHVZK1.ideal.
    wp. call (:true).
        call (:true).
    wp. seq 2 2 : (#pre /\ ={e1, e2}).
    wp. rnd (fun r => r ^^ e{2}) (fun q => q ^^ e{1}).
    auto. progress.
      - by rewrite xorK.
      - apply Sigma.dchallenge_funi.
      - apply Sigma.dchallenge_fu.
      - by rewrite xorK.
      - by rewrite xorA.
      - by rewrite xorA.
    exists* e2{2}. elim*. progress. sp.
    call (shvzk2_equiv (snd h') w' e2_R); auto; progress; smt().
  qed.

  axiom special_soundness_sp1 x msg ch ch' d d' &m :
    ch <> ch' =>
    phoare[SP1.verify : (h = x /\ m = msg /\ e = ch /\ z = d) ==> res] = 1%r =>
    phoare[SP1.verify : (h = x /\ m = msg /\ e = ch' /\ z = d') ==> res] = 1%r =>
    Pr[S1.SpecialSoundness(SP1).main(x, msg, ch, ch', d, d') @ &m : res] = 1%r.

  axiom special_soundness_sp2 x msg ch ch' d d' &m :
    ch <> ch' =>
    phoare[SP2.verify : (h = x /\ m = msg /\ e = ch /\ z = d) ==> res] = 1%r =>
    phoare[SP2.verify : (h = x /\ m = msg /\ e = ch' /\ z = d') ==> res] = 1%r =>
    Pr[S2.SpecialSoundness(SP2).main(x, msg, ch, ch', d, d') @ &m : res] = 1%r.

  local module SpecialSoundness' = {
      var w : witness
      var vd : bool
      var vd' : bool
      proc special_soundness1(h : statement, m, e, e', z, z') = {
        var h1, h2;
        (h1, h2) = h;

        vd  = SP1.verify(h1, m, e, z);
        vd' = SP1.verify(h1, m, e', z');

        w = SP1.witness_extractor(h1, m, e, e', z, z');

        return (e <> e' /\ (R1 h1 w) /\ vd /\ vd');
      }
      proc special_soundness2(h : statement, m, e, e', z, z') = {
        var h1, h2;
        (h1, h2) = h;

        vd  = SP2.verify(h2, m, e, z);
        vd' = SP2.verify(h2, m, e', z');

        w = SP2.witness_extractor(h2, m, e, e', z, z');

        return (e <> e' /\ (R2 h2 w) /\ vd /\ vd');
      }
      proc main(h, m, e e' : challenge, z, z') = {
        var e1,e1',e2,e2',z1,z1',z2,z2',h1,h2,m1,m2,v,v',ret;
        (m1, m2) = m;
        (h1, h2) = h;
        (e1, z1, e2, z2) = z;
        (e1', z1', e2', z2') = z';
        if (e1 <> e1') {
          v  = SP2.verify(h2, m2, e2, z2);
          v' = SP2.verify(h2, m2, e2', z2');
          ret = special_soundness1(h, m1, e1, e1', z1, z1');
        } else {
          v  = SP1.verify(h1, m1, e1, z1);
          v' = SP1.verify(h1, m1, e1', z1');
          ret = special_soundness2(h, m2, e2, e2', z2, z2');
        }
        return (e <> e' /\ e = e1 ^^ e2 /\ e' = e1' ^^ e2' /\ v /\ v' /\ vd /\ vd' /\ (R h w));
      }
    }.

  local lemma special_soundness_soundness'_equiv
    x msg ch ch' e1 e1' e2 e2' z1 z1' z2 z2' &m:
      Pr[SpecialSoundness'.main(x, msg, ch, ch', (e1, z1, e2, z2), (e1', z1', e2', z2')) @ &m : res] =
      Pr[Sigma.SpecialSoundness(ORProtocol(SP1, SP2)).main(x, msg, ch, ch', (e1, z1, e2, z2), (e1', z1', e2', z2')) @ &m : res].
  proof.
    byequiv=>//. proc. inline *. sp.
    case (e1 <> e1').
    rcondt{1} 1. auto.
    rcondt{2} 24. move=> ?. do ? (wp; call (:true)). auto.
    (* Put statements in similar order between the two programs *)
    swap{2} 11 1; swap{1} 2 8; swap{2} 1 1.
    do ? (wp; call (:true)).
    auto. smt().
    (* case : e2 <> e2' *)
    rcondf{1} 1. auto.
    rcondf{2} 24. move=> ?. do ? (wp; call (:true)). auto.
    swap{1} 2 8.
    do ? (wp; call (:true)).
    auto. smt().
  qed.

  local lemma special_soundness1'
    x msg ch ch' r r':
      ch <> ch' =>
      phoare[SP1.verify : (h = (fst x) /\ m = msg /\ e = ch /\ z = r) ==> res] = 1%r =>
      phoare[SP1.verify : (h = (fst x) /\ m = msg /\ e = ch' /\ z = r') ==> res] = 1%r =>
      phoare[SpecialSoundness'.special_soundness1 :
        (h = x /\ m = msg /\ e = ch /\ e' = ch' /\ z = r /\ z' = r') ==> (res /\ SpecialSoundness'.vd /\ SpecialSoundness'.vd' /\ R x SpecialSoundness'.w)] = 1%r.
  proof.
    move=> ch_diff accept1 accept2.
    bypr. progress.
    have <- := (special_soundness_sp1 (fst h{m}) m{m} e{m} e'{m} z{m} z'{m} &m ch_diff accept1 accept2).
    byequiv=>//. proc. do ? call(:true). auto; smt(). qed.

  local lemma special_soundness2'
    x msg ch ch' r r':
      ch <> ch' =>
      phoare[SP2.verify : (h = (snd x) /\ m = msg /\ e = ch /\ z = r) ==> res] = 1%r =>
      phoare[SP2.verify : (h = (snd x) /\ m = msg /\ e = ch' /\ z = r') ==> res] = 1%r =>
      phoare[SpecialSoundness'.special_soundness2 :
        (h = x /\ m = msg /\ e = ch /\ e' = ch' /\ z = r /\ z' = r') ==> (res /\ SpecialSoundness'.vd /\ SpecialSoundness'.vd' /\ R x SpecialSoundness'.w)] = 1%r.
  proof.
    move=> ch_diff accept1 accept2.
    bypr. progress.
    have <- := (special_soundness_sp2 (snd h{m}) m{m} e{m} e'{m} z{m} z'{m} &m ch_diff accept1 accept2).
    byequiv=>//. proc. do ? call(:true). auto; smt(). qed.

  local lemma special_soundness'
    x msg ch ch' e1 e1' z1 z1' e2 e2' z2 z2' &m:
      ch <> ch' =>
      ch = e1 ^^ e2 => (* We explicitly write out what it means for an OR conversation to be accepting *)
      ch' = e1' ^^ e2' =>
      phoare[SP1.verify : (h = (fst x) /\ m = (fst msg) /\ e = e1 /\ z = z1) ==> res] = 1%r =>
      phoare[SP1.verify : (h = (fst x) /\ m = (fst msg) /\ e = e1' /\ z = z1') ==> res] = 1%r =>
      phoare[SP2.verify : (h = (snd x) /\ m = (snd msg) /\ e = e2 /\ z = z2) ==> res] = 1%r =>
      phoare[SP2.verify : (h = (snd x) /\ m = (snd msg) /\ e = e2' /\ z = z2') ==> res] = 1%r =>
      Pr[SpecialSoundness'.main(x, msg, ch, ch', (e1, z1, e2, z2), (e1', z1', e2', z2')) @ &m : res] = 1%r.
  proof.
    move=> ch_diff ch_valid ch'_valid accept11 accept12 accept21 accept22.

    case (e1 <> e1')=> e1_diff.
    byphoare(: h = x /\ m = msg /\ e = ch /\ e' = ch' /\ z = (e1, z1, e2, z2) /\ z' = (e1', z1', e2', z2') ==> _)=>//.
    proc. sp. rcondt 1. auto.
    - have H1 := (special_soundness1' x (fst msg) e1 e1' z1 z1' e1_diff accept11 accept12).
      call H1. call accept22. call accept21. auto.

    have e2_diff : (e2 <> e2') by smt().
    byphoare(: h = x /\ m = msg /\ e = ch /\ e' = ch' /\ z = (e1, z1, e2, z2) /\ z' = (e1', z1', e2', z2') ==> _)=>//.
    proc. sp. rcondf 1. auto.
    - have H2 := (special_soundness2' x (snd msg) e2 e2' z2 z2' e2_diff accept21 accept22).
      call H2. call accept12. call accept11. auto.
  qed.

  (* TODO: Can this be written with just: *)
  (* phoare[OR.verify ==> res]? *)
  lemma or_special_soundness x msg ch ch' e1 e1' z1 z1' e2 e2' z2 z2' &m:
      ch <> ch' =>
      ch = e1 ^^ e2 => (* We explicitly write out what it means for an OR conversation to be accepting *)
      ch' = e1' ^^ e2' =>
      phoare[SP1.verify : (h = (fst x) /\ m = (fst msg) /\ e = e1 /\ z = z1) ==> res] = 1%r =>
      phoare[SP1.verify : (h = (fst x) /\ m = (fst msg) /\ e = e1' /\ z = z1') ==> res] = 1%r =>
      phoare[SP2.verify : (h = (snd x) /\ m = (snd msg) /\ e = e2 /\ z = z2) ==> res] = 1%r =>
      phoare[SP2.verify : (h = (snd x) /\ m = (snd msg) /\ e = e2' /\ z = z2') ==> res] = 1%r =>
      Pr[Sigma.SpecialSoundness(ORProtocol(SP1, SP2)).main(x, msg, ch, ch', (e1, z1, e2, z2), (e1', z1', e2', z2')) @ &m : res] = 1%r.
  proof. move=> ch_diff ch_valid ch'_valid accept11 accept12 accept21 accept22.
    have <- := (special_soundness_soundness'_equiv x msg ch ch' e1 e1' e2 e2' z1 z1' z2 z2' &m).
    by have := (special_soundness' x msg ch ch' e1 e1' z1 z1' e2 e2' z2 z2' &m ch_diff ch_valid ch'_valid accept11 accept12 accept21 accept22).
  qed.

end section Security.
end ORProtocol.
