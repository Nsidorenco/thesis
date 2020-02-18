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

  op dchallenge : {challenge distr | is_lossless dchallenge} as dchallenge_ll.

  op (^^) (c1 : challenge, c2 : challenge) : challenge.
  axiom otp_property x c1 : (x ^^ c1) ^^ c1 = x.

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
    realize SigmaProtocols.dchallenge_ll by apply dchallenge_ll.

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
    realize SigmaProtocols.dchallenge_ll by apply dchallenge_ll.

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
    realize SigmaProtocols.dchallenge_ll by apply dchallenge_ll.

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

axiom SP1_completeness h w &m : (R1 h w) => Pr[S1.SigmaProtocols.Completeness(SP1).main(h, w) @ &m : res] = 1%r.
axiom SP2_completeness h w &m : (R2 h w) => Pr[S2.SigmaProtocols.Completeness(SP2).main(h, w) @ &m : res] = 1%r.
(* local lemma SP2_completeness' h' w' : hoare[C2.main : (h = h' /\ w = w' /\ (R2 h' w')) ==> res]. *)
(*     proof. bypr. progress. apply (SP2_completeness &m) in H. smt. qed. *)
(* local lemma SP1_completeness' h' w' : hoare[C1.main : (h = h' /\ w = w' /\ (R1 h' w')) ==> res]. *)
(*     proof. bypr. progress. apply (SP1_completeness &m) in H. smt. qed. *)

local lemma SP2_completeness_pr h' w' : phoare[C2.main : (h = h' /\ w = w' /\ (R2 h' w')) ==> res] = 1%r.
    proof. bypr. progress. apply (SP2_completeness &m) in H. assumption. qed.
local lemma SP1_completeness_pr h' w' : phoare[C1.main : (h = h' /\ w = w' /\ (R1 h' w')) ==> res] = 1%r.
    proof. bypr. progress. apply (SP1_completeness &m) in H. assumption. qed.


axiom SP2_sim_ll : islossless SP2.simulator.
axiom SP1_init_ll : islossless SP1.init.

local module CompletenessComp = {
  proc main(h : statement, w : witness) : bool = {
    var h1, h2, v, v';
    (h1, h2) = h;
    v  = C1.main(h1, w);
    v' = C2.main(h2, w);

    return (v /\ v');
  }
}.

local module CompletenessCompSplit = {
  proc part11 (h : statement1, w : witness) : message1 * challenge * response1 = {
      var a, r, e, z;
      (a, r) = SP1.init(h, w);
      e <$ S1.SigmaProtocols.dchallenge;
      z = SP1.response(h, w, a, r,  e);
      return (a, e, z);
  }
  proc part12 (h : statement2, w : witness) : message2 * challenge * response2 = {
      var a, r, e, z;
      (a, r) = SP2.init(h, w);
      e <$ S2.SigmaProtocols.dchallenge;
      z = SP2.response(h, w, a, r,  e);
      return (a, e, z);
  }
  proc main(h : statement, w : witness) : bool = {
    var h1, h2, v, v', a1, a2, e1, e2, z1, z2;
    (h1, h2) = h;
    (a1, e1, z1) = part11(h1, w);
    v  = SP1.verify(h1, a1, e1, z1);
    (a2, e2, z2) = part12(h2, w);
    v'  = SP2.verify(h2, a2, e2, z2);

    return (v /\ v');
  }
}.

local module Completeness' = {
  proc main(h : statement, w : witness) : bool = {
    var h1, h2, a1, a2, e1, e2, z1, z2, s, r, v1, v2;
    (h1, h2) = h;
    if (R1 h1 w) {
      e2 <$ dchallenge;
      (a2, z2) = SP2.simulator(h2, e2);
      v2 = SP2.verify(h2, a2, e2, z2);

      (a1, r) = SP1.init(h1, w);
      s <$ Sigma.SigmaProtocols.dchallenge;
      e1 = s ^^ e2;

      z1 = SP1.response(h1, w, a1, r, e1);
      v1 = SP1.verify(h1, a1, e1, z1);

      } else {
        e1 <$ dchallenge;
        (a1, z1) = SP1.simulator(h1, e1);
        v1 = SP1.verify(h1, a1, e1, z1);

        (a2, r) = SP2.init(h2, w);
        s <$ Sigma.SigmaProtocols.dchallenge;
        e2 = s ^^ e1;

        z2 = SP2.response(h2, w, a2, r, e2);
        v2 = SP2.verify(h2, a2, e2, z2);
      }
      return  (s = e1 ^^ e2) /\ v1 /\ v2;
    }
  }.


local module Completeness_procedurised = {
  proc fake1 (h1 : statement1) = {
      var a1, z1, v1, e2, e1, s;
      e1 <$ dchallenge;
      s <$ Sigma.SigmaProtocols.dchallenge;
      e2 = s ^^ e1;

      (a1, z1) = SP1.simulator(h1, e1);
      v1 = SP1.verify(h1, a1, e1, z1);
      return (s, e1, e2, v1);
  }

  proc fake2 (h2 : statement2) = {
      var a2, z2, v2, e2, s, e1;
      e2 <$ dchallenge;
      s <$ Sigma.SigmaProtocols.dchallenge;
      e1 = s ^^ e2;

      (a2, z2) = SP2.simulator(h2, e2);
      v2 = SP2.verify(h2, a2, e2, z2);
      return (s, e1, e2, v2);
  }

  proc real1 (h1 : statement1, w : witness, e1 : challenge) : bool = {
      var a1, r, z1, v1;
      (a1, r) = SP1.init(h1, w);
      z1 = SP1.response(h1, w, a1, r, e1);
      v1 = SP1.verify(h1, a1, e1, z1);
      return v1;
  }

  proc real2 (h2 : statement2, w : witness, e2 : challenge) : bool = {
      var a2, r, z2, v2;
      (a2, r) = SP2.init(h2, w);
      z2 = SP2.response(h2, w, a2, r, e2);
      v2 = SP2.verify(h2, a2, e2, z2);
      return v2;
  }


  proc main(h : statement, w : witness) : bool = {
    var h1, h2, e1, e2, v1, v2, s;
    (h1, h2) = h;
    if (R1 h1 w) {
      (s, e1, e2, v2) = fake2(h2);
      v1 = real1(h1, w, e1);
    } else {
      (s, e1, e2, v1) = fake1(h1);
      v2 = real2(h2, w, e2);
    }
    return (s = e1 ^^ e2) /\ v1 /\ v2;
    }
  }.

(* local lemma completeness_comp h' h1 h2 w': *)
(*     h' = (h1, h2) => *)
(*     (R1 h1 w') /\ (R2 h2 w') => *)
(*     (* Pr[CompletenessComp.main(h', w') @ &m : res] = 1%r. *) *)
(*     hoare[CompletenessComp.main : (h = h' /\ w = w') ==> res]. *)
(*     proof. move=> h_prod [rel1 rel2]. *)
(*     proc. *)
(*     call (SP2_completeness' h2 w'). *)
(*     call (SP1_completeness' h1 w'). *)
(*     auto; progress; rewrite h_prod; done. *)
(*     qed. *)

local lemma completeness_comp h' h1 h2 w' &m:
    h' = (h1, h2) =>
    (* FIXME: This assumption makes the whole proof chain invalid?*)
    (R1 h1 w') /\ (R2 h2 w') =>
    Pr[CompletenessComp.main(h', w') @ &m : res] = 1%r.
    proof.
    move=> h_prod [rel1 rel2].
    byphoare (: (h = h' /\ w = w') ==> _)=> //. proc.
    call (SP2_completeness_pr h2 w').
    call (SP1_completeness_pr h1 w'). auto.
    auto; progress; rewrite h_prod; done.
    qed.

    (* extra helper lemma, split C(1|2).main into two parts *)
    (* (a,e,z) = part1 *)
    (* v = verify(a,e,z) = part2 *)
    local lemma comp_split h' h1 h2 w' &m:
        h' = (h1, h2) =>
        Pr[CompletenessCompSplit.main(h', w') @ &m : res] =
        Pr[CompletenessComp.main(h', w') @ &m : res].
    proof. move=> h_prod.
    byequiv. proc. inline *. sim. progress. progress.
    qed.



    local lemma completeness_sim_equiv h' w' &m:
        Pr[Sigma.SigmaProtocols.Completeness(ORProtocol(SP1,SP2)).main(h', w') @ &m : res] =
        Pr[Completeness'.main(h', w') @ &m : res].
    proof. byequiv=> //.
    proc. inline *. auto. sp.
    case (R1 (fst h') w').
    (* relation is true *)
      - rcondt{1} 1. progress.
      - rcondt{2} 1. progress.
      - rcondt{1} 14. progress. auto. call (: true). rnd. call (: true). progress.
    swap{2} 3 5. sim. wp. call (: true). wp. rnd. wp.
    swap{1} 2 -1. swap{2} 3 -1. call (: true). call (: true). rnd.
    auto.
    (* relation is false *)
      - rcondf{1} 1. progress.
      - rcondf{2} 1. progress.
      - rcondf{1} 14. progress. auto. call (: true). rnd. call (: true). progress.
    swap{2} 3 4. sim. wp. call (: true). wp. rnd. wp.
    swap{1} 2 -1. swap{2} 3 - 1. call (: true). call (: true). rnd.
    auto.
    qed.

    local lemma completeness_proc_equiv h' w' &m:
        Pr[Completeness'.main(h', w') @ &m : res] =
        Pr[Completeness_procedurised.main(h', w') @ &m : res].
    proof. byequiv=> //. proc. inline *. sp.
    if; progress; swap{1} [5..6] -3; sim.
    qed.

    local lemma real1_completeness1_equiv h' w' e' &m:
        Pr[Completeness_procedurised.real1(h', w', e') @ &m : res] =
        Pr[C1.main(h', w') @ &m : res].
    proof. byequiv=> //. proc. swap {2} 2 -1. sim.
    seq 1 1 : ( (e{2} = e')). auto. progress. apply dchallenge_ll.
    auto. progress. apply dchallenge_ll.
    rnd{2}. auto. progress. apply dchallenge_ll.


    local lemma completeness'_correct h' h1 h2 w' &m:
        h' = (h1, h2) =>
        Pr[Completeness_procedurised.main(h', w') @ &m : res] = 1%r.
    proof. move=> h_rel. byphoare => //. proc. sp.
    if.





(* local lemma completeness_or_helper &m h' h1 h2 w': *)
(*     h' = (h1, h2) => *)
(*     (R1 h1 w') \/ (R2 h2 w') => *)
(*     Pr[Sigma.SigmaProtocols.Completeness(ORProtocol(SP1, SP2)).main(h', w') @ &m : res] = *)
(*     Pr[CompletenessComp.main(h', w') @ &m : res]. *)
(*     proof. move=> h_prod rel. *)
(*     byequiv (: (={glob SP1, glob SP2, h, w} /\ h{1} = h' /\ h{2} = h') ==> _)=> //=. *)
(*     proc. inline *. auto. sp. *)
(*       case (R1 (fst h0{1}) w0{1}). rcondt{1} 1. progress. *)
(*     rcondt{1} 14. progress. auto. call (: true). rnd. call (: true). auto. *)
(*     (* NOTE: Plan for tomorrow: *) *)
(*     (* Swap order of SP1 and SP2, such that we end with sim -> verify on lhs. *) *)
(*     (* swap{1} 25 -1. swap{2} [4..5] 6. wp. call (: true). *) *)
(*     (* swap{1} [4..5] 2. *) *)
(*     (* swap{1} [5..5] 2. *) *)
(*     call (: true). swap{2} 5 5. *)
(*     progress. *)
(*     swap{2} 4 5. wp. call (: true). wp. *)
(*     swap{2} 3 5. call (: true). wp. *)
(*     swap{1} 6 -3. wp. *)
(*     swap 1 3. swap{2} 4 3. call (: true). *)
(*     swap{2} 1 5. swap{1} 2 1. rnd. sp. *)
(*     (* sim : (a2{1} = m0{2} /\ ORProtocol.z2{1} = z0{2}). *) *)

lemma completeness_or &m h' h1 h2 w':
    h' = (h1, h2) =>
    (R1 h1 w') \/ (R2 h2 w') =>
    Pr[Sigma.SigmaProtocols.Completeness(ORProtocol(SP1, SP2)).main(h', w') @ &m : res] = 1%r.
    proof. move=> h_rel rel.
    byphoare (: (h = h' /\ w = w') ==> _)=> //. proc.
    inline *.
    sp. case (R1 h1 w').
      rcondt 1. skip. smt().
    rcondt 14. progress. auto. call (: true). rnd. call (: true). auto. smt().
      rcondt 1. auto. progress. smt().
      rcondt 14. auto. call (: true). rnd. call (: true). auto.
      inline *. auto.
    seq 5 : (m = (a1, a2)). auto. wp. progress.
    call SP2_sim_ll. rnd.
    call SP1_init_ll. auto. progress. apply dchallenge_ll.
    seq 1 : #pre. rnd. auto. rnd. auto. progress. apply dchallenge_ll.
    sp.

    apply SP1_completeness.


    (* Idea *)
    (* Swap around statements, such that seq i j is the same as Completeness(P(1|2)) *)
    (* Then prove equivalence. *)
    (* Need to alter implementation to not just global state, prevents swapping statements. *)
end section Security.
end ORProtocol.
