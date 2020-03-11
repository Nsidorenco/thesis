(* Formalization of Sigma Protocols *)
require import AllCore Distr DBool.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

theory SigmaProtocols.
  type statement.
  type witness.
  type message.
  type randomness.
  type challenge.
  type response.

  type transcript = message * challenge * response.

  (* define the relations *)
  op R (x : statement) (w : witness) : bool.

  op dchallenge : {challenge distr | is_lossless dchallenge /\ is_funiform dchallenge} as dchallenge_llfuni.
  (* op dpub : {statement distr | is_lossless dpub} as dpub_ll. *)

  (* Define set of all valid witness/statement pairs ?? *)
  (* axiom domain_R : forall x w, *)
  (*   R x w = true => x \in message. *)

lemma dchallenge_ll : is_lossless dchallenge by have []:= dchallenge_llfuni.
lemma dchallenge_funi : is_funiform dchallenge by have []:= dchallenge_llfuni.
lemma dchallenge_fu : is_full dchallenge by apply/funi_ll_full; [exact/dchallenge_funi|exact/dchallenge_ll].


  (* Sigma Protocol Algoritms *)
  module type SProtocol = {
    proc gen() : statement * witness
    proc init(h : statement, w : witness) : message * randomness
    proc response(h : statement, w : witness,
                  m : message, r : randomness, e : challenge) : response
    proc verify(h : statement, m : message, e : challenge, z : response) : bool
    proc witness_extractor(h : statement, m : message, e e' : challenge, z z' : response) : witness
    proc simulator(h : statement, e : challenge) : message * response
  }.

  module Completeness (S : SProtocol) = {
    proc special(h : statement, w : witness, e : challenge) : bool = {
      var a, r, z, v;

      (a, r) = S.init(h, w);
      z = S.response(h, w, a, r, e);
      v = S.verify(h, a, e, z);

      return v;
    }

    proc normal(h : statement, w : witness) : bool = {
      var a, r, e, z, v;

      (a, r) = S.init(h, w);
      e <$ dchallenge;
      z = S.response(h, w, a, r, e);
      v = S.verify(h, a, e, z);

      return v;
    }

    proc main(h : statement, w : witness) : bool = {
      var e, v;

      e <$ dchallenge;
      v = special(h, w, e);

      return v;
    }
  }.

  equiv normal_main (S <: SProtocol):
    Completeness(S).normal ~ Completeness(S).main : ={h, w, glob S} ==> ={res}.
  proof. proc. inline *. swap{1} 2 -1. sim. qed.

  lemma special_implies_main (S <: SProtocol) h' w':
    (forall h' w' e', phoare[Completeness(S).special : (h = h' /\ w = w' /\ e = e') ==> res] = 1%r) =>
    phoare[Completeness(S).main : (h = h' /\ w = w') ==> res] = 1%r.
  proof.
      move=> ph_special. proc.
      seq 1 : (#pre /\ exists e', e = e'). auto. auto. progress.
      apply dchallenge_ll. by exists v0.
      elim*. progress.
      call (ph_special h' w' e'). auto.
      hoare. auto. progress.
        - by exists e0.
        - progress.
  qed.

  module SpecialSoundness(S : SProtocol) = {
    proc main(h : statement, m : message, c c' : challenge, z z' : response) : bool = {
      var w, v, v';

      v  = S.verify(h, m, c, z);
      v' = S.verify(h, m, c', z');

      w = S.witness_extractor(h, m, c, c', z, z');

      return (c <> c' /\ (R h w) /\ v /\ v');
    }
  }.


  module SHVZK (S : SProtocol) = {
    proc real(h : statement, w : witness, e : challenge) : transcript option = {
      var a, r, z, v, ret;
      (a, r) = S.init(h, w);
      z = S.response(h, w, a, r, e);
      v = S.verify(h, a, e, z);
      ret = None;
      if (v) {
        ret = Some (a, e, z);
      } 
      return ret;
    }

    proc ideal(h : statement, e : challenge) : transcript option = {
      var a, z, v, ret;
      (a, z) = S.simulator(h, e);
      v = S.verify(h, a, e, z);
      ret = None;
      if (v) {
        ret = Some (a, e, z);
      }
      return ret;
    }
  }.

  lemma shvzk_real_never_fail (S <: SProtocol) h' w' e' &m:
      Pr[SHVZK(S).real(h', w', e') @ &m : (res <> None)] =
      Pr[Completeness(S).special(h', w', e') @ &m : res].
  proof. byequiv=>//. proc. wp. by do ? call (: true). qed.

section FiatShamir.
  require import SmtMap.
  (* Oracle idea from: Stoughton and Varia *)
  module Oracle = {
    var h : (message, challenge) fmap
    proc init() = {
      h = empty;
    }
    proc sample (m : message) : challenge = {
      if (m \notin h) {
        h.[m] <$ dchallenge;

      }
      return oget h.[m];
    }
  }.

  module FiatShamir(S : SProtocol) = {
    proc pok(h : statement, w : witness) : transcript = {
      var a, r, z, e;
      Oracle.init();
      (a, r) = S.init(h, w);
      e = Oracle.sample(a);
      z = S.response(h, w, a, r, e);

      return (a, e, z);
    }
  }.

  module FiatShamirCompleteness (S : SProtocol) = {
    module FS = FiatShamir(S)
    proc main(h : statement, w : witness) : bool = {
      var a, e, z, v;

      (a, e, z) = FS.pok(h, w);
      v         = S.verify(h, a, e, z);

      return v;
    }
  }.

  (* Proof of equivalence, if the underlying protocol is not allowed *)
  (* to alter the state of the Oracle. *)
  equiv fiat_shamir_completeness (S <: SProtocol{Oracle}):
      FiatShamirCompleteness(S).main ~ Completeness(S).main : ={h, w, glob S} ==> ={res}.
  proof.
    proc. inline *.
    sim. wp. swap{2} 1 2. swap{2} 5 -2. sp.
    seq 1 1 : (#pre /\ (a0{1} = a{2}) /\ ={r}). call (:true). auto. sp.
    rcondt{1} 1. progress. auto. progress. apply mem_empty.
    auto. progress. by rewrite get_setE.
  qed.

end section FiatShamir.

end SigmaProtocols.
