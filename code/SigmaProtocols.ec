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
    proc main(h : statement, w : witness) : bool = {
      var m, r, e, z, v;

      (m, r) = S.init(h, w);
      e      <$ dchallenge;
      z      = S.response(h, w, m, r, e);
      v      = S.verify(h, m, e, z);

      return v;
    }
  }.

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
    proc real(h : statement, w : witness) : transcript option = {
      var r, a, e, z, v, ret;
      (a, r) = S.init(h, w);
      e <$ dchallenge;
      z = S.response(h, w, a, r, e);
      v = S.verify(h, a, e, z);
      ret = None;
      if (v) {
        ret = Some (a, e, z);
      } 
      return ret;
    }

    proc ideal(h : statement) : transcript option = {
      var a, e, z, v, ret;
      e <$ dchallenge;
      (a, z) = S.simulator(h, e);
      v = S.verify(h, a, e, z);
      ret = None;
      if (v) {
        ret = Some (a, e, z);
      }
      return ret;
    }
  }.

  module SHVZKExperiment(S : SProtocol) = {
    module Game = SHVZK(S)

    proc real(h : statement, w : witness) = {
      var a, e, z, topt, v;
      topt = Game.real(h, w);
      if (topt = None) {
        v = false;
      } else {
        (a, e, z) = oget topt;
        v = S.verify(h, a, e, z);
      }
      return v;
    }

    proc ideal(h) = {
      var a, e, z, topt, v;
      topt = Game.ideal(h);
      if (topt = None) {
        v = false;
      } else {
        (a,e,z) = oget topt;
        v = S.verify(h, a, e, z);
      }
      return v;
    }

  }.

  lemma shvzk_real_never_fail (S <: SProtocol) h' w' &m:
      Pr[SHVZK(S).real(h', w') @ &m : (res <> None)] =
      Pr[Completeness(S).main(h', w') @ &m : res].
  proof. byequiv=>//. proc. wp. do ? call (: true). rnd. by call (: true). qed.

end SigmaProtocols.
