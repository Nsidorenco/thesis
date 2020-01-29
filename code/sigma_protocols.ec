(* Formalization of Sigma Protocols *)
require import AllCore Distr.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

theory SigmaProtocol.
  type public_input.
  type witness.
  type message.
  type randomness.
  type challenge.
  type response.

  (* define the relations *)
  op R (x : public_input) (w : witness) : bool.

  op dchallenge : {challenge distr | is_lossless dchallenge} as dchallenge_ll.
  op dpub : {public_input distr | is_lossless dpub} as dpub_ll.

  (* Define set of all valid witness/statement pairs ?? *)
  axiom domain_R : forall x w,
    R x w = true => x \in dpub.


  (* Sigma Protocol Algoritms *)
  module type Protocol = {
    proc init(h : public_input, w : witness) : message * randomness
    proc response(h : public_input, w : witness,
                  m : message, r : randomness, e : challenge) : response
    proc verify(h : public_input, m : message, e : challenge, z : response) : bool
  }.

  module type Algorithms = {
    proc special_soundness(h : public_input, m : message,
                           e : challenge, z : response,
                           e' : challenge, z' : response) : witness
    proc simulator(h : public_input, e : challenge) : message * challenge * response
  }.

  module Completeness (S : Protocol) = {
    proc main(h : public_input, w : witness) : bool = {
      var m, r, e, z, b;

      (m, r) = S.init(h, w);
      e      <$ dchallenge;
      z      = S.response(h, w, m, r, e);
      b      = S.verify(h, m, e, z);

      return b;
    }
  }.

  section OR_protocol.

  module ORProtocol (S : SigmaProtocol.Protocol) : SigmaProtocol.Protocol = {
      proc init(x1 : SigmaProtocol.public_input, w : SigmaProtocol.witness) = {
        var x2, m, r;
        x2 <$ dpub;
        (m, r) = S.init(x1, w);
        return (m, r);
      }
      proc response(h : SigmaProtocol.public_input, w : SigmaProtocol.witness, m : SigmaProtocol.message, r : SigmaProtocol.randomness, e : SigmaProtocol.challenge) = {
        var z;
        z = S.response(h, w, m, r, e);
        return z;
      }
      proc verify(h : SigmaProtocol.public_input, m : SigmaProtocol.message, e : SigmaProtocol.challenge, z : SigmaProtocol.response) = {
        var b;
        b = S.verify(h, m, e, z);
        return b;
      }
  }.

  lemma or_completeness : forall (S <: SigmaProtocol.Protocol),
    hoare[SigmaProtocol.Completeness(S).main : true ==> res] =>
    hoare[SigmaProtocol.Completeness(ORProtocol(S)).main : true ==> res].
      proof.
      move => S CompS. proc => //.
        inline ORProtocol(S).init.
        sp. call (_: true); auto.
        - call (_ : true); auto.
        * call (_ : true); auto.
        + call (_ : true); auto.
      move => *.

  end section.

end SigmaProtocol.
