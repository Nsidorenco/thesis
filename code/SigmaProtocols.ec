(* Formalization of Sigma Protocols *)
require import AllCore Distr.
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

  op dchallenge : {challenge distr | is_lossless dchallenge} as dchallenge_ll.
  (* op dpub : {statement distr | is_lossless dpub} as dpub_ll. *)

  (* Define set of all valid witness/statement pairs ?? *)
  (* axiom domain_R : forall x w, *)
  (*   R x w = true => x \in message. *)


  (* Sigma Protocol Algoritms *)
  module type Protocol = {
    proc gen() : statement * witness
    proc init(h : statement, w : witness) : message * randomness
    proc response(h : statement, w : witness,
                  m : message, r : randomness, e : challenge) : response
    proc verify(h : statement, m : message, e : challenge, z : response) : bool
  }.

  module type Algorithms = {
    proc witness_extractor(h : statement, m : message,
                           e : challenge, z : response,
                           e' : challenge, z' : response) : witness
    proc simulator(h : statement, e : challenge) : transcript
  }.

  module Completeness (S : Protocol) = {
    proc main(h : statement, w : witness) : bool = {
      var m, r, e, z, b;

      (m, r) = S.init(h, w);
      e      <$ dchallenge;
      z      = S.response(h, w, m, r, e);
      b      = S.verify(h, m, e, z);

      return b;
    }
  }.

  module SHVZK (S : Protocol, A : Algorithms) = {
    proc real() : transcript option = {
      var h, r, w, a, e, z, b, ret;
      (h, w) = S.gen();
      (a, r) = S.init(h, w);
      e <$ dchallenge;
      z = S.response(h, w, a, r, e);
      b = S.verify(h, a, e, z);
      if (b) {
        ret = Some (a, e, z);
      } else {
        ret = None;
      }
      return ret;
    }

    proc ideal() : transcript option = {
      var w, a, e, z, h, b, ret;
      (h, w) = S.gen();
      e <$ dchallenge;
      (a, e', z) = A.simulator(h, e);
      b = S.verify(h, a, e, z);
      if (b) {
        ret = Some (a, e, z);
      } else {
        ret = None;
      }
      if (e' <> e) {
        ret = None;
      }
      return ret;
    }
  }.

  (* section OR_protocol. *)


  (* module ORProtocol (S : SigmaProtocol.Protocol) : SigmaProtocol.Protocol = { *)
  (*     proc init(x1 : SigmaProtocol.statement, w : SigmaProtocol.witness) = { *)
  (*       var x2, m, r; *)
  (*       x2 <$ dpub; *)
  (*       (m, r) = S.init(x1, w); *)
  (*       return (m, r); *)
  (*     } *)
  (*     proc response(h : SigmaProtocol.statement, w : SigmaProtocol.witness, m : SigmaProtocol.message, r : SigmaProtocol.randomness, e : SigmaProtocol.challenge) = { *)
  (*       var z; *)
  (*       z = S.response(h, w, m, r, e); *)
  (*       return z; *)
  (*     } *)
  (*     proc verify(h : SigmaProtocol.statement, m : SigmaProtocol.message, e : SigmaProtocol.challenge, z : SigmaProtocol.response) = { *)
  (*       var b; *)
  (*       b = S.verify(h, m, e, z); *)
  (*       return b; *)
  (*     } *)
  (* }. *)

  (* lemma or_completeness : forall (S <: SigmaProtocol.Protocol), *)
  (*   hoare[SigmaProtocol.Completeness(S).main : true ==> res] => *)
  (*   hoare[SigmaProtocol.Completeness(ORProtocol(S)).main : true ==> res]. *)
  (*     proof. admitted. *)
  (* end section OR_protocol. *)

end SigmaProtocols.
