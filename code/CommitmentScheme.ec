(* Formalization of Commitment schemes *)
require import AllCore Distr DBool.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

theory CommitmentScheme.
  type public_key.
  type secret_key.
  type commitment.
  type message.
  type randomness.

  op dm : {message distr | is_lossless dm} as dm_ll.
  op dr : {randomness distr | is_lossless dr} as dr_ll.

  module type Protocol = {
    proc key_gen() : secret_key * public_key
    proc commit(sk : secret_key, m : message) : commitment * randomness
    proc verify(pk : public_key, m : message, c : commitment, d : randomness) : bool
  }.

  module Correctness(P : Protocol) = {
    proc main(m : message) : bool = {
      var sk, pk, c, d, b;
      (sk, pk) = P.key_gen();
      (c, d)   = P.commit(sk, m);
      b        = P.verify(pk, m, c, d);
      return b;
    }
  }.

  module type HidingAdv = {
    (* proc * means that this operation initializes the modules state *)
    proc * get() : message * message

    proc check(c : commitment) : bool

  }.

  module HidingGame(P : Protocol, A : HidingAdv) = {
    proc main() = {
      var sk, pk, m0, m1, b, b', c, r;
      (sk, pk) = P.key_gen();
      (m0, m1) = A.get();
      b <$ DBool.dbool;
      if (b) {
        (c, r) = P.commit(sk, m0);
      } else {
        (c, r) = P.commit(sk, m1);
      }
      b' = A.check(c);
      return b = b';
    }
  }.

  module type BindingAdv = {
    proc bind(sk : secret_key, pk : public_key) : commitment * message * message * randomness * randomness
  }.

  module BindingGame(P : Protocol, B : BindingAdv) = {
    proc main() = {
    var sk, pk, c, m, m', r, r', v, v';
      (sk, pk) = P.key_gen();
      (c, m, m', r, r') = B.bind(sk, pk);
      v = P.verify(pk, m, c, r);
      v' = P.verify(pk, m', c, r');
      return (v /\ v') /\ (m <> m');
    }
  }.

end CommitmentScheme.
