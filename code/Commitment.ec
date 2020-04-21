(* Formalization of Commitment schemes *)
require import AllCore Distr DBool.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

type public_key.
type secret_key.
type commitment.
type message.
type randomness.

op dm : {message distr | is_lossless dm} as dm_ll.
op dr : {randomness distr | is_lossless dr} as dr_ll.
op dkey : {(secret_key * public_key) distr | is_lossless dkey} as dkey_ll.

op verify (pk : public_key, m : message, c : commitment, d : randomness): bool.

module type Protocol = {
  (* proc * key_gen() : secret_key * public_key *)
  proc commit(sk : secret_key, m : message) : commitment * randomness
}.

module Correctness(P : Protocol) = {
  proc main(m : message) : bool = {
    var sk, pk, c, d, b;
    (sk, pk) <$ dkey;
    (c, d)   = P.commit(sk, m);
    b = verify pk m c d;
    return b;
  }

  proc key_fixed(m : message, sk : secret_key, pk : public_key) : bool = {
    var c, d, b;
    (c, d)   = P.commit(sk, m);
    b = verify pk m c d;
    return b;
  }

  proc intermediate(m : message) = {
    var sk, pk, b;
    (sk, pk) <$ dkey;
    b = key_fixed(m, sk, pk);
    return b;

  }
}.

lemma intermediate (Com <: Protocol) m' &m:
    Pr[Correctness(Com).main(m') @ &m : res] =
    Pr[Correctness(Com).intermediate(m') @ &m : res].
proof.
  byequiv=>//. proc.
  inline *. sim.
qed.

lemma key_fixed_correct (Com <: Protocol) m' &m:
    (forall sk' pk', phoare[Correctness(Com).key_fixed : sk = sk' /\ pk = pk' /\ (sk', pk') \in dkey ==> res] = 1%r)
    => Pr[Correctness(Com).main(m') @ &m : res] = 1%r.
proof.
  move => H.
  have -> := (intermediate Com m' &m).
  byphoare(: m = m' ==> )=>//.
  proc.
  seq 1 : (#pre /\ exists sk' pk', sk = sk' /\ pk = pk' /\ (sk', pk') \in dkey).
  auto. auto. progress.
  apply dkey_ll.
  smt().
  elim * => sk' pk'.
  have H' := H sk' pk'.
  call H'.
  skip; progress.
  hoare.
  auto. progress. smt().
  progress.
qed.



module type HidingAdv = {
  (* proc * means that this operation initializes the modules state *)
  proc * get() : message * message

  proc check(c : commitment) : bool

}.

module HidingGame(P : Protocol, A : HidingAdv) = {
  proc main() = {
    var sk, pk, m0, m1, b, b', c, r;
    (sk, pk) <$ dkey;
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
    (sk, pk) <$ dkey;
    (c, m, m', r, r') = B.bind(sk, pk);
    v = verify pk m c r;
    v' = verify pk m' c r';
    return (v /\ v') /\ (m <> m');
  }
}.
