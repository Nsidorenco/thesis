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


op valid_key (key : secret_key * public_key) : bool.
(* make a predicate *)

module type Committer = {
  proc * key_gen() : secret_key * public_key
  proc commit(sk : secret_key, m : message) : commitment * randomness
}.

module type Verifier = {
  proc verify (pk : public_key, m : message, c : commitment, d : randomness): bool
}.


module Correctness(C : Committer, V : Verifier) = {
  proc main(m : message) : bool = {
    var sk, pk, c, d, b;
    (sk, pk) = C.key_gen();
    (c, d)   = C.commit(sk, m);
    b        = V.verify(pk, m, c, d);
    return b;
  }

  proc key_fixed(m : message, sk : secret_key, pk : public_key) : bool = {
    var c, d, b;
    (c, d)   = C.commit(sk, m);
    b        = V.verify(pk, m, c, d);
    return b;
  }

  proc intermediate(m : message) = {
    var sk, pk, b;
    (sk, pk) = C.key_gen();
    b = key_fixed(m, sk, pk);
    return b;

  }
}.

lemma intermediate (C <: Committer) (V <: Verifier{C}) m' &m:
    Pr[Correctness(C,V).main(m') @ &m : res] =
    Pr[Correctness(C,V).intermediate(m') @ &m : res].
proof.
  byequiv=>//. proc.
  inline *. sim.
qed.

lemma key_fixed_correct (C <: Committer) (V <: Verifier{C}) m'  &m:
    phoare[C.key_gen : true ==> valid_key res] = 1%r =>
    (phoare[Correctness(C,V).key_fixed : valid_key (sk, pk) ==> res] = 1%r)
    => Pr[Correctness(C,V).main(m') @ &m : res] = 1%r.
proof.
  move => key_gen_valid H.
  have -> := (intermediate C V m' &m).
  byphoare(: m = m' ==> )=>//.
  proc.
  call H.
  call key_gen_valid. skip; smt().
qed.



module type HidingAdv = {
  (* proc * means that this operation initializes the modules state *)
  proc * get() : message * message

  proc check(c : commitment) : bool

}.

module HidingGame(C : Committer, A : HidingAdv) = {
  proc main() = {
    var sk, pk, m0, m1, b, b', c, r;
    (sk, pk) = C.key_gen();
    (m0, m1) = A.get();
    b <$ DBool.dbool;
    if (b) {
      (c, r) = C.commit(sk, m0);
    } else {
      (c, r) = C.commit(sk, m1);
    }
    b' = A.check(c);
    return b = b';
  }
}.

module type BindingAdv = {
  proc bind(sk : secret_key, pk : public_key) : commitment * message * message * randomness * randomness
}.

module BindingGame(C : Committer, V : Verifier, B : BindingAdv) = {
  proc main() = {
  var sk, pk, c, m, m', r, r', v, v';
    (sk, pk) = C.key_gen();
    (c, m, m', r, r') = B.bind(sk, pk);
    v =  V.verify(pk, m, c, r);
    v' = V.verify(pk, m', c, r');
    return (v /\ v') /\ (m <> m');
  }
}.
