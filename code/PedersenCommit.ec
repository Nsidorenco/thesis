(* Concrete instantiation of a Commitment scheme *)
require import Int.
require import Real.
require import Distr.
require import CyclicGroup.

require Commitment.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

theory Types.
  type public_key  = group.
  type secret_key  = public_key.
  type commitment  = group.
  type message     = F.t.
  type randomness  = F.t.
end Types.
export Types.

clone export Commitment as Com with
  type public_key <- Types.public_key,
  type secret_key <- Types.secret_key,
  type commitment <- Types.commitment,
  type message    <- Types.message,
  type randomness <- Types.randomness,


  op dm = FDistr.dt,
  op dr = FDistr.dt,
  op verify pk (m : message) c (r : randomness) = g^r * pk^m = c,
  op valid_key (sk : secret_key) (pk : public_key) = (sk = pk).



module Pedersen : Committer = {
  proc key_gen() : secret_key * public_key = {
    var a, h;
    a <$ dr;
    h = g ^ a;

    return (h, h);
  }

  proc commit(sk : secret_key, m : message) : commitment * randomness = {
    var r, c;
    r <$ dr;
    c = g^r * (sk^m);

    return (c, r);
  }
}.

section DLog.

  module type Adversary = {
    proc guess(h : group) : F.t option
  }.

  module DLogGame(A : Adversary) = {
    proc main() = {
      var a, a', ret;

      a <$ FDistr.dt;
      a' = A.guess(g^a);

      if (a' = None) {
        ret = false;
      } else {
        ret = (Some a = a');
      }

      return ret;
    }
  }.
end section DLog.

section Security.

  lemma pedersen_correctness mes &m:
      Pr[Correctness(Pedersen).main(mes) @ &m : res] = 1%r.
  proof. byphoare=> //=.
  proc. inline *.
  by auto; rewrite dr_ll.
  qed.

  module HidingIdeal(A : HidingAdv) = {
    proc main() = {
      var sk, pk, m0, m1, b, b', c, r;
      (sk, pk) = Pedersen.key_gen();
      (m0, m1) = A.get();
      b <$ DBool.dbool;
      r <$ dr;
      c = g ^ r;
      b' = A.check(c);
      return b = b';
    }
  }.

  lemma pedersen_ideal_perfect_hiding (A <: HidingAdv) &m:
      islossless A.get =>
      islossless A.check =>
      Pr[HidingIdeal(A).main() @ &m : res] = 1%r/2%r.
  proof. move=> get_ll check_ll. byphoare=> //=.
  proc. inline *. swap 4 3. swap 4 4. rnd.
  call check_ll. call get_ll. auto; progress.
  - apply dr_ll.
  - rewrite DBool.dboolE. case result=> //=.
  qed.

  lemma pedersen_hiding_real_ideal (A <: HidingAdv) &m:
      Pr[HidingGame(Pedersen, A).main() @ &m : res] =
      Pr[HidingIdeal(A).main() @ &m : res].
  proof. byequiv=> //=. proc. inline *.
    seq 4 4 : (={a, pk, sk, m0, m1, glob A} /\ sk{1} = g ^ a{1}).
    call (: true). wp. rnd. skip. progress.
  seq 1 1 : (#pre /\ ={b}). auto.
  if{1}; sim; wp.
  rnd (fun r => r + a{2} * m0{2}) (fun r => r - a{2} * m0{2}).
  auto. progress.
  - algebra.
  - rewrite /dr. apply FDistr.dt_funi. apply FDistr.dt_fu.
  - algebra.
  - algebra.

  rnd (fun r => r + a{2} * m1{2}) (fun r => r - a{2} * m1{2}).
  auto. progress.
  - algebra.
  - rewrite /dr. apply FDistr.dt_funi. apply FDistr.dt_fu.
  - algebra.
  - algebra.
  qed.

  lemma pedersen_perfect_hiding (A <: HidingAdv) &m:
      islossless A.get =>
      islossless A.check =>
      Pr[HidingGame(Pedersen, A).main() @ &m : res] = 1%r/2%r.
  proof.
  rewrite (pedersen_hiding_real_ideal A &m).
  apply (pedersen_ideal_perfect_hiding A &m).
  qed.

  module DLogPedersen(B : BindingAdv) : Adversary = {
    proc guess(h : group) = {
      var w, c, m, m', r, r', v, v';
      (c, m, m', r, r') = B.bind(h, h);
      v = verify h m c r;
      v' = verify h m' c r';
      if ((v /\ v') /\ (m <> m')) {
        w = Some( (r - r') * inv(m' - m) );
      } else {
        w = None;
      }
      return w;
    }
  }.

  lemma special_soundness m m' c r r' a:
      m <> m' =>
      c = g^r * (g^a)^m /\ c = g^r' * (g^a)^m' =>
      a = (r - r') * inv(m' - m).
  proof. progress.
  rewrite !pow_pow !mul_pow -pow_bij in H0.
  field.
  - apply: contra H=> meq; ring meq. (* NOTE: apply: contra is not documented at all? *)
  - ring H0.
  qed.

  lemma pedersen_comp_binding (B <: BindingAdv) &m:
      Pr[BindingGame(Pedersen, B).main() @ &m : res] =
      Pr[DLogGame(DLogPedersen(B)).main() @ &m : res].
  proof. byequiv (: (={glob B}) ==> _)=>  //=.
  proc. inline *.
  seq 1 1 : (={a} /\ #pre); auto.
  - call (: true); auto; smt(special_soundness).
  qed.
