(* Concrete instantiation of a Sigma Protocol *)
require import Int.
require import Real.
require import Distr.
require import CyclicGroup.

require SigmaProtocols.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

theory Types.
  type statement  = group.
  type witness    = F.t.
  type message    = group.
  type randomness = F.t.
  type challenge  = F.t.
  type response   = F.t.

  op R_DL h w     = (h = g^w).
end Types.
export Types.

clone import SigmaProtocols as Sigma with
  type SigmaProtocols.statement <- statement,
  type SigmaProtocols.witness <- witness,
  type SigmaProtocols.message <- message,
  type SigmaProtocols.randomness <- randomness,
  type SigmaProtocols.challenge <- challenge,
  type SigmaProtocols.response <- response,

  op SigmaProtocols.R = R_DL,
  op SigmaProtocols.dchallenge = FDistr.dt
  proof *.
  realize SigmaProtocols.dchallenge_llfuni.
      split. apply FDistr.dt_ll. apply FDistr.dt_funi. qed.
export SigmaProtocols.


module Schnorr : SProtocol = {
  proc gen() : statement * witness = {
    var w, h;
    w =$ FDistr.dt;
    h = g ^ w;
    return (h, w);
  }

  proc init(s : statement, w : witness) : message * randomness = {
    var r,a;
    r =$ FDistr.dt;
    a = g^r;
    return (a, r);
  }

  proc response(s : statement, w : witness, m : message, r : randomness, e : challenge) : response = {
    return r + e * w;
  }

  proc verify(s : statement, m : message, e : challenge, r : response) : bool = {
    var v,v';

    v  = g ^ r;
    v' = m * (s ^ e);

    return (v = v');
  }

  proc witness_extractor(s : statement, m : message, e e' : challenge, r r' : response) : witness= {
    return (r - r') / (e - e');
  }

  proc simulator(s : statement, e : challenge) = {
    var a, z;
    z =$ FDistr.dt;
    a = g ^ z * s ^ (-e);
    return (a, z);
  }

}.


(* Main Idea of the proof *)
(* after using proc. all calculation depend on the memory &m *)
(* If we want to use our knowledge of our relation, *)
(* then we need to rewrite before we start using the Hoare logic *)
section Security.
  lemma schnorr_correctness h' w' &m:
      R h' w' => Pr[Completeness(Schnorr).main(h', w') @ &m : res] = 1%r.
  proof.
  rewrite /R /R_DL=> rel.
  byphoare (_: w = w' /\ h = h' ==> _)=> />. rewrite rel.
  proc. inline *.
  auto=> &hr />.
  rewrite FDistr.dt_ll=> //= *.
  algebra. (* replaces:  by rewrite pow_pow mul_pow mulC. *)
  qed.

  lemma schnorr_special_soundness (x : statement) msg e e' r r' &m:
      e <> e' =>
      g^r = msg * (x ^ e) =>
      g^r' = msg * (x ^ e') =>
      Pr[SpecialSoundness(Schnorr).main(x, msg, e, e', r, r') @ &m : res] = 1%r.
  proof. move => c_diff accept_1 accept_2.
  byphoare (: h = x /\ m = msg /\ c = e /\ c' = e' /\ z = r /\ z' = r' ==> _)=> //=.
  proc. inline *; auto; progress.
  rewrite /R /R_DL.
  rewrite div_def -pow_pow sub_def -mul_pow pow_opp.
  rewrite accept_1 accept_2 inv_def.
  algebra.
  qed.

  lemma schnorr_shvzk h' w':
      (* NOTE: This implicitly implies that \exists w, (R h' w) in the real case *)
      equiv[SHVZK(Schnorr).ideal ~ SHVZK(Schnorr).real : (={h} /\ h{1} = h' /\ w{2} = w' /\ (R h' w')) ==> ={res}].
  proof.
  proc. inline *. sp.
  swap{2} 4 -3.
  seq 1 1 : (#pre /\ ={e}). auto=> //=.
  wp. sp.
  rnd (fun z => z - e{2} * w') (fun r => r + e{2} * w').
  rewrite /R /R_DL.
  auto; progress; subst; try algebra.
  - apply FDistr.dt_funi.
  - apply FDistr.dt_fu.
  - apply: contra H4=> ?; algebra.
  qed.

  (* lemma schnorr_secure: *)
  (*     schnorr_correctness /\ schnorr_special_soundness /\ schnorr_shvzk. *)

end section Security.
