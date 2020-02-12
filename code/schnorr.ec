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
  realize SigmaProtocols.dchallenge_ll by apply FDistr.dt_ll.
export SigmaProtocols.


module Schnorr : Protocol = {
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

}.

module Helpers : Algorithms = {
  proc witness_extractor(s : statement, m : message, e : challenge,
                         r : response, e' : challenge, r' : response) : witness= {
    return (r - r') / (e - e');
  }

  proc simulator(s : statement, e : challenge) = {
    var a, z;
    z =$ FDistr.dt;
    a = g ^ z * s ^ (-e);
    return (a, e, z);
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

  lemma schnorr_special_soundness (h : statement) msg c c' z z' &m:
      c <> c' =>
      g^z = msg * (h ^ c) =>
      g^z' = msg * (h ^ c') =>
      Pr[Helpers.witness_extractor(h, msg, c, z, c', z') @ &m : (R h res)] = 1%r.
  proof. move=> e_diff accept_1 accept_2.
  (* Same trick again.  we need to introduce values earlier *)
  byphoare (_: s = h /\ m = msg /\ e = c /\ e' = c' /\ r = z /\ r' = z' ==> _)=> //.
  proc. inline *. auto.
  move=> &hr [Hs [Hm [He [He' [Hr Hr']]]]].
  rewrite /R /R_DL Hr Hr' He He'.
  rewrite F.div_def -pow_pow F.sub_def -mul_pow pow_opp log_bij.
  rewrite accept_1 accept_2.
  rewrite log_pow log_mul inv_def.
  field.
  - apply: contra e_diff=> ceq; ring ceq.
  - algebra.
  qed.

  lemma schnorr_shvzk:
      equiv[SHVZK(Schnorr, Helpers).ideal ~ SHVZK(Schnorr, Helpers).real : true ==> ={res}].
      proof.
      proc. inline *.
        seq 3 3 : (={h, w} /\ h{1} = g ^ w{1}). auto=> //=.
      (* sim / true : #pre. *)
        swap{1} 4 -2. swap{2} 3 -2. swap{2} 6 -5. wp.
        seq 1 1 : (#pre /\ ={e}). auto=> //=.
        rnd (fun z => z - e{2} * w{2}) (fun r => r + e{1} * w{1}). auto.
      move=> &1 &2 [[[heq weq] hrel] eeq]; progress; subst; try algebra.
      - apply FDistr.dt_funi.
      - apply FDistr.dt_fu.
      - apply: contra H4=> ?; algebra.
    qed.

  (* lemma schnorr_secure: *)
  (*     schnorr_correctness /\ schnorr_special_soundness /\ schnorr_shvzk. *)

end section Security.
