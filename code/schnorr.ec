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

  proc init(h : statement, w : witness) : message * randomness = {
    var r,a;
    r =$ FDistr.dt;
    a = g^r;
    return (a, r);
  }

  proc response(h : statement, w : witness, m : message, r : randomness, e : challenge) : response = {
    return r + e * w;
  }

  proc verify(h : statement, m : message, e : challenge, z : response) : bool = {
    return (g^z = m * (h ^e));
  }

  proc witness_extractor(h : statement, m : message, e e' : challenge, z z' : response) : witness= {
    return (z - z') / (e - e');
  }

  proc simulator(h : statement, e : challenge) = {
    var a, z;
    z =$ FDistr.dt;
    a = g ^ z * h ^ (-e);
    return (a, z);
  }

}.


(* Main Idea of the proof *)
(* after using proc. all calculation depend on the memory &m *)
(* If we want to use our knowledge of our relation, *)
(* then we need to rewrite before we start using the Hoare logic *)
section Security.
  lemma schnorr_completeness h' w' e' &m:
      R h' w' => Pr[Completeness(Schnorr).special(h', w', e') @ &m : res] = 1%r.
  proof.
  rewrite /R /R_DL=> rel.
  byphoare (_: w = w' /\ h = h' ==> _)=> />. rewrite rel.
  proc. inline *.
  auto=> &hr />.
  rewrite FDistr.dt_ll=> //= *.
  algebra. (* replaces:  by rewrite pow_pow mul_pow mulC. *)
  qed.

  print Schnorr.
  (* phoare[S1.SigmaProtocols.SHVZK(SP1).ideal : (h = h') ==> (res <> None)] = 1%z. *)

  lemma schnorr_special_soundness (x : statement) msg ch ch' d d' &m:
      ch <> ch' =>
      Pr[Schnorr.verify(x, msg, ch, d) @ &m : res] = 1%r =>
      Pr[Schnorr.verify(x, msg, ch', d') @ &m : res] = 1%r =>
      (* phoare[Schnorr.verify : (h = x /\ m = msg /\ e = ch' /\ z = d') ==> (res /\ g^d' = msg * (x ^ ch'))] = 1%r => *)
      Pr[SpecialSoundness(Schnorr).main(x, msg, ch, ch', d, d') @ &m : res] = 1%r.
  proof. move => c_diff accept_1_pr accept_2_pr.
  have accept_1: phoare[Schnorr.verify : (h = x /\ m = msg /\ e = ch /\ z = d) ==> (res /\ g^d = msg * (x ^ ch))] = 1%r.
  - bypr. progress. rewrite - accept_1_pr.
    byequiv=>//. proc. auto.

  have accept_2 : phoare[Schnorr.verify : (h = x /\ m = msg /\ e = ch' /\ z = d') ==> (res /\ g^d' = msg * (x ^ ch'))] = 1%r.
  - bypr. progress. rewrite - accept_2_pr.
    byequiv=>//. proc. auto.

  byphoare (: h = x /\ m = msg /\ c = ch /\ c' = ch' /\ z = d /\ z' = d' ==> _)=> //=.
  proc.
  swap [1..2] 1.
  inline Schnorr.witness_extractor.
  call accept_2.
  call accept_1.
  auto. progress.
  rewrite /R /R_DL.
  rewrite div_def -pow_pow sub_def -mul_pow pow_opp.
  rewrite H2 H0 inv_def.
  algebra.
  qed.

  lemma schnorr_shvzk h' w' e':
      (* NOTE: This implicitly implies that \exists w, (R h' w) in the real case *)
      equiv[SHVZK(Schnorr).ideal ~ SHVZK(Schnorr).real : (={h, e} /\ e{1} = e' /\ h{1} = h' /\ w{2} = w' /\ (R h' w')) ==> ={res}].
  proof.
  proc. sim. inline *. wp.
  rnd (fun z => z - e{2} * w') (fun r => r + e{2} * w'). auto.
  rewrite /R /R_DL. progress.
  - algebra.
  - apply FDistr.dt_funi.
  - apply FDistr.dt_fu.
  - algebra.
  - algebra.
  qed.

  lemma schnorr_shvzk_ideal_success h' e' &m:
      Pr[SHVZK(Schnorr).ideal(h', e') @ &m : (res <> None)] = 1%r.
  proof. byphoare(: h = h' ==> _)=>//. proc. inline *.
  auto. progress. apply dchallenge_ll. algebra. qed.

  (* lemma schnorr_secure: *)
  (*     schnorr_correctness /\ schnorr_special_soundness /\ schnorr_shvzk. *)

end section Security.

require ORProtocol.

clone import ORProtocol as OR with
  type ORProtocol.statement1 <- statement,
  type ORProtocol.statement2 <- statement,
  type ORProtocol.witness    <- witness,
  type ORProtocol.message1   <- message,
  type ORProtocol.message2   <- message,
  type ORProtocol.randomness <- randomness,
  type ORProtocol.challenge  <- challenge,
  type ORProtocol.response1  <- response,
  type ORProtocol.response2  <- response,

  op ORProtocol.R1 = R,
  op ORProtocol.R2 = R,

  op ORProtocol.dchallenge = dchallenge
  proof *.
  realize ORProtocol.dchallenge_llfuni. exact dchallenge_llfuni. qed.
  realize ORProtocol.xorK. admitted.
  realize ORProtocol.xorA. admitted.
export ORProtocol.

print OR.ORProtocol.ORProtocol.
print ORProtocol.Completeness.
print SigmaProtocols.Completeness.

lemma or_schnorr_schnorr_special_soundness x msg ch ch' e1 e1' z1 z1' e2 e2' z2 z2' &m:
      ch <> ch' =>
      ch = e1 ^^ e2 => (* We explicitly write out what it means for an OR conversation to be accepting *)
      ch' = e1' ^^ e2' =>
      phoare[Schnorr.verify : ( h = (fst x) /\ m = (fst msg) /\ e=  e1/\ z = z1) ==> res] = 1%r =>
      phoare[Schnorr.verify : ( h = (fst x) /\ m = (fst msg) /\ e=  e1'/\ z = z1') ==> res] = 1%r =>
      phoare[Schnorr.verify : ( h = (snd x) /\ m = (snd msg) /\ e=  e2 /\ z =z2) ==> res] = 1%r =>
      phoare[Schnorr.verify : ( h = (snd x) /\ m = (snd msg) /\ e=  e2'/\ z = z2') ==> res] = 1%r =>
      Pr[SigmaProtocols.SpecialSoundness(ORProtocol(Schnorr, Schnorr)).main(x, msg, ch, ch', (e1, z1, e2, z2), (e1', z1', e2', z2')) @ &m : res] = 1%r.
  proof.
  move=> ch_diff ch_rel ch'_rel.
    have Hss := (or_special_soundness Schnorr Schnorr _ _ _ _ _ _ _ _ x msg ch ch' e1 e1' z1 z1' e2 e2' z2 z2' &m ch_diff ch_rel ch'_rel).
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    progress.
    have Hpr1 : Pr[Schnorr.verify(x0, msg0, ch0, d) @ &m0 : res] = 1%r.
    byphoare H0=>//.
    have Hpr2 : Pr[Schnorr.verify(x0, msg0, ch'0, d') @ &m0 : res] = 1%r.
    byphoare H1=>//.
    have <- := (schnorr_special_soundness x0 msg0 ch0 ch'0 d d' &m0 H Hpr1 Hpr2).
    byequiv=>//. proc. inline *. auto.
    progress.
    have Hpr1 : Pr[Schnorr.verify(x0, msg0, ch0, d) @ &m0 : res] = 1%r.
    byphoare H0=>//.
    have Hpr2 : Pr[Schnorr.verify(x0, msg0, ch'0, d') @ &m0 : res] = 1%r.
    byphoare H1=>//.
    have <- := (schnorr_special_soundness x0 msg0 ch0 ch'0 d d' &m0 H Hpr1 Hpr2).
    byequiv=>//. proc. inline *. auto.
    move=> transcript_valid.
    apply (Hss transcript_valid).
  qed.


lemma or_schnorr_schnorr_completenes h' w' e' &m:
    (R1 (fst h') w') \/ (R2 (snd h') w') =>
    Pr[SigmaProtocols.Completeness(ORProtocol(Schnorr, Schnorr)).main(h', w', e') @ &m : res] = 1%r.
  proof.
    have H := (or_completeness Schnorr Schnorr _ _ _ _ h' w' &m); progress.
      - have <- := (schnorr_completeness h w &m0 H).
        byequiv=> //. proc. sim. rnd. call (: true). auto. progress.
      - have <- := (schnorr_completeness h w &m0 H).
        byequiv=> //. proc. sim. rnd. call (: true). auto. progress.
      - have <- := (schnorr_shvzk_ideal_success h'0 &m0).
        byequiv=>//. proc. sim. rnd. progress.
      - have <- := (schnorr_shvzk_ideal_success h'0 &m0).
        byequiv=>//. proc. sim. rnd. progress.
  qed.



  lemma schnorr_svhzk_ideal_success h' &m:

  have completeness_schnorr1 := (schnorr_completeness (fst h') w' &m).
  have completeness_schnorr2 := (schnorr_completeness (snd h') w' &m).
  case (R1 (fst h') w'). move=> rel.
  apply completeness_schnorr1 in rel.
  apply H.
