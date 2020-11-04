(* Formalization of ZKBoo Sigma-protocol *)
require import AllCore Distr List DInterval DList DBool.
require (****) SigmaProtocols MPC.
require import IdealCommitment.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

clone import MPC as D.

clone import IdealCommitment as Commit with
  type message <- view .

type statement  = (circuit * output).
type witness    = input.
type message    = share list * Commit.commitment list.
type challenge  = int.
type response   = verification_input.
op dchallenge = [1..3].

axiom challenge_size (c : challenge) : 0 < c <= 3.

op R (h : statement) (w : witness)     = let (c, y) = h in (y = circuit_eval c w).

clone export SigmaProtocols as Sigma with
  type statement <- statement,
  type witness <- witness,
  type message <- message,
  type challenge <- challenge,
  type response <- response,

  op R <- R,
  op dchallenge <- dchallenge
  proof *.
  realize dchallenge_llfuni.
      (* TODO: by [dt_ll, dt_funi] *)
      split. apply dinter_ll. trivial. apply is_full_funiform.
      rewrite /is_full.
      progress.
      case (0 < x <= 3).
      smt.
      move=> H.
      have : 0 < x <= 3. apply challenge_size.
      smt().
      apply dinter_uni.
  qed.

module ZKBoo(C : Committer, D : Phi) : SProtocol = {
  var ws : view list

  proc init(h : statement, w : witness) = {
    var y,c,ks,cs,ys,i,ctmp,ytmp;
    (c, y) <- h;
    ks <- D.sample_tapes(size c);
    ws <- D.decomp(c, w, ks);
    cs <- [];
    ys <- [];
    i <- 0;
    while (i < size ws) {
      ctmp <- C.commit(nth witness ws i);
      ytmp <- output(nth witness ws i);
      cs <- rcons cs ctmp;
      ys <- rcons ys ytmp;
      i <- i + 1;
    }
    return (ys, cs);
  }

  proc response(h : statement, w : witness, m : message, e : challenge) = {
    return f ws e;
  }

  proc verify(h : statement, m : message, e : challenge, z : response) = {
    var ws, i, view, com, ys, cs, c, y, valid_com, valid;
    (c, y) <- h;
    (ys, cs) <- m;
    ws <- f_inv z;
    i <- 0;
    valid_com <- true;
    while (i < size ws) {
      view <- nth witness ws i;
      com <- nth witness cs (e+i);
      valid_com <- valid_com /\ (verify view com);
      i <- i + 1;
    }
    valid <- D.verify(c, z, e, y);

    return valid_com /\ valid;

  }

  proc witness_extractor(h : statement, a : message,
                         e : challenge list, z : response list) = {
    var w;
    w <- D.extractor(z);
    return w;
  }

  proc simulator(h : statement, e : challenge) = {
    var c, y, yn, vs, ys, cs, vs', ctmp, ytmp, i, a;
    (c, y) <- h;
    (vs, yn, vs') <- D.simulator(c, y, e);
    cs <- [];
    ys <- [];
    i <- 0;
    while (i < size vs) {
      ctmp <- C.commit(nth witness vs i);
      ytmp <- output(nth witness vs i);
      cs <- rcons cs ctmp;
      ys <- rcons ys ytmp;
    }
    a <- (ys, cs);

    return (a, vs');
  }

}.

section Protocol.

declare module Decomp : D.Phi{ZKBoo}.
declare module Com : Commit.Committer{ZKBoo, Decomp}.

(* Assume security of Com *)
(* axiom Com_correct &m a : Pr[Correctness(Com).main(a) @ &m : res] = 1%r. *)
const binding_prob : real.

axiom Com_correct :
    phoare[Correctness(Com).main : true ==> res] = 1%r.
axiom Com_hiding_alt :
  equiv[Com.commit ~ Com.commit : ={glob Com} ==> ={res, glob Com}].
axiom Com_binding_pr c m1 m2 &m:
  Pr[BindingGame(Com).main(c, m1, m2) @ &m : ! res] = binding_prob.
lemma Com_binding :
  phoare[BindingGame(Com).main : true ==> ! res] = binding_prob by bypr=> &m H; smt(Com_binding_pr).
axiom Com_ll: islossless Com.commit.

axiom bind_three_equiv c1 c2 c3 a1 a1' a2 a2' a3 a3' &m:
    Pr[BindingGame(Com).bind_three(c1, c2, c3, a1, a1', a2, a2', a3, a3') @ &m : ! res] = binding_prob.


local module Com_Inter = {
  var ws : view list
  var ws' : view list
  var cs : commitment list

  proc decomposition(c, w, e, y) = {
    var ks, z, valid;
    ks <- Decomp.sample_tapes(size c);
    ws <- Decomp.decomp(c, w, ks);

    z <-  f ws e;
    ws' <- f_inv z;

    valid <- Decomp.verify(c, z, e, y);
    return valid;
  }

  proc com(ws) = {
    var ys, i, ctmp, ytmp;
    ys <- [];
    i <- 0;
    while (i < size ws) {
      ctmp <- Com.commit(nth witness ws i);
      ytmp <- output(nth witness ws i);
      cs <- rcons cs ctmp;
      ys <- rcons ys ytmp;
      i <- i + 1;
    }
  }

  proc ver(ws' e) = {
    var valid_com, i, view, c;
    valid_com <- true;
    i <- 0;
    while (i < size ws') {
      view <- nth witness ws' i;
      c <- nth witness cs (e+i);
      valid_com <- valid_com /\ (verify view c);
      i <- i + 1;
    }
    return valid_com;
  }

  proc commitment(ws : view list, e : challenge) = {
    var z, ws', v;
    com(ws);
    z <-  f ws e;
    ws' <- f_inv z;
    v <- ver(ws', e);
    return v;
  }

  proc commitment_stepped(w, l, e) = {
    var v; 
    var valid_com, view, c;
    var ctmp, ytmp, z, ws';
    ctmp <- Com.commit(w);
    ytmp <- output(w);
    cs <- [ctmp];

    z <-  f (rcons l w) e;
    ws' <- f_inv z;

    valid_com <- true;
    if (f_inv (f (rcons l w) e) <> f_inv (f l e)) {
      view <- last witness ws';
      c <- nth_looping cs (e + (size l));
      valid_com <- valid_com /\ (verify view c);
    }

    v <- commitment(l, e);
    return v /\ valid_com;
  }

  proc main(h : statement, w : witness, e : challenge) = {
    var valid_com, valid, c, y;
    (c, y) <- h;
    cs <- [];
    valid <- decomposition(c, w, e, y);
    valid_com <- commitment(ws, e);
    return valid_com /\ valid;
  }
}.

lemma in_dom (a b x : int):
    a < b /\ b < x =>
    x \notin [a..b].
proof.
  progress. smt.
qed.

local equiv com_inter:
  Com_Inter.main ~ Completeness(ZKBoo(Com, Decomp)).special : ={h, w, e, glob Decomp, glob Com} ==> ={res}.
proof.
  proc.
  inline ZKBoo(Com, Decomp).init ZKBoo(Com, Decomp).response ZKBoo(Com, Decomp).verify.
  inline Com_Inter.decomposition Com_Inter.commitment Com_Inter.com Com_Inter.ver.
  auto.
  swap{2} 26 -5.
  auto.
  swap{2} 10 2.
  swap{2} [12..13] 3.
  swap{2} [15..17] 4.
  swap{2} [12..18] -5.
  auto.
  sim.
  auto.
  while (ZKBoo.ws{2} = ws0{1} /\ Com_Inter.cs{1} = cs{2} /\ ={i, ys, glob Com}). auto.
  call (:true). auto. 
  auto.
  call (:true); auto.
  call (:true).
  call (:true).
  auto.
qed.

local lemma commitment_correct:
    phoare[Com_Inter.commitment : e \in dchallenge ==> res] = 1%r.
proof.
  (* bypr=> &m' e_dom. *)
  (* byphoare(:e \in dchallenge==>)=>//. *)
  exists* ws; elim*=>ws.
  elim ws; progress.
  proc.
  (* Base Case*)
  inline Com_Inter.com Com_Inter.ver.
  wp. rcondf 4. auto.
      rcondf 10. auto. progress. smt(f_inv_size).
      auto.
  (* (* while (valid_com = true /\ ws'0 = [] /\ size Com_Inter.cs = min (size ws) d /\ 0 <= i0) (0). *) *)
  (* auto. progress. smt(). *)
  (* auto. rcondf 4; auto.  *)
  (* progress; smt(d_pos f_inv_correct f_inv_size size_eq0). *)
  (* Inductive Case *)
  bypr=> &m [ws_rel e_dom].
  have -> : Pr[Com_Inter.commitment(ws{m}, e{m}) @ &m : res] = 
            Pr[Com_Inter.commitment_stepped(x, l, e{m}) @ &m : res].
  - byequiv=>//.
    proc.
    inline Com_Inter.commitment Com_Inter.com Com_Inter.ver.
    auto.
    splitwhile{1} 5 : (i < size ws0 - 1).
    swap{2} 17 -9.
    rcondt{1} 6; auto.
    - while (i < size ws0); auto.
      call (:true); skip.
      progress. smt().
      progress. smt(size_rcons size_ge0).
    rcondf{1} 11; auto.
    - call (:true).
      while (i < size ws0); auto.
      call (:true); skip.
      progress. smt().
      progress; smt(size_rcons size_ge0).
    (* splitwhile{1} 13 : (i0 < e + d). *)
    (* splitwhile{1} 14 : (i0 < e + d + 1). *)
    case (f_inv (f (rcons s x) e{1}) = f_inv (f s e{1})).
    while (ws'0{1} = ws'1{2} /\ ={i0} /\ valid_com{1} = valid_com0{2}).
    - auto. progress. admit.
    auto. 
    call (:true).
    while (={i, Com_Inter.cs, glob Com} /\ ws0{1} = rcons ws0{2} x /\ i{1} < size ws0{1}).
    - auto.
      call (:true); auto.
      smt(nth_rcons size_rcons size_ge0).
    auto. smt(nth_rcons size_rcons size_ge0).
    splitwhile{1} 17 : (i0 < size ws'0 - 1).
    rcondt{1} 18. auto.
    - while (i0 < size ws'0); auto. progress. smt().
      call (:true).
      while (i < size ws0 /\ size Com_Inter.cs = i); auto. call(:true). auto.
      + progress. smt(size_rcons size_ge0).
        smt(size_rcons size_ge0).
      smt(size_rcons size_ge0 f_inv_size).
    rcondf{1} 22; auto.
    - while (i0 < size ws'0); auto. progress. smt().
      call (:true).
      while (i < size ws0 /\ size Com_Inter.cs = i); auto. call(:true). auto.
      + progress. smt(size_rcons size_ge0).
        smt(size_rcons size_ge0).
      smt(size_rcons size_ge0 f_inv_size).
    while (={i0} /\ ws'0{1} = rcons ws'1{2} x /\ valid_com{1} = valid_com0{2} /\ Com_Inter.cs{1} = rcons Com_Inter.cs{2} ctmp{2}).
    - auto. progress.
      + congr. congr. smt(nth_rcons).
      + admit.
      + smt(size_rcons size_ge0).
      + smt(size_rcons size_ge0).
      + smt(size_rcons size_ge0).
    auto.
    call (:true).
    while (={i, Com_Inter.cs, glob Com} /\ ws0{1} = rcons ws0{2} x /\ i{1} < size ws0{1}).
    - auto.
      call (:true); auto.
      smt(nth_rcons size_rcons size_ge0).
    auto. progress.
    smt(size_rcons size_ge0 f_inv_size).
    smt(size_rcons size_ge0 f_inv_size).
    smt(size_rcons size_ge0 f_inv_size).
    smt(size_rcons size_ge0 f_inv_size).
    smt(size_rcons size_ge0 f_inv_size).
    smt.
    admit.
    smt(size_rcons size_ge0 f_inv_size).
    smt(size_rcons size_ge0 f_inv_size).
    admit.
    admit.
    smt(size_rcons size_ge0 f_inv_size).

    byphoare(: w = x /\ l = s /\ e = e{m} ==> )=>//.
    proc.
    auto. call (:true). admit.
    call H. auto.
    progress.
    admit.
    
axiom Decomp_verifiability :
  phoare[Verifiability(Decomp).main : true ==> res] = 1%r.

lemma completeness:
    phoare[Completeness(ZKBoo(Com,Decomp)).special : R h w ==> res] = 1%r.
proof.
  proc.
  inline Completeness(ZKBoo(Com, Decomp)).special.
  inline ZKBoo(Com, Decomp).init ZKBoo(Com, Decomp).response ZKBoo(Com, Decomp).verify.
  sp; auto.
  swap 23 -5.
  swap [6..10] 3.
  swap [15..17] -6.
  swap 16 -2.
  swap 17 -2.
  swap 18 -6.
  (* Apply commitment game *)
  (* Need intermediate that contains both while loops *)
  (* Prove with induction on list of views that commit correctness => global correctness *)

  
  

local module Intermediate = {
  module ComCorrectness = Correctness(Com)
  module DecompVer = Verifiability(Decomp)

  proc main(h : statement, w : witness, e : challenge) = {
    var c, y, ver;
    (c, y) <- h;
    (* Steps: *)
    (* Decomposition game *)
    ver <- DecompVer.main(c, w, e);
    (* Commitment correctness *)
    (* - This needs f_inv and f properties *)
    return ver;
  }
}.

(* local lemma inter_completeness h' w' e' &m: *)
(*     R h' w' => *)
(*     Pr[Intermediate.main(h', w', e') @ &m : res] = 1%r. *)
(* proof. *)
(*   rewrite /R. rewrite pairS. *)
(*   progress. *)
(*   byphoare(: (h = h' /\ w = w' /\ e = e') ==>)=>//; last first. smt(). *)
(*   proc. *)
(*   call Decomp_verifiability. *)
(*   case (e' = 1). *)
(*     rcondt 10. auto. do ? call(:true); auto. *)
(*     inline *. *)
(*     auto. *)
(*     inline Phi.output Phi.share. *)
(*     sp. wp. *)
(*     call Com_ll. *)
(*     call Com_correct. *)
(*     call Com_correct. *)
(*     auto. *)
(*     have Hcircuit := compute_circuit_correct h'.`1 [w'] []. *)
(*     call Hcircuit. clear Hcircuit. *)
(*     auto; progress. *)
(*     apply dinput_ll. *)
(*     smt(). *)
(*     smt(). *)
(*     smt(). *)
(*     smt(). *)
(*     smt(). *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(nth_last size_ge0). *)
(*     rewrite /valid_view_op. *)
(*     rewrite foldr_range_forall. *)
(*     progress. *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(). *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(). *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(). *)
(*   case (e' = 2). *)
(*     rcondf 10. auto. do ? call(:true); auto. *)
(*     inline *. *)
(*     auto. *)
(*     rcondt 10. auto. do ? call(:true); auto. *)
(*     inline Phi.output Phi.share. *)
(*     auto. *)
(*     inline Phi.output Phi.share. *)
(*     sp. wp. *)
(*     call Com_correct. *)
(*     call Com_correct. *)
(*     call Com_ll. *)
(*     auto. *)
(*     have Hcircuit := compute_circuit_correct h'.`1 [w'] []. *)
(*     call Hcircuit. *)
(*     auto; progress. *)
(*     apply dinput_ll. *)
(*     smt(). *)
(*     smt(). *)
(*     smt(). *)
(*     smt(). *)
(*     smt(). *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(nth_last size_ge0). *)
(*     rewrite /valid_view_op. *)
(*     rewrite foldr_range_forall. *)
(*     progress. *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(). *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(). *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(). *)
(*   (* case (e' = 2) *) *)
(*     rcondf 10. auto. do ? call(:true); auto. *)
(*     inline Phi.output Phi.share. *)
(*     auto. *)
(*     rcondf 10. auto. do ? call(:true); auto. *)
(*     inline Phi.output Phi.share. *)
(*     auto. *)
(*     inline Phi.output Phi.share. *)
(*     sp. wp. *)
(*     call Com_correct. *)
(*     call Com_ll. *)
(*     call Com_correct. *)
(*     auto. *)
(*     have Hcircuit := compute_circuit_correct h'.`1 [w'] []. *)
(*     call Hcircuit. *)
(*     auto; progress. *)
(*     apply dinput_ll. *)
(*     smt(). *)
(*     smt(). *)
(*     smt(). *)
(*     smt(). *)
(*     smt(). *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(nth_last size_ge0). *)
(*     rewrite /valid_view_op. *)
(*     rewrite foldr_range_forall. *)
(*     progress. *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(). *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(). *)
(*     have : (result.`1, result.`2, result.`3, result.`4, result.`5, result.`6) = result by smt(). *)
(*     smt(). *)
(* qed. *)

(* local equiv inter_equiv : *)
(*     Sigma.Completeness(ZKBoo(Com)).special ~ Intermediate.main : *)
(*     ={h, w, e, glob Com} /\ R h{1} w{1} ==> ={res}. *)
(* proof. *)
(*   proc. *)
(*   inline ZKBoo(Com).init ZKBoo(Com).response ZKBoo(Com).verify. *)
(*   sp. *)
(*   case (e{1} = 1). *)
(*   rcondt{1} 17. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   rcondt{2} 9. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   rcondt{1} 26. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   inline Phi.reconstruct Intermediate.ComCorrectness.main. *)
(*   swap{2} [6..8] 9. *)
(*   auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. sim. *)
(*   call (:true); auto. *)

(*   case (e{1} = 2). *)
(*   rcondf{1} 17. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   rcondt{1} 17. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   rcondf{2} 9. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *; auto. *)
(*   rcondt{2} 9. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *; auto. *)
(*   rcondf{1} 26. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   rcondt{1} 26. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   inline Phi.reconstruct Intermediate.ComCorrectness.main. *)
(*   swap{2} [6..8] 9. *)
(*   wp. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. sim. *)
(*   call (:true); auto. *)

(*   (* case e = 3 *) *)
(*   rcondf{1} 17. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   rcondf{1} 17. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   rcondf{2} 9. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *; auto. *)
(*   rcondf{2} 9. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *; auto. *)
(*   rcondf{1} 26. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   rcondf{1} 26. progress. *)
(*     auto; do ? call (:true); auto. *)
(*     inline *. auto. *)
(*   inline Phi.reconstruct Intermediate.ComCorrectness.main. *)
(*   swap{2} [6..8] 9. *)
(*   wp. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. *)
(*   call (:true); auto. sim. *)
(*   call (:true); auto. *)
(* qed. *)

(* lemma zkboo_completeness h' w' e' &m: *)
(*     R h' w' /\ valid_circuit h'.`1 => *)
(*     Pr[Sigma.Completeness(ZKBoo(Com)).special(h', w', e') @ &m : res] = 1%r. *)
(* proof. *)
(*   move=> rel. *)
(*   have -> : Pr[Completeness(ZKBoo(Com)).special(h', w', e') @ &m : res] = *)
(*             Pr[Intermediate.main(h', w', e') @ &m : res]. *)
(*   - byequiv inter_equiv=>/#. *)
(*   by have := inter_completeness h' w' e' &m rel. *)
(* qed. *)

lemma Com_binding_three :
    phoare[BindingGame(Com).bind_three : true ==> ! res] = binding_prob.
proof.
    bypr=> &m Pre.
    smt(bind_three_equiv).
qed.

lemma binding_pred_implies_cons c1 c2 c3 m1 m1' m2 m2' m3 m3' &m:
    Pr[BindingGame(Com).bind_three(c1, c2, c3, m1, m1', m2, m2', m3, m3') @ &m : !res] =
    Pr[BindingGame(Com).bind_three(c1, c2, c3, m1, m1', m2, m2', m3, m3') @ &m :
      !(verify m1 c1 /\
        verify m1' c1 /\
        verify m2 c2 /\
        verify m2' c2 /\
        verify m3 c3 /\
        verify m3' c3 /\
        ((m1 = m1') /\ (m2 = m2') /\ (m3 = m3')))].
proof.
   byequiv=>//.
   proc*.
   inline *. auto.
qed.

lemma binding_three_cons_pr c1 c2 c3 a1 a1' a2 a2' a3 a3' &m:
    Pr[BindingGame(Com).bind_three(c1, c2, c3, a1, a1', a2, a2', a3, a3') @ &m :
      !(verify a1 c1 /\
        verify a1' c1 /\
        verify a2 c2 /\
        verify a2' c2 /\
        verify a3 c3 /\
        verify a3' c3 /\
        ((a1 = a1') /\ (a2 = a2') /\ (a3 = a3')))] = binding_prob.
proof.
    have Hbind := bind_three_equiv c1 c2 c3 a1 a1' a2 a2' a3 a3' &m.
    have <- := Com_binding_pr c1 a1 a1' &m.
    have <- := binding_pred_implies_cons c1 c2 c3 a1 a1' a2 a2' a3 a3' &m.
    smt.
qed.

lemma binding_three_cons c1' c2' c3' a1 a1' a2 a2' a3 a3':
    islossless BindingGame(Com).bind_three =>
    phoare[BindingGame(Com).bind_three : c1 = c1' /\ c2 = c2' /\ c3 = c3' /\ m1 = a1 /\ m1' = a1' /\ m2 = a2 /\ m2' = a2' /\ m3 = a3 /\ m3' = a3'
          ==> !(verify a1 c1' /\
                verify a1' c1' /\
                verify a2 c2' /\
                verify a2' c2' /\
                verify a3 c3' /\
                verify a3' c3' /\
                ((a1 = a1') /\ (a2 = a2') /\ (a3 = a3')))] = binding_prob.
proof.
    move=> bg_ll.
    bypr=> &m Pre.
    smt(binding_three_cons_pr).
qed.

lemma Com_binding_three_valid :
    islossless BindingGame(Com).bind_three =>
    phoare[BindingGame(Com).bind_three : true ==> res] = (1%r - binding_prob).
proof.
    move=> bg_ll.
    phoare split ! (1%r) binding_prob.
    proc*. call bg_ll.
    auto.
    bypr=> &m Pre.
    by have <- := bind_three_equiv c1{m} c2{m} c3{m} m1{m} m1'{m} m2{m} m2'{m} m3{m} m3'{m} &m.
qed.

lemma binding_valid_pred_implies_cons c1 c2 c3 m1 m1' m2 m2' m3 m3' &m:
    Pr[BindingGame(Com).bind_three(c1, c2, c3, m1, m1', m2, m2', m3, m3') @ &m : res] =
    Pr[BindingGame(Com).bind_three(c1, c2, c3, m1, m1', m2, m2', m3, m3') @ &m :
       (verify m1 c1 /\
        verify m1' c1 /\
        verify m2 c2 /\
        verify m2' c2 /\
        verify m3 c3 /\
        verify m3' c3 /\
        ((m1 = m1') /\ (m2 = m2') /\ (m3 = m3')))].
proof.
   byequiv=>//.
   proc*.
   inline *. auto.
qed.

lemma binding_three_cons_valid c1' c2' c3' a1 a1' a2 a2' a3 a3':
    islossless BindingGame(Com).bind_three =>
    phoare[BindingGame(Com).bind_three : c1 = c1' /\ c2 = c2' /\ c3 = c3' /\ m1 = a1 /\ m2 = a2 /\ m3 = a3 /\ m1' = a1' /\ m2' = a2' /\ m3' = a3'
           ==> (verify a1 c1' /\
                verify a1' c1' /\
                verify a2 c2' /\
                verify a2' c2' /\
                verify a3 c3' /\
                verify a3' c3' /\
                ((a1 = a1') /\ (a2 = a2') /\ (a3 = a3')))] = (1%r - binding_prob).
proof.
    move=> bg_ll.
    phoare split ! (1%r) binding_prob.
    proc.
    call (:true).
    auto.
    call (:true).
    auto.
    call (:true).
    auto. auto.

    have Hvalid := binding_three_cons c1' c2' c3' a1 a1' a2 a2' a3 a3' bg_ll.
    proc*. call Hvalid.
    auto.
qed.

equiv zkboo_shvzk:
    SHVZK(ZKBoo(Com, Decomp)).real ~ SHVZK(ZKBoo(Com, Decomp)).ideal :
    ={h, e, glob Com} /\ R h{1} w{1} /\ e{2} \in dchallenge ==> ={res}.
proof.
  proc.
  auto.
  inline ZKBoo(Com, Decomp).simulator.
  sp. auto.
  exists* h{1}.`1. elim*=> c.
  exists* e{2}. elim*=> e.
  exists* w{1}. elim*=> w.
  call (:true). sim.
  progress.
  inline ZKBoo(Com).simulator.
  inline ZKBoo(Com).response.
  inline ZKBoo(Com).init.
  auto.
  case (e = 1).
    rcondt{2} 4. auto.
    swap{2} [8..9] 4.
    swap{1} 14 -2.
    auto.
    call (:true). sim.
    call (:true). sim.
    inline Phi.output. auto.
    call Com_hiding_alt.
    call (:true).
    call (:true).
    wp. sp.
    inline Privacy.ideal Phi.share Phi.output. auto.
    have Hsim := phi_sim_circuit_equiv c e [w].
    call Hsim. clear Hsim.
    auto. smt(dlist_ll dinput_ll nth_last).
  case (e = 2).
    rcondf{2} 4. auto.
    rcondt{2} 4. auto.
    swap{2} [8..9] 4.
    call (:true). sim.
    call (:true). sim.
    inline Phi.output. auto.
    call (:true).
    call (:true).
    call Com_hiding_alt.
    wp. sp.
    inline Privacy.ideal Phi.share Phi.output. auto.
    have Hsim := phi_sim_circuit_equiv c e [w].
    call Hsim. clear Hsim.
    wp. sp.
    swap{1} 1 1.
    rnd (fun x => (w - x20{1}) - x).
    rnd.
    auto. smt(dlist_ll dinput_ll dinput_funi dinput_fu nth_last).
  case (e = 3).
    rcondf{2} 4. auto.
    rcondf{2} 4. auto.
    swap{2} [8..9] 4.
    swap{1} 12 2.
    call (:true). sim.
    call (:true). sim.
    inline Phi.output. auto.
    call (:true).
    call Com_hiding_alt.
    call (:true).
    wp. sp.
    inline Privacy.ideal Phi.share Phi.output. auto.
    have Hsim := phi_sim_circuit_equiv c e [w].
    call Hsim. clear Hsim.
    wp. sp.
    swap{2} 1 1.
    rnd (fun x => (w - x2{2}) - x).
    rnd.
    auto. smt(dlist_ll dinput_ll dinput_funi dinput_fu nth_last).

    exfalso. smt.
qed.

local module SoundnessInter = {
  module ZK = ZKBoo(Com)
  module BGame = BindingGame(Com)
  proc extract_views(h : statement, m : message, z1 z2 z3 : response) = {
    var k1,k2,k3,k1',k2',k3';
    var w1,w2,w3,w1',w2',w3';
    var cons, v1, v2, v3;
    var y1, y2, y3, c1, c2, c3;

    v1 = ZK.verify(h, m, 1, z1);
    v2 = ZK.verify(h, m, 2, z2);
    v3 = ZK.verify(h, m, 3, z3);

    (k1, w1, k2, w2) = z1;
    (k2', w2', k3, w3) = z2;
    (k3', w3', k1', w1') = z3;
    (y1, y2, y3, c1, c2, c3) = m;
    cons = BGame.bind_three(c1, c2, c3, (w1, k1), (w1', k1'), (w2, k2), (w2', k2'), (w3, k3), (w3', k3'));

    return v1 /\ v2 /\ v3;
  }

  proc main(h : statement, m : message, z1 z2 z3 : response) = {
    var v, w, w_get, ret;
    v = extract_views(h, m, z1, z2, z3);
    w = ZK.witness_extractor(h, m, [1;2;3], [z1;z2;z3]);

    if (w = None \/ !v) {
      ret = false;
    } else{
      w_get = oget w;
      ret = R h w_get;
    }
    return ret;
  }
}.

local equiv soundness_inter :
  Sigma.SpecialSoundness(ZKBoo(Com)).main ~ SoundnessInter.main :
  ={h, m} /\ c{1} = [1;2;3] /\ z{1} = [z1{2};z2{2};z3{2}] ==> ={res}.
proof.
  proc.
  sp.
  swap{2} 1 1.
  rcondt{1} 1. auto.
  rcondt{1} 7. auto. call (:true). auto. auto.
  rcondt{1} 13. auto. call (:true). auto. auto. call (:true). auto. auto.
  rcondf{1} 19. auto. call (:true). auto. auto. call (:true). auto. auto. call (:true). auto. auto.
  inline SoundnessInter.extract_views.
  swap{2} [7..9] 5.
  swap{2} 1 13.
  sp.
  wp. call (:true). sim.
  wp. call (:true). sim.
  wp. call (:true). sim.
  wp. call (:true). sim.
  auto; progress.
  inline *.
  auto; smt().
qed.

pred validate_response w1 w2 w3 w1' w2' w3' y y1 y2 y3 c' k1 k2 k3 k1' k2' k3' =
    w1 = w1' /\ w2 = w2' /\ w3 = w3' /\
    k1 = k1' /\ k2 = k2' /\ k3 = k3'
            /\ valid_output_shares y y1 y2 y3
            /\ valid_view 1 w1 w2 c' k1 k2
            /\ valid_view 2 w2 w3 c' k2 k3
            /\ valid_view 3 w3 w1 c' k3 k1
            /\ valid_view_output y1 w1
            /\ valid_view_output y2 w2
            /\ valid_view_output y3 w3
            /\ valid_circuit c'
            /\ size c' = size w1 - 1
            /\ size w1 = size w2
            /\ size w1 = size w3.

local lemma extraction_success
      c' y y1 y2 y3 c1 c2 c3
      w1 w2 w3 w1' w2' w3'
      k1 k2 k3 k1' k2' k3':
  islossless BindingGame(Com).bind_three =>
  phoare[ZKBoo(Com).verify :
      h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k1, w1, k2, w2) ==>
      res /\ valid_output_shares y y1 y2 y3 /\ valid_view 1 w1 w2 c' k1 k2 /\ valid_view_output y1 w1 /\ valid_view_output y2 w2
      /\ valid_circuit c'
      /\ size c' = size w1 - 1 /\ size w1 = size w2 /\ verify (w1, k1) c1 /\ verify (w2,k2) c2] = 1%r =>
  phoare[ZKBoo(Com).verify :
      h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k2', w2', k3, w3) ==>
      res /\ valid_output_shares y y1 y2 y3 /\ valid_view 2 w2' w3 c' k2' k3 /\ valid_view_output y2 w2' /\ valid_view_output y3 w3
      /\ valid_circuit c'
      /\ size c' = size w2' - 1 /\ size w2' = size w3 /\ verify (w2', k2') c2 /\ verify (w3, k3) c3] = 1%r =>
  phoare[ZKBoo(Com).verify :
      h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k3', w3', k1', w1') ==>
      res /\ valid_output_shares y y1 y2 y3 /\ valid_view 3 w3' w1' c' k3' k1' /\ valid_view_output y3 w3' /\ valid_view_output y1 w1'
      /\ valid_circuit c'
      /\ size c' = size w3' - 1 /\ size w3' = size w1' /\ verify (w3', k3') c3 /\ verify (w1', k1') c1] = 1%r =>
  phoare[SoundnessInter.extract_views :
      h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z1 = (k1, w1, k2, w2) /\ z2 = (k2', w2', k3, w3) /\ z3 = (k3', w3', k1', w1')
      ==> res /\ (validate_response w1 w2 w3 w1' w2' w3' y y1 y2 y3 c' k1 k2 k3 k1' k2' k3')] = (1%r - binding_prob).
proof.
    move=> bg_ll accept1 accept2 accept3.
    proc.
    auto.
    have Hcons := binding_three_cons_valid c1 c2 c3 (w1, k1) (w1', k1') (w2, k2) (w2', k2') (w3, k3) (w3', k3') bg_ll.
    call Hcons. clear Hcons.
    auto.
    call accept3.
    call accept2.
    call accept1.
    auto.
    progress.
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
    smt().
qed.

lemma zkboo_soundness_if_consistent
      c' y y1 y2 y3 c1 c2 c3
      k1' k2' k3' w1 w2 w3 &m:
  phoare[ZKBoo(Com).witness_extractor :
          valid_output_shares y y1 y2 y3
          /\ valid_view 1 w1 w2 c' k1' k2'
          /\ valid_view 2 w2 w3 c' k2' k3'
          /\ valid_view 3 w3 w1 c' k3' k1'
          /\ valid_view_output y1 w1
          /\ valid_view_output y2 w2
          /\ valid_view_output y3 w3
          /\ size c' = size w1 - 1
          /\ size w1 = size w2
          /\ size w1 = size w3
          /\ valid_circuit c' /\ h = (c',y) /\ a = (y1,y2,y3,c1,c2,c3) /\ z = [(k1', w1, k2', w2);(k2', w2, k3', w3);(k3', w3, k1', w1)]
         ==> res <> None /\ R (c',y) (oget res)] = 1%r.
proof.
  proc.
  auto.
  rewrite /valid_output_share /valid_view_output; progress.
  rewrite !oget_some.
  clear H7 H8 H9 H10 H11 H12.
  rewrite /R /R_DL.
  progress.
  rewrite /valid_output_shares in H.
  rewrite /valid_view in H0.
  rewrite /valid_view in H1.
  rewrite /valid_view in H2.
  have H' := eval_circuit_module c' [oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0)] y &m.
  apply H'. clear H'.
  have <- :
    Pr[Phi.main(oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0), c') @ &m :
      res = y] =
    Pr[Circuit.eval(c', [oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0)]) @ &m :
      res = y].
  byequiv correctness_module=>//.
  have -> :
    Pr[Phi.main(oget (onth w1 0) + oget (onth w2 0) + oget (onth w3 0), c') @ &m :
      res = y] =
    Pr[Phi.main_fixed_input_and_tape(oget (onth w1 0), oget (onth w2 0), oget (onth w3 0), c' , k1', k2', k3') @ &m :
      res = y].
  byequiv main_fixed_equiv=>//.
  rewrite H.
  byphoare(: valid_circuit c' /\ c = c' /\ k1 = k1' /\ k2 = k2' /\ k3 = k3' /\ x1 = (oget (onth w1 0)) /\ x2 = (oget (onth w2 0)) /\ x3 = (oget (onth w3 0)) ==> res = last 0 w1 + last 0 w2 + last 0 w3)=>//.
  proc.
  inline Phi.reconstruct Phi.output.
  wp.
  inline *.
  auto.
  while (size w10 = size w1 - size c0 /\
         size w20 = size w2 - size c0 /\
         size w30 = size w3 - size c0 /\
         size c' = size c0 + size w10 - 1 /\
         k10 = k1' /\
         k20 = k2' /\
         k30 = k3' /\
         0 < size w10 /\
         0 < size w20 /\
         0 < size w30 /\
         (forall i, 0 <= i < size c0 => (nth (ADDC(0,0)) c0 i = nth (ADDC(0,0)) c' (size w10 - 1 + i) /\ (size w10 -1 + i) < size c')) /\
         (forall i, i < size w10 => nth 0 w1 i = nth 0 w10 i) /\
         (forall i, i < size w20 => nth 0 w2 i = nth 0 w20 i) /\
         (forall i, i < size w30 => nth 0 w3 i = nth 0 w30 i))
        (size c0).
  auto.
  progress.
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  have H14' := H14 (i + 1) _. smt().
  rewrite size_rcons.
  have -> := nth_behead (ADDC(0,0)) c0{hr0} i _. smt().
  smt.
  smt(size_rcons).

  rewrite !nth_rcons.
  case (i < size w10{hr0});progress.
  smt().
  case (i = size w10{hr0}); progress.
  have -> := H0 (size w10{hr0} - 1) _. smt.
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H18.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w10{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H6.
  have := H6 (size w10{hr0} - 1) _. smt.
  have -> := onth_nth (ADDC(0,0)) c' (size w10{hr0} - 1). smt.
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w10{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).

  rewrite !nth_rcons.
  case (i < size w20{hr0});progress.
  smt.
  case (i = size w20{hr0}); progress.
  have -> := H1 (size w20{hr0} - 1) _. smt.
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H18.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w20{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H6.
  have := H6 (size w20{hr0} - 1) _. smt.
  have -> := onth_nth (ADDC(0,0)) c' (size w20{hr0} - 1). smt.
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w20{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).

  rewrite !nth_rcons.
  case (i < size w30{hr0});progress.
  smt.
  case (i = size w30{hr0}); progress.
  have -> := H2 (size w30{hr0} - 1) _. smt.
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H18.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w30{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H6.
  have := H6 (size w30{hr0} - 1) _. smt.
  have -> := onth_nth (ADDC(0,0)) c' (size w30{hr0} - 1). smt.
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w30{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).
  smt(size_rcons head_behead).

  auto.
  smt(onth_nth oget_some size_ge0 dinput_ll nth_out nth_last).
qed.


local lemma zkboo_inter_soundness
    c' y y1 y2 y3 c1 c2 c3
    w1 w2 w3 w1' w2' w3'
    k1 k2 k3 k1' k2' k3' &m:
    islossless BindingGame(Com).bind_three =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k1, w1, k2, w2) ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 1 w1 w2 c' k1 k2 /\ valid_view_output y1 w1 /\ valid_view_output y2 w2
        /\ valid_circuit c'
        /\ size c' = size w1 - 1 /\ size w1 = size w2 /\ verify (w1, k1) c1 /\ verify (w2,k2) c2] = 1%r =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k2', w2', k3, w3) ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 2 w2' w3 c' k2' k3 /\ valid_view_output y2 w2' /\ valid_view_output y3 w3
        /\ valid_circuit c'
        /\ size c' = size w2' - 1 /\ size w2' = size w3 /\ verify (w2', k2') c2 /\ verify (w3, k3) c3] = 1%r =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k3', w3', k1', w1') ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 3 w3' w1' c' k3' k1' /\ valid_view_output y3 w3' /\ valid_view_output y1 w1'
        /\ valid_circuit c'
        /\ size c' = size w3' - 1 /\ size w3' = size w1' /\ verify (w3', k3') c3 /\ verify (w1', k1') c1] = 1%r =>
    phoare[SoundnessInter.main :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z1 = (k1, w1, k2, w2) /\ z2 = (k2', w2', k3, w3) /\ z3 = (k3', w3', k1', w1')
        ==> res] = (1%r - binding_prob).
proof.
  move=> bg_ll accept1 accept2 accept3.
  (* phoare split (1%r - binding_prob) binding_prob : (validate_response w1 w2 w3 w1' w2' w3' y y1 y2 y3 c' k1 k2 k3 k1' k2' k3'). *)
(*   proc. *)
(*   seq 1 : (#pre /\ v /\ validate_response w1 w2 w3 w1' w2' w3' y y1 y2 y3 c' k1 k2 k3 k1' k2' k3') (1%r - binding_prob) 1%r binding_prob 0%r. *)
(*   - auto. *)
(*   - have H' := extraction_success c' y y1 y2 y3 c1 c2 c3 w1 w2 w3 w1' w2' w3' k1 k2 k3 k1' k2' k3' bg_ll accept1 accept2 accept3. *)
(*     call H'. *)
(*     auto. *)
(*   wp. *)
(*   have H' := zkboo_soundness_if_consistent c' y y1 y2 y3 c1 c2 c3 k1 k2 k3 w1 w2 w3 &m. *)
(*   call H'. *)
(*   skip. progress. *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(*   smt(). *)
(* hoare. *)
(* inline *. auto. *)
(* progress. *)
(* smt(). *)

(* lemma zkboo_soundness_if_consistent *)
(*       c' y y1 y2 y3 c1 c2 c3 *)
(*       k1' k2' k3' w1 w2 w3 &m: *)
  have Hcons := binding_three_cons_valid c1 c2 c3 (w1, k1) (w1', k1') (w2, k2) (w2', k2') (w3, k3) (w3', k3') bg_ll.
  proc.
  inline SoundnessInter.ZK.witness_extractor.
  auto.
  inline SoundnessInter.extract_views.
  (* call (: validate_response w1 w2 w3 w1' w2' w3' y y1 y2 y3 c' k1 k2 k3 k1' k2' k3'). *)


  auto.
  have Hcons := binding_three_cons_valid c1 c2 c3 (w1, k1) (w1', k1') (w2, k2) (w2', k2') (w3, k3) (w3', k3') bg_ll.
  call Hcons. clear Hcons.
  auto.
  call accept3.
  call accept2.
  call accept1.
  auto.
  rewrite /valid_output_share /valid_view_output; progress.
  rewrite !oget_some.
  clear accept1 accept2 accept3 H25 H31 H32 H33 H34 H35 H36 H37 H26 H30 H8 H17 H20 H10 H19 H27 H24.
  rewrite /R /R_DL.
  progress.
  rewrite /valid_output_shares in H0.
  rewrite /valid_view in H1.
  rewrite /valid_view in H18.
  rewrite /valid_view in H9.
  clear H29 H28 H15 H6 H14 H11 H21 H5.
  have H' := eval_circuit_module c' [oget (onth w1' 0) + oget (onth w2' 0) + oget (onth w3' 0)] y &m.
  apply H'. clear H'.
  have <- :
    Pr[Phi.main(oget (onth w1' 0) + oget (onth w2' 0) + oget (onth w3' 0), c') @ &m :
      res = y] =
    Pr[Circuit.eval(c', [oget (onth w1' 0) + oget (onth w2' 0) + oget (onth w3' 0)]) @ &m :
      res = y].
  byequiv correctness_module=>//.
  have -> :
    Pr[Phi.main(oget (onth w1' 0) + oget (onth w2' 0) + oget (onth w3' 0), c') @ &m :
      res = y] =
    Pr[Phi.main_fixed_input_and_tape(oget (onth w1' 0), oget (onth w2' 0), oget (onth w3' 0), c' , k1', k2', k3') @ &m :
      res = y].
  byequiv main_fixed_equiv=>//.
  rewrite H0.
  byphoare(: valid_circuit c' /\ c = c' /\ k1 = k1' /\ k2 = k2' /\ k3 = k3' /\ x1 = (oget (onth w1' 0)) /\ x2 = (oget (onth w2' 0)) /\ x3 = (oget (onth w3' 0)) ==> res = last 0 w1' + last 0 w2' + last 0 w3')=>//.
  proc.
  inline Phi.reconstruct Phi.output.
  wp.
  inline *.
  auto.
  while (size w10 = size w1' - size c0 /\
         size w20 = size w2' - size c0 /\
         size w30 = size w3' - size c0 /\
         size c' = size c0 + size w10 - 1 /\
         k10 = k1' /\
         k20 = k2' /\
         k30 = k3' /\
         0 < size w10 /\
         0 < size w20 /\
         0 < size w30 /\
         (forall i, 0 <= i < size c0 => (nth (ADDC(0,0)) c0 i = nth (ADDC(0,0)) c' (size w10 - 1 + i) /\ (size w10 -1 + i) < size c')) /\
         (forall i, i < size w10 => nth 0 w1' i = nth 0 w10 i) /\
         (forall i, i < size w20 => nth 0 w2' i = nth 0 w20 i) /\
         (forall i, i < size w30 => nth 0 w3' i = nth 0 w30 i))
        (size c0).
  auto.
  progress.
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(size_rcons).
  smt(nth_behead size_rcons).
  smt(size_rcons).

  rewrite !nth_rcons.
  case (i < size w10{hr0}); first smt().
  case (i = size w10{hr0}); progress.
  have -> := H1 (size w10{hr0} - 1) _. smt(size_ge0).
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H24.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w10{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H2.
  have := H2 (size w10{hr0} - 1) _. smt(size_ge0).
  have -> := onth_nth (ADDC(0,0)) c' (size w10{hr0} - 1). smt(size_ge0).
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w10{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).

  rewrite !nth_rcons.
  case (i < size w20{hr0}); first smt().
  case (i = size w20{hr0}); progress.
  have -> := H9 (size w20{hr0} - 1) _. smt(size_ge0).
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H24.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w20{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H2.
  have := H2 (size w20{hr0} - 1) _. smt(size_ge0).
  have -> := onth_nth (ADDC(0,0)) c' (size w20{hr0} - 1). smt(size_ge0).
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w20{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).

  rewrite !nth_rcons.
  case (i < size w30{hr0}); first smt().
  case (i = size w30{hr0}); progress.
  have -> := H18 (size w30{hr0} - 1) _. smt(size_ge0).
  have -> := ohead_head (ADDC(0,0)) c0{hr0} H24.
  rewrite oget_some.
  have <- : (nth (ADDC(0,0)) c' (size w30{hr0} - 1)) = head (ADDC(0,0)) c0{hr0}.
  smt(nth0_head size_ge0).
  rewrite /valid_circuit /valid_gate in H2.
  have := H2 (size w30{hr0} - 1) _. smt(size_ge0).
  have -> := onth_nth (ADDC(0,0)) c' (size w30{hr0} - 1). smt(size_ge0).
  rewrite oget_some.
  elim (nth (ADDC(0,0)) c' (size w30{hr0} - 1)); move=>x; case x=> x1 x2; smt().
  smt(size_rcons head_behead).
  smt().

  auto.
  smt(onth_nth oget_some size_ge0 dinput_ll nth_out nth_last).
  smt(nth_last).
  smt(nth_last).
  smt(nth_last).
  smt(nth_last).
  smt(nth_last).
  smt(nth_last).
qed.


lemma zkboo_soundness
    c' y y1 y2 y3 c1 c2 c3
    w1 w2 w3 w1' w2' w3'
    k1 k2 k3 k1' k2' k3' &m:
    islossless BindingGame(Com).bind_three =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k1, w1, k2, w2) ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 1 w1 w2 c' k1 k2 /\ valid_view_output y1 w1 /\ valid_view_output y2 w2
        /\ valid_circuit c'
        /\ size c' = size w1 - 1 /\ size w1 = size w2 /\ verify (w1, k1) c1 /\ verify (w2,k2) c2] = 1%r =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k2', w2', k3, w3) ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 2 w2' w3 c' k2' k3 /\ valid_view_output y2 w2' /\ valid_view_output y3 w3
        /\ valid_circuit c'
        /\ size c' = size w2' - 1 /\ size w2' = size w3 /\ verify (w2', k2') c2 /\ verify (w3, k3) c3] = 1%r =>
    phoare[ZKBoo(Com).verify :
        h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z = (k3', w3', k1', w1') ==>
        res /\ valid_output_shares y y1 y2 y3 /\ valid_view 3 w3' w1' c' k3' k1' /\ valid_view_output y3 w3' /\ valid_view_output y1 w1'
        /\ valid_circuit c'
        /\ size c' = size w3' - 1 /\ size w3' = size w1' /\ verify (w3', k3') c3 /\ verify (w1', k1') c1] = 1%r =>
    Pr[Sigma.SpecialSoundness(ZKBoo(Com)).main((c',y), (y1,y2,y3,c1,c2,c3), [1;2;3], [(k1, w1, k2, w2); (k2', w2', k3, w3); (k3', w3', k1', w1')]) @ &m :res]
        = (1%r - binding_prob).
proof.
  move=> bg_ll accept1 accept2 accept3.
  have -> :
    Pr[SpecialSoundness(ZKBoo(Com)).main((c', y), (y1, y2, y3, c1, c2, c3), [1; 2; 3], [(k1, w1, k2, w2); (k2', w2', k3, w3); (k3', w3', k1', w1')]) @ &m : res] =
    Pr[SoundnessInter.main((c', y), (y1, y2, y3, c1, c2, c3), (k1, w1, k2, w2), (k2', w2', k3, w3), (k3', w3', k1', w1') ) @ &m : res].
  byequiv soundness_inter=>//.

  byphoare(: h = (c',y) /\ m = (y1,y2,y3,c1,c2,c3) /\ z1 = (k1, w1, k2, w2) /\ z2 = (k2', w2', k3, w3) /\ z3 = (k3', w3', k1', w1') ==> _)=>//.
  proc*.
  have Hsuccess := zkboo_inter_soundness c' y y1 y2 y3 c1 c2 c3 w1 w2 w3 w1' w2' w3' k1 k2 k3 k1' k2' k3' &m bg_ll accept1 accept2 accept3.
  call Hsuccess.
  skip. progress.
qed.


end section Protocol.
