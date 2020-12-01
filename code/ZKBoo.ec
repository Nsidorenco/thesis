(* Formalization of ZKBoo Sigma-protocol *)
require import AllCore Distr List DInterval DList DBool IntDiv Folding.
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
op dchallenge   = challenge.

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
      (* (* TODO: by [dt_ll, dt_funi] *) *)
      (* split. apply dinter_ll. trivial. apply is_full_funiform. *)
      (* rewrite /is_full. *)
      (* progress. *)
      (* case (0 < x <= 3). *)
      (* smt. *)
      (* move=> H. *)
      (* have : 0 < x <= 3. apply challenge_size. *)
      (* smt(). *)
      (* apply dinter_uni. *)
  admitted.

module ZKBoo(C : Committer, D : Phi) : SProtocol = {
  var ws : view list

  proc init(h : statement, w : witness) = {
    var y,c,ks,cs,ys,i,ctmp;
    (c, y) <- h;
    ks <- D.sample_tapes(size c);
    ws <- D.decomp(c, w, ks);
    cs <- [];
    ys <- map output ws;
    i <- 0;
    while (i < n) {
      ctmp <- C.commit(nth witness ws i);
      cs <- rcons cs ctmp;
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
    while (i < n) {
      if (in_dom_f n e i) {
        view <- nth_looping ws (i-e);
        com <- nth witness cs i;
        valid_com <- valid_com /\ (verify view com);
      }
      i <- i + 1;
    }
    valid <- D.verify(c, z, e, ys);

    return valid_com /\ valid /\ reconstruct ys = y;

  }

  proc witness_extractor(h : statement, a : message,
                         e : challenge list, z : response list) = {
    var w;
    w <- D.extractor(z);
    return w;
  }

  proc simulator(h : statement, e : challenge) = {
    var c, y, ys, vs, cs, vs', ctmp, i, a;
    (c, y) <- h;
    (vs', ys) <- D.simulator(c, y, e);
    vs <- f_inv vs';
    cs <- [];
    i <- 0;
    while (i < n) {
      if (in_dom_f n e i) {
        ctmp <- C.commit(nth_looping vs (i-e));
        cs <- rcons cs ctmp;
      } else{
        ctmp <- C.commit(witness);
        cs <- rcons cs ctmp;
      }
      i <- i + 1;
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
  module Corr = Correctness(Com)
  var ws : view list

  proc decomposition(c, w, e, y) = {
    var ks, z, valid, ws', ys, y';
    ks <- Decomp.sample_tapes(size c);
    ws <- Decomp.decomp(c, w, ks);

    z <-  f ws e;
    ws' <- f_inv z;

    ys <- map output ws;

    y' <- reconstruct ys;
    valid <- Decomp.verify(c, z, e, ys);
    return valid /\ y' = y;
  }

  proc commitment(ws : view list, e : challenge) = {
    var z, ws';
    var ctmp, cs, i;
    var valid_com, view, c;

    z <-  f ws e;
    ws' <- f_inv z;
    valid_com <- true;
    cs <- [];
    i <- 0;
    while (i < n) {
      ctmp <- Com.commit(nth witness ws i);
      cs <- rcons cs ctmp;
      i <- i + 1;
    }
    i <- 0;
    while (i < n) {
      if (in_dom_f n e i) {
        view <- nth_looping ws' (i-e);
        c <- nth witness cs i;
        valid_com <- valid_com /\ (verify view c);
      }
      i <- i + 1;
    }
    return valid_com;
  }

  proc commitment_combined(ws, e : challenge) = {
    var z, ws', c;
    var ys, i, ctmp, ytmp;
    var valid_com, view, cs;

    z <-  f ws e;
    ws' <- f_inv z;
    valid_com <- true;
    ys <- [];
    cs <- [];
    i <- 0;
    while (i < n) {
      if (in_dom_f n e i) {
        ctmp <- Com.commit(nth witness ws i);
        ytmp <- output(nth witness ws i);
        cs <- rcons cs ctmp;
        ys <- rcons ys ytmp;
        view <- nth_looping ws' (i-e);
        c <- nth witness cs i;
        valid_com <- valid_com /\ (verify view c);
      } else {
        ctmp <- Com.commit(nth witness ws i);
        ytmp <- output(nth witness ws i);
        cs <- rcons cs ctmp;
        ys <- rcons ys ytmp;
      }

      i <- i + 1;
    }
    return valid_com;
  }

  proc commitment_combined_fixed(ws, e : challenge) = {
    var z, ws';
    var ys, i, ctmp, ytmp;
    var valid_com, view, cs;

    z <-  f ws e;
    ws' <- f_inv z;
    valid_com <- true;
    ys <- [];
    cs <- [];
    i <- 0;
    while (i < n) {
      if (in_dom_f n e i) {
        ctmp <- Com.commit(nth witness ws i);
        ytmp <- output(nth witness ws i);
        cs <- rcons cs ctmp;
        ys <- rcons ys ytmp;
        view <- nth_looping ws' (i-e);
        valid_com <- valid_com /\ (verify view ctmp);
      } else {
        ctmp <- Com.commit(nth witness ws i);
        ytmp <- output(nth witness ws i);
        cs <- rcons cs ctmp;
        ys <- rcons ys ytmp;
      }

      i <- i + 1;
    }
    return valid_com;
  }


  proc commitment_game(ws, e : challenge) = {
    var z, ws', b;
    var valid_com, i;

    z <-  f ws e;
    ws' <- f_inv z;
    valid_com <- true;
    i <- 0;
    while (i < n) {
      if (in_dom_f n e i) {
        b <- Corr.main(nth_looping ws' (i-e));
        valid_com <- valid_com /\ b;
      } else {
        Com.commit(nth witness ws i);
      }
      i <- i + 1;
    }
    return valid_com;
  }

  proc main(h : statement, w : witness, e : challenge) = {
    var valid_com, valid, c, y;
    (c, y) <- h;
    valid <- decomposition(c, w, e, y);
    valid_com <- commitment(ws, e);
    return valid_com /\ valid;
  }
}.

local equiv com_inter:
  Com_Inter.main ~ Completeness(ZKBoo(Com, Decomp)).special : ={h, w, e, glob Decomp, glob Com} ==> ={res}.
proof.
  proc.
  inline ZKBoo(Com, Decomp).init ZKBoo(Com, Decomp).response ZKBoo(Com, Decomp).verify.
  inline Com_Inter.decomposition Com_Inter.commitment.
  auto. 
  swap{2} 26 -4.
  auto.
  swap{2} 10 2.
  swap{2} [12..13] 3.
  swap{2} [15..17] 3.
  swap{2} [12..18] -2.
  auto.
  (* fission{2} 9 @ 2 , 4. *)
  while (ws{2} = ws'0{1} /\ size cs0{2} = n /\ valid_com0{1} = valid_com{2} /\ cs{1} = cs0{2} /\ i{1} = i0{2} /\ ={ys, e1, glob Com}).
  - auto.
  swap{1} [12..13] 8.
  auto.
  call (:true). 
  auto.
  while (={cs, glob Com} /\ i{1} = i{2} /\ ws{1} = ZKBoo.ws{2} /\ size cs{2} = i{2} /\ i{2} <= n); auto.
  - call(:true). auto.
    smt(size_ge0 size_rcons).
  auto.
  call (:true); auto.
  call (:true); auto.
  progress.
  smt(n_pos).
  smt(size_ge0).
qed.

lemma foldr_and b s e (cs : commitment list) (ws' : view list) n:
    foldr
    (fun (i, acc) =>
      if in_dom_f n e i then
      acc /\
      verify (nth_looping ws' (i-e)) (nth witness cs i)
    else acc) b s = 
    (foldr
    (fun (i, acc) =>
      if in_dom_f n e i then
      acc /\
      verify (nth_looping ws' (i-e)) (nth witness cs i)
    else acc) true s /\ b).
proof.
  elim s; progress.

  (* Inductive case *)
  smt.
qed.

lemma foldr_rcons b e (ws' : view list) (cs : commitment list) x :
  foldr
    (fun (i : int) (acc : bool) =>
      if in_dom_f n e i then
        acc /\ verify (nth_looping ws' (i-e)) (nth witness cs i)
      else acc) b
    (range 0 (size cs)) =
  foldr
    (fun (i : int) (acc : bool) =>
      if in_dom_f n e i then
        acc /\
        verify (nth_looping ws' (i-e))
          (nth witness (rcons cs x) i)
      else acc) b
    (range 0 (size cs)).
proof.
  rewrite eq_sym.
  rewrite foldr_range.
  rewrite eq_sym.
  rewrite foldr_range.
  congr.
  rewrite rel_ext.
  simplify. 
  rewrite /(===).
  progress.
  rewrite /nth_looping nth_rcons.
  case (0 <= x0 && x0 < size cs); progress.
  case (in_dom_f n e x0); progress.
  smt(size_rcons).
qed.
  

local lemma commitment_correct:
    phoare[Com_Inter.commitment : e \in dchallenge ==> res] = 1%r.
proof.
  bypr=> &m pre.
  have -> : Pr[Com_Inter.commitment(ws{m}, e{m}) @ &m : res]
          = Pr[Com_Inter.commitment_combined(ws{m}, e{m}) @ &m : res].
  - byequiv=>//.
    proc.
    auto.
    while{1} (cs{1} = cs{2} /\ ws'{1} = ws'{2} /\ 0 <= i{1} /\ i{1} <= n /\
              valid_com{1} = foldr (fun (i, acc) => if (in_dom_f n e{1} i) then acc /\ verify (nth_looping ws'{1} (i - e{1})) (nth witness cs{1} i) else acc) true (range 0 i{1}))
             (n - i{1}).
    - progress.
      auto. progress. smt(). smt().
      rewrite rangeSr. smt().
      rewrite - cats1.
      rewrite foldr_cat.
      have -> : (foldr (fun (i : int) (acc : bool) =>
              if in_dom_f n e{hr} i then
                acc /\
                verify (nth_looping ws'{m0} (i - e{hr})) (nth witness cs{m0} i)
              else acc) true [i{hr}]) = verify (nth_looping ws'{m0} (i{hr} - e{hr})) (nth witness cs{m0} i{hr}).
      smt().
      by rewrite - foldr_and.
      smt().
      smt().
      smt().
      rewrite rangeSr. smt().
      rewrite - cats1.
      rewrite foldr_cat.
      have -> : (foldr (fun (i : int) (acc : bool) =>
              if in_dom_f n e{hr} i then
                acc /\
                verify (nth_looping ws'{m0} (i-e{hr})) (nth witness cs{m0} i)
              else acc) true [i{hr}]) = true.
      smt().
      trivial.
      smt().
    auto.
    while (={cs, e, i, ws, glob Com} /\ 0 <= i{1} /\ size cs{1} = i{1} /\ i{1} <= n /\
           valid_com{2} = foldr (fun (i, acc) => if (in_dom_f n e{2} i) then acc /\ verify (nth_looping ws'{2} (i-e{2})) (nth witness cs{2} i) else acc) true (range 0 i{2})).
    - if{2}; auto; call (:true).
      skip; progress.
      smt(). 
      smt(size_rcons).
      smt(size_rcons).
      have -> : (range 0 (size cs{2} + 1)) = (range 0 (size cs{2})) ++ [size cs{2}]. smt(rangeSr cats1).
      rewrite foldr_cat.
      have -> :
      (foldr
        (fun (i : int) (acc : bool) =>
            if in_dom_f n e{2} i then
              acc /\
              verify (nth_looping ws'{2} (i - e{2}))
                (nth witness (rcons cs{2} result_R) i)
            else acc) true [size cs{2}]) =
      verify (nth_looping ws'{2} (size cs{2} - e{2}))
        (nth witness (rcons cs{2} result_R) (size cs{2})).
      smt().
      rewrite - foldr_and.
      rewrite /nth_looping !nth_rcons. simplify.
      progress.
      pose b := (verify (nth witness ws'{2} ((size cs{2} - e{2}) %% n)%IntDiv) result_R).
      by have -> := foldr_rcons (verify (nth witness ws'{2} ((size cs{2} - e{2}) %% n)) result_R)
                                e{2} ws'{2} cs{2} result_R.
      skip; progress.
      smt().
      smt(size_rcons).
      smt(size_rcons).
      rewrite rangeSr. apply size_ge0.
      have -> : (rcons (range 0 (size cs{2})) (size cs{2})) = (range 0 (size cs{2})) ++ [size cs{2}]. smt(cats1).
      rewrite foldr_cat=>/>.
      rewrite H3=>/>.
      by have -> := foldr_rcons true e{2} ws'{2} cs{2} result_R.
      auto.
      progress.
      smt(n_pos).
      smt.
      smt(size_ge0).
      rewrite range_geq; trivial.
      smt().
      smt().

  have -> : Pr[Com_Inter.commitment_combined(ws{m}, e{m}) @ &m : res]
          = Pr[Com_Inter.commitment_combined_fixed(ws{m}, e{m}) @ &m : res].
  - byequiv=>//.
    proc.
    sp. auto.
    inline Com_Inter.Corr.main.
    sim.
    while(={ws, ws', cs, ys, valid_com, glob Com, i, e} /\ i{1} = size cs{1}).
    if. smt.
    - auto.
      call (:true).
      skip; progress.
      congr. rewrite /nth_looping nth_rcons.
      smt(size_rcons).
      by rewrite size_rcons.
    - auto.
      call (:true).
      skip; progress.
      by rewrite size_rcons.
    skip; progress.

  have -> : Pr[Com_Inter.commitment_combined_fixed(ws{m}, e{m}) @ &m : res]
          = Pr[Com_Inter.commitment_game(ws{m}, e{m}) @ &m : res].
  - byequiv=>//.
    proc.
    sp. auto.
    inline Com_Inter.Corr.main.
    sim.
    while(={ws, ws', e, i, glob Com, valid_com} /\ ws'{1} = f_inv z{1} /\ z{1} = f ws{1} e{m} /\ e{1} = e{m}).
    if. smt().
    - auto.
      call (:true).
      wp; skip; progress.
      by have := f_inv_correct ws{2} e{m} pre i{2} H1. 
    - auto.
      call (:true).
      skip; progress.
    skip; progress.

  byphoare(: ws = ws{m} /\ e = e{m} ==> )=>//; proc.
  sp.
  while (valid_com = true) (n - i).
  - progress.
    if.
    + auto.
      call Com_correct.
      skip; smt().
    + auto.
      call Com_ll.
      skip; smt().
    skip; smt().
qed.

axiom Decomp_verifiability :
  phoare[Verifiability(Decomp).main : true ==> res] = 1%r.

local lemma decomposition_correct :
    phoare[Com_Inter.decomposition : R (c, y) w ==> res] = 1%r.
proof.
  bypr=> &m pre.
  have -> : Pr[Com_Inter.decomposition(c{m}, w{m}, e{m}, y{m}) @ &m : res]
          = Pr[Verifiability(Decomp).main(c{m}, w{m}, e{m}) @ &m : res].
  (* - byequiv(: ={glob Decomp, c, e, w} /\ c{2} = c{m} /\ w{1} = w{m} /\  /\ y{1} = circuit_eval c{2} w{2} ==>)=>//. *)
  - byequiv=>//.
    proc.
    call (:true).
    wp.
    call (:true).
    auto.
    call (:true).
    auto. 
    progress.
    smt().
  byphoare Decomp_verifiability=>/>.
qed.

lemma completeness:
    phoare[Completeness(ZKBoo(Com,Decomp)).special : R h w /\ e \in dchallenge ==> res] = 1%r.
proof.
  bypr=> &m rel.
  have <- : Pr[Com_Inter.main(h{m}, w{m}, e{m}) @ &m : res]
          = Pr[Completeness(ZKBoo(Com, Decomp)).special(h{m}, w{m}, e{m}) @ &m : res].
  - byequiv com_inter=>//.
  byphoare(: h = h{m} /\ w = w{m} /\ e = e{m} ==>)=>//.
  proc.
  call commitment_correct.
  call decomposition_correct.
  auto; progress.
  smt().
  smt().
qed.

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

local module SHVZK_Inter = {
    module ZK = ZKBoo(Com, Decomp)
    module PZK = Privacy(Decomp)

    proc real(h, w, e) = {
      var vs,vs',y,c,cs,ys,i,ctmp,v,ret,valid_com,view,com;
      (c, y) <- h;
      (vs', ys) <- PZK.real(c, w, e);
      cs <- [];
      vs <- f_inv vs';
      i <- 0;
      while (i < n) {
        if (in_dom_f n e i) {
          ctmp <- Com.commit(nth_looping vs (i-e));
          cs <- rcons cs ctmp;
          i <- i + 1;
        } else {
          ctmp <- Com.commit(witness);
          cs <- rcons cs ctmp;
          i <- i + 1;
        }
      }

      i <- 0;
      valid_com <- true;
      while (i < n) {
        if (in_dom_f n e i) {
          view <- nth_looping vs (i-e);
          com <- nth witness cs i;
          valid_com <- valid_com /\ (verify view com);
        }
        i <- i + 1;
      }
      v <- Decomp.verify(c, vs', e, ys);

      ret <- None;
      if (v /\ valid_com /\ reconstruct ys = y) {
        ret <- Some ((ys, cs), e, vs');
      }

      return ret;
    }

    proc ideal(h, e : challenge) = {
      var c, y, vs, vs', ys', cs, i, ctmp, ws, view, com, valid_com, v, ret;
      (c, y) <- h;
      (vs', ys') <- PZK.ideal(c, y, e);
      vs <- f_inv vs';
      cs <- [];
      i <- 0;
      while (i < n) {
        ctmp <- Com.commit(nth_looping vs (i-e));
        cs <- rcons cs ctmp;
        i <- i + 1;
      }
      
      ws <- f_inv vs';

      i <- 0;
      valid_com <- true;
      while (i < n) {
        if (in_dom_f n e i) {
          view <- nth_looping ws (i-e);
          com <- nth witness cs i;
          valid_com <- valid_com /\ (verify view com);
        }
        i <- i + 1;
      }
      v <- Decomp.verify(c, vs', e, ys');

      ret <- None;
      if (v /\ valid_com /\ reconstruct ys' = y) {
        ret <- Some ((ys', cs), e, vs');
      }

      return ret;
    }
}.

axiom decomp_privacy:
  equiv[Privacy(Decomp).real ~ Privacy(Decomp).ideal : ={c, e, glob Decomp} ==> ={res, glob Decomp}].

equiv zkboo_shvzk:
    SHVZK(ZKBoo(Com, Decomp)).real ~ SHVZK(ZKBoo(Com, Decomp)).ideal :
    ={h, e, glob Com, glob Decomp} /\ R h{1} w{1} /\ e{2} \in dchallenge ==> ={res}.
proof.
  transitivity SHVZK_Inter.real
    (={h, e, w, glob Com, glob Decomp} /\ R h{1} w{1} /\ e{2} \in dchallenge ==> ={res})
    (={h, e, glob Com, glob Decomp} /\ R h{1} w{1} /\ e{2} \in dchallenge ==> ={res}).
  smt().
  smt().
  - proc.
    auto.
    inline ZKBoo(Com, Decomp).init.
    inline ZKBoo(Com, Decomp).response.
    inline ZKBoo(Com, Decomp).verify.
    inline SHVZK_Inter.PZK.real. 
    auto.
    call (:true). auto.
    while (={valid_com} /\ e1{1} = e{2} /\ cs0{1} = cs{2} /\ i{2} = i0{1} /\ ws{1} = vs{2}). sim.
    auto.
    (* fission{1} 9 @ 2,4. *)
    while (={i, cs, glob Com} /\
           forall i, (if (in_dom_f n e{2} i) then (nth witness ZKBoo.ws{1} i = nth_looping vs{2} (i - e{2})) else true)).
    - if{2}.
      + auto.
        call(:true).
        skip; smt().
      + auto.
        call Com_hiding_alt.
        skip; progress.
    auto.
    call (:true).
    call (:true).
    auto; progress.
    smt.
    smt.

  transitivity SHVZK_Inter.ideal
    (={h, e, glob Com, glob Decomp} /\ R h{1} w{1} /\ e{2} \in dchallenge ==> ={res})
    (={h, e, glob Com, glob Decomp} /\ e{2} \in dchallenge ==> ={res}); last first.
  (* Prove ideal ~ Inter.ideal *)
  - proc. 
    inline ZKBoo(Com, Decomp).simulator ZKBoo(Com, Decomp).verify SHVZK_Inter.PZK.ideal.
    auto.
    call (:true); auto.
    while (={valid_com, ws} /\ cs{1} = cs0{2} /\ i{1} = i0{2} /\ e{1} = e1{2}); auto.
    while (={cs, vs, i, glob Com} /\ e{1} = e0{2} /\
           forall i, (if (in_dom_f n e0{2} i) then (nth_looping vs{1} i = nth_looping vs{2} i) else true)).
    - if{2}.
      + auto.
        call (:true).
        skip; progress. 
      + auto.
        call Com_hiding_alt.
        skip; progress.
    auto.
    call (:true); auto.
    progress.
    smt.
    
  (* Prove precondition and post conditions*)
  smt().
  smt().

  (* Prove Inter.real ~ Inter.ideal *)
  proc.
  auto.
  call (:true).
  while (={valid_com, i, e, cs} /\
           forall i, (if (in_dom_f n e{2} i) then (nth_looping vs{1} (i - e{2}) = nth_looping ws{2} (i - e{2})) else true)).
  - auto; smt().
  auto.
  while (={cs, i, glob Com, vs, e}).
           (* forall i, (if (in_dom_f n e{1} i) then (nth_looping vs{1} (i) = nth_looping vs{2} i) else true)). *)
  - if{1}.
    + auto.
      call (:true).
      by skip. 
    + auto.
      call Com_hiding_alt.
      skip; progress.
  auto.
  call decomp_privacy.
  auto; progress.
qed.

(* local module SoundnessInter = { *)
(*   module ZK = ZKBoo(Com, Decomp) *)
(*   module BGame = BindingGame(Com) *)
(*   proc extract_views(h : statement, m : message, zs : response list) = { *)
(*     var i, v, valid, cons; *)
(*     i <- 0; *)
(*     valid <- true; *)
(*     while (i < n) { *)
(*       v <- ZK.verify(h, m , i, nth witness zs i); *)
(*       valid <- valid /\ v; *)
(*     } *)

(*     cons <- BGame.bind_three(c1, c2, c3, (w1, k1), (w1', k1'), (w2, k2), (w2', k2'), (w3, k3), (w3', k3')); *)

(*     return v1 /\ v2 /\ v3; *)
(*   } *)

(*   proc main(h : statement, m : message, z1 z2 z3 : response) = { *)
(*     var v, w, w_get, ret; *)
(*     v <- extract_views(h, m, z1, z2, z3); *)
(*     w <- ZK.witness_extractor(h, m, [1;2;3], [z1;z2;z3]); *)

(*     if (w = None \/ !v) { *)
(*       ret <- false; *)
(*     } else{ *)
(*       w_get <- oget w; *)
(*       ret <- R h w_get; *)
(*     } *)
(*     return ret; *)
(*   } *)
(* }. *)

(* local equiv soundness_inter : *)
(*   Sigma.SpecialSoundness(ZKBoo(Com)).main ~ SoundnessInter.main : *)
(*   ={h, m} /\ c{1} = [1;2;3] /\ z{1} = [z1{2};z2{2};z3{2}] ==> ={res}. *)
(* proof. *)
(*   proc. *)
(*   sp. *)
(*   swap{2} 1 1. *)
(*   rcondt{1} 1. auto. *)
(*   rcondt{1} 7. auto. call (:true). auto. auto. *)
(*   rcondt{1} 13. auto. call (:true). auto. auto. call (:true). auto. auto. *)
(*   rcondf{1} 19. auto. call (:true). auto. auto. call (:true). auto. auto. call (:true). auto. auto. *)
(*   inline SoundnessInter.extract_views. *)
(*   swap{2} [7..9] 5. *)
(*   swap{2} 1 13. *)
(*   sp. *)
(*   wp. call (:true). sim. *)
(*   wp. call (:true). sim. *)
(*   wp. call (:true). sim. *)
(*   wp. call (:true). sim. *)
(*   auto; progress. *)
(*   inline *. *)
(*   auto; smt(). *)
(* qed. *)

lemma soundness h a vs' es &m:
    size vs' = size es /\
    (forall v, v \in vs' => size v = d) /\
    (forall i, 0 <= i < n => (i \in in_doms_f n es i) (* Must reveal all views *)
    =>
    Pr[Sigma.SpecialSoundness(ZKBoo(Com, Decomp)).main(h, a, es, vs') @ &m : res] = 1%r.

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
