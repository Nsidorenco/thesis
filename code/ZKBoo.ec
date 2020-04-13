(* Formalization of ZKBoo Sigma-protocol *)
require import AllCore Distr List DInterval Decompose.
require (****) SigmaProtocols.
require import Commitment.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

(* TODO index into view *)
(* TODO constuct random tape *)
(* pred valid_view w1 w2 k1 k2 = forall j, w1 = phi_decomp *)

type statement  = (circuit * int).
type witness    = int.
type message    = output * output * output * commitment * commitment * commitment.
type challenge  = int.
type response   = secret_key * secret_key.

op R_DL h w     = let (c, h') = h in (h' = eval_circuit c [w]).

clone import SigmaProtocols as Sigma with
  type SigmaProtocols.statement <- statement,
  type SigmaProtocols.witness <- witness,
  type SigmaProtocols.message <- message,
  type SigmaProtocols.challenge <- challenge,
  type SigmaProtocols.response <- response,

  op SigmaProtocols.R = R_DL,
  op SigmaProtocols.dchallenge = [1..3]
  proof *.
  realize SigmaProtocols.dchallenge_llfuni.
      (* TODO: by [dt_ll, dt_funi] *)
      split. apply dinter_ll. trivial. apply dinter_uni. qed.
export SigmaProtocols.
