Require Import TacNewHyps.
Require Import LibHypsNaming.
Require Import LibDecomp.
Tactic Notation "decomp" constr(c) := (!!decompose_clear c).
(*
Lemma foo : forall x, { aa:nat | (aa = x /\ x=aa) & (aa = aa /\ aa= x) } -> False.
Proof.
  intros x H. 
  decomp H.
Abort.

Lemma foo : { aa:False & True  } -> False.
Proof.
  intros H. 
  decomp H.
Abort.


Lemma foo : { aa:False & True & False  } -> False.
Proof.
  intros H. 
  decomp H.
Abort.
*)
  
(** Some more tactic not specially dedicated to renaming. *)

(* This performs the map from "top" to "bottom" (from older to younger hyps). *)
Ltac map_hyps_rev tac hs :=
  idtac;
  let rec step H hs := tac H ; next_hyp hs step idtac in
  next_hyp hs step idtac.

Ltac map_all_hyps tac := map_hyps tac all_hyps.
Ltac map_all_hyps_rev tac := map_hyps_rev tac all_hyps.

(* A tactic which moves up a hypothesis if it sort is Type or Set. *)
Ltac move_up_types H := match type of H with
                        | ?T => match type of T with
                                | Prop => idtac
                                | Set => move H at top
                                | Type => move H at top
                                end
                        end.

(* Iterating the tactic on all hypothesis. Moves up all Set/Type
   variables to the top. Really useful with [Set Compact Context]
   which is no yet commited in coq-trunk. *)
Ltac up_type := map_all_hyps_rev move_up_types.
