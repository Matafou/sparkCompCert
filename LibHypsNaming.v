(**************************************************************************
* A user-customizable auto-naming scheme for hypothesis in Coq            *
* Author: Pierre Courtieu                                                 *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)

(** This file is a set of tactical (mainly "!! t" where t is a tactic)
    and tactics (!intros, !destruct etc), that automatically rename
    new hypothesis after applying a tactic. The names chosen for
    hypothesis is programmable using Ltac. See examples in comment
    below.

    Comments welcome. *)

(* Comment this and the Z-dependent lines below if you don't want
   ZArith to be loaded *)
Require Import ZArith FunInd.

(** ** The default fallback renaming strategy 
  This is used if the user-defined renaing scheme fails to give a name
  to a hypothesis. [th] is the type of the hypothesis. *)
Ltac fallback_rename_hyp h th :=
  match th with

    | true = beq_nat _ _ => fresh "hbeqnat_true"
    | beq_nat _ _ = true => fresh "hbeqnat_true"
    | false = beq_nat _ _ => fresh "hbeqnat_false"
    | beq_nat _ _ = false => fresh "hbeqnat_false"
    | beq_nat _ _ = _ => fresh "hbeqnat"
    | Zeq_bool _ _ = true => fresh "heq_Z_true"
    | Zeq_bool _ _ = false => fresh "heq_Z_false"
    | true = Zeq_bool _ _ => fresh "heq_Z_true"
    | false = Zeq_bool _ _ => fresh "heq_Z_false"
    | Zeq_bool _ _ = _ => fresh "heq_Z"
    | _ = Zeq_bool _ _ => fresh "heq_Z"
    | ?f = _ => fresh "heq_" f
    | ?f _ = _ => fresh "heq_" f
    | ?f _ _ = _ => fresh "heq_" f
    | ?f _ _ _ = _ => fresh "heq_" f
    | ?f _ _ _ _ = _ => fresh "heq_" f
    | ?f _ _ _ _ _ = _ => fresh "heq_" f
    | ?f _ _ _ _ _ _ = _ => fresh "heq_" f
    | ?f _ _ _ _ _ _ _ = _ => fresh "heq_" f
    | ?f _ _ _ _ _ _ _ _ = _ => fresh "heq_" f
    | _ = ?f => fresh "heq_" f
    | _ = ?f _  => fresh "heq_" f
    | _ = ?f _ _  => fresh "heq_" f
    | _ = ?f _ _ _  => fresh "heq_" f
    | _ = ?f _ _ _ _  => fresh "heq_" f
    | _ = ?f _ _ _ _ _  => fresh "heq_" f
    | _ = ?f _ _ _ _ _ _  => fresh "heq_" f
    | _ = ?f _ _ _ _ _ _ _  => fresh "heq_" f
    | _ = ?f _ _ _ _ _ _ _ _  => fresh "heq_" f
    | @eq bool _ true => fresh "heq_bool_true"
    | @eq bool _ false => fresh "heq_bool_false"
    | @eq bool true _ => fresh "heq_bool_true"
    | @eq bool false _ => fresh "heq_bool_false"
    | @eq bool _ _ => fresh "heq_bool"
    | @eq nat _ true => fresh "heq_nat_true"
    | @eq nat _ false => fresh "heq_nat_false"
    | @eq nat true _ => fresh "heq_nat_true"
    | @eq nat false _ => fresh "heq_nat_false"
    | @eq nat _ _ => fresh "heq_nat"
    | _ <> _ => fresh "hneq"
    | _ = _ => fresh "heq"
    | _ /\ _ => fresh "h_and"
    | _ \/ _ => fresh "h_or"
    | @ex _ _ => fresh "h_ex"
    | ?x < ?y => fresh "h_lt_" x "_" y
    | ?x < _ => fresh "h_lt_" x
    | _ < _ => fresh "h_lt"
    | ?x <= ?y => fresh "h_le_" x "_" y
    | ?x <= _ => fresh "h_le_" x
    | _ <= _ => fresh "h_le"
    | ?x > ?y => fresh "h_gt_" x "_" y
    | ?x > _ => fresh "h_gt_" x
    | _ > _ => fresh "h_gt"
    | ?x >= ?y => fresh "h_ge_" x "_" y
    | ?x >= _ => fresh "h_ge_" x
    | _ >= _ => fresh "h_ge"

    | (?x < ?y)%Z => fresh "h_lt_" x "_" y
    | (?x < _)%Z => fresh "h_lt_" x
    | (_ < _)%Z => fresh "h_lt"
    | (?x <= ?y)%Z => fresh "h_le_" x "_" y
    | (?x <= _)%Z => fresh "h_le_" x
    | (_ <= _)%Z => fresh "h_le"
    | (?x > ?y)%Z => fresh "h_gt_" x "_" y
    | (?x > _)%Z => fresh "h_gt_" x
    | (_ > _)%Z => fresh "h_gt"
    | (?x >= ?y)%Z => fresh "h_ge_" x "_" y
    | (?x >= _)%Z => fresh "h_ge_" x
    | (_ >= _)%Z => fresh "h_ge"
  end.

(** ** The custom renaming tactic
  This tactic should be redefined along a coq development, it should
  return a fresh name build from an hypothesis h and its type th. It
  should fail if no name is found, so that the fallback scheme is
  called.

  Typical use, in increasing order of complexity, approximatively
  equivalent to the decreasing order of interest.

<<
Ltac my_rename_hyp h th :=
  match th with
    | (ind1 _ _ _ _) => fresh "h_ind1"
    | (ind2 _ _) => fresh "h_ind2"
    | f1 _ _ = true => fresh "hf_eq_true"
    | f1 _ _ = false => fresh "hf_eq_false"
    | f1 _ _ = _ => fresh "hf_eq"
    | ind3 ?h ?x => fresh "h_ind3_" h
    | ind3 _ ?x => fresh "h_ind3" (* if fresh h failed above *)

    (* Sometime we want to look for the name of another hypothesis to
       name h. For example here we want to rename hypothesis h into
       "type_of_foo" if there is some H of type [type_of foo = Some
       h]. *)
    | type => (* See if we find something of which h is the type: *)
              match reverse goal with
              | H: type_of ?x = Some h => fresh "type_of_" x
              end

    | _ => previously_defined_renaming_tac1 th (* cumulative with previously defined renaming tactics *)
    | _ => previously_defined_renaming_tac2 th
  end.

(* Overwrite the definition of rename_hyp using the ::= operator. :*)

Ltac rename_hyp ::= my_rename_hyp.>> *)

Ltac rename_hyp h ht := fail.


(* Add this if you want hyps of typr ~ P to be renamed like if of type
   P but prefixed by "neg_" *)
Ltac rename_hyp_neg h th :=
  match th with
  | ~ ?th' =>
    let nme := rename_hyp h th' in
    fresh "neg_" nme
  end.

(* Credit for the harvesting of hypothesis: Jonathan Leivant *)
Ltac harvest_hyps harvester := constr:(ltac:(harvester; constructor) : True).

Ltac revert_clearbody_all := 
  repeat lazymatch goal with H:_ |- _ => try clearbody H; revert H end.

Ltac all_hyps := harvest_hyps revert_clearbody_all.

Ltac next_hyp hs step last := 
  lazymatch hs with 
  | (?hs' ?H) => step H hs'
  | _ => last
  end.

Ltac map_hyps tac hs :=
  idtac;
  let rec step H hs := next_hyp hs step idtac; tac H in
  next_hyp hs step idtac.

(* Renames hypothesis H if it is not in old_hyps. Use user defined
   renaming scheme, and fall back to the default one of it fails. *)
Ltac rename_if_not_old old_hyps H :=
  lazymatch old_hyps with 
  | context[H] => idtac
  | _ =>
    match type of H with
    | ?th => 
      let dummy_name := fresh "dummy" in
      rename H into dummy_name; (* this renaming makes the renaming more or less
                                   idempotent, it is backtracked if the
                                   rename_hyp below fails. *)
        let newname := rename_hyp dummy_name th in
        rename dummy_name into newname
    | ?th => 
      let dummy_name := fresh "dummy" in
      rename H into dummy_name; (* this renaming makes the renaming more or less
                                   idempotent, it is backtracked if the
                                   rename_hyp below fails. *)
        let newname := fallback_rename_hyp dummy_name th in
        rename dummy_name into newname
    | _ => idtac (* "no renaming pattern for " H *)
    end
  end.

Ltac rename_new_hyps tac :=
  let old_hyps := all_hyps in
  let renam H := rename_if_not_old old_hyps H in
  tac;
  let new_hyps := all_hyps in
  map_hyps renam new_hyps.

Ltac rename_all_hyps :=
  let renam H := rename_if_not_old (I) H in
  let hyps := all_hyps in
  map_hyps renam hyps.

Ltac autorename H := rename_if_not_old (I) H.

Tactic Notation "!!" tactic3(Tac) := (rename_new_hyps Tac).
Tactic Notation "!!" tactic3(Tac) constr(h) :=
  (rename_new_hyps (Tac h)).

Ltac subst_if_not_old old_hyps H :=
  match old_hyps with
  | context [H] => idtac
  | _ => 
    match type of H with
    | ?x = ?y => subst x
    | ?x = ?y => subst y
    | _ => idtac
    end
  end.

Ltac subst_new_hyps tac :=
  let old_hyps := all_hyps in
  let substnew H := subst_if_not_old old_hyps H in
  tac
  ; let new_hyps := all_hyps in
    map_hyps substnew new_hyps.

(* do we need a syntax for this. *)
(* Tactic Notation "" tactic3(Tac) := subst_new_hyps Tac. *)

(* !!! tac performs tac, then subst with new hypothesis, then rename
remaining new hyps. *)
Tactic Notation "!!!" tactic3(Tac) := !! (subst_new_hyps Tac).


(** ** Renaming Tacticals *)

(** [!! tactic] (resp. [!! tactic h] and []:: tactic h1 h2) performs
  [tactic] (resp. [tactic h] and [tactic h1 h2]) and renames all new
  hypothesis. During the process all previously known hypothesis (but
  [h], [h1] and [h2]) are marked. It may happen that this mark get in
  the way during the execution of <<tactic>>. We might try to find a
  better way to mark hypothesis. *)

(* Tactic Notation "!!" tactic3(T) := idall; T ; rename_hyps. *)
(* Tactic Notation "!!" tactic3(T) constr(h) := *)
(*   idall; try unid h; (T h) ; try id_ify h; rename_hyps. *)
(* begin hide *)
(* Tactic Notation "!!" tactic3(T) constr(h) constr(h2) := *)
(*   idall; try unid h;try unid h2; (T h h2) ; *)
(*   try id_ify h;try id_ify h2; rename_hyps. *)
(* end hide *)

(** ** Specific redefinition of usual tactics. *)

(** Note that for example !!induction h doesn not work because
 "destruct" is not a ltac function by itself, it is already a
 notation. Hence the special definitions below for this kind of
 tactics: induction ddestruct inversion etc. *)


Ltac decomp_ex h :=
  match type of h with
  | @ex _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_ex h1
  | @sig _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_ex h1
  | @sig2 _ (fun x => _) (fun _ => _) => let x' := fresh x in
                                         let h1 := fresh in 
                                         let h2 := fresh in
                                         destruct h as [x' h1 h2];
                                         decomp_ex h1;
                                         decomp_ex h2
  | @sigT _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_ex h1
  | @sigT2 _ (fun x => _) (fun _ => _) => let x' := fresh x in
                                          let h1 := fresh in
                                          let h2 := fresh in
                                          destruct h as [x' h1 h2]; decomp_ex h1; decomp_ex h2
  | and _ _ => let h1 := fresh in let h2 := fresh in destruct h as [h1 h2]; decomp_ex h1; decomp_ex h2
  | or _ _ => let h' := fresh in destruct h as [h' | h']; [decomp_ex h' | decomp_ex h' ]
  | _ => idtac
  end.



(* decompose and ex and or at once. TODO: generalize. *)
(* clear may fail if h is not a hypname *)
(* Tactic Notation "decomp" hyp(h) :=
   (!! (idtac;decomp_ex h)). *) (* Why do I need this idtac? Without it no rename happens. *)

 Tactic Notation "decomp" constr(c) :=
   match goal with
   | _ => 
     let h := fresh "h_decomp" in
     pose proof c as h;
     (!! (idtac;decomp_ex c)); try clear h (* Why do I need this idtac? Without it no rename happens. *)
   end.
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

Tactic Notation "!induction" constr(h) := !! (induction h).
Tactic Notation "!functional" "induction" constr(h) :=
   !! (functional induction h).
Tactic Notation "!functional" "inversion" constr(h) :=
  !! (functional inversion h).
Tactic Notation "!destruct" constr(h) := !! (destruct h).

Tactic Notation "!destruct" constr(h) "!eqn:" ident(id) :=
  (!!(destruct h eqn:id; revert id));intro id.
Tactic Notation "!destruct" constr(h) "!eqn:?" := (!!(destruct h eqn:?)).

Tactic Notation "!inversion" hyp(h) := !!! (inversion h).
Tactic Notation "!invclear" hyp(h) := !!! (inversion h;clear h).
Tactic Notation "!assert" constr(h) := !! (assert h).

Tactic Notation "!intros" := !!intros.

Tactic Notation "!intro" := !!intro.

Tactic Notation "!intros" "until" ident(id)
  := intros until id; !intros.

Tactic Notation "!intros" simple_intropattern(id1)
  := !! intro id1.

Tactic Notation "!intros" ident(id1) ident(id2)
  := intros id1 id2; !intros.
Tactic Notation "!intros" ident(id1) ident(id2) ident(id3)
  := intros id1 id2 id3; !!intros.
Tactic Notation "!intros" ident(id1) ident(id2) ident(id3) ident(id4)
  := intros id1 id2 id3 id4; !!intros.

Tactic Notation "!intros" ident(id1) ident(id2) ident(id3) ident(id4) ident(id5)
  := intros id1 id2 id3 id4 id5; !!intros.
Tactic Notation "!intros" ident(id1) ident(id2) ident(id3) ident(id4) ident(id5) ident(id6)
  := intros id1 id2 id3 id4 id5 id6; !!intros.


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

