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
Require Import ZArith.

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

(** "marks" hypothesis h of the current goal by putting id(..) on top
   of there types. *)
Ltac id_ify h := let th := type of h in change (id th) in h.

(** Unmarking one hyp. *)
Ltac unid H :=
  match type of H with
    | id ?th => change th in H
  end.

(** Unmarking all hyps *)
Ltac unidall :=
  repeat match goal with
    | H: id ?th |- _ => change th in H
  end.

(** Rename (and mark) all hypothesis using the current rename_hyp
    tactic. It does not rename hypothesis already marked (i.e. of type
    (id _)). *)
Ltac rename_norm :=
  repeat match goal with
           | H:_ |- _ =>
             match type of H with
               | id _ => fail 1 (** This hyp is marked, chose another one *)
               | ?th => let newname := rename_hyp H th in
                        rename H into newname;
                        change (id th) in newname
               (* If the custom renaming tactic failed, then try the fallback one *)
               | ?th => let newname := fallback_rename_hyp H th in
                        rename H into newname;
                        change (id th) in newname
             end
         end.



(* Mark all current hypothesis of the goal to prevent re-renaming hyps
   when calling renaming tactics multiple times.

   Typical use: mark all hyps but the one we want to destruct (say h),
   destruct h; rename all unmarked hyps except h, unmark all hyps.

   That is:

   idall ; unid h; destruct h; try id_ify h; rename_norm; unidall. *)
Ltac idall :=
  repeat match goal with
           | H:_ |- _ =>
             match type of H with
               | id _ => fail 1
               | ?th => change (id th) in H
             end
         end.


(** ** Renaming Tacticals *)

(** [!! tactic] (resp. [!! tactic h] and []:: tactic h1 h2) performs
  [tactic] (resp. [tactic h] and [tactic h1 h2]) and renames all new
  hypothesis. During the process all previously known hypothesis (but
  [h], [h1] and [h2]) are marked. It may happen that this mark get in
  the way during the execution of <<tactic>>. We might try to find a
  better way to mark hypothesis. *)
Tactic Notation "!!" tactic3(T) := idall; T ; rename_norm ; unidall.
Tactic Notation "!!" tactic3(T) constr(h) :=
  idall; unid h; (T h) ; try id_ify h; rename_norm ; unidall.
(* begin hide *)
Tactic Notation "!!" tactic3(T) constr(h) constr(h2) :=
  idall; unid h;unid h2; (T h h2) ;
  try id_ify h;try id_ify h2; rename_norm ; unidall.
(* end hide *)

(** ** Specific redefinition of usual tactics. *)

(** Note that for example !!induction h doesn not work because
 "destruct" is not a ltac function by itself, it is already a
 notation. Hence the special definitions below for this kind of
 tactics: induction ddestruct inversion etc. *)

(* decompose and ex and or at once. TODO: generalize. *)
Tactic Notation "decomp" hyp(h) :=
  !! (fun x => decompose [and ex or] x; clear x) h.
Tactic Notation "!induction" constr(h) := !! (fun x => induction x) h.
Tactic Notation "!functional" "induction" constr(h) :=
   !! (functional induction h).
Tactic Notation "!functional" "inversion" constr(h) :=
  !! (fun x => functional inversion x) h.
Tactic Notation "!destruct" constr(h) := !! (destruct h).
Tactic Notation "!intros" := idall;intros;rename_norm;unidall.
Tactic Notation "!intro" := idall;intro;rename_norm;unidall.
Tactic Notation "!inversion" hyp(h) := !! (inversion h;subst).
Tactic Notation "!invclear" hyp(h) := !! (inversion h;clear h;subst).
Tactic Notation "!assert" constr(h) := !! (assert h).

