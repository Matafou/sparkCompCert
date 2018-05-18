(**************************************************************************
* A user-customizable auto-naming scheme for hypothesis in Coq            *
* Author: Pierre Courtieu                                                 *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)
Require Import TacNewHyps.
(** This file is a set of tactical (mainly "!! t" where t is a tactic)
    and tactics (!intros, !destruct etc), that automatically rename
    new hypothesis after applying a tactic. The names chosen for
    hypothesis is programmable using Ltac. See examples in comment
    below.

    Comments welcome. *)

(* Comment this and the Z-dependent lines below if you don't want
   ZArith to be loaded *)
Require Import ZArith FunInd.

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
    | (ind1 _ _ _ _) => fresh "ind1"
    | (ind2 _ _) => fresh "ind2"
    | f1 _ _ = true => fresh "f_eq_true"
    | f1 _ _ = false => fresh "f_eq_false"
    | f1 _ _ = _ => fresh "f_eq"
    | ind3 ?h ?x => fresh "ind3_" h
    | ind3 _ ?x => fresh "ind3" (* if fresh h failed above *)

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

Ltac rename_hyp h ht := match true with true => fail | _ => fresh "hh" end.

Ltac rename_hyp_prefx h ht :=
  let res := rename_hyp h ht in
  fresh "h_" res.

(** ** Calls the (user-defined) rename_hyp + and fallbacks to some default namings if needed.
    [h] is the hypothesis (ident) to rename, [th] is its type. *)
Ltac fallback_rename_hyp h th :=
  match th with
    | _ => rename_hyp h th
    | true = beq_nat _ _ => fresh "beqnat_true"
    | beq_nat _ _ = true => fresh "beqnat_true"
    | false = beq_nat _ _ => fresh "beqnat_false"
    | beq_nat _ _ = false => fresh "beqnat_false"
    | beq_nat _ _ = _ => fresh "beqnat"
    | Zeq_bool _ _ = true => fresh "eq_Z_true"
    | Zeq_bool _ _ = false => fresh "eq_Z_false"
    | true = Zeq_bool _ _ => fresh "eq_Z_true"
    | false = Zeq_bool _ _ => fresh "eq_Z_false"
    | Zeq_bool _ _ = _ => fresh "eq_Z"
    | _ = Zeq_bool _ _ => fresh "eq_Z"
    | ?f = _ => fresh "eq_" f
    | ?f _ = _ => fresh "eq_" f
    | ?f _ _ = _ => fresh "eq_" f
    | ?f _ _ _ = _ => fresh "eq_" f
    | ?f _ _ _ _ = _ => fresh "eq_" f
    | ?f _ _ _ _ _ = _ => fresh "eq_" f
    | ?f _ _ _ _ _ _ = _ => fresh "eq_" f
    | ?f _ _ _ _ _ _ _ = _ => fresh "eq_" f
    | ?f _ _ _ _ _ _ _ _ = _ => fresh "eq_" f
    | _ = ?f => fresh "eq_" f
    | _ = ?f _  => fresh "eq_" f
    | _ = ?f _ _  => fresh "eq_" f
    | _ = ?f _ _ _  => fresh "eq_" f
    | _ = ?f _ _ _ _  => fresh "eq_" f
    | _ = ?f _ _ _ _ _  => fresh "eq_" f
    | _ = ?f _ _ _ _ _ _  => fresh "eq_" f
    | _ = ?f _ _ _ _ _ _ _  => fresh "eq_" f
    | _ = ?f _ _ _ _ _ _ _ _  => fresh "eq_" f
    | @eq bool _ true => fresh "eq_bool_true"
    | @eq bool _ false => fresh "eq_bool_false"
    | @eq bool true _ => fresh "eq_bool_true"
    | @eq bool false _ => fresh "eq_bool_false"
    | @eq bool _ _ => fresh "eq_bool"
    | @eq nat _ true => fresh "eq_nat_true"
    | @eq nat _ false => fresh "eq_nat_false"
    | @eq nat true _ => fresh "eq_nat_true"
    | @eq nat false _ => fresh "eq_nat_false"
    | @eq nat _ _ => fresh "eq_nat"
    | ?x <> _ => fresh "neq_" x
    | _ <> ?x => fresh "neq_" x
    | _ <> _ => fresh "neq"
    | _ = _ => fresh "eq"
    | _ /\ _ => fresh "and"
    | _ \/ _ => fresh "or"
    | @ex _ _ => fresh "ex"
    | ?x < ?y => fresh "lt_" x "_" y
    | ?x < _ => fresh "lt_" x
    | _ < _ => fresh "lt"
    | ?x <= ?y => fresh "le_" x "_" y
    | ?x <= _ => fresh "le_" x
    | _ <= _ => fresh "le"
    | ?x > ?y => fresh "gt_" x "_" y
    | ?x > _ => fresh "gt_" x
    | _ > _ => fresh "gt"
    | ?x >= ?y => fresh "ge_" x "_" y
    | ?x >= _ => fresh "ge_" x
    | _ >= _ => fresh "ge"

    | (?x < ?y)%Z => fresh "lt_" x "_" y
    | (?x < _)%Z => fresh "lt_" x
    | (_ < _)%Z => fresh "lt"
    | (?x <= ?y)%Z => fresh "le_" x "_" y
    | (?x <= _)%Z => fresh "le_" x
    | (_ <= _)%Z => fresh "le"
    | (?x > ?y)%Z => fresh "gt_" x "_" y
    | (?x > _)%Z => fresh "gt_" x
    | (_ > _)%Z => fresh "gt"
    | (?x >= ?y)%Z => fresh "ge_" x "_" y
    | (?x >= _)%Z => fresh "ge_" x
    | (_ >= _)%Z => fresh "ge"
    | ~ (_ = _) => fail 1(* h_neq already dealt by fallback *)
    | ~ ?th' => 
      let sufx := fallback_rename_hyp h th' in
      fresh "neg_" sufx
    | ~ ?th' => fresh "neg"
    (* Order is important here: *)
    | ?A -> ?B =>
      let nme := fallback_rename_hyp h B in
      fresh "impl_" nme
    | forall z:?A , ?B =>
      fresh "forall_" z
  end.

(* All hyps are prefixed by "h_" except equalities and non-equalities which
   are prefixed by "heq_" "hneq" respectively. *)
Inductive HypPrefixes :=
  | HypNone
  | HypH_
  | HypH.

(* One should rename this if needed *)
Ltac prefixable_eq_neq h th :=
  match th with
  | eq _ _ => HypH
  | ~ (eq _ _) => HypH
  | _ => HypH_
  end.

Ltac prefixable h th := prefixable_eq_neq h th.

(* Add prefix except if not a Prop or if prefixable says otherwise. *)
Ltac add_prefix h th nme :=
  match type of th with
  | Prop => 
    match prefixable h th with
    | HypH_ => fresh "h_" nme
    | HypH => fresh "h" nme
    | HypNone => nme
    end
  | _ => nme
  end.

Ltac fallback_rename_hyp_prefx h th :=
  let res := fallback_rename_hyp h th in
  add_prefix h th res.

(* Add this if you want hyps of typr ~ P to be renamed like if of type
   P but prefixed by "neg_" *)
Ltac rename_hyp_neg h th :=
  match th with
  | ~ (_ = _) => fail 1(* h_neq already dealt by fallback *)
  | ~ ?th' => 
    let sufx := fallback_rename_hyp h th' in
    fresh "neg_" sufx
  | ~ ?th' => fresh "neg"
  | _ => fail
  end.

Ltac autorename H :=
  match type of H with
  | ?th => 
    let dummy_name := fresh "dummy" in
    rename H into dummy_name; (* this renaming makes the renaming more or less
                                 idempotent, it is backtracked if the
                                 rename_hyp below fails. *)
    let newname := fallback_rename_hyp_prefx dummy_name th in
    rename dummy_name into newname
  | _ => idtac (* "no renaming pattern for " H *)
  end.
  
Ltac rename_new_hyps tac := tac_new_hyps tac autorename.

(* Need a way to rename or revert but revert needs to be done in the
   other direction (so better do ";; autorename ;!; revertHyp"), and
   may fail if something depends on the reverted hyp. So we should
   revert everything depending on the unrenamed hyp. *)
Ltac revert_if_norename H :=
  let t := type of H in
  match type of t with
  | Prop => match goal with
            | _ =>  let x := fallback_rename_hyp_prefx H t in idtac
            (* since we are only in prop it is almost never the case
               that something depends on H but if this happens we revert
               everything that does. *)
            | _ => try revert dependent H
            end
  | _ => idtac
  end.

(* two renaming tactical with different priorities wrt ";". !! binds
   stronger than ";", "!" bind weaker than ";". *)
Tactic Notation (at level 3) "!!" tactic3(Tac) := (Tac ;!; revert_if_norename ;; autorename).
Tactic Notation (at level 0) "!" tactic(Tac) := (Tac ;!; revert_if_norename ;; autorename).
(* !!! tac performs tac, then subst with new hypothesis when possible,
   then rename remaining new hyps. "!!!" binds string than ";" *)
Tactic Notation "!!!" tactic3(Tac) := (Tac ;; substHyp ;!; revert_if_norename ;; autorename).

(* Same as !!! + move hyp to the top of the goal if it is Type-sorted. *)
Tactic Notation (at level 4) "!!!!" tactic4(Tac) :=
  (Tac ;; substHyp ;!; revert_if_norename ;; autorename ;; move_up_types).
  (* (tac1 ;; (fun h => substHyp h||(move_up_types h;autorename h))). *)

(* subst or revert, revert is done from older to newer *)
Tactic Notation (at level 4) "??" tactic4(tac1) :=
  (tac1 ;; substHyp ;!; revertHyp).



(* subst or revert, revert is done from older to newer *)
Tactic Notation (at level 4) "?!" tactic4(tac1) :=
  ((tac1 ;; substHyp ;!; revert_if_norename) ;; autorename).

Ltac rename_all_hyps :=
  let renam H := autorename H in
  let hyps := all_hyps in
  map_hyps renam hyps.


(* A full example: *)
(*
Ltac rename_hyp_2 h th :=
  match th with
  | true = false => fresh "trueEQfalse"
  end.

Ltac rename_hyp ::= rename_hyp_2.

Lemma foo: forall x y,
    x <= y -> 
    x = y -> 
    ~x = y -> 
    ~1 < 0 ->
    (true=false) ->
    (False -> (true=false)) ->
    forall z t:nat, IDProp -> 
      (0 < 1 -> ~(true=false)) ->
      (forall w w',w < w' -> ~(true=false)) ->
      (0 < 1 -> ~(1<0)) ->
      (0 < 1 -> 1<0) -> 0 < z.
  (* auto naming at intro: *)
  !intros.
   Undo.
  (* auto naming + subst when possible at intro: *)
  !!!intros.
  Undo.
  (* intros first, rename after: *)
  intros.
  rename_all_hyps.
  Undo.
  (* intros first, rename some hyp only: *)
  intros.
  autorename H0.
  Undo 3.
  (* put !! before a (composed)tactic to rename all new hyps: *)
  intros;; (fun h => substHyp h||(move_up_types h;autorename h)).
  Undo.
  intros until 3.
  !destruct H eqn:?;intros.
  Undo.
  !!destruct H eqn:?;intros.
  Undo.
  ?!(destruct H eqn:?;intros).
Abort.
*)