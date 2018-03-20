Require Import SetoidList.
Require Import sparkfrontend.LibHypsNaming Sorted ZArith List.



Ltac rename_hyp1 h th :=
  match th with
  | List.In ?e ?l => fresh "lst_in_" e "_" l
  | List.In ?e _ => fresh "lst_in_" e
  | List.In _ _ => fresh "lst_in"
  | InA _ ?e ?l => fresh "inA_" e "_" l
  | InA _ ?e _ => fresh "inA_" e
  | InA _ _ _ => fresh "inA"
  | @Forall _ ?P ?x => fresh "lst_forall_" P "_" x
  | @Forall _ _ ?x => fresh "lst_forall_" x
  | @Forall _ ?P _ => fresh "lst_forall_" P
  | @Forall _ _ _ => fresh "lst_forall"
  | @StronglySorted _ ?ord ?l => fresh "strgSorted_" l
  | @StronglySorted _ ?ord ?l => fresh "strgSorted"
  | NoDupA _ ?l => fresh "NoDupA_" l
  | NoDupA _ _ => fresh "NoDupA"
  end.



Ltac rename_hyp ::= rename_hyp1.

(* All elements of a sorted list are smaller or equal to the first
   element. If the ordering is reflexive. *)
Lemma increasing_order_In A : forall ord (stk:list A) (hd:A),
    StronglySorted ord (hd::stk) ->
    List.Forall (fun elt => elt = hd \/ ord hd elt) (hd::stk).
Proof.
  !intros.
  !inversion h_strgSorted.
  constructor 2.
  - left;reflexivity.
  - apply List.Forall_forall.
    !intros.
    right.
    rewrite List.Forall_forall in h_lst_forall_stk.
    auto.
Qed.

Open Scope Z_scope.


Lemma neq_sym A :  forall x y : A, (x = y -> False) -> y = x -> False.
Proof.
  auto.
Qed.

Add Parametric Relation A: A (fun x y : A => x <> y)
    symmetry proved by (neq_sym A)
as toto.

(* FIXME: replace Z(n)eq_bool (which seems more or less deprecated) by
   (not) Z.eqb instead. *)
Lemma Zneq_bool_false_iff: forall x y : Z, x = y <-> Zneq_bool x y = false.
Proof.
  !intros;split;!intros.
  -  subst.
     unfold Zneq_bool.
     rewrite Z.compare_refl;auto.
  - unfold Zneq_bool in *.
    destruct (x ?= y) eqn:h; try discriminate.
    apply Z.compare_eq_iff.
    assumption.
Qed.


Lemma Zeq_is_neq_bool : forall x y : Z, x <> y <-> Zeq_bool x y = false.
Proof.
  !intros.
  split;!intro.
  - destruct (Zeq_bool x y) eqn:h.
    + apply Zeq_bool_eq in h.
      contradiction.
    + reflexivity.
  - apply Zeq_bool_neq.
    assumption.
Qed.


Lemma Zneq_bool_false :  forall x y : Z, x = y -> Zneq_bool x y = false.
Proof.
  intros x y H.
  apply Zneq_bool_false_iff;easy.
Qed.

  
Lemma Zneq_bool_true_iff: forall x y : Z, x <> y <-> Zneq_bool x y = true.
Proof.
  !intros;split;!intros.
  - red in hneq_x.
    rewrite <- Z.compare_eq_iff in hneq_x.
    unfold Zneq_bool.
    destruct (x ?= y); auto.
  - unfold Zneq_bool in *.
    destruct (x ?= y) eqn:h; try discriminate.
    + rewrite  -> Z.compare_lt_iff in h.
      apply Z.lt_neq;auto.
    + rewrite -> Z.compare_gt_iff in h.
      symmetry.
      apply Z.lt_neq;auto.
Qed.

Lemma Zneq_bool_true :  forall x y : Z, x <> y -> Zneq_bool x y = true.
Proof.
  intros x y H.
  apply Zneq_bool_true_iff;easy.
Qed.

Lemma Zeq_bool_Zneq_bool : forall x y, Zeq_bool x y = negb (Zneq_bool x y).
Proof.
  !intros x y.
  !destruct (Z.eq_decidable x y).
  - generalize heq_x.
    !intro .
    apply Zneq_bool_false_iff in heq_x.
    apply Zeq_is_eq_bool in heq_x0.
    rewrite heq_x, heq_x0.
    reflexivity.
  - generalize hneq_x.
    !intro .
    apply Zneq_bool_true in hneq_x.
    apply Zeq_is_neq_bool in hneq_x0.
    rewrite hneq_x, hneq_x0.
    reflexivity.
Qed.
