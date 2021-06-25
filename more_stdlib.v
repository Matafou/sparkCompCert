Require Import SetoidList.
Require Import LibHyps.LibHyps LibHyps.LibHypsNaming
        Sorted ZArith List.

Local Open Scope autonaming_scope.
Import ListNotations.

(* 
Ltac rename_hyp_2 n th :=
  match th with
  | Nat.eqb ?x ?y = _ => name(`_Neqb` ++ x#n ++ x#n)
  | _ = Nat.eqb ?x ?y => name(`_Neqb` ++ x#n ++ x#n)
  end.
 *)


Ltac rename_hyp1 n th :=
  match th with
  | cons ?e ?l => name (e#(S n) ++ l#(S n))
  | pair ?a ?b => name (a#(S n) ++ b#(S n))
  | List.In ?e ?l => name (`_lst_in` ++ e#n ++ l#n)
  | InA _ ?e ?l => name (`_inA` ++ e#n ++ l#n)
  | @Forall _ ?P ?x => name (`_lst_forall` ++ P#n ++ x#n)
  | @Forall2 _ _ _ ?x ?y => name (`_lst_forall` ++ x#n ++ y#n)
  | @StronglySorted _ ?ord ?l => name (`_strgSorted` ++ l#n)
  | NoDupA _ ?l => name (`_NoDupA` ++ l#n)
  | NoDup ?l => name (`_nodup` ++ l#n)
  | Zeq_bool ?x1 ?x2 => name(`_Zeqb` ++ x1#n ++ x2#n)
  end.

Ltac rename_depth ::= constr:(1).


Ltac rename_hyp_local n th :=
  match th with
  | ?a = ?b => name (`eq` ++ a#n ++ b#n)
  | _ => rename_hyp1 n th
  end.

Local Ltac rename_hyp ::= rename_hyp_local.

(* All elements of a sorted list are smaller or equal to the first
   element. If the ordering is reflexive. *)
Lemma increasing_order_In A : forall ord (stk:list A) (hd:A),
    StronglySorted ord (hd::stk) ->
    List.Forall (fun elt => elt = hd \/ ord hd elt) (hd::stk).
Proof.
  intros /sng.
  inversion h_strgSorted_ /sng.
  constructor 2.
  - left;reflexivity.
  - apply List.Forall_forall.
    intros /sng.
    right.
    rewrite List.Forall_forall in h_lst_forall_.
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
  intros;split;intros /sng.
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
  intros /sng.
  split;intro /sng.
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

Ltac rename_depth ::= constr:(2%nat).

  
Lemma Zneq_bool_true_iff: forall x y : Z, x <> y <-> Zneq_bool x y = true.
Proof.
  intros;split;intros /sng.
  - red in h_neq_x_y_.
    rewrite <- Z.compare_eq_iff in h_neq_x_y_.
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
  intros x y /sng.
  destruct (Z.eq_decidable x y) /ng.
  - generalize heq_x_y_.
    intro  /ng.
    apply Zneq_bool_false_iff in heq_x_y_.
    apply Zeq_is_eq_bool in heq_x_y_0.
    rewrite heq_x_y_, heq_x_y_0.
    reflexivity.
  - generalize h_neq_x_y_.
    intro  /sng.
    apply Zneq_bool_true in h_neq_x_y_.
    apply Zeq_is_neq_bool in h_neq_x_y_0.
    rewrite h_neq_x_y_, h_neq_x_y_0.
    reflexivity.
Qed.


Lemma stack_NoDupA_prefix: forall A R, forall CE1 CE2 : list A, NoDupA R (CE1 ++ CE2) -> NoDupA R CE1.
Proof.
  intros until CE2 /sng.
  revert CE1.
  induction CE2;intros /sng.
  - rewrite app_nil_r in h_NoDupA_app_.
    assumption.
  - apply h_all_NoDupA_.
    apply NoDupA_split with (x:=a);auto.
Qed.
  

Ltac rename_depth ::= constr:(2%nat).

Lemma stack_NoDupA_sublist: forall A R, forall CE1 CE2 : list A, NoDupA R (CE1 ++ CE2) -> NoDupA R CE2.
  induction CE1;intros /sng.
  - cbn in h_NoDupA_app_.
    assumption.
  - inversion h_NoDupA_app_ /sng.
    apply h_all_NoDupA_;auto.
Qed.

Lemma Forall_impl_strong : forall A (P Q : A -> Prop) (l: list A),
    (forall a, List.In a l -> P a -> Q a) ->
    Forall P l ->
    Forall Q l.
Proof.
  intros A P Q l H.
  repeat rewrite Forall_forall.
  repeat intro. 
  firstorder.
Qed.
Lemma Forall2_impl : forall A B (P Q : A -> B -> Prop) l l',
    (forall a b, P a b -> Q a b) ->
    Forall2 P l l' ->
    Forall2 Q l l'.
Proof.
  intros A B P Q l l' h_impl_ H. 
  induction H.
  - constructor.
  - constructor;auto.
Qed.
Lemma Forall2_impl_strong : forall A B (P Q : A -> B -> Prop) l l',
    Forall2 (fun a b => P a b  -> Q a b) l l' -> 
    Forall2 P l l' ->
    Forall2 Q l l'.
Proof.
  intros A B P Q l l' h_impl_ H.
  revert h_impl_.
  induction H;intros.
  - constructor.
  - inversion h_impl_;subst.
    constructor;auto.
Qed.
