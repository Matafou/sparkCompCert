Require Import LibHypsNaming Sorted ZArith.

(* my lists *)
Inductive mypair {A:Type} : Type := specprod : nat -> A -> mypair.
Notation "[ x '<-' y ]" := (specprod x y) : list_scope.
Inductive speclist : Type :=  specnil : speclist | speccons : forall {A:Type}, @mypair A -> speclist -> speclist.
Notation " [ ] " := specnil (format "[ ]") : list_scope.
Notation " [ x ] " := (speccons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (speccons x .. (speccons y specnil) ..) : list_scope.
Open Scope list_scope.
Check [1<-true].
Check [1<-true].
Check [ [1<-true] ; [2<-4] ].

(* Notation " [ '(' x '<-' x2 ')' ';' .. ';' '(' y '<-' y2 ')' ] " := ((speccons x x2) .. (speccons y y2 specnil) ..) : list_scope. *)

Open Scope list_scope. 

Ltac assert_reduced_body n x H t :=
  match constr:(n,t) with
  | (0%nat,forall x1, _) =>
    constr:(H x)
  | (1%nat,forall x1, _) =>
    constr:(fun x1 => H x1 x)
  | (2%nat,forall x1 x2, _) =>
    constr:(fun x1 x2 => H x1 x2 x)
  | (3%nat,forall x1 x2 x3, _) =>
    constr:(fun x1 x2 x3 => H x1 x2 x3 x)
  | (4%nat,forall x1 x2 x3 x4, _) =>
    constr:(fun x1 x2 x3 x4 => H x1 x2 x3 x4 x)
  | (5%nat,forall x1 x2 x3 x4 x5, _) =>
    constr:(fun x1 x2 x3 x4 x5 => H x1 x2 x3 x4 x5 x)
  | (6%nat,forall x1 x2 x3 x4 x5 x6, _) =>
    constr:(fun x1 x2 x3 x4 x5 x6 => H x1 x2 x3 x4 x5 x6 x)
  | (7%nat,forall x1 x2 x3 x4 x5 x6 x7, _) =>
    constr:(fun x1 x2 x3 x4 x5 x6 x7 => H x1 x2 x3 x4 x5 x6 x7 x)
  | (8%nat,forall x1 x2 x3 x4 x5 x6 x7 x8, _) =>
    constr:(fun x1 x2 x3 x4 x5 x6 x7 x8 => H x1 x2 x3 x4 x5 x6 x7 x8 x)
  | (9%nat,forall x1 x2 x3 x4 x5 x6 x7 x8 x9, _) =>
    constr:(fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => H x1 x2 x3 x4 x5 x6 x7 x8 x9 x)
  | (10%nat,forall x1 x2 x3 x4 x5 x6 x7 x8 x10, _) =>
    constr:(fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => H x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x)
  end.

Ltac spec_ n H x :=
  let t := type of H in
  let h := fresh H in
  let asserted := assert_reduced_body n x H t in
  specialize asserted.

Ltac spec H p :=
  match p with
  | [?n <- ?x] => spec_ n H x
  end.

Ltac lspec H l :=
  match l with
  | specnil => idtac
  | speccons [?n<-?x] ?l' => spec_ n H x ; lspec H l'
  end.

(* Tactic Notation "spec" hyp(h) constr(x)  := (spec h x). *)
Tactic Notation "spec" hyp(h) constr(x)  := (lspec h x).

(* Test:
Lemma foo: forall P Q (a:nat) (b:bool), (forall x y:bool,forall z t:nat, P x y z t -> Q x z t y) -> False. 
Proof.
  intros P Q a b H.
  spec H [[2<-a] ; [0 <- b]].
Abort.  
*)

(* All elements of a sorted list are smaller or equal to the first
   element. If the ordering is reflexive. *)
Lemma increasing_order_In A : forall ord (stk:list A) (hd:A),
    StronglySorted ord (hd::stk) ->
    List.Forall (fun elt => elt = hd \/ ord hd elt) (hd::stk).
Proof.
  !intros.
  !inversion H.
  constructor 2.
  - left;reflexivity.
  - apply List.Forall_forall.
    !intros.
    right.
    rewrite List.Forall_forall in H3.
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
  - red in hneq.
    rewrite <- Z.compare_eq_iff in hneq.
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
  - generalize hneq.
    !intro .
    apply Zneq_bool_true in hneq.
    apply Zeq_is_neq_bool in hneq0.
    rewrite hneq, hneq0.
    reflexivity.
Qed.
