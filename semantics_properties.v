Require Import LibHypsNaming.
Require Import semantics.
Import STACK.

Functional Scheme update_ind := Induction for update Sort Prop.
Functional Scheme updates_ind := Induction for updates Sort Prop.



Lemma updates_ok_none : forall f x v, updates f x v = None -> fetches x f = None.
Proof.
  !intros.
  !functional induction (updates f x v).
  - discriminate.
  - discriminate.
  - unfold id in *. (* scorie from libhyprenaming *)
    simpl.
    rewrite hbeqnat_false.
    apply IHo.
    assumption.
  - reflexivity.
Qed.

(* the none version could be solved by functiona inversion but it is
   ot applicable here due to a bug in Function with functors. *)
Lemma update_ok_none : forall f x v, update f x v = None -> fetch x f = None.
Proof.
  !intros.
  !functional induction (update f x v).
  - discriminate.
  - unfold fetch.
    eapply updates_ok_none;eauto.
Qed.


(* the none version could be solved by functiona inversion but it is
   ot applicable here due to a bug in Function with functors. *)
Lemma updateG_ok_none : forall f x v, updateG f x v = None -> fetchG x f = None.
Proof.
  !intros.
  !functional induction (updateG f x v).
  - discriminate.
  - discriminate.
  - unfold id in *.
    simpl.
    apply update_ok_none in heq1.
    rewrite heq1.
    auto.
  - reflexivity.
Qed.

Lemma updates_ok_same: forall sto id v sto',
    updates sto id v = Some sto'
    -> fetches id sto' = Some v.
Proof.
  intros until v.
  !functional induction (updates sto id v);!intros;simpl in *;intros.
  - !invclear heq;simpl.
    rewrite hbeqnat_true.
    reflexivity.
  - !invclear heq;simpl.
    !invclear heq0;simpl.
    rewrite hbeqnat_false.
    apply IHo.
    assumption.
  - discriminate.
  - discriminate.
Qed.

Lemma update_ok_same: forall f id v f',
    update f id v = Some f'
    -> fetch id f' = Some v.
Proof.
  intros until v.
  !functional induction (STACK.update f id v);destruct f;simpl in *;intros.
  - !invclear H;simpl.
    apply updates_ok_same in heq.
    unfold fetch.
    simpl.
    assumption.
  - discriminate.
Qed.

Lemma updateG_ok_same: forall s id v s',
    updateG s id v = Some s'
    -> fetchG id s' = Some v.
Proof.
  intros until v.
  !functional induction (updateG s id v);simpl;intros.
  - !invclear H;simpl.
    apply update_ok_same in heq.
    rewrite heq.
    reflexivity.
  - !invclear H;simpl.
    specialize (IHo _ heq).
    destruct (fetch x f) eqn:h.
    + apply update_ok_none in heq0.
      rewrite heq0 in h;discriminate.
    + assumption.
  - discriminate.
  - discriminate.
Qed.



Lemma updates_ok_others: forall sto id v sto',
    updates sto id v = Some sto'
    -> forall id' v',
      id<>id'
      -> fetches id' sto = Some v'
      -> fetches id' sto' = Some v'.
Proof.
  intros until v.
  !functional induction (updates sto id v);!intros;simpl in *;intros.
  - !invclear heq0;simpl.
    simpl in *.
    rewrite -> NPeano.Nat.eqb_eq in hbeqnat_true.
    subst.
    apply NPeano.Nat.neq_sym in hneq.
    rewrite <- NPeano.Nat.eqb_neq in hneq.
    rewrite hneq in *.
    assumption.
  - !invclear heq1;simpl.
    destruct (NPeano.Nat.eq_dec id' y).
    + subst.
      rewrite NPeano.Nat.eqb_refl in *.
      assumption.
    + rewrite <- NPeano.Nat.eqb_neq in n.
      rewrite n in *.
      eapply IHo;eauto.
  - discriminate.
  - discriminate.
Qed.

(* xxx + Name hypothesis. *)
Lemma update_ok_others: forall f id v f',
    update f id v = Some f'
    -> fetch id f' = Some v.
Proof.
  intros until v.
  !functional induction (STACK.update f id v);destruct f;simpl in *;intros.
  - !invclear H;simpl.
    apply updates_ok_others in heq.
    unfold fetch.
    simpl.
    assumption.
  - discriminate.
Qed.

Lemma updateG_ok_others: forall s id v s',
    updateG s id v = Some s'
    -> fetchG id s' = Some v.
Proof.
  intros until v.
  !functional induction (updateG s id v);simpl;intros.
  - !invclear H;simpl.
    apply update_ok_others in heq.
    rewrite heq.
    reflexivity.
  - !invclear H;simpl.
    specialize (IHo _ heq).
    destruct (fetch x f) eqn:h.
    + apply update_ok_none in heq0.
      rewrite heq0 in h;discriminate.
    + assumption.
  - discriminate.
  - discriminate.
Qed.



