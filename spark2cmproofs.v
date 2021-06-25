Require Import FunInd ZArith Sorted Relations SetoidList.
Require Import compcert.common.Errors compcert.backend.Cminor
        compcert.lib.Integers compcert.common.Memory compcert.cfrontend.Ctypes.
Require Import spark.symboltable spark.eval.
Require Import sparkfrontend.function_utils LibHyps.LibHyps sparkfrontend.LibTac
        sparkfrontend.spark2Cminor sparkfrontend.semantics_properties
        sparkfrontend.compcert_utils sparkfrontend.more_stdlib
        sparkfrontend.chained_structure sparkfrontend.spark_utils.
Import Symbol_Table_Module.
Open Scope error_monad_scope.
Open Scope Z_scope.

Local Hint Resolve Z.divide_refl Z.divide_0_r Z.divide_factor_l Z.divide_factor_r: spark.


(* stdlib unicode binders are not boxed correctly imho. *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[' ∀  x  ..  y ,  '/' P ']'") : type_scope.
Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' ∃  '[ ' x  '/' ..  '/' y ,  ']' '/' P ']'") : type_scope.
Notation "'λ' x .. y , P" := (fun x => .. (fun y => P) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' λ  '[ ' x  '/' ..  '/' y ,  ']' '/' P ']'") : type_scope.
Notation "x ∨ y" := (x \/ y)
  (at level 85, right associativity,
   format "'[hv' x  '/' ∨  y ']'") : type_scope.
Notation "x ∧ y" := (x /\ y)
  (at level 80, right associativity,y at level 80,
   format "'[hv' x  '/' ∧  y ']'") : type_scope.
Notation "x → y" := (x -> y)
 (at level 99, y at level 200, right associativity,
   format "'[hv' x  '/' →  y ']'"): type_scope.
Notation "x ↔ y" := (x <-> y)
  (at level 95, no associativity,
     format "'[hv' x  '/' ↔  y ']'"): type_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70,format "'[hv' x  '/' ≠  y ']'") : type_scope.
Notation "x ≤ y" := (le x y) (at level 70, no associativity,format "'[hv' x  '/' ≤  y ']'").
Notation "x ≥ y" := (ge x y) (at level 70, no associativity,format "'[hv' x  '/' ≥  y ']'").

Ltac rename_sparkprf h th := fail.
Ltac rename_name_sparkprf h th := fail.

(** Hypothesis renaming stuff from other files + current file.
    DO NOT REDEFINE IN THIS FILE. Redefine rename_sparkprf instead. *)
Ltac LibHypsNaming.rename_hyp n th ::=
  match th with
  | _ => (rename_sparkprf n th)
  | _ => (spark_utils.rename_hyp_spark n th)
  | _ => (semantics_properties.rename_hyp_sem n th)
  | _ => (more_stdlib.rename_hyp1 n th)
  | _ => (spark2Cminor.rename_hyp1 n th)
  | _ => (compcert_utils.rename_hyp1 n th)
  | _ => (chained_structure.rename_chained n th)
  | _ => (LibHypsNaming.rename_hyp_neg n th)
  end.

Ltac LibHypsNaming.rename_hyp_with_name ::= rename_name_sparkprf.

Ltac rename_depth ::= constr:(2%nat).

(* Removal of uninformative equalities *)
Ltac remove_refl :=
  repeat
    match goal with
    | H: ?e = ?e |- _ => clear H
    end.

(* + exploiting equalities. *)
Ltac eq_same_clear :=
  repeat progress
         (remove_refl;
          (try match goal with
               | H: ?A = _ , H': ?A = _ |- _ => rewrite H in H'; (invclear H')
               | H: OK ?A = OK ?B |- _ => (invclear H)
               | H: Errors.OK ?A = Errors.OK ?B |- _ => invclear H
               | H: Some ?A = Some ?B |- _ => invclear H
               | H: OK ?A = RTE ?B |- _ => discriminate H
               | H: RTE ?B= OK ?A |- _ => discriminate H
               | H: ?A <> ?A |- _ => elim H;reflexivity
               end)).



(* basic notions coincides between compcert and spark *)
Lemma wordsize_ok : wordsize = Integers.Int.wordsize.
Proof. reflexivity. Qed.

Lemma modulus_ok: modulus = Integers.Int.modulus.
Proof. reflexivity. Qed.

Lemma half_modulus_ok: half_modulus = Integers.Int.half_modulus.
Proof. reflexivity. Qed.

Lemma max_unsigned_ok: max_unsigned = Integers.Int.max_unsigned.
Proof. reflexivity. Qed.

Lemma max_signed_ok: max_signed = Integers.Int.max_signed.
Proof. reflexivity. Qed.

Lemma min_signed_ok: min_signed = Integers.Int.min_signed.
Proof. reflexivity. Qed.

(* TODO: replace this by the real typing function *)
Definition type_of_name (stbl:symboltable) (nme:name): res type :=
  match nme with
  | Identifier astnum id =>
      match symboltable.fetch_exp_type astnum stbl with
        Some x => Errors.OK x
      | None =>  Error (msg "type_of_name: unknown type for astnum")
      end
  | IndexedComponent astnum x0 x1 =>
      match symboltable.fetch_exp_type astnum stbl with
        Some x => Errors.OK x
      | None =>  Error (msg "type_of_name: unknown type for astnum (indexed_component)")
      end
  | SelectedComponent astnum x0 x1 =>
      match symboltable.fetch_exp_type astnum stbl with
        Some x => Errors.OK x
      | None =>  Error (msg "type_of_name: unknown type for astnum (selected_component)")
      end
  end.

Local Open Scope autonaming_scope.

(** Hypothesis renaming stuff *)
Ltac rename_hyp1 n th :=
  match th with
  | ?a = ?b => name (`_eq` ++ a#(S n) ++ b#n) (* favoring lhs of equality *)
  (* TODO: remove when we remove type_of_name by the real one. *)
  | type_of_name _ _ = _ => name (`eq_type_of_name`)
  | Values.Val.bool_of_val ?v ?b => name (`_eq_bofv` ++ v#n ++ b#n)
  | CompilEnv.NoDup ?s => name (`_nodup_CE` ++ s#n)
  | CompilEnv.NoDup_G ?s => name (`_nodup_G_CE` ++ s#n)
  | CompilEnv.exact_levelG ?CE => name (`_exct_lvlG` ++ CE#n)
  (* | exp => name (`e`) bad idea: it is applied in leafs of terms *)
  (* | stmt => name (`stmt`) *)
  end.

(* This cannot work anymore because we do not carry the *name* of H. *)
Ltac rename_var_from_context h th :=
  match th with
  | Cminor.expr =>
      match goal with
      | H: transl_expr ?stbl ?CE ?x = Errors.OK h |- _ => name (x## ++ `_t`)
      | H: transl_name ?stbl ?CE ?x = Errors.OK h |- _ => name (x## ++ `_t`)
      end
  | AST.memory_chunk =>
      match goal with
      | H: compute_chnk ?stbl ?x = Errors.OK _ |- h => name (x## ++ `_chk`)
      end
  | SymTable_Exps.V =>
      match goal with
      | H: symboltable.fetch_exp_type (name_astnum ?x) = Some h |- _ => name (x## ++ `_type`)
      | H: symboltable.fetch_exp_type ?x _ = Some h |- _ => name (x## ++ `_type`)
      end
  | Values.val =>
      match goal with
      | H:  Cminor.eval_expr _ _ _ _ ?e h |- _ => name (e## ++ `_v`)
      end
  | value =>
      match goal with
      | H:  evalExp _ _ ?e h |- _ => name (e## ++ `_v`)
      end
  end.

Ltac rename_sparkprf ::= rename_hyp1.

Ltac rename_name_sparkprf ::= rename_var_from_context.

Lemma transl_value_det: forall v tv1 tv2,
    transl_value v tv1 -> transl_value v tv2 -> tv1 = tv2.
Proof.
  intros /sng.
  inversion h_transl_value_v_tv1_; inversion h_transl_value_v_tv2_;subst;auto;inversion H1;auto.
Qed.


(* clear may fail if h is not a hypname *)
(* Tactic Notation "decomp" constr(h) := *)
(*         (decompose [and ex or] h) /sng. *)
(* useless? *)
Lemma transl_value_tot: forall v,
    (exists b, v = Bool b \/ exists n, v = Int n)
    -> exists tv, transl_value v tv.
Proof.
  intros /sng.
  decomp h_ex_or_;subst.
  - destruct b;eexists;econstructor.
  - eexists;econstructor.
Qed.

Ltac rename_depth ::= constr:(2%nat).


Lemma transl_literal_ok1 : forall g (l:literal) v,
    evalLiteral l (OK v) ->
    forall sp t_v,
      Cminor.eval_constant g sp (transl_literal l) = Some t_v ->
      transl_value v t_v.
Proof.
  intros /sng.
  destruct l;simpl in *; eq_same_clear /sn.
  - inversion h_eval_literal_ /sng.
    inversion h_overf_check_v_ /sng.
    constructor.
  - destruct b;simpl in *;eq_same_clear /sn.
    + inversion h_eval_literal_;constructor.
    + inversion h_eval_literal_;constructor.
Qed.

Lemma transl_literal_ok2 : forall g (l:literal) v,
    evalLiteral l (OK v) ->
    forall sp t_v,
      transl_value v t_v ->
      eval_constant g sp (transl_literal l) = Some t_v.
Proof.
  intros /sng.
  destruct l;simpl in *;eq_same_clear /sng.
  - inversion h_eval_literal_ /sng.
    inversion h_overf_check_v_ /sng.
    inversion h_transl_value_v_t_v_ /sng.
    reflexivity.
  - destruct b;simpl in *;eq_same_clear.
    + inversion h_eval_literal_ /sng.
      inversion h_transl_value_v_t_v_ /sng.
      reflexivity.
    + inversion h_eval_literal_ /sng.
      inversion h_transl_value_v_t_v_ /sng.
      reflexivity.
Qed.

Lemma transl_literal_ok : forall g (l:literal) v,
    evalLiteral l (OK v) ->
    forall sp t_v,
      eval_constant g sp (transl_literal l) = Some t_v <->
        transl_value v t_v.
Proof.
  intros g l v H sp t_v.
  split.
  - apply transl_literal_ok1.
    assumption.
  - apply transl_literal_ok2.
    assumption.
Qed.


Ltac inv_if_intop op h :=
  match op with
  | Plus => invclear h
  | Minus => invclear h
  | Multiply => invclear h
  | Divide => invclear h
  end.

(* Transform hypothesis of the form do_range_check into disequalities. *)
(* shortening the name to shorten the tactic below *)
Notation rtc_binop := do_run_time_check_on_binop (only parsing).
Ltac inv_rtc :=
  repeat
    progress
    (try match goal with
         | H: rtc_binop ?op Undefined _ (OK _) |- _ => now inversion H
         | H: rtc_binop ?op _ Undefined (OK _) |- _ => now inversion H
         | H: rtc_binop ?op _ (ArrayV _) (OK _) |- _ => now inv_if_intop op H
         | H: rtc_binop ?op (ArrayV _) _ (OK _) |- _ => now inv_if_intop op H
         | H: rtc_binop ?op _ (RecordV _) (OK _) |- _ => now inv_if_intop op H
         | H: rtc_binop ?op (RecordV _) _ (OK _) |- _ => now inv_if_intop op H
         | H: rtc_binop ?op _ (Bool _) (OK _) |- _ => inv_if_intop op H
         | H: Math.binary_operation ?op _ (Bool _) = (Some _) |- _ => inv_if_intop op H
         | H: rtc_binop ?op (Bool _) _ (OK _) |- _ => inv_if_intop op H
         | H: Math.binary_operation ?op (Bool _) _ = (Some _) |- _ => inv_if_intop op H
         | H: overflowCheck _ (OK (Int _)) |- _ => invclear H
         | H: rangeCheck _ _ _ (OK (Int _)) |- _ => invclear H
         | H: in_bound _ _ true |- _ => invclear H
         | H:(_ >=? _) && (_ >=? _) = true |- _ =>
             rewrite andb_true_iff in H;
             try rewrite Z.geb_le in H;
             try rewrite Z.geb_le in H;
             let h1 := fresh "h_le_"in
             let h2 := fresh "h_le_"in
             destruct H as [h1 h2 ]
         | H:(_ <=? _) && (_ <=? _) = true |- _ =>
             rewrite andb_true_iff in H;
             try rewrite Z.leb_le in H;
             try rewrite Z.leb_le in H;
             let h1 := fresh "h_le_" in
             let h2 := fresh "h_le_" in
             destruct H as [h1 h2 ]
         end; auto 2).


(** In this section we prove that basic operators of SPARK behave,
    when they don't raise a runtime error, like Compcert ones. *)

Lemma not_ok: forall v1 v0 x,
    transl_value v1 x ->
    Math.unary_not v1 = Some v0 ->
    transl_value v0 (Values.Val.notbool x).
Proof.
  intros /sng.
  destruct v1;try discriminate;simpl in *;eq_same_clear /sng.
  destruct n;simpl in *;
  inversion h_transl_value_v1_x_;
  constructor /sng.
Qed.


Lemma and_ok: forall v1 v2 v0 x x0,
    transl_value v1 x ->
    transl_value v2 x0 ->
    Math.and v1 v2 = Some v0 ->
    transl_value v0 (Values.Val.and x x0).
Proof.
  intros /sng.
  destruct v1;simpl in *;try discriminate; destruct v2;simpl in *;try discriminate
  ;eq_same_clear /sng.
  destruct n;destruct n0;simpl
  ;inversion h_transl_value_v1_x_
  ;inversion h_transl_value_v2_x0_
  ; constructor.
Qed.

Lemma or_ok: forall v1 v2 v0 x x0,
    transl_value v1 x ->
    transl_value v2 x0 ->
    Math.or v1 v2 = Some v0 ->
    transl_value v0 (Values.Val.or x x0).
Proof.
  intros /sng.
  destruct v1;try discriminate; destruct v2;try discriminate;simpl in *;eq_same_clear /sng.
  destruct n;destruct n0;simpl
  ;inversion h_transl_value_v1_x_
  ;inversion h_transl_value_v2_x0_
  ; constructor.
Qed.


Definition check_overflow_value (v:value) :=
  match v with
  | Undefined => True
  | Int n => overflowCheck n (OK (Int n))
  | Bool n => True
  | ArrayV a => True(* FIXME *)
  | RecordV r => True (* FIXME *)
  end.

Ltac rename_hyp2 h th :=
  match th with
  | _ => rename_hyp1 h th
  | check_overflow_value _ => name (`_check_overf`)
  end.

Ltac rename_sparkprf ::= rename_hyp2.

Lemma eq_ok: forall v1 v2 v0 x x0,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    transl_value v1 x ->
    transl_value v2 x0 ->
    Math.eq v1 v2 = Some v0 ->
    transl_value v0 (Values.Val.cmp Integers.Ceq x x0).
Proof.
  intros /sng.
  destruct v1;try discriminate; destruct v2;try discriminate;simpl in *;eq_same_clear /sng.
  destruct (Z.eq_dec n n0) /sng.
  - inversion h_transl_value_v1_x_;subst;simpl.
    inversion h_transl_value_v2_x0_;subst;simpl.
    rewrite Zaux.Zeq_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    rewrite Integers.Int.eq_true.
    constructor.
  - rewrite Zaux.Zeq_bool_false;auto.
    unfold Values.Val.cmp.
    inversion h_transl_value_v2_x0_;subst;simpl.
    inversion h_transl_value_v1_x_;subst;simpl.
    rewrite Integers.Int.eq_false.
    + constructor.
    + apply repr_inj_neq.
      * inv_rtc.
      * inv_rtc.
      * assumption.
Qed.


Lemma neq_ok: forall v1 v2 v0 x x0,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    transl_value v1 x ->
    transl_value v2 x0 ->
    Math.ne v1 v2 = Some v0 ->
    transl_value v0 (Values.Val.cmp Integers.Cne x x0).
Proof.
  intros /sng.
  destruct v1;try discriminate; destruct v2;try discriminate;simpl in *;eq_same_clear /sng.
  destruct (Z.eq_dec n n0) /sng.
  - subst.
    replace (Zneq_bool n0 n0) with false. all:swap 1 2. {
      symmetry.
      apply Zneq_bool_false_iff.
      reflexivity. }
    unfold Values.Val.cmp.
    inversion h_transl_value_v1_x_;subst;simpl.
    inversion h_transl_value_v2_x0_;subst;simpl.
    rewrite Integers.Int.eq_true.
    simpl.
    constructor.
  - rewrite Zneq_bool_true;auto.
    unfold Values.Val.cmp.
    inversion h_transl_value_v2_x0_;subst;simpl.
    inversion h_transl_value_v1_x_;subst;simpl.
    rewrite Integers.Int.eq_false.
    simpl.
    + constructor.
    + apply repr_inj_neq.
      * inv_rtc.
      * inv_rtc.
      * assumption.
Qed.

Lemma le_ok: forall v1 v2 v0 x x0,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    transl_value v1 x ->
    transl_value v2 x0 ->
    Math.le v1 v2 = Some v0 ->
    transl_value v0 (Values.Val.cmp Integers.Cle x x0).
Proof.
  intros /sng.
  destruct v1;try discriminate; destruct v2;try discriminate;simpl in *;eq_same_clear /sng.
  inversion h_transl_value_v1_x_;subst;simpl.
  inversion h_transl_value_v2_x0_;subst;simpl.
  destruct (Z.le_decidable n n0) /sng.
  - rewrite Zaux.Zle_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_false.
    + constructor.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
      auto with zarith.
  - { rewrite Zaux.Zle_bool_false.
      - unfold Values.Val.cmp.
        simpl.
        unfold Integers.Int.lt.
        rewrite Coqlib.zlt_true.
        + constructor.
        + rewrite Integers.Int.signed_repr;inv_rtc.
          rewrite Integers.Int.signed_repr;inv_rtc.
          auto with zarith.
      - apply Z.nle_gt.
        assumption. }
Qed.


Lemma ge_ok: forall v1 v2 v0 x x0,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    transl_value v1 x ->
    transl_value v2 x0 ->
    Math.ge v1 v2 = Some v0 ->
    transl_value v0 (Values.Val.cmp Integers.Cge x x0).
Proof.
  intros /sng.
  destruct v1;try discriminate; destruct v2;try discriminate;simpl in * /sng.
  eq_same_clear.
  inversion h_transl_value_v1_x_;subst;simpl.
  inversion h_transl_value_v2_x0_;subst;simpl.
  rewrite Z.geb_leb.
  destruct (Z.le_decidable n0 n) /sng.
  - rewrite Zaux.Zle_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_false.
    + constructor.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
      auto with zarith.
  - { rewrite Zaux.Zle_bool_false.
      - unfold Values.Val.cmp.
        simpl.
        unfold Integers.Int.lt.
        rewrite Coqlib.zlt_true.
        + constructor.
        + rewrite Integers.Int.signed_repr;inv_rtc.
          rewrite Integers.Int.signed_repr;inv_rtc.
          auto with zarith.
      - apply Z.nle_gt.
        assumption. }
Qed.

Lemma lt_ok: forall v1 v2 v0 x x0,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    transl_value v1 x ->
    transl_value v2 x0 ->
    Math.lt v1 v2 = Some v0 ->
    transl_value v0 (Values.Val.cmp Integers.Clt x x0).
Proof.
  intros /sng.
  destruct v1;try discriminate; destruct v2;try discriminate;simpl in * /sng.
  eq_same_clear.
  inversion h_transl_value_v1_x_;subst;simpl.
  inversion h_transl_value_v2_x0_;subst;simpl.
  simpl.
  destruct (Z.lt_decidable n n0) /sng.
  - rewrite Zaux.Zlt_bool_true;auto.
    unfold Values.Val.cmp.
    subst.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_true.
    + constructor.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
  - { rewrite Zaux.Zlt_bool_false.
      - unfold Values.Val.cmp.
        subst.
        simpl.
        unfold Integers.Int.lt.
        rewrite Coqlib.zlt_false.
        + constructor.
        + rewrite Integers.Int.signed_repr;inv_rtc.
          rewrite Integers.Int.signed_repr;inv_rtc.
      - auto with zarith. }
Qed.


Lemma gt_ok: forall v1 v2 v0 x x0,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    transl_value v1 x ->
    transl_value v2 x0 ->
    Math.gt v1 v2 = Some v0 ->
    transl_value v0 (Values.Val.cmp Integers.Cgt x x0).
Proof.
  intros /sng.
  destruct v1;try discriminate; destruct v2;try discriminate;simpl in *;
  eq_same_clear; inversion h_transl_value_v1_x_;subst;simpl /sng.
  inversion h_transl_value_v2_x0_;subst;simpl.
  rewrite Z.gtb_ltb.
  destruct (Z.lt_decidable n0 n) /sng.
  - rewrite Zaux.Zlt_bool_true;auto.
    unfold Values.Val.cmp.
    subst.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_true.
    + constructor.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
  - { rewrite Zaux.Zlt_bool_false.
      - unfold Values.Val.cmp.
        subst.
        simpl.
        unfold Integers.Int.lt.
        rewrite Coqlib.zlt_false.
        + constructor.
        + rewrite Integers.Int.signed_repr;inv_rtc.
          rewrite Integers.Int.signed_repr;inv_rtc.
      - auto with zarith. }
Qed.


(* strangely this one does not need overflow preconditions *)
Lemma unaryneg_ok : forall n v1 v,
    transl_value v1 n ->
    Math.unary_operation Unary_Minus v1 = Some v ->
    transl_value v (Values.Val.negint n).
Proof.
  intros /sng.
  simpl in *.
  destruct v1;simpl in *;try discriminate.
  eq_same_clear.
  inversion h_transl_value_v1_n_.
  simpl.
  rewrite Integers.Int.neg_repr.
  constructor.
Qed.

Lemma do_run_time_check_on_binop_ok: forall v1 v2 v op,
    do_run_time_check_on_binop op v1 v2 (OK v) ->
    Math.binary_operation op v1 v2 = Some v.
Proof.
  intros v1 v2 v op hdo_rtc.
  invclear hdo_rtc /sng.
  - invclear h_overf_check_v_ /sng.
    assumption.
  - invclear h_do_division_check_;simpl in * /sng.
    invclear h_overf_check_v_ /sng.
    assumption.
  - simpl.
    inversion h_do_division_check_;cbn;subst /sng.
    cbn in h_eq_mod'_v0_v3_v_.
    assumption.
  - assumption.
Qed.

Ltac int_simpl :=
  progress
    (try rewrite min_signed_ok;
     try rewrite max_signed_ok;
     try rewrite Integers.Int.add_signed;
     try rewrite Integers.Int.sub_signed;
     try rewrite Integers.Int.mul_signed;
     try rewrite Integers.Int.add_signed;
     rewrite Integers.Int.signed_repr) /sng.

Lemma add_ok : forall v v1 v2 n1 n2,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop Plus v1 v2 (OK v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v (Values.Val.add n1 n2).
Proof.
  intros /sng.
  destruct v1;simpl in *;try discriminate;eq_same_clear;subst;try now inv_rtc /sng.
  destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc /sng.
  inversion h_transl_value_v1_n1_;subst;simpl.
  inversion h_transl_value_v2_n2_;subst;simpl.
  invclear h_do_rtc_binop_;simpl in *; eq_same_clear /sng.
  invclear h_overf_check_v_ /sng.
  int_simpl;auto;inv_rtc /sng.
  rewrite Int.signed_repr; auto.
  constructor 1.
Qed.

Lemma sub_ok : forall v v1 v2 n1 n2,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop Minus v1 v2 (OK v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v (Values.Val.sub n1 n2).
Proof.
  intros /sng.
  destruct v1;simpl in *;try discriminate;eq_same_clear;subst; try now inv_rtc /sng.
  destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc /sng.
  inversion h_transl_value_v1_n1_;subst;simpl.
  inversion h_transl_value_v2_n2_;subst;simpl.
  invclear h_do_rtc_binop_;simpl in *; eq_same_clear /sng.
  invclear h_overf_check_v_ /sng.
  int_simpl;auto;inv_rtc /sng.
  rewrite Int.signed_repr;auto.
  constructor.
Qed.

Lemma mult_ok : forall v v1 v2 n1 n2,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop Multiply v1 v2 (OK v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v (Values.Val.mul n1 n2).
Proof.
  intros /sng.
  simpl in *.
  destruct v1;simpl in *;try discriminate;eq_same_clear;subst; try now inv_rtc /sng.
  destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc /sng.
  inversion h_transl_value_v1_n1_;subst;simpl.
  inversion h_transl_value_v2_n2_;subst;simpl.
  invclear h_do_rtc_binop_;simpl in *; eq_same_clear /sng.
  invclear h_overf_check_v_ /sng.
  int_simpl;auto;inv_rtc /sng.
  rewrite Int.signed_repr;auto.
  constructor.
Qed.

(** Compcert division return None if dividend is min_int and divisor
    in -1, because the result would be max_int +1. In Spark's
    semantics the division is performed but then it fails overflow
    checks. *)
(*  How to compile this? probably by performing a check before. *)
Lemma div_ok : forall v v1 v2 n n1 n2,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop Divide v1 v2 (OK v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v n ->
    Values.Val.divs n1 n2 = Some n.
Proof.
  intros/sng.
  simpl in *.
  destruct v1;subst;simpl in *;try discriminate;try now inv_rtc /sng.
  destruct v2;subst;simpl in *; try discriminate;try now inv_rtc /sng.
  inversion h_transl_value_v2_n2_;subst;simpl.
  inversion h_transl_value_v1_n1_;subst;simpl.
  rename n0 into v1.
  rename n3 into v2.
  invclear h_do_rtc_binop_;simpl in *; eq_same_clear /sng.
  { decompose [or] h_or_eq_Divide_or_;discriminate. }
  inv_rtc /sng.
  rewrite min_signed_ok, max_signed_ok in *.
  inversion h_do_division_check_ /sng.
  apply Zeq_bool_neq in h_eq_Zeqb_v2_0_false_.
  autorename h_eq_Zeqb_v2_0_false_.
  rewrite Integers.Int.eq_false;auto.
  - simpl.
    (* the case where division overflows is dealt with by the overflow
       check in spark semantic. Ths division is performed on Z and
       then overflow is checked and may fails. *)
    destruct (Int.eq (Int.repr v1)
                     (Int.repr Int.min_signed) &&
                Int.eq (Int.repr v2) Int.mone)
             eqn:h_divoverf_.
    + apply andb_true_iff in h_divoverf_.
      destruct h_divoverf_ as [h_divoverf1_ h_divoverf2_].
      exfalso.
      assert (v1_is_min_int: v1 = Integers.Int.min_signed).
      { rewrite Integers.Int.eq_signed in h_divoverf1_.
        unfold Coqlib.zeq in h_divoverf1_;auto.
        rewrite Int.signed_repr in h_divoverf1_;try (split;lia) /ng.
        rewrite Int.signed_repr in h_divoverf1_; try lia.
        destruct (Z.eq_dec v1 Integers.Int.min_signed) /ng;try discriminate.
        assumption. }
      assert (v2_is_min_int: v2 = -1).
      { rewrite Integers.Int.eq_signed in h_divoverf2_.
        unfold Coqlib.zeq in h_divoverf2_;auto.
        rewrite Integers.Int.signed_repr in h_divoverf2_;try (split;lia) /sng.
        destruct (Z.eq_dec v2 (Integers.Int.signed Integers.Int.mone));try discriminate.
        apply e. }
      subst.
      vm_compute in h_eq_div_v1_v2_v4_.
      inversion h_eq_div_v1_v2_v4_.
      subst.
      inversion h_overf_check_v_;subst.
      inv_rtc.
    + unfold Integers.Int.divs.
      do 2 (rewrite Integers.Int.signed_repr;auto 2) /sng.
      simpl in *.
      invclear h_eq_div_v1_v2_v4_ ;subst /sng.
      inversion h_overf_check_v_;subst.
      inversion h_transl_value_v_n_;subst;simpl.
      reflexivity.
  - unfold Integers.Int.zero.
    intro abs.
    apply h_neq_v2_0_.
    rewrite <- (Integers.Int.signed_repr v2).
    + rewrite abs.
      rewrite (Integers.Int.signed_repr 0);auto.
      split; intro;discriminate.
    + split;auto.
Qed.


Lemma binary_operator_ok: forall op (n n1 n2 : Values.val) (v v1 v2 : value),
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop op v1 v2 (OK v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v n ->
    forall m, Cminor.eval_binop (transl_binop op) n1 n2 m = Some n.
Proof.
  intros /sng.
  assert (h_rtc_:=do_run_time_check_on_binop_ok _ _ _ _ h_do_rtc_binop_).
  destruct op;simpl in *.
  - eapply (and_ok v1 v2 v n1 n2) in h_rtc_;auto.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h_rtc_);reflexivity.
  - eapply (or_ok v1 v2 v n1 n2) in h_rtc_;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h_rtc_);reflexivity.

  - eapply (eq_ok v1 v2 v n1 n2) in h_rtc_;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h_rtc_);reflexivity.
  - eapply (neq_ok v1 v2 v n1 n2) in h_rtc_;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h_rtc_);reflexivity.
  - eapply (lt_ok v1 v2 v n1 n2) in h_rtc_;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h_rtc_);reflexivity.
  - eapply (le_ok v1 v2 v n1 n2) in h_rtc_;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h_rtc_);reflexivity.
  - eapply (gt_ok v1 v2 v n1 n2) in h_rtc_;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h_rtc_);reflexivity.
  - eapply (ge_ok v1 v2 v n1 n2) in h_rtc_;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h_rtc_);reflexivity.
  - generalize (add_ok _ _ _ _ _ h_check_overf_ h_check_overf_0 h_do_rtc_binop_
                       h_transl_value_v1_n1_ h_transl_value_v2_n2_).
    intro h.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h);reflexivity.
  - generalize (sub_ok _ _ _ _ _ h_check_overf_ h_check_overf_0 h_do_rtc_binop_
                       h_transl_value_v1_n1_ h_transl_value_v2_n2_).
    intro h.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h);reflexivity.
  - generalize (mult_ok _ _ _ _ _ h_check_overf_ h_check_overf_0 h_do_rtc_binop_
                        h_transl_value_v1_n1_ h_transl_value_v2_n2_).
    intro h.
    rewrite (transl_value_det _ _ _ h_transl_value_v_n_ h);reflexivity.
  - generalize (div_ok _ _ _ _ _ _ h_check_overf_ h_check_overf_0 h_do_rtc_binop_
                       h_transl_value_v1_n1_ h_transl_value_v2_n2_ h_transl_value_v_n_).
    intro h.
    assumption.
  - admit. (* TODO mod_ok *)
Admitted.


(** * Memory invariant and bisimilarity *)


Lemma evalLiteral_overf : forall (l:literal) n,
    evalLiteral l (OK (Int n)) ->
    overflowCheck n (OK (Int n)).
Proof.
  intros /sng.
  inversion h_eval_literal_ /sng.
  inversion h_overf_check_n_ /sng.
  assumption.
Qed.


(** [safe_stack s] means that every value in the spark stack [s] is
    correct wrt to overflows.
    TODO: extend with other values than Int: floats, arrays, records. *)
Definition safe_stack s := forall id n,
    STACK.fetchG id s = Some (Int n) ->
    overflowCheck n (OK (Int n)).

(** Hypothesis renaming stuff *)
Ltac rename_hyp2' n th :=
  match th with
  | _ => rename_hyp2 n th
  | safe_stack ?s => name(`_safe_stack` ++ s#n)
  end.

Ltac rename_sparkprf ::= rename_hyp2'.

Lemma evalName_overf: forall s st nme n,
    safe_stack s
    -> evalName st s nme (OK (Int n))
    -> overflowCheck n (OK (Int n)).
Proof using.
  intros /sng.
  inversion h_eval_name_nme_n_ /sng. (* l'environnement retourne toujours des valeur rangées. *)
  - unfold safe_stack in *.
    eapply h_safe_stack_s_;eauto.
  - simpl in *.
    constructor.
    admit. (* Arrays *)
  - admit. (* records *)
Admitted.

(** on a safe stack, any expression that evaluates into a value,
    evaluates to a not overflowing value, except if it is a unary_plus
    (in which case no check is made). *)
Lemma eval_expr_overf : forall st s,
    safe_stack s ->
    forall e n,
      evalExp st s e (OK (Int n)) ->
      overflowCheck n (OK (Int n)).
Proof.
  intros /sng.
  revert h_safe_stack_s_.
  remember (OK (Int n)) as hN.
  revert n HeqhN.
  induction h_eval_expr_e_n_; try rename v1 into v1_; try rename v2 into v2_;intros ;subst;try discriminate /sng.
  - eapply evalLiteral_overf;eauto.
  - eapply evalName_overf;eauto.
  - invclear h_do_rtc_binop_ /sng.
    + inversion h_overf_check_n0_;subst;auto.
    + inversion h_overf_check_n0_;subst;auto.
    + inversion h_do_division_check_. /sng.
      subst.
      specialize h_all_overf_check_ with (1:=eq_refl) (2:=h_safe_stack_s_).
      specialize h_all_overf_check_0 with (1:=eq_refl) (2:=h_safe_stack_s_).
      inversion h_all_overf_check_;subst /sng.
      cbn in h_eq_mod'_v1_v2_n0_.
      inversion h_eq_mod'_v1_v2_n0_;subst /sng.
      constructor.
      constructor.
      inversion h_all_overf_check_0 /sng.
      inversion h_inbound_0 /sng.
      apply andb_true_intro.
      apply andb_prop in h_eq_andb_leb_leb_true_.
      setoid_rewrite Z.leb_le in h_eq_andb_leb_leb_true_.
      decomp h_eq_andb_leb_leb_true_.
      setoid_rewrite Z.leb_le.
      specialize (Z_lt_le_dec v2 0);intro hor.
      { destruct hor as [? | ?] /sng.
        - specialize Z.mod_neg_bound with (a:=v1)(1:=h_lt_v2_0_);intro h_lt_.
          decomp h_lt_.
          split.
          + lia.
          + assert (max_signed>=0).
            { rewrite max_signed_ok.  apply Int.max_signed_pos. }
            lia.
        - assert (0<v2) /sng.
          { apply  Zeq_bool_neq in h_eq_Zeqb_v2_0_false_.
            lia. }
          specialize Z.mod_pos_bound with (a:=v1)(1:=h_lt_0_v2_);intro h_lt_.
          decomp h_lt_.
          split.
          + assert (min_signed<0).
            { rewrite min_signed_ok. apply Int.min_signed_neg. }
            lia.
          + lia. }
    + rewrite binopexp_ok in *.
      functional inversion h_eq_binary_operation_op_v1__v2__n0_;subst
      ;try match goal with H: ?A <> ?A |- _ => elim H;auto end.
  - invclear h_do_rtc_unop_ /sng.
    + inversion h_overf_check_n0_;subst;auto.
    + rewrite unopexp_ok in *.
      functional inversion h_eq_unary_operation_op_v_n0_;subst
      ;try match goal with H: ?A <> ?A |- _ => elim H;auto end /sng.
Qed.

Lemma evalExp_overf2 : forall st s,
    safe_stack s ->
    forall (e:exp) e_v,
      evalExp st s e (OK e_v) -> check_overflow_value e_v.
Proof.
  intros /sng.
  destruct e_v;simpl in *;auto.
  eapply eval_expr_overf;eauto.
Qed.


Local Hint Resolve evalExp_overf2 : spark.

(* [make_load] does not fail on transl_type a translated variable coming
   from stbl *)
Lemma make_load_no_fail: forall stbl t nme_t x,
    transl_type stbl t = Errors.OK x ->
    exists load_addr_nme, make_load nme_t x = Errors.OK load_addr_nme.
Proof.
  intros /sng.
  unfold make_load.
  destruct t;simpl in * ; simpl; try discriminate;eauto.
  - inversion h_eq_transl_type_x_. subst.
    simpl.
    unfold make_load.
    simpl.
    eauto.
  - inversion h_eq_transl_type_x_. subst.
    simpl.
    unfold make_load.
    simpl.
    eauto.
Qed.

(* THIS IS NOT ALWAYS TRUE: some variable may not be initialized at some point. *)
Definition stack_complete stbl s CE := forall a nme addr_nme,
    transl_variable stbl CE a nme = Errors.OK addr_nme
    -> exists v, evalName stbl s (Identifier a nme) (OK v).

(* All variables in CE have a type in stbl. This is ensured by typing. *)
Definition subset_CE_stbl stbl CE := forall nme addr_nme,
    transl_name stbl CE nme = Errors.OK addr_nme
    -> exists typ_nme, type_of_name stbl nme = Errors.OK typ_nme.

Definition all_greater stck n := forall nme δ_id,
    CompilEnv.fetchG nme stck = Some δ_id ->
    n <= δ_id.

Definition stack_no_null_offset CE := all_greater CE 4.
(*
Lemma stack_no_null_offset_var stbl CE : forall a nme δ_lvl δ_id,
    stack_no_null_offset CE ->
    transl_variable stbl CE a nme = Errors.OK (build_loads δ_lvl δ_id) ->
    4 <= Ptrofs.unsigned (Int.repr δ_id).
Proof.
  intros /sng.
  functional inversion heq_transl_variable_.
  
  destruct (Int.repr δ_id) eqn:heq.
  destruct (Int.repr n) eqn:heq2.
  cbn in *.
  red in H.
  eapply H;eauto.
  unfold transl_variable.
 *)
Definition stack_match_lgth (s : STACK.state) (CE : compilenv) :=
  Datatypes.length s = Datatypes.length CE.
(* The spark dynamic and the compiler static stack have the same structure. *)
Definition stack_match_CE (s : STACK.state) (CE : compilenv) :=
  forall nme lvl,(forall sto, STACK.frameG nme s = Some (lvl,sto) ->
                              exists CE_sto,
                                CompilEnv.frameG nme CE = Some (lvl,CE_sto))
                 ∧ forall CE_sto, CompilEnv.frameG nme CE = Some (lvl,CE_sto)
                                  -> exists sto, STACK.frameG nme s = Some (lvl,sto).


(* stack_match_CE_ must be true on all sub stacks *)
Inductive strong_stack_match_CE: STACK.state → compilenv → Prop :=
| Strg_smCE_nil: stack_match_CE [] [] -> strong_stack_match_CE [] []
| Strg_smCE_cons: forall lvl sto s stoCE CE,
    strong_stack_match_CE s CE ->
    stack_match_CE ((lvl,sto)::s) ((lvl,stoCE)::CE) ->
    strong_stack_match_CE ((lvl,sto)::s) ((lvl,stoCE)::CE).

Ltac rename_stck_matchCE n th :=
  match th with
  | stack_match_CE ?s ?CE => name (`_stk_mtch_CE` ++ s#n ++ CE#n)
  | stack_match_CE ?s _ => name (`_stk_mtch_CE` ++ s#n)
  | stack_match_CE _ _ => name (`_stk_mtch_CE`)
  | stack_no_null_offset ?CE => name (`_nonul_ofs` ++ CE#n)
  | stack_no_null_offset _ => name (`_nonul_ofs`)
  | _ => rename_hyp2' n th
  end.

Ltac rename_sparkprf ::= rename_stck_matchCE.

Lemma nodup_stack_match_CE_strong_:
  forall s CE,
    STACK.NoDup_G s ->
    CompilEnv.NoDup_G CE ->
    Datatypes.length s = Datatypes.length CE ->
    STACK.exact_levelG s -> CompilEnv.exact_levelG CE ->
    stack_match_CE s CE -> strong_stack_match_CE s CE.

Proof.
  induction s;destruct CE; (intros /n); try (cbn in *; try discriminate)/g.
  - now constructor.
  - destruct a,f/ng.
    inversion h_exct_lvl_a_s_ /sng.
    inversion h_exct_lvlG_f_CE_ /sng.
    invclear h_eq_length_a_s_length_ /n.
    rewrite h_eq_length_s_length_.
    constructor;auto.
    all:swap 1 2.
    + rewrite h_eq_length_s_length_ in h_stk_mtch_CE_a_s_f_CE_.
      assumption.
    + apply IHs;auto.
      * eapply STACK.stack_NoDup_G_cons;eauto.
      * eapply CompilEnv.stack_NoDup_G_cons ;eauto.
      * red;intros/g.
        red in h_stk_mtch_CE_a_s_f_CE_.
        specialize (h_stk_mtch_CE_a_s_f_CE_ nme lvl).
        destruct h_stk_mtch_CE_a_s_f_CE_ as [h1 h2].
        split;intros/ng.
        -- specialize (h1 sto).
           assert (STACK.frameG nme ((Datatypes.length s, s1) :: s) = Some (lvl, sto)) /n.
           { assert (STACK.resideG nme s = true)/n.
             { eapply STACK.frameG_resideG_1;eauto. }
             specialize STACK.nodup_G_cons with (1:=h_nodup_G_a_s_) (2:=h_eq_resideG_nme_s_true_);intro h.
             cbn.
             cbn in h.
             rewrite h.
             assumption. }
           specialize h1 with (1:=h_eq_frameG_nme_length_s1_s_lvl_sto_).
           decomp h1.
           cbn in *.
           destruct (CompilEnv.resides nme s3) eqn:? /n.
           ++ exfalso.
              inversion h_eq_CEframeG_nme_length_s3_CE_lvl_CE_sto_;subst.
              rewrite <- h_eq_length_s_length_ in *.
              specialize STACK.exact_levelG_frameG_lt_lgth
                with (1:=h_exct_lvl_s_) (2:=h_eq_frameG_nme_s_lvl_sto_).
              intros.
              lia.
           ++ eauto.
        -- specialize (h2 CE_sto).
           especialize h2 at 1 /n.
           { specialize  CompilEnv.nodup_G_cons with (1:=h_nodup_G_CE_f_CE_) as hh.
             especialize hh at 1 as h; clear hh / d. 
             (* assert (CompilEnv.resideG nme CE = true) /n. *)
             { eapply CompilEnv.frameG_resideG_1;eauto. }
             cbn.
             cbn in h.
             rewrite h.
             assumption. }
           decomp h2.
           cbn in *.
           
           destruct (STACK.resides nme s1) eqn:?.
           ++ exfalso.
              rewrite h_eq_length_s_length_ in *.
              invclear h_eq_frameG_nme_length_s1_s_lvl_sto_ /sg.
              specialize CompilEnv.exact_levelG_frameG_lt_lgth
                with (1:=h_exct_lvlG_CE_)(2:=h_eq_CEframeG_nme_CE_lvl_CE_sto_).
              intros.
              lia.
           ++ eauto.
Qed.



(* A name present in CE is translated to some expression that evaluates
   correctly to an address. *)
Definition stack_match_addresses st CE sp locenv g m :=
  forall nme addr_nme ,
    transl_name st CE nme = Errors.OK addr_nme ->
    exists addr, Cminor.eval_expr g sp locenv m addr_nme addr.

Inductive strong_stack_match_addresses stbl:compilenv → Values.val → env → genv → mem → Prop :=
| Strg_sma_nil: forall v locenv g m,
    stack_match_addresses stbl [] v locenv g m ->
    strong_stack_match_addresses stbl [] v locenv g m
| Strg_sma_cons: forall lvl stoCE CE v v' locenv locenv' g m,
    strong_stack_match_addresses stbl CE v locenv g m ->
    Mem.loadv AST.Mint32 m v' = Some v ->
    stack_match_addresses stbl ((lvl,stoCE)::CE) v' locenv' g m ->
    strong_stack_match_addresses stbl ((lvl,stoCE)::CE) v' locenv' g m.

Ltac rename_stck_matchaddr n th :=
  match th with
  | stack_match_addresses _ _ ?CE _ _ ?m => name(`_stk_mtch_addr` ++ CE#n ++ m#n)
  | strong_stack_match_addresses _ ?CE ?v _ _ ?m => name(`_sstk_mtch_addr` ++ CE#n ++ m#n)
  | _ => rename_stck_matchCE n th
  end.

Ltac rename_sparkprf ::= rename_stck_matchaddr.

Lemma nodup_stack_match_address_strong:
  forall st CE sp locenv g m,
    chained_stack_structure m (Datatypes.length CE) sp ->
    CompilEnv.NoDup_G CE ->
    CompilEnv.exact_levelG CE ->
    stack_match_addresses st CE sp locenv g m -> 
    strong_stack_match_addresses st CE sp locenv g m.
Proof.
  induction CE; (intros /ng).
  - now constructor.
  - rename h_stk_mtch_addr_sp_m_ into h_stack_match_addr.
    destruct a.
    inversion h_chain_m_length_sp_ /sng.
    econstructor 2;eauto.
    + apply IHCE with (1:=h_chain_m_length_vptr_) (locenv:=locenv);eauto.
      * eapply CompilEnv.stack_NoDup_G_cons;eauto.
      * eapply CompilEnv.exact_levelG_sublist;eauto.
      * red in h_stack_match_addr |- *.
        intros /ng.
        functional inversion h_eq_transl_name_nme_t_ /sng.
        functional inversion h_eq_transl_var_nme_t_/sng.

        assert (transl_name st ((s, s0) :: CE) (Identifier astnum id) = Errors.OK (build_loads (S(m' - m0)) n)) /ng.
        { cbn.
          unfold transl_variable;simpl.
          assert (CompilEnv.fetch id (s, s0) = None) /n.
          { eapply CompilEnv.nodupG_fetch_cons;eauto. }
          setoid_rewrite h_eq_CEfetch_id_s_s0_None_.
          setoid_rewrite h_eq_CEfetchG_id_CE_n_.
          rewrite CompilEnv.fetch_ok_none;auto.
          rewrite h_eq_CEframeG_id_CE_m0__x_.
          inversion h_exct_lvlG_a_CE_/sng.
          destruct CE;try discriminate.
          inversion h_exct_lvlG_CE_ /sng.
          set (lCE:= Datatypes.length CE) in *|-*.
          simpl Datatypes.length.
          inversion h_eq_lvloftop_CE_m'_.
          assert (Datatypes.length CE >= m0)%nat.
          { eapply CompilEnv.exact_levelG_frameG_le_top;eauto. }
          replace (S (Datatypes.length CE) - m0)%nat
            with (S ((Datatypes.length CE) - m0))%nat by lia.
          unfold build_loads at 1 2.
          reflexivity.
        }


        specialize h_stack_match_addr with (1:=h_eq_transl_name_bldlds_).
        decomp h_stack_match_addr.
        exists addr.
        simpl in h_chain_m_length_sp_.
        specialize chained_stack_structure_aux with (1:= h_chain_m_length_sp_) (g:=g)(e:=locenv);
          intro h.
        decomp h.
        rewrite h_eq_loadv_vptr_vptr_0 in h_eq_loadv_vptr_vptr_.
        invclear h_eq_loadv_vptr_vptr_/sng.
        inversion h_CM_eval_expr_bldlds_addr_/sng.
        change (Eload AST.Mint32 (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (m' - m0)))
          with (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S (m' - m0)))
          in h_CM_eval_expr_Eload_v1_.
        assert (chained_stack_structure m (S (m' - m0)) (Values.Vptr b Ptrofs.zero)) /n.
        { apply chained_stack_structure_le with (n:=(S (Datatypes.length CE)));auto.
          apply CompilEnv.exact_levelG_sublist in h_exct_lvlG_a_CE_.
          specialize CompilEnv.exact_lvl_lvl_of_top with (1:=h_exct_lvlG_a_CE_);intro h.
          specialize (h _ h_eq_lvloftop_CE_m'_).
          rewrite <- h.
          lia. }
        specialize chained_stack_structure_decomp_S_2 with (1:=h_chain_m_S_vptr_);intro h.
        specialize h with (1:=h_CM_eval_expr_Eload_v1_).
        decomp h.
        inversion h_CM_eval_expr_Eload_sp'_/sng.
        inversion h_CM_eval_expr_Econst_vaddr_ /sng.
        simpl in h_eq_evalcst_vptr_Oaddrstack_vaddr_.
        rewrite Ptrofs.add_zero_l in h_eq_evalcst_vptr_Oaddrstack_vaddr_.
        inversion h_eq_evalcst_vptr_Oaddrstack_vaddr_;subst.
        rewrite h_eq_loadv_vaddr_sp'_ in h_eq_loadv_vptr_vptr_0.
        invclear h_eq_loadv_vptr_vptr_0;subst.
        unfold build_loads.
        econstructor;eauto.
        inversion h_CM_eval_expr_Econst_v2_;subst.
        constructor;auto.
Qed.

Lemma transl_variable_nodup_resideG : forall st CE id a x,
    transl_variable st CE a id = Errors.OK x ->
    CompilEnv.resideG id CE = true.
Proof.
  intros st CE id a x H. 
  functional inversion H.
  apply CompilEnv.frameG_resideG_1.
  eauto.
Qed.



(* Observationnal equivalence of the spark dynamic stack and the compile environment. *)
Definition stack_match st s CE sp locenv g m :=
  forall nme v addr_nme load_addr_nme vaddr typ_nme cm_typ_nme,
    transl_name st CE nme = Errors.OK addr_nme ->
    (* addr_nme evaluated to some address, usually ensured by stack_match_addresses *)
    Cminor.eval_expr g sp locenv m addr_nme vaddr -> 
    (evalName st s nme (OK v) ->
     (* remark: transl_type should always return someting once the
        compiler is complete *)
     transl_type st typ_nme = Errors.OK cm_typ_nme ->
     (* this is usually ensured by subset_CE_stbl *)
     type_of_name st nme = Errors.OK typ_nme ->
     make_load addr_nme cm_typ_nme = Errors.OK load_addr_nme ->
     (* The address contains something compatible with the size *)
     exists v_t,
       (transl_value v v_t /\
          Cminor.eval_expr g sp locenv m load_addr_nme v_t)).

(* stack_match must be true on all sub stacks *)
Inductive strong_stack_match stbl: STACK.state → compilenv → Values.val → env → genv → mem → Prop :=
| Strg_sm_nil: forall v locenv g m,
    stack_match stbl [] [] v locenv g m ->
    strong_stack_match stbl [] [] v locenv g m
| Strg_sm_cons: forall lvl sto s stoCE CE v v' locenv locenv' g m,
    strong_stack_match stbl s CE v locenv g m ->
    Mem.loadv AST.Mint32 m v' = Some v ->
    stack_match stbl ((lvl,sto)::s) ((lvl,stoCE)::CE) v' locenv' g m ->
    strong_stack_match stbl ((lvl,sto)::s) ((lvl,stoCE)::CE) v' locenv' g m.

Definition all_addr_no_overflow CE := forall id δ,
    CompilEnv.fetchG id CE = Some δ -> 0 <= δ < Ptrofs.modulus.

Ltac rename_stck_match n th :=
  match th with
  | stack_no_null_offset ?CE => name (`_nonul_ofs` ++ CE#n)
  | stack_complete _ ?s ?CE => name (`_stk_cmpl` ++ s#n ++ CE#n)
  | all_addr_no_overflow ?x => name (`_no_overf` ++ x#n)
  | stack_match _ ?s _ _ _ _ ?m => name (`_stk_mtch` ++ s#n ++ m#n)
  | stack_match_lgth ?s ?CE => name (`_stk_mtch_lgth` ++ s#n ++ CE#n)
  | stack_match_addresses _ _ ?CE _ _ ?m => name (`_stk_mtch_addr` ++ CE#n ++ m#n)
  | _ => rename_stck_matchaddr n th
  end.

Ltac rename_sparkprf ::= rename_stck_match.

Proposition all_addr_nooverf_cons : forall x CE,
    CompilEnv.NoDup_G (x :: CE) ->
    all_addr_no_overflow (x:: CE) -> all_addr_no_overflow CE.
Proof.
  red.
  intros x CE h_nodupG_ h_alladdr_nooverf_ id δ heq_fetchG_. 
  apply h_alladdr_nooverf_ with id.
  cbn.
  specialize CompilEnv.nodup_G_cons with(1:=h_nodupG_);intro h.
  assert (CompilEnv.fetch id x = None) /sng.
  { apply CompilEnv.reside_false_fetch_none.
    apply h.
    eapply CompilEnv.fetchG_ok;eauto. }
  now rewrite h_eq_CEfetch_id_x_None_.
Qed.

Lemma transl_name_nodup_cons : forall st CE nme lvl n fr,
    all_addr_no_overflow CE ->
    transl_name st CE nme = Errors.OK (build_loads lvl n) ->
    0 <= n ∧ n < Ptrofs.modulus ->
    CompilEnv.NoDup_G (fr :: CE) ->
    CompilEnv.exact_levelG (fr :: CE) ->
    transl_name st (fr::CE) nme = Errors.OK (build_loads (S lvl) n).
Proof.
  intros /sng.
  red in h_nodup_G_CE_fr_CE_.
  functional inversion h_eq_transl_name_bldlds_ /sng.
  specialize transl_variable_nodup_resideG with (1:=h_eq_transl_var_bldlds_) as?  /sng.
  simpl.
  unfold transl_variable.
  simpl.
  specialize CompilEnv.frameG_resideG_2 with (1:= h_eq_resideG_id_CE_true_);intro /sng.
  decomp h_ex_eq_CEframeG_.
  rewrite h_eq_CEframeG_id_CE_x_.
  assert (CompilEnv.fetch id fr = None) /sng.
  { apply CompilEnv.reside_false_fetch_none.
    apply CompilEnv.nodup_G_cons with (l:=CE);auto. }
  rewrite h_eq_CEfetch_id_fr_None_.
  specialize CompilEnv.fetchG_ok_some with (1:=h_eq_resideG_id_CE_true_);intros /sng.
  decomp h_ex_eq_CEfetchG_.
  rewrite h_eq_CEfetchG_id_CE_v_.
  specialize CompilEnv.fetch_ok_none with (1:=h_eq_CEfetch_id_fr_None_);intro /sng.
  rewrite h_eq_reside_id_fr_false_.
  destruct x, fr;simpl.
  inversion h_exct_lvlG_fr_CE_;subst /sng.
  (*           functional inversion h_eq_transl_var_ /sng. *)
  unfold transl_variable in h_eq_transl_var_bldlds_.
  rewrite h_eq_CEfetchG_id_CE_v_ in h_eq_transl_var_bldlds_.
  rewrite h_eq_CEframeG_id_CE_x_ in h_eq_transl_var_bldlds_.
  specialize CompilEnv.exact_lvl_level_of_top with (1:=h_exct_lvlG_CE_) (2:=h_eq_CEframeG_id_CE_x_);intro /sng.
  decomp h_ex_and_.
  rewrite h_eq_lvloftop_CE_top_ in h_eq_transl_var_bldlds_.
  inversion h_eq_transl_var_bldlds_.
  change (match Int.repr v with
          | {| Int.intval := intval |} => intval
          end) with (Int.repr v).(Int.intval) in H1.
  change (match Int.repr n with
          | {| Int.intval := intval |} => intval
          end) with (Int.repr n).(Int.intval) in H1.
  apply f_equal.
  Transparent Int.repr.
  apply build_loads_inj_inv;auto.
  - apply build_loads__inj in H0;auto.
    subst.
    apply CompilEnv.exact_lvl_lvl_of_top in h_eq_lvloftop_CE_top_;auto.
    rewrite <- h_eq_lvloftop_CE_top_.
    unfold Int.repr.
    assert (s <= top)%nat /sng.
    { specialize CompilEnv.exact_levelG_frameG_lt_lgth with (1:=h_exct_lvlG_CE_)(2:=h_eq_CEframeG_id_CE_x_);intro /sng.
      lia. }
    lia.
  - rewrite Int.eqm_small_eq with v n;eauto.
    Transparent Int.repr Int.intval.
    simpl in H1. 
    Opaque Int.repr Int.intval.
    red.
    apply Zbits.eqmod_trans with (v mod Int.modulus); try now apply Zbits.eqmod_mod;auto.
    apply Zbits.eqmod_trans with (n mod Int.modulus); try (apply Zbits.eqmod_sym;now apply Zbits.eqmod_mod;auto).
    setoid_rewrite Int.Z_mod_modulus_eq in H1.
    rewrite H1.
    apply Zbits.eqmod_refl.
Qed.

(* Constant are independent of memory, except Oaddrstack *)
Lemma eval_expr_const_indep: forall g sp locenv m c v,
    eval_expr g sp locenv m (Econst c) v ->
    match c with
    | Oaddrstack _ => False
    | _ => True
    end -> 
    forall sp' locenv' m',
      eval_expr g sp' locenv' m' (Econst c) v.
Proof.
  intros g sp locenv m c v H sp' locenv' m'. 
  inversion H;subst.
  econstructor;eauto.
  rewrite <- eval_constant_ok in H1.
  functional inversion H1;rewrite eval_constant_ok in *;simpl in *;subst;auto.
  contradict sp'.
Qed.


Lemma nodup_stack_match_strong_:
  forall st s CE sp locenv g m,
    chained_stack_structure m (Datatypes.length CE) sp ->
    all_addr_no_overflow CE ->
    STACK.NoDup_G s -> CompilEnv.NoDup_G CE ->
    STACK.exact_levelG s -> CompilEnv.exact_levelG CE ->
    Datatypes.length s = Datatypes.length CE ->
    stack_match st s CE sp locenv g m -> 
    strong_stack_match st s CE sp locenv g m.
Proof.
  induction s;intros /sng.
  - simpl in h_eq_length_nil_length_.
    destruct CE;try discriminate.
    now constructor.
  - destruct CE;try discriminate.
    destruct a, f.
    assert (s0 = s2).
    { transitivity (Datatypes.length s).
      2:transitivity (Datatypes.length CE).
      - now inversion h_exct_lvl_a_s_.
      - simpl in h_eq_length_a_s_length_.
        now inversion h_eq_length_a_s_length_.
      - now inversion h_exct_lvlG_CE_. }
    subst.
    inversion h_chain_m_length_sp_;subst /sng.
    econstructor 2;eauto.
    eapply h_all_strong_stack_match_ with (sp:=(Values.Vptr b' Ptrofs.zero)) (locenv:=locenv).
    all:swap 1 7.
    { simpl in h_eq_length_a_s_length_.
      now inversion h_eq_length_a_s_length_. }
    { red.
      intros /sng.
      red in h_no_overf_CE_.
      eapply h_no_overf_CE_ with (id:=id);eauto.
      eapply CompilEnv.nodupG_fetchG_cons;eauto. } 
    { eapply STACK.stack_NoDup_G_cons;eauto. }
    { eapply CompilEnv.stack_NoDup_G_cons;eauto. }
    { eapply STACK.exact_levelG_sublist;eauto. }
    { eapply CompilEnv.exact_levelG_sublist;eauto. }
    + assumption.
    + clear h_all_strong_stack_match_.
      simpl in h_chain_m_length_sp_.
      simpl in h_eq_length_a_s_length_.
      apply eq_add_S in h_eq_length_a_s_length_.
      red.
      intros /sng.
      functional inversion h_eq_transl_name_nme_t_;subst /sng.
      functional inversion h_eq_transl_var_nme_t_;subst /sng.
      rename _x into __x. (* bad interaction with autonaming. *)
      assert (chained_stack_structure m (S (m' - m0)) (Values.Vptr b Ptrofs.zero)) /sng.
      { eapply chained_stack_structure_le;eauto.
        specialize CompilEnv.exact_lvl_lvl_of_top with (2:=h_eq_lvloftop_CE_m'_);intro h.
        rewrite <- h.
        ** lia.
        ** inversion h_exct_lvlG_CE_;auto. }
      functional inversion h_eq_make_load_load_addr_nme_ /sng.
      subst.
      unfold build_loads in h_CM_eval_expr_nme_t_nme_t_v_.
      red in h_stk_mtch_a_s_m_.
      specialize h_stk_mtch_a_s_m_ with (4:=h_eq_transl_type_cm_typ_nme_) (5:=h_eq_type_of_name_st_nme_typ_nme_).
      specialize h_stk_mtch_a_s_m_ with (vaddr:=nme_t_v) (v:=v) (addr_nme:=(build_loads (S(m' - m0)) n))
                                         (load_addr_nme:=(Eload chunk (build_loads (S(m' - m0)) n))).
      assert (all_addr_no_overflow CE) as h_nooverf_ by (eapply all_addr_nooverf_cons;eauto).
      destruct h_stk_mtch_a_s_m_ /sng.
      * apply transl_name_nodup_cons;auto.
        eapply h_nooverf_;eauto.
      * unfold build_loads.
        inversion h_CM_eval_expr_nme_t_nme_t_v_ /sng.
        econstructor;eauto.
        -- eapply chained_stack_structure_decomp_S_2';eauto.
           econstructor;eauto.
           eapply cm_eval_addrstack_zero_chain;eauto.
        -- eapply eval_expr_const_indep;eauto.
      * inversion  h_eval_name_nme_v_;subst.
        econstructor.
        eapply STACK.nodupG_fetchG_cons;eauto.
      * unfold build_loads, make_load.
        now rewrite h_eq_access_mode_cm_typ_nme_By_value_.
      * destruct h_and_transl_value_CM_eval_expr_ /sng.
        exists x;split;auto.
        Opaque build_loads_.
        unfold build_loads in h_CM_eval_expr_Eload_x_ |- *.
        Transparent build_loads_.
        inversion h_CM_eval_expr_Eload_x_ /sng.
        econstructor.
        2:eauto.
        inversion h_CM_eval_expr_Ebinop_vaddr_ /sng.
        econstructor;eauto.
        -- specialize chained_stack_structure_decomp_S_2 with (1:=h_chain_m_S_vptr_)  (2:=h_CM_eval_expr_Eload_v1_) ;intro h.
           decomp h.
           assert (sp'=(Values.Vptr b' Ptrofs.zero)).
           { inversion h_CM_eval_expr_Eload_sp'_;subst /sng.
             assert (vaddr0=(Values.Vptr b Ptrofs.zero)).
             { eapply det_cm_eval_addrstack_zero_chain;eauto. }
             subst.
             rewrite h_eq_loadv_vaddr0_sp'_ in h_eq_loadv_vptr_vptr_.
             now inversion h_eq_loadv_vptr_vptr_. }
           subst.
           assumption.
        -- eapply eval_expr_const_indep;eauto.
Qed.

Lemma exact_level_transl_variable: forall st astnum CE nme δ n,
    CompilEnv.exact_levelG CE
    -> transl_variable st CE astnum nme = Errors.OK (build_loads δ n)
    -> (δ < (Datatypes.length CE))%nat.
Proof.
  intros /sng.
  functional inversion h_eq_transl_var_bldlds_ /sng.
  specialize build_loads__inj with (1:=h_eq_bldlds_Econst_sub_bldlds_) as ? /sng.
  subst.
  erewrite <- CompilEnv.exact_lvl_lvl_of_top with (2:=h_eq_lvloftop_CE_m'_);eauto.
  lia.
Qed.

Lemma exact_level_transl_name: forall st CE nme δ n,
    CompilEnv.exact_levelG CE
    -> transl_name st CE nme = Errors.OK (build_loads δ n)
    -> (δ < (Datatypes.length CE))%nat.
Proof.
  intros /sng.
  functional inversion h_eq_transl_name_bldlds_.
  eapply exact_level_transl_variable;eauto.
Qed.



(* We have translated all procedures of stbl, and they have all an address
   pointing to there translation *)
(* THIS PROPERTY IS FALSE. ONLY VISIBLE PROCEDURES FROM THE CURRENT CE
   VERIFY THIS PROPERTY. Problem is: this visible procedures are not
   stored in CE. Maybe they should...
 We would need to write a typing function, which would proceed the same way the compilation function does, with always the same CE.  *)

Definition stack_match_functions st stckptr CE locenv g m :=
  forall p pb_lvl pb,
    symboltable.fetch_proc p st = Some (pb_lvl, pb) (* p exists in st *)
    -> exists CE' CE'' paddr pnum fction lglobdef, (* then there we can compute its address in Cminor. *)
      CompilEnv.cut_until CE pb_lvl CE' CE''
      ∧ transl_procedure st CE'' pb_lvl pb = Errors.OK ((pnum,@AST.Gfun _ _ fction) :: lglobdef) (*  *)
      ∧ Cminor.eval_expr g stckptr locenv m
                         (Econst (Oaddrsymbol (transl_procid p) (Ptrofs.repr 0))) paddr
      ∧ Globalenvs.Genv.find_funct g paddr = Some fction.


(* Variable addresses are all disjoint *)
Definition stack_separate st CE sp locenv g m :=
  forall nme nme' addr_nme addr_nme'
         typ_nme typ_nme'  cm_typ_nme cm_typ_nme'
         k₁ δ₁ k₂ δ₂ chnk₁ chnk₂ ,
    type_of_name st nme = Errors.OK typ_nme ->
    type_of_name st nme' = Errors.OK typ_nme' ->
    transl_name st CE nme = Errors.OK addr_nme ->
    transl_name st CE nme' = Errors.OK addr_nme' ->
    transl_type st typ_nme = Errors.OK cm_typ_nme ->
    transl_type st typ_nme' = Errors.OK cm_typ_nme' ->
    Cminor.eval_expr g sp locenv m addr_nme (Values.Vptr k₁ δ₁) ->
    Cminor.eval_expr g sp locenv m addr_nme' (Values.Vptr k₂ δ₂) ->
    Ctypes.access_mode cm_typ_nme  = Ctypes.By_value chnk₁ ->
    Ctypes.access_mode cm_typ_nme' = Ctypes.By_value chnk₂ ->
    nme <> nme' ->
    (k₂ <> k₁
     \/ Ptrofs.unsigned δ₂ + Memdata.size_chunk chnk₂ <= Ptrofs.unsigned δ₁
     \/ Ptrofs.unsigned δ₁ + Memdata.size_chunk chnk₁ <= Ptrofs.unsigned δ₂).

Definition stack_freeable st CE sp g locenv m :=
  forall a chk id id_t b ofs,
    (* translating the variabe to a Cminor load address *)
    transl_variable st CE a id = Errors.OK id_t ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g sp locenv m id_t (Values.Vptr b ofs) ->
    (* Size of variable in Cminor memorry *)
    compute_chnk st (Identifier a id) = Errors.OK chk ->
    Mem.valid_access m chk b (Ptrofs.unsigned ofs) Freeable.


(* TODO: swap arguments *)
Definition gt_snd (x y:(idnum * CompilEnv.V)) := snd y < snd x.
Definition gt_fst (x y:(CompilEnv.scope_level * localframe)) := (fst y < fst x)%nat.

Definition eq_fst_idnum (x y : idnum * CompilEnv.V) := fst x = fst y.

Arguments eq_fst_idnum !x !y.
Local Hint Unfold eq_fst_idnum : spark.

Definition gt_x_fst_y x (y:(CompilEnv.scope_level * localframe)) := (fst y < x)%nat.
Definition gt_fst_x_y (x:(CompilEnv.scope_level * localframe)) y := (y < fst x)%nat.
Definition gt_x_snd_y x (y:(idnum * CompilEnv.V)) := snd y < x.
Definition gt_snd_x_y (x:(idnum * CompilEnv.V)) y := y < snd x.

Notation "X '1<1' Y" := (gt_fst Y X) (at level 80).
Notation "X '2<2' Y" := (gt_snd Y X) (at level 80).
Notation "X '<2' Y" := (gt_x_snd_y Y X) (at level 80).
Notation "X '2<' Y" := (gt_snd_x_y Y X) (at level 80).


Lemma gt_snd_1 x y z : gt_snd (x,y) z = gt_x_snd_y y z.
Proof.
  reflexivity.
Qed.

Lemma gt_snd_2 x y z : gt_snd x (y,z) = gt_snd_x_y x z.
Proof.
  reflexivity.
Qed.

Lemma gt_fst_1 x y z : gt_fst (x,y) z = gt_x_fst_y x z.
Proof.
  reflexivity.
Qed.

Lemma gt_fst_2 x y z : gt_fst x (y,z) = gt_fst_x_y x y.
Proof.
  reflexivity.
Qed.

Local Hint Resolve gt_snd_1 gt_snd_2 gt_fst_1 gt_fst_2 : spark.

(* Local frames are ordered in the sense that they are stored by increasing offests. *)
Definition increasing_order: localframe -> Prop :=
  StronglySorted gt_snd.

Definition increasing_order_fr (f:CompilEnv.frame) :=
  increasing_order(CompilEnv.store_of f).

Definition all_frm_increasing CE := Forall increasing_order_fr CE.


Definition upper_bound fr sz := forall nme nme_ofs,
    CompilEnv.fetches nme fr = Some nme_ofs -> Z.lt nme_ofs sz.

(* the global stack is in incresing level. *)
(* Lemma exact_level_increasing_orderG: ∀ stk: CompilEnv.stack, *)
(*     exact_levelG stk -> StronglySorted gt_fst stk. *)

Definition stbl_var_types_ok st :=
  ∀ nme t, type_of_name st nme = Errors.OK t ->
           ∃ nme_type_t, transl_type st t = Errors.OK nme_type_t.

(*
(* The AST provided by gnat/sireum are supposed to have no two variables sharing
   the same name. This should imply that there are no duplication of name in CE. *)
(* intra-store *)
Definition stack_CE_NoDup (CE : compilenv) := 
(*   List.Forall (fun x => match x with (lvl,sto) => NoDupA eq sto end) CE. *)
  forall nme lvl sto (sto' sto'':localframe),
    CompilEnv.frameG nme CE = Some (lvl,sto) ->
    CompilEnv.cuts_to nme sto = (sto',sto'') ->
    CompilEnv.resides nme sto'' = false.

(* extra-store *)
Definition stack_CE_NoDup_G (CE : compilenv) := 
  forall nme lvl sto CE' CE'',
    CompilEnv.frameG nme CE = Some (lvl,sto) ->
    CompilEnv.cut_until CE lvl CE' CE'' ->
    CompilEnv.resideG nme CE'' = false.
*)




Record safe_cm_env st (CE:compilenv) (sp:Values.val) locenv g m: Prop :=
  mk_safe_cm_env {
      me_stack_match_addresses: @stack_match_addresses st CE sp locenv g m;
      me_stack_match_functions: stack_match_functions st sp CE locenv g m ;
      me_stack_separate: stack_separate st CE sp locenv g m;
      me_stack_localstack_aligned: stack_localstack_aligned (Datatypes.length CE) locenv g m sp;
      me_stack_no_null_offset: stack_no_null_offset CE;
      me_stack_freeable: stack_freeable st CE sp g locenv m;
      me_chain_struct: chained_stack_structure m (Datatypes.length CE) sp 
    }.



(* See CminorgenProof.v@205. *)
(** The Memory bisimilarity/invariant property states that

 -[me_overflow] Spark stack [s] is ok wrt overflows 
 - Compilation environment [CE] contains exactly variables of spark
   stack [s]
 - All variable of [CE] are non overlapping (spark property)
 - The structure of the chaines stack in Cminor is maintained:
 -- Load (Load...(Load 0)) yields to some frame f and a null offset
    ([localstack_aligned])
 -- and no variable overlap with it ([no_null_offset]).
 - the value of a variable is equal to the value of its translation.
   (Its translation is currently an expression of the form
   ELoad((Eload(Eload ...(Eload(0)))) + n)).
 - spark variables and there translated address yield the same
   (translated) value. i.e. the two memories commute. *)
Record match_env st s CE sp locenv g m: Prop :=
  mk_match_env {
      me_stack_match: stack_match st s CE sp locenv g m;
      me_stack_match_CE: stack_match_CE s CE;
      me_stack_match_lgth: stack_match_lgth s CE;
      me_noDup_s: STACK.NoDup s;
      me_noDup_G_s: STACK.NoDup_G s;
      me_exact_levelG: STACK.exact_levelG s;
      (* me_stack_complete: stack_complete st s CE; useless now that stack_match_CE_ is in both directions *)
      me_safe_cm_env: safe_cm_env st CE sp locenv g m;
      me_overflow: safe_stack s; (* Put this somewhere else, concerns only s *)
    }.

Arguments me_stack_match : default implicits.
Arguments me_stack_match_addresses : default implicits.
Arguments me_stack_match_CE : default implicits.
Arguments me_stack_match_lgth : default implicits.
Arguments me_noDup_s : default implicits.
Arguments me_noDup_G_s : default implicits.
Arguments me_exact_levelG : default implicits.
Arguments me_stack_match_functions : default implicits.
Arguments me_overflow : default implicits.
Arguments me_stack_no_null_offset : default implicits.
Arguments me_stack_localstack_aligned : default implicits.
Arguments me_stack_separate : default implicits.
Arguments me_stack_freeable : default implicits.
(* Arguments me_stack_complete : default implicits. *)
Arguments me_safe_cm_env : default implicits.
Arguments me_chain_struct : default implicits.

(** The compilation environment has some intrinsic properties:
 - Frame are numbered in increasing order in the global store
 - In each frame variables are numbered in increasing order
 - variable addresses do not overflow. *)
Record invariant_compile CE stbl :=
  { ci_exact_lvls: CompilEnv.exact_levelG CE ;
    ci_increasing_ids: all_frm_increasing CE ;
    ci_no_overflow: all_addr_no_overflow CE ;
    ci_stbl_var_types_ok: stbl_var_types_ok stbl;
    ce_nodup_CE: CompilEnv.NoDup CE;
    ce_nodup_G_CE: CompilEnv.NoDup_G CE }.

Arguments ci_increasing_ids : default implicits.
Arguments ci_no_overflow : default implicits.
Arguments ci_stbl_var_types_ok : default implicits.
Arguments ce_nodup_CE: default implicits.
Arguments ce_nodup_G_CE: default implicits.

Local Hint Resolve ci_exact_lvls ci_increasing_ids ci_no_overflow ci_stbl_var_types_ok ce_nodup_G_CE ce_nodup_G_CE : spark.
Local Hint Resolve me_stack_match_addresses me_stack_match_functions me_stack_separate me_stack_localstack_aligned
     me_stack_no_null_offset me_stack_freeable me_chain_struct : spark.
Local Hint Resolve me_stack_match me_stack_match_CE me_stack_match_lgth (* me_stack_complete *) me_overflow me_safe_cm_env : spark.


Inductive strong_match_env stbl: STACK.state → compilenv → Values.val → env → genv → mem → Prop :=
| C1: forall v locenv g m,
    match_env stbl [] [] v locenv g m ->
    strong_match_env stbl [] [] v locenv g m
| C2: forall lvl sto s stoCE CE v v' locenv locenv' g m,
    strong_match_env stbl s CE v locenv g m ->
    Mem.loadv AST.Mint32 m v' = Some v ->
    match_env stbl ((lvl,sto)::s) ((lvl,stoCE)::CE) v' locenv' g m ->
    strong_match_env stbl ((lvl,sto)::s) ((lvl,stoCE)::CE) v' locenv' g m.

(*

Definition strong_match_env_2_ (st : symboltable) (s : STACK.state) (CE : compilenv)
           (sp : Values.val) (locenv : env) (g : genv) (m : mem) : Prop :=
  forall lvl CE' CE'',
    CompilEnv.cut_until CE lvl CE' CE'' ->
    Datatypes.length CE'' = lvl ->
    exists sp'',
      (* following chaining params starting from the current one *)
      repeat_Mem_loadv AST.Mint32 m lvl sp sp''
      ∧ exists s' s'' locenv'', STACK.cut_until s lvl s' s''  ∧  match_env_ st s'' CE'' sp'' locenv'' g m.
*)

(** Hypothesis renaming stuff *)
Ltac rename_hyp3 n th :=
  match th with
  | _ => rename_stck_match n th
  | upper_bound ?fr ?sz => name (`_upb` ++ fr#n ++ sz#n)
  | match_env _ _ _ _ _ _ _ => name (`_match_env`)
  (* | all_addr_no_overflow ?CE => name (`alladdr_nooverf` CE) *)
  (* | all_addr_no_overflow _ => name (`alladdr_nooverf` ) *)
  | all_frm_increasing ?x => name (`_allincr` ++ x)
  | stack_match_functions _ _ _ _ _ _ => name (`_stk_mtch_fun`)
  | stack_separate _ ?CE _ _ _ ?m => name (`_separate` ++ CE#n ++ m#n)
  | stack_freeable _ ?CE _ _ _ ?m => name (`_freeable` ++ CE#n ++ m#n)
  | safe_cm_env ?st ?CE ?stkptr ?locenv ?g ?m => name (`_safe_cm` ++ CE#n ++ m#n)
  | invariant_compile ?CE ?stbl => name (`_inv_comp` ++ CE#n ++ stbl#n)
  | increasing_order_fr ?x => name (`_incr_order_fr` x#n)
  | (gt_fst ++ ?x ++ ?y) => name (`_gtfst` ++ x#n ++ y#n)
  | (gt_snd ++ ?x ++ ?y) => name (`_gtsnd` ++ x#n ++ y#n)
  | (gt_x_snd_y ++ ?x ++ ?y) => name (`_gtxsndy` x#n ++ y#n)
  | (gt_snd_x_y ++ ?x ++ ?y) => name (`_gtsndxy` x#n ++ y#n)
  end.

Ltac rename_sparkprf ::= rename_hyp3.

Ltac rename_hyp4 n th :=
  match th with
  | _ => rename_hyp3 n th
end.

Ltac rename_name_ce h th :=
  match reverse goal with
  | H: fetch_var_type ?X _ = Errors.OK h |- _  => name (`type` ++ X#(S O))
  | H: id (fetch_var_type ?X _ = Errors.OK h) |- _ => name (`type` ++ X#(S O))
  | H: (value_at_addr _ _ ?X = Errors.OK h) |- _ => name (`val_at` ++ X#(S O))
  | H: id (value_at_addr _ _ ?X = Errors.OK h) |- _ => name (`val_at` ++ X#(S O))
  | H: transl_variable _ _ _ ?X = Errors.OK h |- _ => name (X## ++ `_t`)
  | H: id (transl_variable _ _ _ ?X = Errors.OK h) |- _ => name (X## ++ `_t`)
  | H: transl_value ?X h |- _ => name (X## ++ `_t`)
  | H: id (transl_value ?X  h) |- _ => name (X## ++ `_t`)
  | H: id (CompilEnv.frameG ?X _ = Some (h, _)) |- _ => name (`lvl` ++ X#(S O))
  | H: CompilEnv.frameG ?X _ = Some (h, _) |- _ => name (`lvl` ++ X#(S O))
  | H: id (CompilEnv.frameG ?X _ = Some (_, h)) |- _ => name (`fr` ++ X#(S O))
  | H: CompilEnv.frameG ?X _ = Some (_, h) |- _ => name (`fr` ++ X#(S O))
  | H: id (CompilEnv.fetchG ?X _ = Some h) |- _ => name (`δ` ++ X#(S O))
  | H: CompilEnv.fetchG ?X _ = Some h |- _ => name (`δ` ++ X#(S O))
  | H: id (CompilEnv.fetchG ?X _ = h) |- _ => name (`δ` ++ X#(S O))
  | H: CompilEnv.fetchG ?X _ = h |- _ => name (`δ` ++ X#(S O))
  | _ => rename_var_from_context h th
  end.

Ltac rename_sparkprf ::= rename_hyp4.
Ltac rename_name_sparkprf ::=  rename_name_ce.

Ltac rename_hyp_cut n th :=
  match th with
  | CompilEnv.cut_until ?CE ?lvl ?CE' ?CE'' => name (`_CEcut` ++ CE#n ++ lvl#n)
  | STACK.cut_until ?CE ?lvl ?CE' ?CE'' => name (`_stkcut` ++ CE#n ++ lvl#n)
(*   | CE_well_formed ?CE => name (`CEwf_` CE#n) *)
(*   | CE_well_formed ?CE => name (`CEwf`) *)
  | CompilEnv.NoDup ?CE => name (`_CEnodup` ++ CE#n)
  | CompilEnv.NoDup_G ?CE => name (`_CEnodupG` ++ CE#n)
  | _ => rename_hyp4 n th
  end.
Ltac rename_sparkprf ::= rename_hyp_cut.


Ltac rename_hyp_strong n th :=
  match th with

  | strong_match_env ?st ?s ?CE ?sp ?locenv ?g ?m => name (`_strg_mtch` ++ s#n ++ CE#n ++ m#n)
(*
  | strong_match_env_2_ ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "strg_mtch2_" s "_" CE "_" m
*)
  | _ => rename_hyp_cut n th
  end.
Ltac rename_sparkprf ::= rename_hyp_strong.

Definition eq_param_name p1 p2 := p1.(parameter_name) = p2.(parameter_name).



Lemma all_frm_increasing_sublist: forall x CE,
    all_frm_increasing (x::CE)
    -> all_frm_increasing CE.
Proof.
  intros x CE H.
  inversion H;cbn in *;auto.
Qed.

Definition stack_push_all_new_ sto CE:= (forall id, CompilEnv.reside id sto = true -> CompilEnv.resideG id CE = false).

Definition invariant_to_locenv g sp m exp :=
  forall l l' x, Cminor.eval_expr g sp l m exp x -> Cminor.eval_expr g sp l' m exp x.

Ltac rename_stack_push_all_new_ n th :=
  match th with
  | stack_push_all_new_ ?sto ?CE => name (`_stckpushallnew` ++ sto#n ++ CE#n)
  | invariant_to_locenv _ _ ?m ?e => name (`_inv_to_locenv` ++ m#n ++ e#n)
  | _ => rename_hyp_strong n th
  end.
Ltac rename_sparkprf ::= rename_stack_push_all_new_.

Lemma all_addr_no_overflow_sublist: forall x CE,
    stack_push_all_new_ x CE
    -> all_addr_no_overflow (x::CE)
    -> all_addr_no_overflow CE.
Proof.
  intros /sng.
  red in h_no_overf_x_CE_.
  red.
  intros /sng.
  apply h_no_overf_x_CE_ with id.
  cbn.
  destruct (CompilEnv.fetch id x) eqn:? /sng.
  - apply CompilEnv.fetch_ok in h_eq_CEfetch_id_x_t_.
    apply h_stckpushallnew_x_CE_ in h_eq_CEfetch_id_x_t_.
    apply CompilEnv.fetchG_ok in h_eq_CEfetchG_id_CE_δ_id_.
    rewrite h_eq_CEfetch_id_x_t_ in h_eq_CEfetchG_id_CE_δ_id_.
    discriminate.
  - assumption.
Qed.



Lemma stack_CE_NoDup_G_stack_push_all_new_: forall x CE,
    CompilEnv.exact_levelG (x::CE) ->
    CompilEnv.NoDup_G (x::CE) -> 
    stack_push_all_new_ x CE.
Proof.
  intros /sng.
  red;intros /sng.
  eapply CompilEnv.nodup_G_cons_2;eauto.
Qed.


Lemma invariant_compile_subcons: forall st x CE,
    invariant_compile (x::CE) st
    -> invariant_compile CE st.
Proof.
  intros /sng.
  inversion h_inv_comp_x_CE_st_;cbn in *.
  split;eauto.
  - eapply CompilEnv.exact_levelG_sublist;eauto.
  - eapply all_frm_increasing_sublist;eauto.
  - eapply all_addr_no_overflow_sublist;eauto.
    apply stack_CE_NoDup_G_stack_push_all_new_;auto.
  - eapply CompilEnv.stack_NoDup_cons;eauto.
  - eapply CompilEnv.stack_NoDup_G_cons;eauto.
Qed.




Lemma invariant_compile_sublist: forall st CE1 CE2,
    invariant_compile (CE1 ++ CE2) st
    -> invariant_compile CE2 st.
Proof.
  induction CE1;simpl;intros /sng.
  - auto.
  - apply h_all_inv_comp_;auto.
    eapply invariant_compile_subcons;eauto.
Qed.

Lemma exact_lvlG_cut_until: forall CE lvl CE' CE'',
    CompilEnv.exact_levelG CE ->
    CompilEnv.cut_until CE lvl CE' CE'' ->
    CompilEnv.exact_levelG CE''.
Proof.
  intros until 1 /sng.
  revert lvl CE' CE''.
  induction h_exct_lvlG_CE_;intros  /sng.
  - inversion h_CEcut_nil_lvl_;subst /sng.
    constructor.
  - inversion h_CEcut_length_fr_stk_lvl_ /sng.
    + constructor.
      assumption.
    + eapply h_all_exct_lvlG_;eauto.
Qed.

Lemma exact_lvlG_nil_left: forall CE,
  CompilEnv.exact_levelG CE ->
  CompilEnv.cut_until CE (Datatypes.length CE) [ ] CE.
Proof.
  intros CE.
  destruct CE;simpl;intros /sng.
  - constructor.
  - constructor.
    inversion h_exct_lvlG_f_CE_.
    simpl.
    lia.
Qed.

Lemma transl_variable_exact_lvl_le_toplvl:
  forall st astnum id CE δlvl n,
    CompilEnv.exact_levelG CE ->          
    transl_variable st CE astnum id = Errors.OK (build_loads δlvl n) ->
    (δlvl < (Datatypes.length CE))%nat.
Proof.
  intros /sng.
  functional inversion h_eq_transl_var_bldlds_ /sng.
  specialize CompilEnv.exact_lvl_level_of_top with (1:=h_exct_lvlG_CE_)(2:=h_eq_CEframeG_id_CE_lvl_id_fr_id_) as h /sng.
  decomp h_ex_and_.
  rewrite h_eq_lvloftop_CE_m'_ in h_eq_lvloftop_CE_top_.
  invclear h_eq_lvloftop_CE_top_ /sng.
  apply CompilEnv.exact_lvl_lvl_of_top in h_eq_lvloftop_CE_m'_;eauto.
  rewrite <- h_eq_lvloftop_CE_m'_ in *.
  specialize build_loads__inj with (1:=h_eq_bldlds_Econst_sub_bldlds_) as ? /sng.
  subst.
  lia.
Qed.


Lemma no_overflow_NoDup_G__app: forall CE CE', 
    CompilEnv.NoDup_G (CE++ CE') -> 
    all_addr_no_overflow (CE++ CE') -> all_addr_no_overflow CE'.
Proof.
  induction CE.
  - cbn;auto.
  - cbn.
    intros /sng. 
    apply IHCE;auto.
    + eapply CompilEnv.stack_NoDup_G_cons;eauto.
    + eapply all_addr_nooverf_cons;eauto.
Qed.

Lemma no_overflow_NoDup_G_cut: forall n CE CE' CE'',
    CompilEnv.NoDup_G CE ->
    CompilEnv.cut_until CE n CE' CE'' -> 
    all_addr_no_overflow (CE'++ CE'') → all_addr_no_overflow CE''.
Proof.
  intros /sng.
  eapply no_overflow_NoDup_G__app;eauto.
  erewrite CompilEnv.cut_until_spec1;eauto.
Qed.


Lemma no_null_offset_NoDup_G_cons:
  forall x CE',  CompilEnv.NoDup_G (x :: CE') -> 
            stack_no_null_offset (x :: CE') -> stack_no_null_offset CE'.
Proof.
  red.
  intros /sng.
  red in h_nonul_ofs_x_CE'_.
  red in h_CEnodupG_x_CE'_.
  red.
  intros /sng.
  eapply h_nonul_ofs_x_CE'_ with nme.
  cbn.
  specialize CompilEnv.nodup_G_cons with(1:=h_CEnodupG_x_CE'_);intro h.
  assert (CompilEnv.fetch nme x = None) /sng.
  { apply CompilEnv.reside_false_fetch_none.
    apply h.
    eapply CompilEnv.fetchG_ok;eauto. }
  now rewrite h_eq_CEfetch_nme_x_None_.
Qed.

Lemma no_null_offset_NoDup_G_app:
  forall CE CE',  CompilEnv.NoDup_G (CE++ CE') -> 
                  stack_no_null_offset (CE++ CE') -> stack_no_null_offset CE'.
Proof.
  induction CE.
  - cbn;auto.
  - cbn.
    intros /sng. 
    apply IHCE;auto.
    + eapply CompilEnv.stack_NoDup_G_cons;eauto.
    + eapply no_null_offset_NoDup_G_cons;eauto.
Qed.

Lemma no_null_offset_NoDup_G_cut: forall n CE CE' CE'',
    CompilEnv.NoDup_G CE ->
    CompilEnv.cut_until CE n CE' CE'' -> 
    stack_no_null_offset (CE'++ CE'') -> stack_no_null_offset CE''.
Proof.
  intros /sng.
  eapply no_null_offset_NoDup_G_app;eauto.
  erewrite CompilEnv.cut_until_spec1;eauto.
Qed.

Lemma stack_match_empty: forall st sp locenv g m,
    stack_match st [] [] sp locenv g m.
Proof.
  intros st sp locenv g m.
  red;intros /sng.
  functional inversion h_eq_transl_name_nme_t_.
Qed.

Lemma stack_match_addressesempty: forall st sp locenv g m,
    stack_match_addresses st [] sp locenv g m.
Proof.
  intros /sng.
  red;intros /sng.
  functional inversion h_eq_transl_name_nme_t_.
Qed.

Lemma stack_match_CE_empty: stack_match_CE [] [].
Proof.
  red;intros /sng.
  split;intros /sng.
  - functional inversion h_eq_frameG_nme_nil_lvl_sto_.
  - cbn in *.
    discriminate.
Qed.

Lemma stack_match_lgth_empty: stack_match_lgth [] [].
Proof.
  now red.
Qed.
 
Lemma stack_complete_empty: forall st,stack_complete st [ ] [ ].
Proof.
  red;intros /sng.

  functional inversion h_eq_transl_var_nme_t_ /sng.    
  functional inversion h_eq_CEframeG_nme_nil_lvl_nme_fr_nme_.
Qed.

Lemma stack_separate_empty: forall st sp locenv g m,
    stack_separate st [ ] sp locenv g m.
Proof.
  red;intros /sng.
  functional inversion h_eq_transl_name_nme_t_ /sng.
Qed.
 
(* frame pointer is always with offset zero. We will show later that it is also true for the enclosing frames. *)
Lemma match_env_sp_zero:forall st CE x sp locenv g m, match_env st CE x sp locenv g m -> exists b, sp = Values.Vptr b Ptrofs.zero.
Proof.
  intros /sng. 
  specialize (me_stack_localstack_aligned (me_safe_cm_env h_match_env_)) as ? /sng.
  red in h_aligned_g_m_.
  assert (O ≤ Datatypes.length x) by lia /sng.
  specialize h_aligned_g_m_ with (1:=h_le_0_length_).
  decomp h_aligned_g_m_.
  cbn in*.
  exists b_δ.
  inversion h_CM_eval_expr_bldlds_vptr_ /sng.
  cbn in h_eq_evalcst_sp_Oaddrstack_vptr_.
  inversion h_eq_evalcst_sp_Oaddrstack_vptr_ /sng.
  unfold Values.Val.offset_ptr in h_eq_val_offs_sp_zero_vptr_.
  destruct sp;try discriminate.
  cbn.
  rewrite Ptrofs.add_zero.
  reflexivity.
Qed.

(* TODO: move this in spark. *)
Lemma stack_NoDup_empty: STACK.NoDup [ ].
Proof.
  red;simpl;now intros /sng.
Qed.

Lemma match_env_empty: forall st sp b locenv g m,
    (* stack_match_functions st sp' [ ] locenv' g m -> *)
    sp = (Values.Vptr b Ptrofs.zero) ->
    match_env st [ ] [ ] sp locenv g m.
Proof.
  intros /sng.
  split (* apply h_match_env_. *).
  7: split.
  + apply stack_match_empty.
  + red;intros /sng.
    split;intros /sng.
    * functional inversion h_eq_frameG_nme_nil_lvl_sto_.
    * cbn in h_eq_CEframeG_nme_nil_lvl_fr_nme_.
      discriminate.
  + now red.
  + apply stack_NoDup_empty.
  + constructor.
  + constructor.
(*  + red;intros /sng.
    functional inversion h_eq_transl_var_ /sng.
    functional inversion h_eq_CEfetchG_nme_.*)
  + apply stack_match_addressesempty.
  + admit. (* This needs typing proofs *)
  + red;intros /sng.
    functional inversion h_eq_transl_name_nme'_t_.
  + red.
    intros /sng.
    simpl in *.
    assert(δ_lvl = 0)%nat by lia.
    subst;cbn.
    eexists.
    econstructor.
    cbn.
    rewrite Ptrofs.add_zero.
    reflexivity.
  + red;intros /sng.
    red;intros /sng.
    functional inversion h_eq_CEfetchG_nme_nil_δ_nme_.
  + red.
    intros /sng.
    exfalso.
    functional inversion h_eq_transl_var_id_t_ /sng.
    functional inversion h_eq_CEfetchG_id_nil_δ_id_.
  + cbn. subst. constructor.
  + red;intros /sng.
    functional inversion h_eq_SfetchG_id_nil_n_.
Admitted.


Lemma eval_expr_Econst_inv_locenv :  forall g sp locenv m c v,
    Cminor.eval_expr g sp locenv m (Econst c) v -> 
    forall locenv' m' , Cminor.eval_expr g sp locenv' m' (Econst c) v.
Proof.
  intros g sp locenv m c v H locenv' m'.
  inversion H.
  now constructor.
Qed.

Lemma eval_expr_Econst_inv_locenv_noaddr :  forall g sp locenv m c v,
    Cminor.eval_expr g sp locenv m (Econst c) v ->
    match c with
    | Ointconst _ => True
    | Ofloatconst _ => True
    | Osingleconst _ => True
    | Olongconst _ => True
    | Oaddrsymbol _ _ => False
    | Oaddrstack _ => False
    end -> 
    forall g' sp' locenv' m' , Cminor.eval_expr g' sp' locenv' m' (Econst c) v.
Proof.
  intros g sp locenv m c v H H' locenv' m'.
  inversion H;subst.
  destruct c; cbn in H';(try now exfalso); now constructor.
Qed.



Lemma eval_expr_build_loads_inv_locenv :  forall δ_lvl g sp locenv m base nme_t_v,
    (* base's evaluation is independent of the local environment *)
    invariant_to_locenv g sp m base ->
    Cminor.eval_expr g sp locenv m (build_loads_ base δ_lvl) nme_t_v ->
    forall locenv',
      Cminor.eval_expr g sp locenv' m (build_loads_ base δ_lvl) nme_t_v.
Proof.
  intros δ_lvl.
  induction δ_lvl;simpl;intros /sng.
  - eapply h_inv_to_locenv_m_base_;eauto.
  - inversion h_CM_eval_expr_Eload_nme_t_v_.
    econstructor;eauto.
Qed.

Lemma Econst_locenv_indep g sp m const: invariant_to_locenv g sp m (Econst const).
Proof.
  red.
  intros /sng.
  inversion h_CM_eval_expr_Econst_x_ /sng.
  econstructor;eauto.
Qed.

Lemma eval_expr_build_load_const_inv_locenv :  forall δ_id g sp locenv m cste nme_t_v,
    Cminor.eval_expr g sp locenv m (build_loads_ (Econst cste) δ_id) nme_t_v ->
    forall locenv',
      Cminor.eval_expr g sp locenv' m (build_loads_ (Econst cste) δ_id) nme_t_v.
Proof.
  intros /sng.
  unfold build_loads in *.
  eapply eval_expr_build_loads_inv_locenv;eauto.
  apply Econst_locenv_indep.
Qed.

Lemma eval_expr_build_load_inv_locenv :  forall δ_lvl δ_id g sp locenv m  nme_t_v,
    Cminor.eval_expr g sp locenv m (build_loads δ_lvl δ_id) nme_t_v ->
    forall locenv',
      Cminor.eval_expr g sp locenv' m (build_loads δ_lvl δ_id) nme_t_v.
Proof.
  intros /sng.
  unfold build_loads in *.
  inversion h_CM_eval_expr_bldlds_nme_t_v_ /sng.
  econstructor;eauto.
  - eapply eval_expr_build_load_const_inv_locenv;eauto.
  - eapply eval_expr_Econst_inv_locenv;eauto.
Qed.

Lemma eval_expr_transl_variable_inv_locenv: forall st CE astnum g sp locenv m nme nme_t v,
          transl_variable st CE astnum nme = Errors.OK nme_t ->
          Cminor.eval_expr g sp locenv m nme_t v ->
          forall locenv', Cminor.eval_expr g sp locenv' m nme_t v.
Proof.
  intros /sng.
  functional inversion h_eq_transl_var_nme_t_;subst /sng.
  eapply eval_expr_build_load_inv_locenv;eauto.
Qed.

Lemma eval_expr_transl_name_inv_locenv: forall st CE  g sp locenv m nme nme_t v,
          transl_name st CE nme = Errors.OK nme_t ->
          Cminor.eval_expr g sp locenv m nme_t v ->
          forall locenv', Cminor.eval_expr g sp locenv' m nme_t v.
Proof.
  intros /sng.
  functional inversion h_eq_transl_name_nme_t_;subst /sng.
  eapply eval_expr_transl_variable_inv_locenv;eauto.
Qed.

Lemma stack_match_addr_inv_locenv :  forall st CE sp locenv g m,
    stack_match_addresses st sp CE locenv g m -> 
    forall locenv',
      stack_match_addresses st sp CE locenv' g m.
Proof.
  intros /sng.
  red.
  intros /sng.
  red in h_stk_mtch_addr_CE_m_.
  specialize h_stk_mtch_addr_CE_m_ with (1:= h_eq_transl_name_nme_t_).
  decomp h_stk_mtch_addr_CE_m_.
  eexists.
  eapply eval_expr_transl_name_inv_locenv;eauto.
Qed.
      
Lemma stack_match_inv_locenv :  forall st s CE sp locenv g m,
    stack_match st s CE sp locenv g m -> 
    forall locenv',
      stack_match st s CE sp locenv' g m.
Proof.
  intros /sng.
  red.
  intros /sng.
  red in h_stk_mtch_s_m_.
  specialize h_stk_mtch_s_m_ with(vaddr := nme_t_v) (3:=h_eval_name_nme_v_) (5:=h_eq_type_of_name_st_nme_typ_nme_) (1:=h_eq_transl_name_nme_t_) (4:=h_eq_transl_type_cm_typ_nme_) (6:=h_eq_make_load_load_addr_nme_).
  destruct h_stk_mtch_s_m_ as [? [? ?]] /sng.
  - eapply eval_expr_transl_name_inv_locenv;eauto.
  - exists v_t;split;auto.
    functional inversion h_eq_make_load_load_addr_nme_;subst /sng.
    inversion h_CM_eval_expr_load_addr_nme_v_t_ /sng.
    econstructor;eauto.
    functional inversion h_eq_transl_name_nme_t_;subst /sng.
    functional inversion h_eq_transl_var_nme_t_;subst /sng.
    rewrite <- h_eq_loadv_nme_t_v0_v_t_.
    f_equal.
    eapply det_eval_expr;eauto.
    eapply eval_expr_build_load_inv_locenv;eauto.
Qed.
  
Lemma stack_match_functions_inv_locenv: forall stbl CE stkptr locenv g m,
    stack_match_functions stbl CE stkptr locenv g m ->
    forall locenv', stack_match_functions stbl CE stkptr locenv' g m.
Proof.
  intros /sng.
  red.
  intros /sng.
  decomp (h_stk_mtch_fun_ _ _ _ h_eq_fetch_proc_p_stbl_pb_lvl_pb_).
  exists CE',  CE'', paddr, pnum, fction, lglobdef;repeat apply conj; eauto 10.
  inversion h_CM_eval_expr_Econst_paddr_.
  econstructor;eauto.
Qed.
  
(** Currently locenv are not considered in match_env, this lemma could become
    more complex if we decide to optimize spark code by leaving in the locenv
    the variables that are not referred from nested procedures. match_env would
    stay the same but we should put a constraint on locenv' to contain the
    same variables than locenv. *)
Lemma match_env_inv_locenv : forall st s CE sp locenv g m,
    match_env st s CE sp locenv g m ->
    forall locenv', match_env st s CE sp locenv' g m.
Proof.
  intros /sng.
  split;[ | | | | | | split | ];try now apply h_match_env_.  
  - eapply stack_match_inv_locenv;eauto with spark.
  - eapply stack_match_addr_inv_locenv; eauto with spark.
  - eapply stack_match_functions_inv_locenv;eauto with spark.
  - pose proof me_stack_separate (me_safe_cm_env h_match_env_) as h_separate_.
    red in h_separate_.
    red;intros /sng.
    assert (Cminor.eval_expr g sp locenv m nme_t (Values.Vptr k₁ δ₁)) /sng.
    { pose proof (stack_match_inv_locenv st s CE sp locenv' g m) as h_stckmtch_.
      eapply eval_expr_transl_name_inv_locenv;eauto. }
    assert (Cminor.eval_expr g sp locenv m nme'_t (Values.Vptr k₂ δ₂)) /sng.
    { pose proof (stack_match_inv_locenv st s CE sp locenv' g m) as h_stckmtch_.
      eapply eval_expr_transl_name_inv_locenv;eauto. }
    specialize h_separate_ with (1:=h_eq_type_of_name_st_nme_typ_nme_)
                                (2:=h_eq_type_of_name_st_nme'_typ_nme'_).
    eauto.
  - pose proof me_stack_localstack_aligned (me_safe_cm_env h_match_env_) as h_align_.
    red in h_align_.
    red.
    intros /sng.
    specialize (h_align_ _ h_le_δ_lvl_length_).
    decomp h_align_;eauto.
    exists b_δ. 
    eapply eval_expr_build_load_const_inv_locenv;eauto.
  - pose proof me_stack_freeable (me_safe_cm_env h_match_env_) as ? /sng.
    red in h_freeable_CE_m_.
    red;intros /sng.
    eapply h_freeable_CE_m_;eauto.
    eapply eval_expr_transl_variable_inv_locenv;eauto.
Qed.


Lemma strong_match_env_inv_locenv : forall st s CE sp locenv g m,
    strong_match_env st s CE sp locenv g m ->
    forall locenv', strong_match_env st s CE sp locenv' g m.
Proof.
  intros until 1 /sng.
  induction h_strg_mtch_s_CE_m_;intros /sng.
  - constructor.
    eapply match_env_inv_locenv;eauto.
  - econstructor;eauto.
    eapply match_env_inv_locenv;eauto.
Qed.



Lemma stack_localstack_aligned_inv_locenv: forall lvl locenv g m sp,
    stack_localstack_aligned lvl locenv g m sp ->
    forall locenv', stack_localstack_aligned lvl locenv' g m sp.
Proof.
  intros /sng.
  red.
  intros /sng.
  decomp (h_aligned_g_m_ _ h_le_δ_lvl_lvl_).
  exists b_δ.
  eapply eval_expr_build_load_const_inv_locenv;eauto.
Qed.

Lemma stack_separate_inv_locenv: forall st CE sp locenv g m,
    stack_separate st CE sp locenv g m ->
    forall locenv', stack_separate st CE sp locenv' g m.
Proof.
  intros /sng.
  red.
  intros /sng.
  red in h_separate_CE_m_.
  specialize eval_expr_transl_name_inv_locenv with
      (1:=h_eq_transl_name_nme_t_) (2:=h_CM_eval_expr_nme_t_vptr_) (locenv':=locenv)
    as ? /sng.
  specialize eval_expr_transl_name_inv_locenv with (1:=h_eq_transl_name_nme'_t_) (2:=h_CM_eval_expr_nme'_t_vptr_) (locenv':=locenv) as ? /sng.
  specialize h_separate_CE_m_ with (1:=h_eq_type_of_name_st_nme_typ_nme_)
                                   (2:=h_eq_type_of_name_st_nme'_typ_nme'_).
  eapply h_separate_CE_m_;eauto.
Qed.

Lemma stack_freeable_inv_locenv: forall st CE sp locenv g m,
    stack_freeable st CE sp g locenv m ->
    forall locenv', stack_freeable st CE sp g locenv' m.
Proof.
  intros /sng.
  red.
  intros /sng.
  red in h_freeable_CE_m_.
  specialize eval_expr_transl_variable_inv_locenv with
      (1 := h_eq_transl_var_id_t_)(2:=h_CM_eval_expr_id_t_vptr_)(locenv':=locenv) as ? /sng. 
  eapply h_freeable_CE_m_;eauto.
Qed.

Lemma safe_cm_env_inv_locenv: forall stbl CE stkptr locenv g m,
    safe_cm_env stbl CE stkptr locenv g m ->
    forall locenv', safe_cm_env stbl CE stkptr locenv' g m.
Proof.
  intros /sng.
  constructor;eauto with spark.
  - eapply stack_match_addr_inv_locenv;eauto with spark.
  - eapply stack_match_functions_inv_locenv;eauto with spark.
  - eapply stack_separate_inv_locenv;eauto with spark.
  - eapply stack_localstack_aligned_inv_locenv;eauto with spark.
  - eapply stack_freeable_inv_locenv;eauto with spark.
Qed.


Lemma cut_until_exact_lvl:
  forall stoCE CE lvl,
    CompilEnv.exact_levelG (stoCE :: CE)
    -> CompilEnv.cut_until (stoCE :: CE) lvl [ ] (stoCE :: CE)
    -> CompilEnv.cut_until CE lvl [ ] CE.
Proof.
  intros /sng.
  destruct CE /sng.
  - constructor.
  - inversion h_CEcut_stoCE_CE_lvl_;subst /sng.
    destruct f /sng.
    inversion h_exct_lvlG_stoCE_CE_;subst;simpl in * /sng.
    constructor 2.
    simpl.
    inversion h_exct_lvlG_s_s0_CE_;subst.
    lia.
Qed.


Lemma cut_until_total: forall s lvl, exists s1 s2, STACK.cut_until s lvl s1 s2.
Proof.
  intros /sng. 
  induction s /sng.
  - exists (@nil STACK.frame).
    exists (@nil STACK.frame).
    constructor.
  - destruct (Nat.lt_decidable (STACK.level_of a) lvl).
    + exists (@nil STACK.frame).
      exists (a :: s).
      constructor 2;auto.
    + decomp h_ex_stkcut_.
      exists (a::s1).
      exists s2.
      constructor 3;auto.
Qed.



Lemma exact_lvl_cut_until_lgth_left: forall CE s,
    stack_match_lgth s CE ->
    STACK.exact_levelG s ->
    CompilEnv.exact_levelG CE ->
    forall CE1 CE2 lvl,
      CompilEnv.cut_until CE lvl CE1 CE2 ->
      exists s1 s2, STACK.cut_until s lvl s1 s2
                    /\ List.length s1 = List.length CE1.
Proof.
  intros /sng.
  (pose proof cut_until_total s lvl) /sng.
  decomp h_ex_stkcut_.
  exists s1,s2.
  split;auto.
  destruct (Nat.le_decidable lvl (Datatypes.length s)) /sng.
  - specialize STACK.cut_until_exact_levelG with (1:=h_exct_lvl_s_) (2:=h_le_lvl_length_)(3:=h_stkcut_s_lvl_);intro /ng.
    assert (lvl ≤ Datatypes.length CE) /sng.
    { red in h_stk_mtch_lgth_s_CE_.
      now rewrite <- h_stk_mtch_lgth_s_CE_. }
    specialize CompilEnv.cut_until_exact_levelG with (1:=h_exct_lvlG_CE_) (2:=h_le_lvl_length_0) (3:=h_CEcut_CE_lvl_);intro /sng.
    specialize CompilEnv.cut_until_spec1 with (1:=h_CEcut_CE_lvl_);intro /sng.
    specialize STACK.cut_until_spec1 with (1:=h_stkcut_s_lvl_);intro /sng.
    subst.
    red in h_stk_mtch_lgth_s_CE_.
    setoid_rewrite app_length in h_stk_mtch_lgth_s_CE_.
    lia.
  - assert ((lvl > Datatypes.length s)%nat) by lia /sng.
    
    specialize STACK.cut_until_exact_levelG_2 with (1:=h_exct_lvl_s_) (2:=h_gt_lvl_length_)(3:=h_stkcut_s_lvl_);intro /sng.
    assert (lvl > Datatypes.length CE)%nat /sng.
    { red in h_stk_mtch_lgth_s_CE_.
      now rewrite <- h_stk_mtch_lgth_s_CE_. }
    specialize CompilEnv.cut_until_exact_levelG_2 with (1:=h_exct_lvlG_CE_) (2:=h_gt_lvl_length_0) (3:=h_CEcut_CE_lvl_);intro /sng.
    specialize CompilEnv.cut_until_spec1 with (1:=h_CEcut_CE_lvl_);intro /sng.
    specialize STACK.cut_until_spec1 with (1:=h_stkcut_s_lvl_);intro /sng.
    subst.
    red in h_stk_mtch_lgth_s_CE_.
    setoid_rewrite app_length in h_stk_mtch_lgth_s_CE_.
    setoid_rewrite app_length in h_eq_length_s_length_.
    setoid_rewrite app_length in h_eq_length_CE_length_.
    lia.
Qed.

Lemma match_env_lgth: forall CE s,
    stack_match_lgth s CE ->
    STACK.exact_levelG s ->
    CompilEnv.exact_levelG CE ->
    forall CE1 CE2 lvl,
      CompilEnv.cut_until CE lvl CE1 CE2 ->
      exists s1 s2, STACK.cut_until s lvl s1 s2
                    /\ List.length s1 = List.length CE1.
Proof.
  eapply exact_lvl_cut_until_lgth_left;eauto.
Qed.


Lemma match_env_length_CE_s : ∀ st s CE sp locenv g m,
    match_env st s CE sp locenv g m ->
    Datatypes.length CE = Datatypes.length s.
Proof.
  intros /sng.
  (pose proof h_match_env_.(me_stack_match_lgth))/sng .
  now red in h_stk_mtch_lgth_s_CE_.
Qed.


(* Yet another hypothesis deducibility *)
Lemma strong_match_repeat_loadv : forall st s CE sp locenv g  m,
    strong_match_env st s CE sp locenv g m ->
    invariant_compile CE st ->
    forall CE' CE'' lvl,
      CompilEnv.cut_until CE lvl CE' CE'' -> 
      exists sp'',
        repeat_Mem_loadv AST.Mint32 m (Datatypes.length CE - lvl)%nat sp sp''.
Proof.
  intros until 1 /sng.
  induction h_strg_mtch_s_CE_m_;intros/sng.
  - rename v into sp.
    cbn.
    exists sp.
    constructor.
  - assert (invariant_compile CE st) /sng.
    { eapply invariant_compile_subcons;eauto. }
    assert (lvl=Datatypes.length CE).
    { (pose proof (ci_exact_lvls _ _ h_inv_comp_lvl_stoCE_CE_st_)) /sng.
      inversion h_exct_lvlG_lvl_stoCE_CE_ /sng.
      reflexivity. }

    rename v' into sp.
    rename v into sp'.
    specialize (h_impl_repeat_loadv_ h_inv_comp_CE_st_).
    inversion h_CEcut_lvl_stoCE_CE_lvl0_ /sng. (* cut reached or not *)
    * (* Reached *)
      cbn in *.
      destruct lvl0;try (exfalso;lia).
      subst.
      assert (Datatypes.length CE - lvl0 = 0)%nat by lia /sng.
      rewrite h_eq_sub_length_lvl0_0_.
      exists sp.
      constructor 1;auto.
    * (* not reached *)
      rename s' into CE'.
      specialize h_impl_repeat_loadv_ with (1:=h_CEcut_CE_lvl0_).
      destruct h_impl_repeat_loadv_ as [sp'' ?] /sng.
      exists sp''.
      cbn in *|-.
      cbn [Datatypes.length].
      assert ((S (Datatypes.length CE) - lvl0 = S (Datatypes.length CE - lvl0))%nat) by lia /sng.
      rewrite h_eq_sub_S_lvl0_S_.
      econstructor;eauto.
Qed.

Lemma strong_match_env_top_: forall st s CE sp locenv g m,
    strong_match_env st s CE sp locenv g m ->
    match_env st s CE sp locenv g m.
Proof.
  intros /sng.
  inversion h_strg_mtch_s_CE_m_;eauto.
Qed.

(* Very bad idea: this triggers name reusing, which confuses new hyps detection.
Local Open Scope autonaming_scope.
Ltac rename_name_CE_s h th :=
  match th with
  | CompilEnv.state  => name (`CE`)
  | compilenv  => name (`CE`)
  | STACK.state => name (`s`)
  | list STACK.frame => name (`s`)
  | _ => rename_name_ce h th
  end.
Local Close Scope autonaming_scope.

Ltac rename_name_sparkprf ::= rename_name_CE_s.
*)
Ltac ce_clean :=
  repeat match goal with
           H:CompilEnv.state |- _ => change compilenv in H
         | H:list CompilEnv.frame |- _ => change compilenv in H
         end.

Lemma strong_match_env_match_env_sublist_ : forall st s CE sp locenv g  m,
    strong_match_env st s CE sp locenv g m ->
    invariant_compile CE st ->
    forall CE' CE'' lvl,
      CompilEnv.cut_until CE lvl CE' CE'' -> 
      exists s' s'' sp'',
      STACK.cut_until s lvl s' s'' /\
      repeat_Mem_loadv AST.Mint32 m (Datatypes.length CE - lvl)%nat sp sp'' /\
      forall locenv,
        match_env st s'' CE'' sp'' locenv g m.
Proof.
  intros;ce_clean /sng.

  assert (Datatypes.length CE= Datatypes.length s) /sng.
  { specialize strong_match_env_top_ with (1:=h_strg_mtch_s_CE_m_) as ? /sng.
    eapply match_env_length_CE_s;eauto. }
  remember (Datatypes.length s) as n /sng.
  assert (exists s' s'', STACK.cut_until s lvl s' s'') /sng.
  { specialize strong_match_env_top_ with (1:=h_strg_mtch_s_CE_m_) as ? /sng.
    specialize exact_lvl_cut_until_lgth_left with (CE:=CE)(s:=s)(CE1:=CE')(CE2:=CE'') as ? /sng.
    edestruct h_impl_and_;eauto with spark /sng.
    - apply h_match_env_.
    - decomp h_ex_and_.
      eauto. }
  assert(exists sp'',repeat_Mem_loadv AST.Mint32 m (Datatypes.length CE - lvl)%nat sp sp'') /sng.
  { eapply strong_match_repeat_loadv;eauto. }
  decomp h_ex_repeat_loadv_.
  decom h_ex_stkcut_ /sg.
  match goal with
    H0 : STACK.cut_until s lvl s' s'' |- _ => autorename H0
  end.
  exists s'.
  exists s''.
  exists sp''.
  assert (Datatypes.length s' = Datatypes.length CE' ∧ Datatypes.length s'' = Datatypes.length CE'') /sng. {
    assert (STACK.exact_levelG s) /sng. {
      specialize strong_match_env_top_ with (1:=h_strg_mtch_s_CE_m_) as ? /sng.
      eapply h_match_env_. }
    assert (CompilEnv.exact_levelG CE) /sng. {
      eapply h_inv_comp_CE_st_. }
    assert (stack_match_lgth s CE) /sng. {
      specialize strong_match_env_top_ with (1:=h_strg_mtch_s_CE_m_) as ? /sng.
      eapply h_match_env_. }
    specialize match_env_lgth with (1:=h_stk_mtch_lgth_s_CE_) (3:=h_exct_lvlG_CE_)(2:=h_exct_lvl_s_) (4:=h_CEcut_CE_lvl_) as ? /sng.
    decomp h_ex_and_.
    specialize STACK.cut_until_uniqueness with (1:=h_stkcut_s_lvl_)(2:=h_stkcut_s_lvl_0) as ? /sng.
    decomp h_and_eq_s'_eq_s''_.
    specialize CompilEnv.cut_until_spec1 with (1:=h_CEcut_CE_lvl_) as ? /sng.
    specialize STACK.cut_until_spec1 with (1:=h_stkcut_s_lvl_) as ? /sng.
    split;auto.
    symmetry in h_eq_length_s1_length_.
    repeat rewrite app_length in h_eq_length_CE_length_.
    rewrite h_eq_length_s1_length_ in h_eq_length_CE_length_.
    lia. }
  decomp h_and_eq_length_eq_length_.

  specialize STACK.cut_until_spec1 with (1:=h_stkcut_s_lvl_) as h_eq_s_.
  specialize CompilEnv.cut_until_spec1 with (1:=h_CEcut_CE_lvl_) as h_eq_CE_.
  
  (* Set Ltac Debug. *)
  (* then_allnh ltac:(LibHyps.LibDecomp.decomp_logicals h_and_eq_length_eq_length_)  ltac:(fun lh => idtac lh). *)
  (* decompose_clear h_and_eq_length_eq_length_ /sng. *)
  (* specialize STACK.cut_until_spec1 with (1:=h_stkcut_s_lvl_) as h_eq_s_. *)
  (* specialize CompilEnv.cut_until_spec1 with (1:=h_CEcut_CE_lvl_) as h_eq_CE_. *)
  
  revert s' s'' st s sp locenv g m h_strg_mtch_s_CE_m_ h_inv_comp_CE_st_ h_eq_length_CE_length_ h_stkcut_s_lvl_ sp'' h_repeat_loadv_sub_sp_ h_eq_s_ h_eq_CE_ h_eq_length_s'_length_ h_eq_length_s''_length_.
  induction h_CEcut_CE_lvl_; ce_clean; (try rename s into CE)/ng; intros;repeat (split;[now auto|])/ng.
  - clear h_eq_app_nil_nil_nil_.
    simpl in *.
    specialize length_invnil with (1:=h_eq_length_s''_length_) as ? /sng.
    subst.
    simpl in h_repeat_loadv_sub_sp_.
    inversion h_repeat_loadv_sub_sp_;subst /sng.
    inversion h_strg_mtch_s_nil_m_.
    eapply match_env_inv_locenv;eauto.
  - clear h_eq_app_nil_f_CE_f_CE_.
    assert (CompilEnv.level_of f = Datatypes.length CE) /sng. {
      inversion h_inv_comp_f_CE_st_ /sng.
      inversion h_exct_lvlG_f_CE_ /sng.
      reflexivity. }
    assert (STACK.exact_levelG s) /sng. {
      specialize strong_match_env_top_ with (1:=h_strg_mtch_s_f_CE_m_) as ? /sng.
      eapply h_match_env_. }
    
    rewrite h_eq_level_of_f_length_ in h_lt_level_of_n_.
    simpl Datatypes.length in h_repeat_loadv_sub_sp_.
    assert (S (Datatypes.length CE) - n = 0)%nat /sng.
    { lia. }
    assert (s'=[]) /sng. {
      eapply length_invnil.
      assumption. }
    simpl in h_eq_app_s'_s''_s_.
    subst.
    rewrite h_eq_sub_S_n_0_ in h_repeat_loadv_sub_sp_.
    inversion h_repeat_loadv_sub_sp_ /sng.
    inversion h_strg_mtch_s_f_CE_m_ /sng.
    eapply match_env_inv_locenv;eauto.
  - simpl in h_eq_length_s'0_length_.
    specialize length_invcons with (1:=h_eq_length_s'0_length_) as ? /sng.
    decom h_ex_eq_s'0_ ; ce_clean/sng.
    (* rename s into CE. *)
    rename s' into CE'.
    rename s'' into CE''.
    rename l' into s'.
    rename s''0 into s''.
    inversion h_strg_mtch_s_f_CE_m_ /sng.
    simpl in h_eq_length_f_CE_length_.
    apply eq_add_S in h_eq_length_f_CE_length_.
    simpl in *.
    assert (STACK.cut_until (s' ++ s'') n s' s'') /sng. {
      rewrite <- h_eq_app_s'0_s''0_s_ in *.
      inversion h_stkcut_s_n_ /sng.
      assumption. }
    assert (invariant_compile CE st) /sng.
    { eapply invariant_compile_subcons;eauto. }
    simpl Datatypes.length in h_repeat_loadv_sub_sp_.
    assert (n <= Datatypes.length CE)%nat. {
      simpl in *.
      specialize ci_exact_lvls with (1:=h_inv_comp_f_CE_st_) as ? /sng.
      inversion h_exct_lvlG_lvl_stoCE_CE_ /sng.
      lia. }
    rewrite Nat.sub_succ_l in h_repeat_loadv_sub_sp_;eauto.
    inversion h_repeat_loadv_sub_sp_ /sng.
    rewrite h_eq_loadv_sp_v_ in h_eq_loadv_sp_sp'_.
    invclear h_eq_loadv_sp_sp'_ /sng.
    specialize h_all_and_ with (1:=h_strg_mtch_s0_CE_m_). (2:=h_inv_comp_CE_st_)(3:=h_eq_length_f_CE_length_). (4:=h_stkcut_x_s0_n_)
                                     (5:=h_repeat_loadv_sub_sp'_).
    destruct IHh_CEcut_CE_lvl_ ;auto /sng.
    { simpl in h_eq_app0_.
      inversion h_eq_app0_.
      reflexivity. }
    decomp h_and_.
    assumption.
Qed.

(* Yet another hypothesis deducibility *)
(*Lemma strong_match_env_match_env_sublist_: 
  forall (st : symboltable) (s : STACK.state) (CE : compilenv)
         (sp : Values.val) (locenv : env) (g : genv) (m : mem),
    strong_match_env_ st s CE sp locenv g m
    → invariant_compile CE st
    → ∀ CE' CE'' (lvl : CompilEnv.scope_level),
        CompilEnv.cut_until CE lvl CE' CE''
        → exists δ sp'' s' s'',
          ((∃ toplvl : CompilEnv.scope_level, CompilEnv.level_of_top CE = Some toplvl ∧ δ = (toplvl + 1 - lvl)%nat)
           ∨ CE = [ ] ∧ δ = 0%nat)
          ∧ repeat_Mem_loadv AST.Mint32 m δ sp sp''
          ∧ STACK.cut_until s lvl s' s'' 
          ∧ ∀ locenv0 : env, match_env_ st s'' CE'' sp'' locenv0 g m.
Proof.
  intros /sng.
  assert (exists δ ,
          ((∃ toplvl : CompilEnv.scope_level, CompilEnv.level_of_top CE = Some toplvl ∧ δ = (toplvl + 1 - lvl)%nat)
           ∨ CE = [ ] ∧ δ = 0%nat)) /sng.
  { destruct (CompilEnv.level_of_top CE) eqn:h_eq_lvl_.
    - exists (s0 + 1 - lvl)%nat.
      left.
      exists s0;eauto.
    - exists 0%nat;right;split;eauto.
      apply CompilEnv.exact_lvlG_lgth_none_ in h_eq_lvl_;auto.
      + apply length_invnil_;auto.
      + apply h_inv_comp_CE_st_. }
  destruct h_ex_ as [δ ?] /sng.
  exists δ.
  pose proof strong_match_env_match_env_sublist_aux3_ _ _ _ _ _ _ _ h_strg_mtch_s_CE_m_ h_inv_comp_CE_st_ _ _ _ h_CEcut_CE_lvl_ δ h_or_ /sng.
  destruct h_ex_;eauto.
  exists x.
  edestruct strong_match_env_match_env_sublist_aux2_;eauto /sng.
  destruct h_ex_.
  exists x0 x1;eauto.
Qed.
*)
(* Is this true? *)


(** Property of the translation: Since chain variables have always zero
   offset, the offset of a variable in CE is the same as its offset in
   CMinor memory. *)
Lemma eval_build_loads_offset: forall lvl g stkptr locenv m δ_lvl δ_id b ofs,
    δ_id mod Ptrofs.modulus = δ_id ->
    stack_localstack_aligned lvl locenv g m stkptr ->
    (δ_lvl <= lvl)%nat
    -> Cminor.eval_expr g stkptr locenv m (build_loads δ_lvl δ_id) (Values.Vptr b ofs) ->
    ofs = Ptrofs.repr δ_id.
Proof.
  intros /sng.
  unfold build_loads in *.
  inversion h_CM_eval_expr_ /sng.
  inversion h_CM_eval_expr_v2_ /sng.
  simpl in *.
  red in h_aligned_g_m_.
  specialize h_aligned_g_m_ with (1:=h_le_δ_lvl_lvl_).
  edestruct h_aligned_g_m_;eauto /sng.
  assert (v1 = Values.Vptr x Ptrofs.zero).
  { eapply det_eval_expr;eauto. }
  subst.
  cbn  in *.
  destruct v2;destruct Archi.ptr64;cbn in *;try discriminate.
  inversion h_eval_binop_Oadd_v1_v2_.
  inversion h_eval_constant_.
  subst.
  rewrite Ptrofs.add_zero_l.
  unfold Ptrofs.of_int.
  apply f_equal.
  rewrite Int.unsigned_repr_eq.
  auto.              
Qed.


(** Property of the translation: Since chain variables have always
    zero offset, the offset of a variable in CE must be more than 3. *)
Lemma eval_build_loads_offset_non_null_var:
  forall stbl CE g stkptr locenv m nme a bld_lds b ofs,
    CompilEnv.exact_levelG CE ->
    all_addr_no_overflow CE ->
    stack_no_null_offset CE ->
    stack_localstack_aligned (Datatypes.length CE) locenv g m stkptr ->
    transl_variable stbl CE a nme = Errors.OK bld_lds ->
    Cminor.eval_expr g stkptr locenv m bld_lds (Values.Vptr b ofs) ->
    4 <= Ptrofs.unsigned ofs.
Proof.
  intros /sng.
  functional inversion h_eq_transl_var_;subst /sng.
  assert (ofs=(Ptrofs.repr δ_nme)) /sng. {
    assert (δ_nme mod Ptrofs.modulus = δ_nme) /sng.
    { red in h_no_overf_CE_.
      specialize h_no_overf_CE_ with (1:=h_eq_CEfetchG_nme_CE_).
      apply Z.mod_small.
      assumption. }
    eapply (eval_build_loads_offset (Datatypes.length CE) g stkptr locenv m (m' - lvl_nme) _ b ofs  h_eq_modulo_ h_aligned_g_m_);auto with arith.
    - erewrite <- CompilEnv.exact_lvl_lvl_of_top with (n:=m').
      + lia.
      + assumption.
      + assumption. }
  subst.
  red in h_nonul_ofs_CE_.
  red in h_nonul_ofs_CE_.
  specialize h_nonul_ofs_CE_ with (1:=h_eq_CEfetchG_nme_CE_).
  red in h_no_overf_CE_.
  specialize h_no_overf_CE_ with (1:=h_eq_CEfetchG_nme_CE_).
  rewrite Ptrofs.unsigned_repr;auto.
  split;try lia.
  unfold Ptrofs.max_unsigned.
  lia.
Qed.

Lemma transl_expr_ok : forall stbl CE e e',
    transl_expr stbl CE e = Errors.OK e' ->
    forall locenv g m (s:STACK.state)  (v:value) stkptr,
      evalExp stbl s e (OK v) ->
      match_env_ stbl s CE stkptr locenv g m ->
      exists v_t,
        (transl_value v v_t /\ Cminor.eval_expr g stkptr locenv m e' v_t).
Proof.
  intros until e.
  functional induction (transl_expr stbl CE e) ;try discriminate;simpl; intros;
  invclear h_eval_expr_v_;eq_same_clear /sng.
  - inversion h_eval_literal_;subst.
    + destruct v0 /sng.
      * eexists;split;intros; econstructor;eauto /sng.
      * eexists;split;intros;econstructor;eauto /sng.
    + eexists;split;intros /sng.
      * eapply (transl_literal_ok g _ _ h_eval_literal_ stkptr).
        econstructor.
      * constructor.
        reflexivity.
  - unfold value_at_addr in heq_value_at_addr_.
    destruct (transl_type stbl astnum_type) eqn:heq_transl_type_;simpl in *.
    + destruct h_match_env_ /sng.
      edestruct h_safe_cm_CE_m_.(me_stack_match_addresses) with (nme:=Identifier astnum id);eauto. 
      eapply h_stk_mtch_s_m_;eauto.
      * simpl.
        assumption.
      * simpl.
        rewrite heq_fetch_exp_type_.
        reflexivity.
    + discriminate.
  - decomp (h_forall_e'_ _ heq_tr_expr_e_ _ _ _ _ _ _ h_eval_expr_e_e_v_ h_match_env_).
    decomp (h_forall_e'0_ _ heq_tr_expr_e0_ _ _ _ _ _ _ h_eval_expr_e0_e0_v_ h_match_env_).
    assert (hex:or (exists b, v = Bool b) (exists n, v = Int n)). {
      apply do_run_time_check_on_binop_ok in h_do_rtc_binop_.
      rewrite binopexp_ok in h_do_rtc_binop_.
      functional inversion h_do_rtc_binop_;subst;eq_same_clear
       ;try contradiction;eauto /sng.
      unfold Math.mod' in  heq_mod'_.
      destruct e_v;try discriminate.
      destruct e0_v;try discriminate.
      inversion heq_mod'_.
      right;eauto. }
    decomp hex;subst.
    + destruct b; eexists;(split;[econstructor;eauto|]).
      * eapply eval_Ebinop;try econstructor;eauto.
        eapply binary_operator_ok with (v1:=e_v) (v2:=e0_v);eauto with spark.
        econstructor;eauto.
      * eapply eval_Ebinop;try econstructor;eauto.
        eapply binary_operator_ok with (v1:=e_v) (v2:=e0_v);eauto with spark.
        econstructor;eauto.
    + eexists;(split;[econstructor;eauto|]).
      eapply eval_Ebinop;try econstructor;eauto.
        eapply binary_operator_ok with (v1:=e_v) (v2:=e0_v);eauto with spark.
        econstructor;eauto.
  - (* Unary minus *)
    simpl in heq_transl_unop_.
    eq_same_clear.
    specialize h_forall_e'_ with (1:=heq_tr_expr_e_) (2:=h_eval_expr_e_e_v_) (3:=h_match_env_).
    decomp h_forall_e'_.
    invclear h_do_rtc_unop_;eq_same_clear /sng.
    invclear h_overf_check_ /sng.
    eexists.
    split.
    * econstructor.
    * assert (h:=unaryneg_ok _ _ _ h_transl_value_e_v_e_t_v_ heq_unary_minus_).
      econstructor;eauto.
      simpl.
      inversion h.
      reflexivity.
  (* Not *)
  - invclear h_do_rtc_unop_;simpl in *;try eq_same_clear /sng.
    specialize h_forall_e'_ with (1:=heq_tr_expr_e_) (2:=h_eval_expr_e_e_v_) (3:=h_match_env_).
    decomp h_forall_e'_.
    generalize (not_ok _ _ _ h_transl_value_e_v_e_t_v_ heq_unary_operation_).
    intro /sng.
    exists (Values.Val.notbool e_t_v).
    split;auto.
    econstructor;simpl in *;eauto.
    + econstructor;eauto.
      reflexivity.
    + destruct e_t_v;simpl in *; try (inversion h_transl_value_e_v_e_t_v_;fail).
      unfold  Values.Val.cmp.
      simpl.
      unfold Values.Val.of_bool.
      reflexivity.
Qed.

Declare Scope res_scope.
Notation " x =: y" := (x = Errors.OK y) (at level 90): res_scope.
Notation " x = y" := (x = Error y) (at level 120): res_scope /sng.
Open Scope res_scope.

Lemma transl_name_ok : forall stbl CE nme nme' typ_nme cm_typ_nme load_addr_nme,
    transl_name stbl CE nme = Errors.OK nme' ->
    type_of_name stbl nme =: typ_nme ->
    transl_type stbl typ_nme =: cm_typ_nme ->
    make_load nme' cm_typ_nme =: load_addr_nme ->
    
    forall locenv g m (s:STACK.state)  (v:value) stkptr,
      evalName stbl s nme (OK v) ->
      match_env_ stbl s CE stkptr locenv g m ->
      exists v_t ,
        (transl_value v v_t
         /\ Cminor.eval_expr g stkptr locenv m load_addr_nme v_t).
Proof.
  intros /sng.
  assert (forall n, evalExp stbl s (Name n nme) (OK v)). {
    intros /sng. 
    constructor.
    assumption. }
  
  specialize (h_match_env_ /sng.(me_safe_cm_env).(me_stack_match_addresses)) as ?.
  red in h_stk_mtch_addr_stkptr_m_.
  specialize h_stk_mtch_addr_stkptr_m_ with (1:=heq_transl_name_).
  decomp h_stk_mtch_addr_stkptr_m_.
  
  specialize (h_match_env_ /sng.(me_stack_match)) as ?.
  red in h_stk_mtch_s_m_.
  specialize h_stk_mtch_s_m_ with (1:=heq_transl_name_) (2:=h_CM_eval_expr_nme_t_nme_t_v_)
                                 (3:=h_eval_name_nme_v_)(4:=heq_transl_type_) (5:=heq_type_of_name_)
                                 (6:=heq_make_load_).
  decomp h_stk_mtch_s_m_.
  eexists.
    split;eauto.
Qed.

Scheme Equality for binary_operator.
Scheme Equality for unary_operator.
Scheme Equality for literal.

Ltac finish_eqdec_ := try subst;try (left;reflexivity);(try now right;intro abs;inversion abs;contradiction).

Lemma expression_dec: forall e1 e2:exp, ({e1=e2} + {e1<>e2})
with name_dec: forall n1 n2:name, ({n1=n2} + {n1<>n2}).
Proof.
  { intros e1 e2.
    case e1;case e2;intros;try now((left+right)).
    - destruct (Nat.eq_dec a0 a);finish_eqdec_.
      destruct (literal_eq_dec l0 l);finish_eqdec_.
    - destruct (Nat.eq_dec a0 a);finish_eqdec_.
      destruct (name_dec n0 n);finish_eqdec_.
    - destruct (Nat.eq_dec a0 a);finish_eqdec_.
      destruct (binary_operator_eq_dec b0 b);finish_eqdec_.
      destruct (expression_dec e3 e);finish_eqdec_.
      destruct (expression_dec e4 e0);finish_eqdec_.
    - destruct (Nat.eq_dec a0 a);finish_eqdec_.
      destruct (unary_operator_eq_dec u0 u);finish_eqdec_.
      destruct (expression_dec e0 e);finish_eqdec_. }
  { intros /sng.
    case n1;case n2;intros;finish_eqdec_.
    - destruct (Nat.eq_dec a0 a);finish_eqdec_.
      destruct (Nat.eq_dec i0 i);finish_eqdec_.
    - destruct (Nat.eq_dec a0 a);finish_eqdec_.
      destruct (name_dec n0 n);finish_eqdec_.
      destruct (expression_dec e0 e);finish_eqdec_.
    - destruct (Nat.eq_dec a0 a);finish_eqdec_.
      destruct (name_dec n0 n);finish_eqdec_.
      destruct (Nat.eq_dec i0 i);finish_eqdec_. }
Defined.


Import STACK.


Lemma CEfetch_reside_true_ : forall id a x,
    CompilEnv.fetch id a = Some x -> CompilEnv.reside id a = true.
Proof.
  intros until a.
  unfold CompilEnv.fetch, CompilEnv.reside.
  induction (CompilEnv.store_of a);simpl;intros;try discriminate /sng.
  destruct a0.
  destruct (beq_nat id i).
  - reflexivity.
  - eapply IHs;eauto.
Qed.

Lemma CEfetch_reside_false_ : forall id a,
    CompilEnv.fetch id a = None -> CompilEnv.reside id a = false.
Proof.
  intros until a.
  unfold CompilEnv.fetch, CompilEnv.reside.
  induction (CompilEnv.store_of a);simpl;intros;try reflexivity /sng.
  destruct a0.
  destruct (beq_nat id i).
  - discriminate.
  - eapply IHs;eauto.
Qed.



Lemma frameG_In : forall a id st,
    CompilEnv.frameG id a = Some st ->
    List.In st a.
Proof.
  intro a.
  induction a;simpl;intros;try discriminate /sng.
  destruct (CompilEnv.reside id a) /sng.
  - inversion heq_Some_.
    left.
    reflexivity.
  - right.
    eapply h_forall_id_;eauto.
Qed.

Lemma fetches_In : forall a id st,
    CompilEnv.fetches id a = Some st ->
    List.In (id,st) a.
Proof.
  intro a.
  induction a;simpl;intros;try discriminate /sng.
  destruct a;simpl in * /sng.
  destruct (eq_nat_dec id i);subst;simpl in * /sng.
  - rewrite <- beq_nat_refl in heq_Some_.
    inversion heq_Some_.
    left.
    reflexivity.
  - right.
    rewrite <- beq_nat_false_iff in hneq_id.
    rewrite hneq_id in heq_Some_.
    eapply h_forall_id_;eauto.
Qed.


Lemma fetches_none_notin: ∀ (a : localframe) (id : idnum) (st : CompilEnv.V), CompilEnv.fetches id a = None → ~List.In (id, st) a.
Proof.
  intros /sng.
  (functional induction (CompilEnv.fetches id a);intros; try discriminate) /sng.
  - specialize (h_impl_neg_lst_in_ heq_CEfetches_id_a_).
    intro abs.
    simpl in *.
    destruct abs /sng.
    + inversion heq_pair_;subst.
      rewrite <- beq_nat_refl in hbeqnat_false.
      discriminate.
    + contradiction.
  - apply in_nil.
Qed.

Arguments fst _ _ p /sng.

Lemma fetches_none_notinA: ∀ (a : localframe) (id : idnum) (st : CompilEnv.V),
    CompilEnv.fetches id a = None →
    ~InA eq_fst_idnum (id, st) a.
Proof.
  intros * /sng.
  (functional induction (CompilEnv.fetches id a);intros; try discriminate) /sng.
  - specialize (h_impl_neg_inA_ heq_CEfetches_id_s'_).
    intro abs.
    inversion abs /sng.
    + red in h_eqfst_idnum_;simpl in h_eqfst_idnum_.
      subst.
      rewrite <- beq_nat_refl in hbeqnat_false.
      discriminate.
    + contradiction.
  - rewrite InA_nil.
    red;trivial.
Qed.

Lemma In_fetches_NoDup: forall l id st,
    NoDupA (fun x y => fst x = fst y) l ->
    List.In (id,st) l ->
    CompilEnv.fetches id l = Some st.
Proof.
  intro l.
  induction l;simpl;intros;try contradiction /sng.
  destruct h_or_;subst /sng.
  - rewrite <- beq_nat_refl.
    reflexivity.
  - destruct a.
    assert (hneq:i<>id).
    { intro abs.
      subst.
      inversion h_NoDupA_;subst.
      absurd (InA eq_fst_idnum (id, t) l);auto.
      apply InA_alt.
      exists (id, st).
      split;auto with spark. }
    apply not_eq_sym in hneq.
    rewrite <- beq_nat_false_iff in hneq.
    rewrite hneq.
    apply h_forall_id_;auto.
    inversion h_NoDupA_;auto.
Qed.


Lemma add_to_frame_nodup: forall stbl subtyp_mrk new_sz nme fram_sz new_fram,
    CompilEnv.fetches nme (fst fram_sz) = None
    -> add_to_frame stbl fram_sz nme subtyp_mrk = Errors.OK (new_fram, new_sz)
    -> NoDupA eq_fst_idnum (fst fram_sz)
    -> NoDupA eq_fst_idnum new_fram.
Proof.
  intros * /sng.
  rew add_to_frame_ok with (idtac;functional induction (function_utils.add_to_frame stbl fram_sz nme subtyp_mrk);simpl;intros;
    try discriminate) /sng.
  invclear heq_OK_ /sng.
  constructor 2.
  - eapply fetches_none_notinA with (st:=sz) in heq_CEfetches_nme_cenv_ .
    assumption.
  - assumption.
Qed.



Ltac rename_hyp_incro n th :=
  match th with
  | exact_levelG ?x => fresh "exact_lvlG_" x
  | exact_levelG _ => fresh "exact_lvlG"
  | _ => rename_stack_push_all_new_ n th
  end.
Ltac rename_sparkprf ::= rename_hyp_incro.

Lemma storev_inv : forall nme_chk m nme_t_addr e_t_v m',
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m'
    -> exists b ofs, nme_t_addr = Values.Vptr b ofs.
Proof.
  intros /sng.
  destruct nme_t_addr; try discriminate.
  eauto.
Qed.

Lemma transl_name_OK_inv : forall stbl CE nme nme_t,
    transl_name stbl CE nme = Errors.OK nme_t
    -> exists astnum id, (transl_variable stbl CE astnum id =  Errors.OK nme_t
                          /\ nme = Identifier astnum id).
Proof.
  intros /sng.
  functional inversion heq_transl_name_.
  eauto.
Qed.

Lemma exact_level_top_lvl: forall CE s3,
    CompilEnv.exact_levelG CE ->
    CompilEnv.level_of_top CE = Some s3 ->
    List.length CE = S s3.
Proof.
  intros /sng.
  inversion h_exct_lvlG_CE_;subst;cbn in *;try discriminate.
  inversion heq_lvloftop_CE_s3_.
  reflexivity.
Qed.


Lemma increase_order_level_of_top_ge: forall CE id s s0 s3,
    CompilEnv.exact_levelG CE ->
    CompilEnv.frameG id CE = Some (s, s0) ->
    CompilEnv.level_of_top CE = Some s3 ->
    (s3 >= s)%nat.
Proof.
  intros until 1 /sng.
  revert id s s0 s3.
  induction h_exct_lvlG_CE_;cbn /sng.
  - discriminate.
  - intros /sng.
    destruct (CompilEnv.resides id fr) eqn:heq_resides_.
    + invclear heq_Some_ /sng.
      invclear heq_Some0_ /sng.
      auto.
    + invclear heq_Some0_ /sng.
      destruct (CompilEnv.level_of_top stk) eqn:heq_lvltop_.
      * specialize(h_forall_id_ id s s0 s1).
        specialize (exact_level_top_lvl _ _ h_exct_lvlG_CE_ heq_lvltop_).
        intro /sng.
        red.
        apply Nat.le_trans with s1.
        -- apply h_forall_id_;auto.
        -- lia.
      * destruct stk.
        -- cbn in heq_Some_.
           discriminate.
        -- cbn in heq_lvltop_.
           destruct f.
           discriminate.
Qed.

Lemma CEfetches_inj : forall id₁ id₂ (lf:localframe) δ₁ δ₂,
    increasing_order lf ->
    CompilEnv.fetches id₁ lf = Some δ₁ ->
    CompilEnv.fetches id₂ lf = Some δ₂ ->
    id₁ ≠ id₂ ->
    δ₁ ≠ δ₂.
Proof.
  intros until lf.
  induction lf;simpl in *;intros /sng.
  - discriminate.
  - destruct a.
    destruct (Nat.eq_dec id₁ i);subst.
    + rewrite Nat.eqb_refl in heq_Some_.
      invclear heq_Some_ /sng.
      assert (h:id₂ ≠ i) by auto.
      rewrite <- (Nat.eqb_neq id₂ i) in h.
      rewrite h in heq_Some0_.
      inversion h_incr_order_;subst;simpl in * /sng.
      assert (δ₂ < δ₁). {
        rewrite Forall_forall in h_lst_forall_lf_.
        eapply (h_lst_forall_lf_ (id₂,δ₂));eauto.
        apply fetches_In.
        assumption. }
      symmetry.
      apply Z.lt_neq.
      assumption.
    + destruct (Nat.eq_dec id₂ i).
      * subst.
        rewrite Nat.eqb_refl in heq_Some0_.
        invclear heq_Some0_ /sng.
        assert (h:id₁ ≠ i) by auto.
        rewrite <- (Nat.eqb_neq id₁ i) in h.
        rewrite h in heq_Some_.
        inversion h_incr_order_;subst;simpl in * /sng.
        assert (δ₁ < δ₂). {
          rewrite Forall_forall in h_lst_forall_lf_.
          eapply (h_lst_forall_lf_ (id₁,δ₁));eauto.
          apply fetches_In.
          assumption. }
        apply Z.lt_neq.
        assumption.
      * rewrite <- (Nat.eqb_neq id₁ i) in n.
        rewrite <- (Nat.eqb_neq id₂ i) in n0.
        rewrite n,n0 in *.
        apply h_forall_δ_₁;auto.
        inversion h_incr_order_.
        assumption.
Qed.


Lemma CEfetch_inj_ : forall id₁ id₂ (a:CompilEnv.frame) δ₁ δ₂,
    increasing_order_fr a ->
    CompilEnv.fetch id₁ a = Some δ₁ ->
    CompilEnv.fetch id₂ a = Some δ₂ ->
    id₁ ≠ id₂ ->
    δ₁ ≠ δ₂.
Proof.
  intros until a.
  unfold CompilEnv.fetch.
  destruct a;simpl /sng.
  unfold increasing_order_fr.
  simpl.
  apply CEfetches_inj.
Qed.

Lemma increasing_order_frameG: forall lvla lvlb fra l id ,
    Forall (gt_x_fst_y lvlb) l ->
    CompilEnv.frameG id l = Some (lvla,fra) ->
    (lvla < lvlb)%nat.
Proof.
  intros /sng.
  apply frameG_In in heq_CEframeG_id_l_.
  rewrite Forall_forall in h_lst_forall_l_.
  apply (h_lst_forall_l_ (lvl_id, fr_id)).
  assumption.
Qed.


Lemma exact_levelG_lgth: forall stk id lvl_id fr_id,
    CompilEnv.exact_levelG stk
    -> CompilEnv.frameG id stk = Some (lvl_id, fr_id)
    -> (lvl_id < Datatypes.length stk)%nat.
Proof.
  red.
  induction 1 /sng.
  - cbn. intro abs;discriminate.
  - cbn. intro /sng.
    rename h_impl_le_ into IH.
    destruct (CompilEnv.resides id fr) /sng.
    + invclear heq_Some_ /sng.
      auto.
    + specialize (IH heq_Some_).
      lia.
Qed.

Lemma CEfetchG_inj : forall CE id₁ id₂,
    CompilEnv.exact_levelG CE ->
    all_frm_increasing CE ->
    forall  δ₁ δ₂ k₁ k₂ frm₁ frm₂,
      CompilEnv.fetchG id₁ CE = Some δ₁ ->
      CompilEnv.fetchG id₂ CE = Some δ₂ ->
      CompilEnv.frameG id₁ CE = Some (k₁, frm₁) ->
      CompilEnv.frameG id₂ CE = Some (k₂, frm₂) ->
      id₁ ≠ id₂ ->
      (k₁ <> k₂ \/ δ₁ <> δ₂).
Proof.
  intros *.
  intro /sng.
  induction h_exct_lvlG_CE_;intros;simpl in *;try discriminate /sng.
  unfold CompilEnv.level_of in *.
  destruct (CompilEnv.fetch id₁ (Datatypes.length stk, fr)) eqn:heq_fetch_id_₁;
    destruct (CompilEnv.fetch id₂ (Datatypes.length stk, fr)) eqn:heq_fetch_id_₂;
    eq_same_clear;subst;simpl in *;try discriminate.
  - right.
    eapply CEfetch_inj_;eauto.
    red in h_allincr_; simpl in h_allincr_.
    inversion h_allincr_.
    assumption.
  - left.
    symmetry.
    apply Nat.lt_neq.
    apply CEfetch_reside_false_ in heq_fetch_id_₂.
    apply CEfetch_reside_true_ in heq_fetch_id_₁.
    rewrite heq_fetch_id_₂,heq_fetch_id_₁ in *;simpl in *.
    invclear heq_CEframeG_id_₁;simpl in * /sng.
    eapply exact_levelG_lgth;eauto.
  - left.
    apply Nat.lt_neq.
    apply CEfetch_reside_true_ in heq_fetch_id_₂.
    apply CEfetch_reside_false_ in heq_fetch_id_₁.
    rewrite heq_fetch_id_₂,heq_fetch_id_₁ in *;simpl in *.
    invclear heq_CEframeG_id_₂;simpl in * /sng.
    eapply exact_levelG_lgth;eauto.
  - apply CEfetch_reside_false_ in heq_fetch_id_₁.
    apply CEfetch_reside_false_ in heq_fetch_id_₂.
    rewrite heq_fetch_id_₁,heq_fetch_id_₂ in *.
    eapply IHh_exct_lvlG_CE_ ;eauto.
    inversion h_allincr_.
    assumption.
Qed.

Lemma minus_same_eq : forall s3 s s1,
    s ≤ s3 ->
    s1 ≤ s3 ->
    (s3 - s1)%nat = (s3 - s)%nat ->
    s = s1.
Proof.
  induction s3;intros /sng.
  - inversion h_le_s_O_;inversion h_le_s1_O_;auto /sng.
  - inversion h_le_s_;inversion h_le_s1_;subst /sng.
    + reflexivity.
    + rewrite minus_diag in heq_sub_.
      apply Nat.sub_0_le in heq_sub_.
      assert (s3 < s3)%nat /sng. {
        eapply lt_le_trans with s1;auto. }
      destruct (lt_irrefl s3);auto.
    + rewrite minus_diag in heq_sub_.
      symmetry in heq_sub_.
      apply Nat.sub_0_le in heq_sub_.
      assert (s3 < s3)%nat. {
        eapply lt_le_trans with s;auto. }
      destruct (lt_irrefl s3);auto.
    + eapply h_forall_s_;eauto.
      setoid_rewrite <- minus_Sn_m in heq_sub_;auto.
Qed.

Lemma minus_same_neq : forall s3 s s1,
    s ≤ s3 ->
    s1 ≤ s3 ->
    s <> s1 ->
    (s3 - s1)%nat <> (s3 - s)%nat.
Proof.
  intros /sng.
  intro abs.
  apply minus_same_eq in abs;auto.
Qed.



Lemma transl_variable_inj : forall CE stbl a₁ a₂ id₁ id₂ k₁ k₂ δ₁ δ₂,
    (* Frame are numbered with different (increasing) numers *)
    CompilEnv.exact_levelG CE ->
    (* In each frame, stacks are also numbered with (increasing) numbers *)
    all_frm_increasing CE ->
    all_addr_no_overflow CE ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a₁ id₁ = Errors.OK (build_loads k₁ δ₁) ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a₂ id₂ = Errors.OK (build_loads k₂ δ₂) ->
    id₁ <> id₂ ->
    (k₁ <> k₂ \/ δ₁<> δ₂).
Proof.
  intros /sng.
  unfold transl_variable in *.
  destruct (CompilEnv.fetchG id₁ CE) eqn:h₁;simpl in *;try discriminate.
  destruct (CompilEnv.fetchG id₂ CE) eqn:h₂;simpl in *;try discriminate.
  destruct (CompilEnv.frameG id₁ CE) eqn:h₁';simpl in *;try discriminate.
  destruct (CompilEnv.frameG id₂ CE) eqn:h₂';simpl in *;try discriminate.
  destruct f.
  destruct f0.
  assert (hh:=CEfetchG_inj _ _ _ h_exct_lvlG_CE_ h_allincr_CE_ _ _ _ _ _ _  h₁ h₂ h₁' h₂' hneq_id₁).
   destruct (CompilEnv.level_of_top CE) eqn:hlvlofCE.
  - (* remember here refrain inversion to bizarrely unfold too much. *)
    remember (build_loads (s3 - s1) t0) as fooo.
    remember (build_loads (s3 - s) t) as fooo'.
    inversion h_eq_transl_var_ as [heqfoo].
    inversion heq_transl_variable0_ as [heqfoo'].
    clear h_eq_transl_var_ heq_transl_variable0_.
    subst.
    apply build_loads_inj in heqfoo.
    apply build_loads_inj in heqfoo'.
    destruct heqfoo /sng.
    destruct heqfoo' /sng.
    subst.
    destruct hh /sng.
    + left.
      eapply minus_same_neq;eauto.
      eapply increase_order_level_of_top_ge;eauto.
      eapply increase_order_level_of_top_ge;eauto.
    + repeat rewrite Integers.Int.Z_mod_modulus_eq in *.
      rewrite Zmod_small in *;eauto.
      subst.
      right.
      intro abs.
      subst.
      apply hneq_t ;reflexivity.
  - discriminate.
Qed.

Lemma transl_variable_inj2 : forall CE stbl a₁ a₂ id₁ id₂ x,
    (* Frame are numbered with different (increasing) numers *)
    CompilEnv.exact_levelG CE ->
    (* In each frame, stacks are also numbered with (increasing) numbers *)
    all_frm_increasing CE ->
    all_addr_no_overflow CE ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a₁ id₁ = Errors.OK x ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a₂ id₂ = Errors.OK x ->
    id₁ = id₂.
Proof.
  intros /sng.
  destruct (Nat.eq_dec id₁ id₂).
  { assumption. }
  exfalso.
  functional inversion h_eq_transl_var_ /sng.
  rewrite <- heq_build_loads_ in h_eq_transl_var_.
  functional inversion heq_transl_variable0_ /sng.
  rewrite <- heq_build_loads0_ in heq_transl_variable0_.
  specialize transl_variable_inj with (1:=h_exct_lvlG_CE_)(2:=h_allincr_CE_)
                                      (3:=h_no_overf_CE_)(4:=h_eq_transl_var_)
                                      (5:=heq_transl_variable0_).
  assert (m' = m'0).
  { rewrite heq_lvloftop_CE_m'_ in heq_lvloftop_CE_m'0_.
    injection heq_lvloftop_CE_m'0_;auto. } 
  subst m'0.
  clear heq_lvloftop_CE_m'0_.
  up_type.
  subst x.
  specialize build_loads_inj with (1:=heq_build_loads0_);intros ? h_inj_ /sng.
  decomp h_and_.
  assert (lvl_id₁ = lvl_id₂).
  { assert (lvl_id₁ <= m')%nat /sng.
    { eapply increase_order_level_of_top_ge;eauto. }
    assert (lvl_id₂ <= m')%nat /sng.
    { eapply increase_order_level_of_top_ge;eauto. }
    eapply minus_same_eq;eauto. }
  subst lvl_id₂.
  assert (δ_id₁ = δ_id₂).
  { red in h_no_overf_CE_.
    specialize h_no_overf_CE_ with (1:=heq_CEfetchG_id_₁_CE) as h.
    specialize h_no_overf_CE_ with (1:=heq_CEfetchG_id_₂_CE) as h'.
    decomp h.
    decomp h'.
    repeat rewrite Int.Z_mod_modulus_eq in *.
    rewrite Zmod_small in heq_Z_mod_modulus_.
    rewrite Zmod_small in heq_Z_mod_modulus_.
    - auto.
    - split; auto.
    - split; auto. } 
  specialize (h_impl_or_ n).
  destruct h_impl_or_ /sng.
  + symmetry in heq_sub_. contradiction.
  + contradiction.
Qed.


Lemma transl_variable_astnum: forall stbl CE astnum id' addrof_nme,
    transl_variable stbl CE astnum id' = Errors.OK addrof_nme
    -> forall a,transl_variable stbl CE a id' = transl_variable stbl CE astnum id'.
Proof.
  intros /sng.
  unfold transl_variable.
  functional inversion h_eq_transl_var_ /sng.
  rewrite  heq_CEfetchG_id'_CE_, heq_CEframeG_id'_CE_, heq_lvloftop_CE_m'_.
  reflexivity.
Qed.



Lemma compute_chk_32 : forall stbl t,
    compute_chnk_of_type stbl t = Errors.OK AST.Mint32
    -> transl_type stbl t = Errors.OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr).
Proof.
  intros /sng.
  functional inversion heq_compute_chnk_of_type_;subst;simpl /sng.
  - functional inversion heq_reduce_type_;simpl /sng.
    reflexivity.
  - functional inversion heq_reduce_type_;simpl /sng.
    reflexivity.
Qed.



Ltac simplify_do :=
  repeat progress
         (match goal with
          | H: context [do _ <- ?e ; _] , H': ?e = _ |- _ =>
            rewrite H' in H;simpl in H
          | H': ?e = _ |- context [do _ <- ?e ; _]  =>
            rewrite H';simpl
          end).


(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load'2:forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> stack_localstack_aligned lvl locenv g m stkptr
    -> 4 <= Ptrofs.unsigned ofs (*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl',
        (lvl' <= lvl)%nat ->
        let load_id := build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl' in
        Cminor.eval_expr g stkptr locenv m' load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
Proof.
  intros /sng.
  rename h_le_ into h_ofs_non_zero_.
  simpl in *.
  subst load_id.
  generalize dependent load_id_v.
  induction lvl';intros;simpl in * /sng.
  - inversion h_CM_eval_expr_load_id_v_;econstructor;eauto /sng.
  - invclear h_CM_eval_expr_load_id_v_ /sng.
    assert (h_CM_eval_expr_on_m_:
              Cminor.eval_expr g stkptr locenv m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl') vaddr).
    { eapply IHlvl'; eauto.
      lia. }
    econstructor.
    + eassumption.
    + destruct vaddr;simpl in *;try discriminate.
      rewrite <- h_loadv_vaddr_load_id_v_.
      symmetry.
      eapply Mem.load_store_other;eauto.
      right.
      left.
      simpl.
      transitivity 4.
      * assert (lvl' <= lvl)%nat /sng.
        { lia. }
        specialize (h_aligned_g_m_ _ h_le_lvl'_lvl0_).
        destruct h_aligned_g_m_ /sng.
        assert ((Values.Vptr b0 i) = (Values.Vptr x Ptrofs.zero)) /sng.
        { eapply det_eval_expr;eauto. }
        invclear heq_vptr_b0_i_ /sng.
        discriminate.
      * apply h_ofs_non_zero_.
Qed.

(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load'3:forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> stack_localstack_aligned lvl locenv g m' stkptr
    -> (4 <= (Ptrofs.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl',
        (lvl' <= lvl)%nat ->
        let load_id := build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl' in
        Cminor.eval_expr g stkptr locenv m load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
Proof.
  intros /sng.
  rename h_le_ into h_ofs_non_zero_.
  simpl in *.
  subst load_id.
  generalize dependent load_id_v.
  induction lvl';intros;simpl in * /sng.
  - inversion h_CM_eval_expr_load_id_v_;econstructor;eauto /sng.
  - invclear h_CM_eval_expr_load_id_v_ /sng.
    assert (h_CM_eval_expr_on_m'_:
              Cminor.eval_expr g stkptr locenv m' (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl') vaddr).
    { eapply IHlvl'; eauto. lia. }
    econstructor.
    + eassumption.
    + destruct vaddr;simpl in *;try discriminate.
      rewrite <- h_loadv_vaddr_load_id_v_.
      eapply Mem.load_store_other;eauto.
      simpl.
      right. left.
      transitivity 4.
      * assert (lvl' <= lvl)%nat /sng.
        { lia. }
        destruct (h_aligned_g_m'_ _ h_le_lvl'_lvl0_) /sng.
        assert ((Values.Vptr b0 i) = (Values.Vptr x Ptrofs.zero)) /sng.
        { eapply det_eval_expr;eauto. }
        invclear heq_vptr_b0_i_ /sng.
        vm_compute.
        intro abs;discriminate.
      * apply h_ofs_non_zero_.
Qed.

(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load'4:forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> stack_localstack_aligned lvl locenv g m stkptr
    -> 4 <= Ptrofs.unsigned ofs (*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl',
        (lvl' <= lvl)%nat ->
        let load_id := build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl' in
        Cminor.eval_expr g stkptr locenv m load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
Proof.
  intros /sng.
  rename h_le_ into h_ofs_non_zero_.
  simpl in *.
  subst load_id.
  generalize dependent load_id_v.
  induction lvl';intros;simpl in * /sng.
  - inversion h_CM_eval_expr_load_id_v_;econstructor;eauto /sng.
  - invclear h_CM_eval_expr_load_id_v_ /sng.
    assert (h_CM_eval_expr_on_m_:
              Cminor.eval_expr g stkptr locenv m' (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl') vaddr).
    { eapply IHlvl'; eauto.
      lia. }
    econstructor.
    + eassumption.
    + destruct vaddr;simpl in *;try discriminate.
      rewrite <- h_loadv_vaddr_load_id_v_.
      eapply Mem.load_store_other;eauto.
      assert ((lvl' <= lvl)%nat) by lia /sng.
      pose proof h_aligned_g_m_ lvl' h_le_lvl'_lvl0_ /sng.
      decomp h_ex_.
      assert ((Values.Vptr b0 i) = (Values.Vptr b_δ Ptrofs.zero)) /sng.
      { eapply det_eval_expr;eauto. }
      invclear heq_vptr_b0_i_ /sng.
      right.
      left.
      rewrite Ptrofs.unsigned_zero.
      cbn.
      lia.
Qed.

Lemma wf_chain_load'':forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned lvl locenv g m stkptr)
    -> (stack_localstack_aligned lvl locenv g m' stkptr)
    -> (4 <= (Ptrofs.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl',
        (lvl' <= lvl)%nat ->
        let load_id := build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl' in
        Cminor.eval_expr g stkptr locenv m' load_id vaddr
        <-> Cminor.eval_expr g stkptr locenv m load_id vaddr.
Proof.
  intros /sng.
  split;intro .
  - eapply wf_chain_load'2 ;eauto.
  - eapply wf_chain_load'3 ;eauto.
Qed.

(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load':forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned lvl locenv g m' stkptr)
    -> (4 <= (Ptrofs.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl' δ_lvl,
        (lvl' <= lvl)%nat ->
        let load_id := build_loads lvl' δ_lvl in
        Cminor.eval_expr g stkptr locenv m load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
Proof.
  intros /sng.
  rename h_le_ into h_ofs_non_zero_.
  simpl in *.
  unfold build_loads in *.
  invclear h_CM_eval_expr_load_id_load_id_v_ /sng.
  econstructor;eauto.
  - eapply wf_chain_load'3;eauto.
  - inversion h_CM_eval_expr_v2_;econstructor;eauto.
Qed.


(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load'_2:forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned lvl locenv g m stkptr)
    -> (4 <= (Ptrofs.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl' δ_lvl,
        (lvl' <= lvl)%nat ->
        let load_id := build_loads lvl' δ_lvl in
        Cminor.eval_expr g stkptr locenv m' load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
Proof.
  intros /sng.
  rename h_le_ into h_ofs_non_zero_.
  simpl in *.
  unfold build_loads in *.
  invclear h_CM_eval_expr_load_id_load_id_v_ /sng.
  econstructor;eauto.
  - eapply wf_chain_load'2;eauto.
  - inversion h_CM_eval_expr_v2_;econstructor;eauto.
Qed.

(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load_var:
  forall stbl CE g locenv stkptr astnum chk m m' b ofs e_t_v id load_id vaddr,
    CompilEnv.exact_levelG CE ->
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned (Datatypes.length CE) locenv g m' stkptr)
    -> (4 <= (Ptrofs.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> transl_variable stbl CE astnum id =: load_id
    -> Cminor.eval_expr g stkptr locenv m load_id vaddr
    -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
Proof.
  intros /sng.
  rename h_le_ into h_ofs_non_zero_.
  simpl in *.
  functional inversion h_eq_transl_var_;subst;clear h_eq_transl_var_ /sng.
  rename m'0 into max_lvl.
  set (δ_lvl:=(max_lvl - lvl_id)%nat) in *.
  eapply wf_chain_load';eauto.
  specialize CompilEnv.exact_lvl_lvl_of_top with (1:=h_exct_lvlG_CE_)(2:=heq_lvloftop_CE_m'0_) as ? /sng.
  rewrite <- heq_S_ in *.
  subst δ_lvl.
  lia.
Qed.

(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load_var':
  forall stbl CE g locenv stkptr astnum chk m m' b ofs e_t_v id load_id vaddr,
    CompilEnv.exact_levelG CE ->
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned (Datatypes.length CE) locenv g m stkptr)
    -> (4 <= (Ptrofs.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> transl_variable stbl CE astnum id =: load_id
    -> Cminor.eval_expr g stkptr locenv m' load_id vaddr
    -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
Proof.
  intros /sng.
  rename h_le_ into h_ofs_non_zero_.
  simpl in *.
  functional inversion h_eq_transl_var_;subst;clear h_eq_transl_var_ /sng.
  rename m'0 into max_lvl.
  set (δ_lvl:=(max_lvl - lvl_id)%nat) in *.
  eapply wf_chain_load'_2;eauto.
  specialize CompilEnv.exact_lvl_lvl_of_top with (1:=h_exct_lvlG_CE_)(2:=heq_lvloftop_CE_m'0_) as ? /sng.
  rewrite <- heq_S_ in *.
  subst δ_lvl.
  lia.
Qed.


(* INVARIANT OF STORE/STOREV: if we do not touch on addresses zero
     of blocks, chaining variables all poitn to zero ofsets. *)
Lemma wf_chain_load_aligned: forall lvl g locenv chk m m' b ofs e_t_v stkptr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (4 <= (Ptrofs.unsigned ofs))
    -> stack_localstack_aligned lvl locenv g m stkptr
    -> stack_localstack_aligned lvl locenv g m' stkptr.
Proof.
  unfold stack_localstack_aligned at 2.
  intros /sng.
  generalize h_aligned_g_m_.
  intros /sng.
  specialize (h_aligned_g_m_ (δ_lvl) h_le_δ_lvl_lvl_).
  decomp h_aligned_g_m_.
  exists b_δ.
  destruct δ_lvl /sng.
  - simpl.
    inversion h_CM_eval_expr_ /sng.
    econstructor;eauto.
  - cbn.
    inversion h_CM_eval_expr_ /sng.
    eapply eval_Eload with (vaddr:=vaddr).
    eapply wf_chain_load'4 with (lvl:=lvl);eauto; try lia.
    rewrite <- h_loadv_.
    destruct vaddr;cbn;try discriminate.
    eapply Mem.load_store_other;eauto.
    cbn.
    red in h_aligned_g_m0_.
    assert ((δ_lvl <= lvl)%nat) by lia /sng.
    specialize (h_aligned_g_m0_ δ_lvl h_le_δ_lvl_lvl0_).
    decomp h_aligned_g_m0_.
    assert ((Values.Vptr b0 i) = (Values.Vptr b_δ0 Ptrofs.zero)) /sng.
    { eapply det_eval_expr;eauto. }
    invclear heq_vptr_b0_i_ /sng.
    right.
    left.
    rewrite Ptrofs.unsigned_zero.
    cbn.
    lia.
Qed.

Lemma wf_chain_load_aligned':forall sp lvl g locenv m,
    stack_localstack_aligned lvl locenv g m sp ->
    lvl = 0%nat ∨ exists b, sp = (Values.Vptr b Ptrofs.zero).
Proof.
  intros sp CE g locenv m h_aligned_g_m_.
  red in h_aligned_g_m_.
  destruct CE /sng.
  - left;reflexivity.
  - right.
    edestruct h_aligned_g_m_ with (δ_lvl:=0%nat);cbn;try lia /sng.
    cbn in *.
    inversion h_CM_eval_expr_;subst /sng.
    cbn in *.
    invclear h_eval_constant_ /sng.
    destruct sp; cbn in *; try discriminate /sng.
    rewrite Ptrofs.add_zero in h_val_offs_sp_zero_.
    inversion h_val_offs_sp_zero_ /sng.
    eauto.
Qed.


Lemma assignment_preserve_loads_offset_non_null:
  forall stbl s CE spb ofs locenv' g m x x0 nme_t nme_chk nme_t_addr e_t_v m',
    invariant_compile CE stbl ->
    match_env_ stbl s CE (Values.Vptr spb ofs) locenv' g m ->
    transl_name stbl CE (Identifier x x0) =: nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv' m nme_t nme_t_addr ->
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
    stack_localstack_aligned (Datatypes.length CE) locenv' g m' (Values.Vptr spb ofs).
Proof.
  intros /sng.
  decomp (storev_inv _ _ _ _ _ heq_storev_e_t_v_m'_) ;subst.
  functional inversion heq_transl_name_.
  eapply wf_chain_load_aligned;eauto with spark.
  eapply eval_build_loads_offset_non_null_var;eauto with spark.
Qed.

Lemma assignment_preserve_stack_match_addresses :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    invariant_compile CE stbl ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
    transl_value e_v e_t_v ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (Identifier a id) = Errors.OK chk ->
    (* the two storing operation maintain match_env_ *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env_ stbl s CE stkptr locenv g m ->
    stack_match_addresses stbl CE stkptr locenv g m'.
Proof.
  intros; red /sng. intros /sng.
  functional inversion heq_transl_name_;subst /sng.
  functional inversion h_eq_transl_var_;subst /sng.
  assert (exists id_t_v_pt id_t_v_ofs, id_t_v = Values.Vptr id_t_v_pt id_t_v_ofs) /sng.
  { destruct id_t_v;try discriminate. eauto. }
  decomp h_ex_; subst.
  destruct (Nat.eq_dec id id0).
  - subst.
    exists (Values.Vptr id_t_v_pt id_t_v_ofs).
    destruct (match_env_sp_zero_ _ _ _ _ _ _ _ h_match_env_);subst.
    eapply wf_chain_load_var;eauto with spark.
    + eapply assignment_preserve_loads_offset_non_null;eauto.
    + eapply eval_build_loads_offset_non_null_var;eauto with spark.
    + destruct (transl_variable_astnum _ _ _ _ _ h_eq_transl_var_ astnum).
      rewrite h_eq_transl_var_ in heq_transl_variable0_.
      inversion heq_transl_variable0_;subst.
      assumption.
  - assert (∃ addr : Values.val, Cminor.eval_expr g stkptr locenv m nme_t addr) /sng.
    { eapply h_match_env_;eauto. }
    decomp h_ex_.
    exists nme_t_v.
    destruct (match_env_sp_zero_ _ _ _ _ _ _ _ h_match_env_);subst.
    eapply wf_chain_load_var;eauto with spark.
    + eapply assignment_preserve_loads_offset_non_null;eauto.
    + eapply eval_build_loads_offset_non_null_var;eauto with spark.
Qed.

Lemma assignment_preserve_stack_match :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    CompilEnv.exact_levelG CE ->
    all_addr_no_overflow CE ->
    all_frm_increasing CE ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
    transl_value e_v e_t_v ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (Identifier a id) = Errors.OK chk ->
    (* the two storing operation maintain match_env_ *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env_ stbl s CE stkptr locenv g m ->
    stack_match stbl s' CE stkptr locenv g m'.
Proof.
  intros until m'.
  intros /sng.
  destruct h_match_env_ /sng.
  destruct h_safe_cm_CE_m_ /sng.
  (* Getting rid of erronous cases *)
  functional inversion h_eq_transl_var_ /sng.
  rename m'0 into lvl_max.
  (* done *)
  (* getting rid of erroneous storev parameter *)
  (* rewrite <- cm_storev_ok in heq_storev_e_t_v_m'_. *)
  rew cm_storev_ok with functional inversion heq_storev_e_t_v_m'_;subst /sng.
  set (loads_id:=(build_loads (lvl_max - lvl_id) δ_id)) in *.
  (* done *)
  assert (h_ofs_nonzero_:4 <= Ptrofs.unsigned ofs). {
    eapply eval_build_loads_offset_non_null_var;eauto. }
  unfold stack_match.
  intros other_nme other_v addr_other load_addr_other type_other cm_typ_other;intros; up_type /sng.
  (* id can already be evaluated in s *)
  (* NO MORE completestack destruct (h_stk_cmpl_s_CE_ _ _ _ h_eq_transl_var_) as [v_id_prev h_eval_name_id_val_prev_]. *)
  set (nme:=(Identifier a id)) in *.
  (* Getting rid of erronous cases *)
  functional inversion heq_transl_name_ /sng.
  subst.
  (* done *)
  rename id0 into other_id.
  set (other_nme:=(Identifier astnum other_id)) in *.
  (* other_nme can already be evaluated in s *)
  assert (heq_ftch_astnum_:symboltable.fetch_exp_type_ astnum stbl = Some cm_typ_other). {
    simpl in heq_type_of_name_.
    destruct (symboltable.fetch_exp_type_ astnum stbl);try discriminate.
    inversion heq_type_of_name_ /sng.
    reflexivity. }
  assert (h_tr_exp_other_:
            transl_expr stbl CE (Name 1%nat (Identifier astnum other_id))
                        =: load_addr_other). {
    simpl.
    simpl in heq_type_of_name_.
    rewrite heq_ftch_astnum_.
    rewrite heq_transl_variable0_.
    invclear heq_type_of_name_ /sng.
    unfold value_at_addr.
    rewrite heq_transl_type_;simpl.
    assumption. }
  destruct (Nat.eq_dec id other_id) /sng.
  - subst nme. (* same variable ==> result is the value just stored *)
    subst other_nme.
    subst other_id.
    simpl in heq_type_of_name_.
    assert (chk = AST.Mint32). {
      rew compute_chnk_ok with functional inversion heq_compute_chnk_;subst;auto /sng. }
    simpl in heq_compute_chnk_.
    unfold compute_chnk_astnum in heq_compute_chnk_.
(*     unfold compute_chnk_id in heq_compute_chnk_. *)
    rewrite heq_ftch_astnum_ in heq_type_of_name_.
(*     rewrite heq_type_of_name_ in heq_compute_chnk_. *)
    lazy beta iota delta [bind] in heq_compute_chnk_.
    rewrite (transl_variable_astnum _ _ _ _ _ heq_transl_variable0_ a) in *.
    rewrite heq_transl_variable0_ in h_eq_transl_var_.
    invclear h_eq_transl_var_ /sng.
    assert (e_v = other_v) /sng. { eapply storeUpdate_id_ok_same_eval_name ;eauto. }
                               subst other_v.
    exists e_t_v;split;auto.
    functional inversion heq_make_load_;subst /sng.
    eapply eval_Eload with (Values.Vptr b ofs).
    * { eapply wf_chain_load_var with (2:= heq_storev_e_t_v_m'_);eauto.
        - eapply wf_chain_load_aligned;eauto. }
    * simpl.
      (* Should be ok by well typedness of the chained stack wrt
           stbl (see hyp on compute_chk). *)
      (* assert (chunk = AST.chunk_of_type t). {
           rewrite cmtype_chk with (1:=heq_transl_type_) (2:=heq_opttype_) (3:=heq0).
           reflexivity. } *)
      assert (chunk = AST.Mint32). {
        functional inversion heq_transl_type_;subst;simpl in h_access_mode_cm_typ_nme_ /sng.
        - inversion h_access_mode_cm_typ_nme_;auto.
        - inversion h_access_mode_cm_typ_nme_;auto. }
      subst.
      specialize Mem.load_store_same with (1:=heq_store_e_t_v_m'_);intro h.
      erewrite h.
      destruct e_t_v;auto;destruct e_v;simpl in *;try discriminate;
        now inversion h_transl_value_e_v_e_t_v_.

  - (* loading a different variable id' than the one stored id.
         2 steps: first prove that the addresses of id' and id did
         not change (the translated expressions did not change + the
         chained stack did not change either), and thus remain
         different, then conclude that the value stored in id' did
         not change. *)
    assert (chk = AST.Mint32) /sng. {
      rew function_utils.compute_chnk_ok with functional inversion heq_compute_chnk_; reflexivity. }

    (*xxxx NO MORE destruct (h_stk_cmpl_s_CE_ _ _ _ heq_transl_variable0_) as [v_other_id_prev h_eval_name_other_id_val_prev_]. *)
    generalize h_stk_mtch_addr_stkptr_m_;intros /sng.
    red in h_stk_mtch_addr_stkptr_m0_.
    specialize h_stk_mtch_addr_stkptr_m0_ with (1:=heq_transl_name_).
    destruct h_stk_mtch_addr_stkptr_m0_ /sng.
    red in h_stk_mtch_s_m_.
    specialize h_stk_mtch_s_m_ with (2:=h_CM_eval_expr_addr_other_addr_other_v_) (1:=heq_transl_name_)
                                   (5:=heq_type_of_name_) (4:=heq_transl_type_)(6:=heq_make_load_) as h.
    
    assert (evalName stbl s (Identifier astnum other_id) (OK other_v)) /sng.
    { constructor.
      erewrite storeUpdate_id_ok_others with (1:=h_storeUpd_);auto.
      unfold other_nme in h_eval_name_other_nme_other_v_.
      inversion h_eval_name_other_nme_other_v_ /sng.
      assumption. }
    subst.
    specialize h with (1:=h_eval_name_other_v_).
    destruct h as [ cm_v [tr_val_v_other h_cm_eval_m_v_other_]].
    exists cm_v.
    split;auto.
    assert (h_aligned_m'_ : stack_localstack_aligned (Datatypes.length CE) locenv g m' stkptr). {
      eapply wf_chain_load_aligned;eauto. }
    functional inversion heq_make_load_;subst /sng.
     
    (* inversion cm_eval_m_v_other /sng. *)
    generalize (wf_chain_load_var _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                  h_exct_lvlG_CE_
                                  heq_storev_e_t_v_m'_ h_aligned_m'_
                                  h_ofs_nonzero_ heq_transl_variable0_
                                  h_CM_eval_expr_addr_other_addr_other_v_).
    intro /sng.
    econstructor.
    + eassumption.
    + inversion h_cm_eval_m_v_other_ /sng.
      assert (addr_other_v = addr_other_v0).
      { eapply det_eval_expr with (m:=m); eauto. }
      subst addr_other_v0.
      destruct addr_other_v; try discriminate;simpl in *.
      clear h_tr_exp_other_.
      erewrite Mem.load_store_other;[now eassumption| now eassumption | ].
      subst nme other_nme.
      unfold compute_chnk_id in heq_compute_chnk_.
      destruct (symboltable.fetch_exp_type_ astnum stbl) eqn:heq_fetchvartyp_;try discriminate.
      invclear heq_ftch_astnum_ /sng.
      unfold stack_separate in h_separate_CE_m_.


      eapply h_separate_CE_m_ with (nme:=(Identifier astnum id))
                                    (nme':=(Identifier astnum other_id))
                                    (k₂ := b0) (k₁:=b);
        clear h_separate_CE_m_;simpl;try eassumption;auto.
        * rewrite heq_fetchvartyp_.
          reflexivity.
        * rewrite heq_fetchvartyp_.
          reflexivity.
        * erewrite transl_variable_astnum;eauto.
        * rewrite h_access_mode_cm_typ_nme_.
          f_equal.
          eq_same_clear.
          clear heq_type_of_name_.
          functional inversion heq_transl_type_;subst;auto;cbn in *.
          -- inversion heq_make_load_;reflexivity.
          -- inversion heq_make_load_;reflexivity.
        * intro abs.
          inversion abs;subst;try discriminate.
          elim hneq_id;reflexivity.
Qed.


Lemma assignment_preserve_stack_match_function_ :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    CompilEnv.exact_levelG CE ->
    all_frm_increasing CE ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
    transl_value e_v e_t_v ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (Identifier a id) = Errors.OK chk ->
    (* the two storing operation maintain match_env_ *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env_ stbl s CE stkptr locenv g m ->
    stack_match_functions_ stbl stkptr CE locenv g m'.
Proof.
  intros /sng.
  red.
  intros /sng.
  destruct h_match_env_ /sng.
  destruct h_safe_cm_CE_m_ /sng.
  up_type.
  red in h_stk_mtch_fun_.
  specialize (h_stk_mtch_fun_ p pb_lvl pb heq_fetch_proc_p_).
   destruct h_stk_mtch_fun_ as [CE' [CE'' [paddr [pnum [fction [lglobdef [? [? [? ?]]]]]]]]] /sng.
  exists CE', CE'', paddr, pnum, fction, lglobdef.
  split;[|split;[|split]];subst;eauto.
  inversion h_CM_eval_expr_paddr_.
  constructor.
  assumption.
Qed.


(*
Lemma updateG_ok_frameG_same_lvl : forall stk id v stk' sto_id  lvl,
    updateG stk id v = Some stk' ->
    STACK.exact_levelG stk ->
    frameG id stk = Some (lvl,sto_id) ->
    forall id' sto'_id',
      frameG id' stk = Some (lvl,sto_id) -> 
      frameG id' stk' = Some (lvl,sto'_id') ->
      Some (lvl,sto'_id') = update (lvl, sto_id) id' v.
Proof.
  intros /sng.
  specialize updateG_spec_1 with (1:=heq_updateG_stk_id_) /sng.
  intro h_ex_;decomp h_ex_;subst;up_type.
  rename H2 into h_forall_.
  rewrite heq_frameG_ in heq_frameG2_.
  invclear heq_frameG2_ /sng.
  unfold update in heq_update_sto_id_.
  cbn in heq_update_sto_id_.
  destruct (updates sto_id id v) eqn:heq; try discriminate /sng.
  invclear heq_update_sto_id_ /sng.
  assert (s =sto'_id').
  { eapply exact_levelG_frameG_unique_lvl;eauto.
    admit. }
  subst.
  unfold update.
  cbn.


  assert (sto'_id' = sto_id).
  { admit. }
  subst.
  unfold update.
  cbn.



  intros until v.
  functional induction (updateG stk id v);simpl;intros;try discriminate;rename x into id;subst;up_type /sng.
  - unfold update;cbn.
    invclear heq_Some_;simpl /sng.
    assert (reside id f = true) /sng.
    { eapply update_ok_same_reside_orig; eauto. }
    rewrite heq_reside_ in heq_Some0_.
    invclear heq_Some0_ /sng.
    unfold update in heq_update_f_x_.
    cbn in heq_update_f_x_.
    assert (updates sto_id id v) /sng.

    assert (reside id' (lvl_id, sto_id) = false) /sng.
    { cbn in *.
      destruct (resides id' sto_id);auto.
      exfalso.
      inversion heq_Some1_.
      now apply hneq. }
    rewrite heq_reside0_ in heq_Some1_.
    unfold update in heq_update_f_x_.
    cbn in heq_update_f_x_.

    functional inversion heq_frameG_;subst.
    + exfalso.
      apply hneq.
      destruct (updates sto_id id v);try discriminate.
      now inversion heq_update_f_x_.
    + rewrite X in heq_Some1_.
      now inversion heq_Some1_.
  - up_type.
    assert (reside id f = false) /sng.
    { apply reside_false_fetch_none_.
      rewrite <- update_ok_none;eauto. }
    rewrite heq_reside_ in heq_Some0_.
    invclear heq_Some_ /sng.
    destruct (reside id' f) eqn:heq.
    + invclear heq_Some1_ /sng.
      cbn in heq_frameG_.
      cbn in heq.
      rewrite heq in heq_frameG_.
      now inversion  heq_frameG_.
    + eapply IHo ;eauto.
      cbn in heq_frameG_.
      now rewrite heq in heq_frameG_.
Qed.
*)

Lemma assignment_preserve_stack_match_CE_ :
  forall stbl CE s a id id_t e_v s',
    (* translating the variabe to a Cminor load address, so id belongs to CE *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* the two storing operation maintain match_env_ *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    stack_match_CE_ s CE ->
    stack_match_CE_ s' CE.
Proof.
  intros /sng.
  red.
  intros /sng.
  up_type.
  red in h_stk_mtch_CE_s_CE_.
  specialize (h_stk_mtch_CE_s_CE_ nme lvl).
  destruct h_stk_mtch_CE_s_CE_ as [h_stk_mtch_CE_s_CE_ h_stk_mtch_CE_s_CE'_].
  destruct (Nat.eq_dec id nme) /sng.
  - subst nme.
    functional inversion h_eq_transl_var_ /sng.
    subst.
    inversion h_storeUpd_;subst /sng.
    pose proof (storeUpdate_id_ok_same _ _ _ _ _ _ h_storeUpd_) /sng.
    destruct (updateG_ok_same_orig _ _ _ _ heq_updateG_s_id_) /sng.
    rename x into e_v'.
    split;intros /sng.
    + pose proof updateG_ok_same_frameG_orig _ _ _ _ _ _ heq_updateG_s_id_ heq_frameG_ /sng.
      destruct h_ex_ /sng.
      apply h_stk_mtch_CE_s_CE_ with (1:=heq_frameG0_).
    + specialize h_stk_mtch_CE_s_CE'_ with (1:=heq_CEframeG_id_CE0_).
      decomp h_stk_mtch_CE_s_CE'_.
      eapply updateG_ok_same_frameG;eauto.
  - functional inversion h_eq_transl_var_ /sng.
    subst.
    inversion h_storeUpd_;subst /sng.
    pose proof storeUpdate_id_ok_others _ _ _ _ _ _ h_storeUpd_ _ hneq_id /sng.
    destruct (updateG_ok_same_orig _ _ _ _ heq_updateG_s_id_) /sng.
    pose proof (updateG_ok_others_frameG _ _ _ _ heq_updateG_s_id_) /sng.
    specialize h_forall_id'_ with (1:=hneq_id).
    split;intros /sng.
    + assert (exists sto', frameG nme s = Some (lvl, sto')) /sng.
      { pose proof (updateG_ok_others_frameG_orig _ _ _ _ heq_updateG_s_id_ _ _ _ hneq_id heq_frameG_).
        assumption. }
      destruct h_ex_ /sng.
      rename x0 into sto'.
      specialize h_forall_id'_ with (1:=heq_frameG0_).
      eapply h_stk_mtch_CE_s_CE_;eauto. 
    + specialize h_stk_mtch_CE_s_CE'_ with (1:=heq_CEframeG_nme_CE_).
      destruct h_stk_mtch_CE_s_CE'_;eauto.
Qed.



Lemma assignment_preserve_stack_complete :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
    transl_value e_v e_t_v ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (Identifier a id) = Errors.OK chk ->
    (* the two storing operation maintain match_env_ *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    stack_complete stbl s CE ->
    stack_complete stbl s' CE.
Proof.
  intros /sng.
  red.
  intros /sng.
  destruct (Nat.eq_dec nme id) /sng.
  - subst.
    exists e_v.
    constructor.
    eapply storeUpdate_id_ok_same;eauto.
  - red in h_stk_cmpl_s_CE_.
    destruct h_stk_cmpl_s_CE_ with (1:=heq_transl_variable0_) /sng.
    exists x.
    constructor.
    invclear h_eval_name_x_ /sng.
    erewrite <- storeUpdate_id_ok_others.
    + eassumption.
    + eassumption.
    + apply not_eq_sym;assumption.
Qed.

Lemma assignment_preserve_stack_separate :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr m',
    invariant_compile CE stbl ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
    transl_value e_v e_t_v ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (Identifier a id) = Errors.OK chk ->
    (* the two storing operation maintain match_env_ *)
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env_ stbl s CE stkptr locenv g m ->
    stack_separate stbl CE stkptr locenv g m'.
Proof.
  intros /sng.
  red.
  intros /sng.
  destruct h_match_env_ /sng.
  destruct h_safe_cm_CE_m_ /sng.
  decomp (storev_inv _ _ _ _ _ heq_storev_e_v_t_m'_);subst.
  functional inversion heq_transl_name0_;subst /sng.
  generalize heq_transl_name_.
  intro h_transl_name_remember_.
  functional inversion h_transl_name_remember_.
  eapply wf_chain_load_var' with (m:=m) in h_CM_eval_expr_nme_t_.
  - eapply wf_chain_load_var' with (m:=m) in h_CM_eval_expr_nme'_t_.
    + eapply h_separate_CE_m_ with (1:=heq_type_of_name_);eauto.
    + apply h_inv_comp_CE_stbl_.
    + eassumption.
    + assumption.
    + eapply eval_build_loads_offset_non_null_var with (6:=h_CM_eval_expr_id_t_id_t_v_)
      ;eauto with spark.
    + simpl in heq_transl_name0_.
      eauto.
  - apply h_inv_comp_CE_stbl_.
  - eassumption.
  - assumption.
  - eapply  eval_build_loads_offset_non_null_var with (6:=h_CM_eval_expr_id_t_id_t_v_)
    ;eauto with spark.
  - eauto.
Qed.

Lemma assignment_preserve_stack_no_null_offset :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
    transl_value e_v e_t_v ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (Identifier a id) = Errors.OK chk ->
    (* the two storing operation maintain match_env_ *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env_ stbl s CE stkptr locenv g m ->
    stack_no_null_offset CE.
Proof.
  intros /sng.
  destruct h_match_env_ /sng.
  destruct h_safe_cm_CE_m_ /sng.
  assumption.
Qed.

Lemma assignment_preserve_stack_safe :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
    transl_value e_v e_t_v ->
    (* if e_v is an int, then it is not overflowing (we are not trying
       to add an overflowing value to the environment). *)
    (forall n, e_v = Int n -> overflowCheck n (OK (Int n))) ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (Identifier a id) = Errors.OK chk ->
    (* the two storing operation maintain match_env_ *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env_ stbl s CE stkptr locenv g m ->
    safe_stack s'.
Proof.
  intros /sng.
  match goal with H: context C [overflowCheck] |- _ => rename H into h_overf_e_v_ end.
  destruct h_match_env_ /sng.
  destruct h_safe_cm_CE_m_ /sng.
  intros /sng.
  red.
  intros /sng.
  destruct (Nat.eq_dec id0 id) /sng.
  - subst.
    apply h_overf_e_v_.
    erewrite storeUpdate_id_ok_same in heq_SfetchG_id0_s'_;eauto.
    inversion heq_SfetchG_id0_s'_ /sng.
    reflexivity.
  - red in h_safe_stack_s_.
    apply h_safe_stack_s_ with (id:=id0);eauto.
    erewrite storeUpdate_id_ok_others;eauto.
Qed.




Lemma assignment_preserve_stack_freeable:
  forall stbl s CE spb ofs locenv' g m x x0 nme_t nme_chk nme_t_addr e_t_v m',
    invariant_compile CE stbl ->
    match_env_ stbl s CE (Values.Vptr spb ofs) locenv' g m ->
    transl_name stbl CE (Identifier x x0) =: nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv' m nme_t nme_t_addr ->
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
    stack_freeable stbl CE (Values.Vptr spb ofs) g locenv' m'.
Proof.
  intros /sng.
  red.
  intros /sng.
  destruct nme_t_v;simpl in * ; try discriminate.
  eapply Mem.store_valid_access_1.
  - eassumption.
  - eapply (me_stack_freeable (me_safe_cm_env h_match_env_));eauto.
    eapply wf_chain_load_var';eauto with spark.
    eapply eval_build_loads_offset_non_null_var
      with (6:=h_CM_eval_expr_nme_t_nme_t_v_);eauto with spark.
Qed.




    

Local Hint Resolve
     assignment_preserve_stack_match assignment_preserve_stack_match_CE_
     assignment_preserve_stack_match_function_
     assignment_preserve_stack_complete
     assignment_preserve_stack_separate assignment_preserve_loads_offset_non_null
     assignment_preserve_stack_no_null_offset assignment_preserve_stack_safe
     assignment_preserve_stack_freeable assignment_preserve_stack_match_addresses : spark.


  


(* TODO: prove and  move somewhere else. *)
Lemma exec_stmt_assoc: forall g the_proc stackptr locenv m prog1 prog2 prog3 trace locenv' m' Out_normal,
    exec_stmt g the_proc stackptr locenv m (Sseq (Sseq prog1 prog2) prog3 )  trace locenv' m' Out_normal ->
    exec_stmt g the_proc stackptr locenv m (Sseq prog1 (Sseq prog2 prog3))  trace locenv' m' Out_normal.
Proof.
Admitted.

Lemma exec_stmt_assoc_2: forall g the_proc stackptr locenv m prog1 prog2 prog3 prog4 prog5 trace locenv' m' Out_normal,
    exec_stmt
      g the_proc stackptr locenv m
      (Sseq (Sseq prog1 (Sseq prog2 prog3)) (Sseq prog4 prog5))
      trace locenv' m' Out_normal ->
    exec_stmt
      g the_proc stackptr locenv m
      (Sseq (Sseq (Sseq prog1 (Sseq prog2 prog3)) (Sseq prog4 Sskip)) prog5)
      trace locenv' m' Out_normal.
Proof.
Admitted.



Lemma assignment_preserve_chained_stack_structure:
  forall stbl CE g locenv stkptr m a chk id id_t e_t_v idaddr m' n,
    chained_stack_structure m n stkptr ->
    all_addr_no_overflow CE -> 
    Datatypes.length CE ≤ n -> (* the chaining structure must be at least as deep as CE *)
    (*     stack_localstack_aligned CE locenv g m ->  *)
    stack_no_null_offset CE -> 
    CompilEnv.exact_levelG CE ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (Identifier a id) = Errors.OK chk ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    chained_stack_structure m' n stkptr.
Proof.
  intros /sng.
  destruct id_t_v;try discriminate.
  assert (4 <= (Ptrofs.unsigned i)) /sng.
  { eapply eval_build_loads_offset_non_null_var;eauto.
    eapply chain_aligned ;eauto. }
  eapply assignment_preserve_chained_stack_structure_aux; eauto.
Qed.

Lemma assignment_preserve_safe_cm_env:
  forall stbl s CE spb ofs locenv locenv' g m x x0 nme_t nme_chk nme_t_addr e_v e_t_v s' m',
    invariant_compile CE stbl ->
    match_env_ stbl s CE (Values.Vptr spb ofs) locenv g m ->
    transl_name stbl CE (Identifier x x0) =: nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t nme_t_addr ->
    compute_chnk stbl (Identifier x x0) = Errors.OK nme_chk ->
    transl_value e_v e_t_v ->
    storeUpdate stbl s (Identifier x x0) e_v (OK s') ->
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
    safe_cm_env stbl CE (Values.Vptr spb ofs) locenv' g m'.
Proof.
  intros /sng.
  assert (safe_cm_env stbl CE (Values.Vptr spb ofs) locenv g m') /sng.
  { split;eauto with spark.
    eapply assignment_preserve_chained_stack_structure;eauto with spark. }
  eapply safe_cm_env_inv_locenv;eauto.
Qed.
  
(*
Lemma aux: forall s nme v s',
    updateG s nme v = Some s' ->
    forall lvl sto_nme sto_nme' sto' sto'' sto'_updated,
      frameG nme s = Some (lvl, sto_nme) ->
      frameG nme s' = Some (lvl, sto_nme') ->
      cuts_to nme sto_nme = (sto', sto'') -> 
      cuts_to nme sto_nme' = (sto'_updated, sto'').
Proof.
  intros s nme v s' ? /sng.
  functional induction updateG s nme v;(try now (simpl;!intros;discriminate));!intros /sng.
  - inversion heq;subst;clear heq.
    cbn in *.
*)

Lemma assignment_preserve_exact_levelG:
  forall s x v s',
    ST.updateG s x v = Some s' ->
    exact_levelG s -> 
    exact_levelG s'.
Proof.
Admitted.



Lemma updateG_preserve_Nodup_s:
  forall s x v s',
    NoDup_G s →
    ST.updateG s x v = Some s' ->
    NoDup s -> 
    NoDup s'.
Proof.
  intros s x v s' h.   
  revert s' h.
  functional induction (ST.updateG s x v);try now(intros;discriminate) /sng.
  - intros /sng.
    invclear heq_Some_ /sng.
    eapply update_nodup;eauto.
  - intros /sng.
    invclear heq_Some_ /sng.
    specialize (h_forall_s'_ s'').
    assert (NoDup s') as h_nodup_s'_.
    { eapply stack_NoDup_cons; eauto. }
    assert (NoDup_G s') as h_nodupG_s'_.
    { eapply stack_NoDup_G_cons; eauto. }
    specialize h_forall_s'_ with (1:=h_nodupG_s'_) (2:=heq_updateG_s'_x_) (3:=h_nodup_s'_).
    eapply nodup_cons with (1:=h_forall_s'_).
    apply stack_NoDup_prefix  with (CE1:=[f])(CE2:=s');eauto.
Qed.


Lemma storeUpdate_preserve_Nodup_s:
  forall stbl s x x0 e_v s',
    NoDup_G s →
    storeUpdate stbl s (Identifier x x0) e_v (OK s') ->
    NoDup s -> 
    NoDup s'.
Proof.
  intros /sng.
  inversion h_storeUpd_ /sng.
  clear h_storeUpd_.
  specialize updateG_spec_1 with (1:=heq_updateG_s_x0_).
  intro h.
  decomp h.
  subst.
  eapply updateG_preserve_Nodup_s;eauto.
Qed.

Lemma storeUpdate_preserve_Nodup_G_s:
  forall stbl s x x0 e_v s',
    NoDup_G s →
    storeUpdate stbl s (Identifier x x0) e_v (OK s') ->
    NoDup_G s'.
Proof.
  intros /sng.
  inversion h_storeUpd_ /sng.
  clear h_storeUpd_.
  specialize updateG_spec_1 with (1:=heq_updateG_s_x0_).
  intro h.
  decomp h.
  subst.
  eapply updateG_nodup_G;eauto.
Qed.

Lemma foo: forall CE, CE <> nil -> CompilEnv.exact_levelG CE ->  CompilEnv.level_of_top CE = Some (Datatypes.length CE - 1)%nat.
Proof.
  intros /sng.
  destruct CE.
  - elim hneq_CE;auto.
  - inversion h_exct_lvlG_CE_;subst.
    unfold CompilEnv.level_of_top.
    simpl.
    auto with arith.
Qed.

Lemma assignment_preserve_match_env_:
  forall stbl s CE spb ofs locenv g m x x0 nme_t nme_chk nme_t_addr e_v e_t_v s' m',
    forall h_overflow_:(forall n, e_v = Int n -> overflowCheck n (OK (Int n))),
      invariant_compile CE stbl ->
      match_env_ stbl s CE (Values.Vptr spb ofs) locenv g m ->
      transl_name stbl CE (Identifier x x0) =: nme_t ->
      Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t nme_t_addr ->
      compute_chnk stbl (Identifier x x0) = Errors.OK nme_chk ->
      transl_value e_v e_t_v ->
      storeUpdate stbl s (Identifier x x0) e_v (OK s') ->
      Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
      match_env_ stbl s' CE (Values.Vptr spb ofs) locenv g m'.
Proof.
  intros /sng.
  generalize heq_transl_name_; unfold transl_name;intro /sng.
  split;eauto with spark.
  - red.
    transitivity (Datatypes.length s).
    + apply STACK.equiv_stack_lgth.
      inversion h_storeUpd_;subst.
      symmetry.
      eapply updateG_eqlist;eauto.
    + apply h_match_env_.
  - eapply storeUpdate_preserve_Nodup_s;eauto.
    + apply h_match_env_.
    + apply h_match_env_.
  - eapply storeUpdate_preserve_Nodup_G_s;eauto.
    + apply h_match_env_.
  - eapply assignment_preserve_exact_levelG;eauto.
    + inversion h_storeUpd_;subst.
      eassumption.
    + apply h_match_env_.
  - eapply assignment_preserve_safe_cm_env;eauto.
Qed.

(* Is there the shadowed variable? If yes this lemma is wrong. *)
(*
Lemma match_env_cons_:
  forall stbl CE s locenv g m sp sp',
    s<>[] -> CE <> [] -> 
    invariant_compile CE stbl ->
    match_env_ stbl s CE sp locenv g m ->
    Mem.loadv AST.Mint32 m sp = Some sp' ->
    stack_match stbl (List.tl s) (List.tl CE) sp' locenv g m.
Proof.
  unfold stack_match.
  intros /sng.
  functional inversion heq_transl_name_;subst /sng.
  functional inversion h_eq_transl_var_;subst.
  assert (evalName stbl s (Identifier astnum id) (OK v)).
  { admit. (* invariant_compile mplies that CE has no shadowing, thus  *)

  }

  revert dependent m.
  revert dependent s.
  revert dependent typ_nme.
  revert dependent cm_typ_nme.
  revert dependent h_inv_comp_CE_stbl_.
  revert dependent hneq0.
  revert locenv g sp sp' v load_addr_nme.
  functional inversion heq_transl_name_ /sng.
  clear heq_transl_name_.
  revert h_eq_transl_var_ heq_nme_. heq_nme0_.
  remember (tl CE) as CE'.
  revert CE HeqCE' nme_t nme nme0.
  functional induction transl_variable stbl CE' astnum id;simpl;!intros /sng.
  
Admitted.
*)


(** Visibility of variables.  *)

(* [visible_spark_id st CE stnum locenv stkptr m spb ofs] means that
   in the context (st CE g locenv stkptr m) the value (spb+ofs)
   denotes the address (of a byte of) a spark variable id (mapped by
   CE to id_t). Remark: [st] not really used here, its in
   transl_variable only for error messages *)
Definition visible_cminor_addr st CE g astnum locenv stkptr (m:mem) spb ofs :=
  ∃ id id_t,
    (* id_t is the address of id_t *)
    (transl_variable st CE astnum id =: id_t)
    /\ ∃ id_chk, (compute_chnk_id st id =: id_chk)
                 (* the block part of the address is exactly spb and the
                    offset ofs is inside [ofs_id, ofs_id+chnk[. *)   
                 /\ ∃ ofs_id , Cminor.eval_expr g stkptr locenv m id_t (Values.Vptr spb ofs_id)
                               /\ Ptrofs.unsigned ofs_id <= ofs < Ptrofs.unsigned ofs_id + size_chunk id_chk.

(* The negation of previous predicate. *)
Definition invisible_cminor_addr st CE g astnum locenv stkptr (m:mem) spb ofs :=
  ∀ id id_t id_chk spb_id ofs_id,
    (* id_t is the address of id_t *)
    transl_variable st CE astnum id =: id_t
    -> compute_chnk_id st id =: id_chk
    -> Cminor.eval_expr g stkptr locenv m id_t (Values.Vptr spb_id ofs_id)
    (* The address spb+ofs is not part of the interval [spb_id , spb_id+ofs_id[ *)
    -> spb_id ≠ spb \/ ofs >= Ptrofs.unsigned ofs_id + size_chunk id_chk \/ ofs < Ptrofs.unsigned ofs_id.


(* Addresses that should be untouched by a function call: the one
   invisible from the function called except the ones that were free
   at calling time. This exception is mainly to allow the modification
   of the chaining variable in the local stack. This chaining variable
   is invisible (it does not correspond to a spark variable) but it
   will be changed during function initialization. In the future this
   may also include things allocated during the function called, and
   also maybe local variables (not in stack). Moreover at the end of
   the function call, the frame used for is indeed free at call
   time, so forbidden mcaller mcallee is strictly included in
   forbidden m m. *)
Definition forbidden := λ st CE g astnum e sp m_caller m_callee sp_id ofs_id,
                        invisible_cminor_addr st CE g astnum e sp m_callee sp_id ofs_id
                        ∧ ~is_free_block m_caller sp_id ofs_id.

(* A stricter notion for procedure body, where the chaining arg does not change anymore. *)
Definition forbidden_strict := λ st CE g astnum e sp m_callee sp_id ofs_id,
                               invisible_cminor_addr st CE g astnum e sp m_callee sp_id ofs_id.


Ltac rename_hyp_forbid n th :=
  match th with
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "forbid_" m "_" m' "_" sp "_" ofs
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "forbid_" m "_" m'
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "forbid_" m
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "forbid_" m'
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "forbid"

  | forbidden_strict ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?sp ?ofs => fresh "forbid_" m "_" sp "_" ofs
  | forbidden_strict ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?sp ?ofs => fresh "forbid_" m
  | forbidden_strict ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?sp ?ofs => fresh "forbid"

  | invisible_cminor_addr ?st ?CE ?g ?astnum ?e ?sp ?m ?sp'b ?sp'ofs => fresh "invis_" sp "_" "_" m "_" sp'b "_" sp'ofs
  | invisible_cminor_addr ?st ?CE ?g ?astnum ?e ?sp ?m ?sp'b ?sp'ofs => fresh "invis_" sp "_" "_" sp'b "_" sp'ofs
  | invisible_cminor_addr ?st ?CE ?g ?astnum ?e ?sp ?m ?sp'b ?sp'ofs => fresh "invis_" sp'b "_" sp'ofs
  | invisible_cminor_addr ?st ?CE ?g ?astnum ?e ?sp ?m ?sp'b ?sp'ofs => fresh "invis"
  | _ => rename_hyp_incro n th
  end.
Ltac rename_sparkprf ::= rename_hyp_forbid.


(* Are those useful? If yes finish the proofs (needs updating compcert, 
   not true with current version). *)
Axiom trans_unchanged : forall P, transitive _ (Mem.unchanged_on P).


Instance unchanged_on_iff: Proper ((eq ==> eq ==> iff) ==> (eq ==> eq ==> iff)) Mem.unchanged_on.
Proof.
  repeat red.
  intros P Q;intros ;subst /sng.
  intro h_proper_.
  split;intros h;auto.
  - repeat red in h_proper_.
    inversion h.
    constructor;intros .
    + assumption.
    + eapply unchanged_on_perm;auto.
      specialize (h_proper_ b b eq_refl ofs ofs eq_refl).
      destruct h_proper_.
      eauto.
    + eapply unchanged_on_contents;auto.
      specialize (h_proper_ b b eq_refl ofs ofs eq_refl).
      destruct h_proper_.
      eauto.
  - repeat red in h_proper_.
    inversion h.
    constructor;intros .
    + assumption.
    + eapply unchanged_on_perm;auto.
      specialize (h_proper_ b b eq_refl ofs ofs eq_refl).
      destruct h_proper_.
      eauto.
    + eapply unchanged_on_contents;auto.
      specialize (h_proper_ b b eq_refl ofs ofs eq_refl).
      destruct h_proper_.
      eauto.
Qed.



Definition unchange_forbidden st CE g astnum e_chain e_chain' sp m_chain m'_chain :=
  forall (sp_id : Values.block) (ofs_id : Z),
    (forbidden st CE g astnum e_chain sp m_chain  m_chain   sp_id ofs_id <->
     forbidden st CE g astnum e_chain' sp m'_chain m'_chain sp_id ofs_id).

(* TODO *)
Lemma unchange_forbidden_trans: forall st CE g astnum e1 e2 e3 sp m1 m2 m3,
    unchange_forbidden st CE g astnum e1 e2 sp m1 m2 ->
    unchange_forbidden st CE g astnum e2 e3 sp m2 m3 ->
    unchange_forbidden st CE g astnum e1 e3 sp m1 m3.
Proof.
Admitted.

Definition strict_unchanged_on st CE g astnum e_chain e_chain' sp m m' :=
  Mem.unchanged_on (forbidden st CE g astnum e_chain sp m m) m m' /\
  unchange_forbidden st CE g astnum e_chain e_chain' sp m m'.

Ltac rename_hyp_forbid_unch n th :=
  match th with
  | unchange_forbidden ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "unch_forbid_" m "_" m'
  | unchange_forbidden ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "unch_forbid_" m
  | unchange_forbidden ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "unch_forbid_" m'
  | unchange_forbidden ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "unch_forbid_"

  | strict_unchanged_on ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "strict_unch_" m "_" m'
  | strict_unchanged_on ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "strict_unch_" m
  | strict_unchanged_on ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "strict_unch_" m'
  | strict_unchanged_on ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "strict_unch"
  | _ => rename_hyp_forbid n th
  end.
Ltac rename_sparkprf ::= rename_hyp_forbid_unch.


Lemma unchange_forbidden_sym: forall st CE g astnum e1 e_chain' sp m1 m2,
    unchange_forbidden st CE g astnum e1 e_chain' sp m1 m2 ->
    unchange_forbidden st CE g astnum  e_chain' e1 sp m2 m1.
Proof.
  intros /sng.
  red.
  intros sp_id ofs_id. 
  symmetry.
  red in h_unch_forbid_m1_m2_.
  eapply h_unch_forbid_m1_m2_;eauto.
Qed.

Lemma unchange_forbidden_refl: forall st CE g astnum e1 sp m,
    unchange_forbidden st CE g astnum e1 e1 sp m m.
Proof.
  intros /sng.
  red;intros /sng.
  reflexivity.
Qed.

Lemma invisible_cminor_addr_inv_locenv : forall st CE g astnum locenv locenv' stkptr m b ofs,
  invisible_cminor_addr st CE g astnum locenv stkptr m b ofs
 -> invisible_cminor_addr st CE g astnum locenv' stkptr m b ofs.
Proof.
  intros /sng.
  unfold invisible_cminor_addr in *.
  intros /sng.
  eapply h_invis_stkptr__m_b_ofs_;eauto.
  eapply eval_expr_transl_variable_inv_locenv;eauto.
Qed.

Lemma forbidden_inv_locenv: forall st CE g astnum locenv locenv' stkptr m b ofs,
    forbidden st CE g astnum locenv stkptr m m b ofs
    -> forbidden st CE g astnum locenv' stkptr m m b ofs.
Proof.
  intros /sng.
  unfold forbidden in *.
  destruct h_forbid_m_m_b_ofs_ /sng.
  split;auto.
  eapply invisible_cminor_addr_inv_locenv;eauto.
Qed.



Lemma stack_localstack_aligned_locenv:
  forall lvl  g m e1 sp,
    stack_localstack_aligned lvl e1 g m sp -> 
    forall e2, stack_localstack_aligned lvl e2 g m sp.
Proof.
  intros /sng.
  unfold stack_localstack_aligned in *;intros /sng.
  specialize (h_aligned_g_m_ _ h_le_δ_lvl_lvl_).
  decomp h_aligned_g_m_.
  exists b_δ.
  apply eval_expr_build_load_const_inv_locenv with (1:=h_CM_eval_expr_).
Qed.



Lemma store_preserves_structure :
  forall stbl astnum locenv id CE m lvl stkptr g nme_t nme_chk nme_ofst nme_block nme_t_v e_t_v m',
    CompilEnv.exact_levelG CE ->
    stack_no_null_offset CE ->
    all_addr_no_overflow CE ->
    chained_stack_structure m lvl stkptr ->
    stack_localstack_aligned (Datatypes.length CE) locenv g m stkptr ->
    transl_variable stbl CE astnum id =: nme_t ->
    eval_expr g stkptr locenv m nme_t nme_t_v ->
    nme_t_v = Values.Vptr nme_block nme_ofst -> 
    Mem.store nme_chk m nme_block (Ptrofs.unsigned nme_ofst) e_t_v = Some m' -> 
    unchange_forbidden stbl CE g astnum locenv locenv stkptr m m'.
Proof.
  intros /sng.
  red.
  intros /sng.
  split;intros /sng.
  + unfold forbidden.
    destruct h_forbid_m_m_sp_id_ofs_id_ /sng.
    split.
    * red;intros /sng.
      red in h_invis_stkptr__m_sp_id_ofs_id_.
      eapply h_invis_stkptr__m_sp_id_ofs_id_;eauto.      
      eapply wf_chain_load_var';eauto.
      subst.
      functional inversion h_eq_transl_var_.
      assert (4 <= n) /sng.
      { eapply h_nonul_ofs_CE_;eauto. }
      assert (n < Ptrofs.modulus) /sng.
      { eapply h_no_overf_CE_;eauto. }
      subst.
      specialize eval_build_loads_offset
        with (2:=h_aligned_g_m_) (4:=h_CM_eval_expr_nme_t_nme_t_v_) as h.
      rewrite h.
      -- rewrite Ptrofs.unsigned_repr;auto.
         unfold Ptrofs.max_unsigned.
         lia.
      -- apply Zmod_small ;lia.
      -- erewrite <- CompilEnv.exact_lvl_lvl_of_top  with (l:=CE)(n:=m'0);auto;lia.
    * unfold is_free_block in *.
      intro abs.
      apply h_neg_free_blck_m_sp_id_ofs_id_.
      intros perm. 
      intro abs2.
      eapply Mem.perm_store_1 in abs2;eauto.
      eapply abs;eassumption.
  + unfold forbidden.
    destruct h_forbid_m'_m'_sp_id_ofs_id_ /sng.
    split.
    * red;intros /sng.
      red in h_invis_stkptr__m'_sp_id_ofs_id_.
      eapply h_invis_stkptr__m'_sp_id_ofs_id_;eauto.
      assert (4 <= Ptrofs.unsigned nme_ofst) /sng.
      { subst.
        functional inversion h_eq_transl_var_.
        assert (4 <= n) /sng.
        { eapply h_nonul_ofs_CE_;eauto. }
        assert (n < Ptrofs.modulus) /sng.
        { eapply h_no_overf_CE_;eauto. }
        subst.
        specialize eval_build_loads_offset
          with (2:=h_aligned_g_m_) (4:=h_CM_eval_expr_nme_t_nme_t_v_) as h.
        rewrite h.
        -- rewrite Ptrofs.unsigned_repr;auto.
           unfold Ptrofs.max_unsigned.
           lia.
        -- apply Zmod_small ;lia.
      -- erewrite <- CompilEnv.exact_lvl_lvl_of_top  with (l:=CE)(n:=m'0);auto;lia. }
      eapply wf_chain_load_var;eauto.
      eapply wf_chain_load_aligned;eauto.
    * unfold is_free_block in *.
      intro abs.
      apply h_neg_free_blck_m'_sp_id_ofs_id_.
      intros perm. 
      intro abs2.
      eapply Mem.perm_store_2 in abs2;eauto.
      eapply abs;eassumption.
Qed.

  (* The forbidden *addresses* remain the same when storing values of
   parameters in the local stack. + chained_structure preserved.  *)
Lemma exec_store_params_preserve_forbidden_subproof:
  forall lparams st CE initparams,
    CompilEnv.exact_levelG CE ->    
    stack_no_null_offset CE ->
    all_addr_no_overflow CE ->
    store_params st CE lparams = Errors.OK initparams -> 
    forall astnum g proc_t sp e_chain e_chain' m t2 m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp ->
      exec_stmt g proc_t sp e_chain m initparams t2 e_chain' m' Out_normal ->
      chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_chain e_chain' sp m m'.
Proof.
  intros until CE /sng.
  rew store_params_ok
      with functional induction function_utils.store_params st CE lparams;cbn;!!intros;try discriminate;eq_same_clear; up_type /sng.
  - inversion h_exec_stmt_initparams_Out_normal_.
    split.
    + subst.
      assumption.
    + red.
      reflexivity.
  (* to avoid duplicating In and In_Out The three following cases are identical, i.e. the parameter mode
       should not be case split but functional induction does and I don't
       want to make the induction by hand. *)
  - specialize (h_forall_initparams_ _ h_exct_lvlG_CE_ h_nonul_ofs_CE_ h_no_overf_CE_ heq_store_params_).
    invclear h_exec_stmt_initparams_Out_normal_; eq_same_clear /sng.
    specialize h_forall_initparams_ with (astnum:=astnum)(1:=heq_length_)(4:=h_exec_stmt_x0_Out_normal_).
    rename m1 into m_mid.
    rename e1 into e_mid.
    assert ({parameter_mode prm = Out} + {parameter_mode prm <> Out}) as h /sng. {
      destruct (parameter_mode prm);auto.
      all:right;intro abs;discriminate. }
    destruct h /sng.
    { rewrite heq_parameter_mode_ in *|-*.
      simpl in *.
      inversion h_exec_stmt_ /sng.
      apply h_forall_initparams_;auto. }
    assert (exists v_x1, (build_param_copyin_assign (parameter_mode prm) x1 x (transl_paramid (parameter_name prm))) = (Sstore x x1 v_x1)) /sng. {
      unfold build_param_copyin_assign in *.
      destruct (parameter_mode prm);simpl in h_exec_stmt_|-* /sng.
      - eauto.
      - exfalso; apply hneq_Out.
        reflexivity.
      - eauto. }
    decomp h_ex_.
    rewrite heq_build_param_copyin_assign_ in h_exec_stmt_.
    inversion h_exec_stmt_ /sng.
    assert (stack_localstack_aligned (Datatypes.length CE) e_mid g m_mid sp) /sng.
    { 
      unfold Mem.storev in heq_storev_v_x1_v_m_mid_.
      destruct x1_v; try discriminate.
      eapply wf_chain_load_aligned;eauto.
      eapply eval_build_loads_offset_non_null_var;eauto. }
    assert (stack_localstack_aligned (Datatypes.length CE) e_chain' g m sp) /sng.
    { eapply stack_localstack_aligned_locenv;eauto. }
    specialize (fun h_chain_ => h_forall_initparams_ h_chain_ h_aligned_g_m_mid_).
    assert (chained_stack_structure m_mid lvl sp) /sng.
    { eapply assignment_preserve_chained_stack_structure;eauto.
      lia. }
    specialize (h_forall_initparams_ h_chain_m_mid_lvl_sp_).
    split.
    { apply h_forall_initparams_. }
    { eapply unchange_forbidden_trans with (m2:=m_mid); [| eapply h_forall_initparams_].
      clear h_forall_initparams_ h_exec_stmt_x0_Out_normal_ m'.
      red.
      intros /sng.
      split;intros /sng.
      + unfold forbidden.
        destruct h_forbid_m_m_sp_id_ofs_id_ /sng.
        split.
        * red;intros /sng.
          red in h_invis_sp__m_sp_id_ofs_id_.
          specialize (h_invis_sp__m_sp_id_ofs_id_
                        id id_t id_chk spb_id ofs_id0 h_eq_transl_var_ heq_compute_chnk_id_).
          set (val_id_t:=(Values.Vptr spb_id ofs_id0)) in *;up_type.
          assert (Cminor.eval_expr g sp e_mid m id_t val_id_t) /sng.
          { unfold Mem.storev in heq_storev_v_x1_v_m_mid_.
            destruct x1_v; try discriminate.
            eapply eval_expr_transl_variable_inv_locenv with (locenv:=e_chain');eauto.
            eapply wf_chain_load_var'.
            - eassumption.
            - cbn. eapply heq_storev_v_x1_v_m_mid_.
            - assumption.
            - eapply eval_build_loads_offset_non_null_var.
              + eassumption.
              + eassumption.
              + eassumption.
              + exact h_aligned_g_m_. (*xxx instantiate correctly. shelve.*)
              + cbn in heq_transl_name_.
                eapply heq_transl_name_.
              + eassumption.
            - eassumption.
            - eapply eval_expr_transl_variable_inv_locenv ; eauto. }
          specialize (h_invis_sp__m_sp_id_ofs_id_ h_CM_eval_expr_id_t_val_id_t_).
          assumption.
        * unfold is_free_block in *.
          intro abs.
          apply h_neg_free_blck_m_sp_id_ofs_id_.
          intros perm. 
          intro abs2.
          unfold Mem.storev in heq_storev_v_x1_v_m_mid_.
          destruct x1_v; try discriminate.
          eapply Mem.perm_store_1 in abs2;eauto.
          eapply abs;eassumption.
      + unfold forbidden.
        destruct h_forbid_m_mid_m_mid_sp_id_ofs_id_ /sng.
        split.
        * red;intros /sng.
          red in h_invis_sp__m_mid_sp_id_ofs_id_.
          specialize (h_invis_sp__m_mid_sp_id_ofs_id_
                        id id_t id_chk spb_id ofs_id0 h_eq_transl_var_ heq_compute_chnk_id_).
          set (val_id_t:=(Values.Vptr spb_id ofs_id0)) in *;up_type.
          assert (Cminor.eval_expr g sp e_mid m_mid id_t val_id_t) /sng.
          { unfold Mem.storev in heq_storev_v_x1_v_m_mid_.
            destruct x1_v; try discriminate.
            eapply eval_expr_transl_variable_inv_locenv with (locenv:=e_mid);eauto.
            eapply wf_chain_load_var.
            5:eauto.
            2:eauto.
            all:eauto.
            eapply eval_build_loads_offset_non_null_var.
            + eassumption.
            + eassumption.
            + eassumption.
            + exact h_aligned_g_m_. (*xxx instantiate correctly. shelve.*)
            + cbn in heq_transl_name_.
              eapply heq_transl_name_.
            + eassumption. }
          specialize (h_invis_sp__m_mid_sp_id_ofs_id_ h_CM_eval_expr_id_t_val_id_t_).
          assumption.
        * unfold is_free_block in *.
          intro abs.
          apply h_neg_free_blck_m_mid_sp_id_ofs_id_.
          intros perm. 
          intro abs2.
          unfold Mem.storev in heq_storev_v_x1_v_m_mid_.
          destruct x1_v; try discriminate.
          eapply Mem.perm_store_2 in abs2;eauto.
          eapply abs;eassumption. }
Qed.

(* The forbidden addresses (which does not move due to previous lemma)
   are not written during the storing of parameters in local stack. *)

Lemma exec_store_params_unchanged_on_subproof:
  forall lparams st CE initparams,
    CompilEnv.exact_levelG CE ->
    stack_no_null_offset CE ->
    all_addr_no_overflow CE ->
    store_params st CE lparams =: initparams ->
    forall astnum g proc_t sp e_chain m t2 e_postchain m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp -> 
      exec_stmt g proc_t sp e_chain m initparams t2 e_postchain m' Out_normal ->
      Mem.unchanged_on (forbidden st CE g astnum e_chain sp m m) m m'.
Proof.
  intros /sng.
  pose proof (exec_store_params_preserve_forbidden_subproof
                  _ _ _ _ h_exct_lvlG_CE_ h_nonul_ofs_CE_ h_no_overf_CE_
                  heq_store_prms_lparams_initparams_
                  astnum _ proc_t _ _ _ _ _ _ _ heq_length_ h_chain_m_lvl_sp_ h_aligned_g_m_
                  h_exec_stmt_initparams_Out_normal_) /sng.
  decomp h_and_.
  revert initparams h_exct_lvlG_CE_ h_nonul_ofs_CE_ heq_store_prms_lparams_initparams_ astnum g proc_t
         sp e_chain m t2 e_postchain m' lvl heq_length_ h_aligned_g_m_ h_exec_stmt_initparams_Out_normal_
         h_unch_forbid_m_m'_ h_chain_m_lvl_sp_ h_chain_m'_lvl_sp_.
  rew store_params_ok with functional induction function_utils.store_params st CE lparams;
    cbn;!intros;try discriminate /sng.
  - invclear heq_OK_ /sng.
    inversion h_exec_stmt_initparams_Out_normal_;subst.
    apply Mem.unchanged_on_refl.
    (* The three following cases are identical, i.e. the parameter mode
       should not be case split but functional induction does and I don't
       want to make the induction by hand. *)
  - rename x0 into initparams'.
    rename x1 into prm_name_t.
    invclear heq_OK_ /sng.
    invclear h_exec_stmt_initparams_Out_normal_; eq_same_clear /sng.
    assert (stack_localstack_aligned (Datatypes.length CE) e1 g m1 sp) /sng.
    { destruct (parameter_mode prm);simpl in h_exec_stmt_.
      - inversion h_exec_stmt_ /sng.
        destruct prm_name_t_v;try now (cbn in heq_storev_v_m1_; discriminate).
        eapply wf_chain_load_aligned;eauto.
        eapply eval_build_loads_offset_non_null_var;eauto.
      - inversion h_exec_stmt_ /sng.
        assumption.
      - inversion h_exec_stmt_ /sng.
        destruct prm_name_t_v;try now (cbn in heq_storev_v_m1_; discriminate).
        eapply wf_chain_load_aligned;eauto.
        eapply eval_build_loads_offset_non_null_var;eauto. }
    specialize (h_forall_initparams_ _ h_exct_lvlG_CE_ h_nonul_ofs_CE_ heq_store_params_ astnum
                    _ _ _ _ _ _ _ _ _ heq_length_ h_aligned_g_m1_ h_exec_stmt_initparams'_Out_normal_).
    rename m1 into m_mid.
    rename e1 into e_mid.
    (* invclear h_exec_stmt_ /sng. *)
    up_type.
    assert (chained_stack_structure m_mid lvl sp) /sng.
    { destruct (parameter_mode prm);simpl in h_exec_stmt_.
      - invclear h_exec_stmt_ /sng.
        destruct prm_name_t_v eqn:heqstorev;try now (cbn in heq_storev_v_m_mid_; discriminate).
        subst.
        eapply assignment_preserve_chained_stack_structure with (m:=m);eauto.
      - invclear h_exec_stmt_ /sng.
        assumption.
      - invclear h_exec_stmt_ /sng.
        destruct prm_name_t_v eqn:heqstorev;try now (cbn in heq_storev_v_m_mid_; discriminate).
        subst.
        eapply assignment_preserve_chained_stack_structure with (m:=m);eauto. }
    assert (chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_mid e_postchain sp m_mid m') /sng.
    { eapply exec_store_params_preserve_forbidden_subproof;eauto. }
    decomp h_and_.
    assert (unchange_forbidden st CE g astnum e_mid e_mid sp m m_mid) /sng.
    { destruct (parameter_mode prm);simpl in h_exec_stmt_.
      - invclear h_exec_stmt_ /sng.
        eapply unchange_forbidden_trans with (e2:= e_postchain)(m2:=m');eauto.
        apply unchange_forbidden_sym;auto.
      - invclear h_exec_stmt_ /sng.
        eapply unchange_forbidden_trans with (e2:= e_postchain)(m2:=m');eauto.
        apply unchange_forbidden_sym;auto.
      - invclear h_exec_stmt_ /sng.
        eapply unchange_forbidden_trans with (e2:= e_postchain)(m2:=m');eauto.
        apply unchange_forbidden_sym;auto. }
      
    specialize (h_forall_initparams_ h_unch_forbid_m_mid_m'_ h_chain_m_mid_lvl_sp_ h_chain_m'_lvl_sp0_).

    destruct (parameter_mode prm);simpl in h_exec_stmt_.
    { invclear h_exec_stmt_ /sng.
      apply trans_unchanged with m_mid;auto.
      + unfold Mem.storev in heq_storev_v_m_mid_.
        destruct prm_name_t_v;try now discriminate.
        eapply Mem.store_unchanged_on;eauto;intros /sng.
        unfold forbidden.
        intros [abs1 abs2].
        red in abs1.
        cbn in heq_transl_name_.
        setoid_rewrite <- transl_variable_astnum with (a:=astnum) in heq_transl_name_;eauto.
        specialize (abs1 (parameter_name prm) prm_name_t x b i heq_transl_name_ heq_compute_chnk_ h_CM_eval_expr_prm_name_t_prm_name_t_v_).
        destruct abs1; try lia /sng.
      + eapply unchanged_on_iff  ;eauto.
        red; red ; intros;subst /sng.
        eapply h_unch_forbid_m_m_mid_. }
    { invclear h_exec_stmt_ /sng.
      assumption. }
    { invclear h_exec_stmt_ /sng.
      apply trans_unchanged with m_mid;auto.
      + unfold Mem.storev in heq_storev_v_m_mid_.
        destruct prm_name_t_v;try now discriminate.
        eapply Mem.store_unchanged_on;eauto;intros /sng.
        unfold forbidden.
        intros [abs1 abs2].
        red in abs1.
        cbn in heq_transl_name_.
        setoid_rewrite <- transl_variable_astnum with (a:=astnum) in heq_transl_name_;eauto.
        specialize (abs1 (parameter_name prm) prm_name_t x b i heq_transl_name_ heq_compute_chnk_ h_CM_eval_expr_prm_name_t_prm_name_t_v_).
        destruct abs1; try lia /sng.
      + eapply unchanged_on_iff  ;eauto.
        red; red ; intros;subst /sng.
        eapply h_unch_forbid_m_m_mid_. }
Qed.


(* The forbidden *addresses* remain the same when storing values of
   parameters in the local stack.  *)
Lemma exec_init_locals_preserve_forbidden_subproof:
  forall decl st CE locvarinit,
    CompilEnv.exact_levelG CE ->    
    stack_no_null_offset CE ->
    all_addr_no_overflow CE ->
    init_locals st CE decl =: locvarinit ->
    forall astnum g proc_t sp e_chain e_chain' m t2 m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp ->
      exec_stmt g proc_t sp e_chain m locvarinit t2 e_chain' m' Out_normal ->
      chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_chain e_chain' sp m m'.
Proof.
  intros until CE /sng.
  rew init_locals_ok with
    functional induction function_utils.init_locals st CE decl;cbn;
    !!intros;try discriminate;eq_same_clear; up_type;
      split;try now (inversion h_exec_stmt_locvarinit_Out_normal_; try red; try reflexivity;subst;try assumption) /sng.
  - inversion h_exec_stmt_locvarinit_Out_normal_;subst.
    eapply assignment_preserve_chained_stack_structure;eauto.
  - rename x1 into objname_t.
    rename x into chk_objdecl.
    red. 
    intros /sng.
    split.
    + intros /sng.
      unfold forbidden.
      destruct h_forbid_m_m_sp_id_ofs_id_ /sng.
      split.
      * red;intros /sng.
        red in h_neg_free_blck_m_sp_id_ofs_id_.
        specialize (fun spb_id ofs_id0 => h_invis_sp__m_sp_id_ofs_id_
                                            _ _ _ spb_id ofs_id0 h_eq_transl_var_ heq_compute_chnk_id_).
        specialize (h_invis_sp__m_sp_id_ofs_id_ spb_id ofs_id0).
        assert (Cminor.eval_expr g sp e_chain m id_t (Values.Vptr spb_id ofs_id0)) /sng.
        { assert (Cminor.eval_expr g sp e_chain m' id_t (Values.Vptr spb_id ofs_id0)) /sng.
          { eapply eval_expr_transl_variable_inv_locenv;eauto. }
          inversion h_exec_stmt_locvarinit_Out_normal_;subst /sng.
          destruct objname_t_v;try discriminate.
          eapply wf_chain_load_var';auto;eauto.
          functional inversion heq_transl_name_;subst /sng.
          functional inversion heq_transl_variable0_;subst /sng.
          pose proof (h_nonul_ofs_CE_ _ _ heq_CEfetchG_) /sng.
          assert (chained_stack_structure m (m'0 - m0) sp) /sng.
          { 
            (*rewrite heq_lvloftop_CE_lvl_ in heq_lvloftop_CE_m'0_.*)
(*             inversion heq_lvloftop_CE_m'0_;subst. *)
            eapply chained_stack_structure_le;eauto.
            assert (Datatypes.length CE = (S m'0)) by (eapply exact_level_top_lvl;eauto) /sng.
            rewrite heq_length_.
            lia. }
          red in h_no_overf_CE_.
          specialize h_no_overf_CE_ with (1:= heq_CEfetchG_).
          
          
          assert (n mod Int.modulus = n) /sng.
          { apply Z.mod_small.
            assumption. }
          specialize chain_struct_build_loads_ofs with (1:=h_chain_m_) (2:=heq_modulo_)
                                                       (3:=h_CM_eval_expr_objname_t_objname_t_v_);intro /sng.
          (* pose proof (chain_struct_build_loads_ofs _ _ _ h_chain_sp_ n _ _ _ _ h_CM_eval_expr_objname_t_objname_t_v_) . *)

          subst.
          rewrite Ptrofs.unsigned_repr;auto.
          unfold Ptrofs.max_unsigned.
          lia. }
        specialize (h_invis_sp__m_sp_id_ofs_id_ h_CM_eval_expr_id_t0_).
        assumption.

      * unfold is_free_block in *.
        inversion h_exec_stmt_locvarinit_Out_normal_ /sng.
        destruct objname_t_v;try discriminate.
        unfold Mem.storev in heq_storev_e_t_v_m'_.
        intro abs.
        apply h_neg_free_blck_m_sp_id_ofs_id_.
        intros perm. 
        intro abs2.
        apply (Mem.perm_store_1 _ _ _ _ _ _ heq_storev_e_t_v_m'_) in abs2.
        specialize (abs perm);contradiction.
    + intros /sng.
      unfold forbidden.
      destruct h_forbid_m'_m'_sp_id_ofs_id_ /sng.
      split.
      * red;intros /sng.
        red in h_invis_sp__m'_sp_id_ofs_id_.
        specialize (fun spb_id ofs_id0 => h_invis_sp__m'_sp_id_ofs_id_ _ _ _ spb_id ofs_id0 h_eq_transl_var_ heq_compute_chnk_id_).
        specialize (h_invis_sp__m'_sp_id_ofs_id_ spb_id ofs_id0).
        assert (Cminor.eval_expr g sp e_chain' m' id_t (Values.Vptr spb_id ofs_id0)) /sng.
        { assert (Cminor.eval_expr g sp e_chain' m id_t (Values.Vptr spb_id ofs_id0)) /sng.
          { eapply eval_expr_transl_variable_inv_locenv;eauto. }
          inversion h_exec_stmt_locvarinit_Out_normal_;subst /sng.
          destruct objname_t_v;try discriminate.
          assert (4 <= Ptrofs.unsigned i).
          { functional inversion heq_transl_name_;subst /sng.
            functional inversion heq_transl_variable0_;subst /sng.
            pose proof (h_nonul_ofs_CE_ _ _ heq_CEfetchG_) /sng.
            assert (chained_stack_structure m (m'0 - m0) sp) /sng.
            { eapply chained_stack_structure_le;eauto.
              assert (Datatypes.length CE = (S m'0)) by (eapply exact_level_top_lvl;eauto) /sng.
              rewrite heq_length_.
              lia. }
          red in h_no_overf_CE_.
          specialize h_no_overf_CE_ with (1:= heq_CEfetchG_).
          assert (n mod Int.modulus = n) /sng.
          { apply Z.mod_small.
            assumption. }
          specialize chain_struct_build_loads_ofs with (1:=h_chain_m_) (2:=heq_modulo_)
                                                       (3:=h_CM_eval_expr_objname_t_objname_t_v_);intro /sng.

            subst.
            rewrite Ptrofs.unsigned_repr;auto.
            unfold Ptrofs.max_unsigned.
            lia. }
          eapply wf_chain_load_var;auto;eauto.
          -- eapply wf_chain_load_aligned;eauto. }
        specialize (h_invis_sp__m'_sp_id_ofs_id_ h_CM_eval_expr_id_t0_).
        assumption. 
      * unfold is_free_block in *.
        inversion h_exec_stmt_locvarinit_Out_normal_ /sng.
        destruct objname_t_v;try discriminate.
        unfold Mem.storev in heq_storev_e_t_v_m'_.
        intro abs.
        apply h_neg_free_blck_m'_sp_id_ofs_id_.
        intros perm. 
        intro abs2.
        apply (Mem.perm_store_2 _ _ _ _ _ _ heq_storev_e_t_v_m'_) in abs2.
        specialize (abs perm);contradiction.
  - inversion h_exec_stmt_locvarinit_Out_normal_ /sng.
    + eapply h_forall_locvarinit0_ with (m:=m1);eauto.
      * eapply h_forall_locvarinit_;eauto.
      * eapply chain_aligned;eauto.
        subst.
        eapply h_forall_locvarinit_;eauto.
    + elim hneq_Out_normal;auto.
  - inversion h_exec_stmt_locvarinit_Out_normal_ /sng.
    + rename m1 into m_mid.
      rename e1 into e_mid.
      apply unchange_forbidden_trans with (e2:=e_mid) (m2:=m_mid).
      * eapply h_forall_locvarinit_ with (locvarinit:=x);eauto.
      * eapply h_forall_locvarinit0_ with (locvarinit:=x0);eauto.
      -- eapply h_forall_locvarinit_;eauto.
      -- eapply chain_aligned;eauto.
         subst.
         eapply h_forall_locvarinit_;eauto.
    + elim hneq_Out_normal;auto.
Qed.

Lemma init_locals_unchanged_on_subproof:
  forall decl st CE locvarinit,
    CompilEnv.exact_levelG CE ->
    all_addr_no_overflow CE ->
    stack_no_null_offset CE ->
    init_locals st CE decl =: locvarinit ->
    forall astnum g proc_t sp e_chain m t2 e_postchain m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp -> 
      exec_stmt g proc_t sp e_chain m locvarinit t2 e_postchain m' Out_normal ->
      Mem.unchanged_on (forbidden st CE g astnum e_chain sp m m) m m'.
Proof.
  intros /sng.
  up_type.
  specialize exec_init_locals_preserve_forbidden_subproof
    with (astnum:=astnum)
      (1:=h_exct_lvlG_CE_) (2:=h_nonul_ofs_CE_) (3:=h_no_overf_CE_) 
         (4:=heq_init_lcl_decl_locvarinit_)
         (5:=heq_length_) (6:=h_chain_m_lvl_sp_) (7:=h_aligned_g_m_)
         (8:=h_exec_stmt_locvarinit_Out_normal_).
  intro /sng.
  decomp h_and_.
  revert locvarinit h_exct_lvlG_CE_ h_nonul_ofs_CE_ heq_init_lcl_decl_locvarinit_ astnum g proc_t sp
         e_chain m t2 e_postchain m' h_aligned_g_m_ lvl heq_length_ h_exec_stmt_locvarinit_Out_normal_
         h_unch_forbid_m_m'_ h_chain_m_lvl_sp_ h_chain_m'_lvl_sp_.
  rew init_locals_ok with
    functional induction function_utils.init_locals st CE decl;cbn;!intros;try discriminate /sng.
  - invclear heq_OK_; inversion h_exec_stmt_locvarinit_Out_normal_;subst /sng. apply Mem.unchanged_on_refl.
  - invclear heq_OK_; inversion h_exec_stmt_locvarinit_Out_normal_;subst; apply Mem.unchanged_on_refl /sng.
  - rename x1 into objname_t.
    rename x into chk_objdecl.
    invclear heq_OK_ /sng.
    invclear h_exec_stmt_locvarinit_Out_normal_; eq_same_clear;up_type /sng.
    unfold Mem.storev in heq_storev_e_t_v_m'_.
    destruct objname_t_v ;try now discriminate.
    eapply Mem.store_unchanged_on;eauto;intros /sng.
    unfold forbidden.
    intros [abs1 abs2].
    red in abs1.
    cbn in heq_transl_name_.
    setoid_rewrite <- transl_variable_astnum with (a:=astnum) in heq_transl_name_;eauto.
    specialize (abs1 (object_name objdecl) objname_t chk_objdecl b i heq_transl_name_ heq_compute_chnk_ h_CM_eval_expr_objname_t_objname_t_v_).
    destruct abs1;try lia /sng.
  - invclear heq_OK_; inversion h_exec_stmt_locvarinit_Out_normal_;subst; apply Mem.unchanged_on_refl /sng.
  - invclear h_exec_stmt_locvarinit_Out_normal_; eq_same_clear;up_type /sng.
    apply Mem.unchanged_on_refl.    
  - rename x into stmt1.
    rename x0 into stmt2.
    invclear heq_OK_ /sng.
    invclear h_exec_stmt_locvarinit_Out_normal_; eq_same_clear;up_type /sng.
    rename m1 into m_mid.
    rename e1 into e_mid.
    assert (chained_stack_structure m_mid lvl sp ∧ unchange_forbidden st CE g astnum e_chain e_mid sp m m_mid) /sng.
    { eapply exec_init_locals_preserve_forbidden_subproof with (locvarinit:=stmt1);eauto. }
    decomp h_and_.
    assert (chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_mid e_postchain sp m_mid m') /sng.
    { eapply exec_init_locals_preserve_forbidden_subproof with (locvarinit:=stmt2);eauto.
      eapply chain_aligned;eauto.
      lia. }
    decomp h_and_.
    apply trans_unchanged with m_mid;auto.
    + eapply h_forall_locvarinit_;eauto.
    + assert (Mem.unchanged_on (forbidden st CE g astnum e_mid sp m_mid m_mid) m_mid m').
      { eapply h_forall_locvarinit0_ with (locvarinit:= stmt2);eauto.
        eapply chain_aligned;eauto.
        lia. }
      red in h_unch_forbid_m_m_mid_.
      eapply unchanged_on_iff;eauto.
       (red;intros);(red;!intros) /sng.
      subst.
      apply h_unch_forbid_m_m_mid_.
Qed.



Lemma init_params_preserves_structure:
  forall lparams st CE initparams,
    CompilEnv.exact_levelG CE ->
    stack_no_null_offset CE ->
    all_addr_no_overflow CE ->
    store_params st CE lparams =: initparams ->
    forall astnum g proc_t sp e_chain m t2 e_chain' m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp -> 
      exec_stmt g proc_t sp e_chain m initparams t2 e_chain' m' Out_normal ->
      Mem.unchanged_on (forbidden st CE g astnum e_chain sp m m) m m'
      ∧ chained_stack_structure m' lvl sp
      ∧ unchange_forbidden st CE g astnum e_chain e_chain' sp m m'.
Proof.
  split.
  - eapply exec_store_params_unchanged_on_subproof;eauto.
  - eapply exec_store_params_preserve_forbidden_subproof;eauto.
Qed.

Lemma init_locals_preserves_structure:
  forall decl st CE locvarinit,
    CompilEnv.exact_levelG CE ->
    stack_no_null_offset CE ->
    all_addr_no_overflow CE ->
    init_locals st CE decl =: locvarinit ->
    forall astnum g proc_t sp e_chain m t2 e_chain' m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp -> 
      exec_stmt g proc_t sp e_chain m locvarinit t2 e_chain' m' Out_normal ->
      Mem.unchanged_on (forbidden st CE g astnum e_chain sp m m) m m'
      ∧ chained_stack_structure m' lvl sp
      ∧ unchange_forbidden st CE g astnum e_chain e_chain' sp m m'.
Proof.
  split.
  - eapply init_locals_unchanged_on_subproof;eauto.
  - eapply exec_init_locals_preserve_forbidden_subproof;eauto.
Qed.

Lemma build_compilenv_exact_lvl:
  forall st CE proc_lvl lparams decl CE' sz,
    CompilEnv.exact_levelG CE ->
    build_compilenv st CE proc_lvl lparams decl =: (CE',sz) ->
    CompilEnv.exact_levelG CE'.
Proof.
  intros /sng.
  rew build_compilenv_ok with functional inversion heq_build_compilenv_.
  unfold stoszchainparam in *.
  simpl in *.
  constructor;auto.
Qed.  



Lemma compute_size_pos : forall st subtyp_mrk x, spark2Cminor.compute_size st subtyp_mrk =: x -> (x>0).
Proof.
  intros /sng.
  rew compute_size_ok with functional inversion heq_cmpt_size_subtyp_mrk_ /sng.
  apply size_chunk_pos.
Qed.

(* Lemma compute_size_pos stbl t : forall x, compute_size stbl t =: x -> x > 0.
Proof.
  intros /sng.
  unfold compute_size in *.
  (* functional inbversion would be better *)
  destruct (compute_chnk_of_type stbl t); cbv in  *;try discriminate.
  destruct m;cbv in *;try inversion heq_cmpt_size_t_;auto.
Qed.
 *)

(* build_frame_lparams return a non overflowed store, but the size may = to Int.modulus.
   So that next addition will overflow *)
Lemma build_frame_lparams_mon: forall st stosz lparams sto' sz',
    build_frame_lparams st stosz lparams =: (sto',sz') ->
    snd stosz<=sz'
    /\
    (forall stoszchainparam sz,
        stosz = (stoszchainparam,sz) -> 
        (* k is the lesser bound of addresses (typically 4 to let room for the chaining arg *)
        forall k,
          (forall nme x, CompilEnv.fetches nme stoszchainparam = Some x
                         -> k <= x <Int.modulus) -> 
          k <= sz < Int.modulus -> 
          forall nme v,
            CompilEnv.fetches nme sto' = Some v ->
            k <= v < Int.modulus).
Proof.
  intros until lparams /sng.
  functional induction (function_utils.build_frame_lparams st stosz lparams);cbn;!intros;subst /sng.
  - invclear heq_OK_ /sng.
    split;intros /sng.
    + cbn. reflexivity.
    + inversion heq_pair_;subst;eauto 5.
  - rewrite heq_add_to_fr_nme_ in heq_bind_.
    cbn [bind] in *.
    specialize (h_forall_sto'_ _ _ heq_bind_).
    rew function_utils.add_to_frame_ok with functional inversion heq_add_to_fr_nme_;subst;cbn /sng.
    cbn in h_forall_sto'_.
    destruct h_forall_sto'_ as [IHr1 IHr3].
    subst new_size.
    subst new_cenv.
    split.
    + assert (x0>0) by (eapply compute_size_pos;eauto) /sng.
      lia.
    + intros /sng.
      inversion heq_pair_;subst.
      specialize (IHr3 ((nme, sz0) :: stoszchainparam) (sz0 + x0) eq_refl k).
      apply IHr3 with (nme:=nme0);auto.
      * intros /sng.
        cbn in heq_CEfetches_nme1_.
        destruct (nme1 =? nme)%nat.
        -- invclear heq_CEfetches_nme1_;auto /sng.
        -- inversion heq_pair_;subst;eauto.
      * assert (x0>0) by (eapply compute_size_pos;eauto) /sng.
        split; try lia.
        rewrite Z.geb_leb in heq_geb_.
        apply Z.leb_gt.
        assumption.
  - rewrite heq_add_to_fr_ERR_nme_ in heq_bind_.
    cbn in heq_bind_.
    discriminate.
Qed.

Lemma build_frame_lparams_mon'': forall st stosz lparams sto' sz',
    build_frame_lparams st stosz lparams =: (sto',sz') ->
    snd stosz <= Ptrofs.modulus -> 
    sz' <= Ptrofs.modulus.
Proof.
  intros until lparams /sng.
  functional induction (function_utils.build_frame_lparams st stosz lparams);cbn;!intros;subst /sng.
  - invclear heq_OK_ /sng.
    cbn in *.
    assumption.
  - rewrite heq_add_to_fr_nme_ in heq_bind_.
    cbn [bind] in *.
    specialize (h_forall_sto'_ _ _ heq_bind_).
    rew function_utils.add_to_frame_ok with functional inversion heq_add_to_fr_nme_;subst;cbn /sng.
    subst new_size.
    subst new_cenv.
    cbn in h_forall_sto'_.
    apply h_forall_sto'_.
    rewrite Z.geb_leb in heq_geb_.
    apply Z.leb_gt in heq_geb_.
    lia.
  - rewrite heq_add_to_fr_ERR_nme_ in heq_bind_.
    cbn in heq_bind_.
    discriminate.
Qed.
(* build_frame_lparams return a non overflowed store, but the size may = to Int.modulus.
   So that next addition will overflow *)
Lemma build_frame_lparams_mon': forall st stosz lparams sto' sz',
    build_frame_lparams st stosz lparams =: (sto',sz') ->
    snd stosz <= Ptrofs.modulus -> 
    snd stosz<=sz'<= Ptrofs.modulus
    /\
    (forall stoszchainparam sz,
        stosz = (stoszchainparam,sz) -> 
        (* k is the lesser bound of addresses (typically 4 to let room for the chaining arg *)
        forall k,
          (forall nme x, CompilEnv.fetches nme stoszchainparam = Some x -> k <= x < sz) -> 
          k <= sz -> 
          forall nme v,
            CompilEnv.fetches nme sto' = Some v ->
            k <= v < sz').
Proof.
  intros until lparams /sng.
  functional induction (function_utils.build_frame_lparams st stosz lparams);cbn;!intros;subst /sng.
  - invclear heq_OK_ /sng.
    split;[split|intros] /sng.
    + cbn. reflexivity.
    + cbn in *.
      assumption.
    + inversion heq_pair_;subst;eauto 5.
  - rewrite heq_add_to_fr_nme_ in heq_bind_.
    cbn [bind] in *.
    specialize (h_forall_sto'_ _ _ heq_bind_).
    rew function_utils.add_to_frame_ok with functional inversion heq_add_to_fr_nme_;subst;cbn /sng.
    assert (x0 >0) /sng.
    { eapply compute_size_pos;eauto. }
    cbn in h_forall_sto'_.
    assert (new_size <= Ptrofs.modulus) /sng.
    { rewrite Z.geb_leb in heq_geb_.
      apply Z.leb_gt in heq_geb_.
      lia. }
    specialize (h_forall_sto'_ h_le_new_size_modulus_).
    destruct h_forall_sto'_ as [[IHr1IHr2] IHr3].
    subst new_size.
    subst new_cenv.
    split;[split|intros] /sng.
    + lia.
    + assumption.
    + inversion heq_pair_;subst.
      specialize (IHr3 ((nme, sz0) :: stoszchainparam) (sz0 + x0) eq_refl k).
      apply IHr3 with (nme:=nme0);auto.
      * intros /sng.
        cbn in heq_CEfetches_nme1_.
        destruct (nme1 =? nme)%nat.
        -- invclear heq_CEfetches_nme1_;split;auto /sng.
           lia.
        -- specialize (h_forall_nme_ nme1 x heq_CEfetches_nme1_).
           destruct h_forall_nme_;auto /sng.
           split;auto.
           lia.
      * lia.
  - rewrite heq_add_to_fr_ERR_nme_ in heq_bind_.
    cbn in heq_bind_.
    discriminate.
Qed.

Lemma build_frame_decl_mon_sz: forall st decl stosz stosz',
    build_frame_decl st stosz decl =: stosz' -> 
    snd stosz <= snd stosz'.
Proof.
  intros until stosz /sng.
  rew build_frame_decl_ok
  with functional induction (function_utils.build_frame_decl st stosz decl);!!intros ;try discriminate /sng.
  - inversion heq_OK_;reflexivity.
  - invclear heq_OK_ /sng.
    cbn.
    pose proof compute_size_pos _ _ _ heq_cmpt_size_ /sng.
    lia.
  - specialize (h_forall_stosz'0_ _ heq_build_frame_decl0_).
    specialize (h_forall_stosz'_ _ heq_build_frame_decl_).
    etransitivity;eauto.
Qed.

Lemma build_frame_decl_mon: forall st stosz lparams sto' sz',
    spark2Cminor.build_frame_decl st stosz lparams =: (sto',sz') ->
    snd stosz <= Ptrofs.modulus -> 
    snd stosz<=sz'<= Ptrofs.modulus
    /\
    (forall stoszchainparam sz,
        stosz = (stoszchainparam,sz) -> 
        (* k is the lesser bound of addresses (typically 4 to let room for the chaining arg *)
        forall k,
          (forall nme x, CompilEnv.fetches nme stoszchainparam = Some x -> k <= x < sz) ->  
          k <= sz -> 
          forall nme v,
            CompilEnv.fetches nme sto' = Some v ->
            k <= v < sz').
Proof.
  intros until lparams /sng.
  rew build_frame_decl_ok
  with functional induction (function_utils.build_frame_decl st stosz lparams);!!intros ;try discriminate /sng.
  - split;[split|].
    + inversion heq_OK_;reflexivity.
    + inversion heq_OK_;cbn in *;lia.
    + invclear heq_OK_;subst;cbn in * /sng.
      intros /sng.
      invclear heq_pair_ /sng.
      eauto.
  - pose proof compute_size_pos _ _ _ heq_cmpt_size_ /sng.
    split;[split|].
    + invclear heq_OK_ /sng.
      cbn.
      lia.
    + invclear heq_OK_;cbn in * /sng.
      destruct (Z.geb_spec (sz + x) Ptrofs.modulus);try discriminate;lia.
    + invclear heq_OK_;subst;cbn in * /sng.
      intros /sng.
      invclear heq_pair_ /sng.
      destruct (Nat.eqb_spec nme (object_name objdecl));subst /sng.
      * invclear heq_Some_ /sng.
        lia.
      * specialize (h_forall_nme_ _ _ heq_Some_).
        lia.
  - destruct x.
    specialize (h_forall_sto'_ _ _ heq_build_frame_decl_ h_le_).
    decomp h_forall_sto'_.
    rename h_forall_stoszchainparam_ into IHr_3.
    specialize (h_forall_sto'0_ _ _ heq_build_frame_decl0_ h_le_z_modulus_).
    decomp h_forall_sto'0_.
    rename h_forall_stoszchainparam_ into IHr0_3.
    split;[split|].
    + cbn in *;lia.
    + assumption.
    + intros /sng.
      rename h_forall_nme_ into h_lelt_.
      invclear heq_pair_;subst /sng.
      cbn in*.
      specialize (IHr_3 _ _ eq_refl _ h_lelt_ h_le_k_sz0_).
      rename z into sz.
      assert (k<=sz) by lia /sng.
      specialize (IHr0_3 _ _ eq_refl k IHr_3 h_le_k_sz_ _ _ heq_CEfetches_nme_sto'_).
      assumption.
Qed.

(* Too much hyps. *)
Lemma transl_variable_cons':
  forall st (scope_lvl:scope_level) x0 CE a nme  δ_lvl δ_id (*sz'*) (*lparams*),
    all_addr_no_overflow ((scope_lvl, x0) :: CE) ->
    CompilEnv.exact_levelG ((scope_lvl, x0) :: CE) ->
    0 <= δ_id -> δ_id < Int.modulus ->
    transl_variable st ((scope_lvl, x0) :: CE) a nme =: build_loads δ_lvl δ_id ->
    (transl_variable st ((scope_lvl, x0)::nil) a nme =: build_loads δ_lvl δ_id)
    ∧ δ_lvl= 0%nat
    ∨ (transl_variable st CE a nme =: build_loads (δ_lvl-1) δ_id).
Proof.
  intros /sng.
  functional inversion h_eq_transl_var_;clear h_eq_transl_var_ /sng.
  red in h_no_overf_.
  specialize h_no_overf_ with (1:=heq_CEfetchG_nme_) as h'.
  decomp h'.
  assert (Int.Z_mod_modulus δ_nme = Int.Z_mod_modulus δ_id) /sng.
  { (* convertible even if unfolding problem *)
    exact heq.  }
  clear heq.    
  rewrite Int.Z_mod_modulus_eq in heq_Z_mod_modulus_.
  rewrite Int.Z_mod_modulus_eq in heq_Z_mod_modulus_.
  rewrite Zmod_small in heq_Z_mod_modulus_;auto.
  rewrite Zmod_small in heq_Z_mod_modulus_;auto.
  subst.
  clear h_lt_δ_nme_modulus_ h_le_Z0_δ_nme_.
  functional inversion heq_CEfetchG_nme_; clear heq_CEfetchG_nme_;subst /sng.
  - unfold CompilEnv.fetch in heq_CEfetch_nme_.
    simpl in heq_CEfetch_nme_.
    left.
    unfold transl_variable.
    cbn.
    rewrite heq_CEfetch_nme_.
    erewrite CompilEnv.fetches_ok;eauto.
    cbn in heq_lvloftop_m'_.
    inversion heq_lvloftop_m'_;subst;clear heq_lvloftop_m'_.
    cbn in heq_CEframeG_nme_.
    erewrite CompilEnv.fetches_ok in heq_CEframeG_nme_;eauto.
    inversion heq_CEframeG_nme_;subst;clear heq_CEframeG_nme_.
    specialize build_loads__inj with (1:=heq_build_loads_);intro /sng.
    subst.
    split;auto with arith.
  - unfold CompilEnv.fetch in heq_CEfetch_nme_.
    simpl in heq_CEfetch_nme_.
    right.
    unfold transl_variable.
    cbn.
    rewrite heq_CEfetchG_nme_CE_.
    functional inversion heq_CEframeG_nme_ /sng.
    + exfalso.
      subst.
      unfold CompilEnv.reside in heq_reside_.
      apply CompilEnv.fetches_ok_none_1 in heq_CEfetch_nme_.
      cbn in heq_reside_.
      rewrite heq_CEfetch_nme_ in heq_reside_.
      discriminate.
    + subst.
      rewrite heq_CEframeG_nme_CE_.
      assert (CompilEnv.exact_levelG CE) /sng.
      { eapply CompilEnv.exact_levelG_sublist;eauto. }
      specialize CompilEnv.exact_lvl_lvl_of_top  with (1:=h_exct_lvlG_) (2:=heq_lvloftop_m'_);intro h_top_.
      cbn in h_top_.
      inversion h_top_ /sng.
      destruct CE.
      -- discriminate.
      -- cbn. destruct p.
         specialize build_loads__inj with (1:=heq_build_loads_);intro;subst /sng.
         erewrite exact_level_top_lvl;auto.
         all: swap 2 1.
         ++ cbn.
            reflexivity.
         ++ assert (s - lvl_nme = S s - lvl_nme - 1)%nat by lia /sng.
            rewrite heq_sub_;reflexivity.
Qed.

(* Too much hyps. *)
Lemma transl_variable_cons'':
  forall st (scope_lvl:scope_level) x0 CE a nme  δ_lvl δ_id (*sz'*) (*lparams*),
    all_addr_no_overflow ((scope_lvl, x0) :: CE) ->
    CompilEnv.exact_levelG ((scope_lvl, x0) :: CE) ->
    transl_variable st ((scope_lvl, x0) :: CE) a nme =: build_loads δ_lvl δ_id ->
    exists δ_id',
           eqm Int.modulus δ_id δ_id' ∧
           ((transl_variable st ((scope_lvl, x0)::nil) a nme =: build_loads δ_lvl δ_id')
            ∧ δ_lvl= 0%nat
              ∨ (transl_variable st CE a nme =: build_loads (δ_lvl-1) δ_id')).
Proof.
  intros /sng.
  functional inversion h_eq_transl_var_;clear h_eq_transl_var_ /sng.
  red in h_no_overf_.
  specialize h_no_overf_ with (1:=heq_CEfetchG_nme_) as h'.
  decomp h'.
  assert (Int.Z_mod_modulus δ_nme = Int.Z_mod_modulus δ_id) /sng.
  { (* convertible even if unfolding problem *)
    exact heq.  }
  clear heq.    
  rewrite Int.Z_mod_modulus_eq in heq_Z_mod_modulus_.
  rewrite Int.Z_mod_modulus_eq in heq_Z_mod_modulus_.
  rewrite Zmod_small in heq_Z_mod_modulus_;auto.
  (* rewrite Zmod_small in heq_Z_mod_modulus_;auto. *)
  subst.
  clear h_lt_δ_nme_modulus_ h_le_Z0_δ_nme_.
  functional inversion heq_CEfetchG_nme_; clear heq_CEfetchG_nme_;subst /sng.
  - unfold CompilEnv.fetch in heq_CEfetch_nme_.
    simpl in heq_CEfetch_nme_.
    (* left. *)
    unfold transl_variable.
    cbn.
    rewrite heq_CEfetch_nme_.
    erewrite CompilEnv.fetches_ok;eauto.
    cbn in heq_lvloftop_m'_.
    inversion heq_lvloftop_m'_;subst;clear heq_lvloftop_m'_.
    cbn in heq_CEframeG_nme_.
    erewrite CompilEnv.fetches_ok in heq_CEframeG_nme_;eauto.
    inversion heq_CEframeG_nme_;subst;clear heq_CEframeG_nme_.
    specialize build_loads__inj with (1:=heq_build_loads_);intro /sng.
    subst.
    exists (δ_id mod Int.modulus).
    split.
    + symmetry.
      apply Zmod_eqm.
    + left;split.
      * reflexivity.
      * auto with arith.
  - unfold CompilEnv.fetch in heq_CEfetch_nme_.
    simpl in heq_CEfetch_nme_.
    (* right. *)
    unfold transl_variable.
    cbn.
    rewrite heq_CEfetchG_nme_CE_.
    functional inversion heq_CEframeG_nme_ /sng.
    + exfalso.
      subst.
      unfold CompilEnv.reside in heq_reside_.
      apply CompilEnv.fetches_ok_none_1 in heq_CEfetch_nme_.
      cbn in heq_reside_.
      rewrite heq_CEfetch_nme_ in heq_reside_.
      discriminate.
    + subst.
      rewrite heq_CEframeG_nme_CE_.
      assert (CompilEnv.exact_levelG CE) /sng.
      { eapply CompilEnv.exact_levelG_sublist;eauto. }
      specialize CompilEnv.exact_lvl_lvl_of_top with (1:=h_exct_lvlG_) (2:=heq_lvloftop_m'_);intro h_top_.
      cbn in h_top_.
      inversion h_top_ /sng.
      destruct CE.
      -- discriminate.
      -- cbn. destruct p.
         specialize build_loads__inj with (1:=heq_build_loads_);intro;subst /sng.
         erewrite exact_level_top_lvl;auto.
         all: swap 2 1.
         ++ cbn.
            reflexivity.
         ++ assert (s - lvl_nme = S s - lvl_nme - 1)%nat by lia /sng.
            exists (δ_id mod Int.modulus);split.
            ** symmetry.
               apply Zmod_eqm.
            ** right.
               rewrite heq_sub_;reflexivity.
Qed.

Lemma build_frame_lparams_no_null_offset:
  forall stbl stosz lparams sto sz sto' sz',
    build_frame_lparams stbl stosz lparams =: (sto',sz')->
    stosz =(sto,sz) ->
    forall n,
      sz >= n ->
      (forall nme δ_nme,
          CompilEnv.fetches nme sto = Some δ_nme ->
          n <= δ_nme) ->
      forall nme δ_nme,
        CompilEnv.fetches nme sto' = Some δ_nme ->
        n <= δ_nme.
Proof.
  intros stbl stosz lparams.
  rew build_frame_lparams_ok with
    functional induction function_utils.build_frame_lparams stbl stosz lparams;try discriminate;
    simpl;!!intros;subst /sng.
  - inversion heq_OK_;subst.
    eauto.
  - rew add_to_frame_ok with
      functional inversion heq_add_to_fr_nme_ /sng.
    clear heq_add_to_fr_nme_.
    subst new_size.
    subst new_cenv.
    specialize h_forall_sto_ with (1:=heq_build_frame_lparams_)(2:=eq_refl)
                        (5:=heq_CEfetches_nme0_sto'_)(n:=n).
    eapply h_forall_sto_;clear h_forall_sto_.
    assert (x0>0).
    { eapply compute_size_pos;eauto. }
    lia.
    intros /sng.
    cbn in heq_CEfetches_nme1_.
    up_type.
    destruct ((nme1 =? nme)%nat) /sng.
    + invclear heq_CEfetches_nme1_ /sng.
      lia.
    + eauto.
Qed.


Lemma build_frame_decl_no_null_offset:
  forall stbl stosz decl sto sz stosz' sto' sz',
    build_frame_decl stbl stosz decl =: stosz' ->
    stosz' = (sto',sz') -> 
    stosz =(sto,sz) ->
    forall n,
      sz >= n ->
      (forall nme δ_nme,
          CompilEnv.fetches nme sto = Some δ_nme ->
          n <= δ_nme) ->
      forall nme δ_nme,
        CompilEnv.fetches nme sto' = Some δ_nme ->
        n <= δ_nme.
Proof.
  intros stbl stosz decl.
  rew build_frame_decl_ok with
    functional induction function_utils.build_frame_decl stbl
    stosz decl;try discriminate;
    try rewrite <- build_frame_decl_ok in * ;simpl;!intros;subst /sng.
  - inversion heq_OK_;subst.
    inversion heq_pair_;subst.
    eauto.
  - invclear heq_OK_ /sng.
    invclear heq_pair_ /sng.
    functional inversion heq_CEfetches_nme_sto'_;subst /sng.
    + lia.
    + eapply h_forall_nme_;eauto.
  - invclear heq_pair_ /sng.
    destruct x.
    specialize h_forall_sto_ with (1:=heq_build_frame_decl_) (2:=eq_refl)(3:=eq_refl) (4:=h_ge_sz0_n_)(5:=h_forall_nme_).
    specialize h_forall_sto0_ with (1:=heq_build_frame_decl0_)(2:=eq_refl)(3:=eq_refl)(5:=h_forall_sto_).
    eapply h_forall_sto0_;eauto.
    apply Zge_trans with sz0;auto.          
    specialize build_frame_decl_mon_sz with (1:=heq_build_frame_decl_).
    cbn.
    lia.
Qed.

Lemma build_compilenv_no_null_offset:
  forall st CE proc_lvl lparams decl lvl sto sz,
    build_compilenv st CE proc_lvl lparams decl =: ((lvl,sto) :: CE, sz) ->
    forall nme δ_nme,
      CompilEnv.fetches nme sto = Some δ_nme ->
      4 <= δ_nme.
Proof.
  intros /sng.
  rew build_compilenv_ok with
    functional inversion heq_build_compilenv_ /sng.
  subst stoszchainparam.
  up_type.
  clear heq_build_compilenv_.
  destruct x.
  eapply build_frame_decl_no_null_offset with (1:=heq_build_frame_decl_);eauto.
  - specialize build_frame_lparams_mon with (1:=heq_bld_frm_lparams_).
    intro /sng.
    decomp h_and_.
    cbn in h_le_.
    lia.
  - intros /sng.
    eapply build_frame_lparams_no_null_offset;eauto.
    + lia.
    + intros /sng.
      functional inversion heq_CEfetches_nme1_.
Qed.

(* Too much hyps. *)
(*
Lemma transl_variable_cons:
  forall st (scope_lvl:scope_level) x0 CE a nme  δ_lvl δ_id (*sz'*) (*lparams*),
    all_addr_no_overflow ((scope_lvl, x0) :: CE) ->
    CompilEnv.exact_levelG ((scope_lvl, x0) :: CE) ->
    transl_variable st ((scope_lvl, x0) :: CE) a nme =: build_loads δ_lvl δ_id ->
           ((transl_variable st ((scope_lvl, x0)::nil) a nme =: build_loads δ_lvl δ_id)
            ∧ δ_lvl= 0%nat
              ∨ (transl_variable st CE a nme =: build_loads (δ_lvl-1) δ_id)).
Proof.
  intros /sng.
  functional inversion h_eq_transl_var_;clear h_eq_transl_var_ /sng.
  red in h_no_overf_.
  specialize h_no_overf_ with (1:=heq_CEfetchG_nme_) as h'.
  decomp h'.
  assert (Int.Z_mod_modulus δ_nme = Int.Z_mod_modulus δ_id) /sng.
  { (* convertible even if unfolding problem *)
    exact heq.  }
  clear heq.    
  rewrite Int.Z_mod_modulus_eq in heq_Z_mod_modulus_.
  rewrite Int.Z_mod_modulus_eq in heq_Z_mod_modulus_.
  rewrite Zmod_small in heq_Z_mod_modulus_;auto.
  (* rewrite Zmod_small in heq_Z_mod_modulus_;auto. *)
  subst.
  clear h_lt_δ_nme_modulus_ h_le_Z0_δ_nme_.
  functional inversion heq_CEfetchG_nme_; clear heq_CEfetchG_nme_;subst /sng.
  - unfold CompilEnv.fetch in heq_CEfetch_nme_.
    simpl in heq_CEfetch_nme_.
    (* left. *)
    unfold transl_variable.
    cbn.
    rewrite heq_CEfetch_nme_.
    erewrite CompilEnv.fetches_ok;eauto.
    cbn in heq_lvloftop_m'_.
    inversion heq_lvloftop_m'_;subst;clear heq_lvloftop_m'_.
    cbn in heq_CEframeG_nme_.
    erewrite CompilEnv.fetches_ok in heq_CEframeG_nme_;eauto.
    inversion heq_CEframeG_nme_;subst;clear heq_CEframeG_nme_.
    specialize build_loads__inj with (1:=heq_build_loads_);intro /sng.
    subst.
    left;split.
    * reflexivity.
    * auto with arith.
  - unfold CompilEnv.fetch in heq_CEfetch_nme_.
    simpl in heq_CEfetch_nme_.
    (* right. *)
    unfold transl_variable.
    cbn.
    rewrite heq_CEfetchG_nme_CE_.
    functional inversion heq_CEframeG_nme_ /sng.
    + exfalso.
      subst.
      unfold CompilEnv.reside in heq_reside_.
      apply CompilEnv.fetches_ok_none_1 in heq_CEfetch_nme_.
      cbn in heq_reside_.
      rewrite heq_CEfetch_nme_ in heq_reside_.
      discriminate.
    + subst.
      rewrite heq_CEframeG_nme_CE_.
      assert (CompilEnv.exact_levelG CE) /sng.
      { eapply CompilEnv.exact_levelG_sublist;eauto. }
      specialize CompilEnv.exact_lvl_lvl_of_top with (1:=h_exct_lvlG_) (2:=heq_lvloftop_m'_);intro h_top_.
      cbn in h_top_.
      inversion h_top_ /sng.
      destruct CE.
      -- discriminate.
      -- cbn. destruct p.
         specialize build_loads__inj with (1:=heq_build_loads_);intro;subst /sng.
         erewrite exact_level_top_lvl;auto.
         all: swap 2 1.
         ++ cbn.
            reflexivity.
         ++ assert (s - lvl_nme = S s - lvl_nme - 1)%nat by lia /sng.
            exists (δ_id mod Int.modulus);split.
            ** symmetry.
               apply Zmod_eqm.
            ** right.
               rewrite heq_sub_;reflexivity.
Qed.
*)
Lemma build_compilenv_stack_no_null_offset:
  ∀ (st : symboltable) (CE : CompilEnv.state) (proc_lvl : level) (lparams : list paramSpec) 
    (decl : decl) (CE' : compilenv) (sz : Z),
    CompilEnv.exact_levelG CE →
    all_addr_no_overflow CE →
    stack_no_null_offset CE →
    build_compilenv st CE proc_lvl lparams decl =: (CE', sz) →
    stack_no_null_offset CE'.
Proof.
  intros /sng.
  rew build_compilenv_ok with
    functional inversion heq_build_compilenv_; rewrite build_compilenv_ok in * /sng.
  destruct x /sng.
  subst stoszchainparam.
  red;red;intros /sng.
  destruct (CompilEnv.fetches nme x0) eqn:h1; destruct (CompilEnv.resides nme x0) eqn:h2; try discriminate;  up_type;
    try match goal with
        | h1 : CompilEnv.fetches nme x0 = Some ?t |- _ => 
          specialize CompilEnv.fetches_ok with (1:=h1);
            let h := fresh "h" in
            intro h;
              rewrite h in *;
              discriminate
        | h1 : CompilEnv.fetches nme x0 = None |- _ => 
          specialize CompilEnv.fetches_ok_none_1 with (1:=h1);
            let h := fresh "h" in
            intro h;
              rewrite h in *;
              discriminate
        end.
  all:swap 1 2.
  - (* nme is in CE, applying hyp. *)
    (* specialize transl_variable_cons'' with (1:=h_no_overf_CE_). *)
    assert (CompilEnv.fetchG nme CE = Some δ_nme) /sng.
    { cbn in heq_CEfetchG_nme_.
      rewrite h1 in heq_CEfetchG_nme_.
      assumption. }
    eapply h_nonul_ofs_CE_ ;eauto.
  - (* nme is in the new top frame *)
    cbn in heq_CEfetchG_nme_.
    rewrite h1 in heq_CEfetchG_nme_.    
    inversion heq_CEfetchG_nme_;subst.
    eapply build_compilenv_no_null_offset;eauto.
Qed.



(** Consequence of chained structure: build_load returns always a pointeur *)
Lemma build_loads_Vptr : forall lvl_nme lvl g spb ofs locenv m δ_nme nme_t nme_t_v,
    Archi.ptr64 = false ->
    stack_localstack_aligned lvl locenv g m (Values.Vptr spb ofs) ->
    (lvl_nme < lvl)%nat ->
    build_loads lvl_nme δ_nme = nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t nme_t_v ->
    ∃ nme_block nme_ofst, nme_t_v = (Values.Vptr nme_block nme_ofst).
Proof.
  unfold build_loads.
  intros; subst /sng.
  invclear h_CM_eval_expr_nme_t_nme_t_v_ /sng.
  cbn in h_eval_binop_Oadd_v1_v2_.
  invclear h_eval_binop_Oadd_v1_v2_ /sng.
  red in h_aligned_g_m_.
  destruct (h_aligned_g_m_ lvl_nme);try lia /sng.
  subst_det_addrstack_zero.
  invclear h_CM_eval_expr_v2_ /sng.
  cbn in *.
  rewrite heq_ptr64_.
  invclear h_eval_constant_ /sng.
  eauto.
Qed.


(** Consequence of chained structure: a variable is always translated into a pointer. *)
Lemma transl_variable_Vptr : forall g spb ofs locenv m stbl CE astnm nme nme_t nme_t_v,
    invariant_compile CE stbl ->
    stack_localstack_aligned (Datatypes.length CE) locenv g m (Values.Vptr spb ofs) ->
    transl_variable stbl CE astnm nme =: nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t nme_t_v ->
    ∃ nme_block nme_ofst, nme_t_v = (Values.Vptr nme_block nme_ofst).
Proof.
  intros /sng.
  functional inversion h_eq_transl_var_ /sng.
  eapply build_loads_Vptr;eauto.
  erewrite <- CompilEnv.exact_lvl_lvl_of_top with (n:=m').
  + lia.
  + apply h_inv_comp_CE_stbl_.
  + assumption.
Qed.


Definition all_addr_no_overflow_localframe sto := 
  ∀ (id : idnum) (δ : CompilEnv.V),CompilEnv.fetch id sto = Some δ → 0 <= δ ∧ δ < Ptrofs.modulus.

Ltac rename_hyp_overf n th :=
  match th with
    all_addr_no_overflow_localframe _ => fresh "no_overf_localf"
  | _ => rename_hyp_forbid_unch n th
  end.

Ltac rename_sparkprf ::= rename_hyp_overf.

Lemma all_addr_no_overflow_fetch_OK_ :
  forall sto CE,
    all_addr_no_overflow_localframe sto
    -> all_addr_no_overflow CE -> all_addr_no_overflow (sto :: CE).
Proof.
  intros /sng.
  red.
  intros /sng.
  cbn in heq_CEfetchG_id_.
  destruct (CompilEnv.fetch id sto) eqn:? /sng.
  - invclear heq_CEfetchG_id_ /sng.
    eauto.
  - eauto.
Qed.



Lemma build_frame_lparams_preserve_no_overflow_pos_addr: ∀ st prmprof l sz lvl l' sz',
    sz >= 0
    -> build_frame_lparams st (l,sz) prmprof =: (l',sz')
    -> all_addr_no_overflow_localframe (lvl, l)
    -> all_addr_no_overflow_localframe (lvl, l') ∧ sz' >= 0.
Proof.
  intros until sz.
  remember (l, sz) as locfrmZ. 
  revert l sz HeqlocfrmZ .
  rew build_frame_lparams_ok with
    (functional induction (function_utils.build_frame_lparams st locfrmZ prmprof);!intros;try discriminate) /sng.
  - invclear heq_OK_ /sng.
    split;assumption.
  - rew function_utils.add_to_frame_ok with
      functional inversion heq_add_to_fr_nme_ /sng.
    assert (x0 > 0).
    { unfold compute_size in heq_cmpt_size_subtyp_mrk_.
      destruct compute_chnk_of_type;try discriminate.
      cbn in heq_cmpt_size_subtyp_mrk_.
      inversion heq_cmpt_size_subtyp_mrk_.
      apply size_chunk_pos;assumption. }
    unfold new_size, new_cenv in *.
    eapply h_forall_l_;eauto;try lia.
    red.
    intros /sng.
    cbn in heq_CEfetch_id_.
    destruct (id =? nme)%nat /sng.
    + invclear heq_CEfetch_id_ /sng.
      generalize (Zge_cases (δ + x0)  Ptrofs.modulus).
      intro h_ge_.
      rewrite heq_geb_ in h_ge_.
      split.
      * lia.
      * lia.
    + unfold all_addr_no_overflow_localframe in h_no_overf_localf_.
      eapply h_no_overf_localf_.
      eassumption.
Qed.

Lemma build_frame_lparams_preserve_no_overflow: ∀ st prmprof l sz lvl l' sz',
    sz >= 0
    -> build_frame_lparams st (l,sz) prmprof =: (l',sz')
    -> all_addr_no_overflow_localframe (lvl, l)
    -> all_addr_no_overflow_localframe (lvl, l').
Proof.
  intros st prmprof l sz lvl l' sz' H H0 H1.
  edestruct build_frame_lparams_preserve_no_overflow_pos_addr;eauto.
Qed.

Lemma build_frame_lparams_preserve_pos_addr: ∀ st prmprof l sz lvl l' sz',
    sz >= 0
    -> build_frame_lparams st (l,sz) prmprof =: (l',sz')
    -> all_addr_no_overflow_localframe (lvl, l)
    -> sz' >= 0.
  intros st prmprof l sz lvl l' sz' H H0 H1.
  edestruct build_frame_lparams_preserve_no_overflow_pos_addr;eauto.
Qed.


Lemma build_frame_decl_preserve_no_overflow_pos_addr: ∀ st decl l sz lvl l' sz',
    sz >= 0
    -> build_frame_decl st (l,sz) decl =: (l',sz')
    -> all_addr_no_overflow_localframe (lvl, l)
    -> all_addr_no_overflow_localframe (lvl, l') ∧ sz' >= 0.
Proof.
  intros until sz.
  remember (l, sz) as locfrmZ.
  revert l sz HeqlocfrmZ .
  rew build_frame_decl_ok with
    functional induction (function_utils.build_frame_decl st locfrmZ decl);!intros;subst ;try discriminate;
      try rewrite <- build_frame_decl_ok in * /sng.
  - split.
    + invclear heq_OK_ /sng.
      invclear heq_pair_ /sng.
      assumption.
    + invclear heq_OK_ /sng.
      invclear heq_pair_ /sng.
      assumption.
  - rename x into size.
    invclear heq_OK_ /sng.
    invclear heq_pair_ /sng.
    assert (size > 0).
    { unfold compute_size in heq_cmpt_size_.
      destruct compute_chnk_of_type;try discriminate.
      cbn in heq_cmpt_size_.
      inversion heq_cmpt_size_.
      apply size_chunk_pos;assumption. }

    split.
    + unfold all_addr_no_overflow_localframe.
      intros /sng.
      cbn in heq_CEfetch_id_.
      
      destruct (id =? (object_name objdecl))%nat /sng.
      * invclear heq_CEfetch_id_ /sng.
        generalize (Zge_cases (δ + size)  Ptrofs.modulus).
        intro h_ge_.
        rewrite heq_geb_ in h_ge_.
        split.
        -- lia.
        -- lia.
      * unfold all_addr_no_overflow_localframe in h_no_overf_localf_.
        eapply h_no_overf_localf_.
        eassumption.
    + lia.
  - rename x into size.
    up_type.
    invclear heq_pair_ /sng.
    destruct size.
    specialize (h_forall_l_ _ _ eq_refl lvl s z h_ge_sz0_Z0_ heq_build_frame_decl_ h_no_overf_localf_).
    split.
    + destruct h_forall_l_ as [IHr1 IHr2].
      eapply h_forall_l0_;eauto.
    + destruct h_forall_l_ as [IHr1 IHr2].
      eapply h_forall_l0_;eauto.
Qed.

Lemma build_frame_decl_preserve_no_overflow: ∀ st decl l sz lvl l' sz',
    sz >= 0
    -> build_frame_decl st (l,sz) decl =: (l',sz')
    -> all_addr_no_overflow_localframe (lvl, l)
    -> all_addr_no_overflow_localframe (lvl, l').
Proof.
  intros st decl l sz lvl l' sz' H H0 H1.
  edestruct build_frame_decl_preserve_no_overflow_pos_addr;eauto.
Qed.

Lemma build_frame_decl_preserve_pos_addr: ∀ st decl l sz lvl l' sz',
    sz >= 0
    -> build_frame_decl st (l,sz) decl =: (l',sz')
    -> all_addr_no_overflow_localframe (lvl, l)
    -> sz >= 0.
Proof.
  intros st decl l sz lvl l' sz' H H0 H1.
  edestruct build_frame_decl_preserve_no_overflow_pos_addr;eauto.
Qed.
(*
Lemma build_frame_decl_preserve_no_overflow_pos_addr: ∀ st decl l sz lvl l' sz',
    sz >= 0
    -> build_frame_decl st (l,sz) decl =: (l',sz')
    -> all_addr_no_overflow_localframe (lvl, l)
    -> all_addr_no_overflow_localframe (lvl, l') ∧ sz' >= 0.
Proof.
  intros until sz.
  remember (l, sz) as locfrmZ.
  revert l sz HeqlocfrmZ .
  rewrite <- build_frame_decl_ok.
  functional induction (build_frame_decl_2 st locfrmZ decl);!intros;subst;try discriminate
  ; try rewrite -> build_frame_decl_ok in * /sng.
*)

Lemma all_addr_nooverflow_localeframe_nil : forall lvl, all_addr_no_overflow_localframe (lvl, [ ]).
Proof.
  intros /sng.
  red. intros /sng.
  unfold CompilEnv.fetch in heq_CEfetch_id_.
  simpl in heq_CEfetch_id_.
  inversion heq_CEfetch_id_.
Qed.

Lemma build_compilenv_stack_no_overf:
  ∀ (st : symboltable) (CE : CompilEnv.state) (proc_lvl : level) (lparams : list paramSpec) (decl : decl) 
    (CE' : compilenv) (sz : Z),
    CompilEnv.exact_levelG CE
    → all_addr_no_overflow CE
    → stack_no_null_offset CE
    → build_compilenv st CE proc_lvl lparams decl =: (CE', sz)
    → all_addr_no_overflow CE'.
Proof.
  intros /sng.
  rew build_compilenv_ok with functional inversion heq_build_compilenv_ /sng.
  red.
  intros /sng.
  destruct x.
  subst stoszchainparam.
  subst scope_lvl.
  eapply all_addr_no_overflow_fetch_OK_;eauto.
  eapply build_frame_decl_preserve_no_overflow;eauto.
  + eapply build_frame_decl_preserve_pos_addr with (lvl:=4%nat);eauto.
    * eapply build_frame_lparams_preserve_pos_addr with (lvl:=4%nat);eauto.
      -- lia.
      -- apply all_addr_nooverflow_localeframe_nil.
    * eapply build_frame_lparams_preserve_no_overflow with (lvl:=4%nat);eauto.
      -- lia.
      -- apply all_addr_nooverflow_localeframe_nil.
  + eapply build_frame_lparams_preserve_no_overflow with (lvl:=4%nat);eauto.
    -- lia.
    -- apply all_addr_nooverflow_localeframe_nil.
Qed.


Lemma build_frame_lparams_preserve_increasing_order:
  forall st init prmprof lvl fr z,
    build_frame_lparams st (init,z) prmprof =: (fr,lvl)
    -> Forall (gt_x_snd_y z) init
    -> increasing_order init
    -> increasing_order fr ∧ Forall (gt_x_snd_y lvl) fr.
Proof.
  intros * /sng.
  remember (init,z) as initz.
  revert init z Heqinitz.
  rew build_frame_lparams_ok
  with (functional induction (function_utils.build_frame_lparams st initz prmprof);
         !intros;try discriminate) /sng.
  - inversion heq_OK_;subst;auto.
  - rew add_to_frame_ok with functional inversion heq_add_to_fr_nme_;subst /sng.
    unfold new_cenv,new_size in *.
    clear new_cenv new_size.
    specialize (h_forall_init_ _ _ eq_refl).
    apply h_forall_init_.
    + assumption.
    + assert (x0>0) /sng.
      { destruct subtyp_mrk;cbn in heq_cmpt_size_subtyp_mrk_;inversion heq_cmpt_size_subtyp_mrk_;lia.  }
      constructor;auto.
      * unfold gt_x_snd_y;cbn;lia.
      * eapply Forall_impl with (P:= gt_x_snd_y z);auto.
        intros /sng.
        unfold gt_x_snd_y in *;cbn in *.
        lia.
    + constructor;auto.
Qed.



Lemma build_frame_decl_preserve_increasing_order:
  forall st init decl lvl fr z,
    build_frame_decl st (init,z) decl =: (fr,lvl)
    -> Forall (gt_x_snd_y z) init
    -> increasing_order init
    -> increasing_order fr ∧ Forall (gt_x_snd_y lvl) fr.
Proof.
  intros * /sng.
  remember (init,z) as initz.
  revert init z Heqinitz lvl fr.
  rew build_frame_decl_ok with
    functional induction (function_utils.build_frame_decl st initz decl);!intros;subst;try discriminate /sng.
  - inversion heq_OK_;subst;auto.
    inversion heq_pair_;subst;auto.
  - invclear heq_OK_;subst /sng.
    invclear heq_pair_;subst /sng.
    split.
    + constructor.
      * assumption.
      * unfold gt_snd.
        simpl.
        change (Forall (gt_x_snd_y z) init).
        assumption.
    + constructor.
      * unfold gt_snd;cbn.
        assert (h:=compute_size_pos _ _ _ heq_cmpt_size_).
        red. simpl.
        lia.
      * apply Forall_forall.
        intros /sng.
        eapply Forall_forall in h_lst_forall_init_;eauto.
        red;simpl.
        red in h_lst_forall_init_;simpl in *.
        assert (h:=compute_size_pos _ _ _ heq_cmpt_size_).
        lia.        
  - destruct x.
    destruct (h_forall_init_ init z heq_pair_ _ _ heq_build_frame_decl_ h_lst_forall_init_ h_incr_order_init_); clear h_forall_init_ /sng.
    destruct (h_forall_init0_ s z0 eq_refl _ _ heq_build_frame_decl0_ h_lst_forall_s_ h_incr_order_s_) /sng.
    split;assumption.
Qed.


Lemma build_frame_lparams_mon_sz: forall st params stosz stosz',
    build_frame_lparams st stosz params =: stosz' -> 
    snd stosz <= snd stosz'.
Proof.
  intros until stosz /sng.
  rew build_frame_lparams_ok with
    functional induction (function_utils.build_frame_lparams st stosz params);!intros /sng.
  - inversion heq_OK_.
    reflexivity.
  - specialize (h_forall_stosz'_ stosz' heq_build_frame_lparams_).
    rew add_to_frame_ok with functional inversion heq_add_to_fr_nme_;subst;cbn in * /sng.
    pose proof compute_size_pos _ _ _ heq_cmpt_size_subtyp_mrk_.
    unfold new_size in *.
    lia.
  - discriminate.
Qed.




Lemma build_compilenv_preserve_invariant_compile:
  forall st CE pb_lvl prmprof pdeclpart CE' stcksize,
    build_compilenv st CE pb_lvl prmprof pdeclpart =: (CE', stcksize)
    -> invariant_compile CE st
    -> invariant_compile CE' st.
Proof.
  (intros until 1) /sng.
  rew build_compilenv_ok with
    (functional inversion heq_build_compilenv_;subst;intro;clear heq_build_compilenv_) /sng.
  split;eauto with spark.
  + constructor.
    eauto with spark.
  + constructor.
    * red.
      cbn.
      destruct x.
      destruct (build_frame_decl_preserve_increasing_order _ _ _ _ _ _ heq_build_frame_decl_);auto.
      -- destruct (build_frame_lparams_preserve_increasing_order _ _ _ _ _ _ heq_bld_frm_prmprof_);auto.
         constructor;cbn in *;auto.
      -- destruct (build_frame_lparams_preserve_increasing_order _ _ _ _ _ _ heq_bld_frm_prmprof_);auto.
         constructor;cbn in *;auto.
    * eapply (ci_increasing_ids h_inv_comp_CE_st_).
  + apply all_addr_no_overflow_fetch_OK_;eauto with spark.
    destruct x;unfold stoszchainparam in *.
    eapply (build_frame_decl_preserve_no_overflow st pdeclpart s z (Datatypes.length CE) x0 stcksize).
    -- eapply (build_frame_lparams_preserve_pos_addr st prmprof) with (lvl:=0%nat);eauto; try lia.
       red. cbn in *. intros /sng.
       discriminate.
    -- assumption.
    -- eapply (build_frame_lparams_preserve_no_overflow st prmprof);eauto with spark; try lia.
       red. cbn. intros /sng.
       discriminate.
  + unfold CompilEnv.NoDup in *.
    intros /sng.
    cbn in h_lst_in_.
    destruct h_lst_in_ /sng.
    * invclear heq_pair_;subst /sng.
      admit. (* spark typing, no name collision intra frame *)
    * pose proof (ce_nodup_CE h_inv_comp_CE_st_) /sng.
      red in h_CEnodup_CE_.
      eapply h_CEnodup_CE_;eauto.
  + unfold CompilEnv.NoDup_G in *.
    constructor.
    all:swap 1 2.
    * apply h_inv_comp_CE_st_.
    * admit. (* spark typing no name collision inter frame *)
Admitted.

Lemma add_to_frame_sz: forall stbl fram_sz parname parsubtype p sz,
    spark2Cminor.add_to_frame stbl fram_sz parname parsubtype =: p
    -> spark2Cminor.compute_size stbl parsubtype = Errors.OK sz
    -> snd p = snd fram_sz + sz.
Proof.
  intros until 1 /sng.
  rew add_to_frame_ok
  with functional inversion heq_add_to_fr_parname_
       ;!intros /sng.
  subst new_size.
  subst new_cenv.
  cbn in *.
  rewrite heq_cmpt_size_parsubtype0_ in heq_cmpt_size_parsubtype_.
  inversion heq_cmpt_size_parsubtype_.
  reflexivity.
Qed.


Lemma add_to_frame_correct: forall stbl fram_sz parname parsubtype p othername,
    spark2Cminor.add_to_frame stbl fram_sz parname parsubtype =: p
    -> CompilEnv.resides othername (fst fram_sz) = true
    -> CompilEnv.resides othername (fst p) = true.
Proof.
  intros until 1 /sng.
  rew add_to_frame_ok with
    functional inversion heq_add_to_fr_parname_ ;!intros /sng.
  subst new_size.
  subst new_cenv.
  simpl.
  destruct (othername =? parname)%nat eqn:heq;auto.
Qed.

Lemma add_to_frame_correct2: forall stbl fram_sz parname parsubtype p,
    spark2Cminor.add_to_frame stbl fram_sz parname parsubtype =: p
    -> CompilEnv.resides parname (fst p) = true.
Proof.
  intros until 1 /sng.
  rew add_to_frame_ok with
    functional inversion heq_add_to_fr_parname_
    ;!intros /sng.
  subst new_size.
  subst new_cenv.
  simpl.
  now rewrite <- beq_nat_refl.
Qed.

Lemma add_to_frame_correct_rev: forall stbl fram_sz parname parsubtype new_fram_sz othername,
    spark2Cminor.add_to_frame stbl fram_sz parname parsubtype =: new_fram_sz
    -> (CompilEnv.resides othername (fst new_fram_sz) = true ∧ othername <> parname)
    -> CompilEnv.resides othername (fst fram_sz) = true.
Proof.
  intros until 1 /sng.
  rew add_to_frame_ok with
    functional inversion heq_add_to_fr_parname_ ;!intros /sng.
  subst new_size.
  subst new_cenv.
  simpl.
  decomp h_and_.
  simpl in heq_resides_.
  rewrite <- Nat.eqb_neq in hneq_othername.
  rewrite hneq_othername in heq_resides_.
  assumption.
Qed.


Lemma build_frame_lparams_correct: forall lparam stbl fram_sz res,
    build_frame_lparams stbl fram_sz lparam  =: res
    -> forall x, (List.In x lparam ∨ CompilEnv.resides (parameter_name x) (fst fram_sz) = true)
                 -> CompilEnv.resides (parameter_name x) (fst res) = true.
Proof.
  intros until fram_sz /sng.
  rew function_utils.build_frame_lparams_ok with
    (functional induction (function_utils.build_frame_lparams stbl fram_sz lparam); try discriminate;!intros) /sng.
  - destruct h_or_ /sng.
    + inversion h_lst_in_x_.
    + simpl in *.
      invclear heq_OK_ /sng.
      assumption.
  - remember {| parameter_astnum := _x; parameter_name := nme; parameter_subtype_mark := subtyp_mrk; parameter_mode := _x0 |}  as p.
    decomp h_or_.
    + destruct h_lst_in_x0_.
      * subst.
        eapply h_forall_res_;eauto.
        right.
        simpl.
        eapply add_to_frame_correct2;eauto.
      * eapply h_forall_res_;eauto.
    + eapply h_forall_res_;eauto.
      right.
      eapply add_to_frame_correct;eauto.
Qed.

Lemma build_frame_lparams_correct_rev: forall lparam stbl fram_sz res,
    build_frame_lparams stbl fram_sz lparam  =: res
    -> forall nme, CompilEnv.resides nme (fst res) = true
                 -> ((exists x,List.In x lparam ∧ (parameter_name x) = nme)
                     ∨ CompilEnv.resides nme (fst fram_sz) = true).
Proof.
  intros until fram_sz /sng.
  rew function_utils.build_frame_lparams_ok with
    (functional induction (function_utils.build_frame_lparams stbl fram_sz lparam); try discriminate;intros) /sng.
  - inversion heq_OK_. 
    right;assumption.
  - up_type.
    remember {| parameter_astnum := _x; parameter_name := nme; parameter_subtype_mark := subtyp_mrk; parameter_mode := _x0 |}  as p.
    specialize (h_forall_res_ _ heq_build_frame_lparams_ _  heq_resides_).
    decompose [ex or and] h_forall_res_ /sng.
    + left.
      exists x0;split;auto.
      right;assumption.
    + destruct (Nat.eq_dec nme0 nme).
      * subst nme0.
        left.
        exists p.
        split.
        -- left;auto.
        -- subst;reflexivity.
      * right.
        eapply add_to_frame_correct_rev;eauto.
Qed.

Lemma add_to_frame_correct3: forall stbl fram_sz parname parsubtype new_fr new_sz othername e,
    increasing_order (fst fram_sz)
    -> upper_bound (fst fram_sz) (snd fram_sz)
    -> CompilEnv.fetches parname (fst fram_sz) = None
    -> spark2Cminor.add_to_frame stbl fram_sz parname parsubtype =: (new_fr, new_sz)
    -> CompilEnv.fetches othername (fst fram_sz) = Some e
    -> CompilEnv.fetches othername new_fr = Some e.
Proof.
  intros /sng.
  rew add_to_frame_ok 
  with functional inversion heq_add_to_fr_parname_
       ;subst;intros /sng.
  subst.
  simpl.
  destruct (othername =? parname)%nat eqn:heq'.
  - apply beq_nat_true in heq'.
    subst.
    rewrite heq_CEfetches_parname_ in heq_CEfetches_othername_;discriminate.
  - assumption.
Qed.

Lemma add_to_frame_correct4: forall stbl fram_sz parname parsubtype new_fram_sz,
    increasing_order (fst fram_sz)
    -> upper_bound (fst fram_sz) (snd fram_sz)
    -> add_to_frame stbl fram_sz parname parsubtype =: new_fram_sz
    -> increasing_order (fst new_fram_sz) ∧ upper_bound (fst new_fram_sz) (snd new_fram_sz)
       ∧ CompilEnv.fetches parname (fst new_fram_sz) = Some (snd fram_sz).
Proof.
  intros /sng.
  rew add_to_frame_ok with
    functional inversion heq_add_to_fr_parname_;!intros /sng.
  subst new_size.
  subst new_cenv.
  simpl.
  split;[|split].
  - red.
    apply Sorted_StronglySorted.
    + red.
      unfold gt_snd.
      intros [a a'] [b b'] [c c'] ? ?;simpl in * /sng.
      transitivity b';auto.
    + apply Sorted_LocallySorted_iff.
      destruct cenv.
      * constructor 2.
      * constructor 3.
        -- apply Sorted_LocallySorted_iff.
           apply StronglySorted_Sorted.
           apply h_incr_order_.
        -- destruct p;simpl.
           unfold gt_snd.
           simpl snd at 1.
           eapply h_upb_ with i;simpl;eauto.
           rewrite Nat.eqb_refl;reflexivity.
  - intros nme nme_ofs ?;simpl in * /sng.
    assert (x>0) by (unshelve eapply compute_size_pos;eauto) /sng.
    destruct (nme =? parname)%nat /sng.
    * inversion heq_CEfetches_nme_;subst.
      lia.
    * specialize (h_upb_ _ _ heq_CEfetches_nme_).
      lia.
  - now rewrite <- beq_nat_refl.
Qed.

Lemma add_to_frame_correct_none: forall stbl fram_sz parname parsubtype new_fr new_sz othername,
    CompilEnv.fetches othername (fst fram_sz) = None
    -> othername <> parname
    -> add_to_frame stbl fram_sz parname parsubtype =: (new_fr, new_sz)
    -> CompilEnv.fetches othername new_fr = None.
Proof.
  intros /sng.
  rew add_to_frame_ok with
    (functional inversion heq_add_to_fr_parname_
       ;subst;intros) /sng.
  simpl.
  destruct (othername =? parname)%nat eqn:heq'.
  - apply beq_nat_true in heq'.
    contradiction.
  - assumption.
Qed.


Lemma add_to_frame_correct_rev2: forall stbl fram_sz parameter_name parsubtype new_fr new_sz othername e,
    add_to_frame stbl fram_sz parameter_name parsubtype =: (new_fr, new_sz)
    -> CompilEnv.fetches othername new_fr = Some e ∧ othername <> parameter_name
    -> CompilEnv.fetches othername (fst fram_sz) = Some e.
Proof.
  intros /sng.
  rew add_to_frame_ok with
    (functional inversion heq_add_to_fr_parameter_name_ ;intros) /sng.
  simpl.
  subst.
  decomp h_and_.
  simpl in heq_CEfetches_othername_.
  rewrite <- Nat.eqb_neq in hneq_othername.
  rewrite hneq_othername in heq_CEfetches_othername_.
  assumption.  
Qed.

Lemma add_to_frame_correct_none_rev: forall stbl fram_sz parameter_name parsubtype new_fr new_sz othername,
    add_to_frame stbl fram_sz parameter_name parsubtype =: (new_fr, new_sz)
    -> CompilEnv.fetches othername new_fr = None
    -> CompilEnv.fetches othername (fst fram_sz) = None.
Proof.
  intros /sng.
  rew add_to_frame_ok with
    functional inversion heq_add_to_fr_parameter_name_;!intros /sng.
  simpl.
  subst.
  functional inversion heq_CEfetches_othername_new_fr_.
  assumption.
Qed.


Definition fresh_params_ lparam (fr:localframe) :=
  Forall (fun prm => CompilEnv.fetches (parameter_name prm) fr = None) lparam.



(* TODO: move this elsewhere *)
Ltac rename_hyp_list n th :=
  match th with
    | fresh_params_ ?l ?fr => fresh "fresh_prms_" l "_" fr
    | fresh_params_ ?l _ => fresh "fresh_prms_" l
    | fresh_params_ _ _ => fresh "fresh_prms_"
    | _ => rename_hyp_overf n th
  end.

Ltac rename_sparkprf ::= rename_hyp_list.

Ltac fold_pairs H :=
  match type of H with
    context C [(fst ?x,snd ?x)] => replace (fst x,snd x) with x in H; [ | destruct x;reflexivity]
  end.

Lemma add_to_frame_fresh: forall stbl fram_sz lparam' subtyp_mrk prm x,
    fresh_params_ (prm::lparam') (fst fram_sz)
    -> NoDupA eq_param_name (prm::lparam')
    -> add_to_frame stbl fram_sz (parameter_name prm) subtyp_mrk =: x
    -> fresh_params_ lparam' (fst x).
Proof.
  intros until prm /sng. 
  remember (parameter_name prm) as prn_nme.
  rew add_to_frame_ok with
    (functional induction (function_utils.add_to_frame stbl fram_sz prn_nme subtyp_mrk);intros;try discriminate) /sng.
  invclear heq_OK_ /sng.
  red. apply Forall_forall.
  intros prm0 ? /sng.
  assert (parameter_name prm0 <> parameter_name prm) /sng.
  { intro abs.
    inversion h_NoDupA_ /sng.
    apply h_neg_inA_prm_lparam'_.
    rewrite InA_alt.
    exists prm0.
    split;auto.
    red.
    symmetry;auto. }
  simpl.
  rewrite <- Nat.eqb_neq in hneq.
  rewrite hneq.
  simpl in hneq.
  unfold fresh_params_ in h_fresh_prms_.
  rewrite Forall_forall in h_fresh_prms_.
  apply h_fresh_prms_.
  simpl.
  right;assumption.
Qed.

Lemma build_frame_lparams_nodup: forall stbl lparam fram_sz res,
    increasing_order (fst fram_sz)
    -> NoDupA eq_param_name lparam    
    -> fresh_params_ lparam (fst fram_sz)
    -> upper_bound (fst fram_sz) (snd fram_sz)
    -> build_frame_lparams stbl fram_sz lparam = Errors.OK res
    -> NoDupA eq_fst_idnum (fst fram_sz)
    -> NoDupA eq_fst_idnum (fst res).
Proof.
  intros until fram_sz /sng.
  rew build_frame_lparams_ok with
    functional induction (function_utils.build_frame_lparams stbl fram_sz lparam);simpl;!intros;
      try discriminate /sng.
  - invclear heq_OK_ /sng.
    assumption.
  - apply h_forall_res_.
    + assert (h:=build_frame_lparams_preserve_increasing_order stbl (fst x) lparam' (snd res) (fst res) (snd x));auto.      
      repeat fold_pairs h.
      eapply add_to_frame_correct4;eauto.
    + inversion h_NoDupA_.
      assumption.
    + assert (fresh_params_ lparam' (fst fram_sz)) /sng.
      { red in h_fresh_prms_.
        red.
        rewrite Forall_forall in h_fresh_prms_|-*.
        intros /sng.
        apply h_fresh_prms_.
        simpl.
        right.
        assumption. }
      eapply add_to_frame_fresh;eauto.
    + eapply add_to_frame_correct4;eauto.
    + assumption.
    + replace x with (fst x,snd x) in heq_add_to_fr_nme_.
      * eapply add_to_frame_nodup;eauto.
        red in h_fresh_prms_.
        rewrite Forall_forall in h_fresh_prms_.
        match type of h_fresh_prms_ with
        | context [List.In _ (?prm::_)]  => specialize (h_fresh_prms_ prm)
        end.
        apply h_fresh_prms_.
        left.
        reflexivity.
      * destruct x;auto.
Qed.
        
        
 
Lemma fetch_In_ : forall a id st,
    CompilEnv.fetch id a = Some st ->
    List.In (id,st) (CompilEnv.store_of a).
Proof.
  intros /sng.
  unfold CompilEnv.fetch in heq_CEfetch_id_a_.
  apply fetches_In.
  assumption.
Qed.

Lemma in_transl_paramid_in_eq_param_name :
  forall st l x,
    List.In (transl_paramid (parameter_name x)) (transl_lparameter_specification_to_lident st l) ->
    InA eq_param_name x l.
Proof.
  intros until l /sng. 
  induction l;(simpl;!!intros) /sng.
  - intro abs;contradict abs.
  - decomp h_or_.
    + destruct a;destruct x;simpl in *|-*.
      constructor 1.
      red.
      simpl.
      unfold transl_paramid, transl_num in heq_transl_paramid_.
      apply SuccNat2Pos.inj in heq_transl_paramid_;try lia.
    + constructor 2.
      apply h_forall_x_.
      assumption.
Qed.

Lemma notin_transl_paramid_notin_eq_param_name :
  forall st l x,
    ~List.In (transl_paramid (parameter_name x)) (transl_lparameter_specification_to_lident st l) ->
    ~InA eq_param_name x l.
Proof.
  intros until l /sng. 
  induction l;(simpl;!!intros) /sng.
  - intro abs.
    eapply InA_nil;eauto.
  - intro abs.
    apply h_neg_or_.
    inversion abs /sng.
    + intro heq.
      red in heq.
      rewrite heq in *.
      left;reflexivity.
    + absurd (InA eq_param_name x l);auto.
Qed.

Lemma chaining_param_neq_transl_lparam:
  forall st procedure_parameter_profile,
    ~  List.In chaining_param (transl_lparameter_specification_to_lident st procedure_parameter_profile).
Proof.
  intros st procedure_parameter_profile. 
  induction procedure_parameter_profile;simpl;!intros /sng.
  - intro; auto.
  - intro abs.
    decomp abs.
    + unfold transl_paramid, transl_num,chaining_param in heq_transl_paramid_.
      specialize (SuccNat2Pos.inj (parameter_name a + 80)%nat 0%nat heq_transl_paramid_) as ? /sng.
      lia.
    + apply h_neg_lst_in_chaining_param_;auto.
Qed.




Lemma transl_lparameter_specification_to_lident_nodup: forall  st lprmSpec,
    NoDupA eq_param_name lprmSpec -> 
    List.NoDup (transl_lparameter_specification_to_lident st lprmSpec).
Proof.
  intros /sng.
  induction h_NoDupA_lprmSpec_;fold transl_lparameter_specification_to_lident /sng.
  - constructor 1.
  - constructor 2;fold transl_lparameter_specification_to_lident.
    + intro abs.
      apply h_neg_inA_x_l_.
      eapply in_transl_paramid_in_eq_param_name;eauto.
    + assumption.
Qed.

Lemma build_frame_lparams_correct2 : forall lparam stbl fram_sz res,
    (* No argument with same name *)
    NoDupA eq_param_name lparam
    -> NoDupA eq_fst_idnum (fst fram_sz)
    (* fram_sz is wellformed *)
    -> increasing_order (fst fram_sz)
    -> upper_bound (fst fram_sz) (snd fram_sz)
    (* res is the new frame build from parameters on top of fram_sz *)
    -> build_frame_lparams stbl fram_sz lparam  =: res
    (* the parameters names were not present in fram_sz before *)
    -> fresh_params_ lparam (fst fram_sz)
    (* then for all x-> e in fram_sz, x->e is still in res *)
    -> forall e x, CompilEnv.fetches x (fst fram_sz) = Some e
                   -> CompilEnv.fetches x (fst res) = Some e.
Proof.
  intros /sng.
  red in h_fresh_prms_lparam_.
  assert (h:=build_frame_lparams_preserve_increasing_order stbl (fst fram_sz) lparam (snd res) (fst res) (snd fram_sz)).
  replace (@pair CompilEnv.store Z (@fst (list (prod idnum OffsetEntry.T)) Z fram_sz)
                   (@snd (list (prod idnum OffsetEntry.T)) Z fram_sz)) with fram_sz in *;[|destruct fram_sz;auto].
  replace (pair (fst res) (snd res)) with res in *;[|destruct res;auto].
  specialize (h heq_bld_frm_lparam_).
  assert (increasing_order (fst res) ∧ Forall (gt_x_snd_y (snd res)) (fst res)) /sng.
  { assert (NoDupA (λ x1 y : idnum * CompilEnv.V, fst x1 = fst y) (fst res)) /sng.
    { eapply build_frame_lparams_nodup;eauto. }
    apply h;auto.
    apply Forall_forall.
    intros  /sng.
    unfold upper_bound in h_upb_.
    apply h_upb_ with (nme:=(fst x0)).
    specialize (h_upb_ (fst x0) (snd x0)).
    apply In_fetches_NoDup.
    - assumption.
    - replace (fst x0, snd x0) with x0;auto.
      destruct x0;simpl;auto. }
  clear h.
  decomp h_and_.
  revert h_incr_order_ h_fresh_prms_lparam_ res heq_bld_frm_lparam_ e x heq_CEfetches_x_ h_incr_order0_  h_lst_forall_ h_upb_.
  rew function_utils.build_frame_lparams_ok with
  (functional induction (function_utils.build_frame_lparams stbl fram_sz lparam); try discriminate;
     intros;up_type) /sng.
  - simpl in *.
    invclear heq_OK_ /sng.
    assumption.
  - rename x into nme_fram_sz.
    invclear h_lst_forall0_ /sng.
    simpl in *.
    destruct nme_fram_sz as [new_fram new_sz].
    assert (h_correct4_:= add_to_frame_correct4 stbl fram_sz nme subtyp_mrk (new_fram,new_sz) h_incr_order_ h_upb_ heq_add_to_fr_nme_).
    decomp h_correct4_.
    assert (h_correct3_:= λ typename, add_to_frame_correct3 stbl fram_sz nme subtyp_mrk new_fram new_sz
                                                           typename e h_incr_order_ h_upb_ heq_CEfetches_none_).
    eapply h_impl_impl_impl_impl_forall_res_;auto.
    + inversion h_NoDupA_lparam_.
      assumption.
    + simpl.
      eapply add_to_frame_nodup;eauto.
    + simpl in *.
      apply Forall_forall.
      intros prmspec ? /sng.
      rewrite Forall_forall in h_lst_forall_lparam'_.
      specialize (h_lst_forall_lparam'_ prmspec h_lst_in_prmspec_lparam'_).
      up_type.
      eapply add_to_frame_correct_none with (parname:=nme);eauto.
      inversion h_NoDupA_lparam_ /sng.
      intro abs.
      subst nme.
      rewrite InA_alt in h_neg_inA_.
      apply h_neg_inA_. clear h_neg_inA_.
      exists prmspec.
      unfold eq_param_name;simpl.
      split;auto.
Qed.

(* Extract the list of object names from a declaration block *)
Fixpoint decl_to_lident (stbl:symboltable) (decl:decl): list idnum :=
  match decl with
  | NullDecl => nil
  | SeqDecl _ decl1 decl2 =>
    let lident1 := decl_to_lident stbl decl1 in
    let lident2 := decl_to_lident stbl decl2 in
    List.app lident1 lident2
  | ObjDecl _ objdecl => (objdecl.(object_name) :: nil)
  | TypeDecl x x0 => nil
  | ProcBodyDecl x x0 => nil
  end.

(*
Lemma build_frame_decl_correct : forall decl stbl fram_sz res,
    (* No argument with same name *)
(*     NoDupA eq_param_name lparam *)
(*     -> fresh_params_ lparam (fst fram_sz) *)
(*     -> *)
    NoDupA (λ x1 y : idnum * CompilEnv.V, fst x1 = fst y) (fst fram_sz)
    (* fram_sz is wellformed *)
    -> increasing_order (fst fram_sz)
    -> upper_bound (fst fram_sz) (snd fram_sz)
    (* res is the new frame build from parameters on top of fram_sz *)
    -> build_frame_decl stbl fram_sz decl  =: res
    (* the parameters names were not present in fram_sz before *)
    -> Forall (fun declnme => CompilEnv.fetches declnme (fst fram_sz) = None) (decl_to_lident stbl decl)
    (* then for all x-> e in fram_sz, x->e is still in res *)
    -> forall e x, CompilEnv.fetches x (fst fram_sz) = Some e
                   -> CompilEnv.fetches x (fst res) = Some e.
Proof.

Admitted.
*)

(*
Inductive Decl_atomic : declaration -> Prop :=
  | Decl_atom_type: forall a t, Decl_atomic(D_Type_Declaration a t)
  | Decl_atom_Object: forall a o, Decl_atomic(D_Object_Declaration a o)
  | Decl_atom_proc: forall a p, Decl_atomic(D_Procedure_Body a p).

Inductive Decl_list_form : declaration  -> Prop:=
| Decl_nil: Decl_list_form D_Null_Declaration
| Decl_cons: forall a d D, Decl_list_form D
                           -> Decl_atomic d
                           -> Decl_list_form (D_Seq_Declaration a d D).


Fixpoint measure_decl (d:declaration):nat :=
  match d with
  | D_Null_Declaration => 0%nat
  | D_Type_Declaration x x0 => 1%nat
  | D_Object_Declaration x x0 => 1%nat
  | D_Procedure_Body x x0 => 1%nat
  | D_Seq_Declaration x x0 x1 => measure_decl x0 + measure_decl x1
  end.

Definition measure_copy_in (pd: list parameter_specification * declaration) :=
  let '(p,d) := pd in
  (List.length p + measure_decl d)%nat.

Definition lt_copy_in d1 d2 := (measure_copy_in d1 < measure_copy_in d2)%nat.

Lemma wf_measure_decl : well_founded lt_copy_in.
Proof.
  eapply well_founded_lt_compat with (f:= measure_copy_in).
  intros x y H.
  assumption.
Qed.
*)

Ltac rename_hyp_decl n th :=
  match th with
(*    | Decl_list_form ?d => fresh "decl_list_" d
    | Decl_list_form _ => fresh "decl_list"
    | Decl_atomic ?d => fresh "decl_atom_" d
    | Decl_atomic _ => fresh "decl_atom"*)
    | _ => rename_hyp_list n th
  end.

Ltac rename_sparkprf ::= rename_hyp_decl.

Ltac spec H := repeat (specialize (H ltac:(assumption))).

Inductive transl_value_list : list value -> list Values.val -> Prop :=
  tr_lval_nil : transl_value_list nil nil
| tr_lval_cons: forall x x' l l', transl_value x x' -> transl_value_list l l' -> transl_value_list (x::l) (x'::l'). 

Inductive transl_prm_value_list : list paramSpec -> store -> list Values.val -> Prop :=
  tr_lprmval_nil : transl_prm_value_list nil nil nil
| tr_lprmval_cons: forall x x' l l' prm lprm,
    transl_value x x' -> transl_prm_value_list lprm l l' ->
    transl_prm_value_list (prm::lprm) ((parameter_name prm, x)::l) (x'::l'). 




(* 
Lemma copy_in_cps:
  forall st s pb_lvl sto prmnme e_v lparam le res,
  copy_in st s (push (pb_lvl, sto) prmnme e_v) lparam le (OK (pb_lvl, res ++ sto))
  -> copy_in st s (push (pb_lvl, nil) prmnme e_v) lparam le (OK (push (pb_lvl, nil) prmnme e_v)).
Proof.
  intros /sng.
  remember (push (pb_lvl, sto) prmnme e_v) as h_push1_.
  remember (OK (pb_lvl, res ++ sto)) as h_res_.
  revert Heqh_push1_ Heqh_res_.
  induction h_copy_in_; !intros;subst; try discriminate; try (now constructor) /sng.
  - unfold push;simpl.
    econstructor 3;eauto.
Qed.
 *)

(** eval_exprlist ok if copy_in ok *)
(* We probably need to generalize this first, as copy_in is written in CPS. *)
(* This is false, since for inout parameter, evalName is called, and for our parameters, nothing is called. *)

Proposition copy_in_lvl : forall st s pb_lvl sto prms_profile args f,
  copyIn st s (pb_lvl,sto) prms_profile args (OK f) ->
  exists sto', f = (pb_lvl,sto').
Proof.
  intros /sng.
  remember (pb_lvl, sto) as pb_lvl_sto.
  remember (OK f) as h_norm_f_.
  revert pb_lvl sto Heqh_norm_f_ Heqpb_lvl_sto.
  induction h_copy_in_; try discriminate;subst;repeat eq_same_clear;intros;subst /sng.
  - inversion Heqh_norm_f_; subst; eauto.
  - unfold push in h_forall_pb_lvl_.
    simpl in h_forall_pb_lvl_.
    edestruct h_forall_pb_lvl_;eauto.
  - unfold push in h_forall_pb_lvl_.
    simpl in h_forall_pb_lvl_.
    edestruct h_forall_pb_lvl_;eauto.
  - unfold push in h_forall_pb_lvl_.
    simpl in h_forall_pb_lvl_.
    edestruct h_forall_pb_lvl_;eauto.
  - unfold push in h_forall_pb_lvl_.
    simpl in h_forall_pb_lvl_.
    edestruct h_forall_pb_lvl_;eauto.
  - unfold push in h_forall_pb_lvl_.
    simpl in h_forall_pb_lvl_.
    edestruct h_forall_pb_lvl_;eauto.
Qed.

Lemma copy_in_spec:
  forall st s CE spb ofs locenv g m sto pb_lvl prms_profile args args_t sto',
    chained_stack_structure m (Datatypes.length CE -1) (Values.Vptr spb ofs)
    -> invariant_compile CE st
    -> match_env_ st s CE (Values.Vptr spb ofs) locenv g m
    -> transl_paramexprlist st CE args prms_profile =: args_t
    (* je veux exprimer la propriété qui parle  *)
    -> copyIn st s (pb_lvl,sto) prms_profile args (OK (pb_lvl,sto'))
    -> exists lval_t, eval_exprlist g (Values.Vptr spb ofs) locenv m args_t lval_t
(*             sto'' /\ copy_in st s (pb_lvl,nil) prms_profile args (OK (pb_lvl,sto'')) *)
(*                       /\ sto' = List.app sto'' sto *)
.
Proof.
  intros /sng.
  remember (OK (pb_lvl, sto')) as res_copy_in.
  remember (pb_lvl, sto) as pb_lvl_sto.
  revert htrans_prmexprl h_chain_m_ h_inv_comp_CE_st_ 
         h_match_env_ Heqres_copy_in Heqpb_lvl_sto .
  revert spb ofs locenv g m sto pb_lvl args_t sto'.
  induction h_copy_in_; try discriminate;subst;repeat eq_same_clear;!intros /sng.
  - subst.
    rew transl_paramexprlist_ok with
    functional inversion htrans_prmexprl; idtac /sng.
    inversion heq_OK_;subst;clear heq_OK_.
    exists  (@nil Values.val).
    constructor.
  - rew transl_paramexprlist_ok with
      functional inversion htrans_prmexprl;subst;
      match goal with
      | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
      end /sng.
    edestruct h_forall_spb_;clear h_forall_spb_;eauto /sng.
    + unfold push;simpl. reflexivity.
    + assert (h_transl_:=transl_expr_ok _ _ _ _ heq_tr_expr_e_ _ _ _ _ _ _ h_eval_expr_e_e_v_ h_match_env_).
      destruct h_transl_ as [v_t [? ?]] /sng.
      exists (e_t_v::x);repeat split;eauto.
      econstructor;eauto.
  - rew transl_paramexprlist_ok with
        functional inversion htrans_prmexprl;subst;
      match goal with
      | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
      end /sng.
    edestruct h_forall_spb_;clear h_forall_spb_;eauto /sng.
    + unfold push;simpl. reflexivity.
    + assert (h_transl_:=transl_expr_ok _ _ _ _ heq_tr_expr_e_ _ _ _ _ _ _ h_eval_expr_e_ h_match_env_).
      destruct h_transl_ as [v_t [? ?]] /sng.
      exists (e_t_v::x);repeat split;eauto.
      econstructor;eauto.
  - rew transl_paramexprlist_ok with
          functional inversion htrans_prmexprl;subst;
            match goal with
            | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
            end /sng.
    edestruct h_forall_spb_;clear h_forall_spb_;eauto /sng.
    + unfold push;simpl. reflexivity.
    + rename x0 into le_t.
      rename x into le_t_v.
      (* We need to show that [nm_t] can be evaluated to something.
         since [n_t] is the adresse of a variable of the program,
         by well_formedness/well_typedness it should correctly evaluate
         to an address.
         Here we can deduce it from the fact that in_out parameter are
         evaluated and it went well, so the variable was evaluated also in Cminor,
         so its address too. *)
      (* First some premisses for stack_match. *)
      assert (h_ex_:exists typ_nme, type_of_name st nm =: typ_nme).
      { admit. (* well typedness of the program? *) }
      destruct h_ex_ as [typ_nme ?]  /sng.
      assert (h_ex_:exists typ, transl_type st typ_nme =: typ).
      { admit. (* completness of type translation? *) }
      destruct h_ex_ as [typ ?] /sng.
      assert (h_ex_: exists load_addr_nme, make_load nm_t typ =: load_addr_nme).
      { admit. (* completness of make_load? *) }
      destruct h_ex_ as [load_addr_nme ?] /sng.
      up_type.
      assert (exists vaddr, eval_expr g (Values.Vptr spb ofs) locenv m nm_t vaddr) /sng.
      { eapply me_safe_cm_env with (1:=h_match_env_) ;eauto. }
      assert (h_stack_mtch_:=(me_stack_match h_match_env_)).
      red in h_stack_mtch_.
      destruct h_ex_ /sng.
      specialize h_stack_mtch_ with 
          (1:=heq_transl_name_)
          (2:=h_CM_eval_expr_nm_t_nm_t_v_)
          (3:=h_eval_name_nm_v_)(4:=heq_transl_type_)
          (5:=heq_type_of_name_) (6:=heq_make_load_). 

      destruct h_stack_mtch_ as [v_t [htrsl h_eval_]] /sng.
      up_type.
      (* Currently we only have by_value loads (but with arrays this may change) *)
      functional inversion heq_make_load_ /sng.
      subst.
      (* From [Cminor.eval_expr (Eload chunk x) v_t] we can deduce that [x] itself can be evaluated to a value. *)
      inversion h_CM_eval_expr_load_addr_nme_load_addr_nme_v_;subst /sng.
      exists (nm_t_v::le_t_v).
      constructor;auto.
  - rew transl_paramexprlist_ok with
       functional inversion htrans_prmexprl;subst;
       match goal with
       | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
       end /sng.
    edestruct h_forall_spb_;clear h_forall_spb_;eauto /sng.
    + unfold push;simpl. reflexivity.
    + rename x0 into le_t.
      rename x into le_t_v.
      (* We need to show that [n_t] can be evaluated to something.
         since [n_t] is the adresse of a variable of the program,
         by well_formedness/well_typedness it should correctly evaluate
         to an address.
         Here we can deduce it from the fact that in_out parameter are
         evaluated and it went well, so the variable was evaluated also in Cminor,
         so its address too. *)
      (* First some premisses for stack_match. *)
      assert (h_ex_:exists typ_nme, type_of_name st nm =: typ_nme).
      { admit. (* well typedness of the program? *) }
      destruct h_ex_ as [typ_nme ?]  /sng.
      assert (h_ex_:exists typ, transl_type st typ_nme =: typ).
      { admit. (* completness of type translation? *) }
      destruct h_ex_ as [typ ?] /sng.
      assert (h_ex_: exists load_addr_nme, make_load nm_t typ =: load_addr_nme).
      { admit. (* completness of make_load? *) }
      destruct h_ex_ as [load_addr_nme ?] /sng.
      up_type.
      assert (exists vaddr, eval_expr g (Values.Vptr spb ofs) locenv m nm_t vaddr) /sng.
      { eapply me_safe_cm_env with (1:=h_match_env_) ;eauto. }
      assert (h_stack_mtch_:=(me_stack_match h_match_env_)).
      red in h_stack_mtch_.
      destruct h_ex_ /sng.
      specialize h_stack_mtch_ with 
          (1:=heq_transl_name_)
          (2:=h_CM_eval_expr_nm_t_nm_t_v_)
          (3:=h_eval_name_nm_)(4:=heq_transl_type_)
          (5:=heq_type_of_name_) (6:=heq_make_load_). 

      destruct h_stack_mtch_ as [v_t [htrsl h_eval_]] /sng.
      up_type.
      (* Currently we only have by_value loads (but with arrays this may change) *)
      functional inversion heq_make_load_.
      subst.
      (* From [Cminor.eval_expr (Eload chunk x) v_t] we can deduce that [x] itself can be evaluated to a value. *)
      inversion h_CM_eval_expr_load_addr_nme_load_addr_nme_v_;subst /sng.
      exists (nm_t_v::le_t_v).
      constructor;auto.
  - up_type.
    rew transl_paramexprlist_ok with
       functional inversion htrans_prmexprl;subst;
       match goal with
       | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
       end /sng.
    edestruct h_forall_spb_;clear h_forall_spb_;eauto /sng.
    + unfold push;simpl. reflexivity.
    + rename x0 into le_t.
      rename x into le_t_v.
      (* We need to show that [nm_t] can be evaluated to something.
         since [nm_t] is the adresse of a variable of the program,
         by well_formedness/well_typedness it should correctly evaluate
         to an address. Even if it is not guaranteed that this address
         contains a value in the current case: (Out parameter). *)
      assert (h_ex_:∃ n_t_v, Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nm_t n_t_v).
      { eapply me_safe_cm_env with (1:=h_match_env_) ;eauto. }

      destruct h_ex_ as [? ?] /sng.
      exists (nm_t_v::le_t_v).
      constructor;auto.
Admitted.


Lemma repeat_Mem_loadv_cut:
  ∀ m n sp v,
  repeat_Mem_loadv AST.Mint32 m n sp v
  → ∀ n' n'',
      (n' + n'' = n)%nat
      → ∃ sp', repeat_Mem_loadv AST.Mint32 m n' sp sp'
               ∧ repeat_Mem_loadv AST.Mint32 m n'' sp' v.
Proof.
  intros until n' /sng.
  revert m n sp v h_repeat_loadv_n_sp_.
  induction n';cbn;!intros /sng.
  - subst.
    exists sp;split.
    + constructor.
    + assumption.
  - subst.
    inversion h_repeat_loadv_n_sp_ /sng.
    specialize (h_forall_m_ m (n' + n'')%nat sp' v h_repeat_loadv_ n'' eq_refl).
    decomp h_forall_m_.
    exists sp'0;split.
    + econstructor;eauto.
    + assumption.
Qed.

Lemma repeat_Mem_loadv_cut_mem_loadv :
  ∀ (m : mem) (n : nat) (sp : Values.val),
    chained_stack_structure m n sp
    → ∀ n' n'' (v : Values.val),
      (n' + n'' = n)%nat
      → repeat_Mem_loadv AST.Mint32 m n' sp v
      → chained_stack_structure m n''%nat v.
Proof.
  intros until n' /sng.
  revert m n sp h_chain_m_n_sp_.
  induction n';cbn;!intros /sng.
  - subst.
    inversion h_repeat_loadv_O_sp_ /sng.
    assumption.
  - inversion h_repeat_loadv_ /sng.
    eapply h_forall_m_ with (n:=(n' + n'')%nat);eauto.
    subst n.
    
    inversion h_chain_m_n_sp_ /sng.
    rewrite h_loadv_ in h_loadv_sp_sp'_.
    inversion h_loadv_sp_sp'_ /sng.
    assumption.
Qed.





(* inversion lemma that let the match lvlv with unresolved. *)
Lemma compilenv_inv:
  forall (stbl : symboltable) (enclosingCE : compilenv) (lvl : level)
         (lparams : list paramSpec) (decl : decl) res,
    build_compilenv stbl enclosingCE lvl lparams decl = Errors.OK res
    -> exists sto sz init_sto_sz fr_prm, res = (((Datatypes.length enclosingCE, sto)::enclosingCE),sz)
                                         /\ init_sto_sz = (nil, 4)
                                         /\ build_frame_lparams stbl init_sto_sz lparams = Errors.OK fr_prm
                                         /\ build_frame_decl stbl fr_prm decl = Errors.OK (sto, sz).
Proof.
  intros stbl enclosingCE lvl lparams decl res heq_bldCE_.
  rew build_compilenv_ok with functional inversion heq_bldCE_ /sng.
  eauto 10.
Qed.

(* Property linking spark args expr list , spark args value
           list , Cminor args expr list and Cminor args value list. We
           need to talk a bout expressions because Out and InOut
           parameters are translated into names (and not expressions)
           in order to be able to have there cminor address. Once the
           prelude of the function is executed, all variables are in
           the stack as standard variables. *)
(*
Section is_copy.
  Variables (stbl : symboltable) (CE : compilenv)   (g : genv) (sp : Values.val) (locenv : env) (m : mem) (s : stack).

  (* FIXME: copy_in ne doit pas prendre une liste de value, mais les calculer à
     la volée, car on ne peut pas faire autrement pour spécifier le Out. *)
  (** [is_copy_in le lprms lv_t] means that in the current environment, lev_t
      correspond to the values that should be stored in the local variables
      of a function having lprm as parameter list. That is: the value of the
      argument when In, its address otherwise (with the correct value at the
      address when In_Out).  *)

  Inductive is_copy_in: list exp -> list parameter_specification -> store -> list Values.val -> Prop :=
  | Is_copy_in_nil: forall sto, is_copy_in nil nil sto nil
  | Is_copy_in_In: ∀ e le prm lprm v sto sto' v_t lv_t,
      parameter_mode prm = In ->
      eval_expr stbl s e (OK v) ->
      transl_value v v_t ->
      is_copy_in le lprm (store_of sto) lv_t ->
      push sto (parameter_name prm) v = sto' ->
      is_copy_in (e::le) (prm::lprm) (store_of sto') (v_t::lv_t)
  | Is_copy_in_In_Out: ∀ ast_num nme le prm lprm v nme_t addr sto v_t lv_t,
      parameter_mode prm = In_Out ->
      evalName stbl s nme (OK v) ->
      transl_value v v_t ->
      transl_name stbl CE nme = OK nme_t ->
      Cminor.eval_expr g sp locenv m nme_t addr -> (* v_t is the value at address addr *)
      Mem.loadv AST.Mint32 m addr = Some v_t ->
      is_copy_in le lprm sto lv_t ->
      is_copy_in (E_Name ast_num nme ::le) (prm::lprm) ((parameter_name prm , v)::sto) (addr::lv_t).
(* TODO: Out parameters *)

End is_copy.
*)

(* Subst ignoring some variables. *)
Ltac subst_hide x :=
  match goal with
  | H: x = ?t |- _ => replace (x = t) with (id (x = t)) in H by reflexivity
  | H: ?t = x |- _ => replace (t = x) with (id (t = x)) in H by reflexivity
  end.

Ltac subst_unhide x :=
  match goal with
  | H: id (x = ?t) |- _ => replace (id (x = t)) with (x = t) in H by reflexivity
  | H: id (?t = x) |- _ => replace (id (t = x)) with (t = x) in H by reflexivity
  end.

(* All names (xi) to ignore are gathered in a product of Prop of the form xi=xi (to keep them in Prop).
   Probably we could gather them more like reame does.
 *)
Ltac subst_exc_l l tac :=
  match l with
  | Prop => tac
  | ((?v = ?v) -> ?l') => subst_hide v; subst_exc_l l' tac; subst_unhide v
  end.

(* I would rather have a subst -[x y z]. *)
Tactic Notation "subst_exc" ident(v1) :=
  subst_exc_l ((v1=v1) -> Prop) subst.
Tactic Notation "subst_exc" ident(v1) ident(v2) :=
  subst_exc_l ((v1=v1) -> (v2=v2) -> Prop) subst.
Tactic Notation "subst_exc" ident(v1) ident(v2) ident(v3) :=
  subst_exc_l ((v1=v1) -> (v2=v2) -> (v3=v3) -> Prop) subst.
Tactic Notation "subst_exc" ident(v1) ident(v2) ident(v3) ident(v4) :=
  subst_exc_l ((v1=v1) -> (v2=v2) -> (v3=v3) -> (v4=v4) -> Prop) subst.
Tactic Notation "subst_exc" ident(v1) ident(v2) ident(v3) ident(v4) ident(v5) :=
  subst_exc_l ((v1=v1) -> (v2=v2) -> (v3=v3) -> (v4=v4) -> (v5=v5) -> Prop) subst.
Tactic Notation "subst_exc" ident(v1) ident(v2) ident(v3) ident(v4) ident(v5) ident(v6) :=
  subst_exc_l ((v1=v1) -> (v2=v2) -> (v3=v3) -> (v4=v4) -> (v5=v5) -> (v6=v6) -> Prop) subst.


Definition wf_st st :=
  forall pnum lvl p decl,
    fetch_proc_ pnum st =Some (lvl, p) ->
    procedure_declarative_part p = decl ->
    ∀ i : AST.ident,
      List.In i (transl_decl_to_lident st decl) → i ≠ chaining_param.

Ltac rename_wf_st n th :=
  match th with
  | wf_st ?st => fresh "wf_st_" st
  | wf_st _ => fresh "wf_st"
  | _ => rename_hyp_decl n th
  end.
Ltac rename_sparkprf ::= rename_wf_st.

(* [transl_procsig] gives [f0,proc_lvl], so f0 is the result
   of a translation with the right CE. All procedures in
   memory are supposed to come from compilation. *)
Lemma transl_procsig_match_env_succeeds_:
  forall st s CE sp e g m pnum f0 proc_addr proc_lvl,
    wf_st st -> 
    match_env_ st s CE sp e g m -> 
    transl_procsig st pnum =: (funsig (AST.Internal f0), proc_lvl) ->
    eval_expr g sp e m (Econst (Oaddrsymbol (transl_procid pnum) (Ptrofs.repr 0))) proc_addr ->
    Globalenvs.Genv.find_funct g proc_addr = Some (AST.Internal f0) -> 
    ∃ CE_prfx CE_sufx pbdy X lotherproc,
      CompilEnv.cut_until CE proc_lvl CE_prfx CE_sufx /\
      fetch_proc_ pnum st = Some (proc_lvl,pbdy) /\
      transl_procedure st CE_sufx proc_lvl pbdy (* prov_lvl+1? *)
      = Errors.OK ((X, AST.Gfun (AST.Internal f0))::lotherproc) /\
      ∀ i : AST.ident,
        List.In i (transl_decl_to_lident st (procedure_declarative_part pbdy))
        → i ≠ chaining_param.
Proof.
  intros /sng.
  unfold transl_procsig in heq_transl_procsig_pnum_.
  assert (stack_match_functions_ st sp CE e g m) by eauto with spark /sng.
  red in h_stk_mtch_fun_.
  unfold symboltable.fetch_proc_ in h_stk_mtch_fun_.
  specialize (h_stk_mtch_fun_ pnum).
  destruct (fetch_proc_ pnum st) eqn:?;try discriminate /sng.
  destruct t /sng.
  specialize (h_stk_mtch_fun_ l p eq_refl).
  decomp h_stk_mtch_fun_.
  exists CE', CE''.
destruct 
  (transl_lparameter_specification_to_procsig
     st l (procedure_parameter_profile p)) eqn:?;try discriminate /sng.
simpl in heq_transl_procsig_pnum_.
invclear heq_transl_procsig_pnum_ /sng.
exists p, pnum0, lglobdef.
split;[ | split;[ | split]].
+ assumption.
+ reflexivity.
+ subst_det_addrstack_zero.
  rewrite heq_find_func_proc_addr_ in heq_find_func_paddr_fction_.
  invclear heq_find_func_paddr_fction_ /sng.
  assumption.
+ eapply h_wf_st_st_;eauto.
Qed.

(* This is not enough, proof fails at some point because we need to
prove everything at once: i.e. this + match_env_ preservation. We keep this half finished proof here for now to grab parts for the next one. *)
Lemma exec_preserve_invisible:
  ∀ g func stkptr locenv m stmt_t tr locenv' m' outc,
    exec_stmt g func stkptr locenv m stmt_t tr locenv' m' outc -> 
    ∀ st CE stmt s lvl,
      wf_st st ->
      lvl = Datatypes.length CE ->
      match_env_ st s CE stkptr locenv g m ->
      chained_stack_structure m lvl stkptr ->
      invariant_compile CE st ->
      transl_stmt st CE stmt =: stmt_t ->
      chained_stack_structure m' lvl stkptr
      ∧ forall astnum,
          (* eval_stmt st s stmt s' -> *)
          Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m'.
Proof.
  intros until 1 /sng.
  induction h_exec_stmt_stmt_t_outc_;!!intros;
    match goal with
  | H: transl_stmt ?st ?CE ?stmt = _ |- _ => 
    rew transl_stmt_ok with !!!functional inversion H
  end ;subst;
      (match goal with |- ?chstactctruct ∧ ?unch => assert (hstruc_m':chstactctruct);[ | split;[assumption|]] end);!intros /sng.
  (* Skip => chained_struct *)
  - assumption.
  (* Skip => unchanged on forbidden *)
  - apply Mem.unchanged_on_refl.
  (* Sstore => chained_struct *)
  - admit.
  (* Store => unchanged on forbidden *)
  - destruct addr_v;try discriminate. 
    up_type.
    simpl in heq_storev_a_v_m'_.
    eapply Mem.store_unchanged_on;eauto.
    intros /sng.
    intros [abs1 abs2].
    red in abs1.
    functional inversion heq_transl_name_;subst /sng.
    simpl in heq_compute_chnk_nme_.
    rewrite <- transl_variable_astnum with (a:=astnum) (1:=h_eq_transl_var_) in h_eq_transl_var_.
    specialize (abs1 id addr chunk b i h_eq_transl_var_ heq_compute_chnk_nme_ h_CM_eval_expr_addr_addr_v_). 
    destruct abs1.
    + apply H. reflexivity.
    + lia.
  (* Scall => chained_struct *)
  - specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_lvl_sp_) as ? /sng.
    decomp h_ex_;subst.
    (* Needs to deal with copyout and copyin, copyin is almost done
    but we must deal with the fact that when funcall starts, there is
    one single step where chainstructure is not true. this step is
    when the first argument (the address of the enclosing frame) is
    copied to the local stack. The effect of this step is to set
    chain_structure back again. *)
    admit.
  (* Scall => unchanged on forbidden *)
  - rename x into args_t.
    rename lexp into args.
(*     rename bl into all_args_t. *)
    rename a_v into proc_addr.
    rename fd into proc_value.
    rename y into proc_lvl.
    inversion h_evalfuncall_fd_vargs_vres_;subst /sng.
    + (* internal function *)
      specialize transl_procsig_match_env_succeeds_ with (1:=h_wf_st_st_) (2:=h_match_env_) (3:=heq_transl_procsig_pnum_) (4:=h_CM_eval_expr_a_a_v_) (5:=heq_find_func_a_v_fd_) as ? /sng.
      decomp h_ex_;up_type.
      rename h_forall_i_ into h_pbdy_chainarg_noclash_.
      rew transl_procedure_ok with
        functional inversion heq_transl_proc_pbdy_;up_type /sng.
      rename x3 into initparams.
      rename x2 into locvarinit.
      rename x1 into bdy.
      rename x4 into copyout.
      subst.
      rename proc_t into pbody_t.
      set (proc_t := {|
                      fn_sig := x5;
                      fn_params := chaining_param :: tlparams;
                      fn_vars := transl_decl_to_lident st decl0;
                      fn_stackspace := y;
                      fn_body := pbody_t |}) in *.
      rename x into CE_proc.
      rename y into proc_sz_locals.
      up_type.
      cbn [ proc_t fn_vars fn_params fn_body pbody_t] in h_exec_stmt_.

      (* Stating relation between CE and CE_prfx ++ CE_sufx *)
      assert (CE = CE_prfx ++ CE_sufx) /sng. { 
        erewrite CompilEnv.cut_until_spec1;eauto. }
      subst CE.
      set (CE:=CE_prfx ++ CE_sufx) in *.

      (* thus CE_sufx preserves the invariant. *)
      assert (invariant_compile CE_proc st) /sng.
      { rew build_compilenv_ok with functional inversion heq_build_compilenv_ /sng.
        eapply build_compilenv_preserve_invariant_compile;eauto.
        eapply invariant_compile_sublist.
        erewrite CompilEnv.cut_until_spec1;eauto. }
        
      (* splitting the execution of proc in 5: chain_param, initparam, initlocvar, bdy and cpout. *)
      inversion_clear h_exec_stmt_;subst /sng.
      2: admit. (* prematurate error, this should work with parts of the normal case *)
      inversion_clear h_exec_stmt_;subst /sng.
      2: admit. (* prematurate error, this should work with parts of the normal case *)
      inversion_clear h_exec_stmt_;subst /sng.
      2: admit. (* prematurate error, this should work with parts of the normal case *)
      inversion_clear h_exec_stmt0_;subst /sng.
      2: admit. (* prematurate error, this should work with parts of the normal case *)

      * (* RENAMING *)
        (* Case where No error occured during the whole function call *)
        rename h_exec_stmt_ into h_exec_stmt_init_.
        match goal with
        | H: exec_stmt _ _ _ _ ?ma chain_param _ ?e ?mb _ |- _ =>
          rename mb into m_chain; rename e into e_chain;
            rename ma into m_pre_chain
        end.
        match goal with
        | H: exec_stmt _ _ _ _ _ initparams _ ?e ?mb _ |- _ =>
          rename mb into m_init_params;rename e into e_initparams;
            rename H into h_exec_stmt_initparams_
        end.
        match goal with
        | H: exec_stmt _ _ _ _ _ (Sseq locvarinit Sskip) _ ?e ?mb _ |- _ => 
          rename mb into m_locvarinit; rename e into e_locvarinit;
            rename H into h_exec_stmt_locvarinit_
        end.
        match goal with
        | H: exec_stmt _ _ _ _ _ bdy _ ?e ?mb _ |- _ => 
          rename mb into m_bdy; rename e into e_bdy
        end.
        match goal with
        | H: exec_stmt _ _ _ _ _ copyout _ ?e ?mb _ |- _ => 
          rename mb into m_cpout; rename e into e_cpout
        end.
        (* END RENAMING *)
        set (sp_proc := Values.Vptr sp0 Ptrofs.zero) in *.
        up_type.
        assert (Mem.unchanged_on (forbidden st CE g astnum e sp m m_chain) m m_pre_chain) /sng.
        { (* Lemma about invisible and alloc. *)
          eapply Mem.alloc_unchanged_on.
          eauto. }
        (* (pose proof strong_match_env_match_env_sublist_ _ _ _ _ _ _ _ h_strg_mtch_s_CE_m_ *)
                (* h_inv_comp_CE_st_ _ _ _ h_CEcut_CE_proc_lvl_) /sng. *)
        (* destruct h_ex_ as [s' [s'' [sp'' [? [? h_mtchenv_]]]]] /sng. *)
         (* well formedness: one can call only visible procedures,
            i.e. of level at most (current level) + 1, where current level
            is |CE|-1, hence: *)
        assert (proc_lvl<=Datatypes.length CE)%nat /sng.
        { admit. }

        assert (proc_lvl = Datatypes.length CE_sufx)%nat.
        { assert (CompilEnv.exact_levelG CE) by eauto with spark /sng.
          eapply CompilEnv.cut_until_exact_levelG;eauto. }
        subst proc_lvl.

        assert (exists sp'' , repeat_Mem_loadv AST.Mint32 m (Datatypes.length CE - Datatypes.length CE_sufx)%nat sp sp'') /sng.
        { unfold addr_enclosing_frame in h_CM_eval_exprl_bl_vargs_.
          inversion h_CM_eval_exprl_bl_vargs_;subst /sng.
          
          rewrite <- chain_repeat_loadv in h_CM_eval_expr_v1_.
          - eauto.
          - unfold current_lvl.
            eapply chained_stack_structure_le;eauto.
            lia. }
        decomp h_ex_.
        assert (chained_stack_structure m (Datatypes.length CE_sufx) sp'') /sng.
        { eapply repeat_Mem_loadv_cut_mem_loadv  with (1:=h_chain_m_lvl_sp_)
                 (n':=(Datatypes.length CE - Datatypes.length CE_sufx)%nat).
          - lia.
          - assumption. }
        assert (Datatypes.length CE_proc = S (Datatypes.length CE_sufx)) as heq_lgth_CE_proc_.
        { rew build_compilenv_ok with functional inversion heq_build_compilenv_.
          reflexivity. }
        (* Since the chaining param is not the translation of a spark
           variable, we stay in callers environment, that is: from
           m_pre_chain to m_chain there is no change in the addresses
           visible in m. *)
        assert (Mem.unchanged_on (forbidden st CE g astnum e sp m m_chain) m_pre_chain m_chain) /sng.
        { unfold chain_param in h_exec_stmt_chain_param_Out_normal_.
          inversion h_exec_stmt_chain_param_Out_normal_ /sng.
          unfold Mem.storev in heq_storev_v_m_chain_.
          destruct vaddr;try discriminate.
          apply Mem.store_unchanged_on with (1:=heq_storev_v_m_chain_).
          intros /sng.
          unfold sp_proc in h_CM_eval_expr_vaddr_.
          destruct h_and_ /sng.
          inversion h_CM_eval_expr_vaddr_;subst /sng.
          cbn in h_eval_constant_.
          inversion h_eval_constant_;subst /sng.
          intro abs. red in abs. destruct abs as [abs1 abs2].
          red in abs2.
          apply abs2.
          red.
          intro.
          eapply fresh_block_alloc_perm_;eauto. }
        (* the new sp (sp') has zero offset. *)
        specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_) as h_ex_ /sng.
        decomp h_ex_.
        subst sp'' .
        set (sp'' := Values.Vptr b' Ptrofs.zero).
        up_type.
        assert (chained_stack_structure m_pre_chain (Datatypes.length CE_sufx) (Values.Vptr b' Ptrofs.zero)) /sng.
        { eapply malloc_preserves_chained_structure;eauto. }

        assert(chained_stack_structure m_chain (Datatypes.length CE_sufx) (Values.Vptr b' Ptrofs.zero)) /sng.
        { inversion heq_lgth_CE_proc_;clear heq_lgth_CE_proc_ /sng.
(*           rewrite <- heq_all_args_t_ in h_CM_eval_exprl_bl_vargs_. *)
          inversion h_CM_eval_exprl_bl_vargs_ /sng.
          unfold chain_param in h_exec_stmt_chain_param_Out_normal_.
          inversion h_exec_stmt_chain_param_Out_normal_ /sng.
          unfold sp_proc in h_CM_eval_expr_vaddr_.
          repeat subst_det_addrstack_zero.
          eapply storev_outside_struct_chain_preserves_chained_structure with (m:=m_pre_chain) (g:=g)(e:=e) (sp0:=sp0).
          + intros /sng.
            assert (n < Datatypes.length CE_sufx)%nat by lia /sng.
            pose proof malloc_distinct_from_chaining_loads _ _ _ h_chain_m_ n _ _ _ h_malloc_m_m1_ e g h_lt_n_ b'0 /sng.
            apply h_impl_neq_b'0_.
            eapply malloc_preserves_chaining_loads_2;eauto.
            eapply chained_stack_structure_le;eauto;lia.
          + assumption.
          + eassumption. }
          
        assert (chained_stack_structure m_chain (S (Datatypes.length CE_sufx)) sp_proc) /sng.
        { inversion heq_lgth_CE_proc_;clear heq_lgth_CE_proc_ /sng.
(*           rewrite <- heq_all_args_t_ in h_CM_eval_exprl_bl_vargs_. *)
          inversion h_CM_eval_exprl_bl_vargs_ /sng.
          unfold chain_param in h_exec_stmt_chain_param_Out_normal_.
          inversion h_exec_stmt_chain_param_Out_normal_ /sng.
          inversion h_CM_eval_expr_v_ /sng.
          cbn [set_params] in heq_mget_chaining_param_v_.          
          rewrite map_get_set_same_nodup in heq_mget_chaining_param_v_;auto.
          assert (chained_stack_structure m (Datatypes.length CE - Datatypes.length CE_sufx) sp) /sng.
          { eapply chained_stack_structure_le;eauto;lia. }
          pose proof chain_repeat_loadv_1 _ _ _ h_chain_m0_ _ g e h_repeat_loadv_.
          rewrite heq_length_.
          apply chained_S with (b':=b').
          - pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m0_ /sng.
            decomp h_ex_.
            unfold sp_proc in h_CM_eval_expr_vaddr_.
            repeat subst_det_addrstack_zero.
            eapply storev_outside_struct_chain_preserves_chained_structure with (m:=m_pre_chain) (g:=g)(e:=e) (sp0:=sp0).
            + intros /sng.
              assert (n < Datatypes.length CE_sufx)%nat by lia /sng.
              pose proof malloc_distinct_from_chaining_loads _ _ _ h_chain_m_ n _ _ _ h_malloc_m_m1_ e g h_lt_n_ b'1 as h_alloc_diff_ /sng.
              apply h_impl_neq_b'1_.
              eapply malloc_preserves_chaining_loads_2;eauto.
              eapply chained_stack_structure_le;eauto;lia.
            + assumption.
            + eassumption.

          (* malloc + store didnt change chaingin struct. *)
          - unfold sp_proc in *.
            repeat  subst_det_addrstack_zero.
            cbn in heq_storev_v_m_chain_ |- * .
            rewrite (Mem.load_store_same _ _ _ _ _ _ heq_storev_v_m_chain_).
            inversion heq_mget_chaining_param_v_.
            reflexivity. }

        (* This is from m_chain only. *)
        (* TODO: prove that (forbidden m_chain m_chain) x y <=>
        (forbidden m m_chain) x y, everything that is visible from
        m_chain is either visible from m or free from m. *)
        assert (Mem.unchanged_on (forbidden st CE_proc g astnum e_chain sp_proc m_chain m_chain) m_chain m_init_params
                 ∧ chained_stack_structure m_init_params (Datatypes.length CE_proc) sp_proc
                 ∧ unchange_forbidden st CE_proc g astnum e_chain e_initparams sp_proc m_chain m_init_params) /sng.
        { eapply init_params_preserves_structure;eauto with spark.
          - eapply build_compilenv_stack_no_null_offset with (CE:=CE_sufx).
            + eapply exact_lvlG_cut_until with (CE:=CE) ;eauto with spark.
            + eapply no_overflow_NoDup_G_cut with (CE:=CE);eauto with spark.
            + eapply no_null_offset_NoDup_G_cut with (CE:=CE); eauto with spark.
            + eassumption.
          - admit. (* TODO *)

          - (* after chaining is done the stkptr of the procedure points to an aligned stack  *)
            (* i.e. malloc+chaining link preserve stack_localstack_aligned. *)
            move pbody_t after t5.
            move chain_param after t5.
            move sp_proc after t5.
            move current_lvl after t5.
            move tlparams after t5.
            set (initlocenv:= set_locals (transl_decl_to_lident st decl0)
                                         (set_params vargs (chaining_param :: tlparams))) in *|- *.
            move initlocenv after proc_t.
            assert (stack_localstack_aligned (Datatypes.length CE_sufx) e g m sp'') /sng.
            { eapply chain_aligned;eauto. }
            red.
            intros /sng.
            destruct δ_lvl.
            + cbn. (* the new procedure stkptr is aligned. *)
              eexists.
              eapply cm_eval_addrstack_zero.
            + unfold sp_proc. (* The stckptr of enclosing procedure are aligned (they did not change). *)
              (*First prove that after one load we are back on sp''.*)
              (* Then prove that nothing visible from there has change (use unchanged_on forbidden hyps)  *)
              red in h_aligned_g_m_.
              assert (δ_lvl ≤ Datatypes.length CE_sufx) /sng.
              { rew build_compilenv_ok with
                  functional inversion heq_build_compilenv_.
                cbn in h_le_δ_lvl_.
                lia. }
              specialize (h_aligned_g_m_ _ h_le_δ_lvl0_).
              decomp h_aligned_g_m_.
(*               unfold chaining_arg in *. *)
(*               inversion heq;clear heq /sng. *)
(*               rewrite <- heq_all_args_t_ in h_CM_eval_exprl_bl_vargs_. *)
              inversion h_CM_eval_exprl_bl_vargs_ /sng.
              unfold initlocenv,chain_param in h_CM_eval_expr_addr_enclosing_frame_addr_enclosing_frame_v_.
              inversion h_exec_stmt_chain_param_Out_normal_ /sng.
              unfold current_lvl in *.
              (* needed by the next lia. *)
              unfold sp_proc in h_CM_eval_expr_vaddr_.
              subst_det_addrstack_zero.
              (* cleaning + recollecting all the occurrencies. *)
              subst sp_proc.
              set (sp_proc:=(Values.Vptr sp0 Ptrofs.zero)) in *|-*.
(*               subst initlocenv. *)
              set (initlocenv := set_locals (transl_decl_to_lident st decl0) (set_params (addr_enclosing_frame_v :: vl) (chaining_param :: tlparams))) in *|-*.
              set (whole_trace := (Events.Eapp Events.E0 (Events.Eapp (Events.Eapp t2 t4) (Events.Eapp t0 t5)))) in *|-* .
              up_type.
              (* end cleaning *)
              (* load sp_proc (S δ_lvl) gives the same as load sp'' δ_lvl, i.e. b_δ. *)
              exists b_δ.
              (* first change the locenv (does not influence a load anyway). *)
              apply eval_expr_build_load_const_inv_locenv with (locenv:=e).

              assert (chained_stack_structure m δ_lvl sp'') /sng.
              { assert(δ_lvl ≤ Datatypes.length CE) /sng.
                { transitivity (Datatypes.length CE_sufx).
                  - assumption.
                  - rewrite <- (CompilEnv.cut_until_spec1 _ _ _ _ h_CEcut_CE_proc_lvl_).
                    rewrite app_length.
                    lia. }
                apply chained_stack_structure_le with (n:=Datatypes.length CE_sufx);eauto. }
              assert (chained_stack_structure m_chain (S δ_lvl) sp_proc) /sng.
              { pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_δ_lvl_sp''_ /sng.
                decomp h_ex_.
                subst sp'' .
                inversion h_CM_eval_expr_v_ /sng.
                unfold initlocenv in heq_mget_chaining_param_initlocenv_v_.
                assert ( Maps.PTree.get chaining_param
                                         (set_locals (transl_decl_to_lident st decl0) (Maps.PTree.set chaining_param addr_enclosing_frame_v (set_params vl tlparams)))
                          = Some addr_enclosing_frame_v) /sng.
                { eapply map_get_set_same_nodup.
                  intros /sng.
                  eapply h_pbdy_chainarg_noclash_.
                  cbn.
                  assumption. }
                subst chain_param.
                (* subst chaining_arg. *)
                cbn [set_params] in heq_mget_chaining_param_initlocenv_v_.
                rewrite heq_mget_chaining_param_initlocenv_v_ in heq_mget_chaining_param_addr_enclosing_frame_v_.
                invclear heq_mget_chaining_param_addr_enclosing_frame_v_ /sng.
                assert (chained_stack_structure m (Datatypes.length CE - Datatypes.length CE_sufx) sp) /sng.
                { eapply chained_stack_structure_le;eauto;lia. }
                specialize chain_repeat_loadv_1 with (1:=h_chain_m0_) (2:=h_repeat_loadv_) as h.
                apply chained_S with (b':=b').
                - assert (chained_stack_structure m_pre_chain  δ_lvl (Values.Vptr b' Ptrofs.zero)) /sng.
                  { eapply malloc_preserves_chained_structure;eauto. }
                  pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_δ_lvl_sp''_ /sng.
                  decomp h_ex_.
                  eapply storev_outside_struct_chain_preserves_chained_structure with (m:=m_pre_chain) (g:=g)(e:=e) (sp0:=sp0).
                  + intros /sng.
                    assert (n < Datatypes.length CE_sufx)%nat by lia /sng.
                    specialize malloc_distinct_from_chaining_loads
                      with (1:=h_chain_m_δ_lvl_sp''_) (2:=h_malloc_m_m1_) (3:=h_lt_n_δ_lvl_) (b':=b'2)
                      as h_b'2_sp0_. 
                    eapply h_b'2_sp0_.
                    eapply malloc_preserves_chaining_loads_2;eauto.
                    eapply chained_stack_structure_le;eauto;lia.
                  + assumption.
                  + eassumption.

                (* malloc + store didnt change chaingin struct. *)
                - unfold sp_proc in *.
                  assert ((Values.Vptr b' Ptrofs.zero) = addr_enclosing_frame_v).
                  { eapply det_eval_expr ;eauto. }
                  subst.
                  cbn in heq_storev_v_m_chain_ |-* .
                  rewrite (Mem.load_store_same _ _ _ _ _ _ heq_storev_v_m_chain_).
                  reflexivity. }
              eapply chained_stack_structure_decomp_S_2' with (sp':=sp'').
              * assumption.
              * econstructor;  (* one load goes to sp'' *) 
                  auto.
                -- eapply cm_eval_addrstack_zero_chain;eauto.
                -- cbn in heq_storev_v_m_chain_ |- *.
                   assert (v = sp'') /sng.
                   { 
                     transitivity addr_enclosing_frame_v.
                     - subst sp_proc.
                       inversion h_CM_eval_expr_v_ /sng.
(*                        unfold initlocenv in heq0. *)
                       unfold initlocenv in heq_mget_chaining_param_initlocenv_v_.
                       rewrite map_get_set_locals_diff in heq_mget_chaining_param_initlocenv_v_.
                       2: admit. (* chaingin_param not in decl *)
                       cbn [set_params] in heq_mget_chaining_param_initlocenv_v_.
                       rewrite Maps.PTree.gss in heq_mget_chaining_param_initlocenv_v_.
                       inversion heq_mget_chaining_param_initlocenv_v_.
                       reflexivity.
                     - apply chain_repeat_loadv with (g:=g)(e:=e) in h_repeat_loadv_.
                       + subst_det_addrstack_zero.
                         reflexivity.
                       + eapply chained_stack_structure_le;eauto;lia. }
                   subst.
                   apply Mem.load_store_same in heq_storev_v_m_chain_.
                   unfold Values.Val.load_result in heq_storev_v_m_chain_.
                   specialize match_env_sp_zero_ with (1:=h_match_env_) as ? /sng.
                   decomp h_ex_.
                   subst sp''.
                   assumption.
              * (* between m and m_chain we made one malloc and only wrote in that malloc, thus
                   the part of memory covered by build_loads from sp'' has not changed.
                   Actually it suffices that chainging addresses (from sp'', not from sp_proc)
                   are untouched, which is true since it is forbidden. *)
                  (* from sp'' nothing changed so eval_expr gives the same result. *)
                  (* (build_loads (Oaddrstask 0)) is a chaingin address, so no variable points to it, so invisible, so unchanged. *)

                (* sp'' is actuall of the form (Vptr sp''b Zero) *)
                specialize match_env_sp_zero_ with (1:=h_match_env_) as ? /sng.
                destruct h_ex_ /sng.
                rename x into sp''b.
                assert (chained_stack_structure m δ_lvl sp'') /sng.
                { apply chained_stack_structure_le with (n:=Datatypes.length CE_sufx).
                  eapply repeat_Mem_loadv_cut_mem_loadv with (1:=h_chain_m_lvl_sp_) (n':=(Datatypes.length CE - Datatypes.length CE_sufx)%nat).
                  - assert(δ_lvl ≤ Datatypes.length CE) /sng.
                    { transitivity (Datatypes.length CE_sufx).
                      - assumption.
                      - rewrite <- (CompilEnv.cut_until_spec1 _ _ _ _ h_CEcut_CE_proc_lvl_).
                        rewrite app_length.
                        lia. }
                    lia.
                  - assumption.
                  - assumption. }

                assert (chained_stack_structure m_pre_chain δ_lvl sp'') /sng.
                { eapply malloc_preserves_chained_structure;eauto. }

                (* all sp (but the last which points to nothing), are different from sp0
                   because sp0 comes from a malloc. *)
                eapply storev_outside_struct_chain_preserves_chaining with (m:=m_pre_chain) (lvl:=δ_lvl)(sp0:=sp0).
                -- (* sp'' points to a structure unchanged by the malloc. *)
                  intros /sng.
                  specialize malloc_distinct_from_chaining_loads with (1:=h_chain_m_δ_lvl_sp''_) (2:=h_malloc_m_m1_) as h_b'_sp0_.
                  assert (Cminor.eval_expr g sp'' e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) (Values.Vptr b'0 Ptrofs.zero)) /sng.
                  { eapply malloc_preserves_chaining_loads_2 with (1:=h_malloc_m_m1_);eauto.
                    eapply chained_stack_structure_le;eauto.
                    lia. }
                  eapply h_b'_sp0_;eauto.
                -- assumption.
                -- unfold sp_proc in heq_storev_v_m_chain_. eassumption.
                -- auto with arith.
                -- (* This is true for m, and malloc does not change it so it is also true for m_pre_chain *) 
                  eapply malloc_preserves_chaining_loads with (1:=h_malloc_m_m1_);eauto. }

        decomp h_and_.

        (* changing the caller in forbidden. *)
        assert (Mem.unchanged_on (forbidden st CE_proc g astnum e_chain sp_proc m m_chain) m_chain m_init_params) /sng.
        { eapply mem_unchanged_on_mon with (P:=(forbidden st CE_proc g astnum e_chain sp_proc m_chain m_chain));try assumption.
          intros /sng.
          unfold forbidden in h_forbid_m_m_chain_x_y_ |- *.
          decomp h_forbid_m_m_chain_x_y_.
          split;auto.
          intro abs.
          unfold is_free_block in h_neg_free_blck_m_x_y_, abs.
          apply h_neg_free_blck_m_x_y_.
          intros /sng.
          intro abs'.
          apply (abs perm).
          (* splitting in m -> m_pre_chain  -> m_chain *)
          assert (Mem.perm m_pre_chain x y Cur perm).
          { eapply Mem.perm_alloc_1 with (m1:=m);eauto. }
          inversion h_exec_stmt_chain_param_Out_normal_ /sng.
          unfold sp_proc in h_CM_eval_expr_vaddr_.
          subst_det_addrstack_zero.
          unfold Mem.storev in heq_storev_v_m_chain_.
          eapply Mem.perm_store_1 with (m1:=m_pre_chain);eauto. }
        clear h_unchanged_on_m_chain_m_init_params_.
        autorename h_unchanged_on_m_chain_m_init_params0_.
          
        assert (Mem.unchanged_on (forbidden st CE_proc g astnum e_initparams sp_proc m_init_params m_init_params) m_init_params m_locvarinit
                ∧ chained_stack_structure m_locvarinit (S (Datatypes.length CE_sufx)) sp_proc
                ∧ unchange_forbidden st CE_proc g astnum e_initparams e_locvarinit sp_proc m_init_params m_locvarinit).
        { inversion h_exec_stmt_locvarinit_;eq_same_clear /sng.
          inversion h_exec_stmt_Sskip_Out_normal_ /sng.
          eapply init_locals_preserves_structure.
          - eapply build_compilenv_exact_lvl with (2:=heq_build_compilenv_) ;eauto.
            eapply exact_lvlG_cut_until with (CE:=CE);eauto with spark.
          - eapply build_compilenv_stack_no_null_offset with (4:=heq_build_compilenv_);eauto.
            + eapply exact_lvlG_cut_until with (CE:=CE);eauto with spark.
            + eapply no_overflow_NoDup_G_cut with (CE:=CE);eauto with spark.
            + eapply no_null_offset_NoDup_G_cut with (CE:=CE);eauto with spark.
          - apply h_inv_comp_CE_proc_st_.
          - eassumption.
          - assumption.
          - rewrite <- heq_lgth_CE_proc_. assumption.
          - eapply chain_aligned.
            + eassumption.
            + lia.
          - eassumption. }

        assert (Mem.unchanged_on (forbidden st CE_proc g astnum e_locvarinit sp_proc m_locvarinit m_locvarinit)
                                 m_locvarinit m_bdy).
        { admit. }
        assert (Mem.unchanged_on (forbidden st CE_proc g astnum e_locvarinit sp_proc m_bdy m_bdy)
                                 m_bdy m_cpout).
        { admit. }

        

        admit. (* associativity of unchanged_on? No, more
                                complex: the unchanged_on on the body part
                                correpsond to either visible parts from sp or from
                                freeed space (outcome_free_mem m2 ... m'). *)
    + (* functional inversion would be cleaner here. *)
      admit. (* No External function *)
  - destruct b.
    + eapply h_forall_st_;eauto.
    + eapply h_forall_st_;eauto.
  - destruct b.
    + eapply h_forall_st_;eauto.
    + eapply h_forall_st_;eauto.
  - specialize h_forall_st_
      with (1:=h_wf_st_st_) (2:=eq_refl _) (3:=h_match_env_)
           (4:=h_chain_m_lvl_sp_) (5:=h_inv_comp_CE_st_) (6:=heq_transl_stmt0_).
    destruct h_forall_st_ as [ ? h_unch_on1_] /sng.
    (* Needing match_env_ preserved here. *)
    specialize h_forall_st0_
      with (1:=h_wf_st_st_) (2:=eq_refl _)
           (4:=h_chain_m1_) (5:=h_inv_comp_CE_st_) (6:=heq_transl_stmt_).
    (* assert (match_env_ st s CE sp e1 g m1). *)
    admit.
  (* specialize (h_forall_st2_ _ _ _ _ ?  heq0). *)
  (* transitivity of unchanged_on is proved in recent
     Compcert, by changing its definition. *)

  - assert (chained_stack_structure m1 (Datatypes.length CE) sp
             ∧ (∀ astnum : ast_basics.astnum, Mem.unchanged_on (forbidden st CE g astnum e sp m m) m m1)) /sng.
    { eapply h_forall_st_;eauto. }
    assert (chained_stack_structure m2 (Datatypes.length CE) sp
             ∧ (∀ astnum : ast_basics.astnum, Mem.unchanged_on (forbidden st CE g astnum e1 sp m1 m1) m1 m2)) /sng.
    { eapply h_forall_st0_;eauto.
      - admit. (* need to enrich the property. *)
      - eapply h_forall_st_;eauto. }
    eapply trans_unchanged with m1.
    + eapply h_and_.
    + admit.
  - eapply h_forall_st_;eauto.
  - eapply h_forall_st_;eauto.
  
Admitted.



Lemma malloc_preserves_is_non_free : forall n1 n2 spb m m',
    Mem.alloc m n1 n2 = (m', spb) ->
    forall addr ofs , 
      ¬ is_free_block m addr ofs ->
      ¬ is_free_block m' addr ofs.
Proof.
  intros /sng.
  intro abs.
  apply h_neg_free_blck_m_addr_ofs_.
  unfold is_free_block in *.
  intro.
  intro abs2.
  apply abs with perm.
  eapply Mem.perm_alloc_1;eauto.
Qed.
Lemma storev_preserves_is_non_free : forall chk m vaddr v m',
    Mem.storev chk m vaddr v = Some m' ->
    forall addr ofs , 
      ¬ is_free_block m addr ofs ->
      ¬ is_free_block m' addr ofs.
Proof.
  unfold is_free_block.
  intros /sng.
  destruct vaddr;eauto;try discriminate.
  intro abs.
  apply h_neg_forall_perm_.
  intros /sng.
  intro abs2.
  apply abs with perm.
  eapply Mem.perm_store_1;eauto.
Qed.

Lemma exact_lvl_transl_variable_empty_top: forall st astnum pb_lvl CE_sufx nme nme_t,
    CompilEnv.exact_levelG ((pb_lvl, [ ]) :: CE_sufx)
    -> transl_variable  st ((pb_lvl, [ ]) :: CE_sufx) astnum nme =: nme_t
    -> exists δ n, nme_t = (build_loads (S δ) n)
                   ∧ (transl_variable st CE_sufx astnum nme =: build_loads δ n).
Proof.
  intros /sng.
  functional inversion h_eq_transl_var_;subst /sng.
  cbn in *.
  invclear heq_lvloftop_m'_ /sng.
  assert (lvl_nme < m')%nat /sng. {
    inversion h_exct_lvlG_ /sng.
    eapply CompilEnv.exact_levelG_frameG_lt_lgth;eauto. }
  exists (m' - lvl_nme -1)%nat.
  exists δ_nme.
  split.
  - f_equal.
    lia.
  - unfold transl_variable.
    rewrite heq_CEfetchG_nme_,heq_CEframeG_nme_.
    assert (CompilEnv.level_of_top CE_sufx = Some (Datatypes.length CE_sufx - 1))%nat /sng. {
      eapply foo.
      - intro abs.
        subst.
        simpl in heq_CEfetchG_nme_.
        discriminate.
      - inversion h_exct_lvlG_;auto. }
    rewrite heq_lvloftop_CE_sufx_.
    assert (m' = Datatypes.length CE_sufx) /sng. {
      inversion h_exct_lvlG_;subst;auto. }
    subst.
    f_equal.
    f_equal.
    lia.
Qed.

Lemma exact_lvl_transl_name_empty_top: forall st pb_lvl CE_sufx nme nme_t,
    CompilEnv.exact_levelG ((pb_lvl, [ ]) :: CE_sufx)
    -> transl_name st ((pb_lvl, [ ]) :: CE_sufx) nme =: nme_t
    -> exists δ n, nme_t = (build_loads (S δ) n)
                   ∧ (transl_name st CE_sufx nme =: build_loads δ n).
Proof.
  intros /sng.
  functional inversion heq_transl_name_;subst /sng.
  eapply exact_lvl_transl_variable_empty_top;eauto.
Qed.

Lemma copy_in_cons:
  ∀ st bigs lprmSpec l_exp_args lvl sto l,
    copyIn st bigs (lvl,sto) lprmSpec l_exp_args (OK (lvl, l)) ->
    exists l' : ST.store,
      l = l' ++ sto
      ∧ Datatypes.length lprmSpec = Datatypes.length l'
      ∧ ∀ ll, copyIn st bigs (lvl,ll) lprmSpec l_exp_args (OK (lvl, l' ++ ll)).
Proof.
  intros until 1 /sng.
  remember (lvl,sto) as x.
  remember (OK (lvl, l)) as x'.
  revert l lvl sto Heqx Heqx'.
  autorename h_copy_in_.
  induction h_copy_in_x_x'_;!intros;subst;unfold ST.push in *; simpl in *; try discriminate /sng.
  - invclear heq_OK_ /sng.
    exists nil;split;[|split];auto.
    intros /sng.
    simpl.
    constructor.
  - rename h_forall_l_ into IHh_copy_in_x_x'_.
    specialize IHh_copy_in_x_x'_ with (2:=eq_refl)(1:=eq_refl).
    decomp IHh_copy_in_x_x'_ /sng.
    exists (l' ++ [(parameter_name param, e_v)]).
    rewrite <- app_assoc;simpl.
    split;[|split].
    + reflexivity.
    + rewrite heq_length_.
      rewrite app_length;simpl.
      rewrite Nat.add_1_r;auto.
    + intros /sng.
      specialize h_forall_ll_ with (ll:=(parameter_name param, e_v) :: ll).
      rewrite  <- app_assoc.
      simpl.
      econstructor 3;eauto.
  - rename h_forall_l_ into IHh_copy_in_x_x'_.
    specialize IHh_copy_in_x_x'_ with (2:=eq_refl)(1:=eq_refl).
    decomp IHh_copy_in_x_x'_ /sng.
    exists (l' ++ [(parameter_name param, Int v)]).
    rewrite <- app_assoc;simpl.
    split;[|split].
    + reflexivity.
    + rewrite heq_length_.
      rewrite app_length;simpl.
      rewrite Nat.add_1_r;auto.
    + intros /sng.
      specialize h_forall_ll_ with (ll:=(parameter_name param, Int v) :: ll).
      rewrite  <- app_assoc.
      simpl.
      econstructor 5;eauto.
  - rename h_forall_l_ into IHh_copy_in_x_x'_.
    specialize IHh_copy_in_x_x'_ with (2:=eq_refl)(1:=eq_refl).
    decomp IHh_copy_in_x_x'_ /sng.
    exists (l' ++ [(parameter_name param, v)]).
    rewrite <- app_assoc;simpl.
    split;[|split].
    + reflexivity.
    + rewrite heq_length_.
      rewrite app_length;simpl.
      rewrite Nat.add_1_r;auto.
    + intros /sng.
      specialize h_forall_ll_ with (ll:=(parameter_name param, v) :: ll).
      rewrite  <- app_assoc.
      simpl.
      econstructor 7;eauto.
  - rename h_forall_l_ into IHh_copy_in_x_x'_.
    specialize IHh_copy_in_x_x'_ with (2:=eq_refl)(1:=eq_refl).
    decomp IHh_copy_in_x_x'_ /sng.
    exists (l' ++ [(parameter_name param, Int v)]).
    rewrite <- app_assoc;simpl.
    split;[|split].
    + reflexivity.
    + rewrite heq_length_.
      rewrite app_length;simpl.
      rewrite Nat.add_1_r;auto.
    + intros /sng.
      specialize h_forall_ll_ with (ll:=(parameter_name param, Int v) :: ll).
      rewrite  <- app_assoc.
      simpl.
      econstructor 9;eauto.
  - rename h_forall_l_ into IHh_copy_in_x_x'_.
    specialize IHh_copy_in_x_x'_ with (2:=eq_refl)(1:=eq_refl).
    decomp IHh_copy_in_x_x'_ /sng.
    exists (l' ++ [(parameter_name param, Undefined)]).
    rewrite <- app_assoc;simpl.
    split;[|split].
    + reflexivity.
    + rewrite heq_length_.
      rewrite app_length;simpl.
      rewrite Nat.add_1_r;auto.
    + intros /sng.
      specialize h_forall_ll_ with (ll:=(parameter_name param, Undefined) :: ll).
      rewrite  <- app_assoc.
      simpl.
      econstructor 10;eauto.
Qed.


Inductive Forall3_rev1 {A B C: Type} (R : A → B → C → Prop) : list A → list B → list C → Prop :=
  Forall3r1_nil : Forall3_rev1 R [] [] []
| Forall3r1_cons : ∀ x y z l l' l'',
    R x y z → Forall3_rev1 R l l' l'' → Forall3_rev1 R (l++[x]) (y :: l') (z :: l'').

Ltac rename_f3 n th :=
  match th with
  | Forall3_rev1 ?R ?A ?B ?C => fresh "for3_" A "_" B "_" C
  | Forall3_rev1 ?R ?A ?B ?C => fresh "for3_" A "_" B
  | Forall3_rev1 ?R ?A ?B ?C => fresh "for3_" A
  | Forall3_rev1 ?R ?A ?B ?C => fresh "for3"
  | _ => rename_wf_st n th
  end.
Ltac rename_sparkprf ::= rename_f3.


Lemma Forall3r1_impl_strong:
  ∀ (A B C : Type) (P Q : A → B → C → Prop) (l : list A) (l' : list B) (l'':list C),
    Forall3_rev1 (λ a b c, P a b c → Q a b c) l l' l'' →
    Forall3_rev1 P l l' l'' →
    Forall3_rev1 Q l l' l''.
Proof.
  intros until 0. (* bad naming of variables *)
  intros until 2 /sng.
  revert h_for3_l_l'_l''_.
  induction h_for3_l_l'_l''0_;intros /sng.
  - constructor.
  - inversion h_for3_ /sng.
    assert (l0 = l ∧ x0 = x) as ? /sng. {
      assert (Datatypes.length (l0 ++ [x0]) = Datatypes.length (l ++ [x])) /sng. {
        rewrite heq_app_.
        reflexivity. }
      setoid_rewrite app_length in heq_length_.
      simpl in heq_length_.
      assert (Datatypes.length l0 = Datatypes.length l) /sng. {
        lia. }
      specialize app_same_length_eq_ with (1:=heq_length0_)(2:=heq_app_) as ? /sng.
      decomp h_and_.
      inversion heq_cons_.
      split;auto. }
    decomp h_and_.
    subst.
    constructor;auto.
Qed.


Lemma copyIn_init:
  ∀ st x y args lparams s, 
    copyIn st s x lparams args y ->
    ∀ lvl initf sto',
      x = (lvl, initf) ->
      y = OK (lvl, sto') -> 
      exists sto'',
        sto' = sto''++ initf
        ∧ Datatypes.length sto'' = Datatypes.length lparams
        ∧ Forall3_rev1 (fun (prm:idnum * V) prm_prof e =>
                          forall k',
                            let (k,v) := prm in
                            transl_paramid k = k' ->
                            match parameter_mode prm_prof with
                            | In => evalExp st s e (OK v)
                            | Out => v = Undefined
                            | InOut => evalExp st s e (OK v)
                            end) sto'' lparams args.
Proof.
  intros until 1 /sng.
  induction h_copy_in_x_y_;!intros;try discriminate;subst /sng.
  - inversion heq_OK_ /sng.
    exists nil.
    split;[|split].
    + auto.
    + auto.
    + constructor.
  - unfold ST.push in h_forall_lvl_.
    simpl in *.
    specialize h_forall_lvl_ with  (1:=eq_refl).
    specialize h_forall_lvl_ with (1:=eq_refl).
    decomp h_forall_lvl_;eauto.
    subst.
    exists (sto'' ++ [(parameter_name param, e_v)]).
    rewrite <- app_assoc.
    simpl.
    split;[|split].
    + reflexivity.
    + rewrite app_length .
      simpl.
      lia.
    + constructor.
      * intros /sng.
        rewrite heq_parameter_mode_.
        assumption.
      * assumption.
  - unfold ST.push in h_forall_lvl_.
    simpl in *.
    specialize h_forall_lvl_ with  (1:=eq_refl).
    specialize h_forall_lvl_ with (1:=eq_refl).
    decomp h_forall_lvl_;eauto.
    subst.
    exists (sto'' ++ [(parameter_name param, Int v)]).
    rewrite <- app_assoc.
    simpl.
    split;[|split].
    + reflexivity.
    + rewrite app_length .
      simpl.
      lia.
    + constructor.
      * intros /sng.
        rewrite heq_parameter_mode_.
        assumption.
      * assumption.
  - unfold ST.push in h_forall_lvl_.
    simpl in *.
    specialize h_forall_lvl_ with  (1:=eq_refl).
    specialize h_forall_lvl_ with  (1:=eq_refl).
    decomp h_forall_lvl_;eauto.
    subst.
    exists (sto'' ++ [(parameter_name param, v)]).
    rewrite <- app_assoc.
    simpl.
    split;[|split].
    + reflexivity.
    + rewrite app_length .
      simpl.
      lia.
    + constructor.
      * intros /sng.
        rewrite heq_parameter_mode_.
        constructor.
        assumption.
      * assumption.
  - unfold ST.push in h_forall_lvl_.
    simpl in *.
    specialize h_forall_lvl_ with  (1:=eq_refl).
    specialize h_forall_lvl_ with  (1:=eq_refl).
    decomp h_forall_lvl_;eauto.
    subst.
    exists (sto'' ++ [(parameter_name param, Int v)]).
    rewrite <- app_assoc.
    simpl.
    split;[|split].
    + reflexivity.
    + rewrite app_length .
      simpl.
      lia.
    + constructor.
      * intros /sng.
        rewrite heq_parameter_mode_.
        constructor.
        assumption.
      * assumption.
  - unfold ST.push in h_forall_lvl_.
    simpl in *.
    specialize h_forall_lvl_ with  (1:=eq_refl).
    specialize h_forall_lvl_ with  (1:=eq_refl).
    decomp h_forall_lvl_;eauto.
    subst.
    exists (sto'' ++ [(parameter_name param, Undefined)]).
    rewrite <- app_assoc.
    simpl.
    split;[|split].
    + reflexivity.
    + rewrite app_length .
      simpl.
      lia.
    + constructor.
      * intros /sng.
        rewrite heq_parameter_mode_.
        reflexivity.
      * assumption.
Qed.
Lemma set_params_in : ∀ l vl k v,
    Maps.PTree.get k (set_params vl l) = Some v ->
    List.In k l.
Proof.
  induction l;simpl;intros /sng.
  - rewrite Maps.PTree.gempty in heq_mget_k_v_.
    inversion heq_mget_k_v_.
  - destruct vl;simpl in *.
    + destruct (Pos.eq_dec a k).
      * left;auto.
      * right.
        rewrite Maps.PTree.gso in heq_mget_k_v_.
        -- eapply IHl;eauto.
        -- symmetry.
           assumption.
    + destruct (Pos.eq_dec a k).
      * left;auto.
      * right.
        rewrite Maps.PTree.gso in heq_mget_k_v_.
        -- eapply IHl;eauto.
        -- symmetry.
           assumption.
Qed.

Definition is_transl_name st CE sp locenv g m (k₁ : Values.block) (δ₁ : ptrofs) nme chnk:=
  exists addr_nme typ_nme cm_typ_nme,
    (type_of_name st nme =: typ_nme)
    ∧ (transl_name st CE nme =: addr_nme)
    ∧ (transl_type st typ_nme =: cm_typ_nme)
    ∧ eval_expr g sp locenv m addr_nme (Values.Vptr k₁ δ₁)
    ∧ Ctypes.access_mode cm_typ_nme = By_value chnk.

Definition stack_separate':=
  λ (st : symboltable) (CE : compilenv) (sp : Values.val) (locenv : env)
    (g : genv) (m : mem),
  ∀  nme₁ nme₂ (k₁ : Values.block) (δ₁ : ptrofs) 
     (k₂ : Values.block) (δ₂ : ptrofs) (chnk₁ chnk₂ : AST.memory_chunk),
    is_transl_name st CE sp locenv g m k₁ δ₁ nme₁ chnk₁
    -> is_transl_name st CE sp locenv g m k₂ δ₂ nme₂ chnk₂
    -> nme₁ ≠ nme₂
    → k₂ ≠ k₁ 
      ∨ Ptrofs.unsigned δ₂ + size_chunk chnk₂ <= Ptrofs.unsigned δ₁
      ∨ Ptrofs.unsigned δ₁ + size_chunk chnk₁ <= Ptrofs.unsigned δ₂.


Ltac rename_separate n th :=
  match th with
  | stack_separate' _ _ _ _ _ _  => fresh "separate'"
  | is_transl_name _ _ _ _ _ _ _ _ ?nme _  => fresh "is_transl_name_" nme
  | is_transl_name _ _ _ _ _ _ _ _ _ _  => fresh "is_transl_name"
  | subset_CE_stbl ?st ?CE => fresh "subset_CE_st_" CE "_" st
  | subset_CE_stbl _ _ => fresh "subset_CE_st"
  | _ => rename_f3 n th
  end.
Ltac rename_sparkprf ::= rename_separate.


Lemma stack_separate_equiv :
  forall (st : symboltable) (CE : compilenv) (sp : Values.val) (locenv : env)
         (g : genv) (m : mem),
    stack_separate st CE sp locenv g m <->  stack_separate' st CE sp locenv g m.
Proof.
  intros /sng.
  split.
  - intro /sng.
    red in h_separate_CE_m_.
    red.
    intros /sng.
    red in h_is_transl_name_nme_₁,h_is_transl_name_nme_₂.
    decomp h_is_transl_name_nme_₁.
    decomp h_is_transl_name_nme_₂.
    eapply h_separate_CE_m_ with (δ₁:=δ₁)(δ₂:=δ₂)(k₁:=k₁)(k₂:=k₂)
                                (chnk₁:=chnk₁) (chnk₂:=chnk₂)
                                (typ_nme:=typ_nme)
                                (typ_nme':=typ_nme0)
                                (cm_typ_nme:=cm_typ_nme)
                                (cm_typ_nme':=cm_typ_nme0) ;
      eauto.
  - intro h_separate'_CE_m_.
    red in h_separate'_CE_m_.
    unfold is_transl_name in h_separate'_CE_m_.
    red;intros /sng.
    eapply h_separate'_CE_m_.
    + exists nme_t, typ_nme, cm_typ_nme;eauto.
    + exists nme'_t, typ_nme', cm_typ_nme';eauto.
    + assumption.
Qed.


Lemma store_param_nosideeffect: 
  forall st CE proc_param_prof s_parms ,
    store_params st CE proc_param_prof =: s_parms ->
    forall g m m' locenv locenv' t2 m1 the_proc stkptr_proc x0 v x2_b x2_ofs,
      chained_stack_structure m (Datatypes.length CE) stkptr_proc ->
      CompilEnv.exact_levelG CE ->
      stack_separate' st CE stkptr_proc locenv g m ->
      (exists astnum id, is_transl_name st CE stkptr_proc locenv g m x2_b x2_ofs (Identifier astnum id) x0) -> 
      subset_CE_stbl st CE ->(* well typedness *) 
      exec_stmt g the_proc stkptr_proc locenv m s_parms t2 locenv' m' Out_normal -> 
      Mem.store x0 m x2_b (Ptrofs.unsigned x2_ofs) v = Some m1 ->
      (Ptrofs.unsigned x2_ofs) >= 4 ->
      exists m1',
        exec_stmt g the_proc stkptr_proc locenv m1 s_parms t2 locenv' m1' Out_normal.
Proof.
  intros until proc_param_prof /sng.
  rew store_params_ok
    with functional induction function_utils.store_params st CE proc_param_prof;
    !intros;(try now discriminate);up_type /sng.
  - inversion heq_OK_;subst.
    exists m1.
    inversion h_exec_stmt_s_parms_Out_normal_ /sng.
    econstructor 1.
  - decomp h_ex_.
    rename x0 into s_parms'.
    invclear heq_OK_;subst /sng.
    specialize h_forall_s_parms_ with (1:=heq_store_prms_lparams'_x0_).
    inversion h_exec_stmt_s_parms_Out_normal_;
      try match goal with
          | H:?X<>?X |- _ => exfalso;apply H;reflexivity
          end /sng.
    clear h_exec_stmt_s_parms_Out_normal_.
    assert (exists m2',
               exec_stmt g the_proc stkptr_proc locenv m1
                         (build_param_copyin_assign (parameter_mode prm) x1 x
                                                    (transl_paramid (parameter_name prm)))
                         t1 e1 m2' Out_normal). {
      specialize Mem.store_valid_access_3 with (1:=heq_store_v_m1_) as  ? /sng.
      specialize Mem.store_valid_access_1 with (1:=heq_store_v_m1_)
                                                (2:=h_valid_access_x2_b_) as ? /sng.
      simpl in heq_transl_name_.
      functional inversion heq_transl_name_ /sng.
      (* unfold build_param_copyin_assign in h_exec_stmt_. *)
      destruct (parameter_mode prm) eqn:heq; simpl in *;up_type.
      all:swap 1 2.
      + (*Out*)inversion h_exec_stmt_ /sng.
        exists m1.
        constructor.
      + (* In *)
        inversion h_exec_stmt_ /sng.
        clear h_exec_stmt_.
        unfold Mem.storev in heq_storev_v0_m2_.
        destruct vaddr; try discriminate.
        specialize Mem.store_valid_access_3 with (1:=heq_storev_v0_m2_) as  ? /sng.
        specialize Mem.store_valid_access_1 with (1:=heq_storev_v0_m2_)
                                                  (2:=h_valid_access_b_) as ? /sng.
        assert (exists m2', Mem.storev x m1 (Values.Vptr b i) v0 = Some m2') /sng. {
          simpl.
          specialize Mem.store_valid_access_1
            with (1:=heq_store_v_m1_) (2:=h_valid_access_b_) as ? /sng.
          edestruct Mem.valid_access_store with (1:=h_valid_access_b1_) /sng.
          exists x0;eauto. }
        decomp h_ex_.
        exists m2'.
        econstructor;eauto.
        * eapply wf_chain_load';eauto.
          -- eapply chain_aligned.
             ++ eapply assignment_preserve_chained_stack_structure_aux
                  with (1:=h_chain_m_) (addr_ofs:= x2_ofs).
                ** lia.
                ** simpl.
                   eassumption.
             ++ specialize CompilEnv.exact_lvl_lvl_of_top
                  with (1:=h_exct_lvlG_CE_)
                       (2:=heq_lvloftop_CE_m'0_) as ? /sng.
                rewrite <- heq_S_.
                lia.
          -- lia. (* NoDup in args names. *)
        * (* TODO: lemma *)
          inversion h_CM_eval_expr_v0_ /sng.
          econstructor;eauto. 
      + (* In_Out *)
        inversion h_exec_stmt_ /sng.
        clear h_exec_stmt_.
        unfold Mem.storev in heq_storev_v0_m2_.
        destruct vaddr; try discriminate.
        specialize Mem.store_valid_access_3 with (1:=heq_storev_v0_m2_) as  ? /sng.
        specialize Mem.store_valid_access_1 with (1:=heq_storev_v0_m2_)
                                                  (2:=h_valid_access_b_) as ? /sng.
        assert (exists m2', Mem.storev x m1  (Values.Vptr b i) v0 = Some m2') /sng. {
          simpl.
          specialize Mem.store_valid_access_1
            with (1:=heq_store_v_m1_) (2:=h_valid_access_b_) as ? /sng.
          edestruct Mem.valid_access_store with (1:=h_valid_access_b1_) /sng.
          exists x0;eauto. }
        decomp h_ex_.

        assert (stack_localstack_aligned (m'0 - m0) e1 g m1 stkptr_proc) /sng. {
          eapply chain_aligned.
          ++ eapply assignment_preserve_chained_stack_structure_aux
               with (1:=h_chain_m_) (addr_ofs:= x2_ofs).
             ** lia.
             ** simpl.
                eassumption.
          ++ specialize CompilEnv.exact_lvl_lvl_of_top
               with (1:=h_exct_lvlG_CE_)
                    (2:=heq_lvloftop_CE_m'0_) as ? /sng.
             rewrite <- heq_S_.
             lia. }
        assert (4 <= Ptrofs.unsigned x2_ofs) /sng. {
          lia. }
        assert (m'0 - m0 ≤ m'0 - m0) /sng. {
          lia. }
        
        (* bug of "specialize with" in presence of letins: *)
        specialize wf_chain_load' as ? /sng.
        lazy zeta in h_forall_lvl_.
        specialize h_forall_lvl_ with
            (1:=heq_store_v_m1_)
            (2:=h_aligned_g_m1_)
            (3:=h_le_)
            (4:=h_le0_)
            (5:=h_CM_eval_expr_vaddr_).

        inversion h_CM_eval_expr_v0_ /sng.
        destruct vaddr;try now discriminate.
        destruct (Nat.eq_dec id (parameter_name prm)).
        all:cycle 1.
        { red in h_separate'_.
          specialize h_separate'_ with
              (1 := h_is_transl_name0_)
              (nme₂ := ( Identifier astnum (parameter_name prm)))
              (k₂:=b0)(δ₂:=i0)(chnk₂:=x)
            as ? /sng. 
          (* b0 i0 is the address of the inout param, b i is the address it points to. *)
          assert (is_transl_name st CE stkptr_proc e1 g m b i
                                  (Identifier O (parameter_name prm)) x) /sng. {
            red.
            exists (build_loads (m'0 - m0) n).
            simpl transl_name.
            assert (transl_name st CE ((Identifier O (parameter_name prm)))=:build_loads (m'0 - m0) n) /sng. {
              simpl.
              assumption. }
            edestruct h_subset_CE_st_CE_st_ with (1:=heq_transl_name0_) /sng.
            exists x0.
            eexists.
            repeat split;eauto.
            - admit. (* transl_type should be complete at some point *)
            - admit. (* this will also change
                                           when the compiler deals with arrays
                                           and records.*)
          }
          
          assert(exists v0',
                     eval_expr g stkptr_proc e1 m1 
                               (Eload x (Evar (transl_paramid (parameter_name prm))))
                               v0') /sng. {
            admit.
          }
          decomp h_ex_.
          edestruct Mem.valid_access_store with (v:=v0') /sng.
          { admit. (* eapply Mem.store_valid_access_3. *) }
          exists x0.
          eapply exec_Sstore with (2:=h_CM_eval_expr_v0'_);eauto. }


    
    decomp H.
    assert
     (exists m'',
         exec_stmt g the_proc stkptr_proc
                   e1 m2' s_parms' t0 locenv' m'' Out_normal) /sng. {
      admit. }
    decomp h_ex_.
    exists m''.
    econstructor;eauto.
Admitted.



(* replacing match-env by strong_match_env_ + unchange_on (forbidden). *)
Lemma transl_stmt_normal_OK : forall stbl (stm:stmt) s norms',
    evalStmt stbl s stm norms' ->
    forall s' CE (stm':Cminor.stmt),
      norms' = OK s' ->
      wf_st stbl ->
      invariant_compile CE stbl ->
      transl_stmt stbl CE stm = (Errors.OK stm') ->
      forall lvl (*spb ofs*) f locenv g m stkptr,
        lvl = Datatypes.length CE -> 
        (* stkptr = Values.Vptr spb ofs ->  *)
        chained_stack_structure m lvl stkptr ->
        match_env_ stbl s CE stkptr locenv g m ->
        exists tr locenv' m',
          Cminor.exec_stmt g f stkptr locenv m stm' tr locenv' m' Out_normal
          /\ match_env_ stbl s' CE stkptr locenv' g m'
          /\ chained_stack_structure m' lvl stkptr
          /\ forall astnum, unchange_forbidden stbl CE g astnum locenv locenv' stkptr m m'
                      /\ Mem.unchanged_on (forbidden stbl CE g astnum locenv stkptr m m) m m'.
Proof.
  intros until 1 /sng.
  Opaque transl_stmt.
  induction h_eval_stmt_;simpl in *;intros ; rename_all_hyps ; eq_same_clear;
  try (let h := match goal with
                | H: transl_stmt _ _ _ = _ |- _ => H
                end in
       rew transl_stmt_ok with functional inversion h);
  subst ; eq_same_clear;
  !specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_lvl_stkptr_) as h_ex_;decomp h_ex_;
    try match type of heq_stkptr_ with
        | _ = ?x => subst stkptr; (set (stkptr:=x) in * )
        end /sng.
  all: swap 6 7. (* putting fun call at the end. *)
  (* Skip *)
  - eexists. eexists. eexists.
    repeat (apply conj;intros) /sng.
    + try now constructor.
    + assumption.
    + assumption.
    + apply unchange_forbidden_refl.
    + apply Mem.unchanged_on_refl.
  
  (* assignment no range constraint *)
  - rename x into nme.
    rename st into stbl.
    rename_all_hyps.
    exists Events.E0.
    exists locenv.
    decomp (transl_name_OK_inv _ _ _ _ heq_transl_name_);subst.
    (*  (edestruct (me_stack_complete h_match_env_);eauto) /sng. *)
    decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e_ _ _ _ _ _ _
                           h_eval_expr_e_e_v_ h_match_env_).
    (* transl_type never fails *)
    assert (hex:exists nme_type_t, transl_type stbl nme_type =: nme_type_t).
    { simpl in *.
      assert (type_of_name stbl (Identifier astnum id) = Errors.OK nme_type).
      { simpl.
        rewrite heq_fetch_exp_type_.
        reflexivity. }
      rename_all_hyps.
      eapply (ci_stbl_var_types_ok h_inv_comp_CE_stbl_);eauto. }
    decomp hex.
    (* make_load does not fail on a translated variable coming from CE *)
    decomp (make_load_no_fail _ _ nme_t _ heq_transl_type_).
    (* Cminor.eval_expr does not fail on a translated variable (invariant) *)
    specialize h_match_env_ /sng.(me_safe_cm_env).(me_stack_match_addresses) as ?.
    red in h_stk_mtch_addr_stkptr_m_.
    (edestruct h_stk_mtch_addr_stkptr_m_;eauto;clear h_stk_mtch_addr_stkptr_m_) /sng.
    specialize transl_variable_Vptr with
    (1:=h_inv_comp_CE_stbl_)
    (2:=(me_stack_localstack_aligned h_match_env_.(me_safe_cm_env)))
      (3:=h_eq_transl_var_)
      (4:= h_CM_eval_expr_nme_t_nme_t_v_).
    intro hex.
    decomp hex.
    (* Adresses of translated variables are always writable (invariant?) *)
    assert (Mem.valid_access m nme_chk nme_block (Ptrofs.unsigned nme_ofst) Writable) /sng. {
      apply Mem.valid_access_implies with (p1:=Freeable).
      - destruct h_match_env_ /sng.
        destruct h_safe_cm_CE_m_ /sng.
        eapply h_freeable_CE_m_;eauto.
        subst.
        assumption.
      - constructor 2. }
    eapply Mem.valid_access_store in h_valid_access_nme_block_.
    destruct h_valid_access_nme_block_ as [m' ?] /sng.
    assert (exec_stmt g f (Values.Vptr b' Ptrofs.zero) locenv m (Sstore nme_chk nme_t e_t)
                      Events.E0 locenv m' Out_normal) /sng. {
      econstructor;eauto.
      subst.
      simpl.
      eassumption. }
    exists m'.
    repeat (apply conj;intros) /sng.
    * assumption.
    * invclear h_exec_stmt_ /sng.
      assert (e_t_v0 = e_t_v).
      { eapply det_eval_expr;eauto. }
      subst e_t_v0.
      assert (match_env_ stbl s' CE (Values.Vptr b' Ptrofs.zero) locenv g m') /sng.
      { eapply assignment_preserve_match_env_;eauto.
        intros /sng.
        subst.
        eapply eval_expr_overf;eauto. }
      up_type.
      assumption.
    * eapply assignment_preserve_chained_stack_structure_aux with (m:=m);eauto.
      subst.
      functional inversion h_eq_transl_var_ /sng.
      functional inversion heq_make_load_ /sng.
      specialize chain_struct_build_loads_ofs with (3:=h_CM_eval_expr_nme_t_nme_t_v_) as h.
      rewrite h.
      rewrite Ptrofs.unsigned_repr.
      -- eapply (h_match_env_.(me_safe_cm_env).(me_stack_no_null_offset)).
         eassumption.
      -- split.
         ++ transitivity 4;try lia.
            eapply (h_match_env_.(me_safe_cm_env).(me_stack_no_null_offset)).
            eassumption.
         ++ specialize (ci_no_overflow h_inv_comp_CE_stbl_).
            intro /sng.
            red in h_no_overf_CE_.
            specialize h_no_overf_CE_ with (1:=heq_CEfetchG_id_CE_).
            decomp h_no_overf_CE_.
            unfold Ptrofs.max_unsigned.
            lia.
      -- eapply chained_stack_structure_le;eauto.
         specialize CompilEnv.exact_lvl_lvl_of_top with (2:=heq_lvloftop_CE_m'0_);intros;eauto /sng.
         rewrite <- h_impl_eq_S_.
         ++ lia.
         ++ apply h_inv_comp_CE_stbl_.
      -- specialize (ci_no_overflow h_inv_comp_CE_stbl_).
         intro /sng.
         red in h_no_overf_CE_.
         specialize h_no_overf_CE_ with (1:=heq_CEfetchG_id_CE_).
         apply Z.mod_small.
         assumption.
    * eapply store_preserves_structure;eauto.
      erewrite transl_variable_astnum;eauto.
    * destruct nme_t_v;try discriminate. 
      up_type.
      eapply Mem.store_unchanged_on;eauto.
      intros /sng.
      intros [abs1 abs2].
      red in abs1.
      functional inversion heq_transl_name_;subst /sng.
      simpl in heq_compute_chnk_nme_.
      rewrite <- transl_variable_astnum with (a:=astnum0) (1:=h_eq_transl_var_) in h_eq_transl_var_.
      specialize (abs1 id _ nme_chk b i h_eq_transl_var_ heq_compute_chnk_nme_ h_CM_eval_expr_nme_t_nme_t_v_). 
      inversion heq_nme_t_v_;subst.
      decomp abs1;auto;try lia.
  (* Assignment with satisifed range constraint (Range l u) *)
  - rename x into nme.
    rename st into stbl.
    rename_all_hyps.
    exists Events.E0.
    exists locenv.
    decomp (transl_name_OK_inv _ _ _ _ heq_transl_name_);subst.
    decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e_ _ _ _ _ _ _ h_eval_expr_e_ h_match_env_).
      (* transl_type never fails *)
      assert (hex:exists nme_type_t, transl_type stbl nme_type =: nme_type_t).
      { simpl in *.
        assert (type_of_name stbl (Identifier astnum id) =: nme_type).
        { simpl.
          rewrite heq_fetch_exp_type_.
          reflexivity. }
        eapply (ci_stbl_var_types_ok h_inv_comp_CE_stbl_);eauto. }
      decomp hex.
      decomp (make_load_no_fail stbl nme_type nme_t nme_type_t heq_transl_type_).


      assert (hex: exists vaddr,
                 Cminor.eval_expr g stkptr locenv m nme_t vaddr).
      {  eapply h_match_env_;eauto. (* stack_match_address_ *) }
      (* A translated variable always results in a Vptr. *)
      destruct hex /sng.
      specialize transl_variable_Vptr with
      (1:=h_inv_comp_CE_stbl_)
        (2:=(me_stack_localstack_aligned h_match_env_ /sng.(me_safe_cm_env)))
        (3:=h_eq_transl_var_)
        (4:= h_CM_eval_expr_nme_t_nme_t_v_) as ?.
      decomp h_ex_. up_type.
      (* Adresses of translated variables are always writable (invariant?) *)
      assert (Mem.valid_access m nme_chk nme_block (Ptrofs.unsigned nme_ofst) Writable) /sng. {
        apply Mem.valid_access_implies with (p1:=Freeable).
        - destruct h_match_env_ /sng.
          destruct h_safe_cm_CE_m_ /sng.
          eapply h_freeable_CE_m_;eauto.
          subst.
          assumption.
        - constructor 2. }
      eapply Mem.valid_access_store in h_valid_access_nme_block_.
      destruct h_valid_access_nme_block_ /sng.
      exists x.
      assert (exec_stmt g f stkptr locenv m (Sstore nme_chk nme_t e_t)
                         Events.E0 locenv x Out_normal) /sng. {
        econstructor;eauto.
        subst.
        simpl.
        eassumption. }
      split;[ | split;[|split;[|split]]].
      * assumption.
      * up_type.
        invclear h_exec_stmt_ /sng.
        assert (e_t_v0 = e_t_v). {
          eapply det_eval_expr;eauto. }
        subst e_t_v0.
        eapply assignment_preserve_match_env_;eauto.
        intros /sng.
        invclear heq_Int_ /sng.
        eapply eval_expr_overf;eauto.
      * subst;eapply assignment_preserve_chained_stack_structure;eauto.
      * eapply store_preserves_structure;eauto.
        erewrite transl_variable_astnum;eauto.
      * up_type.
        eapply Mem.store_unchanged_on;eauto.
        intros /sng.
        intros [abs1 abs2].
        red in abs1.
        (* functional inversion heq_transl_name_;subst /sng. *)
        simpl in heq_compute_chnk_nme_.
        rewrite <- transl_variable_astnum with (a:=astnum0) (1:=h_eq_transl_var_) in h_eq_transl_var_.
        subst.
        specialize abs1 with (1:= h_eq_transl_var_) (2:=heq_compute_chnk_nme_)
                             (3:=h_CM_eval_expr_nme_t_nme_t_v_).
        destruct abs1 /sng.
        -- apply hneq_nme_block. reflexivity.
        -- lia.
  (* If statement --> true *)
  - rename x0 into b_then.
    rename x1 into b_else.
    rename_all_hyps.
    + decomp (transl_expr_ok _ _ _ e_t heq_tr_expr_e_ locenv g m _ _
                             stkptr h_eval_expr_e_ h_match_env_).
      specialize h_forall_s'_ with (1:=eq_refl)(2:=h_wf_st_st_)
                                    (3:=h_inv_comp_CE_st_)
                                    (4:=heq_transl_stmt_stmt_b_then_)
                                    (5:=eq_refl)
                                    (6:=h_chain_m_)
                                    (7:=h_match_env_)
                                    (f:=f).
      decomp h_forall_s'_.
      exists tr.
      exists locenv'.
      exists m'.
      specialize transl_expr_ok with (1:=heq_tr_expr_e_)(2:=h_eval_expr_e_)
                                     (3:=h_match_env_) as h.
      decomp h.
      assert (exec_stmt g f stkptr locenv m
                        (Sifthenelse (Ebinop (Ocmp Cne) e_t (Econst (Ointconst Int.zero)))
                                     b_then b_else) tr locenv' m' Out_normal).
      { econstructor;eauto.
        * { econstructor;eauto.
            - econstructor;eauto.
              simpl.
              reflexivity.
            - simpl.
              reflexivity. }
        * inversion  h_transl_value_e_t_v0_.
          subst.
          econstructor.
        * rewrite  Int.eq_false;eauto.
          apply Int.one_not_zero. }
      split;[|split;[|split;[|split]]].
      * assumption.
      * assumption.
      * assumption.
      * apply h_forall_astnum_.
      * apply h_forall_astnum_.
  (* If statement --> false *)
  - rename x0 into b_then.
    rename x1 into b_else.
    rename_all_hyps.
    + decomp (transl_expr_ok _ _ _ e_t heq_tr_expr_e_ locenv g m _ _
                             stkptr h_eval_expr_e_ h_match_env_).

      specialize h_forall_s'_ with (1:=eq_refl)(2:=h_wf_st_st_)
                                    (3:=h_inv_comp_CE_st_)
                                    (4:=heq_transl_stmt_stmt_b_else_)
                                    (5:=eq_refl)
                                    (6:=h_chain_m_)
                                    (7:=h_match_env_)
                                    (f:=f).
      decomp h_forall_s'_.
      exists tr.
      exists locenv'.
      exists m'.
      decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e_ locenv g m s _ stkptr h_eval_expr_e_ h_match_env_).
      assert (exec_stmt g f stkptr locenv m
                        (Sifthenelse (Ebinop (Ocmp Cne) e_t (Econst (Ointconst Int.zero)))
                                     b_then b_else) tr locenv' m' Out_normal).
      { econstructor;eauto.
        * { econstructor;eauto.
            - econstructor;eauto.
              simpl.
              reflexivity.
            - simpl.
              reflexivity. }
        * inversion  h_transl_value_e_t_v0_.
          subst.
          econstructor.
        * rewrite Int.eq_true.
          simpl.
          assumption. }
      split;[|split;[|split;[|split]]].
      * assumption.
      * assumption.
      * assumption.
      * apply h_forall_astnum_.
      * apply h_forall_astnum_.
  - (* Sequence *)
    simpl in *.
    specialize h_forall_s'_ with (1:=eq_refl) (2:=h_wf_st_st_) (3:=h_inv_comp_CE_st_) (4:=heq_transl_stmt0_)
                                   (5:=eq_refl) (6:=h_chain_m_lvl_stkptr_) (7:=h_match_env_) (f:=f).
    decomp h_forall_s'_.
    match goal with
    | H:forall _, _ ∧ _ |- _ => let nme := fresh "h_unchange_" in rename H into nme
    end.
    specialize h_forall_s'0_ with (m:=m') (1:=eq_refl)(2:=h_wf_st_st_)(3:=h_inv_comp_CE_st_) (4:=heq_transl_stmt_)
                                   (5:=eq_refl) (6:=h_chain_m'_) (7:=h_match_env0_)(f:=f).

    decomp h_forall_s'0_.
    match goal with
    | H:forall _, _ ∧ _ |- _ => let nme := fresh "h_unchange_" in rename H into nme
    end.
    eexists.
    exists locenv'0.
    exists m'0.
    split;[|split;[|split]].
    + econstructor;eauto.
    + assumption.
    + assumption.
    + intros /sng.
      specialize h_unchange_ with (astnum:=astnum).
      specialize h_unchange0_ with (astnum:=astnum).
      decomp h_unchange_.
      decomp h_unchange0_.
      split.
      * eapply unchange_forbidden_trans ;eauto.
      * eapply Mem.unchanged_on_trans with m';auto.
        red in h_unch_forbid_m_m'_, h_unch_forbid_m'_m'0_.
        eapply (unchanged_on_iff );eauto.
        -- do 2 red.
           intros; subst.
           eapply h_unch_forbid_m_m'_.

  (* Procedure call *)
  - (* rename x1 into chaining_expr. *)
    subst current_lvl.
    rename f0 into func.
    rename locals_section into f1'_l.
    rename params_section into f1'_p.
    specialize h_forall_s'_ with (1:=eq_refl).
    rename s1 into suffix_s .
    rename s3 into suffix_s'.
    rename y into lvl_p.
    rename x into args_t.
    rename x0 into p_sign.
    (* subst x3. *)
    (* subst current_lvl. *)
    rename n into pb_lvl.
    eq_same_clear.
    up_type.
    (* renaming m' an locenv' and tr as xx_postfree *)
    change ( ∃ (tr_postfree : Events.trace) (locenv_postfree : env) (m_postfree : mem), 
               exec_stmt g func stkptr locenv m
                         (Scall None p_sign (Econst (Oaddrsymbol (transl_procid p) (Ptrofs.repr 0)))
                                (addr_enclosing_frame :: args_t)) tr_postfree locenv_postfree m_postfree
                         Out_normal
               ∧ match_env_ st s' CE stkptr locenv_postfree g m_postfree
               ∧ chained_stack_structure m_postfree (Datatypes.length CE) stkptr
               ∧ (∀ astnum : astnum,
                     unchange_forbidden st CE g astnum locenv locenv_postfree stkptr m m_postfree
                     ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m_postfree)).
    (* using the invariant to state that the procedure do
       translate to an address containing the translated code.  *)
    pose proof (me_stack_match_functions_ h_match_env_ /sng.(me_safe_cm_env)).
    red in h_stk_mtch_fun_.
    specialize (h_stk_mtch_fun_ _ _ _ heq_fetch_proc_p_).
    destruct h_stk_mtch_fun_ as [CE_prefx [CE_sufx [paddr [pnum [fction [lglobdef [? [? [? ?]]]]]] ]]] /sng.
    up_type.

    (* Core of the proof, link the different phase of execution with
       the pieces of code built by transl_procedure (in h_tr_proc_). *)
    (* ideally functional inversion here would be great but it fails, bug(s) reported *)
    (* rewrite transl_procedure_ok in h_tr_proc_. *)
    (* functional inversion h_tr_proc_ /sng. ;subst;eq_same_clear; clear heq_transl_stmt_stm'_. *)
    (* ************** emulating functional inversion ********************** *)
    destruct pb eqn:heq_pb_;eq_same_clear.
    rewrite <- ?heq_pb_ in heq_fetch_proc_p_. (* to re-fold pb where it didn't reduce. *)
    simpl in *.
    rename heq_transl_proc_pb_ into h_tr_proc_. (* displays better with a short name. *)

    destruct  (build_compilenv st CE_sufx pb_lvl procedure_parameter_profile
                 procedure_declarative_part)  as  [ [CE''_bld stcksize]|] eqn:heq_bldCE_; simpl in h_tr_proc_; try discriminate.
    repeat match type of h_tr_proc_ with
           | (bind2 ?x _) = _  => destruct x as  [ [CE''_bld stcksize]|] eqn:heq_bldCE_
                                 ; simpl in h_tr_proc_; try discriminate
           | context [ ?x <=? ?y ]  =>
             let heqq := fresh "heq" in destruct (Z.leb x y) eqn:heqq; try discriminate
           | (bind ?y ?x) = _ =>
             let heqq := fresh "heq" in
             destruct y eqn:heqq;
                 [ 
                   match type of heqq with
                   | transl_stmt _ _ _ = Errors.OK ?x => rename x into s_pbdy
                   | init_locals _ _ _ = Errors.OK ?x => rename x into s_locvarinit
                   | store_params _ _ _ = Errors.OK ?x => rename x into s_parms
                   | copy_out_params _ _ _ = Errors.OK ?x => rename x into s_copyout
                   | transl_lparameter_specification_to_procsig _ _ _ = Errors.OK ?x => rename x into p_sig
                   | _ => idtac
                   end
                   ; autorename heqq; simpl in h_tr_proc_
                 | discriminate]
           end.
    up_type.
    inversion h_tr_proc_;clear h_tr_proc_ /sng.
    (* invclear heq /sng. *)
    match type of heq_find_func_paddr_fction_ with
    | (_ = Some (AST.Internal ?f)) => set (the_proc := f) in *
    end.
    up_type.
    (* ************** END OF emulating functional inversion ********************** *)
    (* more or less what functional inversion would have produced in one step *)
    (* CE' is the new CE built from CE and the called procedure parameters and local variables *)

    specialize (h_forall_s'_ CE''_bld).
    rewrite heq_transl_stmt_procedure_statements_s_pbdy_ in h_forall_s'_.
    specialize (h_forall_s'_ s_pbdy).
    assert (h_inv_CE''_bld_:invariant_compile CE''_bld st).
    { eapply build_compilenv_preserve_invariant_compile;eauto.
      eapply invariant_compile_sublist with CE_prefx.
      assert (h_CE_:CE_prefx ++ CE_sufx = CE).
      - eapply CompilEnv.cut_until_spec1;eassumption. (* Lemma todo *)
      - rewrite h_CE_.
        assumption. }
    specialize (h_forall_s'_ h_wf_st_st_ h_inv_CE''_bld_ eq_refl).

    unfold transl_params in heq_transl_params_p_x_.
    unfold symboltable.fetch_proc_ in heq_fetch_proc_p_.
    rewrite heq_fetch_proc_p_ in heq_transl_params_p_x_.
    rewrite heq_pb_ in heq_transl_params_p_x_.
    simpl in heq_transl_params_p_x_.

    assert (heq_bldCE'_: build_compilenv st CE_sufx pb_lvl procedure_parameter_profile procedure_declarative_part =: (CE''_bld, stcksize))
      by assumption.
    apply compilenv_inv in heq_bldCE'_.
    destruct heq_bldCE'_ as [sto [sto_sz [init_sto_sz [fr_prm heq_bldCE'_]]]].
    decompose [and] heq_bldCE'_; clear heq_bldCE'_ /sng.
    
    assert (hfrsh:fresh_params_ procedure_parameter_profile sto) by admit. (* spark typing *)
    assert (hnodup_arg:NoDupA eq_param_name procedure_parameter_profile) by admit. (* spark typing *)
    assert (hnodup_decl:NoDupA eq (decl_to_lident st procedure_declarative_part)) by admit. (* spark typing *)
    assert (heq_lgth_CE_sufx_:Datatypes.length CE_sufx = pb_lvl).
    {
      erewrite (CompilEnv.cut_until_exact_levelG _ _ _ _ _ _ h_CEcut_CE_pb_lvl_).
      reflexivity. }
    rewrite heq_lgth_CE_sufx_ in heq_pair_.
    invclear heq_pair_ /sng.
    
    unfold newFrame in h_copy_in_.
    destruct f /sng.
    destruct (copy_in_lvl _ _ _ _ _ _ _ h_copy_in_) as [f h_pair_].
    inversion h_pair_ /sng.

    assert (chained_stack_structure m (Datatypes.length CE - 1) stkptr) /sng.
    { eapply chained_stack_structure_le;eauto;lia. }
    specialize copy_in_spec with (1:=h_chain_m_) (2:=h_inv_comp_CE_st_)(3:=h_match_env_)(4:=heq_transl_params_p_x_) (5:=h_copy_in_) as h.
    destruct h as [args_t_v ?] /sng.
    assert (h_ex_:exists chaining_expr_from_caller_v,Cminor.eval_expr g stkptr locenv m addr_enclosing_frame chaining_expr_from_caller_v).
    { admit. (* invariant to add: The chaining parameter is always evaluable to a value (an address). *) }
    destruct h_ex_ as [chaining_expr_from_caller_v h_chaining_expr_from_caller_v_].
    destruct (Mem.alloc m 0 (fn_stackspace the_proc)) as [m_proc_pre_init spb_proc] eqn:h_alloc_.
    up_type.
    (* locenv_init is the local env filled by CMinor, but the variables are not yet copied into the local stack *)
    
    remember (set_locals (fn_vars the_proc) (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc))) as locenv_init.

    (* Painfuly paraphrasing eval_funcall: should find another way...
       Each part of the procedure creates an intermediary state. Some of them
       do not maintain the global invariant, we state a different one.
       Instead of doing this painful assertions (fragile to any change in the code),
       we would rather use Coq to generate this. Don't know how.

       Suggestion from Arthur Charg.: define a rule where intermediary states are
       not linked from one step to another and where invariants are explicitely stated.
                    ∃σ' (I₁(σ) ∧ <σ,initvar> ⟿ σ')
       ∀σ I₁(σ) ⟿ ∃σ' (I₂(σ) ∧ <σ,initvar> ⟿ σ')
       ∀σ I₂(σ) ⟿ ∃σ' (I₃(σ) ∧ <σ,initvar> ⟿ σ')
       ...
       ∀σ Iₙ₋₁(σ) ⟿ ∃σ' (Iₙ(σ) ∧ <σ,initvar> ⟿ σ')
       --------------------------------------------
            ∃σ' (Iₙ(σ) ∧ <σ,initvar> ===> σ') *)

    (* The following proof follows the scheme:
       m,locenv ---> m_proc_pre_init, empty_locenv   ( just mallocing the new locenv )
                ---> m_postchain,locenv_postchain    ( add the chainging arg )
                ---> m_postprms,locenv_postprms      ( execute parameter init. (copy them to the local stack) )
                ---> m_postdecl,locenv_postdecl      ( execute loc. var init. )
                ---> m_postbdy, locenv_postbdy       ( execute the procedure code )
                ---> m_postcpout,locenv_postcpout    ( copy_out ) 
     *)

    eq_same_clear. up_type.
    set (stkptr_proc:=(Values.Vptr spb_proc Ptrofs.zero)) in *.
    (* expliciting the funcall and that m' = m_postfree. *)
    enough (h_ex_:exists m_postfree trace_postfree v,
               eval_funcall g m (AST.Internal the_proc) (chaining_expr_from_caller_v :: args_t_v) trace_postfree m_postfree v
               /\ match_env_ st s' CE stkptr locenv g m_postfree
               ∧ chained_stack_structure m_postfree (Datatypes.length CE) stkptr
               ∧ (∀ astnum : astnum,
                     unchange_forbidden st CE g astnum locenv locenv stkptr m m_postfree
                     ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m_postfree)
           ).
    { decomp h_ex_.
      match goal with
      | H:forall _, _ ∧ _ |- _ => rename H into h_forbid_
      end.
      (* destruct h_ex_ as [m_postfree [trace_postfree [ vres [h_decl_ok_exec_ h_decl_ok_matchenv_]]]]. *)
      exists trace_postfree, locenv, m_postfree.
      split;[|split;[|split]].
      - econstructor;eauto.
        + econstructor;eauto.
        + cbn.
          unfold transl_procsig in *.        
          rewrite  heq_fetch_proc_p_ in heq_transl_procsig_p_.
          rewrite heq_pb_ in heq_transl_procsig_p_.
          cbn in heq_transl_procsig_p_.
          rewrite heq_transl_lprm_spec_procedure_parameter_profile_p_sig_ in heq_transl_procsig_p_.
          cbn in heq_transl_procsig_p_.
          inversion heq_transl_procsig_p_.
          reflexivity.
      - assumption.
      - assumption.
      - assumption. }

    (* the chained structure from the initial stkptr
       (callers stack pointer) is still true after malloc *)
    assert (chained_stack_structure m_proc_pre_init (Datatypes.length CE)%nat stkptr) /sng.
    { eapply malloc_preserves_chained_structure;eauto. }


    (* After assigning the chaining arg, chained_stack_structure is
    true again with depth of the enclosing procedure +1. Warning:
    enclosing proc is not the calling proc. *)
    assert (exists locenv_postchainarg m_postchainarg trace_postchainarg,
                exec_stmt g the_proc stkptr_proc locenv_init m_proc_pre_init
                         (Sstore AST.Mint32 (Econst (Oaddrstack Ptrofs.zero)) (Evar chaining_param))
                          trace_postchainarg locenv_postchainarg m_postchainarg Out_normal
                ∧ chained_stack_structure m_postchainarg (S (Datatypes.length CE_sufx)) stkptr_proc
                ∧ eval_expr g stkptr_proc locenv_postchainarg m_postchainarg (Eload AST.Mint32 (Econst (Oaddrstack Ptrofs.zero))) chaining_expr_from_caller_v
                ∧ eval_expr g stkptr locenv m_postchainarg (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (Datatypes.length CE_prefx)) chaining_expr_from_caller_v) /sng.
    { exists locenv_init.
      subst.
      destruct (Mem.valid_access_store m_proc_pre_init AST.Mint32 spb_proc 0
                                         chaining_expr_from_caller_v)
        as [m_postchainarg ?] /sng.
      { eapply Mem.valid_access_freeable_any.
        eapply Mem.valid_access_alloc_same;eauto.
        - auto with zarith.
        - simpl.
          transitivity (snd fr_prm).
          + eapply build_frame_lparams_mon_sz in heq_bld_frm_procedure_parameter_profile_.
            simpl in heq_bld_frm_procedure_parameter_profile_.
            assumption.
          + eapply build_frame_decl_mon_sz in heq_build_frame_decl_.
            assumption. }
      assert (Mem.storev AST.Mint32 m_proc_pre_init (Values.Vptr spb_proc Ptrofs.zero)
                          chaining_expr_from_caller_v = Some m_postchainarg) /sng.
      { simpl.
        assumption. }
      exists m_postchainarg.
      (* the first part will be usefull to prove the other parts, let us prove it first. *)
      assert (∃ trace_postchainarg : Events.trace, 
  exec_stmt g the_proc stkptr_proc (set_locals (fn_vars the_proc) (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc))) m_proc_pre_init
    (Sstore AST.Mint32 (Econst (Oaddrstack Ptrofs.zero)) (Evar chaining_param)) trace_postchainarg
    (set_locals (fn_vars the_proc) (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc))) m_postchainarg Out_normal) /sng.
      { eexists.
        econstructor.
        + econstructor.
          reflexivity.
        + econstructor.
          lazy beta delta[the_proc fn_vars fn_params set_params] iota.
          fold set_params.
          rewrite map_get_set_locals_diff.
          * apply Maps.PTree.gss.
          * (*  no variable collides with the chainging param. *)
            intro abs.
            specialize transl_procsig_match_env_succeeds_
              with (pnum:=p) (proc_lvl:=lvl_p) (1:=h_wf_st_st_) (2:=h_match_env_)
                   (5:=heq_find_func_paddr_fction_)
              as h.
            assert (p_sign=funsig (AST.Internal the_proc)) /sng.
            { simpl.
              assert (Errors.OK p_sign = Errors.OK p_sig) /sng.
              { rewrite <- heq_transl_lprm_spec_procedure_parameter_profile_p_sig_.
                rew transl_procsig_ok with
                  functional inversion heq_transl_procsig_p_ /sng.
                rewrite <- heq_transl_lprm_spec_.
                rewrite heq_fetch_proc_ in heq_fetch_proc_p_.
                inversion heq_fetch_proc_p_.
                reflexivity. }
              inversion heq_OK_.
              reflexivity. }
            subst.
            specialize h with (1:=heq_transl_procsig_p_) (2:=h_CM_eval_expr_paddr_).
            decomp h.
            eelim (h_forall_i_ chaining_param);eauto.
            rew transl_procsig_ok with
              functional inversion heq_transl_procsig_p_ /sng.
            subst.
            rewrite heq_fetch_proc_ in *.
            inversion heq_fetch_proc_p_.
            subst.
            simpl.
            assumption.
        + simpl.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_zero.
          assumption. }
      decomp h_ex_.

      exists trace_postchainarg.
      split.
      - auto.
      - assert (Datatypes.length CE = Datatypes.length CE_sufx + Datatypes.length CE_prefx)%nat /sng.
        { erewrite <- CompilEnv.cut_until_spec1 at 1;eauto.
          rewrite app_length.
          auto with arith. }
        rewrite heq_length0_ in h_chain_m_lvl_stkptr_.
        specialize chain_structure_cut with (1:=h_chain_m_lvl_stkptr_) (g:=g) (e:=locenv) as h.
        decomp h.
        assert (heq_lgth_CE_sufx_:Datatypes.length CE_sufx = lvl_p).
        { rew transl_procsig_ok with functional inversion heq_transl_procsig_p_ /sng.
          subst.
          rewrite heq_fetch_proc_ in *.
          inversion heq_fetch_proc_p_;auto. }
        subst lvl_p.
        assert (sp' = chaining_expr_from_caller_v) /sng.
        { unfold addr_enclosing_frame in h_chaining_expr_from_caller_v_.
          eapply det_eval_expr;eauto.
          assert (Datatypes.length CE_prefx = Datatypes.length CE - Datatypes.length CE_sufx)%nat /sng.
          { lia. }
          rewrite heq_length1_;auto. }
        subst sp'.  
        assert (exists cm_addr_enclosing_frame,
                   chaining_expr_from_caller_v = Values.Vptr cm_addr_enclosing_frame Ptrofs.zero) /sng.
        { eapply chained_stack_struct_inv_sp_zero;eauto. }
        decomp h_ex_.
        subst.
        { split;[|split].
          - eapply chained_S with (b':=cm_addr_enclosing_frame) (b:=spb_proc).
            + eapply storev_outside_struct_chain_preserves_chained_structure with (m:=m_proc_pre_init)(e:=locenv)(g:=g).
              all:swap 1 3.
              * eassumption.
              * eapply malloc_preserves_chained_structure with (1:=h_alloc_);eauto.
              * intros /sng.  (* the new frame cannot be accessed via build_load from the callers stkptr *)
                eapply malloc_distinct_from_chaining_loads;eauto.
                eapply malloc_preserves_chaining_loads_2;eauto.
                eapply chained_stack_structure_le;eauto with arith.
            + simpl.
              rewrite Ptrofs.unsigned_zero.
              erewrite Mem.load_store_same;eauto.
              subst addr_enclosing_frame.
              simpl.
              reflexivity. (* This uses Archi.ptr64 = false *)
          - econstructor.
            + econstructor.
              simpl.
              rewrite Ptrofs.add_zero_l.
              reflexivity.
            + 
              unfold Mem.storev in heq_storev_chaining_expr_from_caller_v_m_postchainarg_.
              unfold Mem.loadv.
              erewrite Mem.load_store_same;eauto.
              simpl.
              reflexivity. (* This uses Archi.ptr64 = false *)
          - eapply storev_outside_struct_chain_preserves_chaining with (3:=heq_storev_chaining_expr_from_caller_v_m_postchainarg_).
            all:swap 1 2.
            all:swap 2 3.
            + eassumption.
            + lia.
            + intros /sng.
              eapply malloc_distinct_from_chaining_loads_2 with (1:=h_chain_m_lvl_stkptr_) (2:=h_alloc_) (n:=n).
              * lia.
              * eassumption.
            +
              eapply malloc_preserves_chaining_loads;eauto.
              * eapply chained_stack_structure_le with (1:=h_chain_m_lvl_stkptr_);eauto.
                lia. }
    }
    decomp h_ex_.

    (* the chained structure from the initial stkptr
       (callers stack pointer) is still true after malloc + chain_arg *)
   assert (chained_stack_structure m_postchainarg (Datatypes.length CE)%nat stkptr) /sng.
    { inversion h_exec_stmt_ /sng.
      inversion h_CM_eval_expr_vaddr_ /sng.
      simpl in h_eval_constant_.
      inversion h_eval_constant_ /sng.
      eapply storev_outside_struct_chain_preserves_chained_structure
        with (m:=m_proc_pre_init) (e:=locenv_postchainarg)(g:=g).
      all:swap 1 3.
      - eauto.
      - assumption.
      - intros /sng.
        (* spb_proc was free in m, and b'0 must be non free in m, so they are different *)
        (* b'0 exists in m: *)
        match type of h_CM_eval_expr_ with
        | context c [m_proc_pre_init] => let t := context c[m] in assert t
        end /sng.
        { eapply malloc_preserves_chaining_loads_2;eauto.
          eapply chained_stack_structure_le with (n:=(Datatypes.length CE));eauto.
          lia. }
        eapply malloc_distinct_from_chaining_loads with (1:=h_chain_m_lvl_stkptr_)(2:=h_alloc_);eauto. }

    (* variables of CE_sufx are accessible both from stkptr_proc and stkptr. *)
    assert(
        forall astnum id δlvl n id_v,
          transl_variable st ((pb_lvl, sto) :: CE_sufx) astnum id =: (build_loads (S δlvl) n)
          -> eval_expr g stkptr_proc locenv_postchainarg m_postchainarg (build_loads (S δlvl) n) id_v
          -> eval_expr g stkptr locenv_postchainarg m_postchainarg (build_loads (Datatypes.length CE_prefx+δlvl) n) id_v
          ) as h_reachable_enclosing_variables_. {
      intros /sng.
      up_type.
      assert (Datatypes.length CE = Datatypes.length CE_sufx + Datatypes.length CE_prefx)%nat /sng.
      { erewrite <- CompilEnv.cut_until_spec1 at 1;eauto.
        rewrite app_length.
        auto with arith. }
      assert (δlvl < (Datatypes.length CE_sufx))%nat /sng. {
        assert (CompilEnv.exact_levelG ((pb_lvl, sto) :: CE_sufx)) /sng. {
          apply h_inv_CE''_bld_. }
        specialize transl_variable_exact_lvl_le_toplvl with (1:=h_exct_lvlG_)(2:=h_eq_transl_var_) as h.
        simpl in h.
        lia. }
      assert (chained_stack_structure m_postchainarg (Datatypes.length CE_prefx + δlvl)%nat stkptr) /sng.
      { eapply chained_stack_structure_le;eauto.
        lia. }
      rewrite heq_length0_ in h_chain_m_lvl_stkptr_.
      assert ((δlvl < S (Datatypes.length CE_sufx))%nat) by lia /sng.
      unfold build_loads in h_CM_eval_expr_id_v_.
      Opaque build_loads_.
      inversion h_CM_eval_expr_id_v_ /sng.
      Transparent build_loads_.
      unfold build_loads.
      inversion h_CM_eval_expr_v2_ /sng.
      simpl in h_eval_constant_|- *.
      invclear h_eval_constant_ /sng.
      econstructor.
      all: cycle 1.
      - econstructor;eauto.
        simpl.
        reflexivity.
      - eassumption.
      - 
        rewrite Nat.add_comm.
        eapply chained_stack_structure_decomp_add';eauto.
        all:cycle 1.
        + eapply eval_expr_build_load_const_inv_locenv ;eauto.
        + specialize chained_stack_structure_decomp_S
            with (1:=h_chain_m_postchainarg_)(2:=h_lt_δlvl0_)(3:=h_CM_eval_expr_v1_) as ? /sng.
          decomp h_ex_.
          subst_det_addrstack_zero.
          assumption.
        + eapply chained_stack_structure_le;eauto.
          lia. }

    assert (
      forall astnum id v1 lvl_v1 δ_v1,
        (lvl_v1 <= Datatypes.length CE)%nat ->
        transl_variable st CE astnum id =: build_loads lvl_v1 δ_v1 ->
        eval_expr g stkptr locenv m_postchainarg (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl_v1) v1
        <-> eval_expr g stkptr locenv m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl_v1) v1) /sng. {
      intros /sng.
      split;intros /sng.
      { eapply malloc_preserves_chaining_loads_2 with (lvl:=Datatypes.length CE).
        - eassumption.
        - apply Nat.lt_le_incl.
          eapply transl_variable_exact_lvl_le_toplvl;eauto.
        - assumption.
        - inversion h_exec_stmt_ /sng.
          specialize (cm_eval_addrstack_zero spb_proc Ptrofs.zero m_proc_pre_init g locenv_postchainarg) /sng.
          intro /sng.
          fold stkptr_proc in h_CM_eval_expr_.
          rewrite det_eval_expr with (1:=h_CM_eval_expr_vaddr_)(2:=h_CM_eval_expr_)
            in heq_storev_v_m_postchainarg_.
          eapply storev_outside_struct_chain_preserves_chaining2 with (3:=heq_storev_v_m_postchainarg_).
          all: cycle 1.
          + eassumption.
          + apply Nat.lt_le_incl.
            eapply transl_variable_exact_lvl_le_toplvl;eauto.
          + assumption.
          + intros /sng.
            eapply malloc_distinct_from_chaining_loads_2 with (2:=h_alloc_)(4:=h_CM_eval_expr0_)(lvl:=Datatypes.length CE);auto. }
      { inversion h_exec_stmt_ /sng.
        specialize (cm_eval_addrstack_zero spb_proc Ptrofs.zero m_proc_pre_init g locenv_postchainarg) /sng.
        intro /sng.
        fold stkptr_proc in h_CM_eval_expr_.
        rewrite det_eval_expr with (1:=h_CM_eval_expr_vaddr_)(2:=h_CM_eval_expr_)
          in heq_storev_v_m_postchainarg_.
        eapply storev_outside_struct_chain_preserves_chaining with (3:=heq_storev_v_m_postchainarg_).
        - intros /sng.
          eapply malloc_distinct_from_chaining_loads_2 with (2:=h_alloc_) (4:=h_CM_eval_expr0_)(lvl:=Datatypes.length CE);auto.
          + eassumption.
        - assumption.
        - apply Nat.lt_le_incl.
          eapply transl_variable_exact_lvl_le_toplvl;eauto.
        - eapply malloc_preserves_chaining_loads with (lvl:=Datatypes.length CE).
          + eassumption.
          + apply Nat.lt_le_incl.
            eapply transl_variable_exact_lvl_le_toplvl;eauto.
          + assumption.
          + assumption. }
    }

    assert (∀ astnum addr ofs,
               (forbidden st CE g astnum locenv stkptr m m addr ofs)
            -> (forbidden st CE g astnum locenv stkptr m_postchainarg m_postchainarg addr ofs))
      as h_forbidden_incl_m_m_poschainarg_.
    { unfold forbidden.
      intros /sng.
      decomp h_and_.
      (* rename H0 into hneg_perm. *)
      split.
      all:swap 1 2.
      - inversion h_exec_stmt_ /sng.
        eapply storev_preserves_is_non_free;eauto.
        eapply malloc_preserves_is_non_free with (m:=m);eauto.
      - red.
        intros /sng.
        unfold invisible_cminor_addr in h_invis_stkptr__m_addr_ofs_.
        functional inversion h_eq_transl_var_ /sng.
        assert (chained_stack_structure m (m' - lvl_id) stkptr) /sng. {
          eapply chained_stack_structure_le with (n:=Datatypes.length CE);eauto.
          specialize CompilEnv.exact_lvl_lvl_of_top with (l:=CE) as ? /sng.
          erewrite <- h_impl_forall_n_.
          all:swap 3 1.
          -- eapply heq_lvloftop_CE_m'_.
          -- eapply h_inv_comp_CE_st_.
          -- lia. }
        specialize chain_structure_spec with (1:=h_chain_m0_) (g:=g)(e:=locenv) as ? /sng.
        decomp h_ex_.
        eapply h_invis_stkptr__m_addr_ofs_.
        + eapply h_eq_transl_var_.
        + assumption.
        +
          unfold build_loads.
          inversion h_exec_stmt_ /sng.
          inversion h_CM_eval_expr_vaddr_ /sng.
          simpl in h_eval_constant_.
          inversion h_eval_constant_.
          subst.
          econstructor.
          all:swap 1 2.
          * econstructor.
            reflexivity.
          * eapply h_CM_eval_expr_.
          * simpl.
            assert (Archi.ptr64=false) by reflexivity /sng.
            rewrite heq_ptr64_.
            rewrite Ptrofs.add_zero_l.
            specialize eval_build_loads_offset with (4:=h_CM_eval_expr_id_t_) as  ? /sng.
            erewrite h_forall_lvl_;eauto.
            all:cycle 1.
            -- eapply Z.mod_small.
               eapply h_inv_comp_CE_st_;eauto.
            -- eapply chain_aligned;eauto.
               { specialize CompilEnv.exact_lvl_lvl_of_top with (l:=CE) as ? /sng.
                 erewrite <- h_impl_forall_n_.
                 all:swap 3 1.
                 - eapply heq_lvloftop_CE_m'_.
                 - eapply h_inv_comp_CE_st_.
                 - lia. }
            -- move h_CM_eval_expr_id_t_ after heq_ptr64_.
               unfold build_loads in h_CM_eval_expr_id_t_.
               inversion h_CM_eval_expr_id_t_ /sng.
               move h_CM_eval_expr_ after h_CM_eval_expr_v1_.
               assert (eval_expr g stkptr locenv m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (m' - lvl_id)) v1) /sng. {
                 eapply h_forall_astnum_;eauto.
                 apply Nat.lt_le_incl.
                 eapply transl_variable_exact_lvl_le_toplvl;eauto.
               }
               specialize det_eval_expr with (1:=h_CM_eval_expr_v0_)(2:=h_CM_eval_expr_) as ? /sng.

               subst.
               simpl in h_eval_binop_Oadd_v1_v2_.
               destruct v2; try discriminate /sng.
               rewrite heq_ptr64_ in h_eval_binop_Oadd_v1_v2_.
               inversion h_eval_binop_Oadd_v1_v2_ /sng.
               f_equal.
               f_equal.
               unfold Ptrofs.of_int.
               rewrite Int.unsigned_repr;auto.
               rewrite <- max_unsigned_ok.
               unfold max_unsigned.
               rewrite modulus_ok.
               specialize h_inv_comp_CE_st_ /sng.(ci_no_overflow) as ?.
               red in h_no_overf_CE_.
               specialize h_no_overf_CE_ with (1:=heq_CEfetchG_id_CE_).
               rewrite Ptrofs.modulus_eq32 in h_no_overf_CE_;eauto.
               lia.
    }
          
    (* Maybe we will need to prove the other direction too:
       forbidden m_postchain <-> (forbidden m OR inside CE_prefx). *)
    assert (∀ astnum addr ofs, (forbidden st CE g astnum locenv stkptr m m addr ofs)
            -> (forbidden st ((pb_lvl, sto) :: CE_sufx) g astnum locenv_postchainarg
                          stkptr_proc m_postchainarg m_postchainarg addr ofs))
      as h_forbidden_incl_m_m_poschainarg'_.
    { 
      unfold forbidden.
      intros /sng.
      decomp h_and_.
      (* rename H0 into hneg_perm. *)
      split.
      all:swap 1 2.
      - intro abs.
        apply h_neg_free_blck_m_addr_ofs_.
        unfold is_free_block in *.
        intro.
        intro abs2.
        apply abs with perm.
        inversion h_exec_stmt_ /sng.
        inversion h_CM_eval_expr_vaddr_ /sng.
        simpl in h_eval_constant_.
        inversion h_eval_constant_.
        subst.
        eapply Mem.perm_store_1.
        all:swap 1 2.
         + eapply Mem.perm_alloc_1;eauto.
         + simpl in heq_storev_v_m_postchainarg_.
           eapply heq_storev_v_m_postchainarg_.
      - unfold invisible_cminor_addr.
        intros /sng.
        functional inversion h_eq_transl_var_ /sng.
        cbn in heq_lvloftop_m'_.
        invclear heq_lvloftop_m'_ /sng.
        subst m'.
        subst id_t.
        (* either the variable is local to the new frame and it was
           "not invisible" from enclosing one because it was free,
           either it is from a deeper frame and it was visible from
           enclosing frame. *)
        functional inversion heq_CEframeG_id_;subst /sng.
        + rewrite Nat.sub_diag in *. (* the variable is local *)
          unfold build_loads in h_CM_eval_expr_id_t_.
          simpl in h_CM_eval_expr_id_t_.
          inversion h_CM_eval_expr_id_t_;subst /sng.
          assert (v1 = stkptr_proc) /sng.
          { eapply det_eval_expr;eauto.
            apply cm_eval_addrstack_zero. }
          subst.
          assert (is_free_block m spb_proc ofs) /sng.
          { red.
            intros perm. 
            eapply fresh_block_alloc_perm_;eauto. }
          simpl in h_eval_binop_Oadd_v1_v2_.
          destruct v2;try discriminate.
          assert (Archi.ptr64 = false) by reflexivity /sng.
          rewrite heq_ptr64_ in h_eval_binop_Oadd_v1_v2_.
          inversion h_eval_binop_Oadd_v1_v2_ /sng.
          left.
          eapply is_free_block_disj;eauto.
        + (* The variable is deeper, so it is visible from stkptr *)
          assert (lvl_id < Datatypes.length CE_sufx)%nat /sng.
          { admit. }
          assert (exists δ', Datatypes.length CE_sufx - lvl_id = S δ')%nat /sng.
          { exists ((Datatypes.length CE_sufx - lvl_id) - 1)%nat.
            lia. }
          decomp h_ex_.
          rewrite heq_sub_ in h_eq_transl_var_ , h_CM_eval_expr_id_t_.
          specialize h_reachable_enclosing_variables_ with (1:=h_eq_transl_var_).
          specialize h_reachable_enclosing_variables_ with (1:=h_CM_eval_expr_id_t_).
          (* intermediate state where chained_stack do not hold. But
          the variable was accessible the same way from stkptr *)
          assert (eval_expr g stkptr locenv m_proc_pre_init
                             (build_loads (Datatypes.length CE_prefx + δ') δ_id)
                             (Values.Vptr spb_id ofs_id)) /sng. {
            inversion h_exec_stmt_ /sng.
            inversion h_CM_eval_expr_vaddr_ /sng.
            simpl in h_eval_constant_.
            inversion h_eval_constant_.
            subst.
            eapply storev_outside_struct_chain_preserves_var_addresses2
              with (3:=heq_storev_v_m_postchainarg_)
                   (lvl:=(Datatypes.length CE_prefx + Datatypes.length CE_sufx)%nat).
            all:cycle 1.
            - assert (Datatypes.length CE = (Datatypes.length CE_prefx + Datatypes.length CE_sufx)%nat) /sng.
              { erewrite <- CompilEnv.cut_until_spec1 with (s:=CE);eauto.
                apply app_length. }
              rewrite <- heq_length0_.
              assumption.
            - lia.
            - eapply eval_expr_build_load_inv_locenv;eauto.
            - intros /sng.
              eapply malloc_distinct_from_chaining_loads with (m:=m)(n:=n)(lvl:=Datatypes.length CE);eauto.
              + assert (Datatypes.length CE = (Datatypes.length CE_prefx + Datatypes.length CE_sufx)%nat) /sng.
                { erewrite <- CompilEnv.cut_until_spec1 with (s:=CE);eauto.
                  apply app_length. }
                lia.
              + eapply malloc_preserves_chaining_loads_2;eauto.
                eapply chained_stack_structure_le;eauto.
                assert (Datatypes.length CE = (Datatypes.length CE_prefx + Datatypes.length CE_sufx)%nat) /sng.
                { erewrite <- CompilEnv.cut_until_spec1 with (s:=CE);eauto.
                  apply app_length. }
                lia. }
              
          assert (eval_expr g stkptr locenv m
                            (build_loads (Datatypes.length CE_prefx + δ') δ_id)
                            (Values.Vptr spb_id ofs_id))
            as h_reachable_enclosing_variables_in_m_. {
                unfold build_loads in h_CM_eval_expr_|- *.
                inversion h_CM_eval_expr_ /sng.
                econstructor.
                - eapply malloc_preserves_chaining_loads_2;eauto.
                  + eapply chained_stack_structure_le;eauto.
                    assert (Datatypes.length CE = (Datatypes.length CE_prefx + Datatypes.length CE_sufx)%nat) /sng.
                    { erewrite <- CompilEnv.cut_until_spec1 with (s:=CE);eauto.
                      apply app_length. }
                    lia.
                - eapply eval_expr_Econst_inv_locenv;eauto.
                - assumption.
              }
          (* the variable was accesssible the same way in (locenv,m) *)
          assert (transl_variable st CE astnum id
                                   =: build_loads (Datatypes.length CE_prefx + δ') δ_id) /sng. {
            unfold transl_variable.
            assert (CE = CE_prefx++CE_sufx) /sng. {
              erewrite CompilEnv.cut_until_spec1;eauto. }
            rewrite heq_CE_.            
            erewrite CompilEnv.nodupG_fetchG_app;eauto.
            - erewrite CompilEnv.nodupG_frameG_app;eauto.
              + cbn.
                erewrite foo;eauto.
                * f_equal.
                  f_equal.
                  rewrite app_length.
                  lia.
                * intro abs.
                  apply app_eq_nil in abs.
                  decomp abs.
                  subst.
                  cbn in heq_sub_.
                  inversion heq_sub_.
                * rewrite <- heq_CE_.
                  eapply h_inv_comp_CE_st_.
              + rewrite <- heq_CE_.
                eapply h_inv_comp_CE_st_.
            - rewrite <- heq_CE_.
              eapply h_inv_comp_CE_st_.
            - functional inversion heq_CEfetchG_id_;subst /sng.
              + exfalso.
                rewrite CompilEnv.reside_false_fetch_none_ in heq_reside_.
                rewrite heq_reside_ in heq_CEfetch_id_.
                discriminate heq_CEfetch_id_.
              + assumption. }
          unfold invisible_cminor_addr in h_invis_stkptr__m_addr_ofs_.
          specialize h_invis_stkptr__m_addr_ofs_
            with (1:=heq_transl_variable0_) (2:=heq_compute_chnk_id_)
                 (3:= h_reachable_enclosing_variables_in_m_).
          assumption. }
    
    assert (forall astnum,Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m_postchainarg) as h_unch_m_mpostchain_. {
      intro.
      split.
      - eapply Coqlib.Ple_trans with (q:=Mem.nextblock m_proc_pre_init).
        + erewrite (Mem.nextblock_alloc _ _ _ _ _ h_alloc_).
          apply Coqlib.Ple_succ.
        + inversion h_exec_stmt_ /sng.
          inversion h_CM_eval_expr_vaddr_ /sng.
          simpl in h_eval_constant_.
          inversion h_eval_constant_.
          subst.
          simpl Mem.storev in heq_storev_v_m_postchainarg_.
          erewrite Mem.nextblock_store with (1:=heq_storev_v_m_postchainarg_).
          apply Coqlib.Ple_refl.
      - intros /sng.
        inversion h_exec_stmt_ /sng.
        inversion h_CM_eval_expr_vaddr_ /sng.
        simpl in h_eval_constant_.
        inversion h_eval_constant_.
        subst.
        simpl Mem.storev in heq_storev_v_m_postchainarg_.
        transitivity (Mem.perm m_proc_pre_init b ofs k p0);split /sng.
        + intro hperm.
          eapply Mem.perm_alloc_1;eauto.
        + intros hperm.
          eapply Mem.perm_alloc_4;eauto.
          intro abs.
          subst.
          eapply Mem.fresh_block_alloc_;eauto.
        + intros hperm.
          eapply Mem.perm_store_1; eauto.
        + intros hperm.
          eapply Mem.perm_store_2; eauto.
      - intros /sng.
        inversion h_exec_stmt_ /sng.
        inversion h_CM_eval_expr_vaddr_ /sng.
        simpl in h_eval_constant_.
        inversion h_eval_constant_.
        subst.
        simpl Mem.storev in heq_storev_v_m_postchainarg_.
        rewrite Mem.store_mem_contents with (1:=heq_storev_v_m_postchainarg_).
        transitivity (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m_proc_pre_init))).
        + red in h_forbid_m_m_b_ofs_.
          decomp h_forbid_m_m_b_ofs_.
          destruct (Pos.eq_dec b spb_proc) /sng.
          * subst.
            exfalso.
            apply h_neg_free_blck_m_b_ofs_.
            red.
            intros /sng.
            eapply fresh_block_alloc_perm_;eauto.
          * erewrite Maps.PMap.gso;eauto.
        + specialize Mem.alloc_unchanged_on
            with (P:=forbidden st CE g astnum locenv stkptr m m)
                 (1:=h_alloc_)
            as h.
          destruct h;eauto. }

    (* matchenv between suffix_s and the cminor with stkptr = enclosing frame address. *)
    assert (match_env_ st suffix_s CE_sufx chaining_expr_from_caller_v
                      locenv_postchainarg g m_postchainarg) /sng. {
      assert (strong_match_env_ st s CE stkptr locenv g m_postchainarg) /sng.
      { admit. (* match_env_ + nodup = strong_match_env_ *) }
      specialize strong_match_env_match_env_sublist_
        with (1:=h_strg_mtch_s_CE_m_postchainarg_)
             (2:=h_inv_comp_CE_st_)
             (3:=h_CEcut_CE_pb_lvl_)
        as ? /sng.
      decomp h_ex_.
      edestruct cut_until_uniqueness with (1:=h_stkcut_s_pb_lvl_)(2:=h_stkcut_s_n_);subst.
      specialize chain_repeat_loadv_1 with (2:=h_repeat_loadv_) as ? /sng.
      assert ((Datatypes.length CE - Datatypes.length CE_sufx = Datatypes.length CE_prefx)%nat) /sng. {
        assert (Datatypes.length CE = (Datatypes.length CE_prefx + Datatypes.length CE_sufx)%nat) /sng.
        { erewrite <- CompilEnv.cut_until_spec1 with (s:=CE);eauto.
          apply app_length. }
        lia. }
      rewrite heq_sub_ in h_impl_forall_g_.
      assert (chained_stack_structure m_postchainarg (Datatypes.length CE_prefx) stkptr) /sng. {
        eapply chained_stack_structure_le;eauto.
        assert (Datatypes.length CE = (Datatypes.length CE_prefx + Datatypes.length CE_sufx)%nat) /sng.
        { erewrite <- CompilEnv.cut_until_spec1 with (s:=CE);eauto.
          apply app_length. }
        lia. }
      specialize h_impl_forall_g_ with (1:=h_chain_m_postchainarg1_) (g:=g)(e:=locenv).
      specialize det_eval_expr with (1:=h_impl_forall_g_)(2:=h_CM_eval_expr_chaining_expr_from_caller_v0_) as ?;subst.
      eapply h_forall_locenv_. }

    subst.
    pose (pb_lvl:=Datatypes.length CE_sufx).
    up_type.
    assert (pb_lvl = Datatypes.length suffix_s) /sng. {
      erewrite <- (cut_until_exact_levelG _ _ _ _ _ _ h_stkcut_s_n_).
      reflexivity. }
    
    assert (h_exact_lvlG_:forall x, exact_levelG ((pb_lvl, x) :: suffix_s)). {
      rewrite heq_pb_lvl_.
      econstructor.
      apply h_match_env0_. }

    assert (CompilEnv.exact_levelG CE_sufx) /sng. {
      eapply CompilEnv.exact_levelG_sublist2 with (CE1:=CE_prefx);eauto.
      erewrite (CompilEnv.cut_until_spec1 _ _ _ _ h_CEcut_CE_pb_lvl_);eauto. }

    assert (h_cm_exact_lvlG_:forall x,CompilEnv.exact_levelG ((pb_lvl, x) :: CE_sufx)). {
      constructor.
      eapply CompilEnv.exact_levelG_sublist2 with (CE1:=CE_prefx).
      erewrite (CompilEnv.cut_until_spec1 _ _ _ _ h_CEcut_CE_pb_lvl_);eauto. }

    (* The frame of the new procedure call is empty on bith side. *)
    (* the pre-copy_in env before copy_in match_env_ with the pre-copy_in env in spark. *)
    assert (match_env_ st ((pb_lvl, [ ])::suffix_s) ((pb_lvl, []) :: CE_sufx)
                       stkptr_proc locenv_postchainarg g m_postchainarg) /sng. 
    {
      split.
      all:swap 7 8.
      - red.
        intros /sng.
        functional inversion heq_transl_name_;subst /sng.
        functional inversion h_eq_transl_var_;subst /sng.
        functional inversion heq_CEframeG_id_;subst /sng.
        + exfalso.
          cbn in heq_reside_.
          discriminate.
        + assert (m'>lvl_id)%nat /sng. {
            cbn in heq_lvloftop_m'_.
            inversion heq_lvloftop_m'_.
            unfold pb_lvl.
            eapply CompilEnv.exact_levelG_frameG_lt_lgth.
            * assumption.
            * eassumption. }
          assert (exists lvl, (m' - lvl_id)%nat = S lvl) /sng. {
            exists (m' - lvl_id - 1)%nat.
            lia. }
          decomp h_ex_.
          rewrite heq_sub_ in *.
          specialize (h_match_env0_ /sng.(me_stack_match)) as ?.
          red in h_stk_mtch_suffix_s_m_postchainarg_.
          unfold build_loads in heq_make_load_.
          
          functional inversion heq_make_load_ /sng.
          specialize h_stk_mtch_suffix_s_m_postchainarg_
            with (cm_typ_nme:=cm_typ_nme)(typ_nme:=typ_nme)(nme:=(Identifier astnum id))
                 (vaddr:=nme_t_v)(v:=v)(addr_nme:=(build_loads lvl δ_id))
                 (load_addr_nme:=(Eload chunk (build_loads lvl δ_id))).
          edestruct h_stk_mtch_suffix_s_m_postchainarg_;auto /sng.
          * cbn in heq_CEframeG_id_,heq_CEfetchG_id_,heq_lvloftop_m'_.
            unfold transl_name,transl_variable.
            rewrite heq_CEfetchG_id_,heq_CEframeG_id_.
            invclear heq_lvloftop_m'_ /sng.
            assert (CompilEnv.level_of_top CE_sufx = Some (Datatypes.length CE_sufx - 1)%nat) /sng. {
              rewrite foo with (CE:=CE_sufx);auto.
              - intro abs.
                subst .
                simpl in h_gt_m'_lvl_id_.
                lia. }
            rewrite heq_lvloftop_CE_sufx_.
            do 2 f_equal.
            lia.
          * unfold build_loads in h_CM_eval_expr_nme_t_nme_t_v_.
            Opaque build_loads_.
            inversion h_CM_eval_expr_nme_t_nme_t_v_;subst /sng.
            Transparent build_loads_.
            cbn in heq_lvloftop_m'_.
            invclear heq_lvloftop_m'_ /sng.
            assert (chained_stack_structure m_postchainarg (Datatypes.length CE_sufx - lvl_id) stkptr_proc) /sng. {
              apply chained_stack_structure_le  with (1:=h_chain_m_postchainarg_).
              lia. }
            subst m'.
            rewrite heq_sub_ in h_chain_m_postchainarg1_.
            specialize chained_stack_structure_decomp_S_2
              with (2:=h_CM_eval_expr_v1_)(1:=h_chain_m_postchainarg1_) as ? /sng.
            decomp h_ex_.
            subst_det_addrstack_zero.
            unfold build_loads.
            econstructor;eauto.
            inversion h_CM_eval_expr_v2_.
            econstructor;eauto.
          * inversion h_eval_name_nme_v_ /sng.
            simpl in heq_SfetchG_id_.
            constructor;auto.
          * unfold make_load.
            rewrite h_access_mode_cm_typ_nme_.
            reflexivity.
          * decomp h_and_; exists x;split;eauto.
            unfold build_loads in h_CM_eval_expr_x_.
            inversion h_CM_eval_expr_x_ /sng.
            econstructor. all:cycle 1.
            { eassumption. }
            inversion h_CM_eval_expr_vaddr_ /sng.
            econstructor. all:cycle 1.
            { eapply eval_expr_Econst_inv_locenv_noaddr;eauto. }
            { eassumption. }
            change (Eload AST.Mint32 (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl))
              with (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S lvl)).
            eapply chained_stack_structure_decomp_S_2'.
            -- apply chained_stack_structure_le  with (1:=h_chain_m_postchainarg_).
               rewrite <- heq_sub_.
               assert (S m'=S (Datatypes.length CE_sufx))%nat.
               { erewrite CompilEnv.exact_lvl_lvl_of_top with (2:=heq_lvloftop_m'_);eauto. }
               lia.
            -- eassumption.
            -- assumption.
      - constructor.
        + cbn.
          apply h_match_env0_.
        + cbn.
          intros /sng.
          eapply h_match_env0_.
          eassumption.
      - red.
        cbn.
        f_equal.
        rewrite <- heq_pb_lvl_.
        reflexivity.
      - apply nodup_cons.
        + apply h_match_env0_.
        + red.
          intros /sng.
          cbn in h_lst_in_.
          decomp h_lst_in_.
          * inversion heq_pair_ /sng.
            constructor.
          * intro abs. contradict abs.
      - red.
        constructor.
        + unfold non_empty_intersection_frame.
          lazy beta iota.
          intro abs.
          rewrite InA_alt in abs.
          decomp abs.
          subst pb_lvl.
          cbn in *.
          red in h_nonempty_inters_.
          decomp h_nonempty_inters_.
          inversion h_inA_e_ /sng.
        + apply h_match_env0_.
      - auto 1.
      - red.
        intros /sng.
        simpl in heq_SfetchG_id_.
        eapply h_match_env0_.(me_overflow);eauto.
      - split.
        + red.
          intros /sng.
          specialize (h_match_env0_ /sng.(me_safe_cm_env).(me_stack_match_addresses)) as ?.
          red in h_stk_mtch_addr_chaining_expr_from_caller_v_m_postchainarg_.
          specialize h_stk_mtch_addr_chaining_expr_from_caller_v_m_postchainarg_ with (nme:=nme).
          functional inversion heq_transl_name_ /sng.
          functional inversion h_eq_transl_var_ /sng.
          cbn in heq_CEfetchG_id_,heq_lvloftop_m'_,heq_CEframeG_id_.
          assert (CompilEnv.level_of_top CE_sufx = Some (Datatypes.length CE_sufx - 1)%nat) /sng. {
            rewrite foo with (CE:=CE_sufx);auto.
            - intro abs.
              subst CE_sufx.
              cbn in h_eq_transl_var_.
              discriminate. }
          invclear heq_lvloftop_m'_ /sng.
          subst.
          assert (transl_name st CE_sufx (Identifier astnum id) =:  build_loads (Datatypes.length CE_sufx - 1 - lvl_id) δ_id ) /sng. {
            unfold transl_name,transl_variable.
            rewrite heq_CEfetchG_id_,heq_CEframeG_id_,heq_lvloftop_CE_sufx_.
            reflexivity. }
          specialize h_stk_mtch_addr_chaining_expr_from_caller_v_m_postchainarg_ with (1:=heq_transl_name0_).
          decomp h_stk_mtch_addr_chaining_expr_from_caller_v_m_postchainarg_.
          exists addr.
          assert((Datatypes.length CE_sufx - lvl_id) = S (Datatypes.length CE_sufx - 1 - lvl_id))%nat /sng. {
            assert (lvl_id < Datatypes.length CE_sufx)%nat. {
              eapply CompilEnv.exact_levelG_frameG_lt_lgth;eauto. }
            lia. }
          rewrite heq_sub_.
          unfold build_loads in h_CM_eval_expr_addr_ |- *.
          inversion h_CM_eval_expr_addr_ /sng.
          econstructor.
          * eapply chained_stack_structure_decomp_S_2'.
            -- subst.
               apply chained_stack_structure_le with (1:=h_chain_m_postchainarg_).
               lia.
            -- eassumption.
            -- eassumption.
          * eapply eval_expr_Econst_inv_locenv_noaddr;eauto.
          * assumption.
        + admit. (* This has to be reformulated in safe_cm_env. It is false as it is stated currently *)
        + specialize ((h_match_env0_ /sng.(me_safe_cm_env)).(me_stack_separate)) as ?.
          unfold stack_separate in h_separate_CE_sufx_m_postchainarg_ |- *.
          intros /sng.
          specialize h_separate_CE_sufx_m_postchainarg_
            with (1:=heq_type_of_name_) (2:=heq_type_of_name0_)
                 (5:=heq_transl_type_)(6:=heq_transl_type0_)
                 (9:=h_access_mode_cm_typ_nme_)(10:=h_access_mode_cm_typ_nme'_)
                 (11:=hneq_nme) (k₁:=k₁) (δ₁:=δ₁)(k₂:=k₂) (δ₂:=δ₂).

          assert (CompilEnv.exact_levelG CE_sufx) /sng. {
            specialize ci_exact_lvls with (1:=h_inv_CE''_bld_) as ? /sng.
            inversion h_exct_lvlG_;eauto /sng. }
          assert (CompilEnv.exact_levelG ((pb_lvl, [ ]) :: CE_sufx)) /sng. {
            assert (pb_lvl=Datatypes.length CE_sufx).
            - inversion h_exct_lvlG_CE_sufx_;subst;auto.
            - subst.
              econstructor.
              assumption. }              
          specialize exact_lvl_transl_name_empty_top with (1:=h_exct_lvlG_) (2:=heq_transl_name_) as ? /sng.
          specialize exact_lvl_transl_name_empty_top with (1:=h_exct_lvlG_) (2:=heq_transl_name0_) as ? /sng.
          decomp h_ex_.
          decomp h_ex0_.
          subst.
          assert (chained_stack_structure m_postchainarg (S δ) stkptr_proc) /sng. {
            apply chained_stack_structure_le with (n:=S (Datatypes.length CE_sufx));auto.
            specialize exact_level_transl_name with (1:=h_exct_lvlG_CE_sufx_)(2:=heq_transl_name1_) as ? ;eauto /sng. }
          assert (chained_stack_structure m_postchainarg (S δ0) stkptr_proc) /sng. {
            apply chained_stack_structure_le with (n:=S (Datatypes.length CE_sufx));auto.
            specialize exact_level_transl_name with (1:=h_exct_lvlG_CE_sufx_)(2:=heq_transl_name2_) as ? ;eauto /sng. }
          eapply h_separate_CE_sufx_m_postchainarg_;eauto.
          * unfold build_loads in h_CM_eval_expr_nme_t_,h_CM_eval_expr_nme'_t_.
            Opaque build_loads_.
            inversion h_CM_eval_expr_nme_t_ /sng.
            Transparent build_loads_.
            specialize chained_stack_structure_decomp_S_2
              with (1:=h_chain_m_postchainarg1_)(2:=h_CM_eval_expr_v1_)
              as ? /sng.
            decomp h_ex_.
            assert (sp' = chaining_expr_from_caller_v) /sng. {
              eapply det_eval_expr;eauto. }
            subst sp'.
            unfold build_loads.
            econstructor;eauto.
            eapply eval_expr_Econst_inv_locenv_noaddr;eauto.
          * unfold build_loads in h_CM_eval_expr_nme'_t_.
            Opaque build_loads_.
            inversion h_CM_eval_expr_nme'_t_ /sng.
            Transparent build_loads_.
            specialize chained_stack_structure_decomp_S_2
              with (1:=h_chain_m_postchainarg2_)(2:=h_CM_eval_expr_v1_)
              as ? /sng.
            decomp h_ex_.
            assert (sp' = chaining_expr_from_caller_v) /sng. {
              eapply det_eval_expr;eauto. }
            subst sp'.
            unfold build_loads.
            econstructor;eauto.
            eapply  eval_expr_Econst_inv_locenv_noaddr;eauto.
        + red.
          cbn.
          intros /sng.
          destruct δ_lvl.
          * cbn.
            exists spb_proc.
            eapply cm_eval_addrstack_zero_chain ;eauto.
          * specialize h_match_env0_ /sng.(me_safe_cm_env).(me_stack_localstack_aligned) as ?.
            red in h_aligned_g_m_postchainarg_.
            apply le_S_n in h_le_δ_lvl_.
            specialize h_aligned_g_m_postchainarg_ with (1:=h_le_δ_lvl_).
            decomp h_aligned_g_m_postchainarg_.
            exists b_δ.
            eapply chained_stack_structure_decomp_S_2'.
            -- subst.
               apply chained_stack_structure_le with (1:=h_chain_m_postchainarg_).
               lia.
            -- eassumption.
            -- eassumption.
        + red. red. cbn.
          intros /sng.
          eapply h_match_env0_.(me_safe_cm_env).(me_stack_no_null_offset) ; eauto.
        + red.
          intros /sng.
          assert (CompilEnv.exact_levelG ((pb_lvl, [ ]) :: CE_sufx)) by auto /sng.
          functional inversion h_eq_transl_var_ /sng.
          specialize exact_lvl_transl_variable_empty_top with (1:=h_exct_lvlG_)(2:=h_eq_transl_var_) as ? /sng.
          decomp h_ex_.
          eapply h_match_env0_.(me_safe_cm_env).(me_stack_freeable);eauto.
          subst.
          rewrite heq_id_t_ in h_CM_eval_expr_id_t_.
          unfold build_loads in h_CM_eval_expr_id_t_.
          Opaque build_loads_.
          inversion h_CM_eval_expr_id_t_ /sng.
          Transparent build_loads_.
          
          assert (δ < S (Datatypes.length CE_sufx))%nat /sng. {
            specialize transl_variable_exact_lvl_le_toplvl with (1:=h_exct_lvlG_CE_sufx_)(2:=heq_transl_variable0_) as ? /sng.
            lia. }
          specialize chained_stack_structure_decomp_S
            with (1:=h_chain_m_postchainarg_)(2:=h_lt_δ_) (3:=h_CM_eval_expr_v1_) as ? /sng.
          decomp h_ex_.
          assert (sp' = chaining_expr_from_caller_v). {
            eapply det_eval_expr;eauto. }
          subst.
          unfold build_loads.
          econstructor;eauto.
          eapply eval_expr_Econst_inv_locenv_noaddr with (1:=h_CM_eval_expr_v2_);eauto.
        + cbn.
          assumption. }

    specialize transl_expr_ok with (3:=h_match_env_) as ? /sng.


    (*Lemma copy_in_push:
      ∀ l' st s lvl initf prm_prof e lexp l i v,
      copyIn st s (lvl,initf) (prm_prof::l') (e::lexp) (OK (lvl, l++ (i, v):: initf))
        → Datatypes.length l = Datatypes.length l'
          ∧ i = parameter_name prm_prof
          ∧ match parameter_mode prm_prof with
             | In => evalExp st s e (OK v)
             | Out => v = Undefined
             | InOut => evalExp st s e (OK v)
            end
          ∧ copyIn st s (lvl, (i, v):: initf) (l') (lexp) (OK (lvl, l++(i, v):: initf)).
      Proof.
        induction l';intros /sng.
        - simpl in * |- *.
          inversion h_copy_in_ /sng.
          + inversion h_copy_in0_ /sng.
            assert ((l ++ (i, v) :: initf) = ((l ++ [(i, v)]) ++ initf)) /sng. {
              simpl.
              rewrite <- app_assoc.
              simpl.
              reflexivity. }
            rewrite heq_app_ in heq_cons_.
            change ((parameter_name prm_prof, e_v) :: initf)
                   with ([(parameter_name prm_prof, e_v)] ++ initf) in heq_cons_.
            apply app_same_length_eq2_ in heq_cons_;auto.
            decomp heq_cons_.
            destruct l /sng.
            * repeat split;auto;simpl in *;inversion heq_cons_ /sng.
              -- reflexivity.
              -- rewrite heq_parameter_mode_.
                 assumption.
              -- assumption.
            * exfalso.
              simpl in heq_cons_.
              assert (List.length [(parameter_name prm_prof, e_v)] = List.length (p :: l ++ [(i, v)])) /sng. {
                rewrite  heq_cons_;auto. }
              simpl in heq_length_.
              rewrite app_length in heq_length_.
              simpl in heq_length_.
              lia.
          + inversion h_copy_in0_ /sng.
            assert ((l ++ (i, v) :: initf) = ((l ++ [(i, v)]) ++ initf)) /sng. {
              simpl.
              rewrite <- app_assoc.
              simpl.
              reflexivity. }
            rewrite heq_app_ in heq_cons_.
            change ((parameter_name prm_prof, Int v0) :: initf)
                   with ([(parameter_name prm_prof, Int v0)] ++ initf) in heq_cons_.
            apply app_same_length_eq2_ in heq_cons_;auto.
            decomp heq_cons_.
            destruct l /sng.
            * repeat split;auto;simpl in *; inversion heq_cons_ /sng.
              -- reflexivity.
              -- rewrite heq_parameter_mode_.
                 inversion heq_cons_ /sng.
                 assumption.
              -- assumption.
            * exfalso.
              simpl in heq_cons_.
              assert (List.length [(parameter_name prm_prof, Int v0)] = List.length (p :: l ++ [(i, v)])) /sng. {
                rewrite  heq_cons_;auto. }
              simpl in heq_length_.
              rewrite app_length in heq_length_.
              simpl in heq_length_.
              lia.
          + inversion h_copy_in0_ /sng.
            assert ((l ++ (i, v) :: initf) = ((l ++ [(i, v)]) ++ initf)) /sng. {
              simpl.
              rewrite <- app_assoc.
              simpl.
              reflexivity. }
            rewrite heq_app_ in heq_cons_.
            change ((parameter_name prm_prof, v0) :: initf)
                   with ([(parameter_name prm_prof, v0)] ++ initf) in heq_cons_.
            apply app_same_length_eq2_ in heq_cons_;auto.
            decomp heq_cons_.
            destruct l /sng.
            * repeat split;auto;simpl in *; inversion heq_cons_ /sng.
              -- reflexivity.
              -- rewrite heq_parameter_mode_.
                 constructor.
                 assumption.
              -- assumption.
            * inversion heq_cons_ /sng.
              exfalso.
              eapply app_cons_not_nil with (a:=(i, v));eauto.
          + inversion h_copy_in0_ /sng.
            assert ((l ++ (i, v) :: initf) = ((l ++ [(i, v)]) ++ initf)) /sng. {
              simpl.
              rewrite <- app_assoc.
              simpl.
              reflexivity. }
            rewrite heq_app_ in heq_cons_.
            change ((parameter_name prm_prof, Int v0) :: initf)
                   with ([(parameter_name prm_prof, Int v0)] ++ initf) in heq_cons_.
            apply app_same_length_eq2_ in heq_cons_;auto.
            decomp heq_cons_.
            destruct l /sng.
            * simpl in *.
              repeat split;auto; inversion heq_cons_ /sng.
              -- reflexivity.
              -- rewrite heq_parameter_mode_.
                 constructor.
                 assumption.
              -- assumption.
            * exfalso.
              simpl in heq_cons_.
              assert (List.length [(parameter_name prm_prof, Int v0)] = List.length (p :: l ++ [(i, v)])) /sng. {
                rewrite  heq_cons_;auto. }
              simpl in heq_length_.
              rewrite app_length in heq_length_.
              simpl in heq_length_.
              lia.
          + inversion h_copy_in0_ /sng.
            assert ((l ++ (i, v) :: initf) = ((l ++ [(i, v)]) ++ initf)) /sng. {
              simpl.
              rewrite <- app_assoc.
              simpl.
              reflexivity. }
            rewrite heq_app_ in heq_cons_.
            change ((parameter_name prm_prof, Undefined) :: initf)
                   with ([(parameter_name prm_prof, Undefined)] ++ initf) in heq_cons_.
            apply app_same_length_eq2_ in heq_cons_;auto.
            decomp heq_cons_.
            destruct l /sng.
            * simpl in *.
              repeat split;inversion heq_cons_ /sng.
              -- reflexivity.
              -- rewrite heq_parameter_mode_.
                 reflexivity.
              -- assumption.
            * exfalso.
              simpl in heq_cons_.
              assert (List.length [(parameter_name prm_prof, Undefined)] = List.length (p :: l ++ [(i, v)])) /sng. {
                rewrite  heq_cons_;auto. }
              simpl in heq_length_.
              rewrite app_length in heq_length_.
              simpl in heq_length_.
              lia.
        - inversion h_copy_in_ /sng.
          unfold ST.push in h_copy_in0_.
          simpl in h_copy_in0_.
          assert (exists a' lexp',  copyIn st s (lvl, (parameter_name prm_prof, e_v) :: initf) (a :: l') (a'::lexp') (OK (lvl, l ++ (i, v) :: initf))) /sng. {
            admit.
          }
          decomp h_ex_.
          specialize IHl' with (1:=h_copy_in1_).
     *)

    Lemma copyIn_init':
      ∀ st args lparams bigs sto'',
        Forall3_rev1 (fun (prm:idnum * V) prm_prof e =>
                        forall k',
                          let (k,v) := prm in
                          transl_paramid k = k' ->
                          match parameter_mode prm_prof with
                          | In => evalExp st bigs e (OK v)
                          | Out => v = Undefined
                          | InOut => evalExp st bigs e (OK v)
                          end) sto'' lparams args ->
        ∀ g CE mcalling callinglocenv callingsp tlparams args_t args_t_v
          (CE_sufx : compilenv) s_parms sto,
          store_params st ((Datatypes.length CE_sufx, sto) :: CE_sufx) lparams =: s_parms -> 
          transl_paramexprlist st CE args lparams =: args_t ->
          Datatypes.length sto'' = Datatypes.length lparams ->
          transl_lparameter_specification_to_lident st lparams = tlparams -> 
          eval_exprlist g callingsp callinglocenv mcalling args_t args_t_v ->
          match_env_ st bigs CE callingsp callinglocenv g mcalling ->
          NoDupA (fun x y => x.(parameter_name) = y.(parameter_name)) lparams -> 
          ∀ locenv tlparams,
            set_params (args_t_v) tlparams = locenv ->
            Forall3_rev1
              (fun (prm:idnum * V) prm_prof arg  =>
                 forall k',
                   let (k,v) := prm in
                   transl_paramid k = k' ->
                   match parameter_mode prm_prof with
                   | In => exists v', transl_value v v' ∧ Maps.PTree.get k' locenv = Some v'
                   | Out => (v = Undefined)
                   | InOut => 
                     (* This part is ensured by typing/wellformedness (intialisation of inout vars)*)
                     exists v' chk,
                     transl_value v v' ∧
                     (compute_chnk_of_type st (parameter_subtype_mark prm_prof) =: chk)
                     ∧ (exists addr, Maps.PTree.get k' locenv = Some addr
                                     ∧ Mem.loadv chk mcalling addr = Some v')
                   end) sto'' lparams args.
        Proof.
          intros until 1 /sng.
          induction h_for3_sto''_lparams_args_;!intros;simpl /sng.
          - constructor.
          - constructor.
            + intros /sng.
              rename heq_length_ into heq.
              assert (Datatypes.length l = Datatypes.length l') /sng. {
                rewrite app_length in heq.
                simpl in heq.
                lia. }
              clear heq.
              destruct x;intros /sng.
              specialize h_forall_k'_ with (1:=heq_transl_paramid_).
              destruct (parameter_mode y) eqn:heq_mode_;up_type.
              * rew transl_paramexprlist_ok with functional inversion htrans_prmexprl;
                  match goal with
                  | H: parameter_mode ?a = ?x, H': parameter_mode ?a = ?y |- _ => try now (rewrite H in H';discriminate)
                  end /sng.
                specialize transl_expr_ok with (1:=heq_tr_expr_e_)
                                               (2:=h_forall_k'_) (3:=h_match_env_) as ? /sng.
                decomp h_ex_.
                exists e_t_v.
                split.
                -- assumption.
                -- rew store_params_ok with functional inversion heq_store_prms_ /sng.
                   subst.
                   admit.
              * assumption.
              * rew transl_paramexprlist_ok with functional inversion htrans_prmexprl;
                  match goal with
                  | H: parameter_mode ?a = ?x, H': parameter_mode ?a = ?y |- _ => try now (rewrite H in H';discriminate)
                  end /sng.



(*
  

  unfold transl_name in heq_transl_name_.
  destruct nme; try discriminate /sng.
  revert nme_t heq_transl_name_.
  functional induction (transl_variable stbl CE a i) ;try discriminate;simpl; !!intros /sng.
  

  invclear h_eval_name_v_;eq_same_clear /sng.
  - inversion h_eval_literal_;subst.
    + destruct v0 /sng.
      * eexists;split;intros; econstructor;eauto /sng.
      * eexists;split;intros;econstructor;eauto /sng.
    + eexists;split;intros /sng.
      * eapply (transl_literal_ok g _ _ h_eval_literal_ stkptr).
        econstructor.
      * constructor.
        reflexivity.
  - unfold value_at_addr in heq_value_at_addr_.
    destruct (transl_type stbl astnum_type) eqn:heq_transl_type_;simpl in *.
    + destruct h_match_env_ /sng.
      edestruct h_safe_cm_CE_m_.(me_stack_match_addresses) with (nme:=Identifier astnum id);eauto. 
      eapply h_stk_mtch_s_m_;eauto.
      * simpl.
        assumption.
      * simpl.
        rewrite heq_fetch_exp_type_.
        reflexivity.
    + discriminate.
  - decomp (h_forall_e'_ _ heq_tr_expr_e_ _ _ _ _ _ _ h_eval_expr_e_e_v_ h_match_env_).
    decomp (h_forall_e'0_ _ heq_tr_expr_e0_ _ _ _ _ _ _ h_eval_expr_e0_e0_v_ h_match_env_).
    assert (hex:or (exists b, v = Bool b) (exists n, v = Int n)). {
      apply do_run_time_check_on_binop_ok in h_do_rtc_binop_.
      rewrite binopexp_ok in h_do_rtc_binop_.
      functional inversion h_do_rtc_binop_;subst;eq_same_clear
       ;try contradiction;eauto /sng.
      unfold Math.mod' in  heq_mod'_.
      destruct e_v;try discriminate.
      destruct e0_v;try discriminate.
      inversion heq_mod'_.
      right;eauto. }
    decomp hex;subst.
    + destruct b; eexists;(split;[econstructor;eauto|]).
      * eapply eval_Ebinop;try econstructor;eauto.
        eapply binary_operator_ok with (v1:=e_v) (v2:=e0_v);eauto.
        econstructor;eauto.
      * eapply eval_Ebinop;try econstructor;eauto.
        eapply binary_operator_ok with (v1:=e_v) (v2:=e0_v);eauto.
        econstructor;eauto.
    + eexists;(split;[econstructor;eauto|]).
      eapply eval_Ebinop;try econstructor;eauto.
        eapply binary_operator_ok with (v1:=e_v) (v2:=e0_v);eauto.
        econstructor;eauto.
  - (* Unary minus *)
    simpl in heq_transl_unop_.
    eq_same_clear.
    specialize h_forall_e'_ with (1:=heq_tr_expr_e_) (2:=h_eval_expr_e_e_v_) (3:=h_match_env_).
    decomp h_forall_e'_.
    invclear h_do_rtc_unop_;eq_same_clear /sng.
    invclear h_overf_check_ /sng.
    eexists.
    split.
    * econstructor.
    * assert (h:=unaryneg_ok _ _ _ h_transl_value_e_v_e_t_v_ heq_unary_minus_).
      econstructor;eauto.
      simpl.
      inversion h.
      reflexivity.
  (* Not *)
  - invclear h_do_rtc_unop_;simpl in *;try eq_same_clear /sng.
    specialize h_forall_e'_ with (1:=heq_tr_expr_e_) (2:=h_eval_expr_e_e_v_) (3:=h_match_env_).
    decomp h_forall_e'_.
    generalize (not_ok _ _ _ h_transl_value_e_v_e_t_v_ heq_unary_operation_).
    intro /sng.
    exists (Values.Val.notbool e_t_v).
    split;auto.
    econstructor;simpl in *;eauto.
    + econstructor;eauto.
      reflexivity.
    + destruct e_t_v;simpl in *; try (inversion h_transl_value_e_v_e_t_v_;fail).
      unfold  Values.Val.cmp.
      simpl.
      unfold Values.Val.of_bool.
      reflexivity.
Qed.
*)
Admitted.




    Lemma copyIn_store_params_ok:
      ∀ st CE args lparams args_t ,
        transl_paramexprlist st CE args lparams =: args_t ->
        ∀ g callingsp callinglocenv mcalling args_t_v
          lvl sto' bigs, 
          copyIn st bigs (lvl, []) lparams args (OK (lvl, sto')) ->
          eval_exprlist g callingsp callinglocenv mcalling args_t args_t_v ->
          match_env_ st bigs CE callingsp callinglocenv g mcalling ->
          NoDupA (fun x y => x.(parameter_name) = y.(parameter_name)) lparams -> 
          ∀ locenv tlparams,
            transl_lparameter_specification_to_lident st lparams = tlparams -> 
            set_params (args_t_v) tlparams = locenv -> 
            Forall3_rev1
              (fun (prm:idnum * V) prm_prof arg  =>
                 forall k',
                   let (k,v) := prm in
                   transl_paramid k = k' ->
                   match parameter_mode prm_prof with
                   | In => exists v', transl_value v v' ∧ Maps.PTree.get k' locenv = Some v'
                   | Out => (v = Undefined)
                   | InOut => 
                     (* This part is ensured by typing/wellformedness (intialisation of inout vars)*)
                     exists v' chk,
                     transl_value v v' ∧
                     (compute_chnk_of_type st (parameter_subtype_mark prm_prof) =: chk)
                     ∧ (exists addr, Maps.PTree.get k' locenv = Some addr
                                     ∧ Mem.loadv chk mcalling addr = Some v')
                   end) sto' lparams args.
    Proof.
      intros until lparams /sng.
      
      rew transl_paramexprlist_ok with
          functional induction function_utils.transl_paramexprlist st CE args lparams;
        try (now (simpl in *; discriminate));!intros /sng.
      - inversion h_copy_in_.
        constructor.
      - admit. (*rename p1 into prmSpec.
        rename p2 into lprmSpec.
        rename e2 into l_exp_args.
        rename e into exp_args.
        rename x0 into l_e_t.
        (* no choice in that instantiation: *)
        specialize copyIn_init with (1:=h_copy_in_)(2:=eq_refl)(3:=eq_refl) as ? /sng.
        decomp h_ex_.
        subst.
        intro h_forall3_.
        
        inversion h_NoDupA_ /sng.
        specialize h_forall_args_t_ with (bigs:=bigs)(lvl:=lvl)
                                        (1:=htrans_prmexprl)(5:=h_NoDupA_lprmSpec_).
        invclear heq_OK_ /sng.
        inversion h_CM_eval_exprl_args_t_args_t_v_ /sng.
        clear h_CM_eval_exprl_args_t_args_t_v_.
        specialize h_forall_args_t_ with (1:=h_CM_eval_exprl_l_e_t_vl_)(3:=h_match_env_).
        inversion h_copy_in_;
          match goal with
          | H: parameter_mode ?a = ?x, H': parameter_mode ?a = ?y |- _ => try now (rewrite H in H';discriminate)
          end /sng.
        + unfold ST.push in h_copy_in0_.
          simpl  in h_copy_in0_.

(* exists_last *)

          assert (exists sto'', sto' = sto''++ [(parameter_name prmSpec, exp_args_v)] ) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ? /sng.
            decomp h_ex_;subst.
            exists l';auto. }
          decomp h_ex_.
          subst sto'.
          specialize h_forall_args_t_ with (sto':=sto'').
          up_type.
          assert (copyIn st bigs (lvl, [ ]) lprmSpec l_exp_args (OK (lvl, sto''))) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ?  /sng.
            decomp h_ex_.
            specialize h_forall_ll_ with (ll:=nil) /sng.
            assert (sto''=l'). {
              eapply app_inv_tail with (l:=[(parameter_name prmSpec, exp_args_v)]);eauto. }
            subst.
            rewrite app_nil_r in h_forall_ll_.
            assumption. }
          specialize h_forall_args_t_ with (1:=h_copy_in1_)(2:=eq_refl)(3:=eq_refl).
          rewrite rev_unit.
          constructor;intros /sng.
          * rewrite heq_parameter_mode_.
            specialize transl_expr_ok
              with (1:=heq_tr_expr_e_) (2:=h_eval_expr_exp_args_exp_args_v_)
                   (3:=h_match_env_)
              as ? /sng.
            decomp h_ex_.
            rename e_t_v0 into v'.
            autorename h_transl_value_exp_args_v_e_t_v0_. 
            autorename h_CM_eval_expr_e_t_e_t_v0_. 
            exists v';split;auto.
            intros /sng.
            simpl.
            subst.
            rewrite Maps.PTree.gss.
            specialize transl_expr_ok with (1:=heq_tr_expr_e_) (2:=h_eval_expr_exp_args_exp_args_v_)
                                            (3:=h_match_env_) as ? /sng.
            decomp h_ex_.
            rewrite transl_value_det with (2:=h_transl_value_exp_args_v_e_t_v0_) (1:=h_transl_value_exp_args_v_v'_).
            f_equal.
            eapply det_eval_expr;eauto.
          * specialize transl_expr_ok
              with (1:=heq_tr_expr_e_) (2:=h_eval_expr_exp_args_exp_args_v_)
                   (3:=h_match_env_)
              as ? /sng.
            decomp h_ex_.
            rename e_t_v0 into v'.
            autorename h_transl_value_exp_args_v_e_t_v0_. 
            autorename h_CM_eval_expr_e_t_e_t_v0_. 
             (eapply Forall2_impl with (2:=h_forall_args_t_); intros) /sng.
            destruct a;intros /sng.
            specialize h_forall_k'_ with (1:=heq_transl_paramid_).
            destruct (parameter_mode b).
            -- decomp h_forall_k'_.
               exists t_t;split;auto.
               simpl.
               rewrite Maps.PTree.gso.
               ++ assumption.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {

                    apply transl_lparameter_specification_to_lident_nodup;auto. }

                    specialize set_params_in with (1:=heq_mget_k'_t_t_) as? /sng.
                  simpl in h_nodup_.
                  subst k'.
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto.
            -- auto.
            -- decomp h_forall_k'_.
               exists t_t, chk;split;[|split];auto.
               simpl.
               rewrite Maps.PTree.gso.
               ++ eexists;split.
                  ** eapply heq_mget_k'_addr_.
                  ** assumption.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {
                    apply transl_lparameter_specification_to_lident_nodup;auto. }
                  specialize set_params_in with (1:=heq_mget_k'_addr_) as ? /sng.
                  simpl in h_nodup_.
                  subst k'.
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto.
        + unfold ST.push in h_copy_in0_.
          simpl  in h_copy_in0_.
          assert (exists sto'', sto' = sto''++ [(parameter_name prmSpec, Int v)] ) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ? /sng.
            decomp h_ex_;subst.
            exists l';auto. }
          decomp h_ex_.
          subst sto'.
          specialize h_forall_args_t_ with (sto':=sto'').
          up_type.
          assert (copyIn st bigs (lvl, [ ]) lprmSpec l_exp_args (OK (lvl, sto''))) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ?  /sng.
            decomp h_ex_.
            specialize h_forall_ll_ with (ll:=nil) /sng.
            assert (sto''=l'). {
              eapply app_inv_tail with (l:=[(parameter_name prmSpec, Int v)]);eauto. }
            subst.
            rewrite app_nil_r in h_forall_ll_.
            assumption. }
          specialize h_forall_args_t_ with (1:=h_copy_in1_)(2:=eq_refl)(3:=eq_refl).
          rewrite rev_unit.
          constructor;intros /sng.
          * rewrite heq_parameter_mode_.
            intros /sng.
            simpl.
            subst.
            rewrite Maps.PTree.gss.
            specialize transl_expr_ok with (1:=heq_tr_expr_e_) (2:=h_eval_expr_exp_args_)
                                            (3:=h_match_env_) as ? /sng.
            decomp h_ex_.
            exists e_t_v0;split;auto.
            f_equal.
            eapply det_eval_expr;eauto.
          *  (eapply Forall2_impl with (2:=h_forall_args_t_); intros) /sng.
            destruct a;intros /sng.
            specialize h_forall_k'_ with (1:=heq_transl_paramid_).
            destruct (parameter_mode b).
            -- decomp h_forall_k'_. 
               exists t_t;split;auto.
               simpl.
               rewrite Maps.PTree.gso.
               ++ assumption.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {
                    apply transl_lparameter_specification_to_lident_nodup;auto. }
                  specialize set_params_in with (1:=heq_mget_k'_t_t_) as ? /sng.
                  simpl in h_nodup_.
                  subst k'.
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto.
            -- auto.
            -- intros /sng.
               decomp h_forall_k'_.
               exists t_t , chk;split;[|split];auto.
               simpl.
               rewrite Maps.PTree.gso.
               ++ eexists.
                  split.
                  ** eapply heq_mget_k'_addr_.
                  ** assumption.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {
                    apply transl_lparameter_specification_to_lident_nodup;auto. }
                  specialize set_params_in with (1:=heq_mget_k'_addr_) as ? /sng.
                  simpl in h_nodup_.
                  subst k'.
                  specialize set_params_in with (1:=heq_mget_k'_addr_) as ? /sng.
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto. *)
      - rename p1 into prmSpec.
        rename p2 into lprmSpec.
        rename e2 into l_exp_args.
        rename nme into nme_args.
        rename x0 into l_e_t.
        (* no choice in that instantiation: *)
        inversion h_NoDupA_ /sng.
        specialize h_forall_args_t_ with (bigs:=bigs)(lvl:=lvl)
                                        (1:=htrans_prmexprl)(5:=h_NoDupA_lprmSpec_).
        admit. (*
        invclear heq_OK_ /sng.
        inversion h_CM_eval_exprl_args_t_args_t_v_ /sng.
        clear h_CM_eval_exprl_args_t_args_t_v_.
        specialize h_forall_args_t_ with (1:=h_CM_eval_exprl_l_e_t_vl_)(3:=h_match_env_).
        inversion h_copy_in_;
          match goal with
          | H: parameter_mode ?a = ?x, H': parameter_mode ?a = ?y |- _ => try now (rewrite H in H';discriminate)
          end /sng.
        + unfold ST.push in h_copy_in0_.
          simpl  in h_copy_in0_.
          assert (exists sto'', sto' = sto''++ [(parameter_name prmSpec, Undefined)] ) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ? /sng.
            decomp h_ex_;subst.
            exists l';auto. }
          decomp h_ex_.
          subst sto'.
          specialize h_forall_args_t_ with (sto':=sto'').
          up_type.
          assert (copyIn st bigs (lvl, [ ]) lprmSpec l_exp_args (OK (lvl, sto''))) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ?  /sng.
            decomp h_ex_.
            specialize h_forall_ll_ with (ll:=nil) /sng.
            assert (sto''=l'). {
              eapply app_inv_tail with (l:=[(parameter_name prmSpec, Undefined)]);eauto. }
            subst.
            rewrite app_nil_r in h_forall_ll_.
            assumption. }
          specialize h_forall_args_t_ with (1:=h_copy_in1_)(2:=eq_refl)(3:=eq_refl).
          rewrite rev_unit.
          constructor;intros /sng.
          * rewrite heq_parameter_mode_.
            reflexivity.
          *  (eapply Forall2_impl with (2:=h_forall_args_t_); intros) /sng.
            destruct a;intros /sng.
            specialize h_forall_k'_ with (1:=heq_transl_paramid_).
            destruct (parameter_mode b).
            -- decomp h_forall_k'_.
               exists t_t;split;auto.
               simpl.
               rewrite Maps.PTree.gso.
               ++ assumption.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {
                    apply transl_lparameter_specification_to_lident_nodup;auto. }
                  specialize set_params_in with (1:=heq_mget_k'_t_t_) as ? /sng.
                  simpl in h_nodup_.
                  subst k'.                 
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto.
            -- auto.
            -- intros /sng.
               decomp h_forall_k'_.
               exists t_t,chk;split;[|split];auto.
               simpl.
               rewrite Maps.PTree.gso.
               ++ eexists.
                  split.
                  ** eapply heq_mget_k'_addr_.
                  ** assumption.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {
                    apply transl_lparameter_specification_to_lident_nodup;auto. }
                  specialize set_params_in with (1:=heq_mget_k'_addr_) as ? /sng.
                  simpl in h_nodup_.
                  subst k'.
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto. *)
      - rename p1 into prmSpec.
        rename p2 into lprmSpec.
        rename e2 into l_exp_args.
        rename nme into nme_args.
        rename x0 into l_e_t.
        (* no choice in that instantiation: *)
        inversion h_NoDupA_ /sng.
        specialize h_forall_args_t_ with (bigs:=bigs)(lvl:=lvl)
                                        (1:=htrans_prmexprl)(5:=h_NoDupA_lprmSpec_).
        admit. (*
        invclear heq_OK_ /sng.
        inversion h_CM_eval_exprl_args_t_args_t_v_ /sng.
        clear h_CM_eval_exprl_args_t_args_t_v_.
        specialize h_forall_args_t_ with (1:=h_CM_eval_exprl_l_e_t_vl_)(3:=h_match_env_).
        inversion h_copy_in_;
          match goal with
          | H: parameter_mode ?a = ?x, H': parameter_mode ?a = ?y |- _ => try now (rewrite H in H';discriminate)
          end /sng.
        + rename v into nme_args_v.
          unfold ST.push in h_copy_in0_.
          simpl  in h_copy_in0_.
          assert (exists sto'', sto' = sto''++ [(parameter_name prmSpec, nme_args_v)] ) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ? /sng.
            decomp h_ex_;subst.
            exists l';auto. }
          decomp h_ex_.
          subst sto'.
          specialize h_forall_args_t_ with (sto':=sto'').
          up_type.
          assert (copyIn st bigs (lvl, [ ]) lprmSpec l_exp_args (OK (lvl, sto''))) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ?  /sng.
            decomp h_ex_.
            specialize h_forall_ll_ with (ll:=nil) /sng.
            assert (sto''=l'). {
              eapply app_inv_tail with (l:=[(parameter_name prmSpec, nme_args_v)]);eauto. }
            subst.
            rewrite app_nil_r in h_forall_ll_.
            assumption. }
          specialize h_forall_args_t_ with (1:=h_copy_in1_)(2:=eq_refl)(3:=eq_refl).
          rewrite rev_unit.
          constructor;intros /sng.
          * rewrite heq_parameter_mode_.
            assert (evalExp st bigs (Name O nme_args) (OK nme_args_v)) /sng. {
              constructor;auto. }
            simpl.
            subst.
            rewrite Maps.PTree.gss.
            specialize transl_expr_ok with (2:=h_eval_expr_nme_args_v_) (3:=h_match_env_) as ? /sng.
            assert (transl_expr st CE (Name 0%nat nme_args)
                     = value_at_addr st (parameter_subtype_mark prmSpec) nme_t) /sng. {
              simpl transl_expr.
              functional inversion heq_transl_name_ /sng.
              rewrite h_eq_transl_var_.
              assert (symboltable.fetch_exp_type_ astnum st = Some (parameter_subtype_mark prmSpec)) /sng. {
                admit. (* Well typedness of the call:
                          the actual arg's type = the formal arg type *)
              }
              rewrite heq_fetch_exp_type_.
              reflexivity.
            }
            unfold value_at_addr in heq_tr_expr_.
            destruct (transl_type st (parameter_subtype_mark prmSpec)) eqn:heq.
            all:swap 1 2.
            { exfalso.
              simpl bind in heq_tr_expr_.
              admit. (* well typedness: prmspec is correct, so transl_type and transl_exp should not rturn an error *) }
            simpl bind in heq_tr_expr_.
            specialize make_load_no_fail with (nme_t:=nme_t)(1:=heq) as ? /sng.
            decomp h_ex_.
            rewrite heq_make_load_ in heq_tr_expr_.
            functional inversion heq_make_load_ /sng.
             specialize h_forall_e'_ with (1:=heq_tr_expr_).
             decomp h_forall_e'_.
             exists nme_args_v_t, chunk;split;[|split].
            -- assumption.
            -- functional inversion heq /sng. 
               ++ vm_compute in h_access_mode_t_.
                  inversion h_access_mode_t_;auto.
               ++ vm_compute in h_access_mode_t_.
                  inversion h_access_mode_t_;auto.
            -- exists nme_t_v;split;auto.
               inversion h_CM_eval_expr_nme_args_v_t_ /sng.
               rewrite <- det_eval_expr with (1:=h_CM_eval_expr_nme_t_nme_t_v0_)(2:=h_CM_eval_expr_nme_t_nme_t_v_).
               assumption.
          *  (eapply Forall2_impl with (2:=h_forall_args_t_); intros) /sng.
            destruct a;intros /sng.
            specialize h_forall_k'_ with (1:=heq_transl_paramid_).
            destruct (parameter_mode b).
            -- decomp h_forall_k'_.
               simpl.
               rewrite Maps.PTree.gso.
               ++ eexists;repeat split;eauto.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {
                    apply transl_lparameter_specification_to_lident_nodup;auto. }
                  specialize set_params_in with (1:=heq_mget_k'_t_t_) as ? /sng.
                  simpl in h_nodup_.
                  subst k'.
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto.
            -- auto.
            -- intros /sng.
               decomp h_forall_k'_.
               simpl.
               rewrite Maps.PTree.gso.
               ++ exists t_t,chk;split;[|split];eauto.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {
                    apply transl_lparameter_specification_to_lident_nodup;auto. }
                  specialize set_params_in with (1:=heq_mget_k'_addr_) as ? /sng.
                  simpl in h_nodup_.
                  subst k'.
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto.
        + unfold ST.push in h_copy_in0_.
          simpl  in h_copy_in0_.
          assert (exists sto'', sto' = sto''++ [(parameter_name prmSpec, Int v)] ) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ? /sng.
            decomp h_ex_;subst.
            exists l';auto. }
          decomp h_ex_.
          subst sto'.
          specialize h_forall_args_t_ with (sto':=sto'').
          up_type.
          assert (copyIn st bigs (lvl, [ ]) lprmSpec l_exp_args (OK (lvl, sto''))) /sng. {
            specialize copy_in_cons with (1:=h_copy_in0_) as ?  /sng.
            decomp h_ex_.
            specialize h_forall_ll_ with (ll:=nil) /sng.
            assert (sto''=l'). {
              eapply app_inv_tail with (l:=[(parameter_name prmSpec, Int v)]);eauto. }
            subst.
            rewrite app_nil_r in h_forall_ll_.
            assumption. }
          specialize h_forall_args_t_ with (1:=h_copy_in1_)(2:=eq_refl)(3:=eq_refl).
          rewrite rev_unit.
          constructor;intros /sng.
          * rewrite heq_parameter_mode_.
            assert (evalExp st bigs (Name O nme_args) (OK (Int v))) /sng. {
              constructor;auto. }
            simpl.
            subst.
            rewrite Maps.PTree.gss.
            specialize transl_expr_ok as ? /sng.
            assert (transl_expr st CE (Name 0%nat nme_args) = value_at_addr st (parameter_subtype_mark prmSpec) nme_t) /sng. {
              simpl.
              functional inversion heq_transl_name_ /sng.
              rewrite h_eq_transl_var_.
              assert (symboltable.fetch_exp_type_ astnum st = Some (parameter_subtype_mark prmSpec)) /sng. {
                admit. (* Well typedness *)
              }
              rewrite heq_fetch_exp_type_.
              reflexivity.
            }
            unfold value_at_addr in heq_tr_expr_.
            destruct (transl_type st (parameter_subtype_mark prmSpec)) eqn:heq.
            all:swap 1 2.
            { exfalso. admit. (* well typedness: prmspec is correct *) }
            simpl bind in heq_tr_expr_.
            specialize make_load_no_fail with (nme_t:=nme_t)(1:=heq) as ? /sng.
            decomp h_ex_.
            rewrite heq_make_load_ in heq_tr_expr_.
            functional inversion heq_make_load_ /sng.
             specialize h_forall_stbl_ with (1:=heq_tr_expr_)(2:=h_eval_expr_)
                                           (3:=h_match_env_).
             decomp h_forall_stbl_.
             exists v_t, chunk;split;[|split].
            -- assumption.
            -- functional inversion heq /sng. 
              ++ vm_compute in h_access_mode_t_.
                  inversion h_access_mode_t_;auto.
               ++ vm_compute in h_access_mode_t_.
                  inversion h_access_mode_t_;auto.
            -- exists nme_t_v;split;auto.
               inversion h_CM_eval_expr_v_t_ /sng.
               rewrite <- det_eval_expr with (1:=h_CM_eval_expr_nme_t_nme_t_v0_)(2:=h_CM_eval_expr_nme_t_nme_t_v_).
               assumption.
          *  (eapply Forall2_impl with (2:=h_forall_args_t_); intros) /sng.
            destruct a;intros /sng.
            specialize h_forall_k'_ with (1:=heq_transl_paramid_).
            destruct (parameter_mode b).
            -- intros /sng.
               decomp h_forall_k'_.
               simpl.
               rewrite Maps.PTree.gso.
               ++ exists t_t;split;auto.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {
                    apply transl_lparameter_specification_to_lident_nodup;auto. }
                  specialize set_params_in with (1:=heq_mget_k'_t_t_) as ? /sng.
                  simpl in h_nodup_.
                  subst k'.
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto.
            -- auto.
            -- intros /sng.
               decomp h_forall_k'_.
               simpl.
               rewrite Maps.PTree.gso.
               ++  exists t_t,chk;split;[|split];eauto.
               ++ intro abs.
                  assert (List.NoDup (transl_lparameter_specification_to_lident st (prmSpec::lprmSpec))) /sng. {
                    apply transl_lparameter_specification_to_lident_nodup;auto. }
                  specialize set_params_in with (1:=heq_mget_k'_addr_) as ? /sng.
                  simpl in h_nodup_.
                  subst k'.
                  rewrite abs in *.
                  rewrite NoDup_cons_iff in h_nodup_.
                  destruct h_nodup_ /sng.
                  apply h_neg_lst_in_;auto.*)
Admitted.
        
    assert (NoDupA (λ x y : paramSpec, parameter_name x = parameter_name y)
                   procedure_parameter_profile) /sng. {
      admit. (* well formed/typed function *) }

    specialize copyIn_store_params_ok
      with (1:=heq_transl_params_p_x_) (3:=h_CM_eval_exprl_args_t_args_t_v_)
           (2:=h_copy_in_) (4:=h_match_env_) (5:=h_NoDupA_procedure_parameter_profile_)
           (6:=eq_refl) (7:=eq_refl) as ? /sng.
    rename h_for3_f_procedure_parameter_profile_args_ into h_init_params_.
    (* Actually the arguments are (chaining_expr_from_caller_v :: args_t_v) instead of just args_t_, but thanks to uniqueness of chaining_param   *)
        apply Forall3r1_impl_strong
          with (Q:=(λ (prm : idnum * V) (prm_prof : paramSpec) (_ : exp), 
                     ∀ k' : positive,
                     let (k, v) := prm in
                     transl_paramid k = k'
                     → match parameter_mode prm_prof with
                       | In =>
                           ∃ v' : Values.val, 
                           transl_value v v' ∧ Maps.PTree.get k' (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc)) = Some v'
                       | Out => v = Undefined
                       | In_Out =>
                           ∃ (v' : Values.val) (chk : AST.memory_chunk), 
                           transl_value v v'
                           ∧ (compute_chnk_of_type st (parameter_subtype_mark prm_prof) =: chk)
                             ∧ (∃ addr : Values.val, 
                                Maps.PTree.get k' (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc)) = Some addr
                                ∧ Mem.loadv chk m addr = Some v')
                       end))
      in h_init_params_.


    all:swap 1 2.
    { simpl fn_params.
      unfold set_params at 3 4.
      fold set_params.
      assert (Maps.PTree.get chaining_param (set_params args_t_v (transl_lparameter_specification_to_lident st procedure_parameter_profile)) = None) /sng. {
        destruct Maps.PTree.get eqn:? /sng.
        - exfalso.
          apply set_params_in in heq_mget_chaining_param_v_.
          eapply chaining_param_neq_transl_lparam;eauto.
        - reflexivity. }
      revert heq_get_.
      (* removes the occurrence of procedure_parameter_profile that we do not want
         to induct on. *)
      remember (transl_lparameter_specification_to_lident st procedure_parameter_profile) as l.
      (* do no get it back (elim instead of induction) *)
      elim h_init_params_;!intros /sng.
      - constructor.
      - constructor.
        + intros /sng.
          destruct x;!intros /sng.
          specialize h_forall_k'_ with (1:= heq_transl_paramid_).
          destruct (parameter_mode y);!intros /sng.
          all: swap 1 2.
          * assumption.
          * rewrite Maps.PTree.gso;auto.
            intro abs.
            subst.
            rewrite abs in h_forall_k'_.
            decomp h_forall_k'_.
            specialize h_forall_k'0_ with (1:=abs).
            rewrite heq_get_ in h_forall_k'0_.
            decomp h_forall_k'0_.
            discriminate heq_None_.
          * rewrite Maps.PTree.gso;auto.
            -- intro abs.
               subst.
               decomp h_forall_k'_.
               (* specialize h_forall_k'_ with (1:=h_transl_value_t_v'_)(2:=heq_compute_chnk_of_type_). *)
               rewrite abs in heq_mget_.
               specialize h_forall_k'0_ with (1:=abs).
               decomp h_forall_k'0_.
               rewrite heq_mget_chaining_param_addr0_ in heq_get_.
               discriminate.
        + apply h_impl_for3_l0_l'_l''_;auto. }

    Lemma exec_params_succeeds:
      forall st proc_param_prof revf args m_postchainarg locenv,
        Forall3_rev1
          (λ (prm : idnum * V) (prm_prof : paramSpec) (e : exp), 
           ∀ k' : positive,
             let (k, v) := prm in
             transl_paramid k = k' →
             match parameter_mode prm_prof with
             | In => (∃ v' : Values.val, transl_value v v' ∧ Maps.PTree.get k' locenv = Some v')
             | Out => (v = Undefined)
             | In_Out =>
               (∃ (v' : Values.val) (chk : AST.memory_chunk), 
                   (transl_value v v')
                   ∧ (compute_chnk_of_type st (parameter_subtype_mark prm_prof) =: chk)
                   ∧ (∃ addr : Values.val, 
                         Maps.PTree.get k' locenv = Some addr
                         ∧ Mem.loadv chk m_postchainarg addr = Some v'))
             end) revf proc_param_prof args ->
        forall the_proc CE_sufx sto s_parms initf g f stkptr_proc s suffix_s
               s_init_frame,
          f = revf++initf ->
          store_params st ((Datatypes.length CE_sufx, sto) :: CE_sufx)
                       proc_param_prof =: s_parms ->
          copyIn st s (Datatypes.length suffix_s, initf) proc_param_prof args
                 (OK (Datatypes.length CE_sufx, f)) → 
          invariant_compile ((Datatypes.length CE_sufx, sto) :: CE_sufx) st ->
          match_env_ st (s_init_frame :: suffix_s) ((Datatypes.length suffix_s, sto) :: CE_sufx)
                    stkptr_proc locenv g m_postchainarg ->
          ∃ (locenv' : env) (t2 : Events.trace) (m' : mem), 
            exec_stmt g the_proc stkptr_proc locenv m_postchainarg s_parms
                      t2 locenv' m' Out_normal.
    Proof.
        intros until 1 /sng.
        rename h_for3_revf_proc_param_prof_args_ into h_cpinOK_.
        (induction h_cpinOK_;!intros) /sng.
        - rew store_params_ok with functional inversion heq_store_prms_.
          subst.
          do 3 eexists.
          constructor.
        - rew store_params_ok with functional inversion heq_store_prms_ /sng.
          rename x1 into s_params'.
          destruct x.
          destruct (parameter_mode y) eqn:? /sng.
          all:swap 1 2.
          + (* Out mode *)
            unfold stmt0.
            simpl.
            inversion h_copy_in_;
              match goal with
              | H:parameter_mode y = ?X, H':parameter_mode y = ?Y |- _ =>
                try now (rewrite H in H'; discriminate)
              end /sng.
            assert ((i,t)=(parameter_name y, Undefined)) /sng. {
              admit. (* TODO: lemma similar to copy_in_cons *)
            }
            invclear heq_pair_ /sng.
            rewrite <- app_assoc in h_copy_in0_.
            simpl in h_copy_in0_.
            specialize h_forall_the_proc_ with
                (initf:=(parameter_name y, Undefined)::initf) (the_proc:=the_proc)
                (1:=eq_refl) (2:=heq_store_prms_l'_x1_)(3:=h_copy_in0_)(4:=h_inv_comp_st_)
                (5:=h_match_env_).
            decomp h_forall_the_proc_.
            exists locenv',(Events.Eapp Events.E0 t2),m'.
            eapply exec_Sseq_continue.
            * constructor.
            * eassumption.
            * reflexivity.
          + (*In Mode*)
            simpl in stmt0.
            subst stmt0 id0.
            specialize h_forall_k'_ with (1:=eq_refl).
            decomp h_forall_k'_.
            inversion h_copy_in_;
              match goal with
              | H:parameter_mode y = ?X, H':parameter_mode y = ?Y |- _ =>
                try now (rewrite H in H'; discriminate)
              end /sng.
            * assert ((i,t)=(parameter_name y, e_v)) /sng. {
                admit. (* TODO: lemma similar to copy_in_cons *)
              }
              invclear heq_pair_ /sng.
              rewrite <- app_assoc in h_copy_in0_.
              simpl in h_copy_in0_.
              specialize h_forall_the_proc_ with
                  (initf:=(parameter_name y, e_v)::initf) (the_proc:=the_proc)
                  (1:=eq_refl) (2:=heq_store_prms_l'_x1_)(3:=h_copy_in0_)(4:=h_inv_comp_st_)
                  (5:=h_match_env_).
              decomp h_forall_the_proc_.
              assert (Datatypes.length suffix_s = Datatypes.length CE_sufx) /sng. {
                admit. }
              assert (exists t1 e1 m1, exec_stmt g the_proc stkptr_proc locenv m_postchainarg
                                                 (Sstore x0 x2 (Evar (transl_paramid (parameter_name y))))
                                                 t1 e1 m1 Out_normal) /sng. {
                 specialize (h_match_env_ /sng.(me_safe_cm_env).(me_stack_match_addresses)) as ?.
                 red in h_stk_mtch_addr_stkptr_proc_m_postchainarg_.
                 rewrite heq_length_ in h_stk_mtch_addr_stkptr_proc_m_postchainarg_.
                 specialize h_stk_mtch_addr_stkptr_proc_m_postchainarg_
                            with (1:=heq_transl_name_).
                 decomp h_stk_mtch_addr_stkptr_proc_m_postchainarg_.
                 assert (exists aa bb, stkptr_proc = Values.Vptr aa bb) /sng. {
                   specialize match_env_sp_zero_ with (1:=h_match_env_) as ? /sng.
                   decomp h_ex_.
                   exists b, Ptrofs.zero.
                   assumption. }
                   decomp h_ex_.
                   subst.
                   simpl in heq_transl_name_.
                   specialize transl_variable_Vptr
                   with (1:=h_inv_comp_st_) (3:=heq_transl_name_)
                        (2:=me_stack_localstack_aligned (me_safe_cm_env h_match_env_))
                   as ? /sng.
                 specialize h_forall_nme_t_v_ with (1:=h_CM_eval_expr_x2_x2_v_).
                 decomp h_forall_nme_t_v_.
                 subst.
                 specialize Mem.valid_access_store as ? /sng.
                 specialize h_match_env_ /sng.(me_safe_cm_env).(me_stack_freeable) as ?.
                 red in h_freeable_m_postchainarg_.
                 rewrite heq_length_ in *.
                 specialize h_freeable_m_postchainarg_ with
                     (1:=heq_transl_name_)
                     (2:=h_CM_eval_expr_x2_x2_v_)
                     (3:=heq_compute_chnk_).
                 apply Mem.valid_access_freeable_any with (p:=Writable)
                   in h_freeable_m_postchainarg_.
                 specialize forall_m1 with (v:=t_t)(1:=h_freeable_m_postchainarg_).
                 decomp forall_m1.
                 simpl.
                do 3 eexists.
                econstructor.
                -- eassumption.
                -- constructor.
                   rewrite heq_mget_.
                   reflexivity.
                -- eapply heq_store_t_t_m2_. }
              decomp h_ex_. 
              assert (exists m'' t2, exec_stmt g the_proc stkptr_proc e1 m1
                                           s_params' t2 locenv' m'' Out_normal) /sng. {
                inversion h_exec_stmt_ /sng.



                unfold Mem.storev in heq_storev_v_m1_.
                destruct x2_v;try discriminate.

                assert (chained_stack_structure
                          m_postchainarg
                          (Datatypes.length ((Datatypes.length CE_sufx, sto) :: CE_sufx))
                          stkptr_proc) /sng. {
                  apply h_match_env_.
                }
                assert (CompilEnv.exact_levelG ((Datatypes.length CE_sufx, sto) :: CE_sufx)) /sng. {
                  apply h_inv_comp_st_.
                }
                assert (Ptrofs.unsigned i >= 4) /sng. {
                  admit. (* TODO *) }
                specialize store_param_nosideeffect with
                    (1:=heq_store_prms_l'_x1_)
                    (2:=h_chain_m_postchainarg_)
                    (3:=h_exct_lvlG_)
                    (4:=h_exec_stmt_s_params'_Out_normal_)
                    (5:=heq_storev_v_m1_)
                    (6:=h_ge_)
                  as ? /sng.
                decomp h_ex_.
                exists m1',t2.
                assumption. }
               xxx Finish TODO above.
              decomp h_ex_.
              exists locenv',(Events.Eapp t1 t0),m''.
              eapply exec_Sseq_continue with (t1:=t1)(e1:=e1)(m1:=m1).
              -- assumption.
              -- eassumption.
              -- reflexivity.
            * assert ((i,t)=(parameter_name y, Int v)) /sng. {
                admit. (* TODO: lemma similar to copy_in_cons *)
              }
              invclear heq_pair_ /sng.
              rewrite <- app_assoc in h_copy_in0_.
              simpl in h_copy_in0_.
              specialize h_forall_the_proc_ with
                  (initf:=(parameter_name y, Int v)::initf) (the_proc:=the_proc)
                  (1:=eq_refl) (2:=heq_store_prms_l'_x1_)(3:=h_copy_in0_)(4:=h_inv_comp_st_)
                  (5:=h_match_env_).
              decomp h_forall_the_proc_.
              assert (exists t1 e1 m1, exec_stmt g the_proc stkptr_proc locenv m_postchainarg
                                                 (Sstore x0 x2 (Evar (transl_paramid (parameter_name y))))
                                                 t1 e1 m1 Out_normal) /sng. {
                admit.
              }
              decomp h_ex_. 
              assert (exists m'' t2, exec_stmt g the_proc stkptr_proc e1 m1
                                           s_params' t2 locenv' m'' Out_normal) /sng. {
                admit.
              }
              decomp h_ex_.
              exists locenv',(Events.Eapp t1 t0),m''.
              eapply exec_Sseq_continue with (t1:=t1)(e1:=e1)(m1:=m1).
              -- assumption.
              -- eassumption.
              -- reflexivity.

          + (* in_Out *)
xxxx
                functional inversion heq_transl_name_ /sng.
                 specialize match_env_sp_zero_ with (1:=h_match_env_) as ? /sng.
                 decomp h_ex_.
                 rename b into proc_addr.
                 subst stkptr_proc.
                 assert (Datatypes.length suffix_s = Datatypes.length CE_sufx) /sng. {
                   admit.
                 }
                 specialize (h_match_env_ /sng.(me_safe_cm_env).(me_stack_match_addresses)) as ?.
                 red in h_stk_mtch_addr_.
                 rewrite heq_length_ in h_stk_mtch_addr_.
                 specialize h_stk_mtch_addr_ with (1:=heq_transl_name_).
                 decomp h_stk_mtch_addr_.
                 specialize transl_variable_Vptr
                   with (1:=h_inv_comp_st_)(3:=h_eq_transl_var_)
                        (2:=me_stack_localstack_aligned (me_safe_cm_env h_match_env_))
                   as ? /sng.
                 specialize h_forall_nme_t_v_ with (1:=h_CM_eval_expr_x2_x2_v_).
                 decomp h_forall_nme_t_v_.
                 subst.
                 specialize h_forall_k'_ with (1:=eq_refl).
                 exists locenv.
                 assert (i = (parameter_name y)). {
                   admit. (* TODO: lemma of copyIn. *)
                 }
                 subst i.
              (* Dealing with permissions *)


xxx
              -- eassumption.
              -- admit. (* reflexivity. *)


          
          assert (∃ (locenv'_fst : env) (t_fst : Events.trace) (m_fst : mem), 
                     exec_stmt g the_proc stkptr_proc locenv m_postchainarg
                               (Sstore x0 x2 rexp) t_fst locenv'_fst m_fst Out_normal). {
            functional inversion heq_transl_name_ /sng.
             specialize match_env_sp_zero_ with (1:=h_match_env_) as ? /sng.
             decomp h_ex_.
             rename b into proc_addr.
             subst.
             assert (Datatypes.length suffix_s = Datatypes.length CE_sufx) /sng. {
               admit.
             }
             specialize (h_match_env_ /sng.(me_safe_cm_env).(me_stack_match_addresses)) as ?.
             red in h_stk_mtch_addr_.
             rewrite heq_length_ in h_stk_mtch_addr_.
             specialize h_stk_mtch_addr_ with (1:=heq_transl_name_).
             decomp h_stk_mtch_addr_.
            specialize transl_variable_Vptr
              with (1:=h_inv_comp_st_)(3:=h_eq_transl_var_)
                   (2:=me_stack_localstack_aligned (me_safe_cm_env h_match_env_))
               as ? /sng.
            specialize h_forall_nme_t_v_ with (1:=h_CM_eval_expr_x2_x2_v_).
            decomp h_forall_nme_t_v_.
            subst.
            subst rexp.
            specialize h_forall_k'_ with (1:=eq_refl).
            exists locenv.
            assert (i = (parameter_name y)). {
              admit. (* TODO: lemma of copyIn. *)
            }
            subst i.
            (* Dealing with permissions *)
            specialize Mem.valid_access_store as ? /sng.
            specialize h_match_env_ /sng.(me_safe_cm_env).(me_stack_freeable) as ?.
            red in h_freeable_m_postchainarg_.
            rewrite heq_length_ in *.
            specialize h_freeable_m_postchainarg_ with
                (1:=h_eq_transl_var_)
                (2:=h_CM_eval_expr_x2_x2_v_)
                (3:=heq_compute_chnk_).
              apply Mem.valid_access_freeable_any with (p:=Writable)
                in h_freeable_m_postchainarg_.


            destruct (parameter_mode y) eqn:heq_prmmode_;simpl.
            + decomp h_forall_k'_.
              specialize forall_m1 with (v:=t_t)(1:=h_freeable_m_postchainarg_).
              decomp forall_m1.
              do 2 eexists.
              econstructor.
              * eapply h_CM_eval_expr_x2_x2_v_.
              * econstructor.
                eapply heq_mget_.
              * simpl.
                eapply heq_store_t_t_m2_.
            + subst t.
              specialize forall_m1 with (1:=h_freeable_m_postchainarg_).
              (* decomp forall_m1. *)
              do 2 eexists.
              econstructor.
              * eapply h_CM_eval_expr_x2_x2_v_.
              * econstructor.
                -- econstructor.
                   admit.
                -- edestruct forall_m1 /sng. 
                   econstructor.
                eapply heq_mget_.
              * simpl.
                eapply heq_store_t_t_m2_.
            + 
                
              






             (* temporay *)
             do 3 eexists.
             econstructor.
            + eapply h_CM_eval_expr_x2_x2_v_.
            + subst id0.
              assert (i = (parameter_name y)). {
                admit. (* TODO: lemma of copyIn. *)
              }
              subst i.
              
              destruct (parameter_mode y) eqn:heq_prmmode_;simpl.
              * econstructor.
                specialize h_forall_k'_ with (1:=eq_refl).
                decomp h_forall_k'_.
                eapply heq_mget_.
                rewrite heq_compute_chnk_,heq_store_prms_l'_x1_,h_eq_transl_var_ in heq_store_prms_.
                simpl in heq_store_prms_.
              

            specialize transl_variable_Vptr
              with (1:=h_inv_comp_st_)(3:=h_eq_transl_var_)
                   (2:=me_stack_localstack_aligned (me_safe_cm_env h_match_env_))
               as ? /sng.
            rewrite heq_length_ in h_copy_in_.
            (* destruct args. *)
            (* { inversion h_copy_in_. } *)
            simpl in h_copy_in_.
            (* inversion h_copy_in_ /sng. *)

            assert (exists nme_t_v,eval_expr g (Values.Vptr proc_addr Ptrofs.zero)
                                             locenv_postchainarg m_postchainarg x2 nme_t_v). {
              specialize (me_stack_match(h_match_env_)) as ? /sng.
              red in h_stk_mtch_.
              rewrite heq_length_ in h_stk_mtch_.
              specialize h_stk_mtch_ with (1:=heq_transl_name_).
              
              functional inversion h_eq_transl_var_ /sng.



              specialize transl_expr_ok with (2:=h_eval_expr_e_e_v_) as ? /sng.
              

            }
            rewrite <- app_assoc in h_copy_in_.
            simpl in h_copy_in_.
            specialize copy_in_push with (1:=h_copy_in_) as ? /sng.
            destruct h_and_ /sng.
            destruct h_and_ /sng.
            intro h_prm_mode_.
            subst.
            
            (destruct (parameter_mode y) eqn:heq); simpl in rexp;subst rexp /sng.
            + eexists.
              assert (exists v, eval_expr g (Values.Vptr proc_addr Ptrofs.zero) locenv m_postchainarg (Evar (transl_paramid (parameter_name y))) v) /sng. {
              (* functional inversion h_eq_transl_var_ /sng. *)
              
              eexists.
              econstructor.
              eapply h_forall_k'_ ;eauto.
              * f_equal.
                admit. (* TODO *)
              * 
                
                admit. }


              econstructor.
              eapply h_forall_k'_;eauto.


            (destruct (parameter_mode y) eqn:heq
            ; inversion h_copy_in_;
              try match goal with
                  | H: parameter_mode y = ?m, H':parameter_mode y = ?m' |- _ => 
                    (rewrite H in H'; discriminate) + clear H'
                  end) /sng.
            + specialize (me_stack_match_addresses (me_safe_cm_env h_match_env_)) as ? /sng.
              red in h_stk_mtch_addr_.
              specialize h_stk_mtch_addr_ with (1:=heq_transl_name_).
              decomp h_stk_mtch_addr_.
              specialize h_forall_nme_t_v_ with (1:=h_CM_eval_expr_x2_x2_v_).
              decomp h_forall_nme_t_v_.
              subst.
              simpl.
              specialize Mem.valid_access_store with (chunk:=x0)(m1:=m_postchainarg)
                                                      (b:=nme_block)(ofs:=Ptrofs.unsigned nme_ofst)
              as h_forall_v_. (* TODO: fix hyp naming here. sig is in Type. *)
            assert (Mem.valid_access m_postchainarg x0 nme_block (Ptrofs.unsigned nme_ofst) Writable) /sng. {
              apply Mem.valid_access_freeable_any. 
              specialize (h_match_env_ /sng.(me_safe_cm_env).(me_stack_freeable)) as ?.
              red in h_freeable_m_postchainarg_.
              eapply h_freeable_m_postchainarg_;eauto. }
             assert (exists v, eval_expr g (Values.Vptr proc_addr Ptrofs.zero) locenv m_postchainarg (Evar (transl_paramid (parameter_name y))) v) /sng. {
              (* functional inversion h_eq_transl_var_ /sng. *)
              
              eexists.
              econstructor.
              eapply h_forall_k'_;eauto.
              * f_equal.
                admit. (* TODO *)
              * 
                
                admit. }
            decomp h_ex_.
            specialize h_forall_v_ with (1:=h_valid_access_nme_block_).
            unfold indirection_according_to_mode.
            { simpl in rexp.
              subst rexp id0.

              specialize h_forall_v_ with (v:=v).
              decomp h_forall_v_.
              do 3 eexists.
              eapply exec_Sstore.
              + eapply eval_expr_transl_name_inv_locenv;eauto.
              + eassumption.
              + simpl.
                eapply heq_store_v_m2_. }
            + specialize (me_stack_match_addresses (me_safe_cm_env h_match_env_)) as ? /sng.
              red in h_stk_mtch_addr_.
              specialize h_stk_mtch_addr_ with (1:=heq_transl_name_).
              decomp h_stk_mtch_addr_.
              specialize h_forall_nme_t_v_ with (1:=h_CM_eval_expr_x2_x2_v_).
              decomp h_forall_nme_t_v_.
              subst.
              simpl.
              specialize Mem.valid_access_store with (chunk:=x0)(m1:=m_postchainarg)
                                                      (b:=nme_block)(ofs:=Ptrofs.unsigned nme_ofst)
              as h_forall_v_. (* TODO: fix hyp naming here. sig is in Type. *)
            assert (Mem.valid_access m_postchainarg x0 nme_block (Ptrofs.unsigned nme_ofst) Writable) /sng. {
              apply Mem.valid_access_freeable_any. 
              specialize (h_match_env_ /sng.(me_safe_cm_env).(me_stack_freeable)) as ?.
              red in h_freeable_m_postchainarg_.
              eapply h_freeable_m_postchainarg_;eauto. }
             assert (exists v, eval_expr g (Values.Vptr proc_addr Ptrofs.zero) locenv m_postchainarg (Evar (transl_paramid (parameter_name y))) v) /sng. {
              eexists.
              econstructor.
              eapply h_forall_k'_;eauto.
              * f_equal.
                admit. (* TODO *)
              * admit. }
            decomp h_ex_.
            specialize h_forall_v_ with (1:=h_valid_access_nme_block_).
            unfold indirection_according_to_mode.
            { simpl in rexp.
              subst rexp id0.

              specialize h_forall_v_ with (v:=v0).
              decomp h_forall_v_.
              do 3 eexists.
              eapply exec_Sstore.
              + eapply eval_expr_transl_name_inv_locenv;eauto.
              + eassumption.
              + simpl.
                eapply heq_store_v0_m2_. }
            + specialize (me_stack_match_addresses (me_safe_cm_env h_match_env_)) as ? /sng.
              red in h_stk_mtch_addr_.
              specialize h_stk_mtch_addr_ with (1:=heq_transl_name_).
              decomp h_stk_mtch_addr_.
              specialize h_forall_nme_t_v_ with (1:=h_CM_eval_expr_x2_x2_v_).
              decomp h_forall_nme_t_v_.
              subst.
              simpl.
              specialize Mem.valid_access_store with (chunk:=x0)(m1:=m_postchainarg)
                                                      (b:=nme_block)(ofs:=Ptrofs.unsigned nme_ofst)
                as h_forall_v_. (* TODO: fix hyp naming here. sig is in Type. *)
              assert (Mem.valid_access m_postchainarg x0 nme_block (Ptrofs.unsigned nme_ofst) Writable) /sng. {
                apply Mem.valid_access_freeable_any. 
                specialize (h_match_env_ /sng.(me_safe_cm_env).(me_stack_freeable)) as ?.
                red in h_freeable_m_postchainarg_.
                eapply h_freeable_m_postchainarg_;eauto. }
              assert (exists v,eval_expr g (Values.Vptr proc_addr Ptrofs.zero) locenv m_postchainarg (Eload x0 (Evar (transl_paramid (parameter_name y)))) v) /sng. {
                admit.
              }
              decomp h_ex_.
              specialize h_forall_v_ with (1:=h_valid_access_nme_block_).
              unfold indirection_according_to_mode.
              { simpl in rexp.
                subst rexp id0.
                specialize h_forall_v_ with (v:=v).
                decomp h_forall_v_.

                do 3 eexists.
                eapply exec_Sstore.
                + eapply eval_expr_transl_name_inv_locenv;eauto.
                + eassumption.
                + simpl.
                  eapply heq_store_v_m2_.  }
            +
}
*)
(*
    Lemma exec_params_succeeds:
      ∀ st procedure_declarative_part procedure_parameter_profile s_pbdy CE_init_frame CE_init_frame_sz
        CE CE_sufx (CE_prefx: CompilEnv.state) stkptr
        stkptr_proc b' locenv_proc f f1 suffix_s lglobdef the_proc args_t_v args
        s_locvarinit procedure_statements sto_sz g m m_postchainarg locenv_postchainarg locenv,
      Forall2
        (λ (prm : idnum * V) (prm_prof : paramSpec), 
         ∀ (k' : positive) (v' : Values.val),
           let (k, v) := prm in
           transl_paramid k = k'
           → match parameter_mode prm_prof with
             | In => transl_value v v'
                     → Maps.PTree.get k' (set_locals (transl_decl_to_lident st procedure_declarative_part) locenv_proc) = Some v'
             | Out => v = Undefined
             | In_Out =>
               transl_value v v'
               → ∀ chk : AST.memory_chunk,
                   compute_chnk_of_type st (parameter_subtype_mark prm_prof) =: chk
                   → ∃ addr : Values.val,
                     Maps.PTree.get k' (set_locals (transl_decl_to_lident st procedure_declarative_part) locenv_proc) = Some addr
             end) (rev f) procedure_parameter_profile
      -> 
      ∀ (sto : localframe) (fr_prm : localframe * Z) (p_sig : AST.signature) (s_parms : Cminor.stmt) (args_t : list expr),
        NoDupA (λ x y : paramSpec, parameter_name x = parameter_name y) procedure_parameter_profile
        → NoDupA eq_param_name procedure_parameter_profile
        → NoDupA eq (decl_to_lident st procedure_declarative_part)
        → store_params st ((Datatypes.length CE_sufx, sto) :: CE_sufx) procedure_parameter_profile =: s_parms
        → transl_declaration st ((Datatypes.length CE_sufx, sto) :: CE_sufx)
                             (S (Datatypes.length CE_sufx)) procedure_declarative_part =: lglobdef
        → transl_stmt st ((Datatypes.length CE_sufx, sto) :: CE_sufx) procedure_statements =: s_pbdy
        → init_locals st ((Datatypes.length CE_sufx, sto) :: CE_sufx) procedure_declarative_part =: s_locvarinit
        → build_frame_decl st fr_prm procedure_declarative_part =: (sto, sto_sz)
        (* init_frame contains the previously processed params. the *)
        → build_frame_lparams st (CE_init_frame, CE_init_frame_sz) procedure_parameter_profile =: fr_prm
        → CE_init_frame_sz >= 4
        → fresh_params_ procedure_parameter_profile sto
        → invariant_compile ((Datatypes.length CE_sufx, sto) :: CE_sufx) st
        → (∀ (astnum : astnum) (id : idnum) (δlvl : nat) (n : Z) (id_v : Values.val),
              transl_variable st ((Datatypes.length CE_sufx, sto) :: CE_sufx) astnum id =: build_loads (S δlvl) n
              → eval_expr g stkptr_proc locenv_postchainarg m_postchainarg (build_loads (S δlvl) n) id_v
              → eval_expr g stkptr locenv_postchainarg m_postchainarg (build_loads (Datatypes.length CE_prefx + δlvl) n) id_v)
        → (∀ (astnum : astnum) (addr : Values.block) (ofs : Z),
              forbidden st CE g astnum locenv stkptr m m addr ofs
              → forbidden st ((Datatypes.length CE_sufx, sto) :: CE_sufx)
                          g astnum locenv_postchainarg stkptr_proc m_postchainarg m_postchainarg addr ofs)
        → transl_lparameter_specification_to_procsig st (Datatypes.length CE_sufx) procedure_parameter_profile =: p_sig
        → transl_paramexprlist st CE args procedure_parameter_profile =: args_t
        → eval_exprlist g (Values.Vptr b' Ptrofs.zero) locenv m args_t args_t_v
        → match_env_ st (f1 :: suffix_s) ((Datatypes.length suffix_s, CE_init_frame) :: CE_sufx)
                    stkptr_proc locenv_postchainarg g m_postchainarg
        → ∃ (locenv' : env) (t2 : Events.trace) (m' : mem), 
        exists locenv' t2 m',
          exec_stmt
            g the_proc stkptr_proc
            (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc))
            m_postchainarg s_parms t2 locenv' m'  Out_normal.
    Proof.
      intros /sng.
*)
    assert (
        exists locenv' t2 m',
          exec_stmt
            g the_proc stkptr_proc
            (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc))
            m_postchainarg
            s_parms t2 locenv' m'  Out_normal). {
      remember (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc)) as locenv_proc in *.
      unfold fn_vars, fn_vars, the_proc in h_init_params_.
      
(*      revert s_parms the_proc heq_find_func_paddr_fction_ h_alloc_ Heqlocenv_proc
             h_exec_stmt_ heq_store_prms_procedure_parameter_profile_s_parms_.
      (* revert heq_store_prms_procedure_parameter_profile_s_parms_. *)
      remember (rev f) as revf.
      remember procedure_parameter_profile as prms.*)

      clearbody the_proc.
      clear h_copy_out_ h_copy_in_ heq_fetch_proc_p_
            hcpout_prm_procedure_parameter_profile_s_copyout heq_bldCE_
            heq_transl_stmt_stm'_.
      
      revert sto fr_prm p_sig s_parms args_t
             h_NoDupA_procedure_parameter_profile_
             hnodup_arg hnodup_decl
             heq_store_prms_procedure_parameter_profile_s_parms_
             h_forall_s'_ heq_transl_decl_procedure_declarative_part_c_
             heq_transl_stmt_procedure_statements_s_pbdy_
             heq_init_lcl_procedure_declarative_part_s_locvarinit_
             heq_build_frame_decl_ heq_bld_frm_procedure_parameter_profile_ hfrsh
             h_inv_CE''_bld_ h_reachable_enclosing_variables_
             h_forbidden_incl_m_m_poschainarg'_
             heq_transl_lprm_spec_procedure_parameter_profile_p_sig_
             heq_transl_params_p_x_ h_CM_eval_exprl_args_t_args_t_v_
             .
      induction h_init_params_;!intros /sng.
      - simpl in heq_store_prms_.
        inversion  heq_store_prms_.
        subst s_parms.
        do 3 eexists.
        econstructor.
      - up_type.
        rew store_params_ok with functional inversion heq_store_prms_ /sng.
        rew transl_paramexprlist_ok with functional inversion htrans_prmexprl /sng.
        rename h_impl_impl_forall_sto_ into IH.
        inversion h_NoDupA_ /sng.
        inversion h_NoDupA0_ /sng.
        (* inversion h_NoDupA_procedure_parameter_profile_ /sng. *)
        specialize IH with (1:=h_NoDupA_l'_) (2:=h_NoDupA_l'0_) (3:=h_NoDupA1_)
                           (4:=heq_store_prms_l'_x1_)
                           (5:=h_forall_lvl_)
                           (6:=heq_transl_decl_procedure_declarative_part_lglobdef_)(* useless? *)
                           (7:=heq_transl_stmt_procedure_statements_s_pbdy_)(* useless? *)
                           (8:=heq_init_lcl_procedure_declarative_part_s_locvarinit_)
                           (9:=heq_build_frame_decl_)
                           (12:=h_inv_comp_st_)
                           (13:=h_forall_astnum0_)
                           (14:=h_forall_astnum1_)
        .

        do 3 eexists;econstructor.
        all:swap 1 2.
        eapply IH.
                  (16:=htrans_prmexprl)

        red in h_fresh_prms_.
        inversion h_fresh_prms_ /sng.
        specialize IH with (2:=h_lst_forall_l'_).
        
        rew build_frame_lparams_ok with functional inversion heq_bld_frm_ /sng.
        specialize IH with (1:=)
        .
        specialize 
        specialize h_impl_ex_ with (1:=heq_store_prms_l'_x1_).
        
        eapply h_impl_ex_;auto.
        
        assumption.
        
}


 
xxx
    Lemma init_params_succeeds:
      ∀ stbl stcksizeinit lparams stcksize lvl CE initprms bigs
        s locenv stkptr g m mcalling callinglocenv callingsp proc_t
        args_t m' locenv' tr tlparams CE_prefx
        proc_stkptr
        sto sto' stoCE stoCE' args args' args_t_v args_t_v',
        (* tlparams is the args ids of lparams  *)
        transl_lparameter_specification_to_lident stbl lparams = tlparams -> 
        set_params (args_t_v++args_t_v') tlparams = locenv -> 
        match_env_ stbl ((lvl,sto)::s) ((lvl,stoCE)::CE) proc_stkptr locenv g m -> 

        (* Concerning CE *)
        build_frame_lparams stbl (stoCE,stcksizeinit) lparams =: (stoCE'++stoCE, stcksize) ->
        (* Concerning spark side *)
        copyIn stbl bigs (lvl, sto) lparams args (OK (lvl, sto'++sto)) ->

        (* Concerning Cminor side *)
        (* evaluate real args *)
        eval_exprlist g callingsp callinglocenv mcalling args_t args_t_v ->
        (* build a locenv from args values *)
        set_params args_t_v tlparams = locenv ->
        (* generate the code to copy these values from locenv to stack *)
        store_params stbl ((lvl, stoCE'++stoCE) :: CE) lparams =: initprms ->
        (* execute the code *)
        exec_stmt g proc_t stkptr locenv m initprms tr locenv' m' Out_normal ->


        (* Conclusion *)
        match_env_ stbl bigs (CE_prefx++CE) callingsp callinglocenv g mcalling ->
        match_env_ stbl ((lvl,sto'++sto)::s) ((lvl,stoCE'++stoCE)::CE) stkptr locenv' g m'.

    Lemma init_params_succeeds:
      ∀ stbl l stcksizeinit lparams l' stcksize lvl CE initprms bigs
        args sto s sto' locenv sp g m mcalling callinglocenv callingsp CE_prefx proc_t
        args_t args_t_v stoCE stoCE',

        (* Concerning CE *)
        build_frame_lparams stbl (stoCE,stcksizeinit) lparams =: (stoCE'++stoCE, stcksize) ->

        (* Concerning Cminor side *)
        eval_exprlist g callingsp callinglocenv mcalling args_t args_t_v ->
        set_params args_t_v tlparams = locenv ->
        store_params stbl ((lvl, stoCE'++stoCE) :: CE) lparams =: initprms ->

        (* Concerning spark side *)
        copyIn stbl bigs (lvl, sto) lparams args (OK (lvl, sto')) ->

        (* All together *)
        (* This one implies that spark's copyIn and cminor's
           eval_exprlist+storeparams+set_params corresponds to copyIn *)
        match_env_ stbl bigs (CE_prefx++CE) callingsp callinglocenv g mcalling ->
        match_env_ stbl ((lvl,l++l')::s) ((lvl,stoCE++stoCE')::CE) (Values.Vptr sp Ptrofs.zero) locenv g m ->

        ∃ locenv' t2 m',
          exec_stmt g proc_t (Values.Vptr sp Ptrofs.zero) locenv m initprms t2 locenv'
                    m' Out_normal.

    Lemma init_params_succeeds:
      ∀ stbl lparams lstcksizinit astnum pnum lvl decl0 pbdy statm CE  stcksizeinit stcksize
        newlfundef  initprms decl_t llocals stoCE sto_sz tlparams l l',
        build_frame_lparams stbl lstcksizinit lparams =: (l', stcksize) ->
        build_compilenv stbl CE lvl lparams llocals =: ((lvl, stoCE) :: CE, sto_sz) ->
        pbdy = mkprocBodyDecl astnum pnum lparams decl0 statm ->
        lstcksizinit = (l,stcksizeinit) ->
        (* add_to_frame stbl fram_sz nme subtyp_mrk
           build_compilenv stbl enclosingCE lvl lparams decl0 =: (CE, stcksize) -> *)
        (* stcksize <= Ptrofs.max_unsigned -> *)
        transl_declaration stbl ((lvl, stoCE) :: CE) (S lvl) decl0 =: newlfundef ->
        store_params stbl ((lvl, stoCE) :: CE) lparams =: initprms ->
        transl_decl_to_lident stbl decl0 = decl_t ->
        transl_lparameter_specification_to_lident stbl lparams = tlparams ->
        ∀ proc_t m sp g mcalling callinglocenv callingsp callingCE CE_prefx locenv sto sto' 
          bigs pref_s s args args_t args_t_v,
          (* compilation of the arguments expressions passed to the procedure. *)
          spark2Cminor.transl_paramexprlist stbl callingCE args lparams =: args_t -> 
          ST.cut_until bigs lvl pref_s s ->
          CompilEnv.cut_until callingCE lvl CE_prefx CE ->
          (* spark: storing args values and then local var init *)
          copyIn stbl bigs (lvl, sto) lparams args (OK (lvl, sto')) ->
          (* Cminor: evaluating args *)
           eval_exprlist g callingsp callinglocenv mcalling args_t args_t_v ->
          (* Cminor: and then setting local vars *)
          (*Mem.alloc minit 0 stcksize = (m, sp) ->*) (*  stcksize(fn_stackspace f) *)
          set_params args_t_v tlparams = locenv -> (* FIXME f? *)
          (* match_list_ x'' args_t_v  *)
          (* if match_env_ before calling: *)
          match_env_ stbl bigs callingCE callingsp callinglocenv g mcalling ->
          (* and also when starting  *)
          match_env_ stbl ((lvl,sto)::s) ((lvl,l)::CE) (Values.Vptr sp Ptrofs.zero) locenv g m ->
          ∃ locenv' t2 m',
            exec_stmt g proc_t (Values.Vptr sp Ptrofs.zero) locenv m
                      initprms t2 locenv' m' Out_normal
            ∧ match_env_ stbl ((lvl,sto')::s) ((lvl,l')::CE)
                        (Values.Vptr sp Ptrofs.zero) locenv' g m'.
Proof.
  intros /sng.
  intros stbl tlparams lstcksizinit /sng.
  rew build_frame_lparams_ok with
      functional induction function_utils.build_frame_lparams stbl lstcksizinit tlparams;
    !!!intros; up_type /sng.
  all:swap 2 3.
  - inversion h_copy_in_ /sng.
    invclear heq_OK_ /sng.
    rew store_params_ok with functional inversion heq_store_prms_ /sng.
    exists (set_params args_t_v (transl_lparameter_specification_to_lident stbl [ ])).
    eexists.
    exists m.
    split.
    + econstructor.
    + assumption.
  - inversion heq_Error_.
  - rename h_forall_astnum_ into IH.
    match goal with |- context [?x::lparam'] => set (a:=x) in * end; up_type.
    rew store_params_ok with functional inversion heq_store_prms_;up_type /sng.
    enough (
        ∃ (t_fst : Events.trace) (m_fst:mem) , 
          exec_stmt
            g proc_t (Values.Vptr sp Ptrofs.zero)
            (set_params args_t_v (transl_lparameter_specification_to_lident stbl (a :: lparam'))) m
            (Sstore x1 x3 rexp) t_fst
            (set_params args_t_v (transl_lparameter_specification_to_lident stbl (a :: lparam')))
            m_fst Out_normal
          (* ∧ match_env_ stbl ((lvl, x') :: s) ((lvl, l') :: CE) *)
                      (* (Values.Vptr sp Ptrofs.zero) locenv' g m' *)) /sng.
(*    ∧ exec_stmt
              g proc_t (Values.Vptr sp Ptrofs.zero) locenv_fst m_fst
              x2 t2 locenv' m' Out_normal
          ∧ match_env_ stbl ((lvl, x') :: s) ((lvl, l') :: CE)
                      (Values.Vptr sp Ptrofs.zero) locenv' g m').*)
    { decomp h_ex_. 
      specialize IH
        with (locenv:=(set_params args_t_v (transl_lparameter_specification_to_lident stbl (a :: lparam'))))
             (m:=m_fst).
      (rew transl_paramexprlist_ok with functional inversion htrans_prmexprl);
        specialize IH with (9:=htrans_prmexprl0) /sng.
      all:inversion h_copy_in_;
         match goal with
         | H: parameter_mode ?a = ?x, H': parameter_mode ?a = ?y |- _ => now (rewrite H in H';discriminate)
         | H: parameter_mode ?a = ?x, H': parameter_mode ?a = ?x |- _ => clear H'
         end;
      unfold ST.push in h_copy_in0_;
      cbn in h_copy_in0_ /sng.
      all:inversion h_CM_eval_exprl_args_t_args_t_v_ /sng.
      all:specialize IH with (12:=h_CM_eval_exprl_x5_vl_).
      all:specialize IH with (13:=h_match_env_).
      inversion h_exec_stmt_ /sng.
      specialize assignment_preserve_match_env_
        with (3:=h_match_env0_)
             (5:=h_CM_eval_expr_x3_x3_v_)
             (9:=heq_storev_rexp_v_m_fst_)
        as ? /sng.
      specialize h_forall_x_
        with (4:=heq_compute_chnk_).
        with (3:=heq_transl_name_)
      .

      cbn in h_copy_in0_.
      cbn in h_copy_in0_.

      specialize IH with (10:=h_copy_in0_).

      exists locenv', t2, m'.
                      (* (Values.Vptr sp Ptrofs.zero) locenv' g m' *)
          ∧ ∃ (locenv' : env) (t2 : Events.trace) (m' : mem),
            exec_stmt
              g proc_t (Values.Vptr sp Ptrofs.zero) locenv_fst m_fst
              x2 t2 locenv' m' Out_normal
            ∧ match_env_ stbl ((lvl, x') :: s) ((lvl, l') :: CE)
                        (Values.Vptr sp Ptrofs.zero) locenv' g m').
    { decomp h_ex_. 
      exists locenv', (Events.Eapp t_fst t2), m'.
      split.
      - admit.
        (*econstructor.
        + eassumption.
        + admit.
        + *)
      - admit.
    }
    

    assert (
      ∃ (locenv_fst : env) (t_fst : Events.trace) (m_fst : mem), 
        exec_stmt g proc_t (Values.Vptr sp Ptrofs.zero)
                  (set_params args_t_v (transl_lparameter_specification_to_lident stbl (a :: lparam'))) m (Sstore x1 x3 rexp) t_fst locenv_fst
                  m_fst Out_normal
        ∧ (exec_stmt g proc_t (Values.Vptr sp Ptrofs.zero)
                    (set_params args_t_v (transl_lparameter_specification_to_lident stbl (a :: lparam'))) m (Sstore x1 x3 rexp) t_fst locenv_fst
                    m_fst Out_normal ->
    (∃ (locenv' : env) (t2 : Events.trace) (m' : mem), 
        exec_stmt g proc_t (Values.Vptr sp Ptrofs.zero) locenv_fst m_fst x2 t2 locenv' m' Out_normal
        ∧ match_env_ stbl ((lvl, x') :: s) ((lvl, l') :: CE) (Values.Vptr sp Ptrofs.zero) locenv' g m'))). {
      cbn in heq_transl_name_.
       functional inversion heq_transl_name_ /sng.
       rew add_to_frame_ok with functional inversion heq_add_to_fr_nme_ /sng.
      do 3 eexists .
      split.
      
    + admit.
      (*specialize (h_match_env0_ /sng.(me_stack_match)) as ?.
      red in h_stk_mtch_.
      specialize h_stk_mtch_ with (1:=heq_transl_name_).
      inversion h_copy_in_ /sng.
      functional inversion heq_transl_name_ /sng.
      functional inversion h_eq_transl_var_ /sng.
      econstructor.
      *)
    + intro /sng.
      inversion h_exec_stmt_ /sng.
      rewrite heq.
      eapply h_forall_astnum_. (* eauo here goes in a dead-end *)
      * eassumption.
      * reflexivity.
      * reflexivity.
      * xxx

      rewrite <- heq_E0_ in *.
      decomp h_ex_.
      do 3 eexists.
      split.
      * 

.


    inversion h_copy_in_ /sng.
    + destruct x /sng.
      unfold ST.push in h_copy_in0_.
      cbn in h_copy_in0_.
      specialize IH with (1:=heq_build_frame_lparams_)(2:=eq_refl)(3:=eq_refl)
                          (4:=heq_transl_decl_decl0_newlfundef_)(6:=heq_transl_decl_to_lident_)
                          (9:=h_stkcut_bigs_lvl_)(10:=h_CEcut_callingCE_lvl_)
                          (14:=h_match_env_)(11:=h_copy_in0_).
      up_type.
      subst fram_sz.
      rew store_params_ok with functional inversion heq_store_prms_;
        match goal with
        | H: parameter_mode ?a = ?x, H': parameter_mode ?a = ?y |- _ => try now (rewrite H in H';discriminate)
        end /sng.
      up_type.
      unfold a in id;simpl in id.
      unfold a in id0;simpl in id0.
      specialize IH with (1:=heq_store_params_)(2:=eq_refl).
      rew transl_paramexprlist_ok with functional inversion htrans_prmexprl;
        match goal with
        | H: parameter_mode ?a = ?x, H': parameter_mode ?a = ?y |- _ => try now (rewrite H in H';discriminate)
        end /sng.
      specialize IH with (1:=heq_transl_paramexprlist_).
      inversion h_CM_eval_exprl_args_t_args_t_v_ /sng.
      specialize IH with (1:=h_CM_eval_exprl_x4_vl_)(2:=eq_refl).
      up_type.
      subst locenv.
      specialize IH with (proc_t:=proc_t)(sp:=sp).
      subst tlparams.
      replace (parameter_name a) with nme in * .
      all:swap 1 2.
      { reflexivity. }
      assert 
        (match_env_ stbl ((lvl, (nme, e_v) :: x0) :: s) ((lvl, s0) :: CE) (Values.Vptr sp Ptrofs.zero)
         (set_params vl (transl_lparameter_specification_to_lident stbl lparam')) g m) /sng. {
        admit.
        (*simpl in h_match_env0_.
        replace (parameter_name a) with nme in * .
        all:swap 1 2.
        { reflexivity. }
        destruct h_match_env0_.
        split.
        - red ;intros /sng.
          destruct (name_dec nme0 (Identifier 0%nat nme)).
          + subst nme0.
            inversion h_eval_name_nme0_v_ /sng.
            cbn in heq_SfetchG_nme_.
            rewrite Nat.eqb_refl in heq_SfetchG_nme_.
            invclear heq_SfetchG_nme_ /sng.
            functional inversion heq_make_load_ /sng.
            specialize transl_expr_ok with (1:=heq_tr_expr_e_)(2:=h_eval_expr_e_e_v_)(3:=h_match_env_) as ? /sng.
            decomp h_ex_.
            exists e_t_v0;split;auto.
            econstructor;eauto.*)
      }
      specialize IH with (1:=h_match_env1_).
      decomp IH.
      do 3 eexists.
      split.
      * econstructor.
        -- econstructor.
      


      specialize IHlparams with (1:=heq_is_).

    (* FIXME: have something saying that
       1) evaluation of real args match between sparka and cminor
       2) evaluation of initialization  also match.    
       hopefully remove all about callingm callingCE callingsp callinglocenv.
     *)
    Lemma init_code_succeeds:
      ∀ stbl enclosingCE astnum pnum lvl pbdy lparams decl0 statm CE stcksize
        newlfundef locvarinit initprms decl_t tlparams,
        pbdy = mkprocBodyDecl astnum pnum lparams decl0 statm ->
        build_compilenv stbl enclosingCE lvl lparams decl0 =: (CE, stcksize) ->
        stcksize <= Ptrofs.max_unsigned ->
        transl_declaration stbl CE (S lvl) decl0 =: newlfundef ->
        init_locals stbl CE decl0 =: locvarinit ->
        store_params stbl CE lparams =: initprms ->
        transl_decl_to_lident stbl decl0 = decl_t ->
        transl_lparameter_specification_to_lident stbl lparams = tlparams ->
        ∀ proc_t m sp g callinglocenv callingsp callingCE locenv x x' x''
          bigs pref_s s l l' args args_t args_t_v,
          (* compilation of the arguments expressions passed to the procedure. *)
          spark2Cminor.transl_paramexprlist stbl CE args lparams =: args_t -> 
          ST.cut_until bigs lvl pref_s s ->
          (* spark: storing args values and then local var init *)
          copyIn stbl bigs (lvl, x) lparams args (OK (lvl, x')) ->
          evalDecl stbl s (lvl, x') decl0 (OK (lvl,x'')) ->
          (* Cminor: evaluating args *)
          eval_exprlist g callingsp callinglocenv m args_t args_t_v ->
          (* Cminor: and then setting local vars *)
          Mem.alloc m 0 stcksize = (m, sp) -> (*  stcksize(fn_stackspace f) *)
          set_locals decl_t (set_params args_t_v tlparams) = locenv -> (* FIXME f? *)
          (* match_list_ x'' args_t_v  *)
          (* if match_env_ before calling: *)
          match_env_ stbl bigs callingCE callingsp callinglocenv g m ->
          (* and also when starting  *)
          match_env_ stbl ((lvl,x)::s) ((lvl,l)::CE) (Values.Vptr sp Ptrofs.zero) locenv g m ->
          ∃ locenv' t2 m',
            exec_stmt g proc_t (Values.Vptr sp Ptrofs.zero) locenv m
                      (Sseq initprms locvarinit) t2 locenv' m' Out_normal
            ∧ match_env_ stbl ((lvl,x'')::s) ((lvl,l')::CE)
                        (Values.Vptr sp Ptrofs.zero) locenv' g m'.
Proof.
  intros /sng.

Qed.
xxx Change the statement above.
*)

(*
    Lemma init_params_succeeds:
      ∀ (lparams : list paramSpec) (st : symboltable)(lvl : nat) l
        (CE : CompilEnv.state) (initparams : Cminor.stmt),
        store_params st ((lvl,l)::CE) lparams =: initparams
        → ∀ (g : genv) (proc_t : function) (sp : Values.val) (e_chain : env)
            (m : mem) (bigs pref_s s:ST.state) l' sz sz' x x' args,
          Datatypes.length CE = lvl
          → ST.cut_until bigs (Datatypes.length CE) pref_s s
          → invariant_compile ((lvl,l)::CE) st
          → build_frame_lparams st (l,sz) lparams =: (l',sz')
          (* → build_compilenv st CE lvl lparams NullDecl =: CE' *)
          → chained_stack_structure m lvl sp
          (* → stack_localstack_aligned (Datatypes.length CE) e_chain g m sp *)
          → copyIn st bigs (lvl, x) lparams args (OK (lvl, x'))
          → match_env_ st ((lvl,x)::s) ((lvl,l)::CE) sp e_chain g m
          → exists e_chain' t2 m',
              exec_stmt g proc_t sp e_chain m initparams t2 e_chain' m' Out_normal.
    Proof.
    Admitted.

    Lemma init_params_preserve_match_env_:
      ∀ (lparams : list paramSpec) (st : symboltable) (lvl : nat) l (CE : CompilEnv.state) (initparams : Cminor.stmt),
        store_params st ((lvl,l)::CE) lparams =: initparams
        → ∀ (g : genv) (proc_t : function) (sp : Values.val) (e_chain : env)
            (m : mem) (t2 : Events.trace) (e_chain' : env)(bigs pref_s s:ST.state)
            l' sz sz' (m' : mem) x x'  args,
          Datatypes.length CE = lvl
          → ST.cut_until bigs (Datatypes.length CE) pref_s s
          → invariant_compile ((lvl,l)::CE) st
          → build_frame_lparams st (l,sz) lparams =: (l',sz')
          (* → build_compilenv st CE lvl lparams NullDecl =: CE' *)
          → chained_stack_structure m lvl sp
          (* → stack_localstack_aligned ((lvl,l)::CE) e_chain g m sp *)
          → copyIn st bigs (lvl, x) lparams args (OK (lvl, x'))
          → exec_stmt g proc_t sp e_chain m initparams t2 e_chain' m' Out_normal
          → match_env_ st ((lvl,x)::s) ((lvl,l)::CE) sp e_chain g m
          → match_env_ st ((lvl,x')::s) ((lvl,l')::CE) sp e_chain' g m'.
    Proof.
      intros  until CE.
      rewrite store_params_ok.
      Opaque build_frame_lparams.
      remember ((lvl, l) :: CE) as bigCE.
      revert l lvl CE HeqbigCE.
      functional induction function_utils.store_params st bigCE lparams;
        try rewrite <- store_params_ok in *;cbn;!intros
        ; try discriminate;eq_same_clear; up_type /sng.
      Transparent build_frame_lparams.
      - inversion h_exec_stmt_initparams_Out_normal_ /sng.
        inversion h_copy_in_ /sng.
        simpl in heq_bld_frm_.
        inversion heq_bld_frm_ /sng.
        subst.
        assumption.
      - 
        (* specialize invariant_compile_subcons with (1:=h_inv_comp_st_) as ? /sng. *)
        rewrite build_frame_lparams_ok in heq_bld_frm_.
        functional inversion heq_bld_frm_ /sng.
        rewrite <- build_frame_lparams_ok in *.
        subst.
        assert (_x0 = In). {
          cbn in heq_parameter_mode_.
          assumption. }
        subst _x0.
        set (prm:={| parameter_astnum := _x; parameter_name := nme; parameter_subtype_mark := subtyp_mrk; parameter_mode := In |}) in *.
        rewrite add_to_frame_ok in heq_add_to_fr_nme_.
        functional inversion heq_add_to_fr_nme_;subst /sng.
        rewrite <- add_to_frame_ok in *.
        specialize h_forall_l_
          with (2:=heq_store_params_)(6:=heq_build_frame_lparams_).
        inversion h_copy_in_;
          match goal with
          | H:parameter_mode prm = ?X, H':parameter_mode prm = ?Y |- _ =>
            try (rewrite H in H'; discriminate)
          end; clear heq_parameter_mode0_ /sng.
        + admit. 
          (* copy_in In  norange *)
         (* specialize h_forall_initparams_ with (5:=h_copy_in0_).
          inversion h_exec_stmt_initparams_Out_normal_;try now (exfalso;auto 2) /sng.
          specialize h_forall_initparams_ with (5:=h_exec_stmt_x0_Out_normal_).
          cbn in h_forall_initparams_.
          apply h_forall_initparams_;auto.
          * { split.
              - constructor.
                apply h_inv_comp_CE_st_.
              - 
                
                apply 
*)
        + admit.
      - admit.
      - admit.
Admitted.

 (* TODO: s ans s_suffixmust be defined int his statement and the two above. *)
    Lemma init_params_succeeds_and_preserve_match_env_:
  ∀ (lparams : list paramSpec) (st : symboltable)(lvl : nat) l (CE : CompilEnv.state) (initparams : Cminor.stmt),
    store_params st ((lvl,l)::CE) lparams =: initparams
    → ∀ (g : genv) (proc_t : function) (sp : Values.val) (e_chain : env)
        (m : mem) (bigs pref_s s:ST.state) l' sz sz' x x' args,
        Datatypes.length CE = lvl
        → ST.cut_until bigs (Datatypes.length CE) pref_s s
        → invariant_compile ((lvl,l)::CE) st
        → build_frame_lparams st (l,sz) lparams =: (l',sz')
        (* → build_compilenv st CE lvl lparams NullDecl =: CE' *)
        → chained_stack_structure m lvl sp
        → copyIn st bigs (lvl, x) lparams args (OK (lvl, x'))
        → match_env_ st ((lvl,x)::s) ((lvl,l)::CE) sp e_chain g m
        → exists e_chain' t2 m',
            exec_stmt g proc_t sp e_chain m initparams t2 e_chain' m' Out_normal
            ∧ match_env_ st ((lvl,x')::s) ((lvl,l')::CE) sp e_chain' g m'.
    Proof.
      intros /sng.
      edestruct init_params_succeeds with (proc_t:=proc_t)(s:=s)(pref_s:=pref_s)(bigs:=bigs);eauto /sng.
      decomp h_ex_;eauto.
      exists x0, t2, m';split;auto.
      eapply init_params_preserve_match_env_;eauto.
    Qed.
    Lemma init_locals_succeeds_and_preserve_match_env_:
  ∀ (locals : decl) (st : symboltable)(lvl : nat) l (CE : CompilEnv.state)
    (s_locvarinit : Cminor.stmt),
    init_locals st ((lvl,l)::CE) locals =: s_locvarinit
    → ∀ (g : genv) (proc_t : function) (sp : Values.val) (e_chain : env)
        (m : mem) (s:ST.state) l' sz sz' x x',
        Datatypes.length CE = lvl
        → invariant_compile ((lvl,l)::CE) st
        → build_frame_decl st (l,sz) locals =: (l',sz')
        (* → build_compilenv st CE lvl lparams NullDecl =: CE' *)
        → chained_stack_structure m lvl sp
        → evalDecl st s (lvl,x) locals (OK (lvl,x'))
        → match_env_ st ((lvl,x)::s) ((lvl,l)::CE) sp e_chain g m
        → exists e_chain' t2 m',
            exec_stmt g proc_t sp e_chain m s_locvarinit t2 e_chain' m' Out_normal
            ∧ match_env_ st ((lvl,x')::s) ((lvl,l')::CE) sp e_chain' g m'.
    Proof.
    Admitted.

    Lemma init_arg_locals_succeeds_and_preserve_match_env_:
      ∀ (locals : decl)(lparams : list paramSpec) (st : symboltable)(lvl : nat)
        l (CE : CompilEnv.state)
        (s_locvarinit : Cminor.stmt) (initparams : Cminor.stmt),
        store_params st ((lvl,l)::CE) lparams =: initparams
        → ∀ (g : genv) (proc_t : function) (sp : Values.val) (e_chain : env)
            (m : mem) (s:ST.state) l' l'' sz sz' sz'' x x' x'' CE' args,
          Datatypes.length CE = lvl
          → invariant_compile ((lvl,l)::CE) st
          → build_frame_lparams st (l,sz) lparams =: (l',sz')
          → init_locals st ((lvl,l')::CE) locals =: s_locvarinit
          → build_frame_decl st (l',sz') locals =: (l'',sz'')
          → build_compilenv st CE lvl lparams locals =: (CE',sz'')
          → chained_stack_structure m lvl sp
          → copyIn st bigs (lvl, x) lparams args (OK (lvl, x'))
          → evalDecl st s (lvl,x') locals (OK (lvl,x''))
          → match_env_ st ((lvl,x)::s) ((lvl,l)::CE) sp e_chain g m
          → exists e_chain' t2 m',
              exec_stmt g proc_t sp e_chain m s_locvarinit t2 e_chain' m' Out_normal
              ∧ match_env_ st ((lvl,x'')::s) CE' sp e_chain' g m'.
    Proof.
    Admitted.*)

    destruct f1 as (f_lvl,f_frm).
    assert (f_lvl=Datatypes.length CE_sufx). {
      admit. (*easy lemma.*)
    }
    subst f_lvl.
    specialize init_arg_locals_succeeds_and_preserve_match_env_
               with (1:=heq_store_prms_procedure_parameter_profile_s_parms_)
                    (* (4:=heq_bld_frm_procedure_parameter_profile_) *)
                    (5:=heq_init_lcl_procedure_declarative_part_s_locvarinit_) /sng.
                    (7:=heq_bldCE_)
                    (9:=h_eval_decl_)
                    (2:=eq_refl)
    .
    
                    (2:=eq_refl) (3:=h_stkcut_s_n_)


    destruct fr_prm.
    specialize init_params_succeeds_and_preserve_match_env_
               with (1:=heq_store_prms_procedure_parameter_profile_s_parms_)
                    (2:=eq_refl) (3:=h_stkcut_s_n_)
      as ? /sng.
    (8:=h_match_env1_)

    assert (invariant_compile ((Datatypes.length CE_sufx, [ ]) :: CE_sufx) st) /sng. {
      admit. (* TODO:lemma *)
    }
    assert (chained_stack_structure m_postchainarg (Datatypes.length CE_sufx) stkptr_proc) /sng. {
      apply chained_stack_structure_le with (S (Datatypes.length CE_sufx));eauto. }
    specialize init_params_succeeds_and_preserve_match_env_
               with
                  (*1:=heq_store_prms_procedure_parameter_profile_s_parms_*)
                  (5:=heq_bld_frm_procedure_parameter_profile_) (CE:=CE_sufx) (2:=eq_refl)
                    (7:=h_copy_in_) (3:=h_stkcut_s_n_)(8:=h_match_env1_)(4:=h_inv_comp_st_)
                    (proc_t := the_proc) (*6:=h_chain_m_postchainarg1_*)
      as ? /sng.
      edestruct h_forall_initparams_.
    * eassumption.
      * simpl. reflexivity.
      * admit. (* TODO: lemma. *) 
      * eapply chained_stack_structure_le with (1:=h_chain_m_postchainarg_);auto.
      * 
    assert (exists s_parms', store_params st CE_sufx procedure_parameter_profile =:s_parms'). {
      rewrite store_params_ok in heq_store_prms_procedure_parameter_profile_s_parms_.
      functional inversion heq_store_prms_procedure_parameter_profile_s_parms_;subst;eauto;
        rewrite <- store_params_ok in *.
    + 
        
        eapply h_chain_m_postchainarg0_.
      
    rewrite <- build_compilenv_ok in heq_bldCE_.
    functional inversion heq_bldCE_;subst /sng.
(* xx TODO: check this statement + do the same with build_frame_decl, so that we can have the same for build_compilenv. *)

      
    (* ******* CP_IN STEP ******* *)
    (* exec s_parms gives a result *)
    assert (exists locenv_postargs m_postargs trace_postargs,
                exec_stmt g the_proc stkptr_proc locenv_init m_postchainarg
                          s_parms trace_postargs locenv_postargs m_postargs Out_normal) /sng.
    { 

        
        
        
      revert heq_store_prms_procedure_parameter_profile_s_parms_.
      
      rewrite store_params_ok in *.
      unfold function_utils.store_params in heq_store_prms_procedure_parameter_profile_s_parms_.
      functional induction function_utils.store_params st ((pb_lvl, sto) :: CE_sufx) procedure_parameter_profile;try rewrite <- store_params_ok in * /sng.

      - simpl in heq_store_prms_procedure_parameter_profile_s_parms_.
        inversion heq_store_prms_procedure_parameter_profile_s_parms_.
        subst s_parms.
        exists locenv_init, m_postchainarg, nil.
        constructor.
      - match goal with H: pb = _ -> _ |- _ => rename H into IH end.
        match type of IH with
        | context [exec_stmt g ?X _ _ _ _ _ _ _ _] => set (the_proc':= X ) in *
        end.
        simpl in heq_store_prms_procedure_parameter_profile_s_parms_.
      admit.
    }
    decomp h_ex_.
    assert (∀ astnum addr ofs, 
               (forbidden st CE g astnum locenv stkptr m m addr ofs 
                -> forbidden st ((pb_lvl, sto) :: CE_sufx) g astnum locenv_postargs stkptr_proc
                             m_postargs m_postargs addr ofs)
               ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m_postargs
           ∧ (chained_stack_structure m_postargs (S (Datatypes.length CE_sufx)) stkptr_proc)) as
    h_incl_forbid_m_m_postargs_. {
      assert( CompilEnv.exact_levelG CE_sufx) /sng. {
        eapply CompilEnv.exact_levelG_sublist2 with (CE1:=CE_prefx).
        erewrite (CompilEnv.cut_until_spec1 _ _ _ _ h_CEcut_CE_pb_lvl_);eauto. }
      assert (stack_no_null_offset CE_sufx) /sng. {
        eapply no_null_offset_NoDup_G_cut with (2:=h_CEcut_CE_pb_lvl_) ;eauto.
        erewrite (CompilEnv.cut_until_spec1 _ _ _ _ h_CEcut_CE_pb_lvl_);eauto. }
      assert (all_addr_no_overflow CE_sufx) /sng. {
        eapply no_overflow_NoDup_G_cut with (2:=h_CEcut_CE_pb_lvl_) ;eauto.
        erewrite (CompilEnv.cut_until_spec1 _ _ _ _ h_CEcut_CE_pb_lvl_);eauto. }
      assert (stack_no_null_offset ((pb_lvl, sto) :: CE_sufx)) /sng. {
        eapply build_compilenv_stack_no_null_offset with (4:=heq_bldCE_);eauto. }
      assert (CompilEnv.exact_levelG ((pb_lvl, sto) :: CE_sufx)) /sng. {
        eapply h_inv_CE''_bld_. }
      assert (all_addr_no_overflow ((pb_lvl, sto) :: CE_sufx)) /sng. {
        eapply build_compilenv_stack_no_overf with (4:=heq_bldCE_);eauto. }
      assert (stack_localstack_aligned
                (Datatypes.length ((pb_lvl, sto) :: CE_sufx)) locenv_init g
                m_postchainarg stkptr_proc) /sng. {
        eapply chain_aligned.
        eapply h_chain_m_postchainarg_.
        (* lia fails because implicits do not match exactly (but are convertible) *)
        apply le_n. }
      intros /sng.
      specialize init_params_preserves_structure
        with (1:=h_exct_lvlG_) (2:=H) (3:=h_no_overf_)
             (4:=heq_store_prms_procedure_parameter_profile_s_parms_)
             (7:=h_aligned_g_m_postchainarg_)
             (8:=h_exec_stmt_s_parms_Out_normal_)(astnum:=astnum)
             (lvl:=(1 + Datatypes.length CE_sufx)%nat) as ? /sng.
      destruct h_impl_impl_and_;try eapply h_inv_CE''_bld_;auto /sng.
      decomp h_and_.
      split;[|split];intros /sng.
      + red in h_unch_forbid_m_postchainarg_m_postargs_.
        rewrite <- h_unch_forbid_m_postchainarg_m_postargs_.
        eapply forbidden_inv_locenv;eauto.
      + eapply Mem.unchanged_on_trans with (m2:=m_postchainarg).
        * apply h_unch_m_mpostchain_. 
        * eapply Mem.unchanged_on_implies with (1:=h_unchanged_on_m_postchainarg_m_postargs_).
            intros /sng.
            apply forbidden_inv_locenv with (locenv:=locenv_postchainarg).
            eapply h_forbidden_incl_m_m_poschainarg'_;eauto.
      + assumption. }


    (* We need to prove that now match_env_ is true between ((pb_lvl, f):: suffix_s)
       and (m_postargs,stkptr_proc).
       by induction +  assignment_preserve_match_env_ ? *)
    
    (* ********* END OF CP_IN STEP ************* *)

    (* stating that m_postfree is the result of free on the resulting state of proc body + free *)
    (* We should maybe write here unchange_forbidden on the state
       prior to free. Proving this needs to show that freeing
       something that was also free in m does not change forbiddent. *)
    enough (h_ex_:exists locenv_postcpout m_postcpout trace_postcpout,
               exec_stmt g the_proc stkptr_proc locenv_init m_proc_pre_init
                         (fn_body the_proc) trace_postcpout locenv_postcpout m_postcpout Out_normal
               ∧ exists m_postfree, Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree
               ∧ match_env_ st s'  CE stkptr locenv g m_postfree
               ∧ chained_stack_structure m_postfree (Datatypes.length CE) stkptr
               ∧ (∀ astnum : astnum, 
                     unchange_forbidden st CE g astnum locenv locenv stkptr m m_postfree
                     ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m_postfree)).
    { decomp h_ex_.
      match goal with
      | H:forall _, _ ∧ _ |- _ => rename H into h_forbid_
      end.
      exists m_postfree, trace_postcpout, Values.Vundef.
      split;[|split;[|split]].
      - econstructor.
        + eauto.
        + eauto.
        + rewrite <- Heqlocenv_init. eassumption.
        + cbn. reflexivity.
        + cbn. assumption.
      - assumption.
      - assumption.
      - assumption. }
    

    enough (h_ex_:exists locenv_postcpout m_postcpout trace_postcpout,
               exec_stmt g the_proc stkptr_proc locenv_postchainarg m_postchainarg
                         (Sseq (Sseq s_parms (Sseq s_locvarinit Sskip))
                               (Sseq s_pbdy s_copyout))
                         trace_postcpout locenv_postcpout m_postcpout Out_normal
               ∧ exists m_postfree, Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree
               ∧ match_env_ st s'  CE stkptr locenv g m_postfree
               ∧ chained_stack_structure m_postfree (Datatypes.length CE) stkptr
               ∧ (∀ astnum : astnum, 
                     unchange_forbidden st CE g astnum locenv locenv stkptr m_postchainarg m_postfree
                     ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m_postchainarg m_postfree)).
    { decomp h_ex_.
      eexists locenv_postcpout,m_postcpout.
      eexists.
      split.
      - unfold the_proc at 2.
        simpl.
        econstructor;eauto.
      - exists m_postfree.
        split;[|split;[|split]];eauto.
        intros astnum. 
        split.
        + red.
          intros sp_id ofs_id. 
          transitivity (forbidden st CE g astnum locenv stkptr m_postchainarg m_postchainarg sp_id ofs_id).
          * split.
            -- intro.
               auto.
            admit. (* Not the right property here. *)
          * eapply h_forall_astnum_.
        + eapply Mem.unchanged_on_trans with (m2:=m_postchainarg).
          * apply h_unch_forbid_m_mpostchainarg_.
          * eapply  h_forall_astnum_. }
    
    
xxx


    enough 
    (exists locenv_postcpout m_postcpout trace_postcpout,
        exec_stmt g the_proc stkptr_proc locenv_postchainarg m_postchainarg
                  (Sseq (Sseq s_parms (Sseq s_locvarinit Sskip)) (Sseq s_pbdy s_copyout))
                  trace_postcpout locenv_postcpout m_postcpout Out_normal
        ∧ exists m_postfree,
          Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree
          ∧ match_env_ st s'  CE stkptr locenv g m_postfree
          ∧ chained_stack_structure m_postfree (Datatypes.length CE) stkptr
          ∧ (∀ astnum : astnum, 
                unchange_forbidden st CE g astnum locenv locenv stkptr m m_postfree
                ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m_postfree)) /sng.
    { decomp h_ex_.
      exists locenv_postcpout, m_postcpout.
      exists (Events.Eapp trace_postchainarg trace_postcpout).
      split;[|esplit;[split;[|split;[|split]]]];eauto.
      simpl fn_body.
      econstructor;eauto. }

    (* unchange_forbidden on the state prior to free. Proving this
       needs to show that freeing something that was also free in m
       does not change forbidden. *)
    enough (h_ex_:exists locenv_postcpout m_postcpout trace_postcpout,
               exec_stmt g the_proc stkptr_proc locenv_init m_proc_pre_init
                         (fn_body the_proc) trace_postcpout locenv_postcpout m_postcpout Out_normal
               ∧ exists m_postfree,
                 Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree
                 ∧ match_env_ st s'  CE stkptr locenv g m_postfree
                 ∧ chained_stack_structure m_postfree (Datatypes.length CE) stkptr
                 ∧ (∀ astnum : astnum, 
                       unchange_forbidden st CE g astnum locenv locenv stkptr m m_postcpout
                       ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m_postcpout)).
    { decomp h_ex_.
      match goal with
      | H:forall _, _ ∧ _ |- _ => rename H into h_forbid_
      end.
      exists locenv_postcpout, m_postcpout, trace_postcpout.
      split;[|esplit;[split;[|split;[|split]]]];eauto.
      intros a. 
      specialize h_forbid_ with a.
      decomp h_forbid_.
      split.
      - unfold unchange_forbidden in *.
        intros /sng.
        (* inversion h_chain_m_postfree_ /sng. *)
        transitivity (forbidden st CE g a locenv stkptr m_postcpout m_postcpout sp_id ofs_id);eauto.
        Lemma free_unforbidden_nochange:
          forall m  m' m'' spb_proc sto_sz sp_id ofs_id sp_id ofs_id,
                 Mem.free m' spb_proc 0 sto_sz = Some m'' ->
                 forbidden st CE g a locenv stkptr m_postcpout mm' sp_id ofs_id <->
                 forbidden st CE g a locenv stkptr m'' m'' sp_id ofs_id
        unfold forbidden.
        split;intro h; decomp h.
        + destruct (Pos.eq_dec sp_id spb_proc).
          * subst.
        
        admit. (* some forbidden become free *)
          * admit.
        + admit.
      - apply Mem.unchanged_on_trans with m_postcpout;auto.
        apply Mem.free_unchanged_on with (1:=heq_free_).
        intros /sng.
        intro abs.
        red in abs.
        decomp abs.
        apply h_neg_free_blck_m_spb_proc_i_.
        red.
        eapply fresh_block_alloc_perm_;eauto. }
    
    enough (h_ex_:exists locenv_postinit m_postinit trace_postinit,
               exec_stmt g the_proc stkptr_proc locenv_init m_proc_pre_init
                         (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Ptrofs.zero)) (Evar chaining_param))
                               (Sseq s_parms (Sseq s_locvarinit Sskip)))
                         trace_postinit locenv_postinit m_postinit Out_normal
               ∧ match_env_ st (f1 :: suffix_s) ((pb_lvl, sto) :: CE_sufx) stkptr_proc locenv_postinit g m_postinit
               ∧ chained_stack_structure m_postinit (Datatypes.length ((pb_lvl, sto) :: CE_sufx)) stkptr_proc
               ∧ (∀ astnum : astnum, 
                     unchange_forbidden st CE g astnum locenv locenv_postinit stkptr m_proc_pre_init m_postinit
                     ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m_proc_pre_init m_postinit)).
    { decomp h_ex_.
      specialize IHh_eval_stmt_ with (1:=eq_refl) (2:=h_chain_m_postinit_) (3:=h_match_env0_) (f:=the_proc).
      destruct IHh_eval_stmt_ as [tr_postbdy [locenv_postbdy [m_postbdy IHh_eval_stmt_]]].
      decomp IHh_eval_stmt_.
      exists locenv_postbdy, m_postbdy.
      eexists.
      split.
      - unfold the_proc at 2.
        simpl.
        apply exec_stmt_assoc.
        econstructor;eauto.
        + econstructor;eauto.
          (* TODO copyout *) admit.
      - assert (h_ex_:∃ m_postfree : mem, 
                   Mem.free m_postbdy spb_proc 0 sto_sz = Some m_postfree).
        { admit. (* TODO, needs maybe a bit more that stack_freeable because chaining param is not a variable *)
        }
        decomp h_ex_. 
        exists m_postfree;split;auto.
        admit. (* TODO *)
    }

    



    admit. (* TODO: property of the initial part of a procedure. + subtle stuff about unchanged on caller's view *) 

(* lots of shelved.  *)
Admitted.



xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
old stuff
    decomp h_ex_.
    specialize IHh_eval_stmt_ with (1:=eq_refl) (2:=h_chain_m_postinit_) (3:=h_match_env0_) (f:=the_proc).


    (* Is invariant true at this point? *)
    assert (match_env_ st ((pb_lvl, f1'_p) :: intact_s ++ suffix_s')  CE stkptr locenv g m_proc_pre_init
               ∧ chained_stack_structure m_proc_pre_init (Datatypes.length CE) stkptr
               ∧ (∀ astnum : astnum,
                     unchange_forbidden st CE g astnum locenv locenv stkptr m_proc_pre_init m_proc_pre_init
                     ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m_proc_pre_init m_proc_pre_init)).

    (* Same as above but arriving just before the free performed at the end of funcall *)
    enough (h_ex_:exists locenv_postcpout m_postcpout trace_postcpout,
               exec_stmt g the_proc stkptr_proc locenv_init m_proc_pre_init
                         (fn_body the_proc) trace_postcpout locenv_postcpout m_postcpout Out_normal
               /\ match_env_ st s' CE stkptr locenv g m_postcpout
               ∧ chained_stack_structure m_postcpout (Datatypes.length CE) stkptr
               ∧ (∀ astnum : astnum,
                     unchange_forbidden st CE g astnum locenv locenv stkptr m m_postcpout
                     ∧ Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m_postcpout)).
    { decomp h_ex_.
      destruct (Mem.free m_postcpout spb_proc 0 sto_sz) as [m_postfree|m_postfree] eqn:heq_free_.
      all:swap 1 2.
      - edestruct Mem.range_perm_free eqn:heq.
        erewrite e in heq_free_.
        discriminate.
      - exists locenv_postcpout, m_postcpout, trace_postcpout.
        split;[|exists m_postfree;split;[|split;[|split]]].
        + assumption.
        + auto.
        + admit. (* no variable of CE and st are in m_postcpout, so the free maintains match_env_. *)
        + admit. (* no variable of CE and st are in m_postcpout, chained_stack_structure. *)
        + admit. (* free is always possible on a stackframe (should be in the invariant). *)
    }

    enough (h_ex_:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc stkptr_proc locenv_init m_proc_pre_init
                         (Sseq (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Ptrofs.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ forall locenv_caller,
                 match_env_ st (intact_s ++ suffix_s') CE stkptr locenv_caller g m_postbdy).
    { destruct h_ex_ as [locenv_postbdy [m_postbdy [trace_postbdy [h_exec_ok_ h_matchenv_ok_]]]].
      assert ( ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace),
                  exec_stmt g the_proc (Values.Vptr spb_proc Ptrofs.zero) locenv_postbdy m_postbdy
                            s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal) /sng.
      { admit. (* exec_stmt s_copyout does not raise any error *) }
      destruct h_ex_ as[locenv_postcpout [m_postcpout [trace_postcpout h_exec_ok2_]]].
      exists locenv_postcpout, m_postcpout, (Events.Eapp trace_postbdy trace_postcpout).      
      split;[|split;[|split;[|split]]].
      - unfold the_proc at 2;cbn.
        apply exec_stmt_assoc.
        apply exec_stmt_assoc.
        econstructor;eauto.
      - admit.
      - 

(* temporary patch before switching to strong_match: *)
        match goal with
        | H: context P [(match_env_ st (intact_s ++ suffix_s'))] |- _
          => let x := context P [(strong_match_env_ st (intact_s ++ suffix_s'))] in
             assert (h_str_matchenv_ok_:x) by admit
        end.
        up_type.

        Lemma copy_out_ok:
          ∀ st s prms_v params args opt_s', 
            copy_out st s prms_v params args opt_s' ->
            ∀ s' g the_proc spb ofs spb_proc CE s_copyout m_postbdy m_postcpout locenv_postcpout trace_postcpout locenv_postbdy,
              opt_s' = OK s' ->
              invariant_compile CE st ->
              level_of prms_v = (Datatypes.length CE - 1)%nat ->
              copy_out_params st CE params =: s_copyout ->
              exec_stmt g the_proc (Values.Vptr spb_proc Int.zero)
                        locenv_postbdy m_postbdy
                        s_copyout
                        trace_postcpout locenv_postcpout m_postcpout Out_normal ->
              (forall locenv_caller, strong_match_env_ st s CE (Values.Vptr spb ofs) locenv_caller g m_postbdy) ->
              forall locenv,  strong_match_env_ st s' CE (Values.Vptr spb ofs) locenv g m_postcpout.
        Proof.
          intros until 1 /sng. 
          induction h_copy_out_s_opt_s'_; !intros until 4; !intros ? h_strg_mtch_;try discriminate;subst;up_type /sng.
          - invclear heq /sng.
            cbn in h_cpout_prm_.
            invclear h_cpout_prm_ /sng.
            inversion h_exec_stmt_s_copyout_;subst.
            apply h_strg_mtch_.
          - rename n into real_param_name.
            rename v into param_v.
            intros locenv.
            specialize (IHh_copy_out_s_opt_s'_ s'0 g the_proc spb ofs spb_proc CE).
            rewrite copy_out_params_ok in h_cpout_prm_.
            functional inversion h_cpout_prm_;subst;rewrite <- copy_out_params_ok in * /sng.
            + (* In parameter, no problem *)
              destruct h_or_;
              match goal with
              | H: parameter_mode param = _, H': parameter_mode param = _ |- _ => rewrite H in H';discriminate
              end /sng.
            + (* In or InOut *)
              clear h_or_.
              rename x into chk. rename x0 into cpout_stmt. rename x1 into prm_nme_t.
              inversion h_exec_stmt_s_copyout_;try eq_same_clear /sng.
              clear h_exec_stmt_s_copyout_. (* should be useless now *)
              rename e1 into locenv_id_stored.
              rename m1 into m_id_stored.
              rename t2 into trace_id_stored.
              up_type.
              eapply IHh_copy_out_s_opt_s'_;eauto.
              intros locenv_caller. 


              admit. 

              enough (match_env_ st s' CE (Values.Vptr spb ofs) locenv_caller g m_id_stored).
              { admit. } (* temporary until strong_match_env_ everywhere *)
              assert (stack_match st s' CE (Values.Vptr spb ofs) locenv_caller g m_id_stored).
              { (* Need here something stating thate local variable correspond to params addresses. *)
                xxx
              }

              specialize (IHh_copy_out_s_opt_s'_ cpout_stmt m_postcpout m_id_stored locenv_postcpout trace_id_stored).

            

            cbn in h_cpout_prm_.
            assert ((compute_chnk_id st (parameter_name param)) = OK AST.Mint32) /sng.
            { admit. (* TODO *) }
            rewrite heq0 in h_cpout_prm_.
            simpl in h_cpout_prm_.
            destruct (copy_out_params st CE lparam) eqn:?; try discriminate /sng.
            simpl in h_cpout_prm_.
            destruct (transl_variable st CE 0%nat (parameter_name param)) eqn:?; try discriminate /sng.
            simpl in h_cpout_prm_.
            destruct h_or_ /sng.
            + rewrite heq1 in h_cpout_prm_.
              invclear h_cpout_prm_ /sng.
              inversion h_exec_stmt_;subst;auto /sng.
              * eapply IHh_copy_out_s_opt_s'_ ;eauto.
                specialize 
                  (IHh_copy_out_s_opt_s'_ s'0 g the_proc spb ofs spb_proc CE s0 m_postbdy m_postcpout locenv_postcpout t2 locenv_postbdy eq_refl h_inv_comp_CE_st_ heq h_cpout_prm_lparam_s0_).
                apply IHh_copy_out_s_opt_s'_;auto.
                intros locenv.
                assert (∀ locenv : env, strong_match_env_ st s'0 CE (Values.Vptr spb ofs) locenv g m_postcpout) /sng.
                { 
                eapply IHh_copy_out_s_opt_s'_;eauto.
              inversion h_exec_stmt_;subst;eauto.
              eapply IHh_copy_out_s_opt_s'_;eauto.
              * 
            
            

            eapply IHh_copy_out_s_opt_s'_;eauto.
            + ec

            assert (compute_chnk_id st (parameter_name param) =: ast_num_type) /sng.
            { admit. (* well formedness of st wrt to ast nums *) }
            rewrite heq_fetch_exp_type0_ in h_cpout_prm_.
            
            
        Qed.
        admit.
        (* copy_out property *)
      
      
      
    }



    enough (h_ex_:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env_ st ((pb_lvl, f1'_l ++ f1'_p)::suffix_s') ((pb_lvl, sto)::CE_sufx)
                            (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy).
    { destruct h_ex_ as [locenv_postbdy [m_postbdy [trace_postbdy [h_exec_ok_ h_matchenv_ok_]]]].
      assert (strong_match_env_ st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto)::CE_sufx)
                                (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy) /sng.
      { admit. (* to be added (replace it actually) in the invariant *) }
      (* Just before cpout, the suffix of s match with the enclosing stack  *)
      assert (h_match_env_suffix_s'_: forall enclosingstack locenv_caller,
                 Mem.loadv AST.Mint32 m_postbdy (Values.Vptr spb_proc Int.zero) = Some enclosingstack ->
                 strong_match_env_ st suffix_s' CE_sufx enclosingstack locenv_caller g m_postbdy).
      { intros /sng.
        inversion h_strg_mtch_ /sng.
        rewrite heq2 in heq.
        invclear heq /sng.
        apply strong_match_env_inv_locenv_ with locenv0;assumption. }

      assert ( ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace) m_postfree,
                   exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postbdy m_postbdy
                             s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
                   ∧ Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree) /sng.
      { admit. }
      destruct h_ex_ as[locenv_postcpout [m_postcpout [trace_postcpout [m_postfree [h_exec_ok2_ h_free_]]]]].
        

    enough (h_ex_:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env_ st ((pb_lvl, f1'_l ++ f1'_p)::suffix_s') ((pb_lvl, sto)::CE_sufx)
                            (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy
               /\ ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace) m_postfree,
                   exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postbdy m_postbdy
                             s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
                   ∧ Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree).
    { destruct h_ex_ as
          [locenv_postbdy
             [m_postbdy
                [trace_postbdy [h_exec_ok_ [h_matchenv_ok_ [locenv_postcpout [m_postcpout [trace_postcpout [m_postfree [h_exec_ok2_ h_free_]]]]]]]]]].

      assert (strong_match_env_ st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto)::CE_sufx)
                                (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy) /sng.
      { admit. (* to be added (replace it actually) in the invariant *) }

      (* Just before cpout, the suffix of s match with the enclosing stack  *)
      assert (h_match_env_suffix_s'_: forall enclosingstack locenv_caller,
                 Mem.loadv AST.Mint32 m_postbdy (Values.Vptr spb_proc Int.zero) = Some enclosingstack ->
                 strong_match_env_ st suffix_s' CE_sufx enclosingstack locenv_caller g m_postbdy).
      { intros /sng.
        inversion h_strg_mtch_ /sng.
        rewrite heq2 in heq.
        invclear heq /sng.
        apply strong_match_env_inv_locenv_ with locenv0;assumption. }

      assert (h_ex_:exists intact_s', cut_until s' pb_lvl intact_s' suffix_s').
      { admit. (* property of copy_out *) }
      destruct h_ex_ as [intact_s' h_intact_s'_].
      assert (s' = intact_s' ++ suffix_s'). {
        symmetry.
        eapply cut_until_spec1;eauto. }
      subst s'.
      assert (h_match_env_intact_s_suffix_ss_: forall locenv_caller,
                 strong_match_env_ st (intact_s ++ suffix_s') CE (Values.Vptr spb ofs) locenv_caller g m_postbdy).
      { (* Hard part, needs the fact that intact_s did not change *) }                  
        
        assert (strong_match_env_ intact_s ).

      exists locenv_postcpout m_postcpout (Events.Eapp trace_postbdy trace_postcpout) m_postfree.
      split;[|split].
      - unfold the_proc at 2;cbn.
        apply exec_stmt_assoc.
        econstructor;eauto.
      - assumption.
      - 
      
      

XXXX

    enough (h_ex_:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq
                         (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                            (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env_ st ((pb_lvl, f1'_l ++ f1'_p)::suffix_s') CE (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy
               /\ ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace) m_postfree,
                   exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postbdy m_postbdy
                             s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
                   /\ Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree
                   /\ match_env_ st s' CE (Values.Vptr spb ofs) locenv g m_postfree).
    {
      destruct h_ex_ as
          [locenv_postbdy [m_postbdy [trace_postbdy [h_exec_ok_ [h_matchenv_ok_ [locenv_postcpout
                                                                                 [m_postcpout
                                                                                    [trace_postcpout
                                                                                       [ m_postfree
                                                                                           [h_exec_ok2_ [h_free_ok_ h_matchenv_ok2_]]]]]]]]]]].

      (* the suffix match before cpout *)
      assert (forall enclosingstack locenv_caller,
                 Mem.loadv AST.Mint32 m_postbdy (Values.Vptr spb_proc Int.zero) = Some enclosingstack ->
                 match_env_ st suffix_s' CE_sufx enclosingstack locenv_caller g m_postbdy).
      { assert (strong_match_env_ st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE_sufx) (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy) /sng.
        { admit. (* TODO: put this in the invariant *) }
        inversion H /sng.
        intros /sng.
        rewrite heq2 in heq.
        invclear heq /sng.
        inversion H9 /sng.
        - apply match_env_inv_locenv_ with locenv0;assumption.
        - apply match_env_inv_locenv_ with locenv0;assumption. }


      assert (match_env_ st (intact_s ++ suffix_s') CE (Values.Vptr spb ofs) locenv g m_postcpout).
      { 

      

      exists locenv_postcpout m_postcpout (Events.Eapp trace_postbdy trace_postcpout) m_postfree.
      split;[|split] ;try assumption.
      unfold the_proc at 2;cbn.
      apply exec_stmt_assoc.
      econstructor;eauto. }

    enough (h_ex_:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq
                         (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                            (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env_ st (intact_s ++ suffix_s') CE (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy).
    { destruct h_ex_ as [locenv_postbdy [m_postbdy [trace_postbdy [h_exec_ok_ h_matchenv_ok_]]]].
      exists locenv_postbdy m_postbdy trace_postbdy.
      split;[|split].
      - auto.
      - auto.
      -

        Lemma copy_out_ok: forall the_proc CE pb_lvl CE_sufx st intact_s intact_s' suffix_s' g m_postbdy
                                  locenv_postbdy spb_proc ofs_proc f1'_p params args sto  s_copyout ,
          (* suffix_s' is not changed by copy_out, since that would
          imply an aliasing between the argument in params and the
          variable (still visible from proc since it is in suffix_s' *)
          copy_out st (intact_s ++ suffix_s') (pb_lvl, f1'_p) params args (OK (intact_s' ++ suffix_s')) ->
          copy_out_params st ((pb_lvl, sto) :: CE_sufx) params =: s_copyout ->
          match_env_ st (intact_s ++ suffix_s') CE (Values.Vptr spb_proc ofs_proc) locenv_postbdy g m_postbdy ->
          (* strong_match implies that match_env_ suffix_s' CE_sufx (Vptr (Load^n 0) 0) holds too *)
          ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace),
            exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postbdy m_postbdy
                      s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
            /\ ∃ m_postfree, Mem.free m_postcpout spb_proc 0 (fn_stackspace the_proc) = Some m_postfree
                             /\ forall locenv, match_env_ st (intact_s' ++ suffix_s') CE (Values.Vptr spb_caller ofs) locenv g m_postfree.
        .

        admit. (* Separate lemma about copy_out_params vs copy_out. We need more hypothesis probably. *)
    }

       
    

    
    enough (h_ex_:exists locenv_postdecl m_postdecl trace_postdecl,
            exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                      (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                            (Sseq s_parms (Sseq s_locvarinit Sskip)))
                      trace_postdecl locenv_postdecl m_postdecl Out_normal).


XXXx
    (* execute all the procedure except the cpout part. *)
    enough (h_ex_:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) (Sseq s_pbdy Sskip))
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env_ st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE_sufx) (Values.Vptr spb_proc Int.zero)
                              locenv_postbdy g m_postbdy
).
    { destruct h_ex_ as [locenv_postbdy [m_postbdy [trace_postbdy [h_decl_ok_exec_ h_decl_ok_matchenv_]]]].
      assert({ m_postfree| Mem.free m_postbdy spb_proc 0 sto_sz = Some m_postfree}) as h_exT_.
      { apply Mem.range_perm_free.
        pose proof Mem.perm_alloc_2 _ _ _ _ _ h_alloc_ /sng.
        red.
        intros /sng.
        specialize (H ofs0 Cur h_and_).
        admit. (* from H and no change in freeable status in compiled programs. *)
      }
      destruct h_exT_ as [m_postfree ?] /sng.
      exists m_postfree trace_postbdy Values.Vundef.
      pose (the_proc' := {|
            fn_sig := p_sig;
            fn_params := chaining_param :: transl_lparameter_specification_to_lident st procedure_parameter_profile;
            fn_vars := transl_decl_to_lident st procedure_declarative_part;
            fn_stackspace := sto_sz;
            fn_body := Sseq (Sseq
                               (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) (Sseq s_pbdy Sskip)) s_copyout |}).
      enough (eval_funcall g m (AST.Internal the_proc') (chaining_expr_from_caller_v :: args_t_v) trace_postbdy m_postfree Values.Vundef
              ∧ match_env_ st s' CE (Values.Vptr spb ofs) locenv g m_postfree) /sng.
      { admit. (* Lemma: associativity of Sseq wrt exec_stmt *) }
      assert (fn_vars the_proc = fn_vars the_proc') /sng.
      { cbn.
        reflexivity. }
      assert (fn_params the_proc = fn_params the_proc') /sng.
      { cbn.
        reflexivity. }
      rewrite heq2, heq3 in *.
      split.
      - econstructor;eauto.
        + rewrite <- Heqlocenv_init.
          assert (exec_stmt g the_proc' (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                            (Sseq
                               (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) (Sseq s_pbdy Sskip)) trace_postbdy locenv_postbdy m_postbdy
                            Out_normal).
          { admit . (* idem: associativity of Sseq. *) }
          unfold the_proc' at 2.
          cbn.
          econstructor.
          * eassumption.
          * XXX

              enough (h_ex_:exists locenv_postcpout m_postcpout trace_postcpout,
                         exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                                   s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
                         /\ match_env_ st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE_sufx) (Values.Vptr spb_proc Int.zero)
                                      locenv_postcpout g m_postcpout).

          eassumption.
        + cbn.
          reflexivity.
        + cbn.
          assumption.
      - 
        econstructor;eauto.
        + rewrite <- Heqlocenv_empty.
          unfold the_proc at 2.
          cbn.
          eassumption.
        + unfold the_proc.
          cbn.
          reflexivity.
        + unfold the_proc.
          cbn.
          pose proof  Mem.valid_access_alloc_same _ _ _ _ _ h_alloc_ /sng.
          reflexivity.
        + 



      Lemma copy_out_OK: forall intact_s suffix_s' pb_lvl f1'_p params args s',
          copy_out st (intact_s ++ suffix_s') (pb_lvl, f1'_p) params args (OK s') -> 
          match_env_ st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE_sufx) (Values.Vptr spb_proc Int.zero)
                    locenv_postbdy g m_postbdy -> 
          exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) 
      
xxxxx
      assert({ m_postfree| Mem.free m_postbdy spb_proc 0 sto_sz = Some m_postfree}) as h_exT_.
      { apply Mem.range_perm_free.
        pose proof Mem.perm_alloc_2 _ _ _ _ _ h_alloc_ /sng.
        red.
        intros /sng.
        specialize (H ofs0 Cur h_and_).
        admit. (* from H and no change in freeable status in compiled programs. *)
      }
      destruct h_exT_ as [m_postfree ?] /sng.

XXXXXXXXXXX
    (* After executing intialization of parameters and local variables, we have the usual invariant back *)
    assert (h_ex_:exists locenv_postdecl m_postdecl trace_postdecl,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_empty m_proc_pre_init
                         (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                               (Sseq s_parms (Sseq s_locvarinit Sskip))) 
                         trace_postdecl locenv_postdecl m_postdecl Out_normal
               /\ match_env_ st (f1 :: suffix_s) ((pb_lvl, sto) :: CE_sufx)
                            (Values.Vptr spb_proc Int.zero) locenv_postdecl g m_postdecl).
    { 
      (* After copying parameters into the stack we have a hybrid invariant: parameters are visible, but not local variables *)
      assert (h_ex_:exists locenv_postprms m_postprms trace_postprms,
                 exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_empty m_proc_pre_init
                           (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                 s_parms)
                           trace_postprms locenv_postprms m_postprms Out_normal
                 /\ match_env_ st ((pb_lvl,f) :: suffix_s) ((pb_lvl, fst fr_prm) :: CE_sufx)
                              (Values.Vptr spb_proc Int.zero) locenv_postprms g m_postprms ).
      {
        (* Evaluating the first argument allows to link to the
           enclosing procedure, all variable accessible on the spark side
           are accessible with one more "load" than before. *)
        (* First we prove that there exists a resulting state *)
        assert (h_ex_:exists locenv_postchain m_postchain trace_postchain,
                   exec_stmt g the_proc (Values.Vptr spb_proc Int.zero)
                             locenv_empty m_proc_pre_init
                             (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                             trace_postchain locenv_postchain m_postchain Out_normal
                   /\ (stack_match st ((pb_lvl,nil) :: suffix_s) ((pb_lvl, nil) :: CE_sufx)
                                   (Values.Vptr spb_proc Int.zero) locenv_postchain g m_postchain)).
        { destruct (Mem.valid_access_store m_proc_pre_init AST.Mint32 spb_proc
                                           (Int.unsigned (Int.add Int.zero Int.zero))
                                           chaining_expr_from_caller_v) as [m_postchain h_m_postchain_].
          { apply Mem.valid_access_freeable_any.
            eapply Mem.valid_access_alloc_same;eauto.
            - apply Int.unsigned_range.
            - simpl.
              rewrite Int.add_zero,Int.unsigned_zero; cbn.
              subst init_sto_sz.
              pose proof build_frame_lparams_mon_sz _ _ _ _ heq_bld_frm_procedure_parameter_profile_ /sng.
              cbn in h_le_.
              transitivity (snd fr_prm);auto.
              change sto_sz with (snd (sto, sto_sz)).
              eapply build_frame_decl_mon_sz;eauto.
            - exists 0.
              simpl.
              reflexivity. }
          do 3 eexists.
          split.
          - eapply exec_Sstore with (v:=chaining_expr_from_caller_v) (vaddr:=(Values.Vptr spb_proc (Int.add Int.zero Int.zero))).
            + apply eval_Econst.
              reflexivity.
            + apply eval_Evar.
              subst_exc pb.
              simpl fn_vars.
              simpl fn_params.              
              lazy beta iota delta [set_params].
              fold set_params.
              lazy beta iota delta [set_locals].
              fold set_locals.
              admit. (* because chaining param should be different than any other parameter/var.  *)
            + simpl.
              eassumption.
          - eq_same_clear;up_type.
            assert (h_stck_mtch_CE_:=me_stack_match h_match_env_).
            (* From the point of view of the caller, all variables visible in suffix_s are still there. *)
            assert (stack_match st suffix_s CE (Values.Vptr spb ofs) locenv g m) /sng.
            { red.
              intros /sng.
              red in h_stck_mtch_CE_.
              specialize (h_stck_mtch_CE_ nme v nme_t load_addr_nme typ_nme cm_typ_nme).
              assert (evalName st s nme (OK v)) /sng.
              { admit. (* if it is mapped to v in suffix_s, then it is also in s (no clash name). *)  }
              specialize (h_stck_mtch_CE_ h_eval_name_nme_v0_ heq_type_of_name_ heq_transl_name_ heq_transl_type_ heq_make_load_).
              destruct h_stck_mtch_CE_ as [? [? ?]] /sng.
              exists load_addr_nme_v;split;auto. }

            assert (stack_match st suffix_s CE_sufx (Values.Vptr spb ofs) locenv g m) /sng.
            { (* Lemma: taking a suffix of CE makes stack_match weaker *)
              red; intros /sng.
              eapply h_stk_mtch_suffix_s_m_; try eassumption.
              admit. (* because CE is an extension of CE_sufx, without clash. *) }
            
            (* from the point of view of the called procedure, once the chaining arg has been copied to the stack,
               all previous variables visible from suffix_s are still visible but with one more load, due to the
               one more level in CE. *)
            (* reduce the size of the current goal *)
            clear - h_stk_mtch_suffix_s_m_ h_stk_mtch_suffix_s_m0_ h_cut_until_
                    h_m_postchain_ Heqlocenv_empty h_alloc_ h_chaining_expr_from_caller_v_ h_inv_CE''_bld_.
            clearbody the_proc.
            red.
            intros /sng.

            (* We need to instantiate the stack_match hypothesis on something, we need first to prove that
                 [evalName st s nme (OK v)].
                 Sketch: 
                   -> [ evalName st ((pb_lvl, [ ]) :: suffix_s) nme (OK v)]
                   -> [evalName st suffix_s nme (OK v)]
                   -> [evalName st s nme (OK v)]
             *)
            assert (evalName st suffix_s nme (OK v)) /sng.
            { (* should be lemma about empty top frame.  *)
              inversion h_eval_name_nme_v_ /sng.
              - constructor.
                cbn in heq_SfetchG_x_.
                assumption.
              - admit. (* array *)
              - admit. (* record *) }
            (* ****************** *)
            (* Now we need to prove the other premisses of h_stk_mtch_suffix_s_m_.
                 This is very painful for something trivial. *)
            assert (exists δ nme_t_sub_indirections, nme_t = Ebinop Oadd nme_t_sub_indirections δ) /sng.
            { functional inversion heq_transl_name_ /sng.
              functional inversion h_eq_transl_var_ /sng.
              unfold build_loads.
              eexists;eexists;eauto. }
            destruct h_ex_ as [δ [nme_t_sub_indirections ?]] /sng.
            subst nme_t.
            
            assert (exists pb_lvl_sub, (pb_lvl = S pb_lvl_sub /\ CompilEnv.level_of_top CE_sufx = Some pb_lvl_sub)) /sng.
            { assert (h_ce_lvl_ := ci_exact_lvls _ _ h_inv_CE''_bld_) /sng.
              inversion h_exct_lvlG_ /sng.
              destruct (Datatypes.length CE_sufx) eqn:heq_lgthCE_sufx_.
              - apply length_zero_iff_nil_ in heq_lgthCE_sufx_.
                subst.
                functional inversion heq_transl_name_.
              - exists n;split;auto.
                assert (invariant_compile CE_sufx st) /sng.
                { eapply invariant_compile_sublist with (CE1:=[(S n, sto)]);auto. }
                pose proof ci_exact_lvls _ _ h_inv_comp_CE_sufx_st_ /sng.
                inversion h_exct_lvlG_CE_sufx0_.
                + subst CE_sufx.
                  inversion h_exct_lvlG_;subst /sng.
                  inversion heq.
                + cbn.
                  subst CE_sufx.
                  cbn in heq_lgthCE_sufx_.
                  inversion heq_lgthCE_sufx_ /sng.
                  reflexivity. }
            destruct h_ex_ as [pb_sub_lvl [? ?]]; subst pb_lvl /sng.

            functional inversion heq_make_load_;subst load_addr_nme /sng.
            functional inversion heq_transl_name_ /sng.
            functional inversion h_eq_transl_var_ /sng.
            subst.
            cbn in heq_lvloftop_m'_.
            inversion heq_lvloftop_m'_.
            subst m'; eq_same_clear.
            assert (transl_name st CE_sufx (Identifier astnum id) =:
                                 Ebinop Oadd (build_loads_ (pb_sub_lvl - lvl_id))
                                 (Econst (Ointconst (Int.repr δ_id)))) /sng.
            { unfold transl_name.
              unfold transl_variable.
              simpl in heq_CEfetchG_id_,heq_CEframeG_id_.
              rewrite heq_CEfetchG_id_,heq_CEframeG_id_,heq_lvloftop_CE_sufx_pb_sub_lvl_.
              unfold build_loads.
              reflexivity. }
            assert (make_load (Ebinop Oadd (build_loads_ (pb_sub_lvl - lvl_id)) (Econst (Ointconst (Int.repr δ_id)))) cm_typ_nme
                               =: Eload chunk (Ebinop Oadd (build_loads_ (pb_sub_lvl - lvl_id)) (Econst (Ointconst (Int.repr δ_id))))) /sng.
            { unfold make_load.
              rewrite h_access_mode_cm_typ_nme_.
              reflexivity. }

            red in h_stk_mtch_suffix_s_m0_.
            pose proof (h_stk_mtch_suffix_s_m0_
                          _ _ _ _ _ _
                          h_eval_name_nme_v0_ heq_type_of_name_ heq_transl_name0_ heq_transl_type_ heq_make_load0_)
              as h_stk_mtch_suffix_s_m'_.
            (* instantiation done *)
            (* ****************** *)
            destruct h_stk_mtch_suffix_s_m'_ as [v_t [? ?]] /sng.
            exists v_t.
            split;auto.
            inversion h_CM_eval_expr_v_t_ /sng.
            inversion h_CM_eval_expr_vaddr_ /sng.
            apply eval_Eload with (vaddr := vaddr).
            + remember (set_locals (fn_vars the_proc) (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc)))
                as locenv_postchain.
              apply eval_Ebinop with (v1:=v1) (v2:=v2);auto.
              * (* 1 loads are evaluated only from m, locenv is orthogonal.
                   2 there one more load than in h_CM_eval_expr_v1_, but m_post_chain has one mode frame on the stack. *)
                admit.
              * (* lemma: a constant expression is evaluated indenpendently of the state, hence h_CM_eval_expr_v2_ is sufficient *)
                admit.
            + (* 1 vaddr is the address of a spark variable in Cminor, which exists in m.
                 2 The only difference between m and m_postchain is the new frame (see h_alloc_)
                   and the store on the chaining arg located in the new frame (h_m_postchain_).
                 Hence the value stored at vaddr has not changed.  *)
              admit.
              (*TBC.*)
        }
        destruct h_ex_ as [locenv_postchain [m_postchain [trace_postchain [h_decl_ok_exec_ ?]]]] /sng.

xxxx
        assert (match_env_ st suffix_s CE_sufx (Values.Vptr spb_proc Int.zero) locenv_postchain g m_postchain).

        assert (match_env_ st ((pb_lvl, nil) :: suffix_s) ((pb_lvl, nil) :: CE_sufx)
                           (Values.Vptr spb_proc Int.zero) locenv_postchain g m_postchain) /sng.
        { split.
          + apply h_stk_mtch_.
          + admit.
          + up_type.
            pose proof (me_stack_match_functions_ h_match_env_) as h_sck_mtch_fun_.
            red in h_sck_mtch_fun_.
            red.
            intros /sng.
            specialize (h_sck_mtch_fun_ p0 pb_lvl0 pb0 heq_fetch_proc_p0_).
            destruct h_sck_mtch_fun_ as [CE_prefx' [CE_sufx' [p0addr [p_id [p0_fundef [p_lsubprocs hand]]]]]].
            decomp hand.
            destruct (Compare.le_dec pb_lvl0 pb_lvl).
            * exists ((pb_lvl, [ ]) :: CE_prefx') CE_sufx' p0addr p_id p0_fundef p_lsubprocs.
              assert (Cminor.eval_expr g (Values.Vptr spb_proc Int.zero) locenv_postchain m_postchain
                                       (Econst (Oaddrsymbol (transl_procid p0) (Int.repr 0))) p0addr).
              { inversion h_CM_eval_expr_p0addr_;subst.
                constructor;auto. }

              split;[|split];auto.
              apply CompilEnv.Cut_Until_Tail.
              -- simpl.
                 lia.
              -- assumption.
            

            

            rewrite transl_procedure_ok in heq_transl_proc_pb0_.
            functional inversion heq_transl_proc_pb0_.
                  
(*              


Lemma foo: forall CE (st : symboltable) pb pb_lvl res prfx,
    transl_procedure st CE pb_lvl pb = OK res ->
    invariant_compile CE st ->
    invariant_compile (List.app prfx CE) st ->
    transl_procedure st (List.app prfx CE) pb_lvl pb = OK res.
Proof.
  intros /sng.
  

              Lemma foo: forall CE (st : symboltable) pb pb_lvl,
                  transl_procedure st ((Datatypes.length CE, nil) :: CE) pb_lvl pb = transl_procedure st CE pb_lvl pb.
              Proof.
                intros /sng.
                rewrite transl_procedure_ok.
                functional induction function_utils.transl_procedure st CE pb_lvl pb
                  using transl_procedure_ind2
                with (P0:= fun enclosingCE (lvl : level) (decl : declaration) res =>
                             function_utils.transl_declaration st ((Datatypes.length enclosingCE, nil) :: enclosingCE) lvl decl = res )
                ;up_type /sng.
                - simpl.
                  rewrite <- build_compilenv_ok in heq.
                  functional inversion heq;subst /sng.
                  unfold build_compilenv.
                  unfold stoszchainparam in *.
                  rewrite heq_bld_frm_lparams_;simpl.
                  rewrite heq2;simpl.
                  rewrite heq_bool_true_.
                  rewrite <- IHr.
xxxx


                functional induction (transl_procedure st CE pb_lvl' pb).
*)                
              admit.

              
            * inversion h_CM_eval_expr_x_.
              constructor;auto.
            * assumption.
            
          + admit.
          + admit.
          + admit.
          + admit.
          + admit.
          + admit. }
            
        (* Storing values of parameters of the procedure. *)
        assert (h_ex_:exists locenv_post_parms m_post_parms trace_post_parms,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero)
                         locenv_postchain m_postchain  s_parms
                         trace_post_parms locenv_post_parms m_post_parms Out_normal
             /\ match_env_ st ((pb_lvl, f) :: suffix_s) ((pb_lvl, fst fr_prm) :: CE)
                          (Values.Vptr spb_proc Int.zero) locenv_post_parms g m_post_parms).
        {
          admit.
        }
        destruct h_ex_ as [locenv_postparms [m_postparms [trace_postparms [? ?]]]] /sng.
        exists locenv_postparms m_postparms (Events.Eapp trace_postchain trace_postparms).
        split.
        - eapply exec_Sseq_continue;eauto.
        - assumption.
      }
      destruct h_ex_ as [locenv_postprms [m_postprms [trace_postprms [h_decl_ok_exec_ h_decl_ok_matchenv_]]]].
      admit.
    }
    destruct h_ex_ as [locenv_postdecl [m_postdecl [trace_postdecl [h_decl_ok_exec_ h_decl_ok_matchenv_]]]].
    assert (h_ex_:exists locenv_postcpout m_postcpout trace_postcpout m_postfree vres,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postdecl m_postdecl 
                         (Sseq s_pbdy s_copyout) (* executing the body of the procedure *)
                         trace_postcpout locenv_postcpout m_postcpout Out_normal (* FIXME: Return? *)
               /\ 
               outcome_free_mem Out_normal m_postcpout spb_proc (fn_stackspace the_proc) m_postfree
               /\ 
               outcome_result_value Out_normal (AST.sig_res (fn_sig the_proc)) vres
               /\
               (* Is it true that locenv did not change here? *)
               (* To prove this I probably need (s' should be split):
                match_env_ st ((pb_lvl, f1'_l ++ f1'_p)::s') ((pb_lvl, sto) :: CE) (Values.Vptr spb_proc Int.zero) locenv_postcpout g
                m_postcpout*)
               match_env_ st s' CE (Values.Vptr spb ofs) locenv g m_postfree).
    { 
      (* Executing the body of the procedure: induction hypothesis applies, match_env_ is preserved. *)
      assert (h_ex_:exists locenv_postbdy m_postbdy trace_postbdy,
                 exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postdecl m_postdecl 
                           s_pbdy
                           trace_postbdy locenv_postbdy m_postbdy Out_normal
                 /\ match_env_ st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE) (Values.Vptr spb_proc Int.zero)
                              locenv_postbdy g m_postbdy).
      { specialize (IHh_eval_stmt_ _ _ the_proc _ _ _ h_decl_ok_matchenv_).
        destruct IHh_eval_stmt_ as [trace_postbdy [locenv_postbdy [m_postbdy [IH_exec_stmt_ IH_match_env_] ]]].
        exists locenv_postbdy m_postbdy trace_postbdy;split;auto. }
      destruct h_ex_ as [locenv_postbdy [m_postbdy [trace_postbdy [h_bdy_ok_1_ h_bdy_ok_2_]]]].
      admit. (* Lemma about copy_out *) }
    destruct h_ex_ as [locenv_postcpout [m_postcpout [trace_postcpout [m_postfree [vres [ h_exec_ [h_outcome_ [h_vres_ h_matchenv_ ]]]]]]]].

    exists (Events.Eapp trace_postdecl trace_postcpout).
    exists (set_optvar None vres locenv) m_postfree.
    split.
    + eapply exec_Scall;eauto.
      * econstructor;eauto.
      * simpl.
        unfold transl_procsig in heq_transl_procsig_p_.
        rewrite heq_fetch_proc_p_ in heq_transl_procsig_p_.
        rewrite heq_pb_ in heq_transl_procsig_p_.
        simpl in heq_transl_procsig_p_.
        rewrite heq_transl_lprm_spec_procedure_parameter_profile_p_sig_ in heq_transl_procsig_p_.
        simpl in heq_transl_procsig_p_.
        inversion heq_transl_procsig_p_.
        reflexivity.
      * (* gather every intermediate parts together to get funcall ---> m_postfree *)
        eapply eval_funcall_internal with (e2:=locenv_postcpout) (out:=Out_normal);eauto.
        simpl fn_body.
        subst locenv_empty. 
        eapply exec_Sseq_continue.
        -- eapply h_decl_ok_exec_.
        -- eapply h_exec_.
        -- reflexivity.
    + simpl.
      assumption.
  (* Sequence *)
  - simpl in *.
    decomp (IHh_eval_stmt1_ s1 eq_refl CE _ h_inv_comp_CE_st_
                           heq1 spb ofs f  locenv g m h_match_env_).
    decomp (IHh_eval_stmt2_ s' eq_refl CE _ h_inv_comp_CE_st_
                           heq0 spb ofs f _ _ _ h_match_env0_).
    exists (Events.Eapp x1 x4).
    exists x5.
    exists x6.
    split.
    + econstructor;eauto.
    + assumption.
(* lots of shelved.  *)
Admitted.

    (* TODO: deal with lvl_p = 0. *)
