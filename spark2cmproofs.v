
Require Import function_utils.
Require Import LibHypsNaming.
Require Import Errors.
Require Import spark2Cminor.
Require Import Cminor.
Require Ctypes.
Require Import symboltable.
Require Import semantics.

Lemma wordsize_ok : wordsize = Integers.Int.wordsize.
Proof.
  reflexivity.
Qed.

Lemma modulus_ok: modulus = Integers.Int.modulus.
Proof.
  reflexivity.
Qed.

Lemma half_modulus_ok: half_modulus = Integers.Int.half_modulus.
Proof.
  reflexivity.
Qed.

Lemma max_unsigned_ok: max_unsigned = Integers.Int.max_unsigned.
Proof.
  reflexivity.
Qed.

Lemma max_signed_ok: max_signed = Integers.Int.max_signed.
Proof.
  reflexivity.
Qed.

Lemma min_signed_ok: min_signed = Integers.Int.min_signed.
Proof.
  reflexivity.
Qed.

Import Symbol_Table_Module.
Open Scope error_monad_scope.

Open Scope Z_scope.

(* Auxiliary lemmas, should go in Compcert? *)
Lemma repr_inj:
  forall v1 v2,
    Integers.Int.min_signed <= v1 <= Integers.Int.max_signed ->
    Integers.Int.min_signed <= v2 <= Integers.Int.max_signed ->
    Integers.Int.repr v1 = Integers.Int.repr v2 ->
    v1 = v2.
Proof.
  intros v1 v2 hinbound1 hinboun2.
  !intros.
  assert (h: Integers.Int.signed(Integers.Int.repr v1)
             = Integers.Int.signed(Integers.Int.repr v2)).
  { rewrite heq. reflexivity. }
  rewrite Integers.Int.signed_repr in h;auto.
  rewrite Integers.Int.signed_repr in h;auto.
Qed.

Lemma repr_inj_neq:
  forall v1 v2,
    Integers.Int.min_signed <= v1 <= Integers.Int.max_signed ->
    Integers.Int.min_signed <= v2 <= Integers.Int.max_signed ->
    v1 <> v2 -> 
    Integers.Int.repr v1 <> Integers.Int.repr v2.
Proof.
  intros v1 v2 hinbound1 hinboun2 hneq.
  intro abs.
  apply repr_inj in abs;auto.
Qed.

(* These should be part of std lib maybe.  *)

Lemma Zneq_bool_false: forall x y : Z, x = y -> Zneq_bool x y = false.
Proof.
  !intros.
  subst.
  unfold Zneq_bool.
  rewrite Fcore_Zaux.Zcompare_Eq;auto.
Qed.
  
Lemma Zneq_bool_true: forall x y : Z, x <> y -> Zneq_bool x y = true.
Proof.
  intros x y hneq.
  apply Z.lt_gt_cases in hneq.
  !destruct hneq.
  - unfold Zneq_bool.
    rewrite Fcore_Zaux.Zcompare_Lt;auto.
  - unfold Zneq_bool.
    rewrite Fcore_Zaux.Zcompare_Gt;auto.
Qed.

(* TODO: replace this y the real typing function *)
Definition type_of_name (stbl:symboltable) (nme:name): res type :=
  match nme with
    | E_Identifier astnum id => fetch_var_type id stbl
    | E_Indexed_Component astnum x0 x1 => Error (msg "type_of_name: arrays not treated yet")
    | E_Selected_Component astnum x0 x1 => Error (msg "transl_basetype: records not treated yet")
  end.




(** Hypothesis renaming stuff *)
Ltac rename_hyp1 h th :=
  match th with
    | fetch_var_type _ _ = Error _ => fresh "heq_fetch_var_type_ERR"
    | fetch_var_type _ _ = _ => fresh "heq_fetch_var_type"
    | fetch_exp_type _ _ = Error _ => fresh "heq_fetch_exp_type_ERR"
    | symboltable.fetch_exp_type _ _ = _ => fresh "heq_fetch_exp_type"
    | symboltable.fetch_exp_type _ _ = Error _ => fresh "heq_fetch_exp_type_ERR"
    | fetch_exp_type _ _ = _ => fresh "heq_fetch_exp_type" (* symboltable.fetch_exp_type *)
    | eval_expr _ _ _ (Run_Time_Error _) => fresh "h_eval_expr_RE"
    | eval_expr _ _ _ _ => fresh "h_eval_expr"
    | eval_name _ _ _ (Run_Time_Error _) => fresh "h_eval_name_RE"
    | eval_name _ _ _ _ => fresh "h_eval_name"
    | do_overflow_check _ (Run_Time_Error _) => fresh "h_overf_check_RE"
    | do_overflow_check _ _ => fresh "h_overf_check"
    | do_range_check _ _ _ (Run_Time_Error _) => fresh "h_do_range_check_RE"
    | do_range_check _ _ _ _ => fresh "h_do_range_check"
    | do_run_time_check_on_binop _ _ _ (Run_Time_Error _) => fresh "h_do_rtc_binop_RTE"
    | do_run_time_check_on_binop _ _ _ _ => fresh "h_do_rtc_binop"
    | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ None  => fresh "h_exec_stmt_None"
    | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ _  => fresh "h_exec_stmt"
    | Cminor.eval_constant _ _ _ = (Some _)  => fresh "h_eval_constant"
    | Cminor.eval_constant _ _ _ = None  => fresh "h_eval_constant_None"
    | eval_literal _ (Run_Time_Error _)  => fresh "h_eval_literal_RE"
    | eval_literal _ _  => fresh "h_eval_literal"
    | eval_stmt _ _ _ (Run_Time_Error _) => fresh "h_eval_stmt_RE"
    | eval_stmt _ _ _ _ => fresh "h_eval_stmt"
    | transl_stmt _ _ _ = Error _ => fresh "heq_transl_stmt_ERR"
    | transl_stmt _ _ _ = _ => fresh "heq_transl_stmt"
    | transl_name _ _ _ = Error _ => fresh "heq_transl_name_ERR"
    | transl_name _ _ _ = _ => fresh "heq_transl_name"
    | Cminor.eval_expr _ _ _ _ _ _ => fresh "h_CM_eval_expr"
    | transl_value _ = Error _ => fresh "heq_transl_value_RE"
    | transl_value _ = _ => fresh "heq_transl_value"
    | transl_variable _ _ _ _ = Error _ => fresh "heq_transl_variable_RE"
    | transl_variable _ _ _ _ = _ => fresh "heq_transl_variable"
    | fetch_exp_type _ _ = Some _ => fresh "heq_fetch_exp_type"
    | fetch_exp_type _ _ = None => fresh "heq_fetch_exp_type_none"
    | transl_type _ _ = Error _ => fresh "heq_transl_type_RE"
    | transl_type _ _ = _ => fresh "heq_transl_type"
    | transl_basetype _ _ = Error _ => fresh "heq_transl_basetype_RE"
    | transl_basetype _ _ = _ => fresh "heq_transl_basetype"
    | make_load _ _ = Error _ => fresh "heq_make_load_RE"
    | make_load _ _ = _ => fresh "heq_make_load"
    | STACK.fetchG _ _ = Some _ => fresh "heq_SfetchG"
    | STACK.fetchG _ _ = None => fresh "heq_SfetchG_none"
    | storeUpdate _ _ _ _ (Run_Time_Error _) => fresh "h_storeupdate_RTE"
    | storeUpdate _ _ _ _ _ => fresh "h_storeupdate"
    | do_run_time_check_on_binop _ _ _ (Run_Time_Error _) =>  fresh "h_do_rtc_binop_RE"
    | do_run_time_check_on_binop _ _ _ _ =>  fresh "h_do_rtc_binop"
    | do_run_time_check_on_unop _ _ (Run_Time_Error _) =>  fresh "h_do_rtc_unop_RE"
    | do_run_time_check_on_unop _ _ _ =>  fresh "h_do_rtc_unop"
    | reduce_type _ _ _ = Error _ => fresh "heq_reduce_type_RE"
    | reduce_type _ _ _ = _  => fresh "heq_reduce_type"
    | concrete_type_of_value _ = Error _ => fresh "concrete_type_of_value_RE"
    | concrete_type_of_value _ = _ => fresh "concrete_type_of_value"
    | in_bound _ _ _ => fresh "h_inbound"
    | do_division_check _ _ (Run_Time_Error _) => fresh "h_do_division_check_RTE"
    | do_division_check _ _ _ => fresh "h_do_division_check"
    (* TODO: remove when we remove type_of_name by the real one. *)
    | type_of_name _ _ = Error _ => fresh "heq_type_of_name_ERR"
    | type_of_name _ _ = _ => fresh "heq_type_of_name"
  end.

Ltac rename_hyp ::= rename_hyp1.

Lemma transl_literal_ok :
  forall g (l:literal) v,
    eval_literal l (Normal v) ->
    forall sp,
    exists v',
      transl_value v = OK v'
      /\ eval_constant g sp (transl_literal l) = Some v'.
Proof.
  !intros.
  !destruct l;simpl in *.
  - !inversion h_eval_literal.
    !inversion h_overf_check.
    simpl.
    eauto.
  - destruct b.
    + !inversion h_eval_literal.
      simpl.
      eauto.
    + !inversion h_eval_literal.
      simpl.
      eauto.
Qed.

Ltac remove_refl :=
  repeat
    match goal with
      | H: ?e = ?e |- _ => clear H
    end.

Ltac eq_same_clear :=
  repeat progress
    (repeat remove_refl;
     repeat match goal with
              | H: ?A = _ , H': ?A = _ |- _ => rewrite H in H'; !inversion H'
              | H: OK ?A = OK ?B |- _ => !inversion H
              | H: Some ?A = Some ?B |- _ => !inversion H
              | H: ?A <> ?A |- _ => elim H;reflexivity
            end).


Ltac inv_if_intop op h :=
   match op with
     | Plus => !invclear h
     | Minus => !invclear h
     | Multiply => !invclear h
     | Divide => !invclear h
   end.

(* Transform hypothesis of the form do_range_check into disequalities. *)
Ltac inv_rtc :=
  repeat
    progress
    (try match goal with
           | H: do_run_time_check_on_binop ?op _ (Bool _) (Normal _) |- _ => inv_if_intop op H
           | H: Math.binary_operation ?op _ (Bool _) = (Some _) |- _ => inv_if_intop op H
           | H: do_run_time_check_on_binop ?op (Bool _) _ (Normal _) |- _ => inv_if_intop op H
           | H: Math.binary_operation ?op (Bool _) _ = (Some _) |- _ => inv_if_intop op H
           | H: do_overflow_check _ (Normal (Int _)) |- _ => !invclear H
           | H: do_range_check _ _ _ (Normal (Int _)) |- _ => !invclear H
           | H: in_bound _ _ true |- _ => !invclear H
           | H:(_ >=? _) && (_ >=? _) = true |- _ =>
             rewrite andb_true_iff in H;
           try rewrite Z.geb_le in H;
           try rewrite Z.geb_le in H;
           let h1 := fresh "h_le"in
           let h2 := fresh "h_le"in
           destruct H as [h1 h2 ]
           | H:(_ <=? _) && (_ <=? _) = true |- _ =>
             rewrite andb_true_iff in H;
           try rewrite Z.leb_le in H;
           try rewrite Z.leb_le in H;
           let h1 := fresh "h_le"in
           let h2 := fresh "h_le"in
           destruct H as [h1 h2 ]
         end; auto 2).


(** In this section we prove that basic operators of SPARK behave,
    when they don't raise a runtime error, like Compcert ones. *)

Lemma not_ok: forall v1 v0 x,
                     transl_value v1 = OK x ->
                     Math.unary_not v1 = Some v0 ->
                     transl_value v0 = OK (Values.Val.notbool x).
Proof.
  !intros.
  !destruct v1;try discriminate;simpl in *.
  !invclear heq.
  destruct n;simpl
  ;inversion heq_transl_value
  ; subst.
  simpl.
  fold Integers.Int.mone.
  repeat apply f_equal.
  - rewrite Integers.Int.eq_false.
    + reflexivity.
    + apply Integers.Int.one_not_zero.
  - simpl.
    rewrite Integers.Int.eq_true.
    reflexivity.
Qed.


Lemma and_ok: forall v1 v2 v0 x x0,
                     transl_value v1 = OK x ->
                     transl_value v2 = OK x0 ->
                     Math.and v1 v2 = Some v0 ->
                     transl_value v0 = OK (Values.Val.and x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  destruct n;destruct n0;simpl
  ;inversion heq_transl_value
  ;inversion heq_transl_value0
  ; reflexivity.
Qed.

Lemma or_ok: forall v1 v2 v0 x x0,
                     transl_value v1 = OK x ->
                     transl_value v2 = OK x0 ->
                     Math.or v1 v2 = Some v0 ->
                     transl_value v0 = OK (Values.Val.or x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  destruct n;destruct n0;simpl
  ;inversion heq_transl_value
  ;inversion heq_transl_value0
  ; reflexivity.
Qed.


Definition check_overflow_value (v:value) :=
  match v with
    | Undefined => True
    | Int n => do_overflow_check n (Normal (Int n))
    | Bool n => True
    | ArrayV a => True(* FIXME *)
    | RecordV r => True (* FIXME *)
  end.

Ltac rename_hyp2 h th :=
  match th with
    | check_overflow_value _ => fresh "h_check_overf"
    | _ => rename_hyp1 h th
  end.

Ltac rename_hyp ::= rename_hyp2.


Lemma eq_ok: forall v1 v2 v0 x x0,
               check_overflow_value v1 -> 
               check_overflow_value v2 -> 
               transl_value v1 = OK x ->
               transl_value v2 = OK x0 ->
               Math.eq v1 v2 = Some v0 ->
               transl_value v0 = OK (Values.Val.cmp Integers.Ceq x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  !destruct (Z.eq_dec n n0).
  - subst.
    rewrite Fcore_Zaux.Zeq_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    rewrite Integers.Int.eq_true.
    reflexivity.
  - rewrite Fcore_Zaux.Zeq_bool_false;auto.
    unfold Values.Val.cmp.
    simpl.
    rewrite Integers.Int.eq_false.
    + reflexivity.
    + apply repr_inj_neq.
      * inv_rtc.
      * inv_rtc.
      * assumption.
Qed.


Lemma neq_ok: forall v1 v2 v0 x x0,
               check_overflow_value v1 -> 
               check_overflow_value v2 -> 
               transl_value v1 = OK x ->
               transl_value v2 = OK x0 ->
               Math.ne v1 v2 = Some v0 ->
               transl_value v0 = OK (Values.Val.cmp Integers.Cne x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  !destruct (Z.eq_dec n n0).
  - subst.
    rewrite Zneq_bool_false;auto.
    unfold Values.Val.cmp.
    simpl.
    rewrite Integers.Int.eq_true.
    reflexivity.
  - rewrite Zneq_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    rewrite Integers.Int.eq_false.
    + reflexivity.
    + apply repr_inj_neq.
      * inv_rtc.
      * inv_rtc.
      * assumption.
Qed.

Lemma le_ok: forall v1 v2 v0 x x0,
               check_overflow_value v1 -> 
               check_overflow_value v2 -> 
               transl_value v1 = OK x ->
               transl_value v2 = OK x0 ->
               Math.le v1 v2 = Some v0 ->
               transl_value v0 = OK (Values.Val.cmp Integers.Cle x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  !destruct (Z.le_decidable n n0).
  - rewrite Fcore_Zaux.Zle_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_false.
    + reflexivity.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
      auto with zarith.
  - { rewrite Fcore_Zaux.Zle_bool_false.
      - unfold Values.Val.cmp.
        simpl.
        unfold Integers.Int.lt.
        rewrite Coqlib.zlt_true.
        + reflexivity.
        + rewrite Integers.Int.signed_repr;inv_rtc.
          rewrite Integers.Int.signed_repr;inv_rtc.
          auto with zarith.
      - apply Z.nle_gt.
        assumption. }
Qed.


Lemma ge_ok: forall v1 v2 v0 x x0,
               check_overflow_value v1 -> 
               check_overflow_value v2 -> 
               transl_value v1 = OK x ->
               transl_value v2 = OK x0 ->
               Math.ge v1 v2 = Some v0 ->
               transl_value v0 = OK (Values.Val.cmp Integers.Cge x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  rewrite Z.geb_leb.
  !destruct (Z.le_decidable n0 n).
  - rewrite Fcore_Zaux.Zle_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_false.
    + reflexivity.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
      auto with zarith.
  - { rewrite Fcore_Zaux.Zle_bool_false.
      - unfold Values.Val.cmp.
        simpl.
        unfold Integers.Int.lt.
        rewrite Coqlib.zlt_true.
        + reflexivity.
        + rewrite Integers.Int.signed_repr;inv_rtc.
          rewrite Integers.Int.signed_repr;inv_rtc.
          auto with zarith.
      - apply Z.nle_gt.
        assumption. }
Qed.

Lemma lt_ok: forall v1 v2 v0 x x0,
               check_overflow_value v1 -> 
               check_overflow_value v2 -> 
               transl_value v1 = OK x ->
               transl_value v2 = OK x0 ->
               Math.lt v1 v2 = Some v0 ->
               transl_value v0 = OK (Values.Val.cmp Integers.Clt x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  simpl.
  !destruct (Z.lt_decidable n n0).
  - rewrite Fcore_Zaux.Zlt_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_true.
    + reflexivity.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
  - { rewrite Fcore_Zaux.Zlt_bool_false.
      - unfold Values.Val.cmp.
        simpl.
        unfold Integers.Int.lt.
        rewrite Coqlib.zlt_false.
        + reflexivity.
        + rewrite Integers.Int.signed_repr;inv_rtc.
          rewrite Integers.Int.signed_repr;inv_rtc.
      - auto with zarith. }
Qed.


Lemma gt_ok: forall v1 v2 v0 x x0,
               check_overflow_value v1 -> 
               check_overflow_value v2 -> 
               transl_value v1 = OK x ->
               transl_value v2 = OK x0 ->
               Math.gt v1 v2 = Some v0 ->
               transl_value v0 = OK (Values.Val.cmp Integers.Cgt x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  rewrite Z.gtb_ltb.
  !destruct (Z.lt_decidable n0 n).
  - rewrite Fcore_Zaux.Zlt_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_true.
    + reflexivity.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
  - { rewrite Fcore_Zaux.Zlt_bool_false.
      - unfold Values.Val.cmp.
        simpl.
        unfold Integers.Int.lt.
        rewrite Coqlib.zlt_false.
        + reflexivity.
        + rewrite Integers.Int.signed_repr;inv_rtc.
          rewrite Integers.Int.signed_repr;inv_rtc.
      - auto with zarith. }
Qed.


(* strangely this one does not need overflow preconditions *)
Lemma unaryneg_ok :
  forall n v1 v,
    transl_value v1 = OK n ->
    Math.unary_operation Unary_Minus v1 = Some v ->
    transl_value v = OK (Values.Val.negint n).
Proof.
  !intros.
  simpl in *.
  destruct v1;simpl in *;try discriminate.
  eq_same_clear.
  simpl.
  rewrite Integers.Int.neg_repr.
  reflexivity.
Qed.

Lemma do_run_time_check_on_binop_ok: forall v1 v2 v op,
             do_run_time_check_on_binop op v1 v2 (Normal v) ->
             Math.binary_operation op v1 v2 = Some v.
Proof.
  intros v1 v2 v op hdo_rtc.
  !invclear hdo_rtc.
  - !invclear h_overf_check.
    assumption.
  - !invclear h_do_division_check;simpl in *.
    !invclear h_overf_check.
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
    rewrite !Integers.Int.signed_repr).

Lemma add_ok :
  forall v v1 v2 n1 n2,
    check_overflow_value v1 -> 
    check_overflow_value v2 -> 
    do_run_time_check_on_binop Plus v1 v2 (Normal v) ->
    transl_value v1 = OK n1 ->
    transl_value v2 = OK n2 ->
    transl_value v = OK (Values.Val.add n1 n2).
Proof.
  !intros.
  simpl in *.
  !destruct v1;simpl in *;try discriminate;eq_same_clear; try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear; try now inv_rtc.
  - !invclear h_do_rtc_binop;simpl in *; eq_same_clear. 
    !invclear h_overf_check.
    int_simpl;auto;inv_rtc;auto 2.
Qed.

Lemma sub_ok :
  forall v v1 v2 n1 n2,
    check_overflow_value v1 -> 
    check_overflow_value v2 -> 
    do_run_time_check_on_binop Minus v1 v2 (Normal v) ->
    transl_value v1 = OK n1 ->
    transl_value v2 = OK n2 ->
    transl_value v = OK (Values.Val.sub n1 n2).
Proof.
  !intros.
  simpl in *.
  !destruct v1;simpl in *;try discriminate;eq_same_clear; try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear; try now inv_rtc.
  - !invclear h_do_rtc_binop;simpl in *; eq_same_clear. 
    !invclear h_overf_check.
    int_simpl;auto;inv_rtc;auto 2.
Qed.

Lemma mult_ok :
  forall v v1 v2 n1 n2,
    check_overflow_value v1 -> 
    check_overflow_value v2 -> 
    do_run_time_check_on_binop Multiply v1 v2 (Normal v) ->
    transl_value v1 = OK n1 ->
    transl_value v2 = OK n2 ->
    transl_value v = OK (Values.Val.mul n1 n2).
Proof.
  !intros.
  simpl in *.
  !destruct v1;simpl in *;try discriminate;eq_same_clear; try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear; try now inv_rtc.
  - !invclear h_do_rtc_binop;simpl in *; eq_same_clear. 
    !invclear h_overf_check.
    int_simpl;auto;inv_rtc;auto 2.
Qed.

(** Compcert division return None if dividend is min_int and divisor
    in -1, because the result would be max_int +1. In Spark's
    semantics the division is performed but then it fails overflow
    checks. *)
(*  How to compile this? probably by performing a check before. *)
Lemma div_ok :
  forall v v1 v2 n n1 n2,
    check_overflow_value v1 -> 
    check_overflow_value v2 -> 
    do_run_time_check_on_binop Divide v1 v2 (Normal v) ->
    transl_value v1 = OK n1 ->
    transl_value v2 = OK n2 ->
    transl_value v = OK n ->
    Values.Val.divs n1 n2 = Some n.
Proof.
  !intros.
  simpl in *.
  !destruct v1;simpl in *;try discriminate;try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;try now inv_rtc.
  rename n0 into v1.
  rename n3 into v2.
  eq_same_clear;simpl in *.
  !invclear h_do_rtc_binop;simpl in *; eq_same_clear.
  { decompose [or] H;discriminate. }
  inv_rtc.
  rewrite min_signed_ok, max_signed_ok in *.
  !inversion h_do_division_check.
  apply Zeq_bool_neq in heq_Z_false.
  rewrite Integers.Int.eq_false;auto.
  - simpl.
    (* the case where division overflows is dealt with by the overflow
       check in spark semantic. Ths division is performed on Z and
       then overflow is checked and may fails. *)
    destruct (Integers.Int.eq (Integers.Int.repr v1)
                              (Integers.Int.repr Integers.Int.min_signed) &&
                              Integers.Int.eq (Integers.Int.repr v2) Integers.Int.mone)
             eqn:h_divoverf.
    + apply andb_true_iff in h_divoverf.
      destruct h_divoverf as [h_divoverf1 h_divoverf2].
      exfalso.
      assert (v1_is_min_int: v1 = Integers.Int.min_signed).
      { 
        rewrite Integers.Int.eq_signed in h_divoverf1.
        unfold Coqlib.zeq in h_divoverf1;auto.
        rewrite !Integers.Int.signed_repr in h_divoverf1;try (split;omega).
        destruct (Z.eq_dec v1 Integers.Int.min_signed);try discriminate.
        assumption. }
      assert (v2_is_min_int: v2 = -1).
      { rewrite Integers.Int.eq_signed in h_divoverf2.
        unfold Coqlib.zeq in h_divoverf2;auto.
        rewrite !Integers.Int.signed_repr in h_divoverf2;try (split;omega).
        destruct (Z.eq_dec v2 (Integers.Int.signed Integers.Int.mone));try discriminate.
        assumption. }
      subst.
      vm_compute in heq.
      inversion heq.
      subst.
      inversion h_overf_check;subst.
      inv_rtc.      
    + unfold Integers.Int.divs.
      rewrite !Integers.Int.signed_repr;auto 2.
      simpl in *.
      !invclear heq;subst.
      inversion h_overf_check;subst.
      simpl in *.
      inversion heq_transl_value.
      reflexivity.
  - unfold Integers.Int.zero.
    intro abs.
    apply heq_Z_false.
    rewrite <- (Integers.Int.signed_repr v2).
    + rewrite abs.
      rewrite (Integers.Int.signed_repr 0);auto.
      split; intro;discriminate.      
    + split;auto.
Qed.



Lemma binary_operator_ok:
  forall op (n n1 n2 : Values.val) (v v1 v2 : value),
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop op v1 v2 (Normal v) ->
    transl_value v1 = OK n1 ->
    transl_value v2 = OK n2 ->
    transl_value v = OK n ->
    forall m, Cminor.eval_binop (transl_binop op) n1 n2 m = Some n.
Proof.
  !intros.
  assert (h_rtc:=do_run_time_check_on_binop_ok _ _ _ _ h_do_rtc_binop).
  destruct op.
  - erewrite (and_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (or_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (eq_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (neq_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (lt_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (le_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (gt_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (ge_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (add_ok v v1 v2 n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (sub_ok v v1 v2 n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - erewrite (mult_ok v v1 v2 n1 n2) in heq_transl_value;eq_same_clear;eauto.
  - simpl in *. erewrite (div_ok v v1 v2 n n1 n2);eauto.
Qed.




(** [safe_stack s] means that every value in s is correct wrt to
    overflows.
    TODO: extend with other values than Int: floats, arrays, records. *)
Definition safe_stack s :=
  forall id n,
    STACK.fetchG id s = Some (Int n)
    -> do_overflow_check n (Normal (Int n)).


(** Hypothesis renaming stuff *)
Ltac rename_hyp2' h th :=
  match th with
    | safe_stack _ => fresh "h_safe_stack"
    | _ => rename_hyp2 h th
  end.

Ltac rename_hyp ::= rename_hyp2'.

Lemma eval_literal_overf :
  forall (l:literal) n, 
    eval_literal l (Normal (Int n)) ->
    do_overflow_check n (Normal (Int n)).
Proof.
  !intros.
  !inversion h_eval_literal.
  !inversion h_overf_check.
  assumption.
Qed.


Lemma eval_name_overf : forall s st nme n,
                          safe_stack s
                          -> eval_name st s nme (Normal (Int n))
                          -> do_overflow_check n (Normal (Int n)).
Proof.
  !intros.
  !inversion h_eval_name. (* l'environnement retourne toujours des valeur rangées. *)
  - unfold safe_stack in *.
    eapply h_safe_stack;eauto.
  - admit. (* Arrays *)
  - admit. (* records *)
Qed.

(** on a safe stack, any expression that evaluates into a value,
    evaluates to a not overflowing value, except if it is a unary_plus
    (in which case no check is made). *)
Lemma eval_expr_overf :
  forall st s, safe_stack s ->
            forall (e:expression) n, 
              eval_expr st s e (Normal (Int n)) ->
              do_overflow_check n (Normal (Int n)).
Proof.
  !intros.
  revert h_safe_stack.
  remember (Normal (Int n)) as hN.
  revert HeqhN.
  !induction h_eval_expr;!intros;subst;try discriminate.
  - eapply eval_literal_overf;eauto.
  - eapply eval_name_overf;eauto.
  - !invclear h_do_rtc_binop.
    + inversion h_overf_check;subst;auto.
    + inversion h_overf_check;subst;auto.
    + rewrite binopexp_ok in *.
      functional inversion heq;subst;try match goal with H: ?A <> ?A |- _ => elim H;auto end.
  - !invclear h_do_rtc_unop.
    + inversion h_overf_check;subst;auto.
    + rewrite unopexp_ok in *.
      !functional inversion heq;subst;try match goal with H: ?A <> ?A |- _ => elim H;auto end.
      !invclear heq3.
      apply IHh_eval_expr;auto.
Qed.

Lemma eval_expr_overf2 :
  forall st s, safe_stack s ->
               forall (e:expression) x,
                 eval_expr st s e (Normal x) -> check_overflow_value x.
Proof.
  !intros.
  destruct x;simpl in *;auto.
  eapply eval_expr_overf;eauto.
Qed.
  

(* TRYING A NEW VERSION *)


Inductive follow_chaining: Values.val -> Memory.Mem.mem -> nat -> Values.val -> Prop :=
  FC1: forall sp m, follow_chaining sp m 0 sp
| FC2: forall vsp m lvl vsp' v,
        Memory.Mem.loadv AST.Mint32 m vsp = Some vsp'
        -> follow_chaining vsp' m lvl v
        -> follow_chaining vsp m (S lvl) v.

(** [eq_frame sto b ofs m] means that the memory m contains a block
    at address b, and this block from offset [ofs] matches the spark
    frame [sto]. *)
(* FIXME: are we looking at the stack in the wrong direction? *)
Inductive eq_frame:
  STACK.store -> Values.block -> Integers.Int.int -> Memory.Mem.mem -> Prop :=
  MF1: forall spb ofs m, eq_frame nil spb ofs m
| MF2: forall fr spb ofs m id vid vid',
         transl_value vid = OK vid'
         -> Memory.Mem.load AST.Mint32 m spb ofs = Some vid'
         -> eq_frame fr spb (Integers.Int.add (Integers.Int.repr ofs)
                                               (Integers.Int.repr 4)) m
         -> eq_frame ((id,vid)::fr) spb (Integers.Int.repr ofs) m.

(** [match_env sta b m] means that the chained Cminor stack at address
    [b] in memory m ([b] is the adress of the bottom of the top stack)
    matches spark stack [s]. *)
Inductive eq_env: STACK.stack -> Values.block -> Memory.Mem.mem -> Prop :=
  ME1: forall spb m, eq_env nil spb m
| ME2: forall s sto (lvl:STACK.scope_level) fr spb spb' m,
         eq_frame fr spb (Integers.Int.repr 4) m
         -> eq_env s spb' m
         -> eq_env ((lvl,sto)::s) spb m.









(* See CminorgenProof.v@205. *)
(* We will need more than that probably. But for now let us use
   a simple notion of matching: the value of a variable is equal to
   the value of its translation. Its translation is currently (an
   expression of the form ELoad((Eload(Eload ...(Eload(0)))) + n)). We
   could define a specialization of eval_expr for this kind of
   expression but at some point the form of the expression will
   complexify (some variables may stay temporary instead of going in
   the stack, etc).

   We also put well-typing constraints on the stack wrt symbol
   table. *)
Record match_env (*st:symboltable*) (s: semantics.STACK.stack)
       (*CE:compilenv*) (spb:Values.block) (ofs:Integers.Int.int)
       (*locenv: Cminor.env*) (*g:genv*)(m:Memory.Mem.mem): Prop :=
  mk_match_env {
      me_eq_stack: eq_env s spb m;
(*       me_eq_locenv: local variable never change in our semantic anyway; *)
      me_overflow: safe_stack s }.



Axiom
      me_transl:
        forall st s CE spb ofs locenv g m,
        forall nme v addrof_nme load_addrof_nme typ_nme cm_typ_nme v',
          eval_name st s nme (Normal v) ->
          type_of_name st nme = OK typ_nme ->
          transl_name st CE nme = OK addrof_nme ->
          transl_type st typ_nme = OK cm_typ_nme ->
          make_load addrof_nme cm_typ_nme = OK load_addrof_nme ->
          transl_value v = OK v' ->
          Cminor.eval_expr g (Values.Vptr spb ofs) locenv m load_addrof_nme v'.



(** Hypothesis renaming stuff *)
Ltac rename_hyp3 h th :=
  match th with
    | match_env _ _ _ _ => fresh "h_match_env"
    | _ => rename_hyp2 h th
  end.

Ltac rename_hyp ::= rename_hyp3.



Lemma transl_name_ok :
  forall stbl (s:STACK.stack) (nme:name) (v:value),
    eval_name stbl s nme (Normal v) ->
    forall CE locenv g m  (e' e'':Cminor.expr)
           typeof_nme typeof_nme' spb ofs v',
      type_of_name stbl nme = OK typeof_nme ->
      transl_type stbl typeof_nme = OK typeof_nme' ->
      transl_name stbl CE nme = OK e' ->
      match_env s spb ofs m ->
      make_load e' typeof_nme' = OK e'' ->
      transl_value v = OK v' ->
      Cminor.eval_expr g (Values.Vptr spb ofs) locenv m e'' v'.
Proof.
  intros until v.
  intro h_eval_name.
  remember (Normal v) as Nv.
  revert HeqNv.
  !induction h_eval_name;simpl;!intros; subst;try discriminate.
  !invclear heq.
  !destruct h_match_env.
  rename x into i.
  rename v into val_i.
  specialize (me_transl st s CE spb ofs locenv g m (E_Identifier ast_num i) val_i e' e''
                        typeof_nme typeof_nme' v').
  intro h_me_transl.
  !! (fun _ => assert (eval_name st s (E_Identifier ast_num i) (Normal val_i))) g.
  { constructor.
    assumption. }
  specialize (h_me_transl h_eval_name heq_fetch_var_type heq_transl_variable
                         heq_transl_type heq_make_load heq_transl_value).
  repeat split;auto.
Qed.

Ltac rename_hyp4 h th :=
  match reverse goal with
    | H: fetch_var_type ?X _ = OK h |- _  => (fresh "type_" X)
    | H: id (fetch_var_type ?X _ = OK h) |- _ => (fresh "type_" X)
    | H: (value_at_addr _ _ ?X = OK h) |- _ => fresh "val_at_" X
    | H: id (value_at_addr _ _ ?X = OK h) |- _ => fresh "val_at_" X
    | H: transl_variable _ _ _ ?X = OK h |- _ => fresh X "'"
    | H: id (transl_variable _ _ _ ?X = OK h) |- _ => fresh X "'"
    | H: transl_value ?X = OK h |- _ => fresh X "'"
    | H: id (transl_value ?X = OK h) |- _ => fresh X "'"
    | _ => rename_hyp3 h th
  end.
Ltac rename_hyp ::= rename_hyp4.

Lemma transl_expr_ok :
  forall stbl CE (e:expression) (e':Cminor.expr),
    transl_expr stbl CE e = OK e' ->
    forall locenv g m (s:STACK.stack)  (v:value)
         (spb: Values.block) (ofs:Integers.Int.int),
    eval_expr stbl s e (Normal v) ->
    match_env s spb ofs m ->
    forall v',
    transl_value v = OK v' ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m e' v'.
Proof.
  intros until e.
  !functional induction (transl_expr stbl CE e);try discriminate;simpl; !intros;
  !invclear h_eval_expr;eq_same_clear.
  - destruct (transl_literal_ok g lit v h_eval_literal (Values.Vptr spb ofs)) as [vv h_and].
    !destruct h_and;eq_same_clear.
    constructor.
    assumption.
  - rename v'0 into v'.
    unfold value_at_addr in heq.
    destruct (transl_type stbl type_id) eqn:heq_transl_type;simpl in *.
    + eapply transl_name_ok;simpl; eauto.
    + discriminate.
  - specialize (IHr x heq0 locenv g m s v1 spb ofs).
    specialize (IHr0 x0 heq locenv g m s v2 spb ofs).
    destruct (transl_value v1) as [v1' | errormsg] eqn:heq_transl_value_v1.
    destruct (transl_value v2) as [v2' | errormsg] eqn:heq_transl_value_v2.
    + apply eval_Ebinop with v1' v2';auto.
      eapply binary_operator_ok;eauto.
      * eapply eval_expr_overf2;eauto.
        eapply h_match_env.(me_overflow s spb ofs m).
      * eapply eval_expr_overf2;eauto.
        eapply h_match_env.(me_overflow s spb ofs m).
    + functional inversion heq_transl_value_v2;subst.
      * admit. (* Arrays *)
      * admit. (* Records *)
      * admit. (* Undefined *)
    + functional inversion heq_transl_value_v1;subst.
      * admit. (* Arrays *)
      * admit. (* Records *)
      * admit. (* Undefined *)

  (* Unary minus *)
  - simpl in heq.
    eq_same_clear.
    rename x into e'.
    rename e0 into e.
    destruct (transl_value v0) eqn:heq_transl_value_v
    ; try discriminate;eq_same_clear;simpl in *.
    specialize (IHr e' heq0 locenv g m s v0 spb ofs
                    h_eval_expr h_match_env v1 heq_transl_value_v).
    + apply eval_Eunop with (v1:=v1);auto.
      simpl.
      assert (h:=unaryneg_ok v1 v0 v heq_transl_value_v).
      rewrite h in heq_transl_value.
      * eq_same_clear.
        reflexivity.
      * simpl in *.
        { !invclear h_do_rtc_unop; simpl in *.
          - !invclear h_overf_check;subst;simpl in *; try eq_same_clear.
            assumption.
          - assumption. }
    + functional inversion heq_transl_value_v;subst.
      * inversion h_do_rtc_unop;subst; simpl in *;try discriminate.
      * inversion h_do_rtc_unop;subst; simpl in *;try discriminate.
      * inversion h_do_rtc_unop;subst; simpl in *;try discriminate.
  (* Not *)
  - !invclear h_do_rtc_unop;simpl in *;try eq_same_clear.
    clear hneq.
    destruct v0;simpl in *;try discriminate;eq_same_clear;simpl in *.
    destruct n;simpl in *; eq_same_clear.
    * { econstructor;simpl in *;eauto.
        * eapply IHr ;eauto.
          simpl.
          eauto.
        * constructor.
          simpl.
          eauto.
        * vm_compute.
          reflexivity. }
    * { econstructor;simpl in *;eauto.
        * eapply IHr ;eauto.
          simpl.
          eauto.
        * constructor.
          simpl.
          eauto.
        * vm_compute.
          reflexivity. }
Qed.
(** Hypothesis renaming stuff *)
Ltac rename_hyp5 th :=
  match th with
    | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ None  => fresh "h_exec_stmt_None"
    | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ _  => fresh "h_exec_stmt"
    | _ => rename_hyp4 th
  end.

Ltac rename_hyp ::= rename_hyp5.

      
Require Import Utf8.
Set Printing Width 100.

Axiom det_eval_expr: forall g spb ofs locenv m e v v',
                       Cminor.eval_expr g (Values.Vptr spb ofs) locenv m e v
                       -> Cminor.eval_expr g (Values.Vptr spb ofs) locenv m e v'
                       -> v = v'.
Lemma transl_stmt_ok :
  forall stbl CE  (stm:statement) (stm':Cminor.stmt),
    transl_stmt stbl CE stm = (OK stm') ->
    forall locenv g m (s:STACK.stack)
           (s':STACK.stack) spb ofs f,
      match_env s spb ofs m ->
      eval_stmt stbl s stm (Normal s') ->
      forall tr locenv' m' o,
        Cminor.exec_stmt g f (Values.Vptr spb ofs) locenv m stm' tr locenv' m' o
        ->  match_env s' spb ofs m'.
Proof.
  intros until stm.
  !functional induction (transl_stmt stbl CE stm)
  ;simpl;!intros;eq_same_clear;subst;simpl in *;try discriminate.
  (* skip *)
  - !invclear h_eval_stmt.
    !invclear h_exec_stmt.
    assumption.
    (* assignment *)
  - xxx
    (* Env is only modified at one place (non aliasing?), therefore
       match_env is true if the new value is added at corresponding
       places. And that should be true. *)
    specialize (transl_name_ok stbl s nme).
    intro h.
    !invclear h_exec_stmt.
    !invclear h_eval_stmt.
    + specialize (h ).
    

admit.
admit.






    (* if then else *)
  - specialize (IHr _ heq_transl_stmt0 locenv g m s s' spb ofs f h_match_env).
    specialize (IHr0 _ heq_transl_stmt locenv g m s s' spb ofs f h_match_env).
    !invclear h_eval_stmt;subst;simpl.
    + generalize h_eval_expr.
      intro h_cm_eval_expr.
      eapply transl_expr_ok
      with (locenv:=locenv) (g:=g) (v' := (Values.Vint (Integers.Int.repr 1)))
        in h_cm_eval_expr;eauto.
      apply IHr with (locenv':=locenv') (o:=o) (tr:=tr);auto.
      !invclear h_exec_stmt.
      !inversion h_CM_eval_expr.
      rewrite (det_eval_expr _ _ _ _ _ _ _ _ h_CM_eval_expr1 h_cm_eval_expr) in *.
      !invclear h_CM_eval_expr0.
      simpl in h_eval_constant.
      eq_same_clear.
      simpl in heq0.
      eq_same_clear;simpl in *.
      inversion H11;simpl in *.
      vm_compute in H0, H1.
      subst.
      assumption.
    + generalize h_eval_expr.
      intro h_cm_eval_expr.
      eapply transl_expr_ok
      with (locenv:=locenv) (g:=g) (v' := (Values.Vint (Integers.Int.repr 0)))
        in h_cm_eval_expr;eauto.
      apply IHr0 with (locenv':=locenv') (o:=o) (tr:=tr);auto.
      !invclear h_exec_stmt.
      !inversion h_CM_eval_expr.
      rewrite (det_eval_expr _ _ _ _ _ _ _ _ h_CM_eval_expr1 h_cm_eval_expr) in *.
      !invclear h_CM_eval_expr0.
      simpl in h_eval_constant.
      eq_same_clear.
      simpl in heq0.
      eq_same_clear;simpl in *.
      inversion H11;simpl in *.
      vm_compute in H0, H1.
      subst.
      assumption.
      (* Procedure call *)
  - admit.
    (* sequence *)
  - !inversion h_eval_stmt.
    !inversion h_exec_stmt.
    + specialize (IHr _ heq_transl_stmt0 _ _ _ _ _ _ _ _
                      h_match_env h_eval_stmt1 _ _ _ _ h_exec_stmt1).
      specialize (IHr0 _ heq_transl_stmt _ _ _ _ _ _ _ _
                       IHr h_eval_stmt0 _ _ _ _ h_exec_stmt0).
      assumption.
    + admit. (* hypothesis are too weakcurrently for this one: we
      should consider executions with errors, or prove that if no
      error occur i spark then no error occur in Cminor, which what we
      want ultimately. *)
Qed.

