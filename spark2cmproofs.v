
Require Import function_utils.
Require Import LibHypsNaming.
Require Import Errors.
Require Import spark2Cminor.
Require Import Cminor.
Require Ctypes.
Require Import symboltable.
Require Import semantics.
Require Import semantics_properties.
Require Import Sorted.
Require Import Relations.

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

(* All element of a sorted list are smaller or equal to the first
   element. If the ordering is reflexive. *)
Lemma increasing_order_In A :
  forall (ord:A -> A -> Prop) (stk:list A) (hd:A),
    StronglySorted ord (hd::stk) ->
    Forall (fun elt => elt = hd \/ ord hd elt) (hd::stk).
Proof.
  !intros.
  !inversion H.
  constructor 2.
  - left;reflexivity.
  - apply Forall_forall.
    !intros.
    right.
    rewrite Forall_forall in H3.
    auto.
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
    | ?min <= ?x and ?x < ?max => fresh "h_" x "_bounded_" min "_" max 
    | ?min <= ?x and ?x < ?max => fresh "h_" x "_bounded_"
    | ?min <= ?x and ?x < ?max => fresh "h_bounded"

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

    | CompilEnv.fetchG ?id ?CE = _ => fresh "heq_CEfetchG_" id "_" CE
    | CompilEnv.fetchG ?id _ = _ => fresh "heq_CEfetchG_" id
    | CompilEnv.fetchG _ _ = Some _ => fresh "heq_CEfetchG"
    | CompilEnv.fetchG _ _ = None => fresh "heq_CMfetchG_none"

    | CompilEnv.fetch ?id ?CE = _ => fresh "heq_CEfetch_" id "_" CE
    | CompilEnv.fetch ?id _ = _ => fresh "heq_CEfetch_" id
    | CompilEnv.fetch _ _ = Some _ => fresh "heq_CEfetch"
    | CompilEnv.fetch _ _ = None => fresh "heq_CMfetch_none"

    | CompilEnv.frameG ?id ?CE = _ => fresh "heq_CEframeG_" id "_" CE
    | CompilEnv.frameG ?id _ = _ => fresh "heq_CEframeG_" id
    | CompilEnv.frameG _ _ = Some _ => fresh "heq_CEframeG"
    | CompilEnv.frameG _ _ = None => fresh "heq_CMframeG_none"

    | CompilEnv.level_of_top ?ce = None => fresh "heq_lvloftop_none_" ce
    | CompilEnv.level_of_top ?ce = None => fresh "heq_lvloftop_none"
    | CompilEnv.level_of_top ?ce = Some ?s => fresh "heq_lvloftop_" ce "_" s
    | CompilEnv.level_of_top ?ce = ?s => fresh "heq_lvloftop_" ce "_" s
    | CompilEnv.level_of_top ?ce = _ => fresh "heq_lvloftop_" ce
    | CompilEnv.level_of_top _ = Some ?s => fresh "heq_lvloftop_" s
    | CompilEnv.level_of_top _ = _ => fresh "heq_lvloftop"
                                       
    (* TODO: remove when we remove type_of_name by the real one. *)
    | type_of_name _ _ = Error _ => fresh "heq_type_of_name_ERR"
    | type_of_name _ _ = _ => fresh "heq_type_of_name"
  end.

Ltac rename_hyp ::= rename_hyp1.

Lemma transl_literal_ok :
  forall g (l:literal) v,
    eval_literal l (Normal v) ->
    forall sp,
      eval_constant g sp (transl_literal l) = Some (transl_value v).
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
           | H: do_run_time_check_on_binop ?op Undefined _ (Normal _) |- _ => now inversion H
           | H: do_run_time_check_on_binop ?op _ Undefined (Normal _) |- _ => now inversion H
           | H: do_run_time_check_on_binop ?op _ (ArrayV _) (Normal _) |- _ => now inv_if_intop op H
           | H: do_run_time_check_on_binop ?op (ArrayV _) _ (Normal _) |- _ => now inv_if_intop op H
           | H: do_run_time_check_on_binop ?op _ (RecordV _) (Normal _) |- _ => now inv_if_intop op H
           | H: do_run_time_check_on_binop ?op (RecordV _) _ (Normal _) |- _ => now inv_if_intop op H
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
                     transl_value v1 = x ->
                     Math.unary_not v1 = Some v0 ->
                     transl_value v0 = (Values.Val.notbool x).
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
                     transl_value v1 = x ->
                     transl_value v2 = x0 ->
                     Math.and v1 v2 = Some v0 ->
                     transl_value v0 = (Values.Val.and x x0).
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
                     transl_value v1 = x ->
                     transl_value v2 = x0 ->
                     Math.or v1 v2 = Some v0 ->
                     transl_value v0 = (Values.Val.or x x0).
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
               transl_value v1 = x ->
               transl_value v2 = x0 ->
               Math.eq v1 v2 = Some v0 ->
               transl_value v0 = (Values.Val.cmp Integers.Ceq x x0).
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
    subst.
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
               transl_value v1 = x ->
               transl_value v2 = x0 ->
               Math.ne v1 v2 = Some v0 ->
               transl_value v0 = (Values.Val.cmp Integers.Cne x x0).
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
    subst.
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
               transl_value v1 = x ->
               transl_value v2 = x0 ->
               Math.le v1 v2 = Some v0 ->
               transl_value v0 = (Values.Val.cmp Integers.Cle x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  !destruct (Z.le_decidable n n0).
  - rewrite Fcore_Zaux.Zle_bool_true;auto.
    unfold Values.Val.cmp.
    subst.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_false.
    + reflexivity.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
      auto with zarith.
  - { rewrite Fcore_Zaux.Zle_bool_false.
      - unfold Values.Val.cmp.
        subst.
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
               transl_value v1 = x ->
               transl_value v2 = x0 ->
               Math.ge v1 v2 = Some v0 ->
               transl_value v0 = (Values.Val.cmp Integers.Cge x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  rewrite Z.geb_leb.
  !destruct (Z.le_decidable n0 n).
  - rewrite Fcore_Zaux.Zle_bool_true;auto.
    unfold Values.Val.cmp.
    subst.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_false.
    + reflexivity.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
      auto with zarith.
  - { rewrite Fcore_Zaux.Zle_bool_false.
      - unfold Values.Val.cmp.
        subst.
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
               transl_value v1 = x ->
               transl_value v2 = x0 ->
               Math.lt v1 v2 = Some v0 ->
               transl_value v0 = (Values.Val.cmp Integers.Clt x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  simpl.
  !destruct (Z.lt_decidable n n0).
  - rewrite Fcore_Zaux.Zlt_bool_true;auto.
    unfold Values.Val.cmp.
    subst.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_true.
    + reflexivity.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
  - { rewrite Fcore_Zaux.Zlt_bool_false.
      - unfold Values.Val.cmp.
        subst.
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
               transl_value v1 = x ->
               transl_value v2 = x0 ->
               Math.gt v1 v2 = Some v0 ->
               transl_value v0 = (Values.Val.cmp Integers.Cgt x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  !invclear heq.
  eq_same_clear.
  rewrite Z.gtb_ltb.
  !destruct (Z.lt_decidable n0 n).
  - rewrite Fcore_Zaux.Zlt_bool_true;auto.
    unfold Values.Val.cmp.
    subst.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_true.
    + reflexivity.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
  - { rewrite Fcore_Zaux.Zlt_bool_false.
      - unfold Values.Val.cmp.
        subst.
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
    transl_value v1 = n ->
    Math.unary_operation Unary_Minus v1 = Some v ->
    transl_value v = (Values.Val.negint n).
Proof.
  !intros.
  simpl in *.
  destruct v1;simpl in *;try discriminate.
  eq_same_clear.
  subst.   
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
    transl_value v1 = n1 ->
    transl_value v2 = n2 ->
    transl_value v = (Values.Val.add n1 n2).
Proof.
  !intros.
  simpl in *.
  !destruct v1;simpl in *;try discriminate;eq_same_clear;subst;try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc.
  - !invclear h_do_rtc_binop;simpl in *; eq_same_clear. 
    !invclear h_overf_check.
    int_simpl;auto;inv_rtc;auto 2.
Qed.

Lemma sub_ok :
  forall v v1 v2 n1 n2,
    check_overflow_value v1 -> 
    check_overflow_value v2 -> 
    do_run_time_check_on_binop Minus v1 v2 (Normal v) ->
    transl_value v1 = n1 ->
    transl_value v2 = n2 ->
    transl_value v = (Values.Val.sub n1 n2).
Proof.
  !intros.
  simpl in *.
  !destruct v1;simpl in *;try discriminate;eq_same_clear;subst; try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc.
  - !invclear h_do_rtc_binop;simpl in *; eq_same_clear. 
    !invclear h_overf_check.
    int_simpl;auto;inv_rtc;auto 2.
Qed.

Lemma mult_ok :
  forall v v1 v2 n1 n2,
    check_overflow_value v1 -> 
    check_overflow_value v2 -> 
    do_run_time_check_on_binop Multiply v1 v2 (Normal v) ->
    transl_value v1 = n1 ->
    transl_value v2 = n2 ->
    transl_value v = (Values.Val.mul n1 n2).
Proof.
  !intros.
  simpl in *.
  !destruct v1;simpl in *;try discriminate;eq_same_clear;subst; try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc.
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
    transl_value v1 = n1 ->
    transl_value v2 = n2 ->
    transl_value v = n ->
    Values.Val.divs n1 n2 = Some n.
Proof.
  !intros.
  simpl in *.
  !destruct v1;subst;simpl in *;try discriminate;try now inv_rtc.
  !destruct v2;subst;simpl in *; try discriminate;try now inv_rtc.
  rename n0 into v1.
  rename n into v2.
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
    transl_value v1 = n1 ->
    transl_value v2 = n2 ->
    transl_value v = n ->
    forall m, Cminor.eval_binop (transl_binop op) n1 n2 m = Some n.
Proof.
  !intros.
  assert (h_rtc:=do_run_time_check_on_binop_ok _ _ _ _ h_do_rtc_binop).
  destruct op;simpl.
  - erewrite (and_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (or_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (eq_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (neq_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (lt_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (le_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (gt_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (ge_ok v1 v2 v n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (add_ok v v1 v2 n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (sub_ok v v1 v2 n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
  - erewrite (mult_ok v v1 v2 n1 n2) in heq_transl_value;eq_same_clear;subst;eauto.
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
  


Definition stack_match st s CE sp locenv g m :=
  forall nme v addrof_nme load_addrof_nme typ_nme cm_typ_nme,
    eval_name st s nme (Normal v) ->
    type_of_name st nme = OK typ_nme ->
    transl_name st CE nme = OK addrof_nme ->
    transl_type st typ_nme = OK cm_typ_nme ->
    make_load addrof_nme cm_typ_nme = OK load_addrof_nme ->
    Cminor.eval_expr g sp locenv m load_addrof_nme (transl_value v).

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

Record match_env (st:symboltable) (s: semantics.STACK.stack)
       (CE:compilenv) (sp:Values.val) (locenv: Cminor.env)
       (g:genv)(m:Memory.Mem.mem): Prop :=
  mk_match_env {
      me_transl: stack_match st s CE sp locenv g m;
      me_overflow: safe_stack s
    }.


(** Hypothesis renaming stuff *)
Ltac rename_hyp3 h th :=
  match th with
    | match_env _ _ _ _ _ _ _ => fresh "h_match_env"
    | _ => rename_hyp2 h th
  end.

Ltac rename_hyp ::= rename_hyp3.

Ltac rename_hyp4 h th :=
  match reverse goal with
    | H: fetch_var_type ?X _ = OK h |- _  => (fresh "type_" X)
    | H: id (fetch_var_type ?X _ = OK h) |- _ => (fresh "type_" X)
    | H: (value_at_addr _ _ ?X = OK h) |- _ => fresh "val_at_" X
    | H: id (value_at_addr _ _ ?X = OK h) |- _ => fresh "val_at_" X
    | H: transl_variable _ _ _ ?X = OK h |- _ => fresh X "_t"
    | H: id (transl_variable _ _ _ ?X = OK h) |- _ => fresh X "_t"
    | H: transl_value ?X = OK h |- _ => fresh X "_t"
    | H: id (transl_value ?X = OK h) |- _ => fresh X "_t"
    | _ => rename_hyp3 h th
  end.
Ltac rename_hyp ::= rename_hyp4.

(* Is this true? *)
(*Axiom CM_eval_bigstep_det: forall g sp locenv m e v v',
    Cminor.eval_expr g sp locenv m e v ->
    Cminor.eval_expr g sp locenv m e v' ->
    v = v'.*)


Lemma transl_expr_ok :
  forall stbl CE (e:expression) (e':Cminor.expr),
    transl_expr stbl CE e = OK e' ->
    forall locenv g m (s:STACK.stack)  (v:value)
         (spb: Values.block) (ofs:Integers.Int.int),
    eval_expr stbl s e (Normal v) ->
    match_env stbl s CE (Values.Vptr spb ofs) locenv g m ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m e' (transl_value v).
Proof.
  intros until e.
  !functional induction (transl_expr stbl CE e);try discriminate;simpl; !intros;
  !invclear h_eval_expr;eq_same_clear.
  - generalize (transl_literal_ok g lit v h_eval_literal (Values.Vptr spb ofs)).
    !intro.
    constructor.
    assumption.
  - unfold value_at_addr in heq.
    destruct (transl_type stbl type_id) eqn:heq_transl_type;simpl in *.
    + !destruct h_match_env.
      eapply me_transl0;eauto.
    + discriminate.
  - specialize (IHr x heq0 locenv g m s v1 spb ofs h_eval_expr0 h_match_env).
    specialize (IHr0 x0 heq locenv g m s v2 spb ofs h_eval_expr h_match_env).

    eapply eval_Ebinop;eauto. 
    eapply binary_operator_ok;eauto.
    * eapply eval_expr_overf2;eauto.
      eapply h_match_env.(me_overflow stbl s CE (Values.Vptr spb ofs) locenv g m).
    * eapply eval_expr_overf2;eauto.
      eapply h_match_env.(me_overflow stbl s CE (Values.Vptr spb ofs) locenv g m).
  (* Unary minus *)
  - simpl in heq.
    eq_same_clear.
    rename x into e'.
    rename e0 into e.
    specialize (IHr e' heq0 locenv g m s v0 spb ofs
                    h_eval_expr h_match_env).
    eapply eval_Eunop;auto.
    + apply IHr.
    + simpl.
      assert (h:=unaryneg_ok (transl_value v0) v0 v eq_refl).
      rewrite h in *;auto.
      !invclear h_do_rtc_unop; simpl in *;auto.
      !invclear h_overf_check;subst;simpl in *; try eq_same_clear.
      assumption.
  (* Not *)
  - !invclear h_do_rtc_unop;simpl in *;try eq_same_clear.
    clear hneq.
    destruct v0;simpl in *;try discriminate;eq_same_clear;simpl in *.
    destruct n;simpl in *; eq_same_clear.
    * { econstructor;simpl in *.
        * eapply IHr;eauto.
        * econstructor.
          simpl.
          reflexivity.
        * vm_compute.
          reflexivity. }
    * { econstructor;simpl in *.
        * eapply IHr ;eauto.
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
Set Printing Width 90.


Axiom expression_dec: forall e1 e2:expression, ({e1=e2} + {e1<>e2}).
Axiom name_dec: forall e1 e2:name, {e1=e2} + {e1<>e2}. 

Import STACK.

Axiom det_eval_expr: forall g spb ofs locenv m e v v',
                       Cminor.eval_expr g (Values.Vptr spb ofs) locenv m e v
                       -> Cminor.eval_expr g (Values.Vptr spb ofs) locenv m e v'
                       -> v = v'.

Inductive le_loads (lds: Cminor.expr): Cminor.expr -> Prop :=
  le_loads_n: le_loads lds lds
| le_loads_L: ∀ lds', le_loads lds lds' -> le_loads lds (Eload AST.Mint32 lds').
 
Definition lt_loads := λ l₁ l₂, le_loads(Eload AST.Mint32 l₁) l₂.

Lemma le_loads_ese_L : forall lds₁ lds₂: Cminor.expr,
    le_loads lds₁ lds₂ -> le_loads (Eload AST.Mint32 lds₁) (Eload AST.Mint32 lds₂).
Proof.
  !intros.
  induction H.
  - constructor 1.
  - constructor 2.
    assumption.
Qed.

Lemma le_load_L_e : ∀ l₁ l₂,
    le_loads (Eload AST.Mint32 l₁) (Eload AST.Mint32 l₂) ->
    le_loads l₁ l₂.
Proof.
  intros l₁ l₂.
  revert l₁.
  induction l₂;intros;try discriminate.
  - inversion H;try now constructor.
    inversion H1.
  - inversion H;try now constructor.
    inversion H1.
  - inversion H;try now constructor.
    inversion H1.
  - inversion H;try now constructor.
    inversion H1.
  - inversion H;try now constructor.
    inversion H1;subst.
    + constructor 2.
      auto.
    + constructor 2.
      auto.
Qed.

Lemma lt_load_L_L : ∀ l₁ l₂,
    lt_loads (Eload AST.Mint32 l₁) (Eload AST.Mint32 l₂) ->
    lt_loads l₁ l₂.
Proof.
  unfold lt_loads.
  intros l₁ l₂ H.
  apply le_load_L_e;auto.
Qed.

Lemma lt_load_irrefl : ∀ l₁, ¬ lt_loads l₁ l₁.
Proof.
  intros l₁.
  unfold lt_loads.
  induction l₁;try (intro abs; inversion abs).
  - subst m.
    apply IHl₁.
    rewrite <- H1 at 2.
    constructor 1.
  - subst.
    apply le_load_L_e in abs.
    apply IHl₁.
    assumption.
Qed.

Lemma lt_load_neq : ∀ l₁ l₂, lt_loads l₁ l₂ -> l₁ ≠ l₂.
Proof.
  unfold lt_loads.
  intros l₁ l₂.
  remember (Eload AST.Mint32 l₁) as h'.
  revert h' l₁ Heqh'.
  induction l₂;intros; subst ; try now inversion H.
  intro abs.
  subst.
  assert (m=AST.Mint32). {
    inversion H;auto. }
  subst.
  apply le_load_L_e in H.
  specialize (IHl₂ (Eload AST.Mint32 l₂) l₂ eq_refl H).
  apply IHl₂;auto.
Qed.


Lemma neq_sym : forall A, forall x y : A , x<>y  -> y<>x.
Proof.
  intros A x y H.
  intro abs.
  subst.
  apply H;reflexivity.
Qed.

Lemma build_loads__inj :
  forall i₁ i₂,
    (* translating the variabe to a Cminor load address *)
    build_loads_ i₁ = build_loads_ i₂ ->
    i₁ = i₂.
Proof.
  intros i₁.
  !induction i₁;simpl;!intros.
  - destruct i₂;auto.
    simpl in heq.
    inversion heq.
  - destruct  i₂;simpl in *;auto.
    + inversion heq.
    + inversion heq.
      rewrite (IHi₁ i₂);auto.
Qed.

Lemma build_loads__inj_lt :
  forall i₁ i₂,
    (i₁ < i₂)%nat ->
    forall e₁ e₂ ,
      (* translating the variabe to a Cminor load address *)
      build_loads_ i₁ = e₁ ->
      (* translating the variabe to a Cminor load address *)
      build_loads_ i₂ = e₂ ->
      lt_loads e₁ e₂.
Proof.
  intros i₁ i₂.
  unfold lt_loads.
  !intro.
  induction H;simpl;!intros;subst.
  - constructor 1.
  - constructor 2.
    apply IHle;auto.
Qed.

Lemma build_loads__inj_neq :
  forall i₁ i₂,
    i₁ ≠ i₂ ->
    forall e₁ e₂ ,
      (* translating the variabe to a Cminor load address *)
      build_loads_ i₁ = e₁ ->
      (* translating the variabe to a Cminor load address *)
      build_loads_ i₂ = e₂ ->
      e₁ ≠ e₂.
Proof.
  !intros.
  intro abs.
  subst.
  apply build_loads__inj in abs.
  contradiction.
Qed.

Lemma build_loads_inj :
  forall i₁ i₂ k k' ,
      (* translating the variabe to a Cminor load address *)
      build_loads k i₁ = build_loads k' i₂ ->
      k = k' ∧ Integers.Int.Z_mod_modulus i₁ = Integers.Int.Z_mod_modulus i₂.
Proof.
  unfold build_loads.
  !intros.
  inversion heq.
  split;auto.  
  apply build_loads__inj;auto.
Qed.

Lemma build_loads_inj_neq1 :
  forall i₁ i₂ k k' e₁ e₂,
    k ≠ k' ->
    build_loads k i₁ = e₁ ->
    build_loads k' i₂ = e₂ ->
    e₁ ≠ e₂.
Proof.
  !intros.
  intro abs.
  subst.
  apply build_loads_inj in abs.
  destruct abs;contradiction.
Qed.

Lemma build_loads_inj_neq2 :
  forall i₁ i₂ k k' e₁ e₂,
    Integers.Int.Z_mod_modulus i₁ ≠ Integers.Int.Z_mod_modulus i₂ ->
    build_loads k i₁ = e₁ ->
    build_loads k' i₂ = e₂ ->
    e₁ ≠ e₂.
Proof.
  !intros.
  intro abs.
  subst.
  apply build_loads_inj in abs.
  destruct abs;contradiction.
Qed.


Lemma CEfetch_reside_true : forall id a x,
    CompilEnv.fetch id a = Some x -> CompilEnv.reside id a = true.
Proof.
  intros until a.
  unfold CompilEnv.fetch, CompilEnv.reside.
  induction (CompilEnv.store_of a);simpl;!intros;try discriminate.
  destruct a0.
  destruct (beq_nat id i).
  - reflexivity.
  - eapply IHs;eauto.
Qed.

Lemma CEfetch_reside_false : forall id a,
    CompilEnv.fetch id a = None -> CompilEnv.reside id a = false.
Proof.
  intros until a.
  unfold CompilEnv.fetch, CompilEnv.reside.
  induction (CompilEnv.store_of a);simpl;!intros;try reflexivity.
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
  !induction a;simpl;intros;try discriminate.
  !destruct (CompilEnv.reside id a).
  - inversion H.
    left.
    reflexivity.
  - right.
    eapply IHa;eauto.
Qed.

Lemma fetches_In : forall a id st,
    CompilEnv.fetches id a = Some st ->
    List.In (id,st) a.
Proof.
  intro a.
  !induction a;simpl;!intros;try discriminate.
  !destruct a;simpl in *.
  !destruct (eq_nat_dec id i);subst;simpl in *.
  - rewrite <- beq_nat_refl in heq.
    inversion heq.
    left.
    reflexivity.
  - right.
    rewrite <- beq_nat_false_iff in hneq.
    rewrite hneq in heq.
    eapply IHa;eauto.
Qed.

Lemma fetch_In : forall a id st,
    CompilEnv.fetch id a = Some st ->
    List.In (id,st) (CompilEnv.store_of a).
Proof.
  !intros.
  unfold CompilEnv.fetch in heq_CEfetch_id_a.
  apply fetches_In.
  assumption.
Qed.




Require Import FMapList.
Require Import OrderedType.

(*
Inductive increasing_order : localframe -> Prop :=
  IncO : increasing_order []
| IncNext: forall lf id δ,
    increasing_order lf ->
    (forall otherid y', CompilEnv.fetches otherid lf = Some y' -> δ < y') ->
    increasing_order ((id,δ)::lf).
*)
(*
Module localframeORD <: OrderedType.
  Definition t := (idnum * CompilEnv.V)%type.
  
  Definition eq := @eq t.
  Definition lt := (fun x y:t => snd x < snd y).

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Opaque eq_refl eq_sym eq_trans.

  Lemma lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.
  Proof.
    !intros.
    unfold eq , lt in *.
    intro abs.
    subst.
    destruct (Z.lt_irrefl _ H).
  Qed.
  Lemma lt_irrefl: bool.
    exact true.
  Qed.
  Lemma lt_antisym :symmetric _ lt.
  Proof.
    admit.
  Qed.
      
  Lemma lt_trans:transitive _ lt.
  Proof.
    unfold transitive.
    !intros.
    unfold lt in *.
    eapply Zlt_trans;eauto.
  Qed.



End localframeORD.
MSetList.Make().
*)
Definition increasing_order: localframe -> Prop := StronglySorted (fun x y => snd x > snd y).

Definition increasing_order_fr (f:CompilEnv.frame) :=
  increasing_order(CompilEnv.store_of f).


(* FIXME: find another name *)
(* levels of each substack are ordered *)
(*
Inductive increasing_orderG : CompilEnv.stack -> Prop :=
  IncOG : increasing_orderG []
| IncNextG: forall stk frm,
    increasing_orderG stk ->
    increasing_order_fr frm ->
    (List.Forall
       (fun otherfrm =>
          (CompilEnv.level_of otherfrm < CompilEnv.level_of frm)%nat)
       stk) ->
    increasing_orderG (frm::stk).
*)
Definition increasing_orderG (stk: CompilEnv.stack): Prop :=
  StronglySorted (fun x y => (CompilEnv.level_of x > CompilEnv.level_of y)%nat) stk.




Ltac rename_hyp_incro h th :=
  match th with
    | increasing_order_fr ?x => fresh "h_incr_order_fr_" x
    | increasing_order_fr _ => fresh "h_incr_order_fr"
    | increasing_order ?x => fresh "h_incr_order_" x
    | increasing_order _ => fresh "h_incr_order"
    | increasing_orderG ?x => fresh "h_incr_orderG_" x
    | increasing_orderG _ => fresh "h_incr_orderG"
    | Forall ?P ?x => fresh "h_forall_" P "_" x
    | Forall _ ?x => fresh "h_forall_" x
    | Forall ?P _ => fresh "h_forall_" P
    | Forall _ _ => fresh "h_forall"
    | _ => rename_hyp5 h th
  end.
Ltac rename_hyp ::= rename_hyp_incro.

Section mapping.
  
  Variable (stbl: symboltable) (CE:compilenv) (ofs : Integers.Int.int)
           (spb : Values.block) (locenv : env) (g : genv).

  Lemma increase_order_level_of_top_ge:
    forall id s s0 s3,
      increasing_orderG CE ->
      CompilEnv.frameG id CE = Some (s, s0) ->
      CompilEnv.level_of_top CE = Some s3 -> 
      (s3 >= s)%nat.
  Proof.
    !intros.
    unfold increasing_orderG in *.
    !destruct CE;!intros.
    - simpl in *;try discriminate.
    - specialize (increasing_order_In _ _ _ _ h_incr_orderG_CE).
      !intro.
      rewrite Forall_forall in h_forall.
      apply NPeano.Nat.lt_eq_cases.
      unfold CompilEnv.level_of in *.
      apply frameG_In in heq_CEframeG_id_CE.
      specialize (h_forall _ heq_CEframeG_id_CE).
      !destruct f.
      unfold CompilEnv.level_of_top in heq_lvloftop_CE_s3.
      simpl in *.
      !invclear heq_lvloftop_CE_s3.
      !destruct h_forall;auto.
      inject heq;auto.
  Qed.        

  
  Lemma CEfetches_inj : forall id₁ id₂ (lf:localframe) δ₁ δ₂,
      increasing_order lf ->
      CompilEnv.fetches id₁ lf = Some δ₁ ->
      CompilEnv.fetches id₂ lf = Some δ₂ ->
      id₁ ≠ id₂ ->
      δ₁ ≠ δ₂.
  Proof.
    intros until lf.
    !induction lf;simpl in *;!intros.
    - discriminate.
    - destruct a.
      destruct (NPeano.Nat.eq_dec id₁ i);subst.
      + rewrite NPeano.Nat.eqb_refl in heq0.
        !invclear heq0.
        assert (h:id₂ ≠ i) by auto.
        rewrite <- (NPeano.Nat.eqb_neq id₂ i) in h.
        rewrite h in heq.
        inversion h_incr_order;subst;simpl in *.
        assert (δ₁ > δ₂). {
          rewrite Forall_forall in H2.
          eapply (H2 (id₂,δ₂));eauto.
          apply fetches_In.
          assumption. }
        apply neq_sym.
        apply Z.lt_neq.
        apply Z.gt_lt_iff.
        assumption.
      + destruct (NPeano.Nat.eq_dec id₂ i).
        * subst.        
          rewrite NPeano.Nat.eqb_refl in heq.
          !invclear heq.
          assert (h:id₁ ≠ i) by auto.
          rewrite <- (NPeano.Nat.eqb_neq id₁ i) in h.
          rewrite h in heq0.
          inversion h_incr_order;subst;simpl in *.
        assert (δ₂ > δ₁). {
          rewrite Forall_forall in H2.
          eapply (H2 (id₁,δ₁));eauto.
          apply fetches_In.
          assumption. }
        apply Z.lt_neq.
        apply Z.gt_lt_iff.
        assumption.
        * rewrite <- (NPeano.Nat.eqb_neq id₁ i) in n.
          rewrite <- (NPeano.Nat.eqb_neq id₂ i) in n0.
          rewrite n,n0 in *.
          apply IHlf;auto.
          inversion h_incr_order.
          assumption.
  Qed.

  
  Lemma CEfetch_inj : forall id₁ id₂ (a:CompilEnv.frame) δ₁ δ₂,
      increasing_order_fr a -> 
      CompilEnv.fetch id₁ a = Some δ₁ ->
      CompilEnv.fetch id₂ a = Some δ₂ ->
      id₁ ≠ id₂ ->
      δ₁ ≠ δ₂.
  Proof.
    intros until a.
    unfold CompilEnv.fetch.
    !destruct a;simpl.
    unfold increasing_order_fr.
    simpl.
    apply CEfetches_inj.
  Qed.


  Lemma CEfetchG_inj : forall id₁ id₂,
      increasing_orderG CE -> 
      List.Forall (fun otherfrm => increasing_order_fr otherfrm) CE ->
      forall  δ₁ δ₂ k₁ k₂ frm₁ frm₂,
        CompilEnv.fetchG id₁ CE = Some δ₁ ->
        CompilEnv.fetchG id₂ CE = Some δ₂ ->
        CompilEnv.frameG id₁ CE = Some (k₁, frm₁) -> 
        CompilEnv.frameG id₂ CE = Some (k₂, frm₂) -> 
        id₁ ≠ id₂ ->
        (k₁ <> k₂ \/ δ₁ <> δ₂).
  Proof.
    intros id₁ id₂.
    !intro.
    !induction h_incr_orderG_CE;!intros;simpl in *;try discriminate.
    rewrite Forall_forall in h_forall_l, h_forall.
    unfold CompilEnv.level_of in *.
    destruct (CompilEnv.fetch id₁ a) eqn:heq_fetch_id₁;
      destruct (CompilEnv.fetch id₂ a) eqn:heq_fetch_id₂;
      eq_same_clear;subst;simpl in *;try discriminate.
    - right.
      eapply CEfetch_inj;eauto.
    - left.
      apply neq_sym.
      apply NPeano.Nat.lt_neq.
      apply CEfetch_reside_false in heq_fetch_id₂.
      apply CEfetch_reside_true in heq_fetch_id₁.
      rewrite heq_fetch_id₂,heq_fetch_id₁ in *;simpl in *.
      !invclear heq_CEframeG_id₁;simpl in *.
      specialize (h_forall_l (k₂, frm₂)).
      simpl in *.
      apply h_forall_l.
      eapply frameG_In;eauto.
    - left.
      apply NPeano.Nat.lt_neq.
      apply CEfetch_reside_true in heq_fetch_id₂.
      apply CEfetch_reside_false in heq_fetch_id₁.
      rewrite heq_fetch_id₂,heq_fetch_id₁ in *;simpl in *.
      !invclear heq_CEframeG_id₂;simpl in *.
      specialize (h_forall_l (k₁, frm₁)).
      simpl in *.
      apply h_forall_l.
      eapply frameG_In;eauto.
    - apply CEfetch_reside_false in heq_fetch_id₁. 
      apply CEfetch_reside_false in heq_fetch_id₂. 
      rewrite heq_fetch_id₁,heq_fetch_id₂ in *.
      eapply IHh_incr_orderG_CE ;eauto.
      rewrite Forall_forall.
      intros x H.
      apply h_forall;auto.
  Qed.


  Lemma minus_same_eq : forall s3 s s1,
    s ≤ s3 ->
    s1 ≤ s3 ->
    (s3 - s1)%nat = (s3 - s)%nat ->
    s = s1.
  Proof.
    induction s3;intros.
    - inversion H0;inversion H;auto.
    - inversion H;inversion H0;subst.
      + reflexivity.
      + rewrite minus_diag in H1.
        apply NPeano.Nat.sub_0_le in H1.
        assert (s3 < s3)%nat. {
          eapply lt_le_trans with s1;auto. }
        destruct (lt_irrefl s3);auto.
      + rewrite minus_diag in H1.
        symmetry in H1.
        apply NPeano.Nat.sub_0_le in H1.
        assert (s3 < s3)%nat. {
          eapply lt_le_trans with s;auto. }
        destruct (lt_irrefl s3);auto.
      + eapply IHs3;eauto.
        setoid_rewrite <- minus_Sn_m in H1;auto.
  Qed.

  Lemma minus_same_neq : forall s3 s s1,
    s ≤ s3 ->
    s1 ≤ s3 ->
    s <> s1 ->
    (s3 - s1)%nat <> (s3 - s)%nat.
  Proof.
    !intros.
    intro abs.
    apply minus_same_eq in abs;auto.
  Qed.


  
  Lemma foo :
    forall a₁ a₂ id₁ id₂ k₁ k₂ δ₁ δ₂,
      (* Frame are numbered with different (increasing) numers *)
      increasing_orderG CE ->
      (* In each frame, stacks are also numbered with (increasing) numbers *)
      List.Forall (fun otherfrm => increasing_order_fr otherfrm) CE ->
      (forall id δ, CompilEnv.fetchG id CE = Some δ -> 0 <= δ ∧ δ < Integers.Int.modulus) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a₁ id₁ = OK (build_loads k₁ δ₁) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a₂ id₂ = OK   (build_loads k₂ δ₂) ->
      id₁ <> id₂ ->
      (k₁ <> k₂ \/ δ₁<> δ₂).
  Proof.
    !intros.
    match goal with
    | H: appcontext [(0 <= _) ∧ (_ < Integers.Int.modulus)] |- _ => rename H into h_bound_CE
    end.
    unfold transl_variable in *.
    destruct (CompilEnv.fetchG id₁ CE) eqn:h₁;simpl in *;try discriminate.
    destruct (CompilEnv.fetchG id₂ CE) eqn:h₂;simpl in *;try discriminate.
    destruct (CompilEnv.frameG id₁ CE) eqn:h₁';simpl in *;try discriminate.
    destruct (CompilEnv.frameG id₂ CE) eqn:h₂';simpl in *;try discriminate.
    destruct f.
    destruct f0.
    assert (hh:=CEfetchG_inj _ _ h_incr_orderG_CE h_forall_CE _ _ _ _ _ _  h₁ h₂ h₁' h₂' hneq).
    destruct (CompilEnv.level_of_top CE) eqn:hlvlofCE.
    - (* remember here refrain inversion to bizarrely unfold too much. *)
      remember (build_loads (s3 - s1) t0) as fooo.
      remember (build_loads (s3 - s) t) as fooo'.
      inversion heq_transl_variable as [heqfoo].
      inversion heq_transl_variable0 as [heqfoo'].
      clear heq_transl_variable heq_transl_variable0.
      subst.
      apply build_loads_inj in heqfoo.
      apply build_loads_inj in heqfoo'.
      !destruct heqfoo.
      !destruct heqfoo'.
      subst.
      !destruct hh.
      + left.
        eapply minus_same_neq;eauto.
        eapply increase_order_level_of_top_ge;eauto.
        eapply increase_order_level_of_top_ge;eauto.
      + repeat rewrite Integers.Int.Z_mod_modulus_eq in *.
        rewrite Coqlib.Zmod_small in *;eauto.
        subst.
        right.
        intro abs.
        subst.
        apply hneq0;reflexivity.
    - discriminate.
  Qed.


  (* We need something more precise, probably this: *)
  Lemma foo2 :
    forall stbl chnk₁ chnk₂ a₁ a₂ id₁ id₂ k₁ k₂ δ₁ δ₂,
      (* Frame are numbered with different (increasing) numers *)
      increasing_orderG CE ->
      (* In each frame, stacks are also numbered with (increasing) numbers *)
      List.Forall (fun otherfrm => increasing_order_fr otherfrm) CE ->
      (forall id δ, CompilEnv.fetchG id CE = Some δ
                    -> 0 <= δ ∧ δ < Integers.Int.modulus) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a₁ id₁ = OK (build_loads k₁ δ₁) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a₂ id₂ = OK (build_loads k₂ δ₂) ->
      compute_chnk_id stbl id₁ = OK chnk₁ ->
      compute_chnk_id stbl id₂ = OK chnk₂ ->
      id₁ <> id₂ ->
      (k₁ <> k₂
       \/ δ₁ < δ₂ + Memdata.size_chunk chnk₂
       \/ δ₂ < δ₁ + Memdata.size_chunk chnk₁).
  Proof.
  Admitted.

  xxx
  
(* storeUpdate stbl s (E_Identifier a i) e0_v (@Normal stack s') *)
Lemma foo :
  forall s m a x1 id id_t e e_t e_v e_t_v idaddr s' m',
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = OK id_t ->
    (* translating the expression to Cminor *)
    transl_expr stbl CE e = OK e_t ->
    (* Evaluating in spark *)
    eval_expr stbl s e (Normal e_v) ->
    (* Evaluating expression in Cminor *)
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m e_t e_t_v ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (E_Identifier a id) = OK x1 ->

    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (E_Identifier a id) e_v (Normal s') ->
    Memory.Mem.storev x1 m idaddr e_t_v = Some m' ->
    match_env stbl s CE (Values.Vptr spb ofs) locenv g m ->
    match_env stbl s' CE (Values.Vptr spb ofs) locenv g m'.

Proof.
  intros s m a x1 id id_t e e_t e_v e_t_v idaddr s' m'.
  !intros.
  generalize (transl_expr_ok _ _ _ _ heq1).
  intro h.
  specialize (h _ _ _ _ _ _ _ h_eval_expr h_match_env).

  unfold transl_variable in heq_transl_variable.
  destruct (CompilEnv.fetchG id CE) eqn:heqG;try discriminate.
  destruct (CompilEnv.frameG id CE) eqn:heqfG;try discriminate.
  destruct f.
  destruct (CompilEnv.level_of_top CE) eqn:heqlT;simpl in *;try discriminate.
  
  
  admit.
Qed.



Lemma transl_stmt_ok :
  forall stbl CE  (stm:statement) (stm':Cminor.stmt),
    transl_stmt stbl CE stm = (OK stm') ->
    forall locenv (g:genv) (m:Memory.Mem.mem) (s:stack)
           (s':stack) (spb:Values.block) ofs f,
      match_env stbl s CE (Values.Vptr spb ofs) locenv g m ->
      eval_stmt stbl s stm (Normal s') ->
      forall tr locenv' m' o,
        Cminor.exec_stmt g f (Values.Vptr spb ofs) locenv m stm' tr locenv' m' o
        ->  match_env stbl s' CE (Values.Vptr spb ofs) locenv g m'.
Proof.
  intros until stm.
  !functional induction (transl_stmt stbl CE stm)
  ;simpl;!intros;eq_same_clear;subst;simpl in *;try discriminate.
  (* skip *)
  - !invclear h_eval_stmt.
    !invclear h_exec_stmt.
    assumption.
    (* assignment *)
  - rename x into e0_t.
    rename x0 into nme_t.
    remember (Values.Vptr spb ofs) as stkpter.
    !invclear h_eval_stmt.
    + rename v into e0_v.
      !invclear h_exec_stmt.
      rename v into e0_t_v.
      destruct nme.
      subst.

      assert (forall CE stkpter locenv' g stbl s a i e0_v s' x1 m vaddr e0_t_v  m'  ,
                 storeUpdate stbl s (E_Identifier a i) e0_v (Normal s') ->
                 transl_expr stbl CE e0 = OK e0_t ->
                 eval_expr stbl s e0 (Normal e0_v) ->
                 Cminor.eval_expr g stkpter locenv' m e0_t e0_t_v ->
                 Cminor.eval_expr g stkpter locenv' m nme_t vaddr ->
                 Memory.Mem.storev x1 m vaddr e0_t_v = Some m' ->
                 match_env stbl s CE stkpter locenv' g m ->
                 match_env stbl s' CE stkpter locenv' g m').
      { admit. }
      eapply H;eauto.
      

      
      * rename i into idnme.
        generalize (storeUpdate_id_ok_others a stbl s idnme e0_v s' h_storeupdate).
        intro h_fetch_other_OK.
        generalize (storeUpdate_id_ok_same a stbl s idnme e0_v s' h_storeupdate).
        intro h_fetch_same_OK.
        split. {
          - red.
            !intros.
            rename nme into newnme.
            destruct (name_dec (E_Identifier a idnme) newnme).
            + admit. (* address is the same *)
            + 
        }
          
          * !destruct h_match_env.
        
      
      assert (h:exists v', transl_value e0_v = OK v'). {
        admit. (* transl_value should not return Error. *)
      }
      !destruct h.
      assert ().
      
      eapply transl_expr_ok in heq_transl_value.
      * 
      assert (exists v', transl_value e0_v = OK v'). {      
        transl_expr_ok
        erewrite CM_eval_bigstep_det in h_CM_eval_expr.
        - assumption.
        
      }.
      
      assert (transl_value e0_v = OK v). {
        transl_expr_ok
        erewrite CM_eval_bigstep_det in h_CM_eval_expr.
        - assumption.
        
      }
        
 
          
          
        
        specialize (transl_name_ok stbl s x2 arrObj h_eval_name CE locenv' g m).
      * specialize (transl_name_ok stbl s x2 arrObj h_eval_name CE locenv' g m).
        !inversion heq_transl_name.
        intros h.
Lemma storeUpdate_ok_same:
  forall stbl CE s nme nme_t x (v:value) v' s',
    eval_name stbl s nme (Normal x) ->
    transl_name stbl CE nme = nme_t ->
    storeUpdate stbl s nme v (Normal s') ->
    fetchG nme s' = v ->
    transl_value v v_t ->
    Memory.Mem.storev m nme_t v_t m' ->
    Memory.Mem.loadv chunk m nme_t = Some v_t.
Proof.
    


    specialize (storeUpdate_ok_others ).


     !invclear h_exec_stmt.
   

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

*)