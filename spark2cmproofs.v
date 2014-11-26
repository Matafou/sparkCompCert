
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



(* See CminorgenProof.v@205. *)
Record match_env (st:symboltable) (s: semantics.STACK.stack) (CE:compilenv) (sp:Values.val)
       (locenv: Cminor.env): Prop :=
  mk_match_env {
      (* We will need more than that probably. But for now let us use
         a simple notion of matching: the value of a variable is equal
         to the value of its translation. Its translation is currently
         (an expression of the form ELoad((Eload(Eload ...(Eload(0))))
         + n)). We could define a specialization of eval_expr for this
           kind of expression but at some point the form of the
           expression will complexify (some variables may stay
           temporary instead of going in the stack, etc).

         We also put well-typing constraints on the stack wrt symbol
         table.
       *)
      me_vars:
        forall id st astnum v typeofv,
            STACK.fetchG id s = Some v ->
            fetch_var_type id st = OK typeofv ->
            exists e' v' rtypeofv typeofv' ld,
              reduce_type st typeofv max_recursivity = OK rtypeofv /\
              concrete_type_of_value v = OK rtypeofv /\ (* stack is well typed wrt st *)
              transl_value v = OK v' /\
              transl_type st typeofv = OK typeofv' /\
              transl_variable st CE astnum id = OK e' /\
              make_load e' typeofv' = OK ld /\
              forall (g:genv)(m:Memory.Mem.mem),
                Cminor.eval_expr g sp locenv m ld v';
      
      me_overflow:
        forall id n,
          STACK.fetchG id s = Some (Int n) ->
          do_overflow_check n (Normal (Int n))

(*       me_vars:
        forall id st astnum typeofv,
          fetch_var_type id st = OK typeofv ->
          exists (v:STACK.V) e' v' typeofv' ld,
            STACK.fetchG id s = Some v ->
            transl_variable st CE astnum id = OK e' ->
            transl_type st typeofv = OK typeofv' /\
            transl_value v = OK v' /\
            make_load e' typeofv' = OK ld /\
            forall (g:genv)(m:Memory.Mem.mem),
              Cminor.eval_expr g sp locenv m ld v'
 *)
    }.

(** Hypothesis renaming stuff *)
Ltac rename_hyp1 th :=
  match th with
    | eval_expr _ _ _ (Normal _) => fresh "h_eval_expr"
    | eval_expr _ _ _ (Run_Time_Error _) => fresh "h_eval_expr_RE"
    | eval_name _ _ _ (Normal _) => fresh "h_eval_name"
    | eval_name _ _ _ (Run_Time_Error _) => fresh "h_eval_name_RE"
    | eval_name _ _ _ _ => fresh "h_eval_name"
    | do_overflow_check _ (Run_Time_Error _) => fresh "h_overf_check_RE"
    | do_overflow_check _ _ => fresh "h_overf_check"
    | do_range_check _ _ _ (Run_Time_Error _) => fresh "h_do_range_check_RE"
    | do_range_check _ _ _ _ => fresh "h_do_range_check"
    | do_run_time_check_on_binop _ _ _ (Run_Time_Error _) => fresh "h_do_rtc_binop_RTE"
    | do_run_time_check_on_binop _ _ _ _ => fresh "h_do_rtc_binop"
    | Cminor.eval_constant _ _ _ = (Some _)  => fresh "h_eval_constant"
    | Cminor.eval_constant _ _ _ = None  => fresh "h_eval_constant_None"
    | eval_literal _ (Normal _)  => fresh "h_eval_literal"
    | eval_literal _ (Run_Time_Error _)  => fresh "h_eval_literal_RE"
    | eval_literal _ _  => fresh "h_eval_literal"
    | Cminor.eval_expr _ _ _ _ _ _ => fresh "h_CM_eval_expr"
    | match_env _ _ _ _ _ => fresh "h_match_env"
    | transl_value _ = OK _ => fresh "heq_transl_value"
    | transl_value _ = Run_Time_Error _ => fresh "heq_transl_value_RE"
    | transl_variable _ _ _ _ = OK _ => fresh "heq_transl_variable"
    | transl_variable _ _ _ _ = Run_Time_Error _ => fresh "heq_transl_variable_RE"
    | fetch_exp_type _ _ = Some _ => fresh "heq_fetch_exp_type"
    | fetch_exp_type _ _ = None => fresh "heq_fetch_exp_type_none"
    | transl_type _ _ = OK _ => fresh "heq_transl_type"
    | transl_type _ _ = Run_Time_Error _ => fresh "heq_transl_type_RE"
    | make_load _ _ = OK _ => fresh "heq_make_load"
    | make_load _ _ = Run_Time_Error _ => fresh "heq_make_load_RE"
    | STACK.fetchG _ _ = Some _ => fresh "heq_SfetchG"
    | STACK.fetchG _ _ = None => fresh "heq_SfetchG_none"
    | do_run_time_check_on_binop _ _ _ (Run_Time_Error _) =>  fresh "h_do_rtc_binop_RE"
    | do_run_time_check_on_binop _ _ _ _ =>  fresh "h_do_rtc_binop"
    | do_run_time_check_on_unop _ _ (Run_Time_Error _) =>  fresh "h_do_rtc_unop_RE"
    | do_run_time_check_on_unop _ _ _ =>  fresh "h_do_rtc_unop"
    | reduce_type _ _ _ = OK _  => fresh "heq_reduce_type"
    | reduce_type _ _ _ = Run_Time_Error _ => fresh "heq_reduce_type_RE"
    | reduce_type _ _ _ = _  => fresh "heq_reduce_type"
    | concrete_type_of_value _ = Run_Time_Error _ => fresh "concrete_type_of_value_RE"
    | concrete_type_of_value _ = OK _ => fresh "concrete_type_of_value"
    | in_bound _ _ _ => fresh "h_inbound"
    | do_division_check _ _ _ => fresh "h_do_division_check"
    | do_division_check _ _ (Run_Time_Error _) => fresh "h_do_division_check_RTE"
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


Ltac eq_same e :=
  match goal with
    | H: e = OK ?t1 , H': e = OK ?t2 |- _ => rewrite H in H'; !inversion H'
  end;
  match goal with
      | H: ?e = ?e |- _ => clear H
  end.

(* Transform hypothesis of the form do_range_check into disequalities. *)
Ltac inv_rtc :=
  repeat
    progress
    (try match goal with
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

Lemma eq_ok: forall v1 v2 v0 x x0,
                     transl_value (Int v1) = OK x ->
                     transl_value (Int v2) = OK x0 ->
                     do_overflow_check v1 (Normal (Int v1)) ->
                     do_overflow_check v2 (Normal (Int v2)) ->
                     Math.eq (Int v1) (Int v2) = Some v0 ->
                     transl_value v0
                     = OK (Values.Val.cmp Integers.Ceq x x0).
Proof.
  !intros.
  !invclear heq.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  simpl.
  !destruct (Z.eq_dec v1 v2).
  - subst.
    rewrite Fcore_Zaux.Zeq_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    rewrite Integers.Int.eq_true.
    reflexivity.
  - subst.
    rewrite Fcore_Zaux.Zeq_bool_false;auto.
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
                     transl_value (Int v1) = OK x ->
                     transl_value (Int v2) = OK x0 ->
                     do_overflow_check v1 (Normal (Int v1)) ->
                     do_overflow_check v2 (Normal (Int v2)) ->
                     Math.ne (Int v1) (Int v2) = Some v0 ->
                     transl_value v0
                     = OK (Values.Val.cmp Integers.Cne x x0).
Proof.
  !intros.
  !invclear heq.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  simpl.
  unfold Values.Val.cmp.
  simpl.
  !destruct (Z.eq_dec v1 v2).
  - subst.
    rewrite Zneq_bool_false;auto.
    rewrite Integers.Int.eq_true.
    reflexivity.
  - subst.
    rewrite Zneq_bool_true;auto.
    rewrite Integers.Int.eq_false.
    + reflexivity.
    + apply repr_inj_neq.
      * inv_rtc.
      * inv_rtc.
      * assumption.
Qed.


Lemma le_ok: forall v1 v2 v0 x x0,
                     transl_value (Int v1) = OK x ->
                     transl_value (Int v2) = OK x0 ->
                     do_overflow_check v1 (Normal (Int v1)) ->
                     do_overflow_check v2 (Normal (Int v2)) ->
                     Math.le (Int v1) (Int v2) = Some v0 ->
                     transl_value v0
                     = OK (Values.Val.cmp Integers.Cle x x0).
Proof.
  !intros.
  !invclear heq.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  simpl.
  !destruct (Z.le_decidable v1 v2).
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
                     transl_value (Int v1) = OK x ->
                     transl_value (Int v2) = OK x0 ->
                     do_overflow_check v1 (Normal (Int v1)) ->
                     do_overflow_check v2 (Normal (Int v2)) ->
                     Math.ge (Int v1) (Int v2) = Some v0 ->
                     transl_value v0
                     = OK (Values.Val.cmp Integers.Cge x x0).
Proof.
  !intros.
  !invclear heq.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  simpl.
  rewrite Z.geb_leb.
  !destruct (Z.le_decidable v2 v1).
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
                     transl_value (Int v1) = OK x ->
                     transl_value (Int v2) = OK x0 ->
                     do_overflow_check v1 (Normal (Int v1)) ->
                     do_overflow_check v2 (Normal (Int v2)) ->
                     Math.lt (Int v1) (Int v2) = Some v0 ->
                     transl_value v0
                     = OK (Values.Val.cmp Integers.Clt x x0).
Proof.
  !intros.
  !invclear heq.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  simpl.
  !destruct (Z.lt_decidable v1 v2).
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
                     transl_value (Int v1) = OK x ->
                     transl_value (Int v2) = OK x0 ->
                     do_overflow_check v1 (Normal (Int v1)) ->
                     do_overflow_check v2 (Normal (Int v2)) ->
                     Math.gt (Int v1) (Int v2) = Some v0 ->
                     transl_value v0
                     = OK (Values.Val.cmp Integers.Cgt x x0).
Proof.
  !intros.
  !invclear heq.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  simpl.
  rewrite Z.gtb_ltb.
  !destruct (Z.lt_decidable v2 v1).
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


(* TODO: maybe we should use do_overflow_check here, we will see. *)

(* strangely this one does not need overflow preconditions *)
Lemma unaryneg_ok :
  forall n v1 v,
    transl_value (Int v1) = OK (Values.Vint n) ->
    Math.unary_operation Unary_Minus (Int v1) = Some (Int v) ->
    Values.Val.negint (Values.Vint n) = Values.Vint (Integers.Int.repr v).
Proof.
  !intros.
  simpl in *.
  !invclear heq.
  !invclear heq_transl_value.
  apply f_equal.
  apply Integers.Int.neg_repr.
Qed.

Lemma add_ok :
  forall n n0 v v1 v2,
    do_range_check v1 min_signed max_signed (Normal (Int v1)) ->
    do_range_check v2 min_signed max_signed (Normal (Int v2)) ->
    do_run_time_check_on_binop Plus (Int v1) (Int v2) (Normal (Int v)) ->
    transl_value (Int v1) = OK (Values.Vint n) ->
    transl_value (Int v2) = OK (Values.Vint n0) ->
    Math.binary_operation Plus (Int v1) (Int v2) = Some (Int v) ->
    Values.Val.add (Values.Vint n) (Values.Vint n0) = Values.Vint (Integers.Int.repr v).
Proof.
  !intros.
  simpl in *.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  !invclear heq.
  apply f_equal.
  !invclear h_do_rtc_binop;simpl in *; try match goal with H: Plus <> Plus |- _ => elim H;auto end.
  clear H heq.
  inv_rtc.
  rewrite min_signed_ok, max_signed_ok in *.
  rewrite Integers.Int.add_signed.
  rewrite !Integers.Int.signed_repr;auto 2.
Qed.

Lemma sub_ok :
  forall n n0 v v1 v2,
    do_range_check v1 min_signed max_signed (Normal (Int v1)) ->
    do_range_check v2 min_signed max_signed (Normal (Int v2)) ->
    do_run_time_check_on_binop Minus (Int v1) (Int v2) (Normal (Int v)) ->
    transl_value (Int v1) = OK (Values.Vint n) ->
    transl_value (Int v2) = OK (Values.Vint n0) ->
    Math.binary_operation Minus (Int v1) (Int v2) = Some (Int v) ->
    Values.Val.sub (Values.Vint n) (Values.Vint n0) = Values.Vint (Integers.Int.repr v).
Proof.
  !intros.
  simpl in *.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  !invclear heq.
  apply f_equal.
  !invclear h_do_rtc_binop;simpl in *; try match goal with H: ?A <> ?A |- _ => elim H;auto end.
  clear H heq.
  inv_rtc.
  rewrite min_signed_ok, max_signed_ok in *.
  rewrite Integers.Int.sub_signed.
  rewrite !Integers.Int.signed_repr;auto 2.
Qed.

Lemma mult_ok :
  forall n n0 v v1 v2,
    do_range_check v1 min_signed max_signed (Normal (Int v1)) ->
    do_range_check v2 min_signed max_signed (Normal (Int v2)) ->
    do_run_time_check_on_binop Multiply (Int v1) (Int v2) (Normal (Int v)) ->
    transl_value (Int v1) = OK (Values.Vint n) ->
    transl_value (Int v2) = OK (Values.Vint n0) ->
    Math.binary_operation Multiply (Int v1) (Int v2) = Some (Int v) ->
    Values.Val.mul (Values.Vint n) (Values.Vint n0) = Values.Vint (Integers.Int.repr v).
Proof.
  !intros.
  simpl in *.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  !invclear heq.
  apply f_equal.
  !invclear h_do_rtc_binop;simpl in *; try match goal with H: ?A <> ?A |- _ => elim H;auto end.
  clear H heq.
  inv_rtc.
  rewrite min_signed_ok, max_signed_ok in *.
  rewrite Integers.Int.mul_signed.
  rewrite !Integers.Int.signed_repr;auto 2.
Qed.

Set Printing Width 80.

(** Compcert division return None if dividend is min_int and divisor
    in -1, because the result would be max_int +1. In Spark's
    semantics the division is performed but then it fails overflow
    checks. *)
(*  How to compile this? probably by performing a check before. *)
Lemma div_ok :
  forall n n0 v v1 v2,
    do_range_check v1 min_signed max_signed (Normal (Int v1)) ->
    do_range_check v2 min_signed max_signed (Normal (Int v2)) ->
    do_run_time_check_on_binop Divide (Int v1) (Int v2) (Normal (Int v)) ->
    transl_value (Int v1) = OK (Values.Vint n) ->
    transl_value (Int v2) = OK (Values.Vint n0) ->
    Math.binary_operation Divide (Int v1) (Int v2) = Some (Int v) ->
    Values.Val.divs (Values.Vint n) (Values.Vint n0) = Some (Values.Vint (Integers.Int.repr v)).
Proof.
  !intros.
  simpl in *.
  !invclear heq_transl_value.
  !invclear heq_transl_value0.
  !invclear heq.
  !invclear h_do_rtc_binop;simpl in *; try match goal with H: ?A <> ?A |- _ => elim H;auto end.
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
      vm_compute in h_le0.
      auto.
    + unfold Integers.Int.divs.
      rewrite !Integers.Int.signed_repr;auto 2.

  - unfold Integers.Int.zero.
    intro abs.
    apply heq_Z_false.
    rewrite <- (Integers.Int.signed_repr v2).
    + rewrite abs.
      rewrite (Integers.Int.signed_repr 0);auto.
      split; intro;discriminate.      
    + split;auto.
Qed.




(* *** Hack to workaround a current limitation of Functional Scheme wrt to Function. *)
(*
This should work, but Funcitonal SCheme does not generate the
inversion stuff currently. So we defined by hand the expanded versions
binopexp and unopexp with Function.

Definition binopexp :=
  Eval unfold
       Math.binary_operation
  , Math.and
  , Math.or
  , Math.eq
  , Math.ne
  , Math.lt
  , Math.le
  , Math.gt
  , Math.ge
  , Math.add
  , Math.sub
  , Math.mul
  , Math.div
  in Math.binary_operation.

Definition unopexp :=
  Eval unfold
       Math.unary_operation, Math.unary_plus, Math.unary_minus, Math.unary_not in Math.unary_operation.

Functional Scheme binopnind := Induction for binopexp Sort Prop.
Functional Scheme unopnind := Induction for unopexp Sort Prop.
*)

Function unopexp (op : unary_operator) (v : value) :=
  match op with
    | Unary_Plus =>
      match v with
        | Undefined => None
        | Int _ => Some v
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Unary_Minus =>
      match v with
        | Undefined => None
        | Int v' => Some (Int (- v'))
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Not =>
      match v with
        | Undefined => None
        | Int _ => None
        | Bool v' => Some (Bool (negb v'))
        | ArrayV _ => None
        | RecordV _ => None
      end
  end.

Function binopexp (op : binary_operator) (v1 v2 : value) :=
  match op with
    | And =>
      match v1 with
        | Undefined => None
        | Int _ => None
        | Bool v1' =>
          match v2 with
            | Undefined => None
            | Int _ => None
            | Bool v2' => Some (Bool (v1' && v2'))
            | ArrayV _ => None
            | RecordV _ => None
          end
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Or =>
      match v1 with
        | Undefined => None
        | Int _ => None
        | Bool v1' =>
          match v2 with
            | Undefined => None
            | Int _ => None
            | Bool v2' => Some (Bool (v1' || v2'))
            | ArrayV _ => None
            | RecordV _ => None
          end
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Equal =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (Zeq_bool v1' v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Not_Equal =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (Zneq_bool v1' v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Less_Than =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (v1' <? v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Less_Than_Or_Equal =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (v1' <=? v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Greater_Than =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (v1' >? v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Greater_Than_Or_Equal =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (v1' >=? v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Plus =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Int (v1' + v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Minus =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Int (v1' - v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Multiply =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Int (v1' * v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Divide =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Int (v1' ÷ v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
  end.

Lemma binopexp_ok: forall x y z, Math.binary_operation x y z = binopexp x y z .
Proof.
  reflexivity.
Qed.

Lemma unopexp_ok: forall x y, Math.unary_operation x y = unopexp x y.
Proof.
  reflexivity.
Qed.

(* *** And of the hack *)

(** [safe_stack s] means that every value in s correct wrt to
    overflows.
TODO: extend with other values than Int: floats, arrays, records. *)
Definition safe_stack s :=
  forall id n,
    STACK.fetchG id s = Some (Int n)
    -> do_overflow_check n (Normal (Int n)).

(** Since unary_plus is a nop, it is an exception to the otherwise
    general property that the spark semantics always returns a checked
    value (or a runtime error). *)
Definition is_not_unaryplus e :=
  match e with
    | E_Unary_Operation x x0 x1 =>
      match x0 with
        | Unary_Plus => False
        | _ => True
      end
    | _ => True
  end.

(** Hypothesis renaming stuff *)
Ltac rename_hyp2 th :=
  match th with
    | is_not_unaryplus _ => fresh "h_isnotunplus"
    | safe_stack _ => fresh "h_safe_stack"
    | _ => rename_hyp1 th
  end.

Ltac rename_hyp ::= rename_hyp2.

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
              is_not_unaryplus e -> 
              eval_expr st s e (Normal (Int n)) ->
              do_overflow_check n (Normal (Int n)).
Proof.
  !intros.
  !inversion h_eval_expr;subst.
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
      simpl in h_isnotunplus.
      elim h_isnotunplus.
Qed.




Lemma transl_expr_ok :
  forall stbl CE locenv g m (s:STACK.stack) (e:expression) (v:value) (e':Cminor.expr)
         (sp: Values.val),
    eval_expr stbl s e (Normal v) ->
    transl_expr stbl CE e = OK e' ->
    match_env stbl s CE sp locenv ->
    exists v',
      transl_value v = OK v'
      /\ Cminor.eval_expr g sp locenv m e' v'
      /\ match v with
           | (Int n) => do_overflow_check n (Normal (Int n))
           | _ => True
         end.
Proof.
  intros until sp.
  intro h_eval_expr.
  remember (Normal v) as Nv.
  revert HeqNv.
  revert v e' sp.
  !induction h_eval_expr;simpl;!intros; subst.
  - !invclear heq.
    !destruct h_match_env.
    destruct (transl_literal_ok g l v0 h_eval_literal sp) as [v' h_and].
    !destruct h_and.
    exists v'.
    repeat split.
    + assumption.
    + constructor.
      assumption.
    + destruct v0;auto.
      eapply eval_literal_overf;eauto.
  - !destruct n; try now inversion heq.
     destruct (transl_variable st CE ast_num i) eqn:heq_trv;simpl in *
     ; (try now inversion heq); rename e into trv_i.
     destruct (fetch_var_type i st) eqn:heq_fetch_type; (try now inversion heq);simpl in heq.
    unfold value_at_addr in heq.
    destruct (transl_type st t) eqn:heq_typ;simpl in *;try now inversion heq.
    !invclear h_eval_name.
    destruct h_match_env.
    specialize (me_vars0 i st ast_num v0 t heq_SfetchG heq_fetch_type).
    decomp me_vars0.
    rename x into e''. rename x0 into v1'. rename x1 into bastyp.
    rename x2 into t'. rename x3 into e'''. rename H6 into h_eval_expr. clear me_vars0.
    unfold make_load in heq.
    destruct (Ctypes.access_mode t0) eqn:heq_acctyp; !invclear heq.
    + exists v1'.
      repeat split.
      * assumption.
      * unfold make_load in heq_make_load.
        eq_same (transl_type st t).
        eq_same( transl_variable st CE ast_num i).
        rewrite heq_acctyp in heq_make_load.
        !invclear heq_make_load.
        apply h_eval_expr.
      * destruct v0;auto.
        eapply me_overflow0.
        eauto.
    + exists v1'.
      repeat split.
      * assumption.
      * unfold make_load in heq_make_load.
        eq_same (transl_type st t).
        eq_same( transl_variable st CE ast_num i).
        rewrite heq_acctyp in heq_make_load.
        !invclear heq_make_load.
        apply h_eval_expr.
      * destruct v0;auto.
        eapply me_overflow0.
        eauto.
    + exists v1'.
      repeat split.
      * assumption.
      * unfold make_load in heq_make_load.
        eq_same (transl_type st t).
        eq_same( transl_variable st CE ast_num i).
        rewrite heq_acctyp in heq_make_load.
        !invclear heq_make_load.
        apply h_eval_expr.
      * destruct v0;auto.
        eapply me_overflow0.
        eauto.
  - discriminate heq0.
  - discriminate heq0.
  - destruct (transl_expr st CE e1) eqn:heq_transl_expr1;(try now inversion heq);simpl in heq.
    destruct (transl_expr st CE e2) eqn:heq_transl_expr2;(try now inversion heq);simpl in heq.
    !invclear heq.
    specialize (IHh_eval_expr1 v1 e sp (refl_equal (Normal v1)) (refl_equal (OK e)) h_match_env).
    specialize (IHh_eval_expr2 v2 e0 sp (refl_equal (Normal v2)) (refl_equal (OK e0)) h_match_env).
    decomp IHh_eval_expr1. clear IHh_eval_expr1. rename H2 into hmatch1.
    decomp IHh_eval_expr2. clear IHh_eval_expr2. rename H2 into hmatch2.
    !inversion h_do_rtc_binop; try !invclear h_overf_check. rename H into h_or_op.
    + destruct h_or_op as [ | h_or_op]; [subst|destruct h_or_op;subst].
      * simpl in heq.
        (* shoul dbe a functional inversion *)
        !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in heq.
        inversion heq;subst.
        exists (Values.Vint (Integers.Int.repr (n+n0))).
        { (repeat split);simpl;auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl.
            !invclear heq_transl_value.
            !invclear heq_transl_value0.
            rewrite (add_ok _ _ (n + n0) n n0);auto.
            + constructor.
              inversion hmatch1.
              assumption.
            + constructor.
              inversion hmatch2.
              assumption.
          - constructor.
            assumption. }
      * simpl in heq.
        destruct v1;try discriminate; destruct v2;try discriminate;simpl in heq.
        inversion heq. subst.
        exists (Values.Vint (Integers.Int.repr (n-n0))).
        { (repeat split);auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl.
            !invclear heq_transl_value.
            !invclear heq_transl_value0.
            rewrite (sub_ok _ _ (n - n0) n n0);auto.
            + constructor.
              inversion hmatch1.
              assumption.
            + constructor.
              inversion hmatch2.
              assumption.
          - constructor.
            assumption. }
      * simpl in heq.
        destruct v1;try discriminate; destruct v2;try discriminate;simpl in heq.
        inversion heq. subst.
        exists (Values.Vint (Integers.Int.repr (n*n0))).
        { (repeat split);auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl.
            !invclear heq_transl_value.
            !invclear heq_transl_value0.
            rewrite (mult_ok _ _ (n * n0) n n0);auto.
            + constructor.
              inversion hmatch1.
              assumption.
            + constructor.
              inversion hmatch2.
              assumption.
          - constructor.
            assumption. }

        
    + !inversion h_do_division_check.
      simpl in heq.
      !invclear heq.
      exists (Values.Vint (Integers.Int.repr (Z.quot v3 v4))).
      { (repeat split);auto.
        - econstructor.
          { apply h_CM_eval_expr. }
          { apply h_CM_eval_expr0. }
          simpl.
          !invclear heq_transl_value.
          !invclear heq_transl_value0.
          rewrite (div_ok _ _ (Z.quot v3 v4) v3 v4);auto.
          + constructor.
            inversion hmatch1.
            assumption.
          + constructor.
            inversion hmatch2.
            assumption.
        - apply Do_Overflow_Check_OK.
          assumption. }
    + destruct op;simpl in *; try match goal with H: ?A <> ?A |- _ => elim H;auto end.
      * clear hmatch1 hmatch2.
        repeat match goal with | H:?X <> ?Y |-_ => clear H end.
        exists (Values.Val.and x x0).
        { repeat split;auto.
          - eapply and_ok;eauto.
          - econstructor;eauto.
          - (* functional inversion *)
            !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in heq.
            inversion heq.
            auto. }
      * clear hmatch1 hmatch2.
        repeat match goal with | H:?X <> ?Y |-_ => clear H end.
        exists (Values.Val.or x x0).
        { repeat split;auto.
          - eapply or_ok;eauto.
          - econstructor;eauto.
          - (* functional inversion *)
            !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in heq.
            inversion heq.
            auto. }

      * repeat match goal with | H:?X <> ?Y |-_ => clear H end.
        destruct v1;try discriminate; destruct v2;try discriminate;simpl in heq.
        !invclear heq.
        exists (Values.Val.cmp Integers.Ceq (Values.Vint (Integers.Int.repr n))
                               (Values.Vint (Integers.Int.repr n0))).
        { repeat split;auto.
          - eapply eq_ok with n n0;auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl in *.
            simpl in heq_transl_value0.
            !invclear heq_transl_value.
            !invclear heq_transl_value0.
            reflexivity. }
      * repeat match goal with | H:?X <> ?Y |-_ => clear H end.
        destruct v1;try discriminate; destruct v2;try discriminate;simpl in heq.
        !invclear heq.
        exists (Values.Val.cmp Integers.Cne (Values.Vint (Integers.Int.repr n))
                               (Values.Vint (Integers.Int.repr n0))).
        { repeat split;auto.
          - eapply neq_ok with n n0;auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl in *.
            !invclear heq_transl_value.
            !invclear heq_transl_value0.
            reflexivity. }
      * repeat match goal with | H:?X <> ?Y |-_ => clear H end.
        destruct v1;try discriminate; destruct v2;try discriminate;simpl in heq.
        !invclear heq.
        exists (Values.Val.cmp Integers.Clt (Values.Vint (Integers.Int.repr n))
                               (Values.Vint (Integers.Int.repr n0))).
        { repeat split;auto.
          - eapply lt_ok with n n0;auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl in *.
            !invclear heq_transl_value.
            !invclear heq_transl_value0.
            reflexivity. }

      * repeat match goal with | H:?X <> ?Y |-_ => clear H end.
        destruct v1;try discriminate; destruct v2;try discriminate;simpl in heq.
        !invclear heq.
        exists (Values.Val.cmp Integers.Cle (Values.Vint (Integers.Int.repr n))
                               (Values.Vint (Integers.Int.repr n0))).
        { repeat split;auto.
          - eapply le_ok with n n0;auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl in *.
            !invclear heq_transl_value.
            !invclear heq_transl_value0.
            reflexivity. }

      * repeat match goal with | H:?X <> ?Y |-_ => clear H end.
        destruct v1;try discriminate; destruct v2;try discriminate;simpl in heq.
        !invclear heq.
        exists (Values.Val.cmp Integers.Cgt (Values.Vint (Integers.Int.repr n))
                               (Values.Vint (Integers.Int.repr n0))).
        { repeat split;auto.
          - eapply gt_ok with n n0;auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl in *.
            !invclear heq_transl_value.
            !invclear heq_transl_value0.
            reflexivity. }

      * repeat match goal with | H:?X <> ?Y |-_ => clear H end.
        destruct v1;try discriminate; destruct v2;try discriminate;simpl in heq.
        !invclear heq.
        exists (Values.Val.cmp Integers.Cge (Values.Vint (Integers.Int.repr n))
                               (Values.Vint (Integers.Int.repr n0))).
        { repeat split;auto.
          - eapply ge_ok with n n0;auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl in *.
            !invclear heq_transl_value.
            !invclear heq_transl_value0.
            reflexivity. }

  - inversion heq0.
  - destruct (transl_expr st CE e) eqn:heq_transl_expr1;simpl in heq;(try now inversion heq).
    specialize (IHh_eval_expr v e0 sp (refl_equal (Normal v)) (refl_equal (OK e0)) h_match_env).
    decomp IHh_eval_expr. clear IHh_eval_expr. rename H2 into hmatch.
    !inversion h_do_rtc_unop;simpl in *; !invclear heq.
    + try !invclear h_overf_check.
      exists (Values.Vint (Integers.Int.repr v')).
      repeat (split;auto).
      * apply eval_Eunop with x;auto.
        simpl.
        destruct v;try discriminate.
        simpl in heq_transl_value.
        apply f_equal.
        !invclear heq_transl_value.
        eapply unaryneg_ok with n;auto.
      * constructor.
        assumption.
    + destruct op;try discriminate.
      * elim hneq;reflexivity.
      * clear hneq.
        simpl in *.
        exists (Values.Val.notbool x).
        { repeat split.
          - eapply not_ok;eauto.
          - !invclear heq.
            apply eval_Eunop with x;auto.
            simpl.
        
        !invclear heq.
        unfold Math.unary_not  in heq0.
        destruct v;try discriminate.
        !invclear heq0.
        simpl in *.
        { destruct n;simpl in *.
          - !invclear heq_transl_value.
            exists (Values.Vint (Integers.Int.repr 0));repeat (split;auto).
            apply eval_Eunop with (Values.Vint (Integers.Int.repr 1)).
            + assumption.
            + simpl.
              reflexivity.
            econstructor;auto.
                               (Values.Vint (Integers.Int.repr 0))).
        { destruct n;simpl in *.

        simpl in heq_transl_value.
        assert (transl_value (Bool (negb n)) = OK (Values.Vint (1-x))).
        simpl in heq0.
        !invclear heq0.
        simpl.
        exists (transl_value (Bool (negb n))).
        simpl.
        exists (Values.Vint (Integers.Int.repr )).
        eapply not_ok.

        destruct 
    

    
        
            
            
        
        
        exists (Values.Vint (Integers.Int.repr (n*n0))).
        { (repeat split);auto.
          - econstructor.
            { apply h_CM_eval_expr. }
            { apply h_CM_eval_expr0. }
            simpl.
            !invclear heq_transl_value.


            inversion 
          - XXX

 !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
            !invclear heq.
            destruct n;destruct n0;simpl
            ;inversion heq_transl_value
            ;inversion heq_transl_value0
            ; reflexivity.
          - econstructor;eauto.
          - !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
            !invclear heq.
            trivial. }
      * clear hmatch1 hmatch2.
        repeat match goal with | H:?X <> ?Y |-_ => clear H end.
        exists (Values.Val.or x x0).
        { repeat split.
          - !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
            !invclear heq.
            destruct n;destruct n0;simpl
            ;inversion heq_transl_value
            ;inversion heq_transl_value0
            ; reflexivity.
          - econstructor;eauto.
          - !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
            !invclear heq.
            trivial. }

(*         XXXX etc. TRansformer tout ça en lemmes. *)
      * 



            !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
            !invclear heq.
            destruct n;destruct n0;simpl
            ;!invclear heq_transl_value
            ;!invclear heq_transl_value0
            ;subst.
            simpl.
            assumption.
            ; reflexivity.
          - 
        }
        

      !inversion h_do_rtc_binop.
       * decompose [or] H;subst; try match goal with H: ?A <> ?A |- _ => elim H;auto end.
       * match goal with H: ?A <> ?A |- _ => elim H;auto end.
       * 
      destruct (eval_binop (transl_binop op) x x0 m) eqn:heq_eval.
      Focus 2.
      * destruct op;simpl in heq_eval;inversion heq_eval.
        try match goal with H: ?A <> ?A |- _ => elim H;auto end.
      * !inversion h_do_rtc_binop.



        destruct op;simpl in heq_eval;!invclear heq_eval;subst;try match goal with H: ?A <> ?A |- _ => elim H;auto end.

        !inversion h_do_rtc_binop.
        exists (Values.Val.and x x0).
        



      * destruct v1. ;try discriminate; destruct v2;try discriminate;simpl in *.
        { exists (Values.Val.and x x0);repeat split;simpl;auto.
          - destruct n;destruct n0;simpl in *
            ; !invclear heq_transl_value; !invclear heq_transl_value0;simpl.
inversion heq.
            
            reflexivity.
        }
        
        
      { (repeat split);auto.
        - econstructor.
          { apply h_CM_eval_expr. }
          { apply h_CM_eval_expr0. }
          simpl.
          !invclear heq_transl_value.
            !invclear heq_transl_value0.
            rewrite (mult_ok _ _ (n * n0) n n0);auto.
            + constructor.
              inversion hmatch1.
              assumption.
            + constructor.
              inversion hmatch2.
              assumption.
          - constructor.
            assumption. }

      exists (Int n).
      
      





  - constructor.
          assumption. }

      inversion H.
      inversion H2.
      subst v0.
      rewrite add_ok in 
      



      inversion h_overf_check;subst;simpl.
      exists (Values.Vint (Integers.Int.repr v)).
      split;auto.
      econstructor.
      apply h_CM_eval_expr.
      apply h_CM_eval_expr0.
      decomp H0;subst;simpl.
      rewrite add_ok.

      * .
      simpl.


    XXX (* gérer les différents cas de do_run_time_check_on_binop ... (Normal v). *)
    

              exists v.
    + inversion heq.
      simpl in *.
      unfold id in *.
      apply IHh_eval_expr;auto.
      
    simpl in heq.
    (try now inversion heq). ;simpl in heq.



    destruct (transl_variable rstbl CE a i) eqn:heq_trv;simpl in *; (try now inversion heq); rename e into trv_i.
    destruct (fetch_exp_type a rstbl) eqn:heq_fetch; try now inversion heq.
    unfold value_at_addr in heq.
    destruct (transl_type rstbl t) eqn:heq_typ;simpl in *;try now inversion heq.
    !invclear h_eval_name.
    unfold make_load in heq.
    destruct (Ctypes.access_mode t0) eqn:heq_acctyp; !invclear heq.
    + destruct h_match_env.

      destruct (me_vars0 i rstbl a trv_i v t heq_SfetchG) as [v' me_vars1].
      * admit. (* propriété de cohérence de la pile, c'est du typage. *)
      * assumption.
      * clear me_vars0.
        decomp me_vars1.
        exists v'.
        { split.
          - assumption.
          - unfold make_load in heq_make_load. rewrite heq_acctyp in heq_make_load.
        reflexivity.
    + destruct h_match_env.
      eapply (me_vars0 i rstbl a );try now eassumption.
      * admit. (* propriété de cohérence de la pile, c'est du typage. *)
      * unfold make_load. rewrite heq_acctyp.
        reflexivity.
    + destruct h_match_env.
      eapply (me_vars0 i rstbl a );try now eassumption.
      * admit. (* propriété de cohérence de la pile, c'est du typage. *)
      * unfold make_load. rewrite heq_acctyp.
        reflexivity.
        
  - destruct (transl_expr rstbl CE e1) eqn:heq_tr_e1;try now inversion heq.
    destruct (transl_expr rstbl CE e2) eqn:heq_tr_e2;try now inversion heq.
    simpl in heq.
    !invclear heq.
    !invclear h_eval_expr.
    !destruct (transl_value v1).
    
    !inversion h_do_rtc_binop.
    + !invclear heq.
      !invclear heq.





(*

    Lemma transl_name_ok :
      forall a a0 i e e' t t' v v' s sp,
        transl_variable rstbl CE a i = OK e ->
        fetch_exp_type a rstbl = Some t ->
        transl_type rstbl t = OK t' ->
        make_load e t' = OK e' ->
        match_env s CE sp locenv ->
        transl_value v = OK v' ->
        eval_name stbl s (E_Identifier a0 i) (Normal v) ->
        Cminor.eval_expr g sp locenv m e' v'.
    Proof.
      !intros.
    Qed.


 *)
(* ********************************************** *)
