
Require Import Utf8.
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
Require Import Integers.

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
    | compute_chnk _ ?name = OK ?chk => fresh "heq_compute_chnk_" name "_" chk
    | compute_chnk _ ?name = ?chk => fresh "heq_compute_chnk_" name "_" chk
    | compute_chnk _ ?name = _ => fresh "heq_compute_chnk_" name
    | compute_chnk _ _ = _ => fresh "heq_compute_chnk"
    | symboltable.fetch_exp_type _ _ = _ => fresh "heq_fetch_exp_type"
    | symboltable.fetch_exp_type _ _ = Error _ => fresh "heq_fetch_exp_type_ERR"
    | fetch_exp_type _ _ = _ => fresh "heq_fetch_exp_type" (* symboltable.fetch_exp_type *)
    | eval_expr _ _ _ (Run_Time_Error _) => fresh "h_eval_expr_RE"
    | eval_expr _ _ _ (Normal ?v) => fresh "h_eval_expr_" v
    | eval_expr _ _ _ ?v => fresh "h_eval_expr_" v
    | eval_expr _ _ _ _ => fresh "h_eval_expr"
    | eval_name _ _ _ (Run_Time_Error _) => fresh "h_eval_name_RE"
    | eval_name _ _ _ (Normal ?v) => fresh "h_eval_name_" v
    | eval_name _ _ _ ?v => fresh "h_eval_name_" v
    | eval_name _ _ _ _ => fresh "h_eval_name"
    | do_overflow_check _ (Run_Time_Error _) => fresh "h_overf_check_RE"
    | do_overflow_check _ _ => fresh "h_overf_check"
    | do_range_check _ _ _ (Run_Time_Error _) => fresh "h_do_range_check_RE"
    | do_range_check _ _ _ _ => fresh "h_do_range_check"
    | do_run_time_check_on_binop _ _ _ (Run_Time_Error _) => fresh "h_do_rtc_binop_RTE"
    | do_run_time_check_on_binop _ _ _ _ => fresh "h_do_rtc_binop"
    | Ctypes.access_mode ?x = _ => fresh "h_access_mode_" x
    | Ctypes.access_mode _ = _ => fresh "h_access_mode"
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
    | Cminor.eval_expr _ _ _ _ ?x _ => fresh "h_CM_eval_expr_" x
    | Cminor.eval_expr _ _ _ _ _ _ => fresh "h_CM_eval_expr"
    | transl_value _ Error _ => fresh "heq_transl_value_RE"
    | transl_value _ _ => fresh "heq_transl_value"
    | transl_variable _ _ _ _ = Error _ => fresh "heq_transl_variable_RE"
    | transl_variable _ _ _ _ = _ => fresh "heq_transl_variable"
    | fetch_exp_type _ _ = Some _ => fresh "heq_fetch_exp_type"
    | fetch_exp_type _ _ = None => fresh "heq_fetch_exp_type_none"
    | transl_type _ _ = Error _ => fresh "heq_transl_type_RE"
    | transl_type _ _ = _ => fresh "heq_transl_type"
    | transl_basetype _ _ = Error _ => fresh "heq_transl_basetype_RE"
    | transl_basetype _ _ = _ => fresh "heq_transl_basetype"
    | build_loads ?n ?z = _ => fresh "heq_build_loads_" n "_" z
    | build_loads _ _ = _ => fresh "heq_build_loads"
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

    | Memory.Mem.store ?chk ?m ?blk ?n ?v = None => fresh "heq_store_" v "_none"
    | Memory.Mem.store ?chk ?m ?blk ?n ?v = OK ?m2 => fresh "heq_store_" v "_" m2
    | Memory.Mem.store ?chk ?m ?blk ?n ?v = ?m2 => fresh "heq_store_" v "_" m2
    | Memory.Mem.store ?chk ?m ?blk ?n ?v = ?m2 => fresh "heq_store_" v
    | Memory.Mem.store ?chk ?m ?blk ?n ?v = ?m2 => fresh "heq_store"

    | Memory.Mem.storev ?chk ?m ?vaddr ?v = None => fresh "heq_storev_" v "_none"
    | Memory.Mem.storev ?chk ?m ?vaddr ?v = OK ?m2 => fresh "heq_storev_" v "_" m2
    | Memory.Mem.storev ?chk ?m ?vaddr ?v = ?m2 => fresh "heq_storev_" v "_" m2
    | Memory.Mem.storev ?chk ?m ?vaddr ?v = ?m2 => fresh "heq_storev_" v
    | Memory.Mem.storev ?chk ?m ?vaddr ?v = ?m2 => fresh "heq_storev"


    | transl_expr ?stbl ?CE ?e = Error => fresh "heq_tr_expr_none"
    | transl_expr ?stbl ?CE ?e = OK ?r => fresh "heq_tr_expr_" e
    | transl_expr ?stbl ?CE ?e = ?r => fresh "heq_tr_expr"


    (* TODO: remove when we remove type_of_name by the real one. *)
    | type_of_name _ _ = Error _ => fresh "heq_type_of_name_ERR"
    | type_of_name _ _ = _ => fresh "heq_type_of_name"
  end.


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

Ltac rename_hyp ::= rename_hyp1.

Lemma transl_literal_ok1 :
  forall g (l:literal) v,
    eval_literal l (Normal v) ->
    forall sp t_v,
      eval_constant g sp (transl_literal l) = Some t_v ->
      transl_value v t_v.
Proof.
  !intros.
  !destruct l;simpl in *;eq_same_clear.
  - !inversion h_eval_literal.
    !inversion h_overf_check.
    constructor.
  - destruct b;simpl in *;eq_same_clear.
    + !inversion h_eval_literal;constructor.
    + !inversion h_eval_literal;constructor.
Qed.

Lemma transl_literal_ok2 :
  forall g (l:literal) v,
    eval_literal l (Normal v) ->
    forall sp t_v,
      transl_value v t_v ->
      eval_constant g sp (transl_literal l) = Some t_v.
Proof.
  !intros.
  !destruct l;simpl in *;eq_same_clear.
  - !inversion h_eval_literal.
    !inversion h_overf_check.
    !inversion heq_transl_value.
    reflexivity.
  - destruct b;simpl in *;eq_same_clear.
    + !inversion h_eval_literal.
      !inversion heq_transl_value.
      reflexivity.
    + !inversion h_eval_literal.
      !inversion heq_transl_value.
      reflexivity.
Qed.

Lemma transl_literal_ok :
  forall g (l:literal) v,
    eval_literal l (Normal v) ->
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
                     transl_value v1 x ->
                     Math.unary_not v1 = Some v0 ->
                     transl_value v0 (Values.Val.notbool x).
Proof.
  !intros.
  !destruct v1;try discriminate;simpl in *;eq_same_clear.
  !destruct n;simpl in *
  ; inversion heq_transl_value
  ; constructor.
Qed.


Lemma and_ok: forall v1 v2 v0 x x0,
                     transl_value v1 x ->
                     transl_value v2 x0 ->
                     Math.and v1 v2 = Some v0 ->
                     transl_value v0 (Values.Val.and x x0).
Proof.
  !intros.
  !destruct v1;simpl in *;try discriminate; !destruct v2;simpl in *;try discriminate
  ;eq_same_clear.
  destruct n;destruct n0;simpl
  ;inversion heq_transl_value
  ;inversion heq_transl_value0
  ; constructor.
Qed.

Lemma or_ok: forall v1 v2 v0 x x0,
                     transl_value v1 x ->
                     transl_value v2 x0 ->
                     Math.or v1 v2 = Some v0 ->
                     transl_value v0 (Values.Val.or x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *;eq_same_clear.
  destruct n;destruct n0;simpl
  ;inversion heq_transl_value
  ;inversion heq_transl_value0
  ; constructor.
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
               transl_value v1 x ->
               transl_value v2 x0 ->
               Math.eq v1 v2 = Some v0 ->
               transl_value v0 (Values.Val.cmp Integers.Ceq x x0).
Proof.
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *;eq_same_clear.
  !destruct (Z.eq_dec n n0).
  - subst n0.
    inversion heq_transl_value0;subst;simpl.
    inversion heq_transl_value;subst;simpl.
    rewrite Fcore_Zaux.Zeq_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    rewrite Integers.Int.eq_true.
    constructor.
  - rewrite Fcore_Zaux.Zeq_bool_false;auto.
    unfold Values.Val.cmp.
    inversion heq_transl_value0;subst;simpl.
    inversion heq_transl_value;subst;simpl.
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
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *;eq_same_clear.
  !destruct (Z.eq_dec n n0).
  - subst.
    rewrite Zneq_bool_false;auto.
    unfold Values.Val.cmp.
    inversion heq_transl_value0;subst;simpl.
    inversion heq_transl_value;subst;simpl.
    rewrite Integers.Int.eq_true.
    simpl.
    constructor.
  - rewrite Zneq_bool_true;auto.
    unfold Values.Val.cmp.
    inversion heq_transl_value0;subst;simpl.
    inversion heq_transl_value;subst;simpl.
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
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *;eq_same_clear.
  inversion heq_transl_value0;subst;simpl.
  inversion heq_transl_value;subst;simpl.
  !destruct (Z.le_decidable n n0).
  - rewrite Fcore_Zaux.Zle_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_false.
    + constructor.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
      auto with zarith.
  - { rewrite Fcore_Zaux.Zle_bool_false.
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
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  eq_same_clear.
  inversion heq_transl_value0;subst;simpl.
  inversion heq_transl_value;subst;simpl.
  rewrite Z.geb_leb.
  !destruct (Z.le_decidable n0 n).
  - rewrite Fcore_Zaux.Zle_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_false.
    + constructor.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
      auto with zarith.
  - { rewrite Fcore_Zaux.Zle_bool_false.
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
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  eq_same_clear.
  inversion heq_transl_value0;subst;simpl.
  inversion heq_transl_value;subst;simpl.
  simpl.
  !destruct (Z.lt_decidable n n0).
  - rewrite Fcore_Zaux.Zlt_bool_true;auto.
    unfold Values.Val.cmp.
    subst.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_true.
    + constructor.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
  - { rewrite Fcore_Zaux.Zlt_bool_false.
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
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  eq_same_clear.
  inversion heq_transl_value0;subst;simpl.
  inversion heq_transl_value;subst;simpl.
  rewrite Z.gtb_ltb.
  !destruct (Z.lt_decidable n0 n).
  - rewrite Fcore_Zaux.Zlt_bool_true;auto.
    unfold Values.Val.cmp.
    subst.
    simpl.
    unfold Integers.Int.lt.
    rewrite Coqlib.zlt_true.
    + constructor.
    + rewrite Integers.Int.signed_repr;inv_rtc.
      rewrite Integers.Int.signed_repr;inv_rtc.
  - { rewrite Fcore_Zaux.Zlt_bool_false.
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
Lemma unaryneg_ok :
  forall n v1 v,
    transl_value v1 n ->
    Math.unary_operation Unary_Minus v1 = Some v ->
    transl_value v (Values.Val.negint n).
Proof.
  !intros.
  simpl in *.
  destruct v1;simpl in *;try discriminate.
  eq_same_clear.
  inversion heq_transl_value.
  simpl.
  rewrite Integers.Int.neg_repr.
  constructor.
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
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v (Values.Val.add n1 n2).
Proof.
  !intros.
  !destruct v1;simpl in *;try discriminate;eq_same_clear;subst;try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc.
  inversion heq_transl_value0;subst;simpl.
  inversion heq_transl_value;subst;simpl.
  !invclear h_do_rtc_binop;simpl in *; eq_same_clear. 
  !invclear h_overf_check.
  int_simpl;auto;inv_rtc.
  constructor.
Qed.

Lemma sub_ok :
  forall v v1 v2 n1 n2,
    check_overflow_value v1 -> 
    check_overflow_value v2 -> 
    do_run_time_check_on_binop Minus v1 v2 (Normal v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v (Values.Val.sub n1 n2).
Proof.
  !intros.
  !destruct v1;simpl in *;try discriminate;eq_same_clear;subst; try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc.
  inversion heq_transl_value0;subst;simpl.
  inversion heq_transl_value;subst;simpl.
  !invclear h_do_rtc_binop;simpl in *; eq_same_clear. 
  !invclear h_overf_check.
  int_simpl;auto;inv_rtc.
  constructor.
Qed.

Lemma mult_ok :
  forall v v1 v2 n1 n2,
    check_overflow_value v1 -> 
    check_overflow_value v2 -> 
    do_run_time_check_on_binop Multiply v1 v2 (Normal v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v (Values.Val.mul n1 n2).
Proof.
  !intros.
  simpl in *.
  !destruct v1;simpl in *;try discriminate;eq_same_clear;subst; try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc.
  inversion heq_transl_value0;subst;simpl.
  inversion heq_transl_value;subst;simpl.
  !invclear h_do_rtc_binop;simpl in *; eq_same_clear. 
  !invclear h_overf_check.
  int_simpl;auto;inv_rtc.
  constructor.
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
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v n ->
    Values.Val.divs n1 n2 = Some n.
Proof.
  !intros.
  simpl in *.
  !destruct v1;subst;simpl in *;try discriminate;try now inv_rtc.
  !destruct v2;subst;simpl in *; try discriminate;try now inv_rtc.
  inversion heq_transl_value0;subst;simpl.
  inversion heq_transl_value1;subst;simpl.
  rename n0 into v1.
  rename n3 into v2.
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
    destruct (Int.eq (Int.repr v1)
                              (Int.repr Int.min_signed) &&
                              Int.eq (Int.repr v2) Int.mone)
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
      inversion heq_transl_value;subst;simpl.
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

Lemma transl_value_det: forall v tv1 tv2,
    transl_value v tv1 -> transl_value v tv2 -> tv1 = tv2.
Proof.
!intros.
  inversion heq_transl_value0; inversion heq_transl_value;subst;auto;inversion H1;auto.
                                                                                    Qed.
Tactic Notation "decomp" constr(h) :=
  !! (fun x => decompose [and ex or] x; try clear x) h.

Lemma transl_value_tot: forall v,
        (forall y:nat,(exists b, v = Bool b \/ exists n, v = Int n))
          -> exists tv, transl_value v tv.
Proof.
  !intros.
  decomp (H 0%nat);subst.
  - destruct x;eexists;econstructor.
  - eexists;econstructor.
Qed.

Lemma binary_operator_ok:
  forall op (n n1 n2 : Values.val) (v v1 v2 : value),
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop op v1 v2 (Normal v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v n ->
    forall m, Cminor.eval_binop (transl_binop op) n1 n2 m = Some n.
Proof.
  !intros.
  assert (h_rtc:=do_run_time_check_on_binop_ok _ _ _ _ h_do_rtc_binop).
  destruct op;simpl in *.
  - eapply (and_ok v1 v2 v n1 n2) in h_rtc;auto.
    rewrite (transl_value_det _ _ _ heq_transl_value h_rtc);reflexivity.
  - eapply (or_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value h_rtc);reflexivity.

  - eapply (eq_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value h_rtc);reflexivity.
  - eapply (neq_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value h_rtc);reflexivity.
  - eapply (lt_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value h_rtc);reflexivity.
  - eapply (le_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value h_rtc);reflexivity.
  - eapply (gt_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value h_rtc);reflexivity.
  - eapply (ge_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value h_rtc);reflexivity.
  - generalize (add_ok _ _ _ _ _
                       h_check_overf0 h_check_overf
                       h_do_rtc_binop heq_transl_value1 heq_transl_value0).
    intro h.
    rewrite (transl_value_det _ _ _ heq_transl_value h);reflexivity.
  - generalize (sub_ok _ _ _ _ _
                       h_check_overf0 h_check_overf
                       h_do_rtc_binop heq_transl_value1 heq_transl_value0).
    intro h.
    rewrite (transl_value_det _ _ _ heq_transl_value h);reflexivity.
  - generalize (mult_ok _ _ _ _ _
                       h_check_overf0 h_check_overf
                       h_do_rtc_binop heq_transl_value1 heq_transl_value0).
    intro h.
    rewrite (transl_value_det _ _ _ heq_transl_value h);reflexivity.
  - generalize (div_ok _ _ _ _ _ _
                       h_check_overf0 h_check_overf
                       h_do_rtc_binop heq_transl_value1 heq_transl_value0
                       heq_transl_value).
    intro h.
    assumption.
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
    | safe_stack ?s => fresh "h_safe_stack_" s
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
    eapply h_safe_stack_s;eauto.
  - give_up. (* Arrays *)
  - give_up. (* records *)
Admitted.

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
  revert h_safe_stack_s.
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
      !invclear heq2.
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


Definition stack_complete stbl s CE :=
  forall a nme addrof_nme,
    transl_variable stbl CE a nme = OK addrof_nme
    -> exists v, eval_name stbl s (E_Identifier a nme) (Normal v).


Definition stack_no_null_offset stbl CE :=
  forall a nme δ_lvl δ_id,
    transl_variable stbl CE a nme = OK (build_loads δ_lvl δ_id) ->
    4 <= Int.unsigned (Int.repr δ_id).


Definition stack_localstack_aligned locenv g m :=
  forall b δ_lvl v,
    Cminor.eval_expr g b locenv m (build_loads_ δ_lvl) v
    -> exists b', v = Values.Vptr b' Int.zero.

Definition stack_match st s CE sp locenv g m :=
  forall nme v addrof_nme load_addrof_nme typ_nme cm_typ_nme,
    eval_name st s nme (Normal v) ->
    type_of_name st nme = OK typ_nme ->
    transl_name st CE nme = OK addrof_nme ->
    transl_type st typ_nme = OK cm_typ_nme ->
    make_load addrof_nme cm_typ_nme = OK load_addrof_nme ->
    exists v_t,
      (transl_value v v_t /\
       Cminor.eval_expr g sp locenv m load_addrof_nme v_t).

(* Variable addresses are all disjoint *)
Definition stack_separate st CE sp locenv g m :=
  forall
    nme nme' addrof_nme addrof_nme'
    typ_nme typ_nme'  cm_typ_nme cm_typ_nme'
    k₁ δ₁ k₂ δ₂ chnk₁ chnk₂ ,
    type_of_name st nme = OK typ_nme ->
    type_of_name st nme' = OK typ_nme' ->
    transl_name st CE nme = OK addrof_nme ->
    transl_name st CE nme' = OK addrof_nme' ->
    transl_type st typ_nme = OK cm_typ_nme ->
    transl_type st typ_nme' = OK cm_typ_nme' ->
    Cminor.eval_expr g sp locenv m addrof_nme (Values.Vptr k₁ δ₁) ->
    Cminor.eval_expr g sp locenv m addrof_nme' (Values.Vptr k₂ δ₂) ->
    Ctypes.access_mode cm_typ_nme  = Ctypes.By_value chnk₁ ->
    Ctypes.access_mode cm_typ_nme' = Ctypes.By_value chnk₂ ->
    nme <> nme' ->
    (k₂ <> k₁
     \/ Int.unsigned δ₂ + Memdata.size_chunk chnk₂ <= Int.unsigned δ₁
     \/ Int.unsigned δ₁ + Memdata.size_chunk chnk₁ <= Int.unsigned δ₂).

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

Record match_env (st:symboltable) (s: STACK.stack)
       (CE:compilenv) (sp:Values.val) (locenv: Cminor.env)
       (g:genv)(m:Memory.Mem.mem): Prop :=
  mk_match_env {
      me_stack_match: stack_match st s CE sp locenv g m;
      me_stack_complete: stack_complete st s CE;
      me_stack_separate: stack_separate st CE sp locenv g m;
      me_stack_localstack_aligned: stack_localstack_aligned locenv g m;
      me_stack_no_null_offset: stack_no_null_offset st CE;
      me_overflow: safe_stack s
    }.


(** Hypothesis renaming stuff *)
Ltac rename_hyp3 h th :=
  match th with
  | match_env _ _ _ _ _ _ _ => fresh "h_match_env"
  | stack_match _ ?s _ _ _ _ ?m => fresh "h_stk_mtch_" s "_" m
  | stack_match _ _ _ _ _ _ _ => fresh "h_stk_mtch"
  | stack_complete _ ?s ?CE => fresh "h_stk_cmpl_" s "_" CE
  | stack_complete _ ?s _ => fresh "h_stk_cmpl_" s
  | stack_complete _ _ _ => fresh "h_stk_cmpl"
  | stack_localstack_aligned _ ?g ?m => fresh "h_aligned_" g "_" m
  | stack_localstack_aligned _ _ ?m => fresh "h_aligned_" m
  | stack_localstack_aligned _ ?g _ => fresh "h_aligned_" g
  | stack_no_null_offset _ _ => fresh "h_nonul_ofs"
  | stack_no_null_offset _ ?CE => fresh "h_nonul_ofs_" CE
  | stack_no_null_offset ?s _ => fresh "h_nonul_ofs_" s
  | stack_no_null_offset _ _ => fresh "h_nonul_ofs"
  | stack_separate _ ?CE _ _ _ ?m => fresh "h_separate_" CE "_" m
  | stack_separate _ _ _ _ _ ?m => fresh "h_separate_" m
  | stack_separate _ ?CE _ _ _ _ => fresh "h_separate_" CE
  | stack_separate _ _ _ _ _ _ => fresh "h_separate"
  | _ => rename_hyp2' h th
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
    | H: id (CompilEnv.frameG ?X _ = Some (h, _)) |- _ => fresh "lvl_" X
    | H: CompilEnv.frameG ?X _ = Some (h, _) |- _ => fresh "lvl_" X
    | H: id (CompilEnv.frameG ?X _ = Some (_, h)) |- _ => fresh "fr_" X
    | H: CompilEnv.frameG ?X _ = Some (_, h) |- _ => fresh "fr_" X
    | H: id (CompilEnv.fetchG ?X _ = Some h) |- _ => fresh "δ_" X
    | H: CompilEnv.fetchG ?X _ = Some h |- _ => fresh "δ_" X
    | H: id (CompilEnv.fetchG ?X _ = h) |- _ => fresh "δ_" X
    | H: CompilEnv.fetchG ?X _ = h |- _ => fresh "δ_" X
    | _ => rename_hyp3 h th
  end.
Ltac rename_hyp ::= rename_hyp4.

(* Property of the translation: Since chain variables have always zero
   offset, the offset of a variable in CE is the CMinor one. *)
Lemma eval_build_loads_offset: forall g stkptr locenv m δ_lvl δ_id b ofs,
    stack_localstack_aligned locenv g m ->
    Cminor.eval_expr g stkptr locenv m (build_loads δ_lvl δ_id) (Values.Vptr b ofs) ->
    ofs = Int.repr δ_id.
Proof.
  !intros.
  unfold build_loads in *.
  !inversion h_CM_eval_expr.
  !inversion h_CM_eval_expr0.
  simpl in *.
  edestruct h_aligned_g_m;eauto.
  subst.
  destruct v2;try discriminate.
  simpl in *.
  !invclear heq;subst.
  inversion h_eval_constant.
  rewrite Int.add_zero_l.
  reflexivity.
Qed.


(* Property of the translation: Since chain variables have always zero
   offset, the offset of a variable in CE is more than 3. *)
Lemma eval_build_loads_offset_non_null_var: forall stbl CE g stkptr locenv m nme a bld_lds b ofs,
    stack_no_null_offset stbl CE ->
    stack_localstack_aligned locenv g m ->
    transl_variable stbl CE a nme = OK bld_lds ->
    Cminor.eval_expr g stkptr locenv m bld_lds (Values.Vptr b ofs) ->
    4 <= Int.unsigned ofs.
Proof.
  !intros.
  functional inversion heq_transl_variable;subst.
  assert (ofs=(Int.repr n)). {
    eapply (eval_build_loads_offset _ _ _ _ _ _ _ ofs);eauto. }
  subst.
  eapply h_nonul_ofs;eauto.
Qed.



(* Is this true? *)
(*Axiom CM_eval_bigstep_det: forall g sp locenv m e v v',
    Cminor.eval_expr g sp locenv m e v ->
    Cminor.eval_expr g sp locenv m e v' ->
    v = v'.*)



Lemma transl_expr_ok :
  forall stbl CE (e:expression) (e':Cminor.expr),
    transl_expr stbl CE e = OK e' ->
    forall locenv g m (s:STACK.stack)  (v:value) stkptr,
    eval_expr stbl s e (Normal v) ->
    match_env stbl s CE stkptr locenv g m ->
    exists v_t,
      (transl_value v v_t /\ Cminor.eval_expr g stkptr locenv m e' v_t).
Proof.
  intros until e.
  !functional induction (transl_expr stbl CE e);try discriminate;simpl; !intros;
  !invclear h_eval_expr_v;eq_same_clear.
  - inversion h_eval_literal;subst.
    + !destruct v0.
      * eexists;split;!intros;econstructor;eauto.
      * eexists;split;!intros;econstructor;eauto.
    + eexists;split;!intros.
      * eapply (transl_literal_ok g _ _ h_eval_literal stkptr).
        econstructor.
      * constructor.
        reflexivity.
  - unfold value_at_addr in heq.
    destruct (transl_type stbl type_id) eqn:heq_transl_type;simpl in *.
    + !destruct h_match_env.
      eapply h_stk_mtch_s_m;eauto.
    + discriminate.
  - rename x into e1'.
    rename x0 into e2'.
    specialize (IHr e1' heq_tr_expr_e1 locenv g m s v1 stkptr h_eval_expr_v1 h_match_env).
    specialize (IHr0 e2' heq_tr_expr_e2 locenv g m s v2 stkptr h_eval_expr_v2 h_match_env).
    decomp IHr.
    decomp IHr0.
    rename x into v1'.
    rename x0 into v2'.
    assert (hex:(exists b, v = Bool b) ∨ (exists n, v = Int n)). {
      apply do_run_time_check_on_binop_ok in h_do_rtc_binop.
      rewrite binopexp_ok in h_do_rtc_binop.
      functional inversion h_do_rtc_binop;subst;eq_same_clear
      ;try contradiction;eauto. }
    decomp hex;subst.
    
    + destruct x; eexists;(split;[econstructor;eauto|]).
      * eapply eval_Ebinop;try econstructor;eauto.
        { eapply binary_operator_ok with (v:=(Bool true));try (now econstructor);eauto.
          + eapply eval_expr_overf2;eauto.
            eapply h_match_env.(me_overflow stbl s CE stkptr locenv g m).
          + eapply eval_expr_overf2;eauto.
            eapply h_match_env.(me_overflow stbl s CE stkptr locenv g m). }
      * eapply eval_Ebinop;try econstructor;eauto.
        { eapply binary_operator_ok with (v:=(Bool false));try (now econstructor);eauto.
          + eapply eval_expr_overf2;eauto.
            eapply h_match_env.(me_overflow stbl s CE stkptr locenv g m).
          + eapply eval_expr_overf2;eauto.
            eapply h_match_env.(me_overflow stbl s CE stkptr locenv g m). }
    + eexists;(split;[econstructor;eauto|]).
      eapply eval_Ebinop;try econstructor;eauto.
      { eapply binary_operator_ok with (v:=(Int x));try (now econstructor);eauto.
        + eapply eval_expr_overf2;eauto.
          eapply h_match_env.(me_overflow stbl s CE stkptr locenv g m).
        + eapply eval_expr_overf2;eauto.
          eapply h_match_env.(me_overflow stbl s CE stkptr locenv g m). }
  - (* Unary minus *)
    simpl in heq.
    eq_same_clear.
    rename e0 into e.
    rename x into e'.
    specialize (IHr e' heq_tr_expr_e0 locenv g m s v0 stkptr
                    h_eval_expr_v0 h_match_env).
    decomp IHr.
    rename x into v0'.
    !invclear h_do_rtc_unop;eq_same_clear.
    !invclear h_overf_check.
    eexists.
    split.
    * econstructor.
    * assert (h:=unaryneg_ok v0' v0 (Int v') heq_transl_value heq).
      econstructor;eauto.
      simpl.
      inversion h.
      reflexivity.
  (* Not *)
  - !invclear h_do_rtc_unop;simpl in *;try eq_same_clear.
    specialize (IHr _ heq_tr_expr_e0 _ _ _ _ _ _ h_eval_expr_v0 h_match_env).
    decomp IHr.
    rename x0 into v0'.
    generalize (not_ok _ _ _ heq_transl_value heq).
    !intro.
    exists (Values.Val.notbool v0').
    split;auto.
    econstructor;simpl in *;eauto.
    + econstructor;eauto.
      reflexivity.
    + destruct v0';simpl in *;try (inversion heq_transl_value;fail).
      unfold  Values.Val.cmp.
      simpl.
      unfold Values.Val.of_bool.
      reflexivity.
Qed.


(** Hypothesis renaming stuff *)
Ltac rename_hyp5 th :=
  match th with
    | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ None  => fresh "h_exec_stmt_None"
    | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ _  => fresh "h_exec_stmt"
    | _ => rename_hyp4 th
  end.

Ltac rename_hyp ::= rename_hyp5.

      


Axiom expression_dec: forall e1 e2:expression, ({e1=e2} + {e1<>e2}).
Axiom name_dec: forall e1 e2:name, {e1=e2} + {e1<>e2}. 

Import STACK.

Axiom det_eval_expr: forall g stkptr locenv m e v v',
                       Cminor.eval_expr g stkptr locenv m e v
                       -> Cminor.eval_expr g stkptr locenv m e v'
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
  
(*   Variable (stbl: symboltable) (CE:compilenv) (locenv : env) (g : genv) (stkptr:Values.val). *)
  
  Lemma increase_order_level_of_top_ge:
    forall CE id s s0 s3,
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
      apply Nat.lt_eq_cases.
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
      destruct (Nat.eq_dec id₁ i);subst.
      + rewrite Nat.eqb_refl in heq0.
        !invclear heq0.
        assert (h:id₂ ≠ i) by auto.
        rewrite <- (Nat.eqb_neq id₂ i) in h.
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
      + destruct (Nat.eq_dec id₂ i).
        * subst.
          rewrite Nat.eqb_refl in heq.
          !invclear heq.
          assert (h:id₁ ≠ i) by auto.
          rewrite <- (Nat.eqb_neq id₁ i) in h.
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
        * rewrite <- (Nat.eqb_neq id₁ i) in n.
          rewrite <- (Nat.eqb_neq id₂ i) in n0.
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

Set Printing Width 75.
  Lemma CEfetchG_inj : forall CE id₁ id₂,
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
    intros until 0.
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
      apply Nat.lt_neq.
      apply CEfetch_reside_false in heq_fetch_id₂.
      apply CEfetch_reside_true in heq_fetch_id₁.
      rewrite heq_fetch_id₂,heq_fetch_id₁ in *;simpl in *.
      !invclear heq_CEframeG_id₁;simpl in *.
      specialize (h_forall_l (lvl_id₂, fr_id₂)).
      simpl in *.
      apply h_forall_l.
      eapply frameG_In;eauto.
    - left.
      apply Nat.lt_neq.
      apply CEfetch_reside_true in heq_fetch_id₂.
      apply CEfetch_reside_false in heq_fetch_id₁.
      rewrite heq_fetch_id₂,heq_fetch_id₁ in *;simpl in *.
      !invclear heq_CEframeG_id₂;simpl in *.
      specialize (h_forall_l (lvl_id₁, fr_id₁)).
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
        apply Nat.sub_0_le in H1.
        assert (s3 < s3)%nat. {
          eapply lt_le_trans with s1;auto. }
        destruct (lt_irrefl s3);auto.
      + rewrite minus_diag in H1.
        symmetry in H1.
        apply Nat.sub_0_le in H1.
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


  Lemma transl_variable_inj :
    forall CE stbl a₁ a₂ id₁ id₂ k₁ k₂ δ₁ δ₂,
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
    assert (hh:=CEfetchG_inj _ _ _ h_incr_orderG_CE h_forall_CE _ _ _ _ _ _  h₁ h₂ h₁' h₂' hneq).
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

(*
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
       \/ δ₂ + Memdata.size_chunk chnk₂ <= δ₁
       \/ δ₁ + Memdata.size_chunk chnk₁ <= δ₂).
  Proof.
  Admitted.


    (* We need something more precise, probably this: *)
  Lemma foo2' :
    forall stbl chnk₁ a₁  id₁ k₁ δ₁,
      (* Frame are numbered with different (increasing) numers *)
      increasing_orderG CE ->
      (* In each frame, stacks are also numbered with (increasing) numbers *)
      List.Forall (fun otherfrm => increasing_order_fr otherfrm) CE ->
      (forall id δ, CompilEnv.fetchG id CE = Some δ
                    -> 0 <= δ ∧ δ < Integers.Int.modulus) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a₁ id₁ = OK (build_loads k₁ δ₁) ->
      compute_chnk_id stbl id₁ = OK chnk₁ ->
      forall chnk₂ a₂ id₂ k₂ δ₂,
        (* translating the variabe to a Cminor load address *)
        transl_variable stbl CE a₂ id₂ = OK (build_loads k₂ δ₂) ->
        compute_chnk_id stbl id₂ = OK chnk₂ ->
        id₁ <> id₂ ->
        (k₁ <> k₂
         \/ δ₂ + Memdata.size_chunk chnk₂ <= δ₁
         \/ δ₁ + Memdata.size_chunk chnk₁ <= δ₂).
  Proof.
  Admitted.*)
(*
  (* TODO: simplify this proof. *)
  Lemma cmtype_chk : forall tpnme t tt chk,
      transl_type stbl tpnme = OK t -> 
      Ctypes.opttyp_of_type t = Some tt ->
      Ctypes.access_mode t = Ctypes.By_value chk ->
      chk = AST.chunk_of_type tt.
  Proof.
    intros.
    functional inversion H;subst;simpl in *;eq_same_clear;simpl in *.
    - inversion H1;auto.
    - inversion H1;auto.
    - destruct t;simpl in *;try discriminate;eq_same_clear;
      try
        now
        repeat
        match goal with
        | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
          try functional inversion h;eq_same_clear;subst; try clear h
        | h:function_utils.transl_basetype _ _  =
            OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
        | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
        end.

      + destruct i;simpl in *;
        try
          now
          repeat
          match goal with
          | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
            try functional inversion h;eq_same_clear;subst; try clear h
          | h:function_utils.transl_basetype _ _  =
              OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
          | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
          end;
        destruct s;simpl in *; try rewrite <- transl_typenum_ok in *;
        repeat match goal with
               | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
                 try functional inversion h;eq_same_clear;subst; try clear h
               | h:function_utils.transl_basetype _ _  =
                   OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
               | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
               end.
      + try rewrite <- transl_typenum_ok in *;
        repeat match goal with
               | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
                 try functional inversion h;eq_same_clear;subst; try clear h
               | h:function_utils.transl_basetype _ _  =
                   OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
               | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
               end.
    - destruct t;simpl in *;try discriminate;eq_same_clear;
      try
        now
        repeat
        match goal with
        | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
          try functional inversion h;eq_same_clear;subst; try clear h
        | h:function_utils.transl_basetype _ _  =
            OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
        | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
        end.

      + destruct i;simpl in *;
        try
          now
          repeat
          match goal with
          | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
            try functional inversion h;eq_same_clear;subst; try clear h
          | h:function_utils.transl_basetype _ _  =
              OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
          | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
          end;
        destruct s;simpl in *; try rewrite <- transl_typenum_ok in *;
        repeat match goal with
               | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
                 try functional inversion h;eq_same_clear;subst; try clear h
               | h:function_utils.transl_basetype _ _  =
                   OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
               | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
               end.
      + try rewrite <- transl_typenum_ok in *;
        repeat match goal with
               | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
                 try functional inversion h;eq_same_clear;subst; try clear h
               | h:function_utils.transl_basetype _ _  =
                   OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
               | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
               end.
    - destruct t;simpl in *;try discriminate;eq_same_clear;
      try
        now
        repeat
        match goal with
        | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
          try functional inversion h;eq_same_clear;subst; try clear h
        | h:function_utils.transl_basetype _ _  =
            OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
        | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
        end.

      + destruct i;simpl in *;
        try
          now
          repeat
          match goal with
          | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
            try functional inversion h;eq_same_clear;subst; try clear h
          | h:function_utils.transl_basetype _ _  =
              OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
          | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
          end;
        destruct s;simpl in *; try rewrite <- transl_typenum_ok in *;
        repeat match goal with
               | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
                 try functional inversion h;eq_same_clear;subst; try clear h
               | h:function_utils.transl_basetype _ _  =
                   OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
               | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
               end.
      + try rewrite <- transl_typenum_ok in *;
        repeat match goal with
               | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
                 try functional inversion h;eq_same_clear;subst; try clear h
               | h:function_utils.transl_basetype _ _  =
                   OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
               | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
               end.
    - destruct t;simpl in *;try discriminate;eq_same_clear;
      try
        now
        repeat
        match goal with
        | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
          try functional inversion h;eq_same_clear;subst; try clear h
        | h:function_utils.transl_basetype _ _  =
            OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
        | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
        end.

      + destruct i;simpl in *;
        try
          now
          repeat
          match goal with
          | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
            try functional inversion h;eq_same_clear;subst; try clear h
          | h:function_utils.transl_basetype _ _  =
              OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
          | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
          end;
        destruct s;simpl in *; try rewrite <- transl_typenum_ok in *;
        repeat match goal with
               | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
                 try functional inversion h;eq_same_clear;subst; try clear h
               | h:function_utils.transl_basetype _ _  =
                   OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
               | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
               end.
      + try rewrite <- transl_typenum_ok in *;
        repeat match goal with
               | h:function_utils.transl_typenum _ _ = OK _ |- _ =>
                 try functional inversion h;eq_same_clear;subst; try clear h
               | h:function_utils.transl_basetype _ _  =
                   OK _ |- _ => try functional inversion h;eq_same_clear;subst; try clear h
               | h:Ctypes.By_value _ = Ctypes.By_value _ |- _ => !invclear h;auto
               end.
  Qed.
*)
  Lemma transl_variable_astnum:
    forall stbl CE astnum id' addrof_nme,
      transl_variable stbl CE astnum id' = OK addrof_nme
      -> forall a,transl_variable stbl CE a id' = transl_variable stbl CE astnum id'.
  Proof.
    !intros.
    unfold transl_variable.
    !functional inversion heq_transl_variable.
    rewrite  heq_CEfetchG_id'_CE, heq_CEframeG_id'_CE, heq_lvloftop_CE_m'.
    reflexivity.
  Qed.



  Lemma compute_chk_32 :
    forall stbl t,
      compute_chnk_of_type stbl t = OK AST.Mint32
      -> transl_type stbl t = OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr).
  Proof.
    !intros.
    functional inversion heq;subst;simpl.
    - functional inversion H;simpl.
      reflexivity.
    - functional inversion H;simpl.
      reflexivity.
  Qed.

  Set Printing Width 80.



  Notation " x =: y" := (x = OK y) (at level 90).
  Notation " x =! y" := (x = Error y) (at level 120).

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
  Lemma wf_chain_load'2:forall g locenv stkptr chk m m' b ofs e_t_v
                             vaddr,
      Memory.Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
      -> (stack_localstack_aligned locenv g m)
      -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
      -> forall lvl,
          let load_id := build_loads_ lvl in
          Cminor.eval_expr g stkptr locenv m' load_id vaddr
          -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
  Proof.
    !intros.
    rename H1 into h_ofs_non_zero.
    simpl in *.
    subst load_id.
    generalize dependent vaddr.
    induction lvl;!intros;simpl in *.
    - !inversion h_CM_eval_expr;econstructor;eauto.
    - !invclear h_CM_eval_expr.
      assert (h_CM_eval_expr_on_m:Cminor.eval_expr g stkptr locenv m (build_loads_ lvl) vaddr0). { eapply IHlvl; eauto. }
      econstructor.
      + eassumption.
      + destruct vaddr0;simpl in *;try discriminate.
        rewrite <- heq.
        symmetry.
        eapply Memory.Mem.load_store_other;eauto.
        right.
        left.
        simpl.
        transitivity 4.
        * !destruct (h_aligned_g_m _ _ _ h_CM_eval_expr_on_m).
          !invclear heq.
          !invclear heq0.
          vm_compute.
          intro abs;discriminate.
        * apply h_ofs_non_zero.
  Qed.

  (* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
  Lemma wf_chain_load'3:forall g locenv stkptr chk m m' b ofs e_t_v
                             vaddr,
      Memory.Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
      -> stack_localstack_aligned locenv g m'
      -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
      -> forall lvl,
          let load_id := build_loads_ lvl in
          Cminor.eval_expr g stkptr locenv m load_id vaddr
          -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
  Proof.
    !intros.
    rename H1 into h_ofs_non_zero.
    simpl in *.
    subst load_id.
    generalize dependent vaddr.
    induction lvl;!intros;simpl in *.
    - !inversion h_CM_eval_expr;econstructor;eauto.
    - !invclear h_CM_eval_expr.
      assert (h_CM_eval_expr_on_m':Cminor.eval_expr g stkptr locenv m' (build_loads_ lvl) vaddr0). { eapply IHlvl; eauto. }
      econstructor.
      + eassumption.
      + destruct vaddr0;simpl in *;try discriminate.
        rewrite <- heq.
        eapply Memory.Mem.load_store_other;eauto.
        right.
        left.
        simpl.
        transitivity 4.
        * !destruct (h_aligned_g_m' _ _ _ h_CM_eval_expr_on_m').
          !invclear heq.
          !invclear heq0.
          vm_compute.
          intro abs;discriminate.
        * apply h_ofs_non_zero.
  Qed.


  Lemma wf_chain_load'':forall g locenv stkptr chk m m' b ofs e_t_v
                             vaddr,
      Memory.Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
      -> (stack_localstack_aligned locenv g m)
      -> (stack_localstack_aligned locenv g m')
      -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
      -> forall lvl,
          let load_id := build_loads_ lvl in
          Cminor.eval_expr g stkptr locenv m' load_id vaddr
          <-> Cminor.eval_expr g stkptr locenv m load_id vaddr.
  Proof.
    intros g locenv stkptr chk m m' b ofs e_t_v vaddr H H0 H1 H2 lvl load_id.
    split;intro .
    - eapply wf_chain_load'2 ;eauto.
    - eapply wf_chain_load'3 ;eauto.
  Qed.

  (* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
  Lemma wf_chain_load':forall g locenv stkptr chk m m' b ofs e_t_v
                             vaddr,
      Memory.Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
      -> (stack_localstack_aligned locenv g m')
      -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
      -> forall lvl δ_lvl,
          let load_id := build_loads lvl δ_lvl in
          Cminor.eval_expr g stkptr locenv m load_id vaddr
          -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
  Proof.
    !intros.
    rename H1 into h_ofs_non_zero.
    simpl in *.
    unfold build_loads in *.
    !invclear h_CM_eval_expr_load_id.
    econstructor;eauto.
    Focus 2.
    { inversion h_CM_eval_expr;econstructor;eauto. }
    Unfocus.
    eapply wf_chain_load'3;eauto.
  Qed.

  (* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
  Lemma wf_chain_load'_2:forall g locenv stkptr chk m m' b ofs e_t_v
                             vaddr,
      Memory.Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
      -> (stack_localstack_aligned locenv g m)
      -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
      -> forall lvl δ_lvl,
          let load_id := build_loads lvl δ_lvl in
          Cminor.eval_expr g stkptr locenv m' load_id vaddr
          -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
  Proof.
    !intros.
    rename H1 into h_ofs_non_zero.
    simpl in *.
    unfold build_loads in *.
    !invclear h_CM_eval_expr_load_id.
    econstructor;eauto.
    Focus 2.
    { inversion h_CM_eval_expr;econstructor;eauto. }
    Unfocus.
    eapply wf_chain_load'2;eauto.
  Qed.

  (* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
  Lemma wf_chain_load_var:forall stbl CE g locenv stkptr astnum chk m m' b ofs e_t_v
                             id load_id vaddr,
      Memory.Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
      -> (stack_localstack_aligned locenv g m')
      -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
      -> transl_variable stbl CE astnum id =: load_id
      -> Cminor.eval_expr g stkptr locenv m load_id vaddr
      -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
  Proof.
    !intros.
    rename H1 into h_ofs_non_zero.
    simpl in *.
    !functional inversion heq_transl_variable;subst;clear heq_transl_variable.
    rename m'0 into max_lvl.
    set (δ_lvl:=(max_lvl - lvl_id)%nat) in *.
    eapply wf_chain_load';eauto.
  Qed.

  (* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
  Lemma wf_chain_load_var':forall stbl CE g locenv stkptr astnum chk m m' b ofs e_t_v
                             id load_id vaddr,
      Memory.Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
      -> (stack_localstack_aligned locenv g m)
      -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
      -> transl_variable stbl CE astnum id =: load_id
      -> Cminor.eval_expr g stkptr locenv m' load_id vaddr
      -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
  Proof.
    !intros.
    rename H1 into h_ofs_non_zero.
    simpl in *.
    !functional inversion heq_transl_variable;subst;clear heq_transl_variable.
    rename m'0 into max_lvl.
    set (δ_lvl:=(max_lvl - lvl_id)%nat) in *.
    eapply wf_chain_load'_2;eauto.
  Qed.




  Set Printing Width 100.



  (* INVARIANT OF STORE/STOREV: if we do not touch on addresses zero
     of blocks, chaining variables all poitn to zero ofsets. *)
  Lemma wf_chain_load_aligned:forall g locenv chk m m' b ofs e_t_v,
      Memory.Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
      -> (4 <= (Int.unsigned ofs))
      -> stack_localstack_aligned locenv g m
      -> stack_localstack_aligned locenv g m'.
  Proof.
    unfold stack_localstack_aligned at 2.
    !intros.
    revert g locenv chk m m' b ofs e_t_v heq_storev_e_t_v H0 h_aligned_g_m b0 v h_CM_eval_expr.
    destruct δ_lvl;simpl;!intros.
    - rename h_aligned_g_m0 into h_aligned_m.
      rename h_CM_eval_expr0 into h_CM_eval_expr.
      edestruct (h_aligned_m b0 O v).
      + simpl.
        constructor.
        !inversion h_CM_eval_expr.
        assumption.
      + eauto.
    - rename h_aligned_g_m0 into h_aligned_m.
      rename h_CM_eval_expr0 into h_CM_eval_expr.
      !inversion h_CM_eval_expr.
      generalize h_CM_eval_expr0.
      !intro.
      eapply wf_chain_load'2 in h_CM_eval_expr2;eauto.
      generalize h_CM_eval_expr2.
      !intro.
      eapply h_aligned_m in h_CM_eval_expr3.

      destruct h_CM_eval_expr3.
      subst.
      assert (heq_ld_m:Memory.Mem.loadv AST.Mint32 m (Values.Vptr x Int.zero) = Some v). {
        simpl.
        erewrite <- (Memory.Mem.load_store_other);eauto. }
      red in h_aligned_m.
      eapply (h_aligned_m _ (S δ_lvl)).
      simpl.
      econstructor;eauto.
  Qed.


  

  

  
Set Printing Width 78.

  Lemma assignment_preserve_stack_match :
    forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
      increasing_orderG CE ->
      Forall (λ otherfrm : CompilEnv.frame, increasing_order_fr otherfrm) CE ->
      (∀ (id : idnum) (δ : CompilEnv.V),
          CompilEnv.fetchG id CE = Some δ → 0 <= δ ∧ δ < Integers.Int.modulus) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a id = OK id_t ->
      (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
      transl_value e_v e_t_v ->
      (* Evaluating var address in Cminor *)
      Cminor.eval_expr g stkptr locenv m id_t idaddr ->
      (* Size of variable in Cminor memorry *)
      compute_chnk stbl (E_Identifier a id) = OK chk ->
      (* the two storing operation maintain match_env *)
      storeUpdate stbl s (E_Identifier a id) e_v (Normal s') ->
      Memory.Mem.storev chk m idaddr e_t_v = Some m' ->
      match_env stbl s CE stkptr locenv g m ->
      stack_match stbl s' CE stkptr locenv g m'.
  Proof.
    intros until m'. (* if !intros. then id-t get renamed int id_t0? *)
    !intros.
    rename H1 into h_fetch_bounds.
    !inversion h_match_env.
    (* Getting rid of erronous cases *)
    !functional inversion heq_transl_variable.
    rename m'0 into lvl_max.
    (* done *)
    (* getting rid of erroneous storev parameter *)
    rewrite <- cm_storev_ok in heq_storev_e_t_v.
    !functional inversion heq_storev_e_t_v;subst.
    set (loads_id:=(build_loads (lvl_max - lvl_id) δ_id)) in *.
    rewrite cm_storev_ok in *.
    (* done *)
    assert (h_ofs_nonzero:4 <= Int.unsigned ofs). {
      eapply eval_build_loads_offset_non_null_var;eauto. }

    unfold stack_match.
    !intros other_nme other_val addrof_other_nme load_addrof_other_nme type_other_nme cm_typ_other_nme.
    (* id can already be evaluated in s *)
    destruct (h_stk_cmpl_s_CE _ _ _ heq_transl_variable) as [v_id_prev h_eval_name_id_val_prev].
    set (nme:=(E_Identifier a id)) in *.
    (* done *)
    (* Getting rid of erronous cases *)
    !functional inversion heq_transl_name.
    subst.
    rename id0 into other_id.
    set (other_nme:=(E_Identifier astnum other_id)) in *.
(*     simpl in *. *)
    (* done *)
    (* other_nme can already be evaluated in s *)
    destruct (h_stk_cmpl_s_CE _ _ _ heq_transl_variable0)
      as [v_other_id_prev h_eval_name_other_id_val_prev].
    (* done *)
    destruct (h_stk_mtch_s_m
                _ _ _ _ _ _ h_eval_name_other_id_val_prev
                heq_type_of_name heq_transl_name heq_transl_type heq_make_load)
      as [ cm_v [tr_val_v_other cm_eval_m_v_other]].
    assert (h_tr_exp_other:
              transl_expr stbl CE (E_Name 1%nat (E_Identifier astnum other_id))
                          =: load_addrof_other_nme). {
      simpl.
      simpl in heq_type_of_name.
      rewrite heq_transl_variable0, heq_type_of_name.
      unfold value_at_addr.
      rewrite heq_transl_type;simpl.
      assumption. }
    !destruct (Nat.eq_dec id other_id).
    - subst nme. (* same variable ==> result is the value just stored *)
      subst other_nme.
      subst other_id.
      simpl in heq_type_of_name.
      assert (chk = AST.Mint32). {
        rewrite compute_chnk_ok in heq_compute_chnk.
        !functional inversion heq_compute_chnk;subst;auto. }
      simpl in heq_compute_chnk.
      unfold compute_chnk_id in heq_compute_chnk.
      rewrite heq_type_of_name in heq_compute_chnk.
      lazy beta iota delta [bind] in heq_compute_chnk.
      rewrite (transl_variable_astnum _ _ _ _ _ heq_transl_variable0 a) in *.
      rewrite heq_transl_variable0 in heq_transl_variable.
      !invclear heq_transl_variable.
      !assert (e_v = other_val). { eapply storeUpdate_id_ok_same_eval_name ;eauto. }
      subst other_val.
      exists e_t_v;split;auto.
      !functional inversion heq_make_load;subst.
      eapply eval_Eload with (Values.Vptr b ofs).
      * { eapply wf_chain_load_var with (1:= heq_storev_e_t_v);eauto.
          - eapply wf_chain_load_aligned;eauto. }
      * simpl.
        (* Should be ok by well typedness of the chained stack wrt
           stbl (see hyp on compute_chk). *)
        (* assert (chunk = AST.chunk_of_type t). {
           rewrite cmtype_chk with (1:=heq_transl_type) (2:=heq_opttype) (3:=heq0).
           reflexivity. } *)
        assert (chunk = AST.Mint32). {
          !functional inversion heq_transl_type;subst;simpl in h_access_mode_cm_typ_other_nme.
          - inversion h_access_mode_cm_typ_other_nme;auto.
          - inversion h_access_mode_cm_typ_other_nme;auto. }
        subst.
        erewrite (Memory.Mem.load_store_same _ _ _ _ _ _ heq_store_e_t_v) .
        { destruct e_t_v;auto;destruct e_v;simpl in *;try discriminate; now inversion heq_transl_value. }
        
    - (* loading a different variable id' than the one stored id.
         2 steps: first prove that the addresses of id' and id did
         not change (the translated expressions did not change + the
         chained stack did not change either), and thus remain
         different, then conclude that the value stored in id' did
         not change. *)
      !assert (chk = AST.Mint32). {
        rewrite function_utils.compute_chnk_ok in heq_compute_chnk.
        functional inversion heq_compute_chnk; reflexivity. }

      assert (v_other_id_prev = other_val). { eapply storeUpdate_id_ok_others_eval_name ;eauto. }
      subst.
      exists cm_v.
      split;auto.
      assert (h_aligned_m' : stack_localstack_aligned locenv g m'). {
        eapply wf_chain_load_aligned;eauto. }
      !functional inversion heq_make_load;subst.
      !inversion cm_eval_m_v_other.
      generalize (wf_chain_load_var _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                heq_storev_e_t_v h_aligned_m'
                                h_ofs_nonzero heq_transl_variable0
                                h_CM_eval_expr_addrof_other_nme).
      !intro.
      econstructor.
      + eassumption.
      + destruct vaddr; try discriminate;simpl in *.
        clear h_tr_exp_other.
        erewrite Memory.Mem.load_store_other;[now eassumption| now eassumption | ].
        subst nme other_nme.
        unfold compute_chnk_id in heq_compute_chnk.
        destruct (fetch_var_type id stbl) eqn:heq_fetchvartyp;try discriminate.
        simpl in heq_compute_chnk.

        assert (heq_tr_type_id:transl_type stbl t = OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr)). {
          apply compute_chk_32;auto. }
        unfold stack_separate in h_separate_CE_m.
        { eapply h_separate_CE_m with (nme:=(E_Identifier a id))
                             (nme':=(E_Identifier astnum other_id))
                             (k₂ := b0) (k₁:=b); clear h_separate_CE_m;simpl;try eassumption;auto.
          intro abs.
          inversion abs;subst;try discriminate.
          elim hneq;reflexivity. }
  Qed.


  Lemma storev_inv : forall nme_chk m nme_t_addr e_t_v m',
      Memory.Mem.storev nme_chk m nme_t_addr e_t_v = Some m'
      -> exists b ofs, nme_t_addr = Values.Vptr b ofs.
  Proof.
    !intros.
    destruct nme_t_addr; try discriminate.
    eauto.
  Qed.        

  Lemma transl_name_OK_inv : forall stbl CE nme nme_t,
      transl_name stbl CE nme = OK nme_t
      -> exists astnum id, (transl_variable stbl CE astnum id =  OK nme_t /\ nme = E_Identifier astnum id).
  Proof.
    !intros stbl CE nme nme_t H.
    functional inversion H.
    eauto.
  Qed.
 
  Lemma assignment_preserve_stack_complete :
    forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
      increasing_orderG CE ->
      Forall (λ otherfrm : CompilEnv.frame, increasing_order_fr otherfrm) CE ->
      (∀ (id : idnum) (δ : CompilEnv.V),
          CompilEnv.fetchG id CE = Some δ → 0 <= δ ∧ δ < Integers.Int.modulus) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a id = OK id_t ->
      (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
      transl_value e_v e_t_v ->
      (* Evaluating var address in Cminor *)
      Cminor.eval_expr g stkptr locenv m id_t idaddr ->
      (* Size of variable in Cminor memorry *)
      compute_chnk stbl (E_Identifier a id) = OK chk ->
      (* the two storing operation maintain match_env *)
      storeUpdate stbl s (E_Identifier a id) e_v (Normal s') ->
      Memory.Mem.storev chk m idaddr e_t_v = Some m' ->
      stack_complete stbl s CE ->
      stack_complete stbl s' CE.
  Proof.
    !intros.
    red.
    !intros.
    !destruct (Nat.eq_dec nme id).
    - subst.
      exists e_v.
      constructor.
      eapply storeUpdate_id_ok_same;eauto.
    - red in h_stk_cmpl_s_CE.
      destruct h_stk_cmpl_s_CE with (1:=heq_transl_variable0).
      exists x.
      constructor.
      !invclear H.
      erewrite <- storeUpdate_id_ok_others.
      + eassumption.
      + eassumption.
      + apply not_eq_sym;assumption.
  Qed.

  Lemma assignment_preserve_stack_separate :
    forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
      increasing_orderG CE ->
      Forall (λ otherfrm : CompilEnv.frame, increasing_order_fr otherfrm) CE ->
      (∀ (id : idnum) (δ : CompilEnv.V),
          CompilEnv.fetchG id CE = Some δ → 0 <= δ ∧ δ < Integers.Int.modulus) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a id = OK id_t ->
      (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
      transl_value e_v e_t_v ->
      (* Evaluating var address in Cminor *)
      Cminor.eval_expr g stkptr locenv m id_t idaddr ->
      (* Size of variable in Cminor memorry *)
      compute_chnk stbl (E_Identifier a id) = OK chk ->
      (* the two storing operation maintain match_env *)
      storeUpdate stbl s (E_Identifier a id) e_v (Normal s') ->
      Memory.Mem.storev chk m idaddr e_t_v = Some m' ->
      match_env stbl s CE stkptr locenv g m ->
      stack_separate stbl CE stkptr locenv g m'.
  Proof.
    !intros.
    red.
    !intros.
    !destruct h_match_env.
    decompose [ex] (storev_inv _ _ _ _ _ heq_storev_e_t_v);subst.
    !functional inversion heq_transl_name;subst.
    generalize heq_transl_name0.
    intro h_transl_name_remember.
    functional inversion h_transl_name_remember.
    eapply wf_chain_load_var' with (m:=m) in h_CM_eval_expr_addrof_nme.
    - eapply wf_chain_load_var' with (m:=m) in h_CM_eval_expr_addrof_nme'.
      + eapply h_separate_CE_m with (1:=heq_type_of_name0);eauto.
      + eassumption.
      + assumption.
      + eapply eval_build_loads_offset_non_null_var with (4:=h_CM_eval_expr_id_t);eauto.
      + simpl in heq_transl_name.
        eauto.
    - eassumption.
    - assumption.
    - eapply eval_build_loads_offset_non_null_var with (4:=h_CM_eval_expr_id_t);eauto.
    - eauto.
  Qed.

  Lemma assignment_preserve_stack_no_null_offset :
    forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
      increasing_orderG CE ->
      Forall (λ otherfrm : CompilEnv.frame, increasing_order_fr otherfrm) CE ->
      (∀ (id : idnum) (δ : CompilEnv.V),
          CompilEnv.fetchG id CE = Some δ → 0 <= δ ∧ δ < Integers.Int.modulus) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a id = OK id_t ->
      (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
      transl_value e_v e_t_v ->
      (* Evaluating var address in Cminor *)
      Cminor.eval_expr g stkptr locenv m id_t idaddr ->
      (* Size of variable in Cminor memorry *)
      compute_chnk stbl (E_Identifier a id) = OK chk ->
      (* the two storing operation maintain match_env *)
      storeUpdate stbl s (E_Identifier a id) e_v (Normal s') ->
      Memory.Mem.storev chk m idaddr e_t_v = Some m' ->
      match_env stbl s CE stkptr locenv g m ->
      stack_no_null_offset stbl CE.
  Proof.
    !intros.
    destruct h_match_env.
    assumption.
  Qed.

  Lemma assignment_preserve_stack_safe :
    forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
      increasing_orderG CE ->
      Forall (λ otherfrm : CompilEnv.frame, increasing_order_fr otherfrm) CE ->
      (∀ (id : idnum) (δ : CompilEnv.V),
          CompilEnv.fetchG id CE = Some δ → 0 <= δ ∧ δ < Integers.Int.modulus) ->
      (* translating the variabe to a Cminor load address *)
      transl_variable stbl CE a id = OK id_t ->
      (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
      transl_value e_v e_t_v ->
      (* if e_v is an int, then it is not overflowing *)
      (forall n, e_v = Int n -> do_overflow_check n (Normal (Int n))) ->
      (* Evaluating var address in Cminor *)
      Cminor.eval_expr g stkptr locenv m id_t idaddr ->
      (* Size of variable in Cminor memorry *)
      compute_chnk stbl (E_Identifier a id) = OK chk ->
      (* the two storing operation maintain match_env *)
      storeUpdate stbl s (E_Identifier a id) e_v (Normal s') ->
      Memory.Mem.storev chk m idaddr e_t_v = Some m' ->
      match_env stbl s CE stkptr locenv g m ->
      safe_stack s'.
  Proof.
    !intros.
    rename H1 into h_fetch_safe.
    rename H4 into h_overf_e_v.
    !destruct h_match_env.
    !intros.
    red.
    !intros.
    !destruct (Nat.eq_dec id0 id).
    - subst.
      apply h_overf_e_v.
      erewrite storeUpdate_id_ok_same in heq_SfetchG;eauto.
      inversion heq_SfetchG.
      reflexivity.
    - red in h_safe_stack_s.
      apply h_safe_stack_s with (id:=id0);eauto.
      erewrite storeUpdate_id_ok_others;eauto.
  Qed.


Set Printing Width 78.
Lemma transl_stmt_ok :
  forall stbl CE  (stm:statement) (stm':Cminor.stmt),
      increasing_orderG CE ->
      Forall (λ otherfrm : CompilEnv.frame, increasing_order_fr otherfrm) CE ->
      (∀ (id : idnum) (δ : CompilEnv.V),
          CompilEnv.fetchG id CE = Some δ → 0 <= δ ∧ δ < Integers.Int.modulus) ->
    transl_stmt stbl CE stm = (OK stm') ->
    forall locenv (g:genv) (m:Memory.Mem.mem) (s:stack)
           (s':stack) (spb:Values.block) ofs f,
      match_env stbl s CE (Values.Vptr spb ofs) locenv g m ->
      eval_stmt stbl s stm (Normal s') ->
      forall tr locenv' m' o,
        Cminor.exec_stmt g f (Values.Vptr spb ofs) locenv m stm' tr locenv' m' o
        ->  match_env stbl s' CE (Values.Vptr spb ofs) locenv' g m'.
Proof.
  intros until stm.
  !functional induction (transl_stmt stbl CE stm)
  ;simpl;!intros;eq_same_clear;subst;simpl in *;try discriminate.
  (* skip *)
  - !invclear h_eval_stmt.
    !invclear h_exec_stmt.
    assumption.
    (* assignment *)
  - rename e0 into e.
    rename x into e_t.
    rename x0 into nme_t.
    rename x1 into nme_chk.
    !inversion h_match_env.
    !invclear h_eval_stmt.
    + rename t into nme_type.
      rename v into e_v.
      !invclear h_exec_stmt.
      rename v into e_t_v.
      rename vaddr into nme_t_addr.
      constructor.
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_match;eauto.
          decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr_v h_match_env).
          assert (x1 = e_t_v). {
            eapply det_eval_expr;eauto. }
          subst x1.
          assumption. }
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_complete;eauto.
          decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr_v h_match_env).
          assert (x1 = e_t_v). {
            eapply det_eval_expr;eauto. }
          subst x1.
          assumption. }
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_separate;eauto.
          decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr_v h_match_env).
          assert (x1 = e_t_v). {
            eapply det_eval_expr;eauto. }
          subst x1.
          eassumption. }
      * decomp (storev_inv _ _ _ _ _ heq_storev_v) ;subst.
        functional inversion heq_transl_name.
        eapply wf_chain_load_aligned;eauto.
        eapply eval_build_loads_offset_non_null_var;eauto.
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_no_null_offset;eauto.
          decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr_v h_match_env).
          assert (x1 = e_t_v). {
            eapply det_eval_expr;eauto. }
          subst x1.
          eassumption. }
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_safe;eauto.
          decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr_v h_match_env).
          assert (x1 = e_t_v). {
            eapply det_eval_expr;eauto. }
          subst x1.
          eassumption.
          !intros.
          subst.
          eapply eval_expr_overf;eauto. }
    + rename t into nme_type.
      rename v into e_v.
      !invclear h_exec_stmt.
      rename v into e_t_v.
      rename vaddr into nme_t_addr.
      constructor.
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_match;eauto.
          decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr h_match_env).
          assert (x1 = e_t_v). {
            eapply det_eval_expr;eauto. }
          subst x1.
          assumption. }
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_complete;eauto.
          decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr h_match_env).
          assert (x1 = e_t_v). {
            eapply det_eval_expr;eauto. }
          subst x1.
          assumption. }
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_separate;eauto.
          decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr h_match_env).
          assert (x1 = e_t_v). {
            eapply det_eval_expr;eauto. }
          subst x1.
          eassumption. }
      * decomp (storev_inv _ _ _ _ _ heq_storev_v) ;subst.
        functional inversion heq_transl_name.
        eapply wf_chain_load_aligned;eauto.
        eapply eval_build_loads_offset_non_null_var;eauto.
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_no_null_offset;eauto.
          decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr h_match_env).
          assert (x1 = e_t_v). {
            eapply det_eval_expr;eauto. }
          subst x1.
          eassumption. }
      * { decompose [and ex] (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
          eapply assignment_preserve_stack_safe;eauto.
          - decompose [ex and] (transl_expr_ok _ _ _ _ heq_tr_expr_e0 _ _ _ _ _ _
                                             h_eval_expr h_match_env).
            assert (x1 = e_t_v). {
              eapply det_eval_expr;eauto. }
            subst x1.
            eassumption.
          - !intros.
            inversion heq;subst.
            eapply eval_expr_overf;eauto. }
  (* IF THEN ELSE *)
  - rename e0 into e.
    rename x into e_t.
    rename x0 into b_then.
    rename x1 into b_else.
    !invclear h_eval_stmt.
    + !invclear h_exec_stmt.
      generalize (transl_expr_ok _ _ _ e_t heq_tr_expr_e0 locenv g m _ _ (Values.Vptr spb ofs) h_eval_expr h_match_env).
      intro h_ex.
      decomp h_ex.
      assert (b=true). {
        clear IHr IHr0 h_exec_stmt.
        !invclear h_CM_eval_expr.
        !invclear h_CM_eval_expr.
        simpl in *.
        generalize (det_eval_expr _ _ _ _ _ _ _ h_CM_eval_expr_e_t h_CM_eval_expr_e_t0).
        !intro;subst.
        clear h_CM_eval_expr_e_t0.
        !invclear heq_transl_value.
        !invclear h_eval_constant.
        !invclear heq.
        vm_compute in H12.
        inversion H12.
        reflexivity. }
      subst.
      eapply IHr;eauto.
    + !invclear h_exec_stmt.
      generalize (transl_expr_ok _ _ _ e_t heq_tr_expr_e0 locenv g m _ _ (Values.Vptr spb ofs) h_eval_expr h_match_env).
      intro h_ex.
      decomp h_ex.
      assert (b=false). {
        clear IHr IHr0 h_exec_stmt.
        !invclear h_CM_eval_expr.
        !invclear h_CM_eval_expr.
        simpl in *.
        generalize (det_eval_expr _ _ _ _ _ _ _ h_CM_eval_expr_e_t h_CM_eval_expr_e_t0).
        !intro;subst.
        clear h_CM_eval_expr_e_t0.
        !invclear heq_transl_value.
        !invclear h_eval_constant.
        !invclear heq.
        vm_compute in H12.
        inversion H12.
        reflexivity. }
      subst.
      eapply IHr0;eauto.
  (* CALL *)
  - admit.
  (* SEQUENCE *)
  - rename s1 into stmt1.
    rename s2 into stmt2.
    !invclear h_eval_stmt.
    !invclear h_exec_stmt.
    + eapply IHr0 with (6:=h_eval_stmt); eauto. 
    + xxx eapply IHr0 with (6:=h_eval_stmt); eauto.
    + eapply IHr with (6:=h_eval_stmt0); eauto. 
      all:eauto.
      * 
    
Admitted.




