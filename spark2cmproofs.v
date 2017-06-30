Require Import FunInd ZArith function_utils LibHypsNaming  Errors
        spark2Cminor Cminor symboltable eval semantics_properties
        Sorted Relations compcert.lib.Integers compcert_utils more_stdlib.
Require Import SetoidList.
Require Ctypes.
Import Symbol_Table_Module Memory.
Require Import chained_structure.
Open Scope error_monad_scope.
Open Scope Z_scope.

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

(** Hypothesis renaming stuff from other files + current file.
    DO NOT REDEFINED INT HIS FILE *)
Ltac rename_hyp h th ::=
  match th with
  | _ => (STACK.rename_hyp1 h th)
  | _ => (semantics_properties.rename_hyp_sem h th)
  | _ => (more_stdlib.rename_hyp1 h th)
  | _ => (spark2Cminor.rename_hyp1 h th)
  | _ => (compcert_utils.rename_hyp1 h th)
  | _ => (chained_structure.rename_chained h th)
  | _ => (LibHypsNaming.rename_hyp_neg h th)
  | _ => (rename_sparkprf h th)
  end.


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
               | H: ?A = _ , H': ?A = _ |- _ => rewrite H in H'; !inversion H'
               | H: OK ?A = OK ?B |- _ => !inversion H
               | H: Errors.OK ?A = Errors.OK ?B |- _ => !inversion H
               | H: Some ?A = Some ?B |- _ => !inversion H
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
    | None =>  Error (msg "type_of_name: unknown type for astnum (indexed_component")
    end
  | SelectedComponent astnum x0 x1 =>
    match symboltable.fetch_exp_type astnum stbl with
      Some x => Errors.OK x
    | None =>  Error (msg "type_of_name: unknown type for astnum (selected_component")
    end
  end.

(** Hypothesis renaming stuff *)
Ltac rename_hyp1 h th :=
  match th with
  (* TODO: remove when we remove type_of_name by the real one. *)
  | type_of_name _ _ = Error _ => fresh "heq_type_of_name_ERR"
  | type_of_name _ _ = _ => fresh "heq_type_of_name"
  | Values.Val.bool_of_val ?v ?b => fresh "heq_bofv_" v "_" b
  | Values.Val.bool_of_val ?v ?b => fresh "heq_bofv_" v
  | Values.Val.bool_of_val ?v ?b => fresh "heq_bofv_" b
  | Values.Val.bool_of_val ?v ?b => fresh "heq_bofv"
  | STACK.NoDup ?s => fresh "h_nodup_s_" s
  | STACK.NoDup _ => fresh "h_nodup_s"
  | STACK.NoDup_G ?s => fresh "h_nodup_G_s_" s
  | STACK.NoDup_G _ => fresh "h_nodup_G_s"
  | CompilEnv.NoDup ?s => fresh "h_nodup_CE_" s
  | CompilEnv.NoDup _ => fresh "h_nodup_CE"
  | CompilEnv.NoDup_G ?s => fresh "h_nodup_G_CE_" s
  | CompilEnv.NoDup_G _ => fresh "h_nodup_G_CE"
  | CompilEnv.exact_levelG ?CE => fresh "h_exct_lvlG_" CE
  | CompilEnv.exact_levelG ?CE => fresh "h_exct_lvlG"
  | exp => fresh "e"
  | stmt => fresh "stmt"
  | Cminor.expr => match goal with
                   | H: transl_expr ?stbl ?CE ?x = Errors.OK h |- _ => fresh x "_t"
                   | H: transl_name ?stbl ?CE ?x = Errors.OK h |- _ => fresh x "_t"
                   end
  | AST.memory_chunk => match goal with
                   | H: compute_chnk ?stbl ?x = Errors.OK h |- _ => fresh x "_chk"
                   end
  | SymTable_Exps.V =>
    match goal with
    | H: symboltable.fetch_exp_type (name_astnum ?x) _ = Some h |- _ => fresh x "_type"
    | H: symboltable.fetch_exp_type ?x _ = Some h |- _ => fresh x "_type"
    end
  | Values.val =>
    match goal with
    | H:  Cminor.eval_expr _ _ _ _ ?e h |- _ => fresh e "_v"
    end
  | value =>
    match goal with
    | H:  evalExp _ _ ?e (OK h) |- _ => fresh e "_v"
    | H:  evalExp _ _ ?e h |- _ => fresh e "_v"
    end
  end.

Ltac rename_sparkprf ::= rename_hyp1.

Lemma transl_value_det: forall v tv1 tv2,
    transl_value v tv1 -> transl_value v tv2 -> tv1 = tv2.
Proof.
  !intros.
  inversion heq_transl_value_v_tv1; inversion heq_transl_value_v_tv2;subst;auto;inversion H1;auto.
Qed.

(* clear may fail if h is not a hypname *)
(* Tactic Notation "decomp" constr(h) := *)
(*        !! (decompose [and ex or] h). *)
(* useless? *)
Lemma transl_value_tot: forall v,
    (exists b, v = Bool b \/ exists n, v = Int n)
    -> exists tv, transl_value v tv.
Proof.
  !intros.
  decomp h_ex;subst.
  - destruct b;eexists;econstructor.
  - eexists;econstructor.
Qed.


Lemma transl_literal_ok1 : forall g (l:literal) v,
    evalLiteral l (OK v) ->
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

Lemma transl_literal_ok2 : forall g (l:literal) v,
    evalLiteral l (OK v) ->
    forall sp t_v,
      transl_value v t_v ->
      eval_constant g sp (transl_literal l) = Some t_v.
Proof.
  !intros.
  !destruct l;simpl in *;eq_same_clear.
  - !inversion h_eval_literal.
    !inversion h_overf_check.
    !inversion heq_transl_value_v_t_v.
    reflexivity.
  - destruct b;simpl in *;eq_same_clear.
    + !inversion h_eval_literal.
      !inversion heq_transl_value_v_t_v.
      reflexivity.
    + !inversion h_eval_literal.
      !inversion heq_transl_value_v_t_v.
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
  | Plus => !invclear h
  | Minus => !invclear h
  | Multiply => !invclear h
  | Divide => !invclear h
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
         | H: overflowCheck _ (OK (Int _)) |- _ => !invclear H
         | H: rangeCheck _ _ _ (OK (Int _)) |- _ => !invclear H
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
             let h1 := fresh "h_le" in
             let h2 := fresh "h_le" in
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
  !destruct n;simpl in *;
  inversion heq_transl_value_v1_x;
  constructor.
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
  ;inversion heq_transl_value_v1_x
  ;inversion heq_transl_value_v2_x0
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
  ;inversion heq_transl_value_v1_x
  ;inversion heq_transl_value_v2_x0
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
  | check_overflow_value _ => fresh "h_check_overf"
  | _ => rename_hyp1 h th
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
  !intros.
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *;eq_same_clear.
  !destruct (Z.eq_dec n n0).
  - subst n0.
    inversion heq_transl_value_v1_x;subst;simpl.
    inversion heq_transl_value_v2_x0;subst;simpl.
    rewrite Fcore_Zaux.Zeq_bool_true;auto.
    unfold Values.Val.cmp.
    simpl.
    rewrite Integers.Int.eq_true.
    constructor.
  - rewrite Fcore_Zaux.Zeq_bool_false;auto.
    unfold Values.Val.cmp.
    inversion heq_transl_value_v2_x0;subst;simpl.
    inversion heq_transl_value_v1_x;subst;simpl.
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
    replace (Zneq_bool n0 n0) with false. all:swap 1 2. {
      symmetry.
      apply Zneq_bool_false_iff.
      reflexivity. }
    unfold Values.Val.cmp.
    inversion heq_transl_value_v1_x;subst;simpl.
    inversion heq_transl_value_v2_x0;subst;simpl.
    rewrite Integers.Int.eq_true.
    simpl.
    constructor.
  - rewrite Zneq_bool_true;auto.
    unfold Values.Val.cmp.
    inversion heq_transl_value_v2_x0;subst;simpl.
    inversion heq_transl_value_v1_x;subst;simpl.
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
  inversion heq_transl_value_v1_x;subst;simpl.
  inversion heq_transl_value_v2_x0;subst;simpl.
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
  inversion heq_transl_value_v1_x;subst;simpl.
  inversion heq_transl_value_v2_x0;subst;simpl.
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
  inversion heq_transl_value_v1_x;subst;simpl.
  inversion heq_transl_value_v2_x0;subst;simpl.
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
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *;
  eq_same_clear; inversion heq_transl_value_v1_x;subst;simpl.
  inversion heq_transl_value_v2_x0;subst;simpl.
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
Lemma unaryneg_ok : forall n v1 v,
    transl_value v1 n ->
    Math.unary_operation Unary_Minus v1 = Some v ->
    transl_value v (Values.Val.negint n).
Proof.
  !intros.
  simpl in *.
  destruct v1;simpl in *;try discriminate.
  eq_same_clear.
  inversion heq_transl_value_v1_n.
  simpl.
  rewrite Integers.Int.neg_repr.
  constructor.
Qed.

Lemma do_run_time_check_on_binop_ok: forall v1 v2 v op,
    do_run_time_check_on_binop op v1 v2 (OK v) ->
    Math.binary_operation op v1 v2 = Some v.
Proof.
  intros v1 v2 v op hdo_rtc.
  !invclear hdo_rtc.
  - !invclear h_overf_check.
    assumption.
  - !invclear h_do_division_check;simpl in *.
    !invclear h_overf_check.
    assumption.
  - simpl.
    !inversion h_do_division_check;cbn;subst.
    cbn in heq_mod'.
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

Lemma add_ok : forall v v1 v2 n1 n2,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop Plus v1 v2 (OK v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v (Values.Val.add n1 n2).
Proof.
  !intros.
  !destruct v1;simpl in *;try discriminate;eq_same_clear;subst;try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc.
  inversion heq_transl_value_v1_n1;subst;simpl.
  inversion heq_transl_value_v2_n2;subst;simpl.
  !invclear h_do_rtc_binop;simpl in *; eq_same_clear.
  !invclear h_overf_check.
  int_simpl;auto;inv_rtc.
  constructor.
Qed.

Lemma sub_ok : forall v v1 v2 n1 n2,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop Minus v1 v2 (OK v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v (Values.Val.sub n1 n2).
Proof.
  !intros.
  !destruct v1;simpl in *;try discriminate;eq_same_clear;subst; try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc.
  inversion heq_transl_value_v1_n1;subst;simpl.
  inversion heq_transl_value_v2_n2;subst;simpl.
  !invclear h_do_rtc_binop;simpl in *; eq_same_clear.
  !invclear h_overf_check.
  int_simpl;auto;inv_rtc.
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
  !intros.
  simpl in *.
  !destruct v1;simpl in *;try discriminate;eq_same_clear;subst; try now inv_rtc.
  !destruct v2;simpl in *; try discriminate;eq_same_clear;subst; try now inv_rtc.
  inversion heq_transl_value_v1_n1;subst;simpl.
  inversion heq_transl_value_v2_n2;subst;simpl.
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
Lemma div_ok : forall v v1 v2 n n1 n2,
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop Divide v1 v2 (OK v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v n ->
    Values.Val.divs n1 n2 = Some n.
Proof.
  !intros.
  simpl in *.
  !destruct v1;subst;simpl in *;try discriminate;try now inv_rtc.
  !destruct v2;subst;simpl in *; try discriminate;try now inv_rtc.
  inversion heq_transl_value_v2_n2;subst;simpl.
  inversion heq_transl_value_v1_n1;subst;simpl.
  rename n0 into v1.
  rename n3 into v2.
  !invclear h_do_rtc_binop;simpl in *; eq_same_clear.
  { decompose [or] h_or;discriminate. }
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
      { rewrite Integers.Int.eq_signed in h_divoverf1.
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
      vm_compute in heq_div.
      inversion heq_div.
      subst.
      inversion h_overf_check;subst.
      inv_rtc.
    + unfold Integers.Int.divs.
      rewrite !Integers.Int.signed_repr;auto 2.
      simpl in *.
      !invclear heq_div;subst.
      inversion h_overf_check;subst.
      inversion heq_transl_value_v_n;subst;simpl.
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


Lemma binary_operator_ok: forall op (n n1 n2 : Values.val) (v v1 v2 : value),
    check_overflow_value v1 ->
    check_overflow_value v2 ->
    do_run_time_check_on_binop op v1 v2 (OK v) ->
    transl_value v1 n1 ->
    transl_value v2 n2 ->
    transl_value v n ->
    forall m, Cminor.eval_binop (transl_binop op) n1 n2 m = Some n.
Proof.
  !intros.
  assert (h_rtc:=do_run_time_check_on_binop_ok _ _ _ _ h_do_rtc_binop).
  destruct op;simpl in *.
  - eapply (and_ok v1 v2 v n1 n2) in h_rtc;auto.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h_rtc);reflexivity.
  - eapply (or_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h_rtc);reflexivity.

  - eapply (eq_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h_rtc);reflexivity.
  - eapply (neq_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h_rtc);reflexivity.
  - eapply (lt_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h_rtc);reflexivity.
  - eapply (le_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h_rtc);reflexivity.
  - eapply (gt_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h_rtc);reflexivity.
  - eapply (ge_ok v1 v2 v n1 n2) in h_rtc;eq_same_clear;subst;eauto.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h_rtc);reflexivity.
  - generalize (add_ok _ _ _ _ _ h_check_overf h_check_overf0 h_do_rtc_binop
                       heq_transl_value_v1_n1 heq_transl_value_v2_n2).
    intro h.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h);reflexivity.
  - generalize (sub_ok _ _ _ _ _ h_check_overf h_check_overf0 h_do_rtc_binop
                       heq_transl_value_v1_n1 heq_transl_value_v2_n2).
    intro h.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h);reflexivity.
  - generalize (mult_ok _ _ _ _ _ h_check_overf h_check_overf0 h_do_rtc_binop
                        heq_transl_value_v1_n1 heq_transl_value_v2_n2).
    intro h.
    rewrite (transl_value_det _ _ _ heq_transl_value_v_n h);reflexivity.
  - generalize (div_ok _ _ _ _ _ _ h_check_overf h_check_overf0 h_do_rtc_binop
                       heq_transl_value_v1_n1 heq_transl_value_v2_n2 heq_transl_value_v_n).
    intro h.
    assumption.
  - admit. (* TODO mod_ok *)
Admitted.


(** * Memory invariant and bisimilarity *)


Lemma evalLiteral_overf : forall (l:literal) n,
    evalLiteral l (OK (Int n)) ->
    overflowCheck n (OK (Int n)).
Proof.
  !intros.
  !inversion h_eval_literal.
  !inversion h_overf_check.
  assumption.
Qed.


(** [safe_stack s] means that every value in the spark stack [s] is
    correct wrt to overflows.
    TODO: extend with other values than Int: floats, arrays, records. *)
Definition safe_stack s := forall id n,
    STACK.fetchG id s = Some (Int n) ->
    overflowCheck n (OK (Int n)).

(** Hypothesis renaming stuff *)
Ltac rename_hyp2' h th :=
  match th with
  | safe_stack ?s => fresh "h_safe_stack_" s
  | safe_stack _ => fresh "h_safe_stack"
  | _ => rename_hyp2 h th
  end.

Ltac rename_sparkprf ::= rename_hyp2'.

Lemma evalName_overf: forall s st nme n,
    safe_stack s
    -> evalName st s nme (OK (Int n))
    -> overflowCheck n (OK (Int n)).
Proof using.
  !intros.
  !inversion h_eval_name_nme. (* l'environnement retourne toujours des valeur rangées. *)
  - unfold safe_stack in *.
    eapply h_safe_stack_s;eauto.
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
  !intros.
  revert h_safe_stack_s.
  remember (OK (Int n)) as hN.
  revert n HeqhN.
  !induction h_eval_expr_e;!intros;subst;try discriminate.
  - eapply evalLiteral_overf;eauto.
  - eapply evalName_overf;eauto.
  - !invclear h_do_rtc_binop.
    + inversion h_overf_check;subst;auto.
    + inversion h_overf_check;subst;auto.
    + !inversion h_do_division_check.
      subst.
      specialize IHh_eval_expr_e1 with (1:=eq_refl) (2:=h_safe_stack_s).
      specialize IHh_eval_expr_e2 with (1:=eq_refl) (2:=h_safe_stack_s).
      !inversion IHh_eval_expr_e1;subst.
      !inversion IHh_eval_expr_e1;subst.
      cbn in heq_mod'.
      !inversion heq_mod';subst.
      constructor.
      constructor.
      !inversion IHh_eval_expr_e1.
      !inversion IHh_eval_expr_e2.
      !inversion h_inbound1.
      !inversion h_inbound2.
      apply andb_true_intro.
      apply andb_prop in heq_andb.
      apply andb_prop in heq_andb0.
      setoid_rewrite Z.leb_le in heq_andb.
      setoid_rewrite Z.leb_le in heq_andb0.
      decomp heq_andb.
      decomp heq_andb0.
      setoid_rewrite Z.leb_le.
      specialize (Z_lt_le_dec v2 0);intro hor.
      { !!destruct hor as [? | ?].
        - specialize Z.mod_neg_bound with (a:=v1)(1:=h_lt_v2_Z0);intro h_lt.
          decomp h_lt.
          split.
          + omega.
          + assert (max_signed>=0).
            { rewrite max_signed_ok.  apply Int.max_signed_pos. }
            omega.
        - !assert (0<v2).
          { apply  Zeq_bool_neq in heq_Z_false.
            omega. }
          specialize Z.mod_pos_bound with (a:=v1)(1:=h_lt_Z0_v2);intro h_lt.
          decomp h_lt.
          split.
          + assert (min_signed<0).
            { rewrite min_signed_ok. apply Int.min_signed_neg. }
            omega.
          + omega. }
    + rewrite binopexp_ok in *.
      functional inversion heq_binary_operation;subst
      ;try match goal with H: ?A <> ?A |- _ => elim H;auto end.
  - !invclear h_do_rtc_unop.
    + inversion h_overf_check;subst;auto.
    + rewrite unopexp_ok in *.
      !functional inversion heq_unary_operation;subst
      ;try match goal with H: ?A <> ?A |- _ => elim H;auto end.
Qed.

Lemma evalExp_overf2 : forall st s,
    safe_stack s ->
    forall (e:exp) e_v,
      evalExp st s e (OK e_v) -> check_overflow_value e_v.
Proof.
  !intros.
  destruct e_v;simpl in *;auto.
  eapply eval_expr_overf;eauto.
Qed.

Hint Resolve evalExp_overf2.

(* [make_load] does not fail on transl_type a translated variable coming
   from stbl *)
Lemma make_load_no_fail: forall stbl t nme_t x2,
    transl_type stbl t = Errors.OK x2 ->
    exists load_addr_nme, make_load nme_t x2 = Errors.OK load_addr_nme.
Proof.
  !intros.
  unfold make_load.
  destruct t;simpl in * ; simpl; try discriminate;eauto.
  - inversion heq_transl_type. subst.
    simpl.
    unfold make_load.
    simpl.
    eauto.
  - inversion heq_transl_type. subst.
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

Definition stack_no_null_offset stbl CE := forall a nme δ_lvl δ_id,
    transl_variable stbl CE a nme = Errors.OK (build_loads δ_lvl δ_id) ->
    4 <= Int.unsigned (Int.repr δ_id).

Definition stack_match_lgth (s : STACK.state) (CE : compilenv) :=
  Datatypes.length s = Datatypes.length CE.
(* The spark dynamic and the compiler static stack have the same structure. *)
Definition stack_match_CE (s : STACK.state) (CE : compilenv) :=
  forall nme lvl,(forall sto, STACK.frameG nme s = Some (lvl,sto) ->
                              exists CE_sto,
                                CompilEnv.frameG nme CE = Some (lvl,CE_sto))
                 ∧ forall CE_sto, CompilEnv.frameG nme CE = Some (lvl,CE_sto)
                                  -> exists sto, STACK.frameG nme s = Some (lvl,sto).


(* stack_match_CE must be true on all sub stacks *)
Inductive strong_stack_match_CE: STACK.state → compilenv → Prop :=
| Strg_smCE_nil: stack_match_CE [] [] -> strong_stack_match_CE [] []
| Strg_smCE_cons: forall lvl sto s stoCE CE,
    strong_stack_match_CE s CE ->
    stack_match_CE ((lvl,sto)::s) ((lvl,stoCE)::CE) ->
    strong_stack_match_CE ((lvl,sto)::s) ((lvl,stoCE)::CE).


Lemma nodup_stack_match_CE_strong:
  forall s CE,
    STACK.NoDup_G s ->
    CompilEnv.NoDup_G CE ->
    Datatypes.length s = Datatypes.length CE ->
    STACK.exact_levelG s -> CompilEnv.exact_levelG CE ->
    stack_match_CE s CE -> strong_stack_match_CE s CE.
Proof.
  induction s;destruct CE;!intros; try (cbn in heq_length; try discriminate).
  - now constructor.
  - !!destruct a,f.
    !inversion h_exct_lvl.
    !inversion h_exct_lvlG.
    !invclear heq_length.
    rewrite heq_length.
    constructor;auto.
    + apply IHs;auto.
      * eapply STACK.stack_CE_NoDup_G_cons with (1:=h_exct_lvl);eauto.
      * eapply CompilEnv.stack_CE_NoDup_G_cons with (1:=h_exct_lvlG);eauto.
      * red;!intros.
        red in H4.
        specialize (H4 nme lvl).
        destruct H4 as [h1 h2].
        split;!intros.
        -- specialize (h1 sto).
           !assert (STACK.frameG nme ((Datatypes.length s, s1) :: s) = Some (lvl, sto)).
           { !assert (STACK.resideG nme s = true).
             { eapply STACK.frameG_resideG_1;eauto. }
             specialize STACK.nodup_G_cons with (1:=h_exct_lvl) (2:=h_nodup_G_s) (3:=heq_resideG);intro h.
             cbn.
             cbn in h.
             rewrite h.
             assumption. }
           specialize h1 with (1:=heq_frameG0).
           decomp h1.
           cbn in heq_CEframeG_nme.
           !!destruct (CompilEnv.resides nme s3) eqn:?.
           ++ exfalso.
              inversion heq_CEframeG_nme;subst.
              rewrite <- heq_length in *.
              specialize STACK.exact_levelG_frameG_lt_lgth
                with (1:=h_exct_lvl_s) (2:=heq_frameG).
              intros.
              omega.
           ++ eauto.
        -- specialize (h2 CE_sto).
           !assert (CompilEnv.frameG nme ((Datatypes.length CE, s3) :: CE)
                    = Some (lvl, CE_sto)).
           { !assert (CompilEnv.resideG nme CE = true).
             { eapply CompilEnv.frameG_resideG_1;eauto. }
             specialize CompilEnv.nodup_G_cons with (1:=h_exct_lvlG)  (2:=h_nodup_G_CE) (3:=heq_resideG);intro h.
             cbn.
             cbn in h.
             rewrite h.
             assumption. }
           specialize h2 with (1:=heq_CEframeG_nme).
           decomp h2.
           cbn in heq_frameG.
           !!destruct (STACK.resides nme s1) eqn:?.
           ++ exfalso.
              !invclear heq_frameG;subst;up_type.
              rewrite heq_length in *.
              specialize CompilEnv.exact_levelG_frameG_lt_lgth
                with (1:=h_exct_lvlG_CE) (2:=heq_CEframeG_nme_CE).
              intros.
              omega.
           ++ eauto.
    + rewrite heq_length in H4.
      assumption.
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


Lemma nodup_stack_match_address_strong:
  forall st CE sp locenv g m,
    chained_stack_structure m (Datatypes.length CE) sp ->
    CompilEnv.NoDup_G CE ->
    CompilEnv.exact_levelG CE ->
    stack_match_addresses st CE sp locenv g m -> 
    strong_stack_match_addresses st CE sp locenv g m.
Proof.
  induction CE;!intros.
  - now constructor.
  - rename H2 into h_stack_match_addr.
    destruct a.
    !inversion h_chain_m;subst;up_type.
    econstructor 2;eauto.
    + apply IHCE with (1:=h_chain_m0) (locenv:=locenv);eauto.
      * eapply CompilEnv.stack_CE_NoDup_G_cons;eauto.
      * eapply CompilEnv.exact_levelG_sublist;eauto.
      * red in h_stack_match_addr |- *.
        !intros.
        !functional inversion heq_transl_name;subst.
        !functional inversion heq_transl_variable;subst.

        !assert (transl_name st ((s, s0) :: CE) (Identifier astnum id) = Errors.OK (build_loads (S(m' - m0)) n)).
        { cbn.
          unfold transl_variable;simpl.
          !assert (CompilEnv.fetch id (s, s0) = None).
          { destruct (CompilEnv.fetch id (s, s0)) eqn:heq;auto.
            exfalso.
            unfold CompilEnv.NoDup_G in h_nodup_G_CE.
            !assert (CompilEnv.frameG id ((s, s0) :: CE) = Some (s, s0)).
            { cbn.
              erewrite CompilEnv.fetches_ok;eauto. }
            specialize h_nodup_G_CE with (s':=(s, s0)::nil) (s'':=CE) (1:=heq_CEframeG_id).
            apply CompilEnv.fetchG_ok in heq_CEfetchG_id_CE.
            rewrite h_nodup_G_CE in heq_CEfetchG_id_CE.
            - inversion heq_CEfetchG_id_CE.
            - constructor;simpl;try auto with arith.
              eapply CompilEnv.cut_until_exct_lvl;eauto. }
          setoid_rewrite heq_CEfetch_id.
          rewrite heq_CEfetchG_id_CE.
          rewrite CompilEnv.fetch_ok_none;auto.
          rewrite heq_CEframeG_id_CE.
          !inversion h_exct_lvlG;subst.
          !destruct CE;try discriminate.
          !inversion h_exct_lvlG_CE.
          set (lCE:= Datatypes.length CE) in *|-*.
          simpl Datatypes.length.
          !inversion heq_lvloftop_CE_m'.
          assert (Datatypes.length CE >= m0)%nat.
          { eapply CompilEnv.exact_levelG_frameG_le_top;eauto. }
          replace (S (Datatypes.length CE) - m0)%nat
            with (S ((Datatypes.length CE) - m0))%nat by omega.
          unfold build_loads at 1 2.
          reflexivity.
        }
        specialize h_stack_match_addr with (1:=heq_transl_name0).
        decomp h_stack_match_addr.
        exists addr.
        simpl in h_chain_m.
        specialize chained_stack_structure_aux with (1:=h_chain_m) (g:=g)(e:=locenv);
          intro h.
        decomp h.
        rewrite h_loadv0 in h_loadv.
        !invclear h_loadv.
        !inversion h_CM_eval_expr_addr;subst.
        change (Eload AST.Mint32 (build_loads_ (Econst (Oaddrstack Int.zero)) (m' - m0)))
          with (build_loads_ (Econst (Oaddrstack Int.zero)) (S (m' - m0)))
          in h_CM_eval_expr_v1.
        !assert (chained_stack_structure m (S (m' - m0)) (Values.Vptr b Int.zero)).
        { apply chained_stack_structure_le with (n:=(S (Datatypes.length CE)));auto.
          apply CompilEnv.exact_levelG_sublist in h_exct_lvlG.
          specialize CompilEnv.exact_lvl_lvl_of_top with (1:=h_exct_lvlG);intro h.
          specialize (h _ heq_lvloftop_CE_m').
          rewrite <- h.
          omega. }
        specialize chained_stack_structure_decomp_S_2 with (1:=h_chain_m2);intro h.
        specialize h with (1:=h_CM_eval_expr_v1).
        decomp h.
        !inversion h_CM_eval_expr_sp';subst.
        !inversion h_CM_eval_expr_vaddr;subst.
        simpl in h_eval_constant.
        rewrite Int.add_zero_l in h_eval_constant.
        inversion h_eval_constant;subst.
        rewrite h_loadv_vaddr_sp' in h_loadv0.
        !invclear h_loadv0;subst.
        unfold build_loads.
        econstructor;eauto.
        inversion h_CM_eval_expr_v2;subst.
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
    CompilEnv.fetchG id CE = Some δ -> 0 <= δ < Integers.Int.modulus.

Proposition all_addr_nooverf_cons : forall x CE,
    CompilEnv.exact_levelG (x :: CE) ->
    CompilEnv.NoDup_G (x :: CE) ->
    all_addr_no_overflow (x:: CE) -> all_addr_no_overflow CE.
Proof.
  red.
  intros x CE h_exactlvl h_nodupG h_alladdr_nooverf id δ heq_fetchG. 
  apply h_alladdr_nooverf with id.
  cbn.
  specialize CompilEnv.nodup_G_cons with (1:=h_exactlvl)(2:=h_nodupG);intro h.
  !assert (CompilEnv.fetch id x = None).
  { apply CompilEnv.reside_false_fetch_none.
    apply h.
    eapply CompilEnv.fetchG_ok;eauto. }
  now rewrite heq_CEfetch_id_x.
Qed.

Lemma transl_name_nodup_cons : forall st CE nme lvl n fr,
    all_addr_no_overflow CE ->
    transl_name st CE nme = Errors.OK (build_loads lvl n) ->
    0 <= n ∧ n < Int.modulus ->
    CompilEnv.NoDup_G (fr :: CE) ->
    CompilEnv.exact_levelG (fr :: CE) ->
    transl_name st (fr::CE) nme = Errors.OK (build_loads (S lvl) n).
Proof.
  !intros.
  rename H into h_no_overf.
  red in h_nodup_G_CE.
  !functional inversion heq_transl_name;subst.
  specialize transl_variable_nodup_resideG with (1:=heq_transl_variable);!intro.
  simpl.
  unfold transl_variable.
  simpl.
  specialize CompilEnv.frameG_resideG_2 with (1:= heq_resideG);!intro.
  decomp h_ex.
  rewrite heq_CEframeG_id_CE.
  !assert (CompilEnv.fetch id fr = None).
  { apply CompilEnv.reside_false_fetch_none.
    apply CompilEnv.nodup_G_cons with (l:=CE);auto. }
  rewrite heq_CEfetch_id_fr.
  specialize CompilEnv.fetchG_ok_some with (1:=heq_resideG);!intros.
  decomp h_ex.
  rewrite heq_CEfetchG_id_CE.
  specialize CompilEnv.fetch_ok_none with (1:=heq_CEfetch_id_fr);!intro.
  rewrite heq_reside.
  destruct x, fr;simpl.
  !inversion h_exct_lvlG;subst.
  (*           !functional inversion heq_transl_variable. *)
  unfold transl_variable in heq_transl_variable.
  rewrite heq_CEfetchG_id_CE in heq_transl_variable.
  rewrite heq_CEframeG_id_CE in heq_transl_variable.
  specialize CompilEnv.exact_lvl_level_of_top with (1:=h_exct_lvlG_CE) (2:=heq_CEframeG_id_CE);!intro.
  decomp h_ex.          
  rewrite heq_lvloftop_CE_top in heq_transl_variable.
  inversion heq_transl_variable.
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
    apply CompilEnv.exact_lvl_lvl_of_top in heq_lvloftop_CE_top;auto.
    rewrite <- heq_lvloftop_CE_top.
    unfold Int.repr.
    !assert (s <= top)%nat.
    { specialize CompilEnv.exact_levelG_frameG_lt_lgth with (1:=h_exct_lvlG_CE)(2:=heq_CEframeG_id_CE);!intro.
      omega. }
    omega.
  - rewrite Int.eqm_small_eq with v n;eauto.
    Transparent Int.repr Int.intval.
    simpl in H1. 
    Opaque Int.repr Int.intval.
    red.
    apply Int.eqmod_trans with (v mod Int.modulus); try now apply Int.eqmod_mod;auto.
    apply Int.eqmod_trans with (n mod Int.modulus); try (apply Int.eqmod_sym;now apply Int.eqmod_mod;auto).
    setoid_rewrite Int.Z_mod_modulus_eq in H1.
    rewrite H1.
    apply Int.eqmod_refl.
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


Lemma nodup_stack_match_strong:
  forall st s CE sp locenv g m,
    chained_stack_structure m (Datatypes.length CE) sp ->
    all_addr_no_overflow CE ->
    STACK.NoDup_G s -> CompilEnv.NoDup_G CE ->
    STACK.exact_levelG s -> CompilEnv.exact_levelG CE ->
    Datatypes.length s = Datatypes.length CE ->
    stack_match st s CE sp locenv g m -> 
    strong_stack_match st s CE sp locenv g m.
Proof.
  !!induction s;!intros.
  - simpl in heq_length.
    destruct CE;try discriminate.
    now constructor.
  - rename H0 into h_no_overf.
    rename H6 into h_stack_mtch.
    destruct CE;try discriminate.
    up_type.
    destruct a, f.
    assert (s0 = s2).
    { transitivity (Datatypes.length s).
      2:transitivity (Datatypes.length CE).
      - now inversion h_exct_lvl.
      - simpl in heq_length.
        now inversion heq_length.
      - now inversion h_exct_lvlG_CE. }
    subst.
    !inversion h_chain_m;subst.
    econstructor 2;eauto.
    eapply IHs with (sp:=(Values.Vptr b' Int.zero)) (locenv:=locenv).
    all:swap 1 7.
    { simpl in heq_length.
      now inversion heq_length. }
    { red.
      !intros.
      red in h_no_overf.
      eapply h_no_overf with (id:=id);eauto.
      eapply CompilEnv.nodupG_fetchG_cons;eauto. } 
    { eapply STACK.stack_CE_NoDup_G_cons;eauto. }
    { eapply CompilEnv.stack_CE_NoDup_G_cons;eauto. }
    { eapply STACK.exact_levelG_sublist;eauto. }
    { eapply CompilEnv.exact_levelG_sublist;eauto. }
    + assumption.
    + clear IHs. up_type.
      simpl in h_chain_m.
      simpl in heq_length.
      apply eq_add_S in heq_length.
      red;!intros.
      !functional inversion heq_transl_name;subst.
      !functional inversion heq_transl_variable;subst.
      !assert (chained_stack_structure m (S (m' - m0)) (Values.Vptr b Int.zero)).
      { eapply chained_stack_structure_le;eauto.
        specialize CompilEnv.exact_lvl_lvl_of_top with (2:=heq_lvloftop_CE_m');intro h.
        rewrite <- h.
        ** omega.
        ** inversion h_exct_lvlG_CE;auto. }
      !functional inversion heq_make_load.
      subst.
      unfold build_loads in h_CM_eval_expr_nme_t_nme_t_v.
      red in h_stack_mtch.
      specialize h_stack_mtch with (vaddr:=nme_t_v) (nme := (Identifier astnum id)) (v:=v)
                                   (addr_nme:=(build_loads (S(m' - m0)) n))(load_addr_nme:=(Eload chunk (build_loads (S(m' - m0)) n)))
                                   (4:=heq_transl_type)(5:=heq_type_of_name).
      assert (all_addr_no_overflow CE) as h_nooverf by (eapply all_addr_nooverf_cons;eauto).
      !destruct h_stack_mtch.
      * apply transl_name_nodup_cons;auto.
        eapply h_nooverf;eauto.
      * unfold build_loads.
        !inversion h_CM_eval_expr_nme_t_nme_t_v;subst.
        econstructor;eauto.
        -- eapply chained_stack_structure_decomp_S_2';eauto.
           econstructor;eauto.
           eapply cm_eval_addrstack_zero_chain;eauto.
        -- eapply eval_expr_const_indep;eauto.
      * inversion  h_eval_name_nme_v;subst.
        econstructor.
        eapply STACK.nodupG_fetchG_cons;eauto.
      * unfold build_loads, make_load.
        now rewrite h_access_mode_cm_typ_nme.
      * up_type.
        !destruct h_and.
        exists x;split;auto.
        Opaque build_loads_.
        unfold build_loads in h_CM_eval_expr_x |- *.
        Transparent build_loads_.
        !inversion h_CM_eval_expr_x;subst.
        econstructor.
        2:eauto.
        !inversion h_CM_eval_expr_vaddr;subst.
        econstructor;eauto.
        -- specialize chained_stack_structure_decomp_S_2 with (1:=h_chain_m1) (2:=h_CM_eval_expr_v1) ;intro h.
           decomp h.
           assert (sp'=(Values.Vptr b' Int.zero)).
              { !inversion h_CM_eval_expr_sp';subst.
                assert (vaddr0=(Values.Vptr b Int.zero)).
                { eapply det_cm_eval_addrstack_zero_chain;eauto. }
                subst.
                rewrite h_loadv_vaddr0_sp' in h_loadv.
                now inversion h_loadv. }
              subst.
              assumption.
        -- eapply eval_expr_const_indep;eauto.
Qed.        




(* We have translated all procedures of stbl, and they have all an address
   pointing to there translation *)
Definition stack_match_functions st stckptr CE locenv g m :=
  forall p pb_lvl pb,
    symboltable.fetch_proc p st = Some (pb_lvl, pb) (* p exists in st *)
    -> exists CE' CE'' paddr pnum fction lglobdef, (* then there we can compute its address in Cminor. *)
      CompilEnv.cut_until CE pb_lvl CE' CE''
      ∧ transl_procedure st CE'' pb_lvl pb = Errors.OK ((pnum,@AST.Gfun _ _ fction) :: lglobdef) (*  *)
      ∧ Cminor.eval_expr g stckptr locenv m
                         (Econst (Oaddrsymbol (transl_procid p) (Int.repr 0))) paddr
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
     \/ Int.unsigned δ₂ + Memdata.size_chunk chnk₂ <= Int.unsigned δ₁
     \/ Int.unsigned δ₁ + Memdata.size_chunk chnk₁ <= Int.unsigned δ₂).

Definition stack_freeable st CE sp g locenv m :=
  forall a chk id id_t b ofs,
    (* translating the variabe to a Cminor load address *)
    transl_variable st CE a id = Errors.OK id_t ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g sp locenv m id_t (Values.Vptr b ofs) ->
    (* Size of variable in Cminor memorry *)
    compute_chnk st (Identifier a id) = Errors.OK chk ->
    Mem.valid_access m chk b (Int.unsigned ofs) Freeable.


(* TODO: swap arguments *)
Definition gt_snd (x y:(idnum * CompilEnv.V)) := snd y < snd x.
Definition gt_fst (x y:(CompilEnv.scope_level * localframe)) := (fst y < fst x)%nat.

Definition eq_fst_idnum (x y : idnum * CompilEnv.V) := fst x = fst y.

Arguments eq_fst_idnum !x !y.
Hint Unfold eq_fst_idnum.

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

Hint Resolve gt_snd_1 gt_snd_2 gt_fst_1 gt_fst_2.

(* Local frames are ordered in the sense that they are stored by increasing offests. *)
Definition increasing_order: localframe -> Prop :=
  StronglySorted gt_snd.

Definition increasing_order_fr (f:CompilEnv.frame) :=
  increasing_order(CompilEnv.store_of f).

Definition all_frm_increasing CE := Forall increasing_order_fr CE.


Definition upper_bound fr sz := forall nme nme_ofs,
    CompilEnv.fetches nme fr = Some nme_ofs -> Zlt nme_ofs sz.

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
      me_stack_no_null_offset: stack_no_null_offset st CE;
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
      (* me_stack_complete: stack_complete st s CE; useless now that stack_match_CE is in both directions *)
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

Hint Resolve ci_exact_lvls ci_increasing_ids ci_no_overflow ci_stbl_var_types_ok ce_nodup_G_CE ce_nodup_G_CE.
Hint Resolve me_stack_match_addresses me_stack_match_functions me_stack_separate me_stack_localstack_aligned
     me_stack_no_null_offset me_stack_freeable me_chain_struct.
Hint Resolve me_stack_match me_stack_match_CE me_stack_match_lgth (* me_stack_complete *) me_overflow me_safe_cm_env.

(*
Inductive strong_match_env stbl: STACK.state → compilenv → Values.val → env → genv → mem → Prop :=
| C1: forall v locenv g m,
    match_env stbl [] [] v locenv g m ->
    strong_match_env stbl [] [] v locenv g m
| C2: forall lvl sto s stoCE CE v v' locenv locenv' g m,
    strong_match_env stbl s CE v locenv g m ->
    Mem.loadv AST.Mint32 m v' = Some v ->
    match_env stbl ((lvl,sto)::s) ((lvl,stoCE)::CE) v' locenv' g m ->
    strong_match_env stbl ((lvl,sto)::s) ((lvl,stoCE)::CE) v' locenv' g m.



Definition strong_match_env_2 (st : symboltable) (s : STACK.state) (CE : compilenv)
           (sp : Values.val) (locenv : env) (g : genv) (m : mem) : Prop :=
  forall lvl CE' CE'',
    CompilEnv.cut_until CE lvl CE' CE'' ->
    Datatypes.length CE'' = lvl ->
    exists sp'',
      (* following chaining params starting from the current one *)
      repeat_Mem_loadv AST.Mint32 m lvl sp sp''
      ∧ exists s' s'' locenv'', STACK.cut_until s lvl s' s''  ∧  match_env st s'' CE'' sp'' locenv'' g m.
*)

(** Hypothesis renaming stuff *)
Ltac rename_hyp3 h th :=
  match th with
  | upper_bound ?fr ?sz => fresh "h_upb_" fr "_" sz
  | upper_bound ?fr _ => fresh "h_upb_" fr
  | upper_bound _ _ => fresh "h_upb"
  | match_env _ _ _ _ _ _ _ => fresh "h_match_env"
  | stack_match _ ?s _ _ _ _ ?m => fresh "h_stk_mtch_" s "_" m
  | stack_match _ _ _ _ _ _ _ => fresh "h_stk_mtch"
  | stack_match_addresses _ _ ?CE _ _ ?m => fresh "h_stk_mtch_addr_" CE "_" m
  | stack_match_addresses _ _ ?CE _ _ _ => fresh "h_stk_mtch_addr_" CE
  | stack_match_addresses _ _ _ _ _ _ => fresh "h_stk_mtch_addr"
  | stack_match_CE ?s ?CE => fresh "h_stk_mtch_CE_" s "_" CE
  | stack_match_CE ?s _ => fresh "h_stk_mtch_CE_" s
  | stack_match_CE _ _ => fresh "h_stk_mtch_CE"
  | stack_match_lgth ?s ?CE => fresh "h_stk_mtch_lgth_" s "_" CE
  | stack_match_lgth ?s _ => fresh "h_stk_mtch_lgth_" s
  | stack_match_lgth _ _ => fresh "h_stk_mtch_lgth"
  | stack_match_functions _ _ _ _ _ _ => fresh "h_stk_mtch_fun"
  | stack_complete _ ?s ?CE => fresh "h_stk_cmpl_" s "_" CE
  | stack_complete _ ?s _ => fresh "h_stk_cmpl_" s
  | stack_complete _ _ _ => fresh "h_stk_cmpl"
  | stack_no_null_offset _ _ => fresh "h_nonul_ofs"
  | stack_no_null_offset _ ?CE => fresh "h_nonul_ofs_" CE
  | stack_no_null_offset ?s _ => fresh "h_nonul_ofs_" s
  | stack_no_null_offset _ _ => fresh "h_nonul_ofs"
  | stack_separate _ ?CE _ _ _ ?m => fresh "h_separate_" CE "_" m
  | stack_separate _ _ _ _ _ ?m => fresh "h_separate_" m
  | stack_separate _ ?CE _ _ _ _ => fresh "h_separate_" CE
  | stack_separate _ _ _ _ _ _ => fresh "h_separate"
  | stack_freeable _ ?CE _ _ _ ?m => fresh "h_freeable_" CE "_" m
  | stack_freeable _ _ _ _ _ ?m => fresh "h_freeable_" m
  | stack_freeable _ ?CE _ _ _ _ => fresh "h_freeable_" CE
  | stack_freeable _ _ _ _ _ _ => fresh "h_freeable"
  | safe_cm_env ?st ?CE ?stkptr ?locenv ?g ?m => fresh "h_safe_cm_" CE "_" m
  | safe_cm_env ?st ?CE ?stkptr ?locenv ?g ?m => fresh "h_safe_cm_" CE
  | safe_cm_env ?st ?CE ?stkptr ?locenv ?g ?m => fresh "h_safe_cm"
  | invariant_compile ?CE ?stbl => fresh "h_inv_comp_" CE "_" stbl
  | invariant_compile ?CE _ => fresh "h_inv_comp_" CE
  | invariant_compile _ ?stbl => fresh "h_inv_comp_" stbl
  | invariant_compile _ _ => fresh "h_inv_comp"
  | increasing_order ?l => fresh "h_incr_gt_" l
  | increasing_order _ => fresh "h_incr_ord"
  | _ => rename_hyp2' h th
  end.

Ltac rename_sparkprf ::= rename_hyp3.

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
Ltac rename_sparkprf ::= rename_hyp4.

Ltac rename_hyp_cut h th :=
  match th with
  | CompilEnv.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_CEcut_" CE "_" lvl
  | CompilEnv.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_CEcut_" CE
  | CompilEnv.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_CEcut"
  | STACK.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_stkcut_" CE "_" lvl
  | STACK.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_stkcut_" CE
  | STACK.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_stkcut"
(*   | CE_well_formed ?CE => fresh "h_CEwf_" CE *)
(*   | CE_well_formed ?CE => fresh "h_CEwf" *)
  | CompilEnv.NoDup ?CE => fresh "h_CEnodup_" CE
  | CompilEnv.NoDup ?CE => fresh "h_CEnodup"
  | CompilEnv.NoDup_G ?CE => fresh "h_CEnodupG" CE
  | CompilEnv.NoDup_G ?CE => fresh "h_CEnodupG"
  | _ => rename_hyp4 h th                                
  end.
Ltac rename_sparkprf ::= rename_hyp_cut.


Ltac rename_hyp_strong h th :=
  match th with
(*
  | strong_match_env ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch_" s "_" CE "_" m
  | strong_match_env ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch_" s "_" CE
  | strong_match_env ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch_" s
  | strong_match_env ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch"

  | strong_match_env_2 ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch2_" s "_" CE "_" m
  | strong_match_env_2 ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch2_" s "_" CE
  | strong_match_env_2 ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch2_" s
  | strong_match_env_2 ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch2"
*)
  | _ => rename_hyp_cut h th
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

Definition stack_push_all_new sto CE:= (forall id, CompilEnv.reside id sto = true -> CompilEnv.resideG id CE = false).


Lemma all_addr_no_overflow_sublist: forall x CE,
    stack_push_all_new x CE
    -> all_addr_no_overflow (x::CE)
    -> all_addr_no_overflow CE.
Proof.
  !!intros ? ? h halladdr.
  red in halladdr.
  red.
  !intros.
  apply halladdr with id.
  cbn.
  !!destruct (CompilEnv.fetch id x) eqn:?.
  - apply CompilEnv.fetch_ok in heq_CEfetch_id_x.
    apply h in heq_CEfetch_id_x.
    apply CompilEnv.fetchG_ok in heq_CEfetchG_id_CE.
    rewrite heq_CEfetch_id_x in heq_CEfetchG_id_CE.
    discriminate.
  - assumption.
Qed.

Lemma stack_push_all_new_subcons:
  forall a CE,
    CompilEnv.NoDup_G (a :: CE) ->
    CompilEnv.exact_levelG (a :: CE) ->
    stack_push_all_new a CE.
Proof.
  !intros.
  red;!intros.
  red in h_CEnodupG.
  specialize (h_CEnodupG id (CompilEnv.level_of a) (CompilEnv.store_of a) [a] CE).
  !assert (CompilEnv.frameG id (a :: CE) = Some (CompilEnv.level_of a, CompilEnv.store_of a)).
  { cbn.
    rewrite heq_reside.
    destruct a;auto. }
  specialize (h_CEnodupG heq_CEframeG_id).
  !assert (CompilEnv.cut_until (a :: CE) (CompilEnv.level_of a) [a] CE).
  { econstructor 3.
    - omega.
    - !!destruct CE eqn:?.
      + constructor.
      + !!inversion h_exct_lvlG;subst.
        cbn.
        constructor 2.
        inversion h_exct_lvlG0.
        cbn.
        omega. }
  specialize (h_CEnodupG h_CEcut).
  assumption.
Qed.



Lemma stack_CE_NoDup_G_stack_push_all_new: forall x CE,
    CompilEnv.exact_levelG (x::CE) ->
    CompilEnv.NoDup_G (x::CE) -> 
    stack_push_all_new x CE.
Proof.
  !intros.
  red;!intros.
  red in h_CEnodupG.
  cbn in h_CEnodupG.
  destruct x.
  eapply h_CEnodupG with (nme:= id).
  - rewrite heq_reside.
    reflexivity.
  - constructor 3;auto with arith.
    eapply CompilEnv.cut_until_exct_lvl;eauto.
Qed.


Lemma invariant_compile_subcons: forall st x CE,
    invariant_compile (x::CE) st
    -> invariant_compile CE st.
Proof.
  !intros.
  inversion h_inv_comp_st;cbn in *.
  split;eauto.
  - eapply CompilEnv.exact_levelG_sublist;eauto.
  - eapply all_frm_increasing_sublist;eauto.
  - eapply all_addr_no_overflow_sublist;eauto.
    apply stack_CE_NoDup_G_stack_push_all_new;auto.
  - eapply CompilEnv.stack_CE_NoDup_cons;eauto.
  - eapply CompilEnv.stack_CE_NoDup_G_cons;eauto.
Qed.




Lemma invariant_compile_sublist: forall st CE1 CE2,
    invariant_compile (CE1 ++ CE2) st
    -> invariant_compile CE2 st.
Proof.
  !!induction CE1;simpl;!intros.
  - auto.
  - apply IHCE1;auto.
    eapply invariant_compile_subcons;eauto.
Qed.




Lemma exact_lvlG_lgth: forall CE lvl,
    CompilEnv.exact_levelG CE ->
    CompilEnv.level_of_top CE = Some lvl ->
    List.length CE = S lvl.
Proof.
  intros CE lvl H.
  revert lvl.
  induction H.
  - !intros; discriminate.
  - intros lvl H0.
    cbn in H0.
    !inversion H0;simpl;clear H0.
    reflexivity.
Qed.

Lemma exact_lvlG_lgth_none: forall CE,
    CompilEnv.exact_levelG CE ->
    CompilEnv.level_of_top CE = None ->
    List.length CE = 0%nat.
Proof.
  intros CE H H0.
  destruct CE;cbn in *;try discriminate;auto.
  destruct f;try discriminate.
Qed.



Lemma exact_lvlG_cut_until: forall CE lvl CE' CE'',
    CompilEnv.exact_levelG CE ->
    CompilEnv.cut_until CE lvl CE' CE'' ->
    CompilEnv.exact_levelG CE''.
Proof.
  !!intros until 1.
  revert lvl CE' CE''.
  !induction h_exct_lvlG_CE;!intros .
  - !inversion h_CEcut;subst.
    constructor.
  - !inversion h_CEcut.
    + constructor.
      assumption.
    + eapply IHh_exct_lvlG_CE;eauto.
Qed.

Lemma exact_lvlG_nil_left: forall CE,
  CompilEnv.exact_levelG CE ->
  CompilEnv.cut_until CE (Datatypes.length CE) [ ] CE.
Proof.
  intros CE.
  destruct CE;simpl;!intros.
  - constructor.
  - constructor.
    inversion h_exct_lvlG.
    simpl.
    omega.
Qed.

Lemma stack_match_empty: forall st sp locenv g m,
    stack_match st [] [] sp locenv g m.
Proof.
  intros st sp locenv g m.
  red;!intros.
  functional inversion heq_transl_name.
Qed.

Lemma stack_match_addresses_empty: forall st sp locenv g m,
    stack_match_addresses st [] sp locenv g m.
Proof.
  !intros.
  red;!intros.
  functional inversion heq_transl_name.
Qed.

Lemma stack_match_CE_empty: stack_match_CE [] [].
Proof.
  red;!intros.
  split;!intros.
  - functional inversion heq_frameG.
  - cbn in *.
    discriminate.
Qed.

Lemma stack_match_lgth_empty: stack_match_lgth [] [].
Proof.
  now red.
Qed.
 
Lemma stack_complete_empty: forall st,stack_complete st [ ] [ ].
Proof.
  red;!intros.
  !functional inversion heq_transl_variable.    
  functional inversion heq_CEfetchG_nme.
Qed.

Lemma stack_separate_empty: forall st sp locenv g m,
    stack_separate st [ ] sp locenv g m.
Proof.
  red;!intros.
  !functional inversion heq_transl_name.
Qed.
 
(* frame pointer is always with offset zero. We will show later that it is also true for the enclosing frames. *)
Lemma match_env_sp_zero:forall st CE x sp locenv g m, match_env st CE x sp locenv g m -> exists b, sp = Values.Vptr b Int.zero.
Proof.
  !intros. 
  !!pose proof (me_stack_localstack_aligned (me_safe_cm_env h_match_env)).
  red in h_aligned_g_m.
  !!assert (O ≤ Datatypes.length x) by omega.
  specialize h_aligned_g_m with (1:=h_le_O).
  decomp h_aligned_g_m.
  cbn in*.
  exists b_δ.
  !inversion h_CM_eval_expr.
  cbn in h_eval_constant.
  !inversion h_eval_constant.
  unfold Values.Val.add in h_val_add_sp.
  destruct sp;try discriminate.
  cbn.
  rewrite Int.add_zero.
  reflexivity.
Qed.

(* TODO: move this in spark. *)
Lemma stack_NoDup_empty: STACK.NoDup [ ].
Proof.
  red;simpl;!intros.
  discriminate.
Qed.

Lemma stack_NoDup_G_empty: STACK.NoDup_G [ ].
Proof.
  red;simpl;!intros.
  discriminate.
Qed.

Lemma match_env_empty: forall st sp b sp' locenv locenv' g m,
    stack_match_functions st sp' [ ] locenv' g m ->
    sp = (Values.Vptr b Int.zero) ->
    match_env st [ ] [ ] sp locenv g m.
Proof.
  !intros.
  split (* apply h_match_env. *).
  7: split.
  + apply stack_match_empty.
  + red;!intros.
    split;!intros.
    * functional inversion heq_frameG.
    * cbn in heq_CEframeG_nme.
      discriminate.
  + now red.
  + apply stack_NoDup_empty.
  + apply stack_NoDup_G_empty.
  + constructor.
(*  + red;!intros.
    !functional inversion heq_transl_variable.
    functional inversion heq_CEfetchG_nme.*)
  + apply stack_match_addresses_empty.
  + red;!intros.
    red in h_stk_mtch_fun.
    specialize h_stk_mtch_fun with (1:=h_fetch_proc_p).
    !!decomp h_stk_mtch_fun.
    up_type.
    exists CE', CE'', paddr, pnum, fction, lglobdef.
    repeat split;auto.
    constructor.
    inversion h_CM_eval_expr_paddr;subst; simpl in *.
    assumption.
  + red;!intros.
    functional inversion heq_transl_name.
  + red.
    !intros.
    simpl in *.
    assert(δ_lvl = 0)%nat by omega.
    subst;cbn.
    eexists.
    econstructor.
    cbn.
    rewrite Int.add_zero.
    reflexivity.
  + red;!intros.
    !functional inversion heq_transl_variable.
    functional inversion heq_CEfetchG_nme.
  + red.
    !intros.
    exfalso.
    !functional inversion heq_transl_variable.
    functional inversion heq_CEfetchG_id.
  + cbn. subst. constructor.
  + red;!intros.
    functional inversion heq_SfetchG_id.
Qed.


Lemma eval_expr_Econst_inv_locenv :  forall g sp locenv m c v,
    Cminor.eval_expr g sp locenv m (Econst c) v -> 
    forall locenv' m' , Cminor.eval_expr g sp locenv' m' (Econst c) v.
Proof.
  intros g sp locenv m c v H locenv' m'.
  inversion H.
  now constructor.
Qed.

Definition invariant_to_locenv g sp m exp :=
  forall l l' x, Cminor.eval_expr g sp l m exp x -> Cminor.eval_expr g sp l' m exp x.


Lemma eval_expr_build_loads_inv_locenv :  forall δ_lvl g sp locenv m base nme_t_v,
    (* base's evaluation is independent of the local environment *)
    invariant_to_locenv g sp m base ->
    Cminor.eval_expr g sp locenv m (build_loads_ base δ_lvl) nme_t_v ->
    forall locenv',
      Cminor.eval_expr g sp locenv' m (build_loads_ base δ_lvl) nme_t_v.
Proof.
  intros δ_lvl.
  !!(induction δ_lvl;simpl;intros).
  - eapply H;eauto.
  - inversion h_CM_eval_expr_nme_t_v.
    econstructor;eauto.
Qed.

Lemma Econst_locenv_indep g sp m const: invariant_to_locenv g sp m (Econst const).
Proof.
  red.
  !intros.
  !inversion h_CM_eval_expr_x.
  econstructor;eauto.
Qed.

Lemma eval_expr_build_load_const_inv_locenv :  forall δ_id g sp locenv m cste nme_t_v,
    Cminor.eval_expr g sp locenv m (build_loads_ (Econst cste) δ_id) nme_t_v ->
    forall locenv',
      Cminor.eval_expr g sp locenv' m (build_loads_ (Econst cste) δ_id) nme_t_v.
Proof.
  !intros.
  unfold build_loads in *.
  eapply eval_expr_build_loads_inv_locenv;eauto.
  apply Econst_locenv_indep.
Qed.

Lemma eval_expr_build_load_inv_locenv :  forall δ_lvl δ_id g sp locenv m  nme_t_v,
    Cminor.eval_expr g sp locenv m (build_loads δ_lvl δ_id) nme_t_v ->
    forall locenv',
      Cminor.eval_expr g sp locenv' m (build_loads δ_lvl δ_id) nme_t_v.
Proof.
  !intros.
  unfold build_loads in *.
  !inversion h_CM_eval_expr_nme_t_v.
  econstructor;eauto.
  - eapply eval_expr_build_load_const_inv_locenv;eauto.
  - eapply eval_expr_Econst_inv_locenv;eauto.
Qed.

Lemma eval_expr_transl_variable_inv_locenv: forall st CE astnum g sp locenv m nme nme_t v,
          transl_variable st CE astnum nme = Errors.OK nme_t ->
          Cminor.eval_expr g sp locenv m nme_t v ->
          forall locenv', Cminor.eval_expr g sp locenv' m nme_t v.
Proof.
  !intros.
  !functional inversion heq_transl_variable;subst.
  eapply eval_expr_build_load_inv_locenv;eauto.
Qed.

Lemma eval_expr_transl_name_inv_locenv: forall st CE  g sp locenv m nme nme_t v,
          transl_name st CE nme = Errors.OK nme_t ->
          Cminor.eval_expr g sp locenv m nme_t v ->
          forall locenv', Cminor.eval_expr g sp locenv' m nme_t v.
Proof.
  !intros.
  !functional inversion heq_transl_name;subst.
  eapply eval_expr_transl_variable_inv_locenv;eauto.
Qed.

Lemma stack_match_addr_inv_locenv :  forall st CE sp locenv g m,
    stack_match_addresses st sp CE locenv g m -> 
    forall locenv',
      stack_match_addresses st sp CE locenv' g m.
Proof.
  !intros.
  red.
  !intros.
  red in h_stk_mtch_addr_CE_m.
  specialize h_stk_mtch_addr_CE_m with (1:= heq_transl_name).
  decomp h_stk_mtch_addr_CE_m.
  eexists.
  eapply eval_expr_transl_name_inv_locenv;eauto.
Qed.
      
Lemma stack_match_inv_locenv :  forall st s CE sp locenv g m,
    stack_match st s CE sp locenv g m -> 
    forall locenv',
      stack_match st s CE sp locenv' g m.
Proof.
  !intros.
  red.
  !intros.
  red in h_stk_mtch_s_m.
  specialize h_stk_mtch_s_m with(vaddr := nme_t_v) (3:=h_eval_name_nme_v) (5:=heq_type_of_name) (1:=heq_transl_name) (4:=heq_transl_type) (6:=heq_make_load).
  !!destruct h_stk_mtch_s_m as [? [? ?]].
  - eapply eval_expr_transl_name_inv_locenv;eauto.
  - exists load_addr_nme_v;split;auto.
    !functional inversion heq_make_load;subst.
    !inversion h_CM_eval_expr_load_addr_nme_load_addr_nme_v.
    econstructor;eauto.
    !functional inversion heq_transl_name;subst.
    !functional inversion heq_transl_variable;subst.
    rewrite <- h_loadv_nme_t_v0_load_addr_nme_v.
    f_equal.
    eapply det_eval_expr;eauto.
    eapply eval_expr_build_load_inv_locenv;eauto.
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
  !intros.
  split;[ | | | | | | split | ];try now apply h_match_env.  
  - eapply stack_match_inv_locenv;eauto.
  - eapply stack_match_addr_inv_locenv; eauto.
  - pose proof me_stack_match_functions (me_safe_cm_env h_match_env) as h_mtch_fun.
    red in h_mtch_fun.
    red;!intros.
    specialize h_mtch_fun with (1:=h_fetch_proc_p).
    decomp h_mtch_fun.
    repeat eexists;eauto.
    eapply eval_expr_Econst_inv_locenv;eauto.
  - pose proof me_stack_separate (me_safe_cm_env h_match_env) as h_separate.
    red in h_separate.
    red;!intros.
    !assert (Cminor.eval_expr g sp locenv m nme_t (Values.Vptr k₁ δ₁)).
    { pose proof (stack_match_inv_locenv st s CE sp locenv' g m) as h_stckmtch.
      eapply eval_expr_transl_name_inv_locenv;eauto. }
    !assert (Cminor.eval_expr g sp locenv m nme'_t (Values.Vptr k₂ δ₂)).
    { pose proof (stack_match_inv_locenv st s CE sp locenv' g m) as h_stckmtch.
      eapply eval_expr_transl_name_inv_locenv;eauto. }
    specialize (h_separate _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq_type_of_name heq_type_of_name0
                           heq_transl_name heq_transl_name0 heq_transl_type heq_transl_type0
                           h_CM_eval_expr_nme_t0 h_CM_eval_expr_nme'_t0 h_access_mode_cm_typ_nme
                           h_access_mode_cm_typ_nme' hneq).
    assumption.
  - pose proof me_stack_localstack_aligned (me_safe_cm_env h_match_env) as h_align.
    red in h_align.
    red.
    !intros.
    specialize (h_align _ h_le_δ_lvl).
    decomp h_align;eauto.
    exists b_δ. 
    eapply eval_expr_build_load_const_inv_locenv;eauto.
  - !!pose proof me_stack_freeable (me_safe_cm_env h_match_env).
    red in h_freeable_CE_m.
    red;!intros.
    eapply h_freeable_CE_m;eauto.
    eapply eval_expr_transl_variable_inv_locenv;eauto.
Qed.

(*
Lemma strong_match_env_inv_locenv : forall st s CE sp locenv g m,
    strong_match_env st s CE sp locenv g m ->
    forall locenv', strong_match_env st s CE sp locenv' g m.
Proof.
  !!intros until 1.
  !induction h_strg_mtch_s_CE_m;!intros.
  - constructor.
    eapply match_env_inv_locenv;eauto.
  - econstructor;eauto.
    eapply match_env_inv_locenv;eauto.
Qed.
*)

Lemma stack_match_functions_inv_locenv: forall stbl CE stkptr locenv g m,
    stack_match_functions stbl CE stkptr locenv g m ->
    forall locenv', stack_match_functions stbl CE stkptr locenv' g m.
Proof.
  !intros.
  red.
  !intros.
  decomp (h_stk_mtch_fun _ _ _ h_fetch_proc_p).
  exists CE',  CE'', paddr, pnum, fction, lglobdef;repeat apply conj; eauto 10.
  inversion h_CM_eval_expr_paddr.
  econstructor;eauto.
Qed.

Lemma stack_localstack_aligned_inv_locenv: forall lvl locenv g m sp,
    stack_localstack_aligned lvl locenv g m sp ->
    forall locenv', stack_localstack_aligned lvl locenv' g m sp.
Proof.
  !intros.
  red.
  !intros.
  decomp (h_aligned_g_m _ h_le_δ_lvl_lvl).
  exists b_δ.
  eapply eval_expr_build_load_const_inv_locenv;eauto.
Qed.

Lemma stack_separate_inv_locenv: forall st CE sp locenv g m,
    stack_separate st CE sp locenv g m ->
    forall locenv', stack_separate st CE sp locenv' g m.
Proof.
  !intros.
  red.
  !intros.
  red in h_separate_CE_m.
  !!pose proof eval_expr_transl_name_inv_locenv _ _ _ _ _ _ _ _ _ heq_transl_name h_CM_eval_expr_nme_t locenv.
  !!pose proof eval_expr_transl_name_inv_locenv _ _ _ _ _ _ _ _ _ heq_transl_name0 h_CM_eval_expr_nme'_t locenv.
  decomp (h_separate_CE_m _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq_type_of_name heq_type_of_name0 heq_transl_name heq_transl_name0 heq_transl_type heq_transl_type0 h_CM_eval_expr_nme_t0 h_CM_eval_expr_nme'_t0 h_access_mode_cm_typ_nme h_access_mode_cm_typ_nme' hneq)
  ;eauto.
Qed.

Lemma stack_freeable_inv_locenv: forall st CE sp locenv g m,
    stack_freeable st CE sp g locenv m ->
    forall locenv', stack_freeable st CE sp g locenv' m.
Proof.
  !intros.
  red.
  !intros.
  red in h_freeable_CE_m.
  !!pose proof eval_expr_transl_variable_inv_locenv _ _ _ _ _ _ _ _ _ _ heq_transl_variable h_CM_eval_expr_id_t locenv.
  eapply h_freeable_CE_m;eauto.
Qed.

Lemma safe_cm_env_inv_locenv: forall stbl CE stkptr locenv g m,
    safe_cm_env stbl CE stkptr locenv g m ->
    forall locenv', safe_cm_env stbl CE stkptr locenv' g m.
Proof.
  !intros.
  constructor;eauto.
  - eapply stack_match_addr_inv_locenv;eauto.
  - eapply stack_match_functions_inv_locenv;eauto.
  - eapply stack_separate_inv_locenv;eauto.
  - eapply stack_localstack_aligned_inv_locenv;eauto.
  - eapply stack_freeable_inv_locenv;eauto.
Qed.

Lemma cut_until_exact_lvl:
  forall stoCE CE lvl,
    CompilEnv.exact_levelG (stoCE :: CE)
    -> CompilEnv.cut_until (stoCE :: CE) lvl [ ] (stoCE :: CE)
    -> CompilEnv.cut_until CE lvl [ ] CE.
Proof.
  !intros.
  !destruct CE.
  - constructor.
  - !inversion h_CEcut;subst.
    !destruct f.
    !inversion h_exct_lvlG;subst;simpl in *.
    constructor 2.
    simpl.
    inversion h_exct_lvlG0;subst.
    omega.
Qed.


Lemma cut_until_total: forall s lvl, exists s1 s2, STACK.cut_until s lvl s1 s2.
Proof.
  !intros. 
  !induction s.
  - exists (@nil STACK.frame).
    exists (@nil STACK.frame).
    constructor.
  - destruct (Nat.lt_decidable (STACK.level_of a) lvl).
    + exists (@nil STACK.frame).
      exists (a :: s).
      constructor 2;auto.
    + decomp h_ex.
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
  !intros.
  !!pose proof cut_until_total s lvl.
  decomp h_ex.
  exists s1,s2.
  split;auto.
  !destruct (Nat.le_decidable lvl (Datatypes.length s)).
  - specialize STACK.cut_until_exact_levelG with (1:=h_exct_lvl_s) (2:=h_le_lvl)(3:=h_stkcut_s_lvl);!intro.
    !assert (lvl ≤ Datatypes.length CE).
    { red in h_stk_mtch_lgth_s_CE.
      now rewrite <- h_stk_mtch_lgth_s_CE. }
    specialize CompilEnv.cut_until_exact_levelG with (1:=h_exct_lvlG_CE) (2:=h_le_lvl0) (3:=h_CEcut_CE_lvl);!intro.
    specialize CompilEnv.cut_until_spec1 with (1:=h_CEcut_CE_lvl);!intro.
    specialize STACK.cut_until_spec1 with (1:=h_stkcut_s_lvl);!intro.
    subst.
    red in h_stk_mtch_lgth_s_CE.
    setoid_rewrite app_length in h_stk_mtch_lgth_s_CE.
    omega.
  - !!assert ((lvl > Datatypes.length s)%nat) by omega.
    
    specialize STACK.cut_until_exact_levelG_2 with (1:=h_exct_lvl_s) (2:=h_gt_lvl)(3:=h_stkcut_s_lvl);!intro.
    !assert (lvl > Datatypes.length CE)%nat.
    { red in h_stk_mtch_lgth_s_CE.
      now rewrite <- h_stk_mtch_lgth_s_CE. }
    specialize CompilEnv.cut_until_exact_levelG_2 with (1:=h_exct_lvlG_CE) (2:=h_gt_lvl0) (3:=h_CEcut_CE_lvl);!intro.
    specialize CompilEnv.cut_until_spec1 with (1:=h_CEcut_CE_lvl);!intro.
    specialize STACK.cut_until_spec1 with (1:=h_stkcut_s_lvl);!intro.
    subst.
    red in h_stk_mtch_lgth_s_CE.
    setoid_rewrite app_length in h_stk_mtch_lgth_s_CE.
    setoid_rewrite app_length in heq_length.
    setoid_rewrite app_length in heq_length0.
    omega.
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
  !intros.
  !!pose proof h_match_env.(me_stack_match_lgth).
  now red in h_stk_mtch_lgth_s_CE.
Qed.

(*
(* Yet another hypothesis deducibility *)
Lemma strong_match_repeat_loadv : forall st s CE sp locenv g  m,
    match_env st s CE sp locenv g m ->
    invariant_compile CE st ->
    forall CE' CE'' lvl,
      CompilEnv.cut_until CE lvl CE' CE'' -> 
      exists sp'',
        repeat_Mem_loadv AST.Mint32 m (Datatypes.length CE - lvl)%nat sp sp''.
Proof.
  !!intros until 1.
  !!induction h_strg_mtch_s_CE_m;!intros;up_type.
  - rename v into sp.
    cbn.
    exists sp.
    constructor.
  - !assert (invariant_compile CE st).
    { eapply invariant_compile_subcons;eauto. }
    assert (lvl=Datatypes.length CE).
    { !!pose proof (ci_exact_lvls _ _ h_inv_comp_st).
      !inversion h_exct_lvlG.
      reflexivity. }

    rename v' into sp.
    rename v into sp'.
    specialize (IHh_strg_mtch_s_CE_m h_inv_comp_CE_st).
    !inversion h_CEcut;up_type. (* cut reached or not *)
    * (* Reached *)
      cbn in *.
      destruct lvl0;try (exfalso;omega).
      subst.
      !!assert (Datatypes.length CE - lvl0 = 0)%nat by omega.
      rewrite heq_sub.
      exists sp.
      constructor 1;auto.
    * (* not reached *)
      rename s' into CE'.
      specialize IHh_strg_mtch_s_CE_m with (1:=h_CEcut_CE_lvl0).      
      !!destruct IHh_strg_mtch_s_CE_m as [sp'' ?].
      exists sp''.
      cbn in *|-.
      cbn [Datatypes.length].
      !!assert ((S (Datatypes.length CE) - lvl0 = S (Datatypes.length CE - lvl0))%nat) by omega.
      rewrite heq_sub.
      econstructor;eauto.
Qed.

Lemma strong_match_env_match_env_sublist : forall st s CE sp locenv g  m,
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
  !intros.
  !assert ((Datatypes.length CE= Datatypes.length s)).
  { eapply match_env_length_CE_s;eauto. }
  !assert (exists s' s'', STACK.cut_until s lvl s' s'').
  { eapply strong_match_env_cut_CE_cut_s;eauto. }
  !assert(exists sp'',repeat_Mem_loadv AST.Mint32 m (Datatypes.length CE - lvl)%nat sp sp'').
  { eapply strong_match_repeat_loadv;eauto. }
  decomp h_ex.
  decomp h_ex0.
  exists s'.
  exists s''.
  exists sp''.
  repeat (split;[now auto|]).
  !destruct (dec_lt lvl (Datatypes.length CE)).
  - eapply strong_match_env_match_env_sublist_aux1;eauto.
  - !assert (CE' = [] ∧ CE''=CE ∧ s' = [] ∧ s''=s).
    { !inversion h_CEcut_CE_lvl.
      - repeat (split;[now auto|]).
        + cbn in *. symmetry in heq_length.
          apply length_zero_iff_nil in heq_length.
          subst.
          !inversion h_stkcut_s_lvl;auto.
      - rename s0 into CE''.
        repeat (split;[now auto|]).
        !inversion h_strg_mtch_s_CE_m.
        !inversion h_stkcut_s_lvl;auto.
        cbn -[minus] in *.
        !!pose proof (ci_exact_lvls _ _ h_inv_comp_CE_st).
        !inversion h_exct_lvlG.
        exfalso;omega.
      - !!pose proof (ci_exact_lvls _ _ h_inv_comp_CE_st).
        !inversion h_exct_lvlG.
        cbn in *.
        exfalso;omega. }
    decomp h_and.
    subst.
    subst.
    !!assert ((Datatypes.length CE) - lvl = 0)%nat by omega.
    rewrite heq_sub in h_repeat_loadv.
    !inversion h_repeat_loadv.
    intro.
    apply strong_match_env_match_env.
    eapply strong_match_env_inv_locenv.
    eassumption.
Qed.
*)

(* Yet another hypothesis deducibility *)
(*Lemma strong_match_env_match_env_sublist: 
  forall (st : symboltable.symboltable) (s : STACK.state) (CE : compilenv)
         (sp : Values.val) (locenv : env) (g : genv) (m : mem),
    strong_match_env st s CE sp locenv g m
    → invariant_compile CE st
    → ∀ (CE' CE'' : CompilEnv.stack) (lvl : CompilEnv.scope_level),
        CompilEnv.cut_until CE lvl CE' CE''
        → exists δ sp'' s' s'',
          ((∃ toplvl : CompilEnv.scope_level, CompilEnv.level_of_top CE = Some toplvl ∧ δ = (toplvl + 1 - lvl)%nat)
           ∨ CE = [ ] ∧ δ = 0%nat)
          ∧ repeat_Mem_loadv AST.Mint32 m δ sp sp''
          ∧ STACK.cut_until s lvl s' s'' 
          ∧ ∀ locenv0 : env, match_env st s'' CE'' sp'' locenv0 g m.
Proof.
  !intros.
  !assert (exists δ ,
          ((∃ toplvl : CompilEnv.scope_level, CompilEnv.level_of_top CE = Some toplvl ∧ δ = (toplvl + 1 - lvl)%nat)
           ∨ CE = [ ] ∧ δ = 0%nat)).
  { destruct (CompilEnv.level_of_top CE) eqn:heq_lvl.
    - exists (s0 + 1 - lvl)%nat.
      left.
      exists s0;eauto.
    - exists 0%nat;right;split;eauto.
      apply exact_lvlG_lgth_none in heq_lvl;auto.
      + apply length_invnil;auto.
      + apply h_inv_comp_CE_st. }
  !!destruct h_ex as [δ ?].
  exists δ.
  !!pose proof strong_match_env_match_env_sublist_aux3 _ _ _ _ _ _ _ h_strg_mtch_s_CE_m h_inv_comp_CE_st _ _ _ h_CEcut_CE_lvl δ h_or.
  destruct h_ex;eauto.
  exists x.
  !!edestruct strong_match_env_match_env_sublist_aux2;eauto.
  destruct h_ex.
  exists x0 x1;eauto.
Qed.
*)
(* Is this true? *)


(** Property of the translation: Since chain variables have always zero
   offset, the offset of a variable in CE is the same as its offset in
   CMinor memory. *)
Lemma eval_build_loads_offset: forall lvl g stkptr locenv m δ_lvl δ_id b ofs,
    stack_localstack_aligned lvl locenv g m stkptr ->
    (δ_lvl <= lvl)%nat
    -> Cminor.eval_expr g stkptr locenv m (build_loads δ_lvl δ_id) (Values.Vptr b ofs) ->
    ofs = Int.repr δ_id.
Proof.
  !intros.
  unfold build_loads in *.
  !inversion h_CM_eval_expr.
  !inversion h_CM_eval_expr_v2.
  simpl in *.
  red in h_aligned_g_m.
  specialize h_aligned_g_m with (1:=h_le_δ_lvl_lvl).
  !!edestruct h_aligned_g_m;eauto.
  assert (v1 = Values.Vptr x Int.zero).
  { eapply det_eval_expr;eauto. }
  subst.
  cbn  in *.
  destruct v2;cbn in *;try discriminate.
  inversion h_eval_binop_Oadd_v1_v2.
  inversion h_eval_constant.
  apply Int.add_zero_l.
Qed.


(** Property of the translation: Since chain variables have always
    zero offset, the offset of a variable in CE must be more than 3. *)
Lemma eval_build_loads_offset_non_null_var:
  forall stbl CE g stkptr locenv m nme a bld_lds b ofs,
    CompilEnv.exact_levelG CE ->
    stack_no_null_offset stbl CE ->
    stack_localstack_aligned (Datatypes.length CE) locenv g m stkptr ->
    transl_variable stbl CE a nme = Errors.OK bld_lds ->
    Cminor.eval_expr g stkptr locenv m bld_lds (Values.Vptr b ofs) ->
    4 <= Int.unsigned ofs.
Proof.
  !intros.
  functional inversion heq_transl_variable;subst.
  assert (ofs=(Int.repr n)). {
    eapply (eval_build_loads_offset (Datatypes.length CE) g stkptr locenv m (m' - m0) _ b ofs h_aligned_g_m);auto with arith.
    - erewrite exact_lvlG_lgth with (lvl:=m').
      + omega.
      + assumption.
      + assumption. }
  subst.
  eapply h_nonul_ofs;eauto.
Qed.

Lemma transl_expr_ok : forall stbl CE e e',
    transl_expr stbl CE e = Errors.OK e' ->
    forall locenv g m (s:STACK.state)  (v:value) stkptr,
      evalExp stbl s e (OK v) ->
      match_env stbl s CE stkptr locenv g m ->
      exists v_t,
        (transl_value v v_t /\ Cminor.eval_expr g stkptr locenv m e' v_t).
Proof.
  intros until e.
  !functional induction (transl_expr stbl CE e) ;try discriminate;simpl; !intros;
  !invclear h_eval_expr_v;eq_same_clear.
  - inversion h_eval_literal;subst.
    + !destruct v0.
      * eexists;split;!intros; econstructor;eauto.
      * eexists;split;!intros;econstructor;eauto.
    + eexists;split;!intros.
      * eapply (transl_literal_ok g _ _ h_eval_literal stkptr).
        econstructor.
      * constructor.
        reflexivity.
  - unfold value_at_addr in heq_value_at_addr.
    destruct (transl_type stbl astnum_type) eqn:heq_transl_type;simpl in *.
    + !destruct h_match_env.
      edestruct h_safe_cm_CE_m.(me_stack_match_addresses) with (nme:=Identifier astnum id);eauto. 
      eapply h_stk_mtch_s_m;eauto.
      * simpl.
        assumption.
      * simpl.
        rewrite heq_fetch_exp_type.
        reflexivity.
    + discriminate.
  - decomp (IHr _ heq_tr_expr_e _ _ _ _ _ _ h_eval_expr_e_e_v h_match_env).
    decomp (IHr0 _ heq_tr_expr_e0 _ _ _ _ _ _ h_eval_expr_e0_e0_v h_match_env).
    assert (hex:or (exists b, v = Bool b) (exists n, v = Int n)). {
      apply do_run_time_check_on_binop_ok in h_do_rtc_binop.
      rewrite binopexp_ok in h_do_rtc_binop.
      !functional inversion h_do_rtc_binop;subst;eq_same_clear
       ;try contradiction;eauto.
      unfold Math.mod' in  heq_mod'.
      destruct e_v;try discriminate.
      destruct e0_v;try discriminate.
      inversion heq_mod'.
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
    simpl in heq_transl_unop.
    eq_same_clear.
    specialize IHr with (1:=heq_tr_expr_e) (2:=h_eval_expr_e_e_v) (3:=h_match_env).
    decomp IHr.
    !invclear h_do_rtc_unop;eq_same_clear.
    !invclear h_overf_check.
    eexists.
    split.
    * econstructor.
    * assert (h:=unaryneg_ok _ _ _ heq_transl_value_e_v_e_t_v heq_unary_minus).
      econstructor;eauto.
      simpl.
      inversion h.
      reflexivity.
  (* Not *)
  - !invclear h_do_rtc_unop;simpl in *;try eq_same_clear.
    specialize IHr with (1:=heq_tr_expr_e) (2:=h_eval_expr_e_e_v) (3:=h_match_env).
    decomp IHr.
    generalize (not_ok _ _ _ heq_transl_value_e_v_e_t_v heq_unary_operation).
    !intro.
    exists (Values.Val.notbool e_t_v).
    split;auto.
    econstructor;simpl in *;eauto.
    + econstructor;eauto.
      reflexivity.
    + destruct e_t_v;simpl in *; try (inversion heq_transl_value_e_v_e_t_v;fail).
      unfold  Values.Val.cmp.
      simpl.
      unfold Values.Val.of_bool.
      reflexivity.
Qed.


Scheme Equality for binary_operator.
Scheme Equality for unary_operator.
Scheme Equality for literal.

Ltac finish_eqdec := try subst;try (left;reflexivity);(try now right;intro abs;inversion abs;contradiction).

Lemma expression_dec: forall e1 e2:exp, ({e1=e2} + {e1<>e2})
with name_dec: forall n1 n2:name, ({n1=n2} + {n1<>n2}).
Proof.
  { intros e1 e2.
    case e1;case e2;intros;try now((left+right)).
    - destruct (Nat.eq_dec a0 a);finish_eqdec.
      destruct (literal_eq_dec l0 l);finish_eqdec.
    - destruct (Nat.eq_dec a0 a);finish_eqdec.
      destruct (name_dec n0 n);finish_eqdec.
    - destruct (Nat.eq_dec a0 a);finish_eqdec.
      destruct (binary_operator_eq_dec b0 b);finish_eqdec.
      destruct (expression_dec e3 e);finish_eqdec.
      destruct (expression_dec e4 e0);finish_eqdec.
    - destruct (Nat.eq_dec a0 a);finish_eqdec.
      destruct (unary_operator_eq_dec u0 u);finish_eqdec.
      destruct (expression_dec e0 e);finish_eqdec. }
  { !intros.
    case n1;case n2;intros;finish_eqdec.
    - destruct (Nat.eq_dec a0 a);finish_eqdec.
      destruct (Nat.eq_dec i0 i);finish_eqdec.
    - destruct (Nat.eq_dec a0 a);finish_eqdec.
      destruct (name_dec n0 n);finish_eqdec.
      destruct (expression_dec e0 e);finish_eqdec.
    - destruct (Nat.eq_dec a0 a);finish_eqdec.
      destruct (name_dec n0 n);finish_eqdec.
      destruct (Nat.eq_dec i0 i);finish_eqdec. }
Defined.


Import STACK.


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
  - rewrite <- beq_nat_refl in heq_Some.
    inversion heq_Some.
    left.
    reflexivity.
  - right.
    rewrite <- beq_nat_false_iff in hneq.
    rewrite hneq in heq_Some.
    eapply IHa;eauto.
Qed.


Lemma fetches_none_notin: ∀ (a : localframe) (id : idnum) (st : CompilEnv.V), CompilEnv.fetches id a = None → ~List.In (id, st) a.
Proof.
  !intros.
  !!(functional induction (CompilEnv.fetches id a);intros; try discriminate).
  - specialize (IHo heq_CEfetches_id_a).
    intro abs.
    simpl in *.
    !destruct abs.
    + inversion heq_pair;subst.
      rewrite <- beq_nat_refl in hbeqnat_false.
      discriminate.
    + contradiction.
  - apply in_nil.
Qed.

Arguments fst _ _ !p.

Lemma fetches_none_notinA: ∀ (a : localframe) (id : idnum) (st : CompilEnv.V),
    CompilEnv.fetches id a = None →
    ~InA eq_fst_idnum (id, st) a.
Proof.
  !!intros until 0.
  !!(functional induction (CompilEnv.fetches id a);intros; try discriminate).
  - specialize (IHo heq_CEfetches_id_s').
    intro abs.
    !inversion abs.
    + red in H0;simpl in H0.
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
  !induction l;simpl;!intros;try contradiction.
  !destruct h_or;subst.
  - rewrite <- beq_nat_refl.
    reflexivity.
  - destruct a.
    assert (hneq:i<>id).
    { intro abs.
      subst.
      inversion h_NoDupA;subst.
      absurd (InA eq_fst_idnum (id, t) l);auto.
      apply InA_alt.
      exists (id, st).
      split;auto. }
    apply not_eq_sym in hneq.
    rewrite <- beq_nat_false_iff in hneq.
    rewrite hneq.
    apply IHl;auto.
    inversion h_NoDupA;auto.
Qed.

Lemma add_to_frame_nodup: forall stbl subtyp_mrk new_sz nme fram_sz new_fram,
    CompilEnv.fetches nme (fst fram_sz) = None
    -> add_to_frame stbl fram_sz nme subtyp_mrk = Errors.OK (new_fram, new_sz)
    -> NoDupA eq_fst_idnum (fst fram_sz)
    -> NoDupA eq_fst_idnum new_fram.
Proof.
  !!intros until 0.
  rewrite add_to_frame_ok.
  !!functional induction (function_utils.add_to_frame stbl fram_sz nme subtyp_mrk);simpl;!intros;
    try discriminate.
  !invclear heq_OK.
  constructor 2.
  - eapply fetches_none_notinA with (st:=sz) in heq_CEfetches_nme_cenv .
    assumption.
  - assumption.
Qed.



Ltac rename_hyp_incro h th :=
  match th with
  | increasing_order_fr ?x => fresh "h_incr_order_fr_" x
  | increasing_order_fr _ => fresh "h_incr_order_fr"
  | increasing_order ?x => fresh "h_incr_order_" x
  | increasing_order _ => fresh "h_incr_order"
  | exact_levelG ?x => fresh "h_exact_lvlG_" x
  | exact_levelG _ => fresh "h_exact_lvlG"
  | all_frm_increasing ?x => fresh "h_allincr_" x
  | all_frm_increasing _ => fresh "h_allincr"
  | all_addr_no_overflow ?x => fresh "h_bound_addr_" x
  | all_addr_no_overflow _ => fresh "h_bound_addr"
  | _ => rename_hyp_strong h th
  end.
Ltac rename_sparkprf ::= rename_hyp_incro.

Lemma storev_inv : forall nme_chk m nme_t_addr e_t_v m',
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m'
    -> exists b ofs, nme_t_addr = Values.Vptr b ofs.
Proof.
  !intros.
  destruct nme_t_addr; try discriminate.
  eauto.
Qed.

Lemma transl_name_OK_inv : forall stbl CE nme nme_t,
    transl_name stbl CE nme = Errors.OK nme_t
    -> exists astnum id, (transl_variable stbl CE astnum id =  Errors.OK nme_t
                          /\ nme = Identifier astnum id).
Proof.
  !intros stbl CE nme nme_t H.
  functional inversion H.
  eauto.
Qed.

Lemma exact_level_top_lvl: forall CE s3,
    CompilEnv.exact_levelG CE ->
    CompilEnv.level_of_top CE = Some s3 ->
    List.length CE = S s3.
Proof.
  !intros.
  inversion h_exct_lvlG_CE;subst;cbn in *;try discriminate.
  inversion heq_lvloftop_CE_s3.
  reflexivity.
Qed.


Lemma increase_order_level_of_top_ge: forall CE id s s0 s3,
    CompilEnv.exact_levelG CE ->
    CompilEnv.frameG id CE = Some (s, s0) ->
    CompilEnv.level_of_top CE = Some s3 ->
    (s3 >= s)%nat.
Proof.
  !!intros until 1.
  revert id s s0 s3.
  !induction h_exct_lvlG_CE;cbn.
  - discriminate.
  - !intros.
    destruct (CompilEnv.resides id fr) eqn:heq_resides.
    + !invclear heq_Some.
      !invclear heq_Some0.
      auto.
    + !invclear heq_Some0.
      destruct (CompilEnv.level_of_top stk) eqn:heq_lvltop.
      * specialize(IHh_exct_lvlG_CE id s s0 s1).
        specialize (exact_level_top_lvl _ _ h_exct_lvlG_CE heq_lvltop).
        !intro.
        red.
        apply Nat.le_trans with s1.
        -- apply IHh_exct_lvlG_CE;auto.
        -- omega.
      * destruct stk.
        -- cbn in heq_Some.
           discriminate.
        -- cbn in heq_lvltop.
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
  !induction lf;simpl in *;!intros.
  - discriminate.
  - destruct a.
    destruct (Nat.eq_dec id₁ i);subst.
    + rewrite Nat.eqb_refl in heq_Some.
      !invclear heq_Some.
      assert (h:id₂ ≠ i) by auto.
      rewrite <- (Nat.eqb_neq id₂ i) in h.
      rewrite h in heq_Some0.
      inversion h_incr_order;subst;simpl in *.
      assert (δ₂ < δ₁). {
        rewrite Forall_forall in H2.
        eapply (H2 (id₂,δ₂));eauto.
        apply fetches_In.
        assumption. }
      symmetry.
      apply Z.lt_neq.
      assumption.
    + destruct (Nat.eq_dec id₂ i).
      * subst.
        rewrite Nat.eqb_refl in heq_Some0.
        !invclear heq_Some0.
        assert (h:id₁ ≠ i) by auto.
        rewrite <- (Nat.eqb_neq id₁ i) in h.
        rewrite h in heq_Some.
        inversion h_incr_order;subst;simpl in *.
        assert (δ₁ < δ₂). {
          rewrite Forall_forall in H2.
          eapply (H2 (id₁,δ₁));eauto.
          apply fetches_In.
          assumption. }
        apply Z.lt_neq.
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

Lemma increasing_order_frameG: forall lvla lvlb fra l id ,
    Forall (gt_x_fst_y lvlb) l ->
    CompilEnv.frameG id l = Some (lvla,fra) ->
    (lvla < lvlb)%nat.
Proof.
  !intros.
  apply frameG_In in heq_CEframeG_id_l.
  rewrite Forall_forall in h_forall_l.
  apply (h_forall_l (lvl_id, fr_id)).
  assumption.
Qed.


Lemma exact_levelG_lgth: forall stk id lvl_id fr_id,
    CompilEnv.exact_levelG stk
    -> CompilEnv.frameG id stk = Some (lvl_id, fr_id)
    -> (lvl_id < Datatypes.length stk)%nat.
Proof.
  red.
  induction 1.
  - cbn. intro abs;discriminate.
  - cbn. intro.
    !destruct (CompilEnv.resides id fr).
    + !invclear H0.
      auto.
    + specialize (IHexact_levelG H0).
      omega.
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
  intros until 0.
  !intro.

  !induction h_exct_lvlG_CE;!intros;simpl in *;try discriminate.
  unfold CompilEnv.level_of in *.
  destruct (CompilEnv.fetch id₁ (Datatypes.length stk, fr)) eqn:heq_fetch_id₁;
    destruct (CompilEnv.fetch id₂ (Datatypes.length stk, fr)) eqn:heq_fetch_id₂;
    eq_same_clear;subst;simpl in *;try discriminate.
  - right.
    eapply CEfetch_inj;eauto.
    red in h_allincr; simpl in h_allincr.
    inversion h_allincr.
    assumption.
  - left.
    symmetry.
    apply Nat.lt_neq.
    apply CEfetch_reside_false in heq_fetch_id₂.
    apply CEfetch_reside_true in heq_fetch_id₁.
    rewrite heq_fetch_id₂,heq_fetch_id₁ in *;simpl in *.
    !invclear heq_CEframeG_id₁;simpl in *.
    eapply exact_levelG_lgth;eauto.
  - left.
    apply Nat.lt_neq.
    apply CEfetch_reside_true in heq_fetch_id₂.
    apply CEfetch_reside_false in heq_fetch_id₁.
    rewrite heq_fetch_id₂,heq_fetch_id₁ in *;simpl in *.
    !invclear heq_CEframeG_id₂;simpl in *.
    eapply exact_levelG_lgth;eauto.
  - apply CEfetch_reside_false in heq_fetch_id₁.
    apply CEfetch_reside_false in heq_fetch_id₂.
    rewrite heq_fetch_id₁,heq_fetch_id₂ in *.
    eapply IHh_exct_lvlG_CE ;eauto.
    inversion h_allincr.
    assumption.
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
  !intros.
  unfold transl_variable in *.
  destruct (CompilEnv.fetchG id₁ CE) eqn:h₁;simpl in *;try discriminate.
  destruct (CompilEnv.fetchG id₂ CE) eqn:h₂;simpl in *;try discriminate.
  destruct (CompilEnv.frameG id₁ CE) eqn:h₁';simpl in *;try discriminate.
  destruct (CompilEnv.frameG id₂ CE) eqn:h₂';simpl in *;try discriminate.
  destruct f.
  destruct f0.
  assert (hh:=CEfetchG_inj _ _ _ h_exct_lvlG_CE h_allincr_CE _ _ _ _ _ _  h₁ h₂ h₁' h₂' hneq).
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

Lemma transl_variable_astnum: forall stbl CE astnum id' addrof_nme,
    transl_variable stbl CE astnum id' = Errors.OK addrof_nme
    -> forall a,transl_variable stbl CE a id' = transl_variable stbl CE astnum id'.
Proof.
  !intros.
  unfold transl_variable.
  !functional inversion heq_transl_variable.
  rewrite  heq_CEfetchG_id'_CE, heq_CEframeG_id'_CE, heq_lvloftop_CE_m'.
  reflexivity.
Qed.



Lemma compute_chk_32 : forall stbl t,
    compute_chnk_of_type stbl t = Errors.OK AST.Mint32
    -> transl_type stbl t = Errors.OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr).
Proof.
  !intros.
  functional inversion heq_compute_chnk_of_type;subst;simpl.
  - functional inversion H;simpl.
    reflexivity.
  - functional inversion H;simpl.
    reflexivity.
Qed.


Notation " x =: y" := (x = Errors.OK y) (at level 90).
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
Lemma wf_chain_load'2:forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> stack_localstack_aligned lvl locenv g m stkptr
    -> 4 <= Int.unsigned ofs (*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl',
        (lvl' <= lvl)%nat ->
        let load_id := build_loads_ (Econst (Oaddrstack Int.zero)) lvl' in
        Cminor.eval_expr g stkptr locenv m' load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
Proof.
  !intros.
  rename h_le into h_ofs_non_zero.
  simpl in *.
  subst load_id.
  generalize dependent load_id_v.
  induction lvl';!intros;simpl in *.
  - !inversion h_CM_eval_expr_load_id_v;econstructor;eauto.
  - !invclear h_CM_eval_expr_load_id_v.
    assert (h_CM_eval_expr_on_m:
              Cminor.eval_expr g stkptr locenv m (build_loads_ (Econst (Oaddrstack Int.zero)) lvl') vaddr).
    { eapply IHlvl'; eauto.
      omega. }
    econstructor.
    + eassumption.
    + destruct vaddr;simpl in *;try discriminate.
      rewrite <- h_loadv_vaddr_load_id_v.
      symmetry.
      eapply Mem.load_store_other;eauto.
      right.
      left.
      simpl.
      transitivity 4.
      * !assert (lvl' <= lvl)%nat.
        { omega. }
        specialize (h_aligned_g_m _ h_le_lvl'_lvl0).
        !destruct h_aligned_g_m.
        !assert ((Values.Vptr b0 i) = (Values.Vptr x Int.zero)).
        { eapply det_eval_expr;eauto. }
        !invclear heq_vptr_b0_i.
        discriminate.
      * apply h_ofs_non_zero.
Qed.

(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load'3:forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> stack_localstack_aligned lvl locenv g m' stkptr
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl',
        (lvl' <= lvl)%nat ->
        let load_id := build_loads_ (Econst (Oaddrstack Int.zero)) lvl' in
        Cminor.eval_expr g stkptr locenv m load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
Proof.
  !intros.
  rename h_le into h_ofs_non_zero.
  simpl in *.
  subst load_id.
  generalize dependent load_id_v.
  induction lvl';!intros;simpl in *.
  - !inversion h_CM_eval_expr_load_id_v;econstructor;eauto.
  - !invclear h_CM_eval_expr_load_id_v.
    assert (h_CM_eval_expr_on_m':
              Cminor.eval_expr g stkptr locenv m' (build_loads_ (Econst (Oaddrstack Int.zero)) lvl') vaddr).
    { eapply IHlvl'; eauto. omega. }
    econstructor.
    + eassumption.
    + destruct vaddr;simpl in *;try discriminate.
      rewrite <- h_loadv_vaddr_load_id_v.
      eapply Mem.load_store_other;eauto.
      simpl.
      right. left.
      transitivity 4.
      * !assert (lvl' <= lvl)%nat.
        { omega. }
        !destruct (h_aligned_g_m' _ h_le_lvl'_lvl0).
        !assert ((Values.Vptr b0 i) = (Values.Vptr x Int.zero)).
        { eapply det_eval_expr;eauto. }
        !invclear heq_vptr_b0_i.
        vm_compute.
        intro abs;discriminate.
      * apply h_ofs_non_zero.
Qed.

(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load'4:forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> stack_localstack_aligned lvl locenv g m stkptr
    -> 4 <= Int.unsigned ofs (*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl',
        (lvl' <= lvl)%nat ->
        let load_id := build_loads_ (Econst (Oaddrstack Int.zero)) lvl' in
        Cminor.eval_expr g stkptr locenv m load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
Proof.
  !intros.
  rename h_le into h_ofs_non_zero.
  simpl in *.
  subst load_id.
  generalize dependent load_id_v.
  induction lvl';!intros;simpl in *.
  - !inversion h_CM_eval_expr_load_id_v;econstructor;eauto.
  - !invclear h_CM_eval_expr_load_id_v.
    assert (h_CM_eval_expr_on_m:
              Cminor.eval_expr g stkptr locenv m' (build_loads_ (Econst (Oaddrstack Int.zero)) lvl') vaddr).
    { eapply IHlvl'; eauto.
      omega. }
    econstructor.
    + eassumption.
    + destruct vaddr;simpl in *;try discriminate.
      rewrite <- h_loadv_vaddr_load_id_v.
      eapply Mem.load_store_other;eauto.
      !!assert ((lvl' <= lvl)%nat) by omega.
      !!pose proof h_aligned_g_m lvl' h_le_lvl'_lvl0.
      decomp h_ex.
      !assert ((Values.Vptr b0 i) = (Values.Vptr b_δ Int.zero)).
      { eapply det_eval_expr;eauto. }
      !invclear heq_vptr_b0_i.
      right.
      left.
      rewrite Int.unsigned_zero.
      cbn.
      omega.
Qed.

Lemma wf_chain_load'':forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned lvl locenv g m stkptr)
    -> (stack_localstack_aligned lvl locenv g m' stkptr)
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl',
        (lvl' <= lvl)%nat ->
        let load_id := build_loads_ (Econst (Oaddrstack Int.zero)) lvl' in
        Cminor.eval_expr g stkptr locenv m' load_id vaddr
        <-> Cminor.eval_expr g stkptr locenv m load_id vaddr.
Proof.
  !intros.
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
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl' δ_lvl,
        (lvl' <= lvl)%nat ->
        let load_id := build_loads lvl' δ_lvl in
        Cminor.eval_expr g stkptr locenv m load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
Proof.
  !intros.
  rename h_le into h_ofs_non_zero.
  simpl in *.
  unfold build_loads in *.
  !invclear h_CM_eval_expr_load_id_load_id_v.
  econstructor;eauto.
  Focus 2.
  { inversion h_CM_eval_expr_v2;econstructor;eauto. }
  Unfocus.
  eapply wf_chain_load'3;eauto.
Qed.


(* Well-formedness of the chained stack: store never modify the
     address of a variable. Reason: since variable addresses are
     expressions of the form ((Load(Load(...(Load 0))))+δ) with δ >= 4
     and that stores never touch the addresses 0, variables addresses
     never change. *)
Lemma wf_chain_load'_2:forall lvl g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned lvl locenv g m stkptr)
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl' δ_lvl,
        (lvl' <= lvl)%nat ->
        let load_id := build_loads lvl' δ_lvl in
        Cminor.eval_expr g stkptr locenv m' load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
Proof.
  !intros.
  rename h_le into h_ofs_non_zero.
  simpl in *.
  unfold build_loads in *.
  !invclear h_CM_eval_expr_load_id_load_id_v.
  econstructor;eauto.
  Focus 2.
  { inversion h_CM_eval_expr_v2;econstructor;eauto. }
  Unfocus.
  eapply wf_chain_load'2;eauto.
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
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> transl_variable stbl CE astnum id =: load_id
    -> Cminor.eval_expr g stkptr locenv m load_id vaddr
    -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
Proof.
  !intros.
  rename h_le into h_ofs_non_zero.
  simpl in *.
  !functional inversion heq_transl_variable;subst;clear heq_transl_variable.
  rename m'0 into max_lvl.
  set (δ_lvl:=(max_lvl - lvl_id)%nat) in *.
  eapply wf_chain_load';eauto.
  pose proof exact_lvlG_lgth _ _ h_exct_lvlG_CE heq_lvloftop_CE_m'0.
  rewrite H in *.
  subst δ_lvl.
  omega.
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
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> transl_variable stbl CE astnum id =: load_id
    -> Cminor.eval_expr g stkptr locenv m' load_id vaddr
    -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
Proof.
  !intros.
  rename h_le into h_ofs_non_zero.
  simpl in *.
  !functional inversion heq_transl_variable;subst;clear heq_transl_variable.
  rename m'0 into max_lvl.
  set (δ_lvl:=(max_lvl - lvl_id)%nat) in *.
  eapply wf_chain_load'_2;eauto.
  pose proof exact_lvlG_lgth _ _ h_exct_lvlG_CE heq_lvloftop_CE_m'0.
  rewrite H in *.
  subst δ_lvl.
  omega.
Qed.


(* INVARIANT OF STORE/STOREV: if we do not touch on addresses zero
     of blocks, chaining variables all poitn to zero ofsets. *)
Lemma wf_chain_load_aligned: forall lvl g locenv chk m m' b ofs e_t_v stkptr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (4 <= (Int.unsigned ofs))
    -> stack_localstack_aligned lvl locenv g m stkptr
    -> stack_localstack_aligned lvl locenv g m' stkptr.
Proof.
  unfold stack_localstack_aligned at 2.
  !intros.
  generalize h_aligned_g_m.
  !intros.
  specialize (h_aligned_g_m (δ_lvl) h_le_δ_lvl_lvl).
  decomp h_aligned_g_m.
  exists b_δ.
  !destruct δ_lvl.
  - simpl.
    !inversion h_CM_eval_expr.
    econstructor;eauto.
  - cbn.
    !inversion h_CM_eval_expr.
    eapply eval_Eload with (vaddr:=vaddr).
    eapply wf_chain_load'4 with (lvl:=lvl);eauto; try omega.
    rewrite <- h_loadv.
    destruct vaddr;cbn;try discriminate.
    eapply Mem.load_store_other;eauto.
    cbn.
    red in h_aligned_g_m0.
    !!assert ((δ_lvl <= lvl)%nat) by omega.
    specialize (h_aligned_g_m0 δ_lvl h_le_δ_lvl_lvl0).
    decomp h_aligned_g_m0.
    !assert ((Values.Vptr b0 i) = (Values.Vptr b_δ0 Int.zero)).
    { eapply det_eval_expr;eauto. }
    !invclear heq_vptr_b0_i.
    right.
    left.
    rewrite Int.unsigned_zero.
    cbn.
    omega.
Qed.

Lemma wf_chain_load_aligned':forall sp lvl g locenv m,
    stack_localstack_aligned lvl locenv g m sp ->
    lvl = 0%nat ∨ exists b, sp = (Values.Vptr b Int.zero).
Proof.
  intros sp CE g locenv m h_aligned_g_m.
  red in h_aligned_g_m.
  !destruct CE.
  - left;reflexivity.
  - right.
    !!edestruct h_aligned_g_m with (δ_lvl:=0%nat);cbn;try omega.
    cbn in *.
    !inversion h_CM_eval_expr;subst.
    cbn in *.
    !invclear h_eval_constant.
    !destruct sp; cbn in *; try discriminate.
    rewrite Int.add_zero in h_val_add_sp.
    !inversion h_val_add_sp.
    eauto.
Qed.


Lemma assignment_preserve_loads_offset_non_null:
  forall stbl s CE spb ofs locenv' g m x x0 nme_t nme_chk nme_t_addr e_t_v m',
    invariant_compile CE stbl ->
    match_env stbl s CE (Values.Vptr spb ofs) locenv' g m ->
    transl_name stbl CE (Identifier x x0) =: nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv' m nme_t nme_t_addr ->
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
    stack_localstack_aligned (Datatypes.length CE) locenv' g m' (Values.Vptr spb ofs).
Proof.
  !intros.
  decomp (storev_inv _ _ _ _ _ heq_storev_e_t_v_m') ;subst.
  functional inversion heq_transl_name.
  eapply wf_chain_load_aligned;eauto.
  eapply eval_build_loads_offset_non_null_var;eauto.
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
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    stack_match_addresses stbl CE stkptr locenv g m'.
Proof.
  !intros; red. !intros.
  !functional inversion heq_transl_name;subst.
  !functional inversion heq_transl_variable;subst.
  !assert (exists id_t_v_pt id_t_v_ofs, id_t_v = Values.Vptr id_t_v_pt id_t_v_ofs).
  { destruct id_t_v;try discriminate. eauto. }
  decomp h_ex; subst.
  destruct (Nat.eq_dec id id0).
  - subst.
    exists (Values.Vptr id_t_v_pt id_t_v_ofs).
    destruct (match_env_sp_zero _ _ _ _ _ _ _ h_match_env);subst.
    eapply wf_chain_load_var;eauto.
    + eapply assignment_preserve_loads_offset_non_null;eauto.
    + eapply eval_build_loads_offset_non_null_var;eauto.
    + destruct (transl_variable_astnum _ _ _ _ _ heq_transl_variable astnum).
      rewrite heq_transl_variable in heq_transl_variable0.
      inversion heq_transl_variable0;subst.
      assumption.
  - !assert (∃ addr : Values.val, Cminor.eval_expr g stkptr locenv m nme_t addr).
    { eapply h_match_env;eauto. }
    decomp h_ex.
    exists nme_t_v.
    destruct (match_env_sp_zero _ _ _ _ _ _ _ h_match_env);subst.
    eapply wf_chain_load_var;eauto.
    + eapply assignment_preserve_loads_offset_non_null;eauto.
    + eapply eval_build_loads_offset_non_null_var;eauto.
Qed.

Lemma assignment_preserve_stack_match :
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
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    stack_match stbl s' CE stkptr locenv g m'.
Proof.
  intros until m'.
  !intros.
  !destruct h_match_env.
  !destruct h_safe_cm_CE_m.
  (* Getting rid of erronous cases *)
  !functional inversion heq_transl_variable.
  rename m'0 into lvl_max.
  (* done *)
  (* getting rid of erroneous storev parameter *)
  rewrite <- cm_storev_ok in heq_storev_e_t_v_m'.
  !functional inversion heq_storev_e_t_v_m';subst.
  set (loads_id:=(build_loads (lvl_max - lvl_id) δ_id)) in *.
  rewrite cm_storev_ok in *.
  (* done *)
  assert (h_ofs_nonzero:4 <= Int.unsigned ofs). {
    eapply eval_build_loads_offset_non_null_var;eauto. }
  unfold stack_match.
  !intros other_nme other_v addr_other load_addr_other type_other cm_typ_other;up_type.
  (* id can already be evaluated in s *)
  (* NO MORE completestack destruct (h_stk_cmpl_s_CE _ _ _ heq_transl_variable) as [v_id_prev h_eval_name_id_val_prev]. *)
  set (nme:=(Identifier a id)) in *.
  (* Getting rid of erronous cases *)
  !functional inversion heq_transl_name.
  subst.
  (* done *)
  rename id0 into other_id.
  set (other_nme:=(Identifier astnum other_id)) in *.
  (* other_nme can already be evaluated in s *)
  assert (heq_ftch_astnum:symboltable.fetch_exp_type astnum stbl = Some cm_typ_other). {
    simpl in heq_type_of_name.
    destruct (symboltable.fetch_exp_type astnum stbl);try discriminate.
    !inversion heq_type_of_name.
    reflexivity. }
  assert (h_tr_exp_other:
            transl_expr stbl CE (Name 1%nat (Identifier astnum other_id))
                        =: load_addr_other). {
    simpl.
    simpl in heq_type_of_name.
    rewrite heq_ftch_astnum.
    rewrite heq_transl_variable0.
    !invclear heq_type_of_name.
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
    unfold compute_chnk_astnum in heq_compute_chnk.
(*     unfold compute_chnk_id in heq_compute_chnk. *)
    rewrite heq_ftch_astnum in heq_type_of_name.
(*     rewrite heq_type_of_name in heq_compute_chnk. *)
    lazy beta iota delta [bind] in heq_compute_chnk.
    rewrite (transl_variable_astnum _ _ _ _ _ heq_transl_variable0 a) in *.
    rewrite heq_transl_variable0 in heq_transl_variable.
    !invclear heq_transl_variable.
    !assert (e_v = other_v). { eapply storeUpdate_id_ok_same_eval_name ;eauto. }
                               subst other_v.
    exists e_t_v;split;auto.
    !functional inversion heq_make_load;subst.
    eapply eval_Eload with (Values.Vptr b ofs).
    * { eapply wf_chain_load_var with (2:= heq_storev_e_t_v_m');eauto.
        - eapply wf_chain_load_aligned;eauto. }
    * simpl.
      (* Should be ok by well typedness of the chained stack wrt
           stbl (see hyp on compute_chk). *)
      (* assert (chunk = AST.chunk_of_type t). {
           rewrite cmtype_chk with (1:=heq_transl_type) (2:=heq_opttype) (3:=heq0).
           reflexivity. } *)
      assert (chunk = AST.Mint32). {
        !functional inversion heq_transl_type;subst;simpl in h_access_mode_cm_typ_nme.
        - inversion h_access_mode_cm_typ_nme;auto.
        - inversion h_access_mode_cm_typ_nme;auto. }
      subst.
      specialize Mem.load_store_same with (1:=heq_store_e_t_v_m');intro h.
      erewrite h.
      destruct e_t_v;auto;destruct e_v;simpl in *;try discriminate;
        now inversion heq_transl_value_e_v_e_t_v.

  - (* loading a different variable id' than the one stored id.
         2 steps: first prove that the addresses of id' and id did
         not change (the translated expressions did not change + the
         chained stack did not change either), and thus remain
         different, then conclude that the value stored in id' did
         not change. *)
    !assert (chk = AST.Mint32). {
      rewrite function_utils.compute_chnk_ok in heq_compute_chnk.
      functional inversion heq_compute_chnk; reflexivity. }

    (*xxxx NO MORE destruct (h_stk_cmpl_s_CE _ _ _ heq_transl_variable0) as [v_other_id_prev h_eval_name_other_id_val_prev]. *)
    generalize h_stk_mtch_addr_stkptr_m;!intros.
    red in h_stk_mtch_addr_stkptr_m0.
    specialize h_stk_mtch_addr_stkptr_m0 with (1:=heq_transl_name).
    !destruct h_stk_mtch_addr_stkptr_m0.
    red in h_stk_mtch_s_m.
    specialize h_stk_mtch_s_m with (2:=h_CM_eval_expr_addr_other_addr_other_v) (1:=heq_transl_name)
                                   (5:=heq_type_of_name) (4:=heq_transl_type)(6:=heq_make_load) as h.
    
    !assert (evalName stbl s (Identifier astnum other_id) (OK other_v)).
    { constructor.
      erewrite storeUpdate_id_ok_others with (1:=h_storeUpd);auto.
      unfold other_nme in h_eval_name_other_nme_other_v.
      !inversion h_eval_name_other_nme_other_v.
      assumption. }
    subst.
    specialize h with (1:=h_eval_name_other_v).
    destruct h as [ cm_v [tr_val_v_other h_cm_eval_m_v_other]].
    exists cm_v.
    split;auto.
    assert (h_aligned_m' : stack_localstack_aligned (Datatypes.length CE) locenv g m' stkptr). {
      eapply wf_chain_load_aligned;eauto. }
    !functional inversion heq_make_load;subst.
     
    (* !inversion cm_eval_m_v_other. *)
    generalize (wf_chain_load_var _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                  h_exct_lvlG_CE
                                  heq_storev_e_t_v_m' h_aligned_m'
                                  h_ofs_nonzero heq_transl_variable0
                                  h_CM_eval_expr_addr_other_addr_other_v).
    !intro.
    econstructor.
    + eassumption.
    + !inversion h_cm_eval_m_v_other.
      assert (addr_other_v = addr_other_v0).
      { eapply det_eval_expr with (m:=m); eauto. }
      subst addr_other_v0.
      destruct addr_other_v; try discriminate;simpl in *.
      clear h_tr_exp_other.
      erewrite Mem.load_store_other;[now eassumption| now eassumption | ].
      subst nme other_nme.
      unfold compute_chnk_id in heq_compute_chnk.
      destruct (symboltable.fetch_exp_type astnum stbl) eqn:heq_fetchvartyp;try discriminate.
      !invclear heq_ftch_astnum.
      unfold stack_separate in h_separate_CE_m.


      eapply h_separate_CE_m with (nme:=(Identifier astnum id))
                                    (nme':=(Identifier astnum other_id))
                                    (k₂ := b0) (k₁:=b);
        clear h_separate_CE_m;simpl;try eassumption;auto.
        * rewrite heq_fetchvartyp.
          reflexivity.
        * rewrite heq_fetchvartyp.
          reflexivity.
        * erewrite transl_variable_astnum;eauto.
        * rewrite h_access_mode_cm_typ_nme.
          f_equal.
          eq_same_clear.
          clear heq_type_of_name.
          functional inversion heq_transl_type;subst;auto;cbn in *.
          -- inversion heq_make_load;reflexivity.
          -- inversion heq_make_load;reflexivity.
        * intro abs.
          inversion abs;subst;try discriminate.
          elim hneq;reflexivity.
Qed.


Lemma assignment_preserve_stack_match_function :
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
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    stack_match_functions stbl stkptr CE locenv g m'.
Proof.
  !intros.
  red.
  !intros.
  !destruct h_match_env.
  !destruct h_safe_cm_CE_m.
  up_type.
  red in h_stk_mtch_fun.
  specialize (h_stk_mtch_fun p pb_lvl pb h_fetch_proc_p).
  !! destruct h_stk_mtch_fun as [CE' [CE'' [paddr [pnum [fction [lglobdef [? [? [? ?]]]]]]]]].
  exists CE', CE'', paddr, pnum, fction, lglobdef.
  split;[|split;[|split]];subst;eauto.
  inversion h_CM_eval_expr_paddr.
  constructor.
  assumption.
Qed.


Lemma updateG_ok_others_frameG: forall stk id v stk',
      updateG stk id v = Some stk' ->
      forall id' lvl sto,
        id<>id' ->
        frameG id' stk = Some (lvl,sto) -> 
        exists sto', frameG id' stk' = Some (lvl,sto').
Proof.
  intros until v.
  !functional induction (updateG stk id v);simpl;!intros;try discriminate.
  - !invclear heq_Some;simpl.
    !!pose proof update_ok_others_reside _ _ _ _ heq_update_f_x _ hneq.
    rewrite <- heq_reside.
    !! (destruct (reside id' f) eqn:h).
    + !invclear heq_Some0.
      unfold update in heq_update_f_x.
      cbn in *.
      destruct (updates sto x v) eqn:heq.
      * !invclear heq_update_f_x.
        eauto.
      * discriminate.
    + rewrite heq_Some0.
      eauto.
  - !invclear heq_Some;simpl.
    !! (destruct (reside id' f) eqn:h).
    + !invclear heq_Some0.
      eauto.
    + eapply IHo;eauto.
Qed.

Lemma updateG_ok_frameG_others : forall stk id v stk' sto_id  lvl_id,
    updateG stk id v = Some stk' ->
    frameG id stk = Some (lvl_id,sto_id) ->
    forall id' lvl sto_id' sto'_id',
      frameG id' stk = Some (lvl,sto_id') -> 
      frameG id' stk' = Some (lvl,sto'_id') ->
      lvl <> lvl_id ->
      sto_id' = sto'_id'.
Proof.
  intros until v.
  !functional induction (updateG stk id v);simpl;!intros;try discriminate;rename x into id.
  - !invclear heq_Some;simpl.
    !assert (reside id f = true).
    { eapply update_ok_same_reside_orig; eauto. }
    rewrite heq_reside in heq_Some0.
    !invclear heq_Some0.
    !assert (reside id' (lvl_id, sto_id) = false).
    { cbn in *.
      destruct (resides id' sto_id);auto.
      exfalso.
      inversion heq_Some1.
      now apply hneq. }
    rewrite heq_reside0 in heq_Some1.
    unfold update in heq_update_f_x.
    cbn in heq_update_f_x.

    functional inversion heq_frameG;subst.
    + exfalso.
      apply hneq.
      destruct (updates sto_id id v);try discriminate.
      now inversion heq_update_f_x.
    + rewrite X in heq_Some1.
      now inversion heq_Some1.
  - up_type.
    !assert (reside id f = false).
    { apply reside_false_fetch_none.
      rewrite <- update_ok_none;eauto. }
    rewrite heq_reside in heq_Some0.
    !invclear heq_Some.
    destruct (reside id' f) eqn:heq.
    + !invclear heq_Some1.
      cbn in heq_frameG.
      cbn in heq.
      rewrite heq in heq_frameG.
      now inversion  heq_frameG.
    + eapply IHo ;eauto.
      cbn in heq_frameG.
      now rewrite heq in heq_frameG.
Qed.

Lemma exact_lvl_frameG_same_lvl : forall stk,
    STACK.exact_levelG stk ->
    forall id id' lvl sto_id sto_id',
      frameG id stk = Some (lvl,sto_id) ->
      frameG id' stk = Some (lvl,sto_id') ->
      sto_id = sto_id'.
Proof.
  !!intros until 1.
  induction h_exct_lvl_stk;!intros.
  - functional inversion heq_frameG.
  - functional inversion heq_frameG;functional inversion heq_frameG0;subst;auto.
    + exfalso.
      apply exact_levelG_frameG_lt_lgth in X.
      * omega.
      * assumption.
    + exfalso.
      apply  exact_levelG_frameG_lt_lgth in X.
      * omega.
      * assumption.
    + eapply IHh_exct_lvl_stk;eauto.
Qed.

Lemma updateG_spec_1 : forall stk id v stk',
    updateG stk id v = Some stk' ->
    exists stk1 sto sto' stk2 ,
      stk = stk1 ++ (sto::stk2)
      ∧ stk' = stk1 ++ (sto'::stk2)
      ∧ update sto id v = Some sto'
      ∧ (forall sto1, List.In sto1 stk1 -> reside id sto1 = false)
      ∧ frameG id stk = Some sto.
Proof.
  intros stk id v. 
  !functional induction (updateG stk id v);!intros.
  - !invclear heq_Some.
    exists [], f, f' , s';repeat split;auto.
    + intros sto1 hIn. 
      inversion hIn.
    + cbn.
      erewrite update_ok_same_reside_orig;eauto.
  - !invclear heq_Some.
    specialize IHo with (1:=heq_updateG_s'_x).
    decomp IHo;subst.
    rename H2 into hforall.
    !!exists (f::stk1), sto, sto', stk2;repeat split;auto.
    + intros sto1 hIn. 
      cbn in hIn.
      destruct hIn.
      * subst.
        apply update_ok_none in heq_update_f_x.
        now apply fetch_ok_none.
      * now apply hforall.
    + cbn.
      !assert (reside x f = false).
      { destruct (reside x f) eqn:heq;auto.
        apply fetch_ok_some in heq.
        decomp heq.
        rewrite update_ok_none in heq_update_f_x.
        rewrite heq_update_f_x in heq_fetch_x_f.
        discriminate. }
      now rewrite heq_reside.
  - discriminate.
  - discriminate.
Qed.


Lemma exact_levelG_sublist2:
  ∀ (CE1 CE2 : list frame), exact_levelG (CE1 ++ CE2) → exact_levelG CE2.
Proof.
  induction CE1.
  - now intro.
  - intros CE2 H.
    specialize exact_levelG_sublist with (1:=H).
    intro.
    apply IHCE1.
    assumption.
Qed.

Lemma exact_levelG_frameG_unique_lvl: forall stk1 stk2 lvl sto_id1 id sto_id2,
      exact_levelG (stk1 ++ (lvl, sto_id1) :: stk2) ->
      frameG id (stk1 ++ (lvl, sto_id1) :: stk2) = Some (lvl, sto_id2) ->
      sto_id1 = sto_id2.
Proof.
  induction stk1;!intros.
  - cbn in *.
    destruct (resides id sto_id1) eqn:heq.
    + now inversion heq_frameG.
    + exfalso.
      !assert (exact_levelG stk2).
      { now eapply exact_levelG_sublist;eauto. }
      specialize exact_lvl_level_of_top with (1:=h_exct_lvl_stk2)(2:=heq_frameG);!intro.
      decomp h_ex.
      specialize exact_lvl_lvl_of_top with (1:=h_exct_lvl_stk2)(2:=heq_level_of_top);!intro.
      
      inversion h_exct_lvl;subst.
      omega.
  - eapply IHstk1.
    + cbn in h_exct_lvl.
      now eapply exact_levelG_sublist;eauto. 
    + functional inversion heq_frameG;subst.
      * exfalso.

        assert (exact_levelG ((lvl, sto_id1) :: stk2)).
        { eapply exact_levelG_sublist2;eauto. }
        eapply exact_lvl_lvl_of_top in H.
        all:swap 1 2.
        cbn.
        reflexivity.
        eapply exact_lvl_lvl_of_top in h_exct_lvl.
        all:swap 1 2.
        cbn.
        reflexivity.
        simpl Datatypes.length in *.
        rewrite app_length in h_exct_lvl.
        simpl Datatypes.length in *.
        fold frame in *. (* omega fails to unify some terms otherwise *)
        omega.
      * eauto.
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
  !intros.
  !!specialize updateG_spec_1 with (1:=heq_updateG_stk_id).
  intro h_ex;decomp h_ex;subst;up_type.
  rename H2 into h_forall.
  rewrite heq_frameG in heq_frameG2.
  !invclear heq_frameG2.
  unfold update in heq_update_sto_id.
  cbn in heq_update_sto_id.
  !!destruct (updates sto_id id v) eqn:heq; try discriminate.
  !invclear heq_update_sto_id.
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
  !functional induction (updateG stk id v);simpl;!intros;try discriminate;rename x into id;subst;up_type.
  - unfold update;cbn.
    !invclear heq_Some;simpl.
    !assert (reside id f = true).
    { eapply update_ok_same_reside_orig; eauto. }
    rewrite heq_reside in heq_Some0.
    !invclear heq_Some0.
    unfold update in heq_update_f_x.
    cbn in heq_update_f_x.
    !assert (updates sto_id id v).

    !assert (reside id' (lvl_id, sto_id) = false).
    { cbn in *.
      destruct (resides id' sto_id);auto.
      exfalso.
      inversion heq_Some1.
      now apply hneq. }
    rewrite heq_reside0 in heq_Some1.
    unfold update in heq_update_f_x.
    cbn in heq_update_f_x.

    functional inversion heq_frameG;subst.
    + exfalso.
      apply hneq.
      destruct (updates sto_id id v);try discriminate.
      now inversion heq_update_f_x.
    + rewrite X in heq_Some1.
      now inversion heq_Some1.
  - up_type.
    !assert (reside id f = false).
    { apply reside_false_fetch_none.
      rewrite <- update_ok_none;eauto. }
    rewrite heq_reside in heq_Some0.
    !invclear heq_Some.
    destruct (reside id' f) eqn:heq.
    + !invclear heq_Some1.
      cbn in heq_frameG.
      cbn in heq.
      rewrite heq in heq_frameG.
      now inversion  heq_frameG.
    + eapply IHo ;eauto.
      cbn in heq_frameG.
      now rewrite heq in heq_frameG.
Qed.
*)
Lemma updateG_ok_others_frameG_orig: forall stk id v stk',
      updateG stk id v = Some stk' ->
      forall id' lvl sto,
        id<>id' ->
        frameG id' stk' = Some (lvl,sto) -> 
        exists sto', frameG id' stk = Some (lvl,sto').
Proof.
  intros until v.
  !functional induction (updateG stk id v);simpl;!intros;try discriminate.
  - !invclear heq_Some;simpl.
    !!pose proof update_ok_others_reside _ _ _ _ heq_update_f_x _ hneq.
    rewrite heq_reside.
    simpl in heq_frameG.
    !! (destruct (reside id' f') eqn:h).
    + !invclear heq_frameG.
      unfold update in heq_update_f_x.
      cbn in *.
      destruct (updates (store_of f) x v) eqn:heq.
      * !invclear heq_update_f_x.
        destruct f;simpl in *.
        eauto.
      * discriminate.
    + rewrite heq_frameG.
      eauto.
  - !invclear heq_Some;simpl.
    simpl in *. 
    !! (destruct (reside id' f) eqn:h).
    + !invclear heq_frameG.
      eauto.
    + eapply IHo;eauto.
Qed.

Lemma assignment_preserve_stack_match_CE :
  forall stbl CE s a id id_t e_v s',
    (* translating the variabe to a Cminor load address, so id belongs to CE *)
    transl_variable stbl CE a id = Errors.OK id_t ->
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    stack_match_CE s CE ->
    stack_match_CE s' CE.
Proof.
  !intros.
  red.
  !intros.
  up_type.
  red in h_stk_mtch_CE_s_CE.
  specialize (h_stk_mtch_CE_s_CE nme lvl).
  destruct h_stk_mtch_CE_s_CE as [h_stk_mtch_CE_s_CE h_stk_mtch_CE_s_CE'].
  !destruct (Nat.eq_dec id nme).
  - subst nme.
    !functional inversion heq_transl_variable.
    subst.
    !inversion h_storeUpd;subst.
    !!pose proof (storeUpdate_id_ok_same _ _ _ _ _ _ h_storeUpd).
    !destruct (updateG_ok_same_orig _ _ _ _ heq_updateG_s_id).
    rename x into e_v'.
    split;!intros.
    + !!pose proof updateG_ok_same_frameG_orig _ _ _ _ _ _ heq_updateG_s_id heq_frameG.
      !destruct h_ex.
      apply h_stk_mtch_CE_s_CE with (1:=heq_frameG0).
    + specialize h_stk_mtch_CE_s_CE' with (1:=heq_CEframeG_id_CE0).
      decomp h_stk_mtch_CE_s_CE'.
      eapply updateG_ok_same_frameG;eauto.
  - !functional inversion heq_transl_variable.
    subst.
    !inversion h_storeUpd;subst.
    !!pose proof storeUpdate_id_ok_others _ _ _ _ _ _ h_storeUpd _ hneq.
    !destruct (updateG_ok_same_orig _ _ _ _ heq_updateG_s_id).
    !!pose proof (updateG_ok_others_frameG _ _ _ _ heq_updateG_s_id).
    specialize H with (1:=hneq).
    split;!intros.
    + !assert (exists sto', frameG nme s = Some (lvl, sto')).
      { pose proof (updateG_ok_others_frameG_orig _ _ _ _ heq_updateG_s_id _ _ _ hneq heq_frameG).
        assumption. }
      !destruct h_ex.
      rename x0 into sto'.
      specialize H with (1:=heq_frameG0).
      eapply h_stk_mtch_CE_s_CE;eauto. 
    + specialize h_stk_mtch_CE_s_CE' with (1:=heq_CEframeG_nme_CE).
      destruct h_stk_mtch_CE_s_CE';eauto.
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
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
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
    (* the two storing operation maintain match_env *)
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    stack_separate stbl CE stkptr locenv g m'.
Proof.
  !intros.
  red.
  !intros.
  !destruct h_match_env.
  !destruct h_safe_cm_CE_m.
  decomp (storev_inv _ _ _ _ _ heq_storev_e_t_v_m');subst.
  !functional inversion heq_transl_name0;subst.
  generalize heq_transl_name.
  intro h_transl_name_remember.
  functional inversion h_transl_name_remember.
  eapply wf_chain_load_var' with (m:=m) in h_CM_eval_expr_nme_t.
  - eapply wf_chain_load_var' with (m:=m) in h_CM_eval_expr_nme'_t.
    + eapply h_separate_CE_m with (1:=heq_type_of_name);eauto.
    + apply h_inv_comp_CE_stbl.
    + eassumption.
    + assumption.
    + eapply eval_build_loads_offset_non_null_var with (5:=h_CM_eval_expr_id_t_id_t_v)
      ;eauto.
    + simpl in heq_transl_name0.
      eauto.
  - apply h_inv_comp_CE_stbl.
  - eassumption.
  - assumption.
  - eapply eval_build_loads_offset_non_null_var with (5:=h_CM_eval_expr_id_t_id_t_v)
    ;eauto.
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
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    stack_no_null_offset stbl CE.
Proof.
  !intros.
  !destruct h_match_env.
  !destruct h_safe_cm_CE_m.
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
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (Identifier a id) e_v (OK s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    safe_stack s'.
Proof.
  !intros.
  match goal with H: context C [overflowCheck] |- _ => rename H into h_overf_e_v end.
  !destruct h_match_env.
  !destruct h_safe_cm_CE_m.
  !intros.
  red.
  !intros.
  !destruct (Nat.eq_dec id0 id).
  - subst.
    apply h_overf_e_v.
    erewrite storeUpdate_id_ok_same in heq_SfetchG_id0_s';eauto.
    inversion heq_SfetchG_id0_s'.
    reflexivity.
  - red in h_safe_stack_s.
    apply h_safe_stack_s with (id:=id0);eauto.
    erewrite storeUpdate_id_ok_others;eauto.
Qed.




Lemma assignment_preserve_stack_freeable:
  forall stbl s CE spb ofs locenv' g m x x0 nme_t nme_chk nme_t_addr e_t_v m',
    invariant_compile CE stbl ->
    match_env stbl s CE (Values.Vptr spb ofs) locenv' g m ->
    transl_name stbl CE (Identifier x x0) =: nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv' m nme_t nme_t_addr ->
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
    stack_freeable stbl CE (Values.Vptr spb ofs) g locenv' m'.
Proof.
  !intros.
  red.
  !intros.
  destruct nme_t_v;simpl in * ; try discriminate.
  eapply Mem.store_valid_access_1.
  - eassumption.
  - eapply (me_stack_freeable (me_safe_cm_env h_match_env));eauto.
    eapply wf_chain_load_var';eauto.
    eapply eval_build_loads_offset_non_null_var
      with (5:=h_CM_eval_expr_nme_t_nme_t_v);eauto.
Qed.




    

Hint Resolve
     assignment_preserve_stack_match assignment_preserve_stack_match_CE
     assignment_preserve_stack_match_function
     assignment_preserve_stack_complete
     assignment_preserve_stack_separate assignment_preserve_loads_offset_non_null
     assignment_preserve_stack_no_null_offset assignment_preserve_stack_safe
     assignment_preserve_stack_freeable assignment_preserve_stack_match_addresses.


  


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
    Datatypes.length CE ≤ n -> (* the chaining structure must be at least as deep as CE *)
    (*     stack_localstack_aligned CE locenv g m ->  *)
    stack_no_null_offset stbl CE -> 
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
  !intros.
  destruct id_t_v;try discriminate.
  assert (4 <= (Int.unsigned i)).
  { eapply eval_build_loads_offset_non_null_var;eauto.
    eapply chain_aligned ;eauto. }
  eapply assignment_preserve_chained_stack_structure_aux; eauto.
Qed.

Lemma assignment_preserve_safe_cm_env:
  forall stbl s CE spb ofs locenv locenv' g m x x0 nme_t nme_chk nme_t_addr e_v e_t_v s' m',
    invariant_compile CE stbl ->
    match_env stbl s CE (Values.Vptr spb ofs) locenv g m ->
    transl_name stbl CE (Identifier x x0) =: nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t nme_t_addr ->
    compute_chnk stbl (Identifier x x0) = Errors.OK nme_chk ->
    transl_value e_v e_t_v ->
    storeUpdate stbl s (Identifier x x0) e_v (OK s') ->
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
    safe_cm_env stbl CE (Values.Vptr spb ofs) locenv' g m'.
Proof.
  !intros.
  assert (safe_cm_env stbl CE (Values.Vptr spb ofs) locenv g m').
  { split;eauto.
    eapply assignment_preserve_chained_stack_structure;eauto. }
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
  !!intros s nme v s' ?.
  !!functional induction updateG s nme v;(try now (simpl;!intros;discriminate));!intros.
  - inversion heq;subst;clear heq.
    cbn in *.
*)


Lemma assignment_preserve_Nodup_s:
  forall s x v s',
    ST.updateG s x v = Some s' ->
    NoDup s -> 
    NoDup s'.
Proof.
  intros s x v. 
  functional induction (ST.updateG s x v).
  - !intros.
    !invclear heq_Some.
    unfold NoDup in *;!intros.
    specialize h_nodup_s with (2:=heq_cuts_to).
    functional inversion heq_frameG;subst.
    + 
    assert (frameG nme (f :: s') = Some (lvl, sto)).
    { cbn in heq_frameG |- *.
      !!destruct (reside nme f') eqn:?.
      - specialize update_ok_same_reside_orig with (1:=e0);!intro.
        rewrite heq_reside0.
    }
    eapply h_nodup_s;eauto.
    
Qed.

Lemma assignment_preserve_Nodup_s:
  forall stbl s x x0 e_v s',
    storeUpdate stbl s (Identifier x x0) e_v (OK s') ->
    NoDup s -> 
    NoDup s'.
Proof.
  !!intros.
  !inversion h_storeUpd.
  clear h_storeUpd.
  specialize updateG_spec_1 with (1:=heq_updateG_s_x0).
(* xxxx *)
  intro h.
  decomp h.
  subst.

  red.
  !intros;up_type.



xxxx
  revert x s' heq_updateG_s_x0.
  !functional induction (ST.updateG s x0 e_v);simpl;!intros;up_type;decomp h_ex;subst.
  - (* the variable x0 is in f. *)
    !invclear heq_Some.
    red.
    !intros.
    functional inversion heq_frameG;subst.
    + admit.
    + 

    unfold NoDup in *;!intros;up_type.
    eapply h_nodup_s.
    
    functional inversion heq_frameG;subst.
    specialize h_nodup_s with (2:=heq_cuts_to).
    apply h_nodup_s with (lvl:=lvl).
  
  red.
  red in h_nodup_s_s.
  !intros.
  !assert (exists sto_nme, frameG nme s = Some (lvl,sto_nme)).
  { clear h_nodup_s_s.
    !inversion h_storeUpd;subst; clear h_storeUpd;up_type.
    destruct (Nat.eq_dec nme x0).
    - subst.
      eapply updateG_ok_same_frameG_orig;eauto.
    - eapply updateG_ok_others_frameG_orig;eauto. }
  decomp h_ex.
  up_type.
  eapply h_nodup_s_s;eauto.
  
(*
  specialize (fun sto' sto'' => nodup_s_s _ _ _ sto' sto'' heq1).
  !assert (sto = sto'++sto'').
  { eapply STACK.cuts_to_decomp;eauto. }
  !assert (exists v sto''', sto'' = (nme,v)::sto''').
  { eapply cuts_to_snd_reside;eauto.
    eapply frameG_resides;eauto. }
  decomp h_ex.
  subst.
  

  

  !inversion h_storeUpd;subst; clear h_storeUpd;up_type.


  assert (sto = sto'++sto'').
  { eapply aux;eauto. }
  subst.
  specialize (nodup_s_s _ _ _ sto' sto'' heq1).
  apply nodup_s_s.

  assert (update (lvl,sto) x0 e_v = Some (lvl, sto'++sto'')).
  { admit. }
  

  assert (sto_nme = update s).
(*   ST.updateG s x0 e_v = Some s' *)
  !assert (exists sto_nme', cuts_to nme sto_nme = (sto_nme', sto'')).
  { clear nodup_s_s.
    !inversion h_storeUpd;subst; clear h_storeUpd;up_type.
    functional inversion heq_updateG_s_x0;subst.
    destruct (Nat.eq_dec nme x0).
    - subst.



      eapply updateG_ok_same_frameG_orig;eauto.
    - eapply updateG_ok_others_frameG_orig;eauto.

    admit. }
  decomp h_ex.
  eapply nodup_s_s ;eauto.
Qed.

**)
Admitted.

Function my_update (f: frame) (x: idnum) (v: V): option frame := 
  match updates (store_of f) x v with 
  | Some s => Some (level_of f, s)
  | None => None 
  end.

Lemma my_update_ok: forall (f: frame) (x: idnum) (v: V), ST.update f x v = my_update f x v.
Proof.
  reflexivity.
Qed.


Function my_updateG (s : ST.state) (x : idnum) (v : V) {struct s} : option ST.state :=
  match s with
  | [ ] => None
  | f :: s' =>
      match ST.update f x v with
      | Some f' => Some (f' :: s')
      | None => match my_updateG s' x v with
                | Some s'' => Some (f :: s'')
                | None => None
                end
      end
  end
.

Lemma my_updateG_ok: forall f x v, ST.updateG f x v = my_updateG f x v.
Proof.
  reflexivity.
Qed.

Lemma foo: forall CE, CE <> nil -> CompilEnv.exact_levelG CE ->  CompilEnv.level_of_top CE = Some (Datatypes.length CE - 1)%nat.
Proof.
  !intros.
  destruct CE.
  - elim hneq;auto.
  - inversion h_exct_lvlG_CE;subst.
    unfold CompilEnv.level_of_top.
    simpl.
    auto with arith.
Qed.

(*
Lemma assignment_preserve_strong_match_env:
  forall stbl s CE spb ofs locenv g m x x0 nme_t nme_chk nme_t_addr e_v e_t_v s' m',
    strong_match_env stbl s CE (Values.Vptr spb ofs) locenv g m ->
    chained_stack_structure m (Datatypes.length s) (Values.Vptr spb ofs) ->
    transl_name stbl CE (Identifier x x0) =: nme_t ->
    forall h_overflow:(forall n, e_v = Int n -> overflowCheck n (OK (Int n))),
      invariant_compile CE stbl ->
      transl_name stbl CE (Identifier x x0) =: nme_t ->
      Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t nme_t_addr ->
      compute_chnk stbl (Identifier x x0) = Errors.OK nme_chk ->
      transl_value e_v e_t_v ->
      storeUpdate stbl s (Identifier x x0) e_v (OK s') ->
      Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
      strong_match_env stbl s' CE (Values.Vptr spb ofs) locenv g m'.
Proof.
  !!intros until 3.
  assert (ofs = Int.zero).
  { specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m).
    !intro.
    decomp h_ex.
    !inversion heq_vptr_spb_ofs.
    reflexivity. }
  subst.
  !functional inversion heq_transl_name;subst.
  clear heq_transl_name.
  !functional inversion heq_transl_variable.
  clear heq_transl_variable.
  revert x x0 nme_t nme_chk nme_t_addr e_v e_t_v s' m' δ_x0 lvl_x0 fr_x0 m'0 h_chain_m heq_CEfetchG_x0_CE heq_CEframeG_x0_CE heq_lvloftop_CE_m'0 heq_build_loads.
  !induction h_strg_mtch_s_CE_m;!intros.
  - !inversion h_storeUpd;subst.
    cbv in heq_updateG_x0.
    discriminate.
  - up_type.
    !inversion h_storeUpd;subst.
    rewrite my_updateG_ok in heq_updateG_x0.
    !functional inversion heq_updateG_x0;subst.
    all:rewrite <- my_updateG_ok in *.
    + (* The updated variable is in the top store *)
      rewrite my_update_ok in heq_update_x0.
      functional inversion heq_update_x0.
      rewrite <- my_update_ok in heq_update_x0.
      subst.
      econstructor.
      * specialize IHh_strg_mtch_s_CE_m with (s':=s).
        eapply IHh_strg_mtch_s_CE_m;eauto.
        -- !inversion h_chain_m;subst.
           rewrite h_loadv_v'_v in h_loadv.
           inversion h_loadv.
           subst.
           assumption.
        --
      * admit.
      * admit.
    + (* The updated variable is deeper un CE *)
      cbn in h_chain_m.
      !inversion h_chain_m;subst.
      rewrite h_loadv_v'_v in h_loadv.
      !invclear h_loadv.
      cbv in heq_lvloftop_m'0.
      !invclear heq_lvloftop_m'0.
      !!pose proof me_stack_match_CE h_match_env.
      red in h_stk_mtch_CE.
      specialize h_stk_mtch_CE with x0 lvl_x0.
      destruct h_stk_mtch_CE as [h1 h2].
      econstructor 2;eauto.
      * eapply IHh_strg_mtch_s_CE_m with (δ_x0:=δ_x0) (lvl_x0:=lvl_x0) (fr_x0:=fr_x0);eauto.
       all:swap 3 1.
        -- apply foo.
           ++ intro abs.*
              subst CE.
              specialize h2 with (1:=heq_CEframeG_x0).
              decomp h2.
              simpl in heq_frameG.
              
              !functional inversion heq_CEfetchG_x0;subst.
              ** apply update_ok_none in heq_update_x0.
                 !!pose proof me_stack_match_CE h_match_env.
                 red in h_stk_mtch_CE.
                 specialize h_stk_mtch_CE with x0 lvl_x0.
                 destruct h_stk_mtch_CE as [h1 h2].
                 !assert (frameG x0 ((m'0, sto) :: s) = Some (lvl_x0, sto)).
                 { simpl.
                   
                   apply CompilEnv.fetchG_ok in heq_CEfetchG_x0.
                   apply fetch_ok_none in heq_update_x0.
                   change CompilEnv.scope_level with scope_level in *.
                   rewrite heq_update_x0.
                   specialize h2 with (1:=heq_CEframeG_x0).
                   decomp h2.
                   simpl in heq_frameG.

                   !!pose proof CompilEnv.fetchG_ok _ _ _ heq_CEfetchG_x0.
                   simpl in heq_resideG.
                   
                   rewrite heq_resideG.
                   
                 }
                 specialize h1 with sto.
        
       
(* xxxxxxxxxxxxx *)


  revert stbl s spb locenv g m  nme_chk nme_t_addr e_v e_t_v s' m' δ_x0 lvl_x0 fr_x0 m'0 h_chain_m heq_CEfetchG_x0_CE heq_CEframeG_x0_CE heq_lvloftop_CE_m'0 heq_build_loads.
  induction 




  !!functional induction CompilEnv.fetchG x0 CE;!intros.
  all: swap 3 1.
  all: swap 3 2.
  - discriminate.
  - (* x0 belongs to top frame f *)
    rename fr_x0 into sto_CE.
    rename s' into CE.
    subst.
    !inversion heq_Some. clear heq_Some.
    assert (f = (lvl_x0, sto_CE)).
    { !functional inversion heq_CEframeG_x0;subst.
      - reflexivity.
      - pose proof CompilEnv.fetch_ok as h.
        specialize h with (1:=heq_CEfetch_x0_f).
        rewrite h in heq_reside.
        discriminate. }
    subst.
    !inversion h_strg_mtch_s;subst.

    !inversion h_storeUpd;subst. clear h_storeUpd.
    !functional inversion heq_updateG_x0;subst.
    all:swap 1 2.
    (* x0 cannot be unfound in sto, since it is in sto_CE. *)
    { exfalso. (* TODO: simplify this *)
      apply update_ok_none in heq_update_x0.
      !!pose proof me_stack_match_CE h_match_env.
      red in h_stk_mtch_CE.
      specialize h_stk_mtch_CE with x0 lvl_x0.
      destruct h_stk_mtch_CE as [h1 h2].
      specialize h2 with (1:=heq_CEframeG_x0).
      decomp h2.
      !functional inversion heq_frameG;subst.
      - apply fetch_ok_none in heq_update_x0.
        rewrite heq_update_x0 in heq_reside.
        discriminate.
      - !!assert (lvl_x0 > Datatypes.length s0)%nat.
        { admit. }
        !!pose proof me_exact_levelG h_match_env.
        !inversion h_exct_lvl;subst.
        specialize exact_lvl_level_of_top with (1:=h_exct_lvl_s0) (2:=heq_frameG0);!intros.
        decomp h_ex.
        destruct s0.
        + cbn in *.
          inversion heq_frameG0.
        + simpl in h_le, h_gt_lvl_x0.
          destruct f.
          cbn in heq_level_of_top.
          inversion heq_level_of_top.
          subst s.
          omega. }
    rewrite my_update_ok in heq_update_x0.
    functional inversion heq_update_x0.
    rewrite <- my_update_ok in *.
    subst.
    econstructor 2 with (v:=v) ;eauto.
    all:swap 1 2.
    + c

    !!pose proof me_stack_match_CE h_match_env.
      red in h_stk_mtch_CE.
      specialize h_stk_mtch_CE with x0 lvl_x0.
      destruct h_stk_mtch_CE as [h1 h2].
    

    + rewrite my_update_ok in heq_update_x0.
      !functional inversion heq_update_x0;subst.
      rewrite <- my_update_ok in heq_update_x0.
      cbn in heq_updates_x0.
      eapply C2 with (v:=(Values.Vptr spb ofs)) (locenv:=locenv).
      * admit. (* invisible *)
    + exfalso.
      apply update_ok_none in heq_update_x0.
      setoid_rewrite heq_fetch_x0 in heq_update_x0.
      discriminate.

    !invclear h_strg_mtch_s;up_type.
    !assert (∃ δ, fetch x0 (lvl,sto) = Some v_x0 ∧ ).
    { admit. }
    decomp h_ex.
    up_type.

    !functional inversion heq_updateG_s_x0;subst.
    + rewrite my_update_ok in heq_update_x0.
      !functional inversion heq_update_x0;subst.
      rewrite <- my_update_ok in heq_update_x0.
      cbn in heq_updates_x0.
      eapply C2 with (v:=(Values.Vptr spb ofs)) (locenv:=locenv).
      * admit. (* invisible *)
    + exfalso.
      apply update_ok_none in heq_update_x0.
      setoid_rewrite heq_fetch_x0 in heq_update_x0.
      discriminate.



    !functional inversion heq_updateG_s_x0;subst.
    + rewrite my_update_ok in heq_update_x0.
      !functional inversion heq_update_x0;subst.
      rewrite <- my_update_ok in heq_update_x0.
      cbn in heq_updates_x0.
      econstructor 2;eauto.
      
    cbn in heq_updateG_s_x0.
    
    !functional inversion heq_CEframeG_x0;subst; simpl in *.
    + rewrite heq_reside in heq_CEframeG_x0.
      clear heq_CEframeG_x0.
      !inversion h_strg_mtch_s;subst.
      !functional inversion heq_updateG_s_x0;subst;try discriminate.
      * admit.
      * exfalso.
        rewrite update_ok_none in heq_update_x0.
        !assert (stack_match_CE ((lvl_x0, sto) :: s0) ((lvl_x0, fr_x0) :: s')).
        { !inversion h_strg_mtch_s;subst.
          apply h_match_env0. }
        edestruct (h_stk_mtch_CE x0 lvl_x0) as [h_stk_mtch_CE1 h_stk_mtch_CE2].
        
        !assert (∃ CE_sto_x0 ,
                    CompilEnv.frameG x0 ((lvl_x0, fr_x0) :: s')
                    = Some (lvl_x0, CE_sto_x0)).
        { cbn.
          unfold CompilEnv.fetch in heq_CEfetch_x0_f.
          !!pose proof (CompilEnv.fetches_ok _ _ _ heq_CEfetch_x0_f).
          exists fr_x0.
          cbn in heq_resides.
          rewrite heq_resides.
          reflexivity. }
        decomp h_ex.
        specialize h_stk_mtch_CE2 with (1:=heq_CEframeG_x0).
        decomp h_stk_mtch_CE2.
        
        !assert (∃ δ , fetch x0 (lvl_x0, sto) = Some δ).
        { 
          simpl in heq_frameG.
          !!pose proof fetch_ok_none _ _ heq_update_x0.
          setoid_rewrite heq_reside0 in heq_frameG.
          specialize exact_lvl_level_of_top with (2:=heq_frameG);!intro.
          !assert (exact_levelG s0).
          { !inversion h_strg_mtch_s;subst.
            assert (exact_levelG ((lvl_x0, sto) :: s0)).
            !inversion h_match_env0.
            + assumption.
            + inversion H0.
              assumption. }
          specialize (H h_exct_lvl_s0).

          destruct (reside x0 (lvl_x0, sto)) eqn:heq_reside_x0;eauto.
          setoid_rewrite heq_reside_x0 in heq_reside0.
          discriminate.

          - destruct (fetch x0 (lvl_x0, sto)) eqn:heq_fetch_x0.
            + eauto.
            + !!pose proof fetch_ok_none _ _ heq_fetch_x0.
              rewrite heq_reside0 in heq_reside_x0.
              discriminate.
          - apply reside_false_fetch_none in heq_reside_x0.

          destruct (CompilEnv.reside x0 (lvl_x0, fr_x0)) eqn:heq_reside_x0.
          - 
          admit. (* use exact_lvl *)
        }
        decomp h_ex.
        setoid_rewrite heq_update_x0 in heq_fetch_x0.
        discriminate.
    + admit. (* use IH *)
  - !inversion h_strg_mtch_s;subst.
    !inversion h_storeUpd;subst.
    functional inversion heq_updateG_x0.
Admitted.
*)

Lemma assignment_preserve_match_env:
  forall stbl s CE spb ofs locenv g m x x0 nme_t nme_chk nme_t_addr e_v e_t_v s' m',
    forall h_overflow:(forall n, e_v = Int n -> overflowCheck n (OK (Int n))),
      invariant_compile CE stbl ->
      match_env stbl s CE (Values.Vptr spb ofs) locenv g m ->
      transl_name stbl CE (Identifier x x0) =: nme_t ->
      Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t nme_t_addr ->
      compute_chnk stbl (Identifier x x0) = Errors.OK nme_chk ->
      transl_value e_v e_t_v ->
      storeUpdate stbl s (Identifier x x0) e_v (OK s') ->
      Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
      match_env stbl s' CE (Values.Vptr spb ofs) locenv g m'.
Proof.
  !intros.
  generalize heq_transl_name; unfold transl_name;!intro.
  split;eauto.
  - admit.
  - eapply assignment_preserve_Nodup_s;eauto.
    apply h_match_env.
  - eapply assignment_preserve_Nodup_s;eauto.
    apply h_match_env.
  - eapply _s;eauto.
    apply h_match_env.
  - admit.
  - unfold transl_name in heq_transl_name.
    !!pose proof (me_stack_complete h_match_env).
    red in h_stk_cmpl_s_CE.
    specialize (h_stk_cmpl_s_CE x x0 nme_t heq_transl_name).
    decomp h_stk_cmpl_s_CE.
    !! pose proof (me_stack_match h_match_env).
    eapply assignment_preserve_safe_cm_env;eauto.
Admitted.

(* Is there the shadowed variable? If yes this lemma is wrong. *)
(*
Lemma match_env_cons:
  forall stbl CE s locenv g m sp sp',
    s<>[] -> CE <> [] -> 
    invariant_compile CE stbl ->
    match_env stbl s CE sp locenv g m ->
    Mem.loadv AST.Mint32 m sp = Some sp' ->
    stack_match stbl (List.tl s) (List.tl CE) sp' locenv g m.
Proof.
  unfold stack_match.
  !intros.
  !functional inversion heq_transl_name;subst.
  functional inversion heq_transl_variable;subst.
  assert (evalName stbl s (Identifier astnum id) (OK v)).
  { admit. (* invariant_compile mplies that CE has no shadowing, thus  *)

  }

  revert dependent m.
  revert dependent s.
  revert dependent typ_nme.
  revert dependent cm_typ_nme.
  revert dependent h_inv_comp_CE_stbl.
  revert dependent hneq0.
  revert locenv g sp sp' v load_addr_nme.
  !functional inversion heq_transl_name.
  clear heq_transl_name.
  revert heq_transl_variable heq_nme. heq_nme0.
  remember (tl CE) as CE'.
  revert CE HeqCE' nme_t nme nme0.
  !!functional induction transl_variable stbl CE' astnum id;simpl;!intros.
  
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
                               /\ Int.unsigned ofs_id <= ofs < Int.unsigned ofs_id + size_chunk id_chk.

(* The negation of previous predicate. *)
Definition invisible_cminor_addr st CE g astnum locenv stkptr (m:mem) spb ofs :=
  ∀ id id_t id_chk spb_id ofs_id,
    (* id_t is the address of id_t *)
    transl_variable st CE astnum id =: id_t
    -> compute_chnk_id st id =: id_chk
    -> Cminor.eval_expr g stkptr locenv m id_t (Values.Vptr spb_id ofs_id)
    (* The address spb+ofs is not part of the interval [spb_id , spb_id+ofs_id[ *)
    -> spb_id ≠ spb \/ ofs >= Int.unsigned ofs_id + size_chunk id_chk \/ ofs < Int.unsigned ofs_id.


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


Ltac rename_hyp_forbid h th :=
  match th with
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "h_forbid_" m "_" m' "_" sp "_" ofs
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "h_forbid_" m "_" m'
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "h_forbid_" m
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "h_forbid_" m'
  | forbidden ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?m' ?sp ?ofs => fresh "h_forbid"

  | forbidden_strict ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?sp ?ofs => fresh "h_forbid_" m "_" sp "_" ofs
  | forbidden_strict ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?sp ?ofs => fresh "h_forbid_" m
  | forbidden_strict ?st ?CE ?g ?astnum ?e_chain ?stckptr ?m ?sp ?ofs => fresh "h_forbid"

  | invisible_cminor_addr ?st ?CE ?g ?astnum ?e ?sp ?m ?sp'b ?sp'ofs => fresh "h_invis_" sp "_" "_" m "_" sp'b "_" sp'ofs
  | invisible_cminor_addr ?st ?CE ?g ?astnum ?e ?sp ?m ?sp'b ?sp'ofs => fresh "h_invis_" sp "_" "_" sp'b "_" sp'ofs
  | invisible_cminor_addr ?st ?CE ?g ?astnum ?e ?sp ?m ?sp'b ?sp'ofs => fresh "h_invis_" sp'b "_" sp'ofs
  | invisible_cminor_addr ?st ?CE ?g ?astnum ?e ?sp ?m ?sp'b ?sp'ofs => fresh "h_invis"
  | _ => rename_hyp_incro h th
  end.
Ltac rename_sparkprf ::= rename_hyp_forbid.


(* Are those useful? If yes finish the proofs (needs updating compcert, 
   not true with current version). *)
Axiom trans_unchanged : forall P, transitive _ (Mem.unchanged_on P).


Instance unchanged_on_iff: Proper ((eq ==> eq ==> iff) ==> (eq ==> eq ==> iff)) Mem.unchanged_on.
Proof.
  repeat red.
  !intros P Q;!intros ;subst.
  split;intros h;auto.
  - repeat red in H.
    inversion h.
    constructor;intros .
    + eapply unchanged_on_perm;auto.
      specialize (H b b eq_refl ofs ofs eq_refl).
      destruct H.
      eauto.
    + eapply unchanged_on_contents;auto.
      specialize (H b b eq_refl ofs ofs eq_refl).
      destruct H.
      eauto.
  - repeat red in H.
    inversion h.
    constructor;intros .
    + eapply unchanged_on_perm;auto.
      specialize (H b b eq_refl ofs ofs eq_refl).
      destruct H.
      eauto.
    + eapply unchanged_on_contents;auto.
      specialize (H b b eq_refl ofs ofs eq_refl).
      destruct H.
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

Lemma unchange_forbidden_sym: forall st CE g astnum e1 e_chain' sp m1 m2,
    unchange_forbidden st CE g astnum e1 e_chain' sp m1 m2 ->
    unchange_forbidden st CE g astnum  e_chain' e1 sp m2 m1.
Proof.
  intros st CE g astnum e1 e_chain' sp m1 m2 H. 
  red.
  intros sp_id ofs_id. 
  symmetry.
  red in H.
  eapply H;eauto.
Admitted.

Lemma unchange_forbidden_refl: forall st CE g astnum e1 sp m,
    unchange_forbidden st CE g astnum e1 e1 sp m m.
Proof.
  !intros.
  red;!intros.
  reflexivity.
Qed.

Definition strict_unchanged_on st CE g astnum e_chain e_chain' sp m m' :=
  Mem.unchanged_on (forbidden st CE g astnum e_chain sp m m) m m' /\
  unchange_forbidden st CE g astnum e_chain e_chain' sp m m'.

Lemma stack_localstack_aligned_locenv:
  forall lvl  g m e1 sp,
    stack_localstack_aligned lvl e1 g m sp -> 
    forall e2, stack_localstack_aligned lvl e2 g m sp.
Proof.
  !intros.
  unfold stack_localstack_aligned in *;!intros.
  specialize (h_aligned_g_m _ h_le_δ_lvl_lvl).
  decomp h_aligned_g_m.
  exists b_δ.
  apply eval_expr_build_load_const_inv_locenv with (1:=h_CM_eval_expr).
Qed.


Ltac rename_hyp_forbid_unch h th :=
  match th with
  | unchange_forbidden ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "h_unch_forbid_" m "_" m'
  | unchange_forbidden ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "h_unch_forbid_" m
  | unchange_forbidden ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "h_unch_forbid_" m'
  | unchange_forbidden ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "h_unch_forbid"

  | strict_unchanged_on ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "h_strict_unch_" m "_" m'
  | strict_unchanged_on ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "h_strict_unch_" m
  | strict_unchanged_on ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "h_strict_unch_" m'
  | strict_unchanged_on ?st ?CE ?g ?astnum ?e_chain ?e_chain' ?spid ?m ?m' => fresh "h_strict_unch"
  | _ => rename_hyp_forbid h th
  end.
Ltac rename_sparkprf ::= rename_hyp_forbid_unch.

(* The forbidden *addresses* remain the same when storing values of
   parameters in the local stack. + chained_structure preserved.  *)
Lemma exec_store_params_preserve_forbidden_subproof:
  forall lparams st CE initparams,
    CompilEnv.exact_levelG CE ->    
    stack_no_null_offset st CE ->
    store_params st CE lparams = Errors.OK initparams -> 
    forall astnum g proc_t sp e_chain e_chain' m t2 m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp ->
      exec_stmt g proc_t sp e_chain m initparams t2 e_chain' m' Out_normal ->
      chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_chain e_chain' sp m m'.
Proof.
  !!intros until CE.
  rewrite store_params_ok.
  !!functional induction function_utils.store_params st CE lparams;try rewrite <- store_params_ok in *;cbn;!intros;try discriminate;eq_same_clear; up_type.
  - inversion h_exec_stmt_initparams_Out_normal.
    split.
    + subst.
      assumption.
    + red.
      reflexivity.
  (* The three following cases are identical, i.e. the parameter mode
       should not be case split but functional induction does and I don't
       want to make the induction by hand. *)
  - specialize (IHr _ h_exct_lvlG_CE h_nonul_ofs heq_store_params).
    !invclear h_exec_stmt_initparams_Out_normal; eq_same_clear.
    specialize (fun h_chain h_align => IHr astnum _ _ _ _ _ _ _ _ _ heq_length h_chain h_align h_exec_stmt_x0_Out_normal).
    rename m1 into m_mid.
    rename e1 into e_mid.
    !invclear h_exec_stmt.
    up_type.

    !assert (stack_localstack_aligned (Datatypes.length CE) e_mid g m_mid sp).
    { unfold Mem.storev in heq_storev_v_m_mid.
      destruct x1_v; try discriminate.
      eapply wf_chain_load_aligned;eauto.
      eapply eval_build_loads_offset_non_null_var;eauto. }
    !assert (stack_localstack_aligned (Datatypes.length CE) e_chain' g m sp).
    { eapply stack_localstack_aligned_locenv;eauto. }
    specialize (fun h_chain => IHr h_chain h_aligned_g_m_mid).
    !assert (chained_stack_structure m_mid lvl sp).
    { eapply assignment_preserve_chained_stack_structure;eauto.
      omega. }
    specialize (IHr h_chain_lvl_sp0).
    split.
    { apply IHr. }
    { eapply unchange_forbidden_trans with (m2:=m_mid); [| eapply IHr].
      clear IHr h_exec_stmt_x0_Out_normal m'.
      red.
      !intros.
      split;!intros.
      + unfold forbidden.
        !destruct h_forbid_m_m_sp_id_ofs_id.
        split.
        * red;!intros.
          red in h_invis_sp__m_sp_id_ofs_id.
          specialize (h_invis_sp__m_sp_id_ofs_id
                        id id_t id_chk spb_id ofs_id0 heq_transl_variable heq_compute_chnk_id).
          set (val_id_t:=(Values.Vptr spb_id ofs_id0)) in *;up_type.
          !assert (Cminor.eval_expr g sp e_mid m id_t val_id_t).
          { unfold Mem.storev in heq_storev_v_m_mid.
            destruct x1_v; try discriminate.
            eapply eval_expr_transl_variable_inv_locenv with (locenv:=e_chain');eauto.
            eapply wf_chain_load_var'.
            - eassumption.
            - cbn. eapply heq_storev_v_m_mid.
            - assumption.
            - eapply eval_build_loads_offset_non_null_var.
              + eassumption.
              + eassumption.
              + exact h_aligned_g_m. (*xxx instantiate correctly. shelve.*)
              + cbn in heq_transl_name.
                eapply heq_transl_name.
              + eassumption.
            - eassumption.
            - eapply eval_expr_transl_variable_inv_locenv ; eauto. }
          specialize (h_invis_sp__m_sp_id_ofs_id h_CM_eval_expr_id_t_val_id_t).
          assumption.
        * unfold is_free_block in *.
          intro abs.
          apply neg_h_free_blck_m_sp_id_ofs_id.
          intros perm. 
          intro abs2.
          unfold Mem.storev in heq_storev_v_m_mid.
          destruct x1_v; try discriminate.
          eapply Mem.perm_store_1 in abs2;eauto.
          eapply abs;eassumption.
      + unfold forbidden.
        !destruct h_forbid_m_mid_m_mid_sp_id_ofs_id.
        split.
        * red;!intros.
          red in h_invis_sp__m_mid_sp_id_ofs_id.
          specialize (h_invis_sp__m_mid_sp_id_ofs_id
                        id id_t id_chk spb_id ofs_id0 heq_transl_variable heq_compute_chnk_id).
          set (val_id_t:=(Values.Vptr spb_id ofs_id0)) in *;up_type.
          !assert (Cminor.eval_expr g sp e_mid m_mid id_t val_id_t).
          { unfold Mem.storev in heq_storev_v_m_mid.
            destruct x1_v; try discriminate.
            eapply eval_expr_transl_variable_inv_locenv with (locenv:=e_mid);eauto.
            eapply wf_chain_load_var.
            5:eauto.
            2:eauto.
            all:eauto.
            eapply eval_build_loads_offset_non_null_var.
            + eassumption.
            + eassumption.
            + exact h_aligned_g_m. (*xxx instantiate correctly. shelve.*)
            + cbn in heq_transl_name.
              eapply heq_transl_name.
            + eassumption. }
          specialize (h_invis_sp__m_mid_sp_id_ofs_id h_CM_eval_expr_id_t_val_id_t).
          assumption.
        * unfold is_free_block in *.
          intro abs.
          apply neg_h_free_blck_m_mid_sp_id_ofs_id.
          intros perm. 
          intro abs2.
          unfold Mem.storev in heq_storev_v_m_mid.
          destruct x1_v; try discriminate.
          eapply Mem.perm_store_2 in abs2;eauto.
          eapply abs;eassumption. }
  - specialize (IHr _ h_exct_lvlG_CE h_nonul_ofs heq_store_params).
    !invclear h_exec_stmt_initparams_Out_normal; eq_same_clear.
    specialize (fun h_chain h_align => IHr astnum _ _ _ _ _ _ _ _ _ heq_length h_chain h_align h_exec_stmt_x0_Out_normal).
    rename m1 into m_mid.
    rename e1 into e_mid.
    !invclear h_exec_stmt.
    up_type.

    !assert (stack_localstack_aligned (Datatypes.length CE) e_mid g m_mid sp).
    { unfold Mem.storev in heq_storev_v_m_mid.
      destruct x1_v; try discriminate.
      eapply wf_chain_load_aligned;eauto.
      eapply eval_build_loads_offset_non_null_var;eauto. }
    !assert (stack_localstack_aligned (Datatypes.length CE) e_chain' g m sp).
    { eapply stack_localstack_aligned_locenv;eauto. }
    specialize (fun h_chain => IHr h_chain h_aligned_g_m_mid).
    !assert (chained_stack_structure m_mid lvl sp).
    { eapply assignment_preserve_chained_stack_structure;eauto.
      omega. }
    specialize (IHr h_chain_lvl_sp0).
    split.
    { apply IHr. }
    { eapply unchange_forbidden_trans with (m2:=m_mid); [| eapply IHr].
      clear IHr h_exec_stmt_x0_Out_normal m'.
      red.
      !intros.
      split;!intros.
      + unfold forbidden.
        !destruct h_forbid_m_m_sp_id_ofs_id.
        split.
        * red;!intros.
          red in h_invis_sp__m_sp_id_ofs_id.
          specialize (h_invis_sp__m_sp_id_ofs_id
                        id id_t id_chk spb_id ofs_id0 heq_transl_variable heq_compute_chnk_id).
          set (val_id_t:=(Values.Vptr spb_id ofs_id0)) in *;up_type.
          !assert (Cminor.eval_expr g sp e_mid m id_t val_id_t).
          { unfold Mem.storev in heq_storev_v_m_mid.
            destruct x1_v; try discriminate.
            eapply eval_expr_transl_variable_inv_locenv with (locenv:=e_chain');eauto.
            eapply wf_chain_load_var'.
            - eassumption.
            - cbn. eapply heq_storev_v_m_mid.
            - assumption.
            - eapply eval_build_loads_offset_non_null_var.
              + eassumption.
              + eassumption.
              + exact h_aligned_g_m. (*xxx instantiate correctly. shelve.*)
              + cbn in heq_transl_name.
                eapply heq_transl_name.
              + eassumption.
            - eassumption.
            - eapply eval_expr_transl_variable_inv_locenv ; eauto. }
          specialize (h_invis_sp__m_sp_id_ofs_id h_CM_eval_expr_id_t_val_id_t).
          assumption.
        * unfold is_free_block in *.
          intro abs.
          apply neg_h_free_blck_m_sp_id_ofs_id.
          intros perm. 
          intro abs2.
          unfold Mem.storev in heq_storev_v_m_mid.
          destruct x1_v; try discriminate.
          eapply Mem.perm_store_1 in abs2;eauto.
          eapply abs;eassumption.
      + unfold forbidden.
        !destruct h_forbid_m_mid_m_mid_sp_id_ofs_id.
        split.
        * red;!intros.
          red in h_invis_sp__m_mid_sp_id_ofs_id.
          specialize (h_invis_sp__m_mid_sp_id_ofs_id
                        id id_t id_chk spb_id ofs_id0 heq_transl_variable heq_compute_chnk_id).
          set (val_id_t:=(Values.Vptr spb_id ofs_id0)) in *;up_type.
          !assert (Cminor.eval_expr g sp e_mid m_mid id_t val_id_t).
          { unfold Mem.storev in heq_storev_v_m_mid.
            destruct x1_v; try discriminate.
            eapply eval_expr_transl_variable_inv_locenv with (locenv:=e_mid);eauto.
            eapply wf_chain_load_var.
            5:eauto.
            2:eauto.
            all:eauto.
            eapply eval_build_loads_offset_non_null_var.
            + eassumption.
            + eassumption.
            + exact h_aligned_g_m. (*xxx instantiate correctly. shelve.*)
            + cbn in heq_transl_name.
              eapply heq_transl_name.
            + eassumption. }
          specialize (h_invis_sp__m_mid_sp_id_ofs_id h_CM_eval_expr_id_t_val_id_t).
          assumption.
        * unfold is_free_block in *.
          intro abs.
          apply neg_h_free_blck_m_mid_sp_id_ofs_id.
          intros perm. 
          intro abs2.
          unfold Mem.storev in heq_storev_v_m_mid.
          destruct x1_v; try discriminate.
          eapply Mem.perm_store_2 in abs2;eauto.
          eapply abs;eassumption. }
  - specialize (IHr _ h_exct_lvlG_CE h_nonul_ofs heq_store_params).
    !invclear h_exec_stmt_initparams_Out_normal; eq_same_clear.
    specialize (fun h_chain h_align => IHr astnum _ _ _ _ _ _ _ _ _ heq_length h_chain h_align h_exec_stmt_x0_Out_normal).
    rename m1 into m_mid.
    rename e1 into e_mid.
    !invclear h_exec_stmt.
    up_type.

    !assert (stack_localstack_aligned (Datatypes.length CE) e_mid g m_mid sp).
    { unfold Mem.storev in heq_storev_v_m_mid.
      destruct x1_v; try discriminate.
      eapply wf_chain_load_aligned;eauto.
      eapply eval_build_loads_offset_non_null_var;eauto. }
    !assert (stack_localstack_aligned (Datatypes.length CE) e_chain' g m sp).
    { eapply stack_localstack_aligned_locenv;eauto. }
    specialize (fun h_chain => IHr h_chain h_aligned_g_m_mid).
    !assert (chained_stack_structure m_mid lvl sp).
    { eapply assignment_preserve_chained_stack_structure;eauto.
      omega. }
    specialize (IHr h_chain_lvl_sp0).
    split.
    { apply IHr. }
    { eapply unchange_forbidden_trans with (m2:=m_mid); [| eapply IHr].
      clear IHr h_exec_stmt_x0_Out_normal m'.
      red.
      !intros.
      split;!intros.
      + unfold forbidden.
        !destruct h_forbid_m_m_sp_id_ofs_id.
        split.
        * red;!intros.
          red in h_invis_sp__m_sp_id_ofs_id.
          specialize (h_invis_sp__m_sp_id_ofs_id
                        id id_t id_chk spb_id ofs_id0 heq_transl_variable heq_compute_chnk_id).
          set (val_id_t:=(Values.Vptr spb_id ofs_id0)) in *;up_type.
          !assert (Cminor.eval_expr g sp e_mid m id_t val_id_t).
          { unfold Mem.storev in heq_storev_v_m_mid.
            destruct x1_v; try discriminate.
            eapply eval_expr_transl_variable_inv_locenv with (locenv:=e_chain');eauto.
            eapply wf_chain_load_var'.
            - eassumption.
            - cbn. eapply heq_storev_v_m_mid.
            - assumption.
            - eapply eval_build_loads_offset_non_null_var.
              + eassumption.
              + eassumption.
              + exact h_aligned_g_m. (*xxx instantiate correctly. shelve.*)
              + cbn in heq_transl_name.
                eapply heq_transl_name.
              + eassumption.
            - eassumption.
            - eapply eval_expr_transl_variable_inv_locenv ; eauto. }
          specialize (h_invis_sp__m_sp_id_ofs_id h_CM_eval_expr_id_t_val_id_t).
          assumption.
        * unfold is_free_block in *.
          intro abs.
          apply neg_h_free_blck_m_sp_id_ofs_id.
          intros perm. 
          intro abs2.
          unfold Mem.storev in heq_storev_v_m_mid.
          destruct x1_v; try discriminate.
          eapply Mem.perm_store_1 in abs2;eauto.
          eapply abs;eassumption.
      + unfold forbidden.
        !destruct h_forbid_m_mid_m_mid_sp_id_ofs_id.
        split.
        * red;!intros.
          red in h_invis_sp__m_mid_sp_id_ofs_id.
          specialize (h_invis_sp__m_mid_sp_id_ofs_id
                        id id_t id_chk spb_id ofs_id0 heq_transl_variable heq_compute_chnk_id).
          set (val_id_t:=(Values.Vptr spb_id ofs_id0)) in *;up_type.
          !assert (Cminor.eval_expr g sp e_mid m_mid id_t val_id_t).
          { unfold Mem.storev in heq_storev_v_m_mid.
            destruct x1_v; try discriminate.
            eapply eval_expr_transl_variable_inv_locenv with (locenv:=e_mid);eauto.
            eapply wf_chain_load_var.
            5:eauto.
            2:eauto.
            all:eauto.
            eapply eval_build_loads_offset_non_null_var.
            + eassumption.
            + eassumption.
            + exact h_aligned_g_m. (*xxx instantiate correctly. shelve.*)
            + cbn in heq_transl_name.
              eapply heq_transl_name.
            + eassumption. }
          specialize (h_invis_sp__m_mid_sp_id_ofs_id h_CM_eval_expr_id_t_val_id_t).
          assumption.
        * unfold is_free_block in *.
          intro abs.
          apply neg_h_free_blck_m_mid_sp_id_ofs_id.
          intros perm. 
          intro abs2.
          unfold Mem.storev in heq_storev_v_m_mid.
          destruct x1_v; try discriminate.
          eapply Mem.perm_store_2 in abs2;eauto.
          eapply abs;eassumption. }
Qed.

(* The forbidden addresses (which does not move due to previous lemma)
   are not written during the storing of parameters in local stack. *)

Lemma exec_store_params_unchanged_on_subproof:
  forall lparams st CE initparams,
    CompilEnv.exact_levelG CE ->
    stack_no_null_offset st CE ->
    store_params st CE lparams =: initparams ->
    forall astnum g proc_t sp e_chain m t2 e_postchain m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp -> 
      exec_stmt g proc_t sp e_chain m initparams t2 e_postchain m' Out_normal ->
      Mem.unchanged_on (forbidden st CE g astnum e_chain sp m m) m m'.
Proof.
  !intros.
  !!pose proof (exec_store_params_preserve_forbidden_subproof
                  _ _ _ _ h_exct_lvlG_CE h_nonul_ofs heq_store_prms_lparams_initparams
                  astnum _ proc_t _ _ _ _ _ _ _ heq_length h_chain_lvl_sp h_aligned_g_m
                  h_exec_stmt_initparams_Out_normal).
  decomp h_and.
  revert initparams h_exct_lvlG_CE h_nonul_ofs heq_store_prms_lparams_initparams astnum g proc_t
         sp e_chain m t2 e_postchain m' lvl heq_length h_aligned_g_m h_exec_stmt_initparams_Out_normal
         h_unch_forbid_m_m' h_chain_lvl_sp h_chain_lvl_sp0.
  rewrite store_params_ok.
  !!functional induction function_utils.store_params st CE lparams;
    try rewrite <- store_params_ok in *;cbn;!intros;try discriminate.
  - !invclear heq_OK.
    inversion h_exec_stmt_initparams_Out_normal;subst.
    apply Mem.unchanged_on_refl.
    (* The three following cases are identical, i.e. the parameter mode
       should not be case split but functional induction does and I don't
       want to make the induction by hand. *)
  - rename x0 into initparams'.
    rename x1 into prm_name_t.
    !invclear heq_OK.
    !invclear h_exec_stmt_initparams_Out_normal; eq_same_clear.
    !assert (stack_localstack_aligned (Datatypes.length CE) e1 g m1 sp).
    { !inversion h_exec_stmt.
      destruct prm_name_t_v;try now (cbn in heq_storev_v_m1; discriminate).
      eapply wf_chain_load_aligned;eauto.
      eapply eval_build_loads_offset_non_null_var;eauto. }
    specialize (IHr _ h_exct_lvlG_CE h_nonul_ofs heq_store_params astnum
                    _ _ _ _ _ _ _ _ _ heq_length h_aligned_g_m1 h_exec_stmt_initparams'_Out_normal).
    rename m1 into m_mid.
    rename e1 into e_mid.
    !invclear h_exec_stmt.
    up_type.
    !assert (chained_stack_structure m_mid lvl sp).
    { destruct prm_name_t_v eqn:heqstorev;try now (cbn in heq_storev_v_m_mid; discriminate).
      subst.
      eapply assignment_preserve_chained_stack_structure with (m:=m);eauto. }
    !assert (chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_mid e_postchain sp m_mid m').
    { eapply exec_store_params_preserve_forbidden_subproof;eauto. }
    decomp h_and.
    !assert (unchange_forbidden st CE g astnum e_mid e_mid sp m m_mid).
    { eapply unchange_forbidden_trans with (e2:= e_postchain)(m2:=m');eauto.
      apply unchange_forbidden_sym;auto. }
      
    specialize (IHr h_unch_forbid_m_mid_m' h_chain_lvl_sp1 h_chain_lvl_sp2).

    apply trans_unchanged with m_mid;auto.
    + unfold Mem.storev in heq_storev_v_m_mid.
      destruct prm_name_t_v;try now discriminate.
      eapply Mem.store_unchanged_on;eauto;!intros.
      unfold forbidden.
      intros [abs1 abs2].
      red in abs1.
      cbn in heq_transl_name.
      setoid_rewrite <- transl_variable_astnum with (a:=astnum) in heq_transl_name;eauto.
      specialize (abs1 (parameter_name prm) prm_name_t x b i heq_transl_name heq_compute_chnk h_CM_eval_expr_prm_name_t_prm_name_t_v).
      destruct abs1; try omega.
      apply H;auto.
    + eapply unchanged_on_iff  ;eauto.
      red; red ; !intros;subst.
      eapply h_unch_forbid_m_m_mid.
  - rename x0 into initparams'.
    rename x1 into prm_name_t.
    !invclear heq_OK.
    !invclear h_exec_stmt_initparams_Out_normal; eq_same_clear.
    !assert (stack_localstack_aligned (Datatypes.length CE) e1 g m1 sp).
    { !inversion h_exec_stmt.
      destruct prm_name_t_v;try now (cbn in heq_storev_v_m1; discriminate).
      eapply wf_chain_load_aligned;eauto.
      eapply eval_build_loads_offset_non_null_var;eauto. }
    specialize (IHr _ h_exct_lvlG_CE h_nonul_ofs heq_store_params astnum
                    _ _ _ _ _ _ _ _ _ heq_length h_aligned_g_m1 h_exec_stmt_initparams'_Out_normal).
    rename m1 into m_mid.
    rename e1 into e_mid.
    !invclear h_exec_stmt.
    up_type.
    !assert (chained_stack_structure m_mid lvl sp).
    { destruct prm_name_t_v eqn:heqstorev;try now (cbn in heq_storev_v_m_mid; discriminate).
      subst.
      eapply assignment_preserve_chained_stack_structure with (m:=m);eauto. }
    !assert (chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_mid e_postchain sp m_mid m').
    { eapply exec_store_params_preserve_forbidden_subproof;eauto. }
    decomp h_and.
    !assert (unchange_forbidden st CE g astnum e_mid e_mid sp m m_mid).
    { eapply unchange_forbidden_trans with (e2:= e_postchain)(m2:=m');eauto.
      apply unchange_forbidden_sym;auto. }
      
    specialize (IHr h_unch_forbid_m_mid_m' h_chain_lvl_sp1 h_chain_lvl_sp2).

    apply trans_unchanged with m_mid;auto.
    + unfold Mem.storev in heq_storev_v_m_mid.
      destruct prm_name_t_v;try now discriminate.
      eapply Mem.store_unchanged_on;eauto;!intros.
      unfold forbidden.
      intros [abs1 abs2].
      red in abs1.
      cbn in heq_transl_name.
      setoid_rewrite <- transl_variable_astnum with (a:=astnum) in heq_transl_name;eauto.
      specialize (abs1 (parameter_name prm) prm_name_t x b i heq_transl_name heq_compute_chnk h_CM_eval_expr_prm_name_t_prm_name_t_v).
      destruct abs1; try omega.
      apply H;auto.
    + eapply unchanged_on_iff  ;eauto.
      red;red;!intros;subst.
      eapply h_unch_forbid_m_m_mid.
  - rename x0 into initparams'.
    rename x1 into prm_name_t.
    !invclear heq_OK.
    !invclear h_exec_stmt_initparams_Out_normal; eq_same_clear.
    !assert (stack_localstack_aligned (Datatypes.length CE) e1 g m1 sp).
    { !inversion h_exec_stmt.
      destruct prm_name_t_v;try now (cbn in heq_storev_v_m1; discriminate).
      eapply wf_chain_load_aligned;eauto.
      eapply eval_build_loads_offset_non_null_var;eauto. }
    specialize (IHr _ h_exct_lvlG_CE h_nonul_ofs heq_store_params astnum
                    _ _ _ _ _ _ _ _ _ heq_length h_aligned_g_m1 h_exec_stmt_initparams'_Out_normal).
    rename m1 into m_mid.
    rename e1 into e_mid.
    !invclear h_exec_stmt.
    up_type.
    !assert (chained_stack_structure m_mid lvl sp).
    { destruct prm_name_t_v eqn:heqstorev;try now (cbn in heq_storev_v_m_mid; discriminate).
      subst.
      eapply assignment_preserve_chained_stack_structure with (m:=m);eauto. }
    !assert (chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_mid e_postchain sp m_mid m').
    { eapply exec_store_params_preserve_forbidden_subproof;eauto. }
    decomp h_and.
    !assert (unchange_forbidden st CE g astnum e_mid e_mid sp m m_mid).
    { eapply unchange_forbidden_trans with (e2:= e_postchain)(m2:=m');eauto.
      apply unchange_forbidden_sym;auto. }
      
    specialize (IHr h_unch_forbid_m_mid_m' h_chain_lvl_sp1 h_chain_lvl_sp2).

    apply trans_unchanged with m_mid;auto.
    + unfold Mem.storev in heq_storev_v_m_mid.
      destruct prm_name_t_v;try now discriminate.
      eapply Mem.store_unchanged_on;eauto;!intros.
      unfold forbidden.
      intros [abs1 abs2].
      red in abs1.
      cbn in heq_transl_name.
      setoid_rewrite <- transl_variable_astnum with (a:=astnum) in heq_transl_name;eauto.
      specialize (abs1 (parameter_name prm) prm_name_t x b i heq_transl_name heq_compute_chnk h_CM_eval_expr_prm_name_t_prm_name_t_v).
      destruct abs1; try omega.
      apply H;auto.
    + eapply unchanged_on_iff  ;eauto.
      red; red;!intros;subst.
      eapply h_unch_forbid_m_m_mid.
Qed.


(* The forbidden *addresses* remain the same when storing values of
   parameters in the local stack.  *)
Lemma exec_init_locals_preserve_forbidden_subproof:
  forall decl st CE locvarinit,
    CompilEnv.exact_levelG CE ->    
    stack_no_null_offset st CE ->
    init_locals st CE decl =: locvarinit ->
    forall astnum g proc_t sp e_chain e_chain' m t2 m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp ->
      exec_stmt g proc_t sp e_chain m locvarinit t2 e_chain' m' Out_normal ->
      chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_chain e_chain' sp m m'.
Proof.
  !!intros until CE.
  rewrite init_locals_ok.
  !!functional induction function_utils.init_locals st CE decl;try rewrite <- init_locals_ok in * ;cbn;
    !intros;try discriminate;eq_same_clear; up_type;
      split;try now (inversion h_exec_stmt_locvarinit_Out_normal; try red; try reflexivity;subst;try assumption).
  - inversion h_exec_stmt_locvarinit_Out_normal;subst.
    eapply assignment_preserve_chained_stack_structure;eauto.
  - rename x1 into objname_t.
    rename x into chk_objdecl.
    red. 
    !intros.
    split.
    + !intros.
      unfold forbidden.
      !destruct h_forbid_m_m_sp_id_ofs_id.
      split.
      * red;!intros.
        red in neg_h_free_blck_m_sp_id_ofs_id.
        specialize (fun spb_id ofs_id0 => h_invis_sp__m_sp_id_ofs_id
                                            _ _ _ spb_id ofs_id0 heq_transl_variable heq_compute_chnk_id).
        specialize (h_invis_sp__m_sp_id_ofs_id spb_id ofs_id0).
        !assert (Cminor.eval_expr g sp e_chain m id_t (Values.Vptr spb_id ofs_id0)).
        { !assert (Cminor.eval_expr g sp e_chain m' id_t (Values.Vptr spb_id ofs_id0)).
          { eapply eval_expr_transl_variable_inv_locenv;eauto. }
          !inversion h_exec_stmt_locvarinit_Out_normal;subst.
          destruct objname_t_v;try discriminate.
          eapply wf_chain_load_var';auto;eauto.
          !functional inversion heq_transl_name;subst.
          !functional inversion heq_transl_variable0;subst.
          !!pose proof (h_nonul_ofs _ _ _ _ heq_transl_variable0).
          !assert (chained_stack_structure m (m'0 - m0) sp).
          { 
            (*rewrite heq_lvloftop_CE_lvl in heq_lvloftop_CE_m'0.*)
(*             inversion heq_lvloftop_CE_m'0;subst. *)
            eapply chained_stack_structure_le;eauto.
            !!assert (Datatypes.length CE = (S m'0)) by (eapply exact_level_top_lvl;eauto).
            rewrite heq_length.
            omega. }
          
          pose proof (chain_struct_build_loads_ofs _ _ _ h_chain_sp n _ _ _ _ h_CM_eval_expr_objname_t_objname_t_v) .
          subst;assumption. }
        specialize (h_invis_sp__m_sp_id_ofs_id h_CM_eval_expr_id_t0).
        assumption.

      * unfold is_free_block in *.
        !inversion h_exec_stmt_locvarinit_Out_normal.
        destruct objname_t_v;try discriminate.
        unfold Mem.storev in heq_storev_e_t_v_m'.
        intro abs.
        apply neg_h_free_blck_m_sp_id_ofs_id.
        intros perm. 
        intro abs2.
        apply (Mem.perm_store_1 _ _ _ _ _ _ heq_storev_e_t_v_m') in abs2.
        specialize (abs perm);contradiction.
    + !intros.
      unfold forbidden.
      !destruct h_forbid_m'_m'_sp_id_ofs_id.
      split.
      * red;!intros.
        red in h_invis_sp__m'_sp_id_ofs_id.
        specialize (fun spb_id ofs_id0 => h_invis_sp__m'_sp_id_ofs_id _ _ _ spb_id ofs_id0 heq_transl_variable heq_compute_chnk_id).
        specialize (h_invis_sp__m'_sp_id_ofs_id spb_id ofs_id0).
        !assert (Cminor.eval_expr g sp e_chain' m' id_t (Values.Vptr spb_id ofs_id0)).
        { !assert (Cminor.eval_expr g sp e_chain' m id_t (Values.Vptr spb_id ofs_id0)).
          { eapply eval_expr_transl_variable_inv_locenv;eauto. }
          !inversion h_exec_stmt_locvarinit_Out_normal;subst.
          destruct objname_t_v;try discriminate.
          assert (4 <= Int.unsigned i).
          { !functional inversion heq_transl_name;subst.
            !functional inversion heq_transl_variable0;subst.
            !!pose proof (h_nonul_ofs _ _ _ _ heq_transl_variable0).
            !assert (chained_stack_structure m (m'0 - m0) sp).
            { eapply chained_stack_structure_le;eauto.
              !!assert (Datatypes.length CE = (S m'0)) by (eapply exact_level_top_lvl;eauto).
              rewrite heq_length.
              omega. }
            pose proof (chain_struct_build_loads_ofs _ _ _ h_chain_sp n _ _ _ _ h_CM_eval_expr_objname_t_objname_t_v) .
            subst;assumption. }
          eapply wf_chain_load_var;auto;eauto.
          -- eapply wf_chain_load_aligned;eauto. }
        specialize (h_invis_sp__m'_sp_id_ofs_id h_CM_eval_expr_id_t0).
        assumption. 
      * unfold is_free_block in *.
        !inversion h_exec_stmt_locvarinit_Out_normal.
        destruct objname_t_v;try discriminate.
        unfold Mem.storev in heq_storev_e_t_v_m'.
        intro abs.
        apply neg_h_free_blck_m'_sp_id_ofs_id.
        intros perm. 
        intro abs2.
        apply (Mem.perm_store_2 _ _ _ _ _ _ heq_storev_e_t_v_m') in abs2.
        specialize (abs perm);contradiction.
  - !inversion h_exec_stmt_locvarinit_Out_normal.
    + eapply IHr0 with (m:=m1);eauto.
      * eapply IHr;eauto.
      * eapply chain_aligned;eauto.
        subst.
        eapply IHr;eauto.
    + elim hneq;auto.
  - !inversion h_exec_stmt_locvarinit_Out_normal.
    + rename m1 into m_mid.
      rename e1 into e_mid.
      apply unchange_forbidden_trans with (e2:=e_mid) (m2:=m_mid).
      * eapply IHr with (locvarinit:=x);eauto.
      * eapply IHr0 with (locvarinit:=x0);eauto.
      -- eapply IHr;eauto.
      -- eapply chain_aligned;eauto.
         subst.
         eapply IHr;eauto.
    + elim hneq;auto.
Qed.

Lemma init_locals_unchanged_on_subproof:
  forall decl st CE locvarinit,
    CompilEnv.exact_levelG CE ->
    stack_no_null_offset st CE ->
    init_locals st CE decl =: locvarinit ->
    forall astnum g proc_t sp e_chain m t2 e_postchain m' lvl,
      Datatypes.length CE = lvl -> 
      chained_stack_structure m lvl sp ->
      stack_localstack_aligned (Datatypes.length CE) e_chain g m sp -> 
      exec_stmt g proc_t sp e_chain m locvarinit t2 e_postchain m' Out_normal ->
      Mem.unchanged_on (forbidden st CE g astnum e_chain sp m m) m m'.
Proof.
  !intros.
  up_type.
  !!pose proof (exec_init_locals_preserve_forbidden_subproof
                  _ _ _ _ h_exct_lvlG_CE h_nonul_ofs heq_init_lcl_decl_locvarinit astnum _ proc_t
                  _ _ _ _ _ _ lvl heq_length h_chain_lvl_sp h_aligned_g_m h_exec_stmt_locvarinit_Out_normal).
  decomp h_and.
  revert locvarinit h_exct_lvlG_CE h_nonul_ofs heq_init_lcl_decl_locvarinit astnum g proc_t sp
         e_chain m t2 e_postchain m' h_aligned_g_m lvl heq_length h_exec_stmt_locvarinit_Out_normal
         h_unch_forbid_m_m' h_chain_lvl_sp h_chain_lvl_sp0.
  rewrite init_locals_ok.
  !!functional induction function_utils.init_locals st CE decl;try rewrite <- init_locals_ok in *;cbn;!intros;try discriminate.
  - !invclear heq_OK; inversion h_exec_stmt_locvarinit_Out_normal;subst. apply Mem.unchanged_on_refl.
  - !invclear heq_OK; inversion h_exec_stmt_locvarinit_Out_normal;subst; apply Mem.unchanged_on_refl.
  - rename x1 into objname_t.
    rename x into chk_objdecl.
    !invclear heq_OK.
    !invclear h_exec_stmt_locvarinit_Out_normal; eq_same_clear;up_type.
    unfold Mem.storev in heq_storev_e_t_v_m'.
    destruct objname_t_v ;try now discriminate.
    eapply Mem.store_unchanged_on;eauto;!intros.
    unfold forbidden.
    intros [abs1 abs2].
    red in abs1.
    cbn in heq_transl_name.
    setoid_rewrite <- transl_variable_astnum with (a:=astnum) in heq_transl_name;eauto.
    specialize (abs1 (object_name objdecl) objname_t chk_objdecl b i heq_transl_name heq_compute_chnk h_CM_eval_expr_objname_t_objname_t_v).
    !destruct abs1;try omega.
    apply hneq;auto.
  - !invclear heq_OK; inversion h_exec_stmt_locvarinit_Out_normal;subst; apply Mem.unchanged_on_refl.
  - !invclear h_exec_stmt_locvarinit_Out_normal; eq_same_clear;up_type.
    apply Mem.unchanged_on_refl.    
  - rename x into stmt1.
    rename x0 into stmt2.
    !invclear heq_OK.
    !invclear h_exec_stmt_locvarinit_Out_normal; eq_same_clear;up_type.
    rename m1 into m_mid.
    rename e1 into e_mid.
    !assert (chained_stack_structure m_mid lvl sp ∧ unchange_forbidden st CE g astnum e_chain e_mid sp m m_mid).
    { eapply exec_init_locals_preserve_forbidden_subproof with (locvarinit:=stmt1);eauto. }
    decomp h_and.
    !assert (chained_stack_structure m' lvl sp ∧ unchange_forbidden st CE g astnum e_mid e_postchain sp m_mid m').
    { eapply exec_init_locals_preserve_forbidden_subproof with (locvarinit:=stmt2);eauto.
      eapply chain_aligned;eauto.
      omega. }
    decomp h_and.
    apply trans_unchanged with m_mid;auto.
    + eapply IHr;eauto.
    + assert (Mem.unchanged_on (forbidden st CE g astnum e_mid sp m_mid m_mid) m_mid m').
      { eapply IHr0 with (locvarinit:= stmt2);eauto.
        eapply chain_aligned;eauto.
        omega. }
      red in h_unch_forbid_m_m_mid.
      eapply unchanged_on_iff;eauto.
       (red;!intros);(red;!intros).
      subst.
      apply h_unch_forbid_m_m_mid.
Qed.



Lemma init_params_preserves_structure:
  forall lparams st CE initparams,
    CompilEnv.exact_levelG CE ->
    stack_no_null_offset st CE ->
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
    stack_no_null_offset st CE ->
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
  !intros.
  rewrite <- build_compilenv_ok  in heq_build_compilenv.
  functional inversion heq_build_compilenv.
  constructor;auto.
Qed.  



Lemma compute_size_pos : forall st subtyp_mrk x, spark2Cminor.compute_size st subtyp_mrk =: x -> (x>0).
Proof.
  !intros.
  rewrite <- compute_size_ok in *.
  !functional inversion heq_cmpt_size_subtyp_mrk.
  apply size_chunk_pos.
Qed.

(* Lemma compute_size_pos stbl t : forall x, compute_size stbl t =: x -> x > 0.
Proof.
  !intros.
  unfold compute_size in *.
  (* functional inbversion would be better *)
  destruct (compute_chnk_of_type stbl t); cbv in  *;try discriminate.
  destruct m;cbv in *;try inversion heq_cmpt_size_t;auto.
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
  !!intros until lparams.
  !functional induction (function_utils.build_frame_lparams st stosz lparams);cbn;!intros;subst.
  - !invclear heq_OK.
    split;intros.
    + cbn. reflexivity.
    + inversion H;subst;eauto 5.
  - rewrite heq_add_to_fr_nme in heq_bind.
    cbn [bind] in *.
    specialize (IHr _ _ heq_bind).
    rewrite function_utils.add_to_frame_ok in *.
    !functional inversion heq_add_to_fr_nme;subst;cbn.
    cbn in IHr.
    destruct IHr as [IHr1 IHr3].
    subst new_size.
    subst new_cenv.
    split.
    + !!assert (x0>0) by (eapply compute_size_pos;eauto).
      omega.
    + !!intros * ? * h_forall **. 
      inversion heq_pair;subst.
      specialize (IHr3 ((nme, sz0) :: stoszchainparam) (sz0 + x0) eq_refl k).
      apply IHr3 with (nme:=nme0);auto.
      * !intros.
        cbn in heq_CEfetches_nme1.
        destruct (nme1 =? nme)%nat.
        -- !invclear heq_CEfetches_nme1;auto.
        -- inversion heq_pair;subst;eauto.
      * assert (x0>0) by (eapply compute_size_pos;eauto).
        split; try omega.
        rewrite Z.geb_leb in heq_geb.
        apply Z.leb_gt.
        assumption.
  - rewrite heq_add_to_fr_ERR_nme in heq_bind.
    cbn in heq_bind.
    discriminate.
Qed.

Lemma build_frame_lparams_mon'': forall st stosz lparams sto' sz',
    build_frame_lparams st stosz lparams =: (sto',sz') ->
    snd stosz <= Int.modulus -> 
    sz' <= Int.modulus.
Proof.
  !!intros until lparams.
  !functional induction (function_utils.build_frame_lparams st stosz lparams);cbn;!intros;subst.
  - !invclear heq_OK.
    cbn in *.
    assumption.
  - rewrite heq_add_to_fr_nme in heq_bind.
    cbn [bind] in *.
    specialize (IHr _ _ heq_bind).
    rewrite function_utils.add_to_frame_ok in *.
    !functional inversion heq_add_to_fr_nme;subst;cbn.
    subst new_size.
    subst new_cenv.
    cbn in IHr.
    apply IHr.
    rewrite Z.geb_leb in heq_geb.
    apply Z.leb_gt in heq_geb.
    omega.
  - rewrite heq_add_to_fr_ERR_nme in heq_bind.
    cbn in heq_bind.
    discriminate.
Qed.
(* build_frame_lparams return a non overflowed store, but the size may = to Int.modulus.
   So that next addition will overflow *)
Lemma build_frame_lparams_mon': forall st stosz lparams sto' sz',
    build_frame_lparams st stosz lparams =: (sto',sz') ->
    snd stosz <= Int.modulus -> 
    snd stosz<=sz'<= Int.modulus
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
  !!intros until lparams.
  !functional induction (function_utils.build_frame_lparams st stosz lparams);cbn;!intros;subst.
  - !invclear heq_OK.
    split;[split|intros].
    + cbn. reflexivity.
    + cbn in *.
      assumption.
    + inversion H;subst;eauto 5.
  - rewrite heq_add_to_fr_nme in heq_bind.
    cbn [bind] in *.
    specialize (IHr _ _ heq_bind).
    rewrite function_utils.add_to_frame_ok in *.
    !functional inversion heq_add_to_fr_nme;subst;cbn.
    !assert (x0 >0).
    { eapply compute_size_pos;eauto. }
    cbn in IHr.
    !assert (new_size <= Int.modulus).
    { rewrite Z.geb_leb in heq_geb.
      apply Z.leb_gt in heq_geb.
      omega. }
    specialize (IHr h_le_new_size_modulus).
    destruct IHr as [[IHr1IHr2] IHr3].
    subst new_size.
    subst new_cenv.
    split;[split|!intros].
    + omega.
    + assumption.
    + inversion heq_pair;subst.
      specialize (IHr3 ((nme, sz0) :: stoszchainparam) (sz0 + x0) eq_refl k).
      apply IHr3 with (nme:=nme0);auto.
      * !intros.
        cbn in heq_CEfetches_nme1.
        destruct (nme1 =? nme)%nat.
        -- !invclear heq_CEfetches_nme1;split;auto.
           omega.
        -- specialize (H1 nme1 x heq_CEfetches_nme1).
           !destruct H1;auto.
           split;auto.
           omega.
      * omega.
  - rewrite heq_add_to_fr_ERR_nme in heq_bind.
    cbn in heq_bind.
    discriminate.
Qed.

Lemma build_frame_decl_mon_sz: forall st decl stosz stosz',
    build_frame_decl st stosz decl =: stosz' -> 
    snd stosz <= snd stosz'.
Proof.
  !!intros until stosz.
  rewrite build_frame_decl_ok.
  !functional induction (function_utils.build_frame_decl st stosz decl);!intros ;try discriminate.
  all: try rewrite <- build_frame_decl_ok in *.
  - inversion heq_OK;reflexivity.
  - !invclear heq_OK.
    cbn.
    !!pose proof compute_size_pos _ _ _ heq_cmpt_size.
    omega.
  - specialize (IHr0 _ heq_build_frame_decl0).
    specialize (IHr _ heq_build_frame_decl).
    etransitivity;eauto.
Qed.

Lemma build_frame_decl_mon: forall st stosz lparams sto' sz',
    spark2Cminor.build_frame_decl st stosz lparams =: (sto',sz') ->
    snd stosz <= Int.modulus -> 
    snd stosz<=sz'<= Int.modulus
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
  !!intros until lparams.
  rewrite build_frame_decl_ok.
  !functional induction (function_utils.build_frame_decl st stosz lparams);!intros ;try discriminate.
  all: try rewrite <- build_frame_decl_ok in *.
  - split;[split|].
    + inversion heq_OK;reflexivity.
    + inversion heq_OK;cbn in *;omega.
    + !invclear heq_OK;subst;cbn in *.
      !intros.
      !invclear heq_pair.
      eauto.
  - !!pose proof compute_size_pos _ _ _ heq_cmpt_size.
    split;[split|].
    + !invclear heq_OK.
      cbn.
      omega.
    + !invclear heq_OK;cbn in *.
      destruct (Z.geb_spec (sz + x) Int.modulus);try discriminate;omega.
    + !invclear heq_OK;subst;cbn in *.
      !intros.
      !invclear heq_pair.
      !destruct (Nat.eqb_spec nme (object_name objdecl));subst.
      * !invclear heq_Some.
        omega.
      * specialize (H0 _ _ heq_Some).
        omega.
  - destruct x.
    specialize (IHr _ _ heq_build_frame_decl h_le).
    decomp IHr.
    rename H0 into IHr_3.
    specialize (IHr0 _ _ heq_build_frame_decl0 h_le_z_modulus).
    decomp IHr0.
    rename H0 into IHr0_3.
    split;[split|].
    + cbn in *;omega.
    + assumption.
    + !intros.
      rename H0 into h_lelt.
      !invclear heq_pair;subst.
      cbn in*.
      specialize (IHr_3 _ _ eq_refl _ h_lelt h_le_k_sz0).
      rename z into sz.
      !!assert (k<=sz) by omega.
      specialize (IHr0_3 _ _ eq_refl k IHr_3 h_le_k_sz _ _ heq_CEfetches_nme_sto').
      assumption.
Qed.


Lemma build_compilenv_stack_no_null_offset:
  ∀ (st : symboltable) (CE : CompilEnv.state) (proc_lvl : level) (lparams : list paramSpec) 
    (decl : decl) (CE' : compilenv) (sz : Z),
    CompilEnv.exact_levelG CE →
    stack_no_null_offset st CE →
    build_compilenv st CE proc_lvl lparams decl =: (CE', sz) →
    stack_no_null_offset st CE'.
Proof.
  !intros.
  rewrite <- build_compilenv_ok  in heq_build_compilenv.
  !functional inversion heq_build_compilenv;subst; rewrite build_compilenv_ok in *.
  rewrite function_utils.build_frame_decl_ok in heq_build_frame_decl.
  !destruct x.
  subst stoszchainparam.
  pose proof build_frame_lparams_mon' _ _ _ _ _ heq_bld_frm_lparams as h_bld_frm.
  cbn in h_bld_frm.
  !!assert (4 <= Int.modulus). {
    vm_compute.
    intro abs;discriminate. }
   specialize (h_bld_frm h_le).
  destruct h_bld_frm as [h_bld_frm1 h_bld_frm2].

  specialize (h_bld_frm2 [] 4  eq_refl 4).
  !!assert (h_ftch_nil: ∀ (nme : idnum) (x : CompilEnv.V), CompilEnv.fetches nme [] = Some x → 4 <= x < 4).
  { !intros.
    functional inversion heq_CEfetches_nme. }
  !!assert (4 <= 4) by omega.
  specialize (h_bld_frm2 h_ftch_nil h_le0).
  pose proof build_frame_decl_mon _ _ _ _ _ heq_build_frame_decl as h_bld_decl.
  cbn in h_bld_decl.
  !destruct h_bld_frm1.
  specialize (h_bld_decl h_le_z_modulus).
  destruct h_bld_decl as [h_le_z' h_bld_decl].
  cbn in h_le_z'.
  specialize (h_bld_decl s z eq_refl 4 h_bld_frm2 h_le1).
  red;!intros.
(*   unfold transl_variable in heq_transl_variable. *)
(*   cbn in heq_transl_variable. *)
  destruct (CompilEnv.fetches nme x0) eqn:h1; destruct (CompilEnv.resides nme x0) eqn:h2; try discriminate;  up_type.
  - unfold transl_variable in heq_transl_variable.
    cbn in heq_transl_variable.
    rewrite h1, h2 in heq_transl_variable.
    specialize (h_bld_decl _ _ h1).
    !destruct h_bld_decl.
    !destruct h_le_z'.

    assert (Int.unsigned (Int.repr t)=Int.unsigned (Int.repr δ_id)). {
      inversion heq_transl_variable.
      destruct (Int.repr t) eqn:heq_t;destruct (Int.repr δ_id) eqn:heq_δ_id;auto. }
    rewrite <- H.
    rewrite Int.unsigned_repr.
    * omega.
    * split;try omega.
      unfold Int.max_unsigned.
      omega.
  - !assert (CompilEnv.resides nme x0 = true). {
      apply (CompilEnv.fetches_resides nme x0).
      exists t;auto. }
    rewrite h2 in heq_resides;discriminate.
  - !assert (exists t, CompilEnv.fetches nme x0 = Some t). {
      apply (CompilEnv.fetches_resides nme x0).
      assumption. }
    !!decompose [ex] h_ex.
    rewrite h1 in heq_CEfetches_nme_x0;discriminate.

  - red in h_nonul_ofs.
    !assert (exists top, CompilEnv.level_of_top CE = Some top /\ Datatypes.length CE = S top).
    { destruct (CompilEnv.level_of_top CE) eqn:heq_top.
      - exists s0;split;auto.
        eapply exact_level_top_lvl;eauto.
      - !functional inversion heq_transl_variable.
        cbn in heq_CEframeG_nme.
        rewrite h2 in heq_CEframeG_nme.
        functional inversion heq_CEframeG_nme.
        + subst CE.
          cbn in heq_top.
          destruct f.
          inversion heq_top.
        + subst CE.
          cbn in heq_top.
          destruct f.
          inversion heq_top. }
    decomp h_ex.
    rename top into top_CE.
    autorename heq_lvloftop_CE_top.
    !!enough(exists δ_lvl', transl_variable st CE a nme =: build_loads δ_lvl' δ_id).
    { decomp h_ex.
      eapply h_nonul_ofs;eauto. }
    unfold transl_variable in heq_transl_variable.
    cbn in heq_transl_variable.
    rewrite h1, h2 in heq_transl_variable. 
    cbn.
    unfold transl_variable.
    cbn.
    rewrite heq_lvloftop_CE_top_CE.
    unfold scope_lvl in heq_transl_variable.
    rewrite heq_length in heq_transl_variable.
    !!destruct (CompilEnv.fetchG nme CE) eqn:?;destruct (CompilEnv.frameG nme CE) eqn:?;cbn in * ;eauto.
    destruct f;cbn in *.
    apply OK_inv in heq_transl_variable.
    !!pose proof build_loads_inj_2 _ _ _ _ heq_transl_variable.
    decomp h_and.
    exists (top_CE - s0)%nat.
    f_equal.
    unfold build_loads.
    rewrite heq_repr.
    reflexivity.
Qed.
(** Consequence of chained structure: build_load returns always a pointeur *)
Lemma build_loads_Vptr : forall lvl_nme lvl g spb ofs locenv m δ_nme nme_t nme_t_v,
    stack_localstack_aligned lvl locenv g m (Values.Vptr spb ofs) ->
    (lvl_nme < lvl)%nat ->
    build_loads lvl_nme δ_nme = nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t nme_t_v ->
    ∃ nme_block nme_ofst, nme_t_v = (Values.Vptr nme_block nme_ofst).
Proof.
  unfold build_loads.
  !intros; subst.
  !invclear h_CM_eval_expr_nme_t_nme_t_v.
  cbn in h_eval_binop_Oadd_v1_v2.
  !invclear h_eval_binop_Oadd_v1_v2.
  red in h_aligned_g_m.
  !destruct (h_aligned_g_m lvl_nme);try omega.
  subst_det_addrstack_zero.
  !invclear h_CM_eval_expr_v2.
  cbn in *.
  !invclear h_eval_constant.
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
  !intros.
  !functional inversion heq_transl_variable.
  eapply build_loads_Vptr;eauto.
  erewrite exact_lvlG_lgth with (lvl:=m').
  + omega.
  + apply h_inv_comp_CE_stbl.
  + assumption.
Qed.


Definition all_addr_no_overflow_localframe sto := 
  ∀ (id : idnum) (δ : CompilEnv.V),CompilEnv.fetch id sto = Some δ → 0 <= δ ∧ δ < Int.modulus.

Ltac rename_hyp_overf h th :=
  match th with
    all_addr_no_overflow_localframe _ => fresh "h_no_overf_localf"
  | _ => rename_hyp_forbid_unch h th
  end.

Ltac rename_sparkprf ::= rename_hyp_overf.

Lemma all_addr_no_overflow_fetch_OK :
  forall sto CE,
    all_addr_no_overflow_localframe sto
    -> all_addr_no_overflow CE -> all_addr_no_overflow (sto :: CE).
Proof.
  intros sto CE H H0.
  red.
  !intros.
  cbn in heq_CEfetchG_id.
  !destruct (CompilEnv.fetch id sto) !eqn:?.
  - !invclear heq_CEfetchG_id.
    eapply H;eauto.
  - eapply H0;eauto.
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
  rewrite build_frame_lparams_ok.
  !functional induction (function_utils.build_frame_lparams st locfrmZ prmprof);!intros;subst;try discriminate.
  - !invclear heq_OK.
    split;assumption.
  - rewrite function_utils.add_to_frame_ok in heq_add_to_fr_nme.
    !functional inversion heq_add_to_fr_nme;subst.
    rewrite <- function_utils.add_to_frame_ok in *.
    assert (x0 > 0).
    { unfold compute_size in heq_cmpt_size_subtyp_mrk.
      destruct compute_chnk_of_type;try discriminate.
      cbn in heq_cmpt_size_subtyp_mrk.
      inversion heq_cmpt_size_subtyp_mrk.
      apply size_chunk_pos;assumption. }
    unfold new_size, new_cenv in *.
    eapply IHr;eauto;try omega.
    red.
    !!intros.
    cbn in heq_CEfetch_id.
    !destruct (id =? nme)%nat.
    + !invclear heq_CEfetch_id.
      generalize (Zge_cases (δ + x0)  Int.modulus).
      intro h_ge.
      rewrite heq_geb in h_ge.
      split.
      * omega.
      * omega.
    + unfold all_addr_no_overflow_localframe in h_no_overf_localf.
      eapply h_no_overf_localf.
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
  rewrite build_frame_decl_ok in *.
  !!functional induction (function_utils.build_frame_decl st locfrmZ decl);!intros;subst ;try discriminate;
  try rewrite <- build_frame_decl_ok in *.
  - split.
    + !invclear heq_OK.
      !invclear heq_pair.
      assumption.
    + !invclear heq_OK.
      !invclear heq_pair.
      assumption.
  - rename x into size.
    !invclear heq_OK.
    !invclear heq_pair.
    assert (size > 0).
    { unfold compute_size in heq_cmpt_size.
      destruct compute_chnk_of_type;try discriminate.
      cbn in heq_cmpt_size.
      inversion heq_cmpt_size.
      apply size_chunk_pos;assumption. }

    split.
    + unfold all_addr_no_overflow_localframe.
      !intros.
      cbn in heq_CEfetch_id.
      
      !destruct (id =? (object_name objdecl))%nat.
      * !invclear heq_CEfetch_id.
        generalize (Zge_cases (δ + size)  Int.modulus).
        intro h_ge.
        rewrite heq_geb in h_ge.
        split.
        -- omega.
        -- omega.
      * unfold all_addr_no_overflow_localframe in h_no_overf_localf.
        eapply h_no_overf_localf.
        eassumption.
    + omega.
  - rename x into size.
    up_type.
    !invclear heq_pair.
    destruct size.
    specialize (IHr _ _ eq_refl lvl s z h_ge_sz0_Z0 heq_build_frame_decl h_no_overf_localf).
    split.
    + destruct IHr as [IHr1 IHr2].
      eapply IHr0;eauto.
    + destruct IHr as [IHr1 IHr2].
      eapply IHr0;eauto.
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
  !functional induction (build_frame_decl_2 st locfrmZ decl);!intros;subst;try discriminate
  ; try rewrite -> build_frame_decl_ok in *.
*)



Lemma build_frame_lparams_preserve_increasing_order:
  forall st init prmprof lvl fr z,
    build_frame_lparams st (init,z) prmprof =: (fr,lvl)
    -> Forall (gt_x_snd_y z) init
    -> increasing_order init
    -> increasing_order fr ∧ Forall (gt_x_snd_y lvl) fr.
Proof.
  !!intros until 0.
  remember (init,z) as initz.
  revert init z Heqinitz.
  rewrite build_frame_lparams_ok.
  !functional induction (function_utils.build_frame_lparams st initz prmprof);!intros;subst;try discriminate;try rewrite <- build_frame_lparams_ok in *.
  - inversion heq_OK;subst;auto.
  - rewrite add_to_frame_ok in heq_add_to_fr_nme.
    !functional inversion heq_add_to_fr_nme;subst.
    rewrite <- add_to_frame_ok in *.
    unfold new_cenv,new_size in *.
    clear new_cenv new_size.
    specialize (IHr _ _ eq_refl).
    apply IHr.
    + assumption.
    + !assert (x0>0).
      { destruct subtyp_mrk;cbn in heq_cmpt_size_subtyp_mrk;inversion heq_cmpt_size_subtyp_mrk;omega.  }
      constructor;auto.
      * unfold gt_x_snd_y;cbn;omega.
      * eapply Forall_impl with (P:= gt_x_snd_y z);auto.
        !intros.
        unfold gt_x_snd_y in *;cbn in *.
        omega.
    + constructor;auto.
Qed.



Lemma build_frame_decl_preserve_increasing_order:
  forall st init decl lvl fr z,
    build_frame_decl st (init,z) decl =: (fr,lvl)
    -> Forall (gt_x_snd_y z) init
    -> increasing_order init
    -> increasing_order fr ∧ Forall (gt_x_snd_y lvl) fr.
Proof.
  !!intros until 0.
  remember (init,z) as initz.
  revert init z Heqinitz lvl fr.
  rewrite build_frame_decl_ok.
  !functional induction (function_utils.build_frame_decl st initz decl);!intros;subst;try discriminate;
    try rewrite <- build_frame_decl_ok in *.
  - inversion heq_OK;subst;auto.
    inversion heq_pair;subst;auto.
  - !invclear heq_OK;subst.
    !invclear heq_pair;subst.
    split.
    + constructor.
      * assumption.
      * unfold gt_snd.
        simpl.
        change (Forall (gt_x_snd_y z) init).
        assumption.
    + constructor.
      * unfold gt_snd;cbn.
        assert (h:=compute_size_pos _ _ _ heq_cmpt_size).
        red. simpl.
        omega.
      * apply Forall_forall.
        !intros.
        eapply Forall_forall in h_forall_init;eauto.
        red;simpl.
        red in h_forall_init;simpl in *.
        assert (h:=compute_size_pos _ _ _ heq_cmpt_size).
        omega.        
  - destruct x.
    !destruct (IHr init z heq_pair _ _ heq_build_frame_decl h_forall_init h_incr_order_init); clear IHr.
    !destruct (IHr0 s z0 eq_refl _ _ heq_build_frame_decl0 h_forall_s h_incr_order_s).
    split;assumption.
Qed.


Lemma build_frame_lparams_mon_sz: forall st params stosz stosz',
    build_frame_lparams st stosz params =: stosz' -> 
    snd stosz <= snd stosz'.
Proof.
  !!intros until stosz.
  rewrite build_frame_lparams_ok.
  !functional induction (function_utils.build_frame_lparams st stosz params);!intros.
  all: try rewrite <- build_frame_lparams_ok in *.
  - inversion heq_OK.
    reflexivity.
  - specialize (IHr stosz' heq_build_frame_lparams).
    rewrite add_to_frame_ok in heq_add_to_fr_nme.
    !functional inversion heq_add_to_fr_nme;subst;cbn in *.
    pose proof compute_size_pos _ _ _ heq_cmpt_size_subtyp_mrk.
    unfold new_size in *.
    omega.
  - discriminate.
Qed.




Lemma build_compilenv_preserve_invariant_compile:
  forall st CE pb_lvl prmprof pdeclpart CE' stcksize,
    build_compilenv st CE pb_lvl prmprof pdeclpart =: (CE', stcksize)
    -> invariant_compile CE st
    -> invariant_compile CE' st.
Proof.
  !!(intros until 1).
  rewrite <- build_compilenv_ok in heq_build_compilenv.
  !!(functional inversion heq_build_compilenv;subst;intro; rewrite -> ?build_compilenv_ok in *;clear heq_build_compilenv).
  split;eauto.
  + constructor.
    eauto.
  + constructor.
    * red.
      cbn.
      destruct x.
      destruct (build_frame_decl_preserve_increasing_order _ _ _ _ _ _ heq_build_frame_decl);auto.
      -- destruct (build_frame_lparams_preserve_increasing_order _ _ _ _ _ _ heq_bld_frm_prmprof);auto.
         constructor;cbn in *;auto.
      -- destruct (build_frame_lparams_preserve_increasing_order _ _ _ _ _ _ heq_bld_frm_prmprof);auto.
         constructor;cbn in *;auto.
    * eapply (ci_increasing_ids h_inv_comp_CE_st).
  + apply all_addr_no_overflow_fetch_OK;eauto.
    destruct x;unfold stoszchainparam in *.
    eapply (build_frame_decl_preserve_no_overflow st pdeclpart s z (Datatypes.length CE) x0 stcksize).
    -- eapply (build_frame_lparams_preserve_pos_addr st prmprof) with (lvl:=0%nat);eauto; try omega.
       red. cbn in *. !intros.
       discriminate.
    -- assumption.
    -- eapply (build_frame_lparams_preserve_no_overflow st prmprof);eauto; try omega.
       red. cbn. !intros.
       discriminate.
  + unfold CompilEnv.NoDup in *.
    !intros.
    cbn in heq_CEframeG_nme.
    destruct (CompilEnv.resides nme x0) eqn:hresid.
    * admit. (* spark typing, no name collision intra frame *)
    * !!pose proof (ce_nodup_CE h_inv_comp_CE_st).
      red in h_CEnodup_CE.
      eapply h_CEnodup_CE;eauto.
  + unfold CompilEnv.NoDup_G in *.
    !intros.
    cbn in heq_CEframeG_nme.
    destruct (CompilEnv.resides nme x0) eqn:hresid.
    * !invclear heq_CEframeG_nme.
      !inversion h_CEcut.
      -- cbn in h_lt;exfalso;omega.
      -- clear H1.
         admit. (* spark typing no name collision inter frame *)
    * !!pose proof (ce_nodup_G_CE h_inv_comp_CE_st).
      !inversion h_CEcut.
      -- cbn in *.
         !assert (CompilEnv.exact_levelG CE).
         { apply h_inv_comp_CE_st. }         
         pose proof (CompilEnv.exact_levelG_lgth _ _ _ _ h_exct_lvlG_CE heq_CEframeG_nme).
         exfalso.
         subst scope_lvl.
         omega.
      -- eapply h_CEnodupGCE;eauto.
Admitted.

Lemma add_to_frame_sz: forall stbl fram_sz parname parsubtype p sz,
    spark2Cminor.add_to_frame stbl fram_sz parname parsubtype =: p
    -> spark2Cminor.compute_size stbl parsubtype = Errors.OK sz
    -> snd p = snd fram_sz + sz.
Proof.
  !!intros until 1.
  rewrite add_to_frame_ok in heq_add_to_fr_parname.
  functional inversion heq_add_to_fr_parname
  ;rewrite ?add_to_frame_ok in *
  ;subst;!intros.
  subst new_size.
  subst new_cenv.
  rewrite H1 in heq_cmpt_size_parsubtype.
  inversion heq_cmpt_size_parsubtype.
  subst.
  simpl.
  reflexivity.
Qed.


Lemma add_to_frame_correct: forall stbl fram_sz parname parsubtype p othername,
    spark2Cminor.add_to_frame stbl fram_sz parname parsubtype =: p
    -> CompilEnv.resides othername (fst fram_sz) = true
    -> CompilEnv.resides othername (fst p) = true.
Proof.
  !!intros until 1.
  rewrite add_to_frame_ok in heq_add_to_fr_parname.
  functional inversion heq_add_to_fr_parname
  ;rewrite <- ?add_to_frame_ok in *
  ;subst;!intros.
  subst new_size.
  subst new_cenv.
  simpl.
  destruct (othername =? parname)%nat eqn:heq;auto.
Qed.

Lemma add_to_frame_correct2: forall stbl fram_sz parname parsubtype p,
    spark2Cminor.add_to_frame stbl fram_sz parname parsubtype =: p
    -> CompilEnv.resides parname (fst p) = true.
Proof.
  !!intros until 1.
  rewrite add_to_frame_ok in heq_add_to_fr_parname.
  functional inversion heq_add_to_fr_parname
  ;rewrite <- ?add_to_frame_ok in *
  ;subst;!intros.
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
  !!intros until 1.
  rewrite add_to_frame_ok in heq_add_to_fr_parname.
  functional inversion heq_add_to_fr_parname
  ;rewrite <- ?add_to_frame_ok in *
  ;subst;!intros.
  subst new_size.
  subst new_cenv.
  simpl.
  decomp h_and.
  simpl in heq_resides.
  rewrite <- Nat.eqb_neq in hneq.
  rewrite hneq in heq_resides.
  assumption.
Qed.


Lemma build_frame_lparams_correct: forall lparam stbl fram_sz res,
    build_frame_lparams stbl fram_sz lparam  =: res
    -> forall x, (List.In x lparam ∨ CompilEnv.resides (parameter_name x) (fst fram_sz) = true)
                 -> CompilEnv.resides (parameter_name x) (fst res) = true.
Proof.
  !!intros until fram_sz.
  rewrite function_utils.build_frame_lparams_ok.
  !!functional induction (function_utils.build_frame_lparams stbl fram_sz lparam); try discriminate;
  try rewrite <- function_utils.build_frame_lparams_ok;!intros.
  - !destruct h_or.
    + inversion h_in_x.
    + simpl in *.
      !invclear heq_OK.
      assumption.
  - remember {| parameter_astnum := _x; parameter_name := nme; parameter_subtype_mark := subtyp_mrk; parameter_mode := _x0 |}  as p.
    decomp h_or.
    + destruct h_in_x0.
      * subst.
        eapply IHr;eauto.
        right.
        simpl.
        eapply add_to_frame_correct2;eauto.
      * eapply IHr;eauto.
    + eapply IHr;eauto.
      right.
      eapply add_to_frame_correct;eauto.
Qed.

Lemma build_frame_lparams_correct_rev: forall lparam stbl fram_sz res,
    build_frame_lparams stbl fram_sz lparam  =: res
    -> forall nme, CompilEnv.resides nme (fst res) = true
                 -> ((exists x,List.In x lparam ∧ (parameter_name x) = nme)
                     ∨ CompilEnv.resides nme (fst fram_sz) = true).
Proof.
  !!intros until fram_sz.
  rewrite function_utils.build_frame_lparams_ok.
  !!(functional induction (function_utils.build_frame_lparams stbl fram_sz lparam); try discriminate;
  try rewrite <- ?function_utils.build_frame_lparams_ok in *;intros).
  - inversion heq_OK. 
    right;assumption.
  - up_type.
    remember {| parameter_astnum := _x; parameter_name := nme; parameter_subtype_mark := subtyp_mrk; parameter_mode := _x0 |}  as p.
    specialize (IHr _ heq_bld_frm_lparam' _  heq_resides).
    !!decompose [ex or and] IHr.
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
  !!intros.
  rewrite add_to_frame_ok in heq_add_to_fr_parname.
  functional inversion heq_add_to_fr_parname
  ;rewrite <- ?add_to_frame_ok in *
  ;subst;!intros.
  subst.
  simpl.
  destruct (othername =? parname)%nat eqn:heq'.
  - apply beq_nat_true in heq'.
    subst.
    rewrite heq_CEfetches_parname in heq_CEfetches_othername;discriminate.
  - assumption.
Qed.

Lemma add_to_frame_correct4: forall stbl fram_sz parname parsubtype new_fram_sz,
    increasing_order (fst fram_sz)
    -> upper_bound (fst fram_sz) (snd fram_sz)
    -> add_to_frame stbl fram_sz parname parsubtype =: new_fram_sz
    -> increasing_order (fst new_fram_sz) ∧ upper_bound (fst new_fram_sz) (snd new_fram_sz)
       ∧ CompilEnv.fetches parname (fst new_fram_sz) = Some (snd fram_sz).
Proof.
  !!intros.
  rewrite add_to_frame_ok in heq_add_to_fr_parname.
  !! (functional inversion heq_add_to_fr_parname
      ;rewrite <- ?add_to_frame_ok in *
      ;subst;intros).
  subst new_size.
  subst new_cenv.
  simpl.
  split;[|split].
  - red.
    apply Sorted_StronglySorted.
    + red.
      unfold gt_snd.
      !!intros [a a'] [b b'] [c c'] ? ?;simpl in *.
      transitivity b';auto.
    + apply Sorted_LocallySorted_iff.
      destruct cenv.
      * constructor 2.
      * constructor 3.
        -- apply Sorted_LocallySorted_iff.
           apply StronglySorted_Sorted.
           apply h_incr_order.
        -- destruct p;simpl.
           unfold gt_snd.
           simpl snd at 1.
           eapply h_upb with i;simpl;eauto.
           rewrite Nat.eqb_refl;reflexivity.
  - !!intros nme nme_ofs ?;simpl in *.
    !!assert (x>0) by (unshelve eapply compute_size_pos;eauto).
    !destruct (nme =? parname)%nat.
    * inversion heq_CEfetches_nme;subst.
      omega.
    * specialize (h_upb _ _ heq_CEfetches_nme).
      omega.
  - now rewrite <- beq_nat_refl.
Qed.

Lemma add_to_frame_correct_none: forall stbl fram_sz parname parsubtype new_fr new_sz othername,
    CompilEnv.fetches othername (fst fram_sz) = None
    -> othername <> parname
    -> add_to_frame stbl fram_sz parname parsubtype =: (new_fr, new_sz)
    -> CompilEnv.fetches othername new_fr = None.
Proof.
  !!intros.
  rewrite add_to_frame_ok in heq_add_to_fr_parname.
  !!(functional inversion heq_add_to_fr_parname
     ;rewrite <- ?add_to_frame_ok in *
     ;subst;intros;subst).
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
  !!intros.
  rewrite add_to_frame_ok in heq_add_to_fr_parameter_name.
  functional inversion heq_add_to_fr_parameter_name
  ;rewrite <- ?add_to_frame_ok in *
  ;subst;!intros.
  simpl.
  subst.
  decomp h_and.
  simpl in heq_CEfetches_othername_new_cenv.
  rewrite <- Nat.eqb_neq in hneq.
  rewrite hneq in heq_CEfetches_othername_new_cenv.
  assumption.  
Qed.

Lemma add_to_frame_correct_none_rev: forall stbl fram_sz parameter_name parsubtype new_fr new_sz othername,
    add_to_frame stbl fram_sz parameter_name parsubtype =: (new_fr, new_sz)
    -> CompilEnv.fetches othername new_fr = None
    -> CompilEnv.fetches othername (fst fram_sz) = None.
Proof.
  !!intros.
  rewrite add_to_frame_ok in heq_add_to_fr_parameter_name.
  functional inversion heq_add_to_fr_parameter_name
  ;rewrite <- ?add_to_frame_ok in *
  ;subst;!intros.
  simpl.
  subst.
  functional inversion heq_CEfetches_othername_new_fr.
  assumption.
Qed.


Definition fresh_params lparam (fr:localframe) :=
  Forall (fun prm => CompilEnv.fetches (parameter_name prm) fr = None) lparam.



(* TODO: move this elsewhere *)
Ltac rename_hyp_list h th :=
  match th with
    | fresh_params ?l ?fr => fresh "h_fresh_prms_" l "_" fr
    | fresh_params ?l _ => fresh "h_fresh_prms_" l
    | fresh_params _ _ => fresh "h_fresh_prms"
    | _ => rename_hyp_overf h th
  end.

Ltac rename_sparkprf ::= rename_hyp_list.

Ltac fold_pairs H :=
  match type of H with
    context C [(fst ?x,snd ?x)] => replace (fst x,snd x) with x in H; [ | destruct x;reflexivity]
  end.

Lemma add_to_frame_fresh: forall stbl fram_sz lparam' subtyp_mrk prm x,
    fresh_params (prm::lparam') (fst fram_sz)
    -> NoDupA eq_param_name (prm::lparam')
    -> add_to_frame stbl fram_sz (parameter_name prm) subtyp_mrk =: x
    -> fresh_params lparam' (fst x).
Proof.
  !!intros until prm. 
  remember (parameter_name prm) as prn_nme.
  rewrite add_to_frame_ok.
  !!(functional induction (function_utils.add_to_frame stbl fram_sz prn_nme subtyp_mrk);intros;try discriminate).
  !invclear heq_OK.
  red. apply Forall_forall.
  !!intros prm0 ?.
  !assert (parameter_name prm0 <> parameter_name prm).
  { intro abs.
    !inversion h_NoDupA.
    apply neg_h_inA_prm_lparam'.
    rewrite InA_alt.
    exists prm0.
    split;auto.
    red.
    symmetry;auto. }
  simpl.
  rewrite <- Nat.eqb_neq in hneq.
  rewrite hneq.
  simpl in hneq.
  unfold fresh_params in h_fresh_prms.
  rewrite Forall_forall in h_fresh_prms.
  apply h_fresh_prms.
  simpl.
  right;assumption.
Qed.

Lemma build_frame_lparams_nodup: forall stbl lparam fram_sz res,
    increasing_order (fst fram_sz)
    -> NoDupA eq_param_name lparam    
    -> fresh_params lparam (fst fram_sz)
    -> upper_bound (fst fram_sz) (snd fram_sz)
    -> build_frame_lparams stbl fram_sz lparam = Errors.OK res
    -> NoDupA eq_fst_idnum (fst fram_sz)
    -> NoDupA eq_fst_idnum (fst res).
Proof.
  !!intros until fram_sz.
  rewrite build_frame_lparams_ok.
  !!functional induction (function_utils.build_frame_lparams stbl fram_sz lparam);simpl;!intros;
    try discriminate;try rewrite <- ?build_frame_lparams_ok in *.
  - !invclear heq_OK.
    assumption.
  - apply IHr.
    + assert (h:=build_frame_lparams_preserve_increasing_order stbl (fst x) lparam' (snd res) (fst res) (snd x));auto.      
      repeat fold_pairs h.
      eapply add_to_frame_correct4;eauto.
    + inversion h_NoDupA.
      assumption.
    + !assert (fresh_params lparam' (fst fram_sz)).
      { red in h_fresh_prms.
        red.
        rewrite Forall_forall in h_fresh_prms|-*.
        !intros.
        apply h_fresh_prms.
        simpl.
        right.
        assumption. }
      eapply add_to_frame_fresh;eauto.
    + eapply add_to_frame_correct4;eauto.
    + assumption.
    + replace x with (fst x,snd x) in heq_add_to_fr_nme.
      * eapply add_to_frame_nodup;eauto.
        red in h_fresh_prms.
        rewrite Forall_forall in h_fresh_prms.
        match type of h_fresh_prms with
        | context [List.In _ (?prm::_)]  => specialize (h_fresh_prms prm)
        end.
        apply h_fresh_prms.
        left.
        reflexivity.
      * destruct x;auto.
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
    -> fresh_params lparam (fst fram_sz)
    (* then for all x-> e in fram_sz, x->e is still in res *)
    -> forall e x, CompilEnv.fetches x (fst fram_sz) = Some e
                   -> CompilEnv.fetches x (fst res) = Some e.
Proof.
  !!intros.
  red in h_fresh_prms_lparam.
  assert (h:=build_frame_lparams_preserve_increasing_order stbl (fst fram_sz) lparam (snd res) (fst res) (snd fram_sz)).
  replace (@pair CompilEnv.store Z (@fst (list (prod idnum OffsetEntry.T)) Z fram_sz)
                   (@snd (list (prod idnum OffsetEntry.T)) Z fram_sz)) with fram_sz in *;[|destruct fram_sz;auto].
  replace (pair (fst res) (snd res)) with res in *;[|destruct res;auto].
  specialize (h heq_bld_frm_lparam).
  !assert (increasing_order (fst res) ∧ Forall (gt_x_snd_y (snd res)) (fst res)).
  { !assert (NoDupA (λ x1 y : idnum * CompilEnv.V, fst x1 = fst y) (fst res)).
    { eapply build_frame_lparams_nodup;eauto. }
    apply h;auto.
    apply Forall_forall.
    !intros .
    unfold upper_bound in h_upb.
    apply h_upb with (nme:=(fst x0)).
    specialize (h_upb (fst x0) (snd x0)).
    apply In_fetches_NoDup.
    - assumption.
    - replace (fst x0, snd x0) with x0;auto.
      destruct x0;simpl;auto. }
  clear h.
  !!destruct h_and as [? h_forall_ord].
  rewrite function_utils.build_frame_lparams_ok in *.
  revert h_incr_order h_fresh_prms_lparam res heq_bld_frm_lparam e x heq_CEfetches_x h_incr_order0  h_forall h_upb.
  !!(functional induction (function_utils.build_frame_lparams stbl fram_sz lparam); try discriminate;
     try rewrite <- ?function_utils.build_frame_lparams_ok in *;intros;up_type).
  - simpl in *.
    !invclear heq_OK.
    assumption.
  - rename x into nme_fram_sz.
    !invclear h_forall0.
    simpl in *.
    destruct nme_fram_sz as [new_fram new_sz].
    assert (h_correct4:= add_to_frame_correct4 stbl fram_sz nme subtyp_mrk (new_fram,new_sz) h_incr_order h_upb heq_add_to_fr_nme).
    decomp h_correct4.
    assert (h_correct3:= λ typename, add_to_frame_correct3 stbl fram_sz nme subtyp_mrk new_fram new_sz
                                                           typename e h_incr_order h_upb heq_CEfetches_none).
    eapply IHr;auto.
    + inversion h_NoDupA_lparam.
      assumption.
    + simpl.
      eapply add_to_frame_nodup;eauto.
    + simpl in *.
      apply Forall_forall.
      !!intros prmspec ?.
      rewrite Forall_forall in h_forall_lparam'.
      specialize (h_forall_lparam' prmspec h_in_prmspec_lparam').
      up_type.
      eapply add_to_frame_correct_none with (parname:=nme);eauto.
      !inversion h_NoDupA_lparam.
      intro abs.
      subst nme.
      rewrite InA_alt in neg_h_inA.
      apply neg_h_inA. clear neg_h_inA.
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
(*     -> fresh_params lparam (fst fram_sz) *)
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

Ltac rename_hyp_decl h th :=
  match th with
(*    | Decl_list_form ?d => fresh "h_decl_list_" d
    | Decl_list_form _ => fresh "h_decl_list"
    | Decl_atomic ?d => fresh "h_decl_atom_" d
    | Decl_atomic _ => fresh "h_decl_atom"*)
    | _ => rename_hyp_list h th
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


Definition transl_paramexprlist := Eval cbv beta delta [bind bind2 transl_paramexprlist] in transl_paramexprlist.

Function function_utils_transl_paramexprlist (stbl : symboltable) (CE : compilenv) (el : list exp) (lparams : list paramSpec) {struct el} :
  res (list expr) :=
  let (l, l0) := (el, lparams) in
  match l with
  | nil => match l0 with
           | nil => Errors.OK nil
           | _ :: _ => Error (msg "Bad number of arguments")
           end
  | e1 :: e2 =>
      match l0 with
      | nil => Error (msg "Bad number of arguments")
      | p1 :: p2 =>
          match parameter_mode p1 with
          | In =>
              match transl_expr stbl CE e1 with
              | Errors.OK x => match function_utils_transl_paramexprlist stbl CE e2 p2 with
                        | Errors.OK x0 => Errors.OK (x :: x0)
                        | Error msg => Error msg
                        end
              | Error msg => Error msg
              end
          | Out =>
              match e1 with
              | Literal _ _ => Error (msg "Out or In Out parameters should be names")
              | Name _ nme =>
                  match transl_name stbl CE nme with
                  | Errors.OK x => match function_utils_transl_paramexprlist stbl CE e2 p2 with
                            | Errors.OK x0 => Errors.OK (x :: x0)
                            | Error msg => Error msg
                            end
                  | Error msg => Error msg
                  end
              | BinOp _ _ _ _ => Error (msg "Out or In Out parameters should be names")
              | UnOp _ _ _ => Error (msg "Out or In Out parameters should be names")
              end
          | In_Out =>
              match e1 with
              | Literal _ _ => Error (msg "Out or In Out parameters should be names")
              | Name _ nme =>
                  match transl_name stbl CE nme with
                  | Errors.OK x => match function_utils_transl_paramexprlist stbl CE e2 p2 with
                            | Errors.OK x0 => Errors.OK (x :: x0)
                            | Error msg => Error msg
                            end
                  | Error msg => Error msg
                  end
              | BinOp _ _ _ _ => Error (msg "Out or In Out parameters should be names")
              | UnOp _ _ _ => Error (msg "Out or In Out parameters should be names")
              end
          end
      end
  end.


Lemma transl_paramexprlist_ok : forall x y z, function_utils_transl_paramexprlist x y z = spark2Cminor.transl_paramexprlist x y z.
Proof.
  reflexivity.
Qed.

Ltac rename_tmp h th :=
  match th with
    | transl_paramexprlist _ _ _ _ = Error _ => fresh "heq_transl_params_ERR"
    | transl_paramexprlist _ _ _ _ = (OK ?r) => fresh "heq_transl_params_" r
    | _ => rename_hyp_decl h th
  end.
Ltac rename_sparkprf ::= rename_tmp.


(* 
Lemma copy_in_cps:
  forall st s pb_lvl sto prmnme e_v lparam le res,
  copy_in st s (push (pb_lvl, sto) prmnme e_v) lparam le (OK (pb_lvl, res ++ sto))
  -> copy_in st s (push (pb_lvl, nil) prmnme e_v) lparam le (OK (push (pb_lvl, nil) prmnme e_v)).
Proof.
  !intros.
  remember (push (pb_lvl, sto) prmnme e_v) as h_push1.
  remember (OK (pb_lvl, res ++ sto)) as h_res.
  revert Heqh_push1 Heqh_res.
  !induction h_copy_in; !intros;subst; try discriminate; try (now constructor).
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
  !intros.
  remember (pb_lvl, sto) as pb_lvl_sto.
  remember (OK f) as h_norm_f.
  revert pb_lvl sto Heqh_norm_f Heqpb_lvl_sto.
  !induction h_copy_in; try discriminate;subst;repeat eq_same_clear;intros;subst.
  - inversion Heqh_norm_f; subst; eauto.
  - unfold push in IHh_copy_in.
    simpl in IHh_copy_in.
    edestruct IHh_copy_in;eauto.
  - unfold push in IHh_copy_in.
    simpl in IHh_copy_in.
    edestruct IHh_copy_in;eauto.
  - unfold push in IHh_copy_in.
    simpl in IHh_copy_in.
    edestruct IHh_copy_in;eauto.
  - unfold push in IHh_copy_in.
    simpl in IHh_copy_in.
    edestruct IHh_copy_in;eauto.
  - unfold push in IHh_copy_in.
    simpl in IHh_copy_in.
    edestruct IHh_copy_in;eauto.
Qed.

Lemma copy_in_spec:
  forall st s CE spb ofs locenv g m sto pb_lvl prms_profile args args_t sto',
    chained_stack_structure m (Datatypes.length CE -1) (Values.Vptr spb ofs)
    -> invariant_compile CE st
    -> match_env st s CE (Values.Vptr spb ofs) locenv g m
    -> transl_paramexprlist st CE args prms_profile =: args_t
    (* je veux exprimer la propriété qui parle  *)
    -> copyIn st s (pb_lvl,sto) prms_profile args (OK (pb_lvl,sto'))
    -> exists lval_t, eval_exprlist g (Values.Vptr spb ofs) locenv m args_t lval_t
(*             sto'' /\ copy_in st s (pb_lvl,nil) prms_profile args (OK (pb_lvl,sto'')) *)
(*                       /\ sto' = List.app sto'' sto *)
.
Proof.
  !intros.
  remember (OK (pb_lvl, sto')) as res_copy_in.
  remember (pb_lvl, sto) as pb_lvl_sto.
  revert heq_transl_paramexprlist h_chain h_inv_comp_CE_st 
         h_match_env Heqres_copy_in Heqpb_lvl_sto .
  revert spb ofs locenv g m sto pb_lvl args_t sto'.
  !induction h_copy_in; try discriminate;subst;repeat eq_same_clear;!intros.
  - subst.
    rewrite <- transl_paramexprlist_ok in heq_transl_paramexprlist;
      functional inversion heq_transl_paramexprlist;
      subst;
      rewrite ?transl_paramexprlist_ok in * ;
      idtac.
    inversion heq_OK;subst;clear heq_OK.
    exists  (@nil Values.val).
    constructor.
  - rewrite <- transl_paramexprlist_ok in heq_transl_paramexprlist;
      functional inversion heq_transl_paramexprlist;subst; rewrite ?transl_paramexprlist_ok in *;
      match goal with
      | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
      end.
    !!edestruct IHh_copy_in;clear IHh_copy_in;eauto.
    + unfold push;simpl. reflexivity.
    + assert (h_transl:=transl_expr_ok _ _ _ _ H9 _ _ _ _ _ _ h_eval_expr_e_e_v h_match_env).
      !!destruct h_transl as [v_t [? ?]].
      exists (x_v::x1);repeat split;eauto.
      econstructor;eauto.
  - rewrite <- transl_paramexprlist_ok in heq_transl_paramexprlist;
      functional inversion heq_transl_paramexprlist;subst; rewrite ?transl_paramexprlist_ok in *;
      match goal with
      | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
      end.
    !!edestruct IHh_copy_in;clear IHh_copy_in;eauto.
    + unfold push;simpl. reflexivity.
    + assert (h_transl:=transl_expr_ok _ _ _ _ H9 _ _ _ _ _ _ h_eval_expr_e h_match_env).
      !!destruct h_transl as [v_t [? ?]].
      exists (x_v::x1);repeat split;eauto.
      econstructor;eauto.
  - !!(rewrite <- transl_paramexprlist_ok in heq_transl_paramexprlist;
       functional inversion heq_transl_paramexprlist;subst; rewrite ?transl_paramexprlist_ok in *;
      match goal with
      | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
      end).
    !!edestruct IHh_copy_in;clear IHh_copy_in;eauto.
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
      assert (h_ex:exists typ_nme, type_of_name st nm =: typ_nme).
      { admit. (* well typedness of the program? *) }
      !!destruct h_ex as [typ_nme ?] .
      assert (h_ex:exists typ, transl_type st typ_nme =: typ).
      { admit. (* completness of type translation? *) }
      !!destruct h_ex as [typ ?].
      assert (h_ex: exists load_addr_nme, make_load nm_t typ =: load_addr_nme).
      { admit. (* completness of make_load? *) }
      !!destruct h_ex as [load_addr_nme ?].
      assert (h_stack_mtch:=(me_stack_match h_match_env)).
      red in h_stack_mtch.
      !!destruct (h_stack_mtch _ _ _ _ _ _ h_eval_name_nm_v heq_type_of_name heq_transl_name heq_transl_type heq_make_load) as [v_t [htrsl h_eval]];eauto.
      up_type.
      (* Currently we only have by_value loads (but with arrays this may change) *)
      !functional inversion heq_make_load.
      subst.
      (* From [Cminor.eval_expr (Eload chunk x) v_t] we can deduce that [x] itself can be evaluated to a value. *)
      !inversion h_CM_eval_expr_load_addr_nme_load_addr_nme_v;subst.
      exists (nm_t_v::le_t_v).
      constructor;auto.
  - !!(rewrite <- transl_paramexprlist_ok in heq_transl_paramexprlist;
       functional inversion heq_transl_paramexprlist;subst; rewrite ?transl_paramexprlist_ok in *;
       match goal with
       | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
       end).
    !!edestruct IHh_copy_in;clear IHh_copy_in;eauto.
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
      assert (h_ex:exists typ_nme, type_of_name st nm =: typ_nme).
      { admit. (* well typedness of the program? *) }
      !!destruct h_ex as [typ_nme ?] .
      assert (h_ex:exists typ, transl_type st typ_nme =: typ).
      { admit. (* completness of type translation? *) }
      !!destruct h_ex as [typ ?].
      assert (h_ex: exists load_addr_nme, make_load nm_t typ =: load_addr_nme).
      { admit. (* completness of make_load? *) }
      !!destruct h_ex as [load_addr_nme ?].
      assert (h_stack_mtch:=(me_stack_match h_match_env)).
      red in h_stack_mtch.
      !!destruct (h_stack_mtch _ _ _ _ _ _ h_eval_name_nm heq_type_of_name heq_transl_name heq_transl_type heq_make_load) as [v_t [htrsl h_eval]];eauto.
      up_type.
      (* Currently we only have by_value loads (but with arrays this may change) *)
      functional inversion heq_make_load.
      subst.
      (* From [Cminor.eval_expr (Eload chunk x) v_t] we can deduce that [x] itself can be evaluated to a value. *)
      !inversion h_CM_eval_expr_load_addr_nme_load_addr_nme_v;subst.
      exists (nm_t_v::le_t_v).
      constructor;auto.
  - up_type.
    !!(rewrite <- transl_paramexprlist_ok in heq_transl_paramexprlist;
       functional inversion heq_transl_paramexprlist;subst; rewrite ?transl_paramexprlist_ok in *;
       match goal with
       | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
       end).
    !!edestruct IHh_copy_in;clear IHh_copy_in;eauto.
    + unfold push;simpl. reflexivity.
    + rename x0 into le_t.
      rename x into le_t_v.
      (* We need to show that [n_t] can be evaluated to something.
         since [n_t] is the adresse of a variable of the program,
         by well_formedness/well_typedness it should correctly evaluate
         to an address. Even if it is not guaranteed that this address
         contains a value in the current case: (Out parameter). *)
      assert (h_ex:∃ n_t_v, Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nm_t n_t_v).
      { !!pose proof (me_stack_match_addresses (me_safe_cm_env h_match_env)).
        red in h_stk_mtch_addr_CE_m.
        eapply h_stk_mtch_addr_CE_m.
        eassumption. }

      !!destruct h_ex as [? ?].
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
  !!intros until n'.
  revert m n sp v h_repeat_loadv_n_sp.
  !induction n';cbn;!intros.
  - subst.
    exists sp;split.
    + constructor.
    + assumption.
  - subst.
    !inversion h_repeat_loadv_n_sp.
    specialize (IHn' m (n' + n'')%nat sp' v h_repeat_loadv n'' eq_refl).
    decomp IHn'.
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
  !!intros until n'.
  revert m n sp h_chain_n_sp.
  !induction n';cbn;!intros.
  - subst.
    !inversion h_repeat_loadv_O_sp.
    assumption.
  - !inversion h_repeat_loadv.
    eapply IHn' with (n:=(n' + n'')%nat);eauto.
    subst n.
    
    !inversion h_chain_n_sp.
    rewrite h_loadv in h_loadv_sp_sp'.
    !inversion h_loadv_sp_sp'.
    assumption.
Qed.

Lemma malloc_preserves_chained_structure : 
  ∀ lvl m sp b ofs  m' new_sp,
    Mem.alloc m b ofs = (m', new_sp) ->
    chained_stack_structure m lvl sp ->
    chained_stack_structure m' lvl sp.
Proof.
  intro lvl.
  !induction lvl;!intros.
  - !inversion h_chain_O_sp.
    constructor.
  - !inversion h_chain_sp.
    cbn in *.
    econstructor.
    + eapply IHlvl;eauto.
    + cbn.
      eapply Mem.load_alloc_other;eauto.
Qed.




Lemma malloc_preserves_chaining_loads : 
  ∀ m lvl sp sz m' new_sp,
    Mem.alloc m 0 sz = (m', new_sp) ->
    ∀ n, (n <= lvl)%nat ->
         chained_stack_structure m lvl sp ->
         ∀ e g sp',
           Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Int.zero)) n) sp'
           -> Cminor.eval_expr g sp e m' (build_loads_ (Econst (Oaddrstack Int.zero)) n) sp'.
Proof.
  !!intros until n.
  induction n;!intros.
  - cbn in *.
    !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_lvl_sp.
    decomp h_ex.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - !!assert (n <= lvl)%nat by omega.
    specialize (IHn h_le_n_lvl h_chain_lvl_sp).
    cbn -[Mem.storev] in *.
    !inversion h_CM_eval_expr_sp'.
    specialize (IHn _ _ _ h_CM_eval_expr_vaddr).
    econstructor.
    + eassumption.
    + cbn in *.
      rewrite <- h_loadv_vaddr_sp'.
      destruct vaddr; try discriminate.
      cbn in *.
      eapply Mem.load_alloc_unchanged;eauto.
      eapply Mem.valid_access_valid_block.
      apply Mem.load_valid_access in h_loadv_vaddr_sp'.
      eapply Mem.valid_access_implies with (1:=h_loadv_vaddr_sp').
      constructor.
Qed.


Lemma malloc_preserves_chaining_loads_2 : 
  ∀ m lvl sp sz m' new_sp,
    Mem.alloc m 0 sz = (m', new_sp) ->
    ∀ n, (n <= lvl)%nat ->
         chained_stack_structure m lvl sp ->
         ∀ e g sp',
           Cminor.eval_expr g sp e m' (build_loads_ (Econst (Oaddrstack Int.zero)) n) sp'
           -> Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Int.zero)) n) sp'.
Proof.
  !!intros until n.
  induction n;!intros.
  - cbn in *.
    !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_lvl_sp.
    decomp h_ex.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - !!assert (n <= lvl)%nat by omega.
    specialize (IHn h_le_n_lvl h_chain_lvl_sp).
    cbn -[Mem.storev] in *.
    !inversion h_CM_eval_expr_sp'.
    specialize (IHn _ _ _ h_CM_eval_expr_vaddr).
    econstructor.
    + eassumption.
    + cbn in *.
      rewrite <- h_loadv_vaddr_sp'.
      destruct vaddr; try discriminate.
      cbn in *.
      symmetry.
      eapply Mem.load_alloc_unchanged;eauto.
      destruct (Mem.valid_block_alloc_inv _ _ _ _ _ h_malloc_m_m' b).
      * eapply Mem.valid_access_valid_block.
        apply Mem.load_valid_access in h_loadv_vaddr_sp'.
        eapply Mem.valid_access_implies with (1:=h_loadv_vaddr_sp').
        constructor.
      * exfalso.
        subst.
        !!assert ((lvl-n) + n = lvl)%nat by omega.
        rewrite <- heq_add in h_chain_lvl_sp.
        !!pose proof (chain_structure_cut _ _ _ _ h_chain_lvl_sp) g e.
        decomp h_ex.
        rewrite heq_add in h_CM_eval_expr_v.
        subst_det_addrstack_zero.
        destruct (lvl - n)%nat eqn:heq'.
        -- exfalso; omega.
        -- cbn in h_CM_eval_expr_v0.
           eapply chained_stack_structure_decomp_S_2 in h_CM_eval_expr_v0.
           ++ decomp h_CM_eval_expr_v0.
              !inversion h_CM_eval_expr_sp'0.
              subst_det_addrstack_zero.
              absurd (Mem.valid_block m new_sp).
              ** eapply Mem.fresh_block_alloc;eauto.
              ** unfold Mem.loadv in h_loadv_vaddr_sp'0.
                 eapply  Mem.load_valid_access in h_loadv_vaddr_sp'0.
                 eapply Mem.valid_access_valid_block.
                 eapply Mem.valid_access_implies;eauto.
                 constructor.
           ++ assumption.
      * assumption.
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
  intros stbl enclosingCE lvl lparams decl res heq_bldCE.
  rewrite <- build_compilenv_ok in heq_bldCE.
  !functional inversion heq_bldCE;subst.
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
    fetch_proc pnum st =Some (lvl, p) ->
    procedure_declarative_part p = decl ->
    ∀ i : AST.ident,
      List.In i (transl_decl_to_lident st decl) → i ≠ chaining_param.

Ltac rename_wf_st h th :=
  match th with
  | wf_st ?st => fresh "h_wf_st_" st
  | wf_st _ => fresh "h_wf_st"
  | _ => rename_tmp h th
  end.
Ltac rename_sparkprf ::= rename_wf_st.

Lemma exec_preserve_invisible:
  ∀ g func stkptr locenv m stmt_t tr locenv' m' outc,
    exec_stmt g func stkptr locenv m stmt_t tr locenv' m' outc -> 
    ∀ st CE stmt s lvl,
      wf_st st ->
      lvl = Datatypes.length CE ->
      strong_match_env st s CE stkptr locenv g m ->
      chained_stack_structure m lvl stkptr ->
      invariant_compile CE st ->
      transl_stmt st CE stmt =: stmt_t ->
      chained_stack_structure m' lvl stkptr
      ∧ forall astnum,
          (* eval_stmt st s stmt s' -> *)
          Mem.unchanged_on (forbidden st CE g astnum locenv stkptr m m) m m'.
Proof.
  !!intros until 1.
  !induction h_exec_stmt_stmt_t_outc;!intros;
    match goal with
  | H: transl_stmt ?st ?CE ?stmt = _ |- _ => 
    rewrite <- transl_stmt_ok in H;
    !functional inversion H
  end;
    rewrite transl_stmt_ok in *;subst;
      (match goal with |- ?chstactctruct ∧ ?unch => assert (hstruc_m':chstactctruct);[ | split;[assumption|]] end);!intros.
  (* Skip => chained_struct *)
  - assumption.
  (* Skip => unchanged on forbidden *)
  - apply Mem.unchanged_on_refl.
  (* Sstore => chained_struct *)
  - admit.
  (* Store => unchanged on forbidden *)
  - destruct addr_v;try discriminate. 
    up_type.
    simpl in heq_storev_a_v_m'.
    split.
    + admit.
    + !intros.
      eapply Mem.store_unchanged_on;eauto.
      !intros.
      intros [abs1 abs2].
      red in abs1.
      !functional inversion heq_transl_name;subst.
      simpl in heq_compute_chnk_nme.
      rewrite <- transl_variable_astnum with (a:=astnum) (1:=heq_transl_variable) in heq_transl_variable.
      specialize (abs1 id addr chunk b i heq_transl_variable heq_compute_chnk_nme h_CM_eval_expr_addr_addr_v). 
      destruct abs1;auto;omega.
  (* Scall => chained_struct *)
  - admit.
  (* Scall => unchanged on forbidden *)
  - rename x into args_t.
    rename lexp into args.
(*     rename bl into all_args_t. *)
    rename a_v into proc_addr.
    rename fd into proc_value.
    rename y into proc_lvl.
    !assert (match_env st s CE sp e g m).
    { inversion h_strg_mtch_s_CE_m;auto. }
    !inversion h_evalfuncall_fd_vargs_vres;subst.
    + (* internal function *)
      !assert (
         (* [transl_procsig] gives [f0,proc_lvl], so f0 is the result
            of a translation with the right CE. All procedures in
            memory are supposed to come from compilation. *)
         ∃ CE_prfx CE_sufx pbdy X lotherproc,
           CompilEnv.cut_until CE proc_lvl CE_prfx CE_sufx /\
           transl_procedure st CE_sufx proc_lvl pbdy (* prov_lvl+1? *)
           = Errors.OK ((X, AST.Gfun (AST.Internal f0))::lotherproc) /\
           ∀ i : AST.ident,
             List.In i (transl_decl_to_lident st (procedure_declarative_part pbdy))
             → i ≠ chaining_param).
      { unfold transl_procsig in heq_transl_procsig_pnum.
        !!assert (stack_match_functions st sp CE e g m) by eauto.
        red in h_stk_mtch_fun.
        unfold symboltable.fetch_proc in h_stk_mtch_fun.
        specialize (h_stk_mtch_fun pnum).
        !!destruct (fetch_proc pnum st) eqn:?;try discriminate.
        !destruct t0.
        specialize (h_stk_mtch_fun l p eq_refl).
        decomp h_stk_mtch_fun.
        exists CE', CE''.
        !!destruct 
          (transl_lparameter_specification_to_procsig
             st l (procedure_parameter_profile p)) eqn:?;try discriminate.
        simpl in heq_transl_procsig_pnum.
        !invclear heq_transl_procsig_pnum.
        exists p, pnum0, lglobdef.
        split;[ | split].
        + assumption.
        + subst_det_addrstack_zero.
          rewrite heq_find_func_a_v_fd in heq_find_func_paddr_fction.
          !invclear heq_find_func_paddr_fction.
          assumption.
        + eapply h_wf_st_st;eauto. }
      decomp h_ex;up_type.
      rename H2 into h_pbdy_chainarg_noclash.
      rewrite transl_procedure_ok in heq_transl_proc_pbdy.
      !functional inversion heq_transl_proc_pbdy;up_type.
      rewrite <- transl_procedure_ok in *.
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
      cbn [ proc_t fn_vars fn_params fn_body pbody_t] in h_exec_stmt.

      (* splitting the execution of proc in 5: chain_param, initparam, initlocvar, bdy and cpout. *)
      !!inversion_clear h_exec_stmt;subst.
      2: admit. (* prematurate error, this should work with parts of the normal case *)
      !!inversion_clear h_exec_stmt;subst.
      2: admit. (* prematurate error, this should work with parts of the normal case *)
      !!inversion_clear h_exec_stmt;subst.
      2: admit. (* prematurate error, this should work with parts of the normal case *)
      !!inversion_clear h_exec_stmt0;subst.
      2: admit. (* prematurate error, this should work with parts of the normal case *)

      * (* RENAMING *)
        (* Case where No error occured during the whole function call *)
        rename h_exec_stmt into h_exec_stmt_init.
        match goal with
        | H: exec_stmt _ _ _ _ ?ma chain_param _ ?e ?mb _ |- _ =>
          rename mb into m_chain; rename e into e_chain;
            rename ma into m_pre_chain
        end.
        match goal with
        | H: exec_stmt _ _ _ _ _ initparams _ ?e ?mb _ |- _ =>
          rename mb into m_init_params;rename e into e_initparams;
            rename H into h_exec_stmt_initparams
        end.
        match goal with
        | H: exec_stmt _ _ _ _ _ (Sseq locvarinit Sskip) _ ?e ?mb _ |- _ => 
          rename mb into m_locvarinit; rename e into e_locvarinit;
            rename H into h_exec_stmt_locvarinit
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
        set (sp_proc := Values.Vptr sp0 Int.zero) in *.
        up_type.
        !assert (Mem.unchanged_on (forbidden st CE g astnum e sp m m_chain) m m_pre_chain).
        { (* Lemma about invisible and alloc. *)
          eapply Mem.alloc_unchanged_on.
          eauto. }
        !!(pose proof strong_match_env_match_env_sublist _ _ _ _ _ _ _ h_strg_mtch_s_CE_m
                h_inv_comp_CE_st _ _ _ h_CEcut_CE_proc_lvl).
        !!destruct h_ex as [s' [s'' [sp'' [? [? h_mtchenv]]]]].
         (* well formedness: one can call only visible procedures,
            i.e. of level at most (current level) + 1, where current level
            is |CE|-1, hence: *)
        !assert (proc_lvl<=Datatypes.length CE)%nat.
        { admit. }
        assert (proc_lvl = Datatypes.length CE_sufx)%nat.
        { !!assert (CompilEnv.exact_levelG CE) by eauto.
          eapply cut_until_CompilEnv.exact_levelG;eauto. }
        subst proc_lvl.        
        !assert (chained_stack_structure m (Datatypes.length CE_sufx) sp'').
        { eapply (repeat_Mem_loadv_cut_mem_loadv _ _ _ h_chain_lvl_sp (Datatypes.length CE - Datatypes.length CE_sufx)).
          - omega.
          - assumption. }
        assert (Datatypes.length CE_proc = S (Datatypes.length CE_sufx)) as heq_lgth_CE_proc.
        { rewrite <- build_compilenv_ok in heq_build_compilenv.
          functional inversion heq_build_compilenv.
          reflexivity. }
        (* Since the chaining param is not the translation of a spark variable, 
           we stay in callers environment, that is: from m1 to m4 there is no change
           in the addresses visible in m. *)
        !assert (Mem.unchanged_on (forbidden st CE g astnum e sp m m_chain) m_pre_chain m_chain).
        { unfold chain_param in h_exec_stmt_chain_param_Out_normal.
          !inversion h_exec_stmt_chain_param_Out_normal.
          unfold Mem.storev in heq_storev_v_m_chain.
          destruct vaddr;try discriminate.
          apply Mem.store_unchanged_on with (1:=heq_storev_v_m_chain).
          !intros.
          unfold sp_proc in h_CM_eval_expr_vaddr.
          !destruct h_and.
          !inversion h_CM_eval_expr_vaddr;subst.
          cbn in h_eval_constant.
          !inversion h_eval_constant;subst.
          intro abs. red in abs. destruct abs as [abs1 abs2].
          red in abs2.
          apply abs2.
          red.
          intro.
          eapply fresh_block_alloc_perm;eauto. }
        (* the new sp (sp') has zero offset. *)
        !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_sp''.
        decomp h_ex.
        subst sp'' .
        set (sp'' := Values.Vptr b' Int.zero).
        up_type.
        !assert (chained_stack_structure m_pre_chain (Datatypes.length CE_sufx) (Values.Vptr b' Int.zero)).
        { eapply malloc_preserves_chained_structure;eauto. }

        !assert(chained_stack_structure m_chain (Datatypes.length CE_sufx) (Values.Vptr b' Int.zero)).
        { !!inversion heq_lgth_CE_proc;clear heq_lgth_CE_proc.
(*           rewrite <- heq_all_args_t in h_CM_eval_exprl_bl_vargs. *)
          !inversion h_CM_eval_exprl_bl_vargs.
          unfold chain_param in h_exec_stmt_chain_param_Out_normal.
          !inversion h_exec_stmt_chain_param_Out_normal.
          unfold sp_proc in h_CM_eval_expr_vaddr.
          repeat subst_det_addrstack_zero.
          eapply storev_outside_struct_chain_preserves_chained_structure with (m:=m_pre_chain) (g:=g)(e:=e) (sp0:=sp0).
          + !intros.
            !!assert (n < Datatypes.length CE_sufx)%nat by omega.
            !!pose proof malloc_distinct_from_chaining_loads _ _ _ h_chain_sp'' n _ _ _ h_malloc_m_m1 e g h_lt_n b'0.
            apply H.
            eapply malloc_preserves_chaining_loads_2;eauto.
            eapply chained_stack_structure_le;eauto;omega.
          + assumption.
          + eassumption. }
          
        !assert (chained_stack_structure m_chain (S (Datatypes.length CE_sufx)) sp_proc).
        { !!inversion heq_lgth_CE_proc;clear heq_lgth_CE_proc.
(*           rewrite <- heq_all_args_t in h_CM_eval_exprl_bl_vargs. *)
          !inversion h_CM_eval_exprl_bl_vargs.
          unfold chain_param in h_exec_stmt_chain_param_Out_normal.
          !inversion h_exec_stmt_chain_param_Out_normal.
          !inversion h_CM_eval_expr_v.
          cbn [set_params] in heq_mget_chaining_param_v.          
          rewrite map_get_set_same_nodup in heq_mget_chaining_param_v;auto.
          !assert (chained_stack_structure m (Datatypes.length CE - Datatypes.length CE_sufx) sp).
          { eapply chained_stack_structure_le;eauto;omega. }
          pose proof chain_repeat_loadv _ _ _ h_chain_sp _ g e h_repeat_loadv.
          rewrite heq_length.
          apply chained_S with (b':=b').
          - !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain.
            decomp h_ex.
            unfold sp_proc in h_CM_eval_expr_vaddr.
            repeat subst_det_addrstack_zero.
            eapply storev_outside_struct_chain_preserves_chained_structure with (m:=m_pre_chain) (g:=g)(e:=e) (sp0:=sp0).
            + !intros.
              !!assert (n < Datatypes.length CE_sufx)%nat by omega.
              !!pose proof malloc_distinct_from_chaining_loads _ _ _ h_chain_sp'' n _ _ _ h_malloc_m_m1 e g h_lt_n b'1 as h_alloc_diff.
              apply h_alloc_diff.
              eapply malloc_preserves_chaining_loads_2;eauto.
              eapply chained_stack_structure_le;eauto;omega.
            + assumption.
            + eassumption.

          (* malloc + store didnt change chaingin struct. *)
          - unfold sp_proc in *.
            repeat  subst_det_addrstack_zero.
            cbn in heq_storev_v_m_chain |- * .
            rewrite (Mem.load_store_same _ _ _ _ _ _ heq_storev_v_m_chain).
            inversion heq_mget_chaining_param_v.
            reflexivity. }

        (* This is from m_chain only. *)
        (* TODO: prove that (forbidden m_chain m_chain) x y <=>
        (forbidden m m_chain) x y, everything that is visible from
        m_chain is either visible from m or free from m. *)
        !assert (Mem.unchanged_on (forbidden st CE_proc g astnum e_chain sp_proc m_chain m_chain) m_chain m_init_params
                 ∧ chained_stack_structure m_init_params (Datatypes.length CE_proc) sp_proc
                 ∧ unchange_forbidden st CE_proc g astnum e_chain e_initparams sp_proc m_chain m_init_params).
        { eapply init_params_preserves_structure;eauto.
          - eapply build_compilenv_exact_lvl with (2:=heq_build_compilenv);eauto.
            eapply exact_lvlG_cut_until;eauto.
          - eapply build_compilenv_stack_no_null_offset with (CE:=CE_sufx).
            + eapply exact_lvlG_cut_until;eauto.
            + specialize (h_mtchenv e).
              eapply me_safe_cm_env.
              eapply h_mtchenv.
            + eauto.
          - rewrite heq_lgth_CE_proc.
            assumption.
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
            !assert (stack_localstack_aligned (Datatypes.length CE_sufx) e g m sp'').
            { apply h_mtchenv. }
            red.
            !intros.
            destruct δ_lvl.
            + cbn. (* the new procedure stkptr is aligned. *)
              eexists.
              eapply cm_eval_addrstack_zero.
            + unfold sp_proc. (* The stckptr of enclosing procedure are aligned (they did not change). *)
              (*First prove that after one load we are back on sp''.*)
              (* Then prove that nothing visible from there has change (use unchanged_on forbidden hyps)  *)
              red in h_aligned_g_m.
              !assert (δ_lvl ≤ Datatypes.length CE_sufx).
              { rewrite <-build_compilenv_ok in heq_build_compilenv.
                functional inversion heq_build_compilenv.
                rewrite build_compilenv_ok in heq_build_compilenv;subst.
                cbn in h_le_δ_lvl.
                omega. }
              specialize (h_aligned_g_m _ h_le_δ_lvl0).
              decomp h_aligned_g_m.
(*               unfold chaining_arg in *. *)
(*               !!inversion heq;clear heq. *)
(*               rewrite <- heq_all_args_t in h_CM_eval_exprl_bl_vargs. *)
              !inversion h_CM_eval_exprl_bl_vargs.
              unfold initlocenv,chain_param in h_CM_eval_expr_addr_enclosing_frame_addr_enclosing_frame_v.
              !inversion h_exec_stmt_chain_param_Out_normal.
              unfold current_lvl in *.
              (* needed by the next omega. *)
              unfold sp_proc in h_CM_eval_expr_vaddr.
              subst_det_addrstack_zero.
              (* cleaning + recollecting all the occurrencies. *)
              subst sp_proc.
              set (sp_proc:=(Values.Vptr sp0 Int.zero)) in *|-*.
(*               subst initlocenv. *)
              set (initlocenv := set_locals (transl_decl_to_lident st decl0) (set_params (addr_enclosing_frame_v :: vl) (chaining_param :: tlparams))) in *|-*.
              set (whole_trace := (Events.Eapp Events.E0 (Events.Eapp (Events.Eapp t2 t4) (Events.Eapp t0 t5)))) in *|-* .
              up_type.
              (* end cleaning *)
              (* load sp_proc (S δ_lvl) gives the same as load sp'' δ_lvl, i.e. b_δ. *)
              exists b_δ.
              (* first change the locenv (does not influence a load anyway). *)
              apply eval_expr_build_load_const_inv_locenv with (locenv:=e).

              !assert (chained_stack_structure m δ_lvl sp'').
              { !assert(δ_lvl ≤ Datatypes.length CE).
                { transitivity (Datatypes.length CE_sufx).
                  - assumption.
                  - rewrite <- (CompilEnv.cut_until_spec1 _ _ _ _ h_CEcut_CE_proc_lvl).
                    rewrite app_length.
                    omega. }
                apply chained_stack_structure_le with (n:=Datatypes.length CE_sufx);eauto. }
              !assert (chained_stack_structure m_chain (S δ_lvl) sp_proc).
              { !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_δ_lvl_sp''.
                decomp h_ex.
                subst sp'' .
                !inversion h_CM_eval_expr_v.
                unfold initlocenv in heq_mget_chaining_param_initlocenv_v.
                !assert ( Maps.PTree.get chaining_param
                                         (set_locals (transl_decl_to_lident st decl0) (Maps.PTree.set chaining_param addr_enclosing_frame_v (set_params vl tlparams)))
                          = Some addr_enclosing_frame_v).
                { eapply map_get_set_same_nodup.
                  !intros.
                  eapply h_pbdy_chainarg_noclash.
                  cbn.
                  assumption. }
                  subst chain_param.
(*                   subst chaining_arg. *)
                  cbn [set_params] in heq_mget_chaining_param_initlocenv_v.
                  rewrite heq_mget_chaining_param_initlocenv_v in heq_mget_chaining_param_addr_enclosing_frame_v.
                  !invclear heq_mget_chaining_param_addr_enclosing_frame_v.
                  !assert (chained_stack_structure m (Datatypes.length CE - Datatypes.length CE_sufx) sp).
                  { eapply chained_stack_structure_le;eauto;omega. }
                  !!pose proof chain_repeat_loadv _ _ _ h_chain_sp _ g e h_repeat_loadv.
                  apply chained_S with (b':=b').
                - !assert (chained_stack_structure m_pre_chain  δ_lvl (Values.Vptr b' Int.zero)).
                  { eapply malloc_preserves_chained_structure;eauto. }
                  !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_δ_lvl.
                  decomp h_ex.
                  eapply storev_outside_struct_chain_preserves_chained_structure with (m:=m_pre_chain) (g:=g)(e:=e) (sp0:=sp0).
                  + !intros.
                    !!assert (n < Datatypes.length CE_sufx)%nat by omega.
                    pose proof malloc_distinct_from_chaining_loads _ _ _ h_chain_sp'' n
                      _ _ _ h_malloc_m_m1 e g h_lt_n b'2 as h_b'2_sp0.
                    apply h_b'2_sp0.
                    eapply malloc_preserves_chaining_loads_2;eauto.
                    eapply chained_stack_structure_le;eauto;omega.
                  + assumption.
                  + eassumption.

                (* malloc + store didnt change chaingin struct. *)
                - unfold sp_proc in *.
                  assert ((Values.Vptr b' Int.zero) = addr_enclosing_frame_v).
                  { eapply det_eval_expr ;eauto. }
                  subst.
                  cbn in heq_storev_v_m_chain |-* .
                  rewrite (Mem.load_store_same _ _ _ _ _ _ heq_storev_v_m_chain).
                  reflexivity. }
              eapply chained_stack_structure_decomp_S_2' with (sp':=sp'').
              * assumption.
              * econstructor;  (* one load goes to sp'' *) 
                  auto.
                -- eapply cm_eval_addrstack_zero_chain;eauto.
                -- cbn in heq_storev_v_m_chain |- *.
                   !assert (v = sp'').
                   { 
                     transitivity addr_enclosing_frame_v.
                     - subst sp_proc.
                       !inversion h_CM_eval_expr_v.
(*                        unfold initlocenv in heq0. *)
                       unfold initlocenv in heq_mget_chaining_param_initlocenv_v.
                       rewrite map_get_set_locals_diff in heq_mget_chaining_param_initlocenv_v.
                       2: admit. (* chaingin_param not in decl *)
                       cbn [set_params] in heq_mget_chaining_param_initlocenv_v.
                       rewrite Maps.PTree.gss in heq_mget_chaining_param_initlocenv_v.
                       inversion heq_mget_chaining_param_initlocenv_v.
                       reflexivity.
                     - apply chain_repeat_loadv with (g:=g)(e:=e) in h_repeat_loadv.
                       + subst_det_addrstack_zero.
                         reflexivity.
                       + eapply chained_stack_structure_le;eauto;omega. }
                   subst.
                   apply Mem.load_store_same in heq_storev_v_m_chain.
                   unfold Values.Val.load_result in heq_storev_v_m_chain.
                   !!pose proof match_env_sp_zero _ _ _ _ _ _ _ (h_mtchenv initlocenv).
                   decomp h_ex.
                   subst sp''.
                   assumption.
              * (* between m and m_chain we made one malloc and only wrote in that malloc, thus
                   the part of memory covered by build_loads from sp'' has not changed.
                   Actually it suffices that chainging addresses (from sp'', not from sp_proc)
                   are untouched, which is true since it is forbidden. *)
                  (* from sp'' nothing changed so eval_expr gives the same result. *)
                  (* (build_loads (Oaddrstask 0)) is a chaingin address, so no variable points to it, so invisible, so unchanged. *)

                (* sp'' is actuall of the form (Vptr sp''b Zero) *)
                !destruct (match_env_sp_zero _ _ _ _ _ _ _ (h_mtchenv e)).
                rename x into sp''b.
                !assert (chained_stack_structure m δ_lvl sp'').
                { apply chained_stack_structure_le with (n:=Datatypes.length CE_sufx).
                  eapply (repeat_Mem_loadv_cut_mem_loadv _ _ _ h_chain_lvl_sp (Datatypes.length CE - Datatypes.length CE_sufx)).
                  - !assert(δ_lvl ≤ Datatypes.length CE).
                    { transitivity (Datatypes.length CE_sufx).
                      - assumption.
                      - rewrite <- (CompilEnv.cut_until_spec1 _ _ _ _ h_CEcut_CE_proc_lvl).
                        rewrite app_length.
                        omega. }
                    omega.
                  - assumption.
                  - assumption. }

                !assert (chained_stack_structure m_pre_chain δ_lvl sp'').
                { eapply malloc_preserves_chained_structure;eauto. }

                (* all sp (but the last which points to nothing), are different from sp0
                   because sp0 comes from a malloc. *)
                eapply storev_outside_struct_chain_preserves_chaining with (m:=m_pre_chain) (lvl:=δ_lvl)(sp0:=sp0).
                -- (* sp'' points to a structure unchanged by the malloc. *)
                  !intros.
                  pose proof malloc_distinct_from_chaining_loads _ _ _ h_chain_δ_lvl_sp'' n _ _ _ h_malloc_m_m1 as h_b'_sp0.
                  !assert (Cminor.eval_expr g sp'' e m (build_loads_ (Econst (Oaddrstack Int.zero)) n) (Values.Vptr b'0 Int.zero)).
                  { eapply malloc_preserves_chaining_loads_2 with (1:=h_malloc_m_m1);eauto.
                    eapply chained_stack_structure_le;eauto.
                    omega. }
                  eapply h_b'_sp0;eauto.
                -- assumption.
                -- unfold sp_proc in heq_storev_v_m_chain. eassumption.
                -- auto with arith.
                -- (* This is true for m, and malloc does not change it so it is also true for m_pre_chain *) 
                  eapply malloc_preserves_chaining_loads with (1:=h_malloc_m_m1);eauto. }

        decomp h_and.

        (* changing the caller in forbidden. *)
        !assert (Mem.unchanged_on (forbidden st CE_proc g astnum e_chain sp_proc m m_chain) m_chain m_init_params).
        { eapply mem_unchanged_on_mon with (P:=(forbidden st CE_proc g astnum e_chain sp_proc m_chain m_chain));try assumption.
          !intros.
          unfold forbidden in h_forbid_m_m_chain_x_y |- *.
          decomp h_forbid_m_m_chain_x_y.
          split;auto.
          intro abs.
          unfold is_free_block in neg_h_free_blck_m_x_y, abs.
          apply neg_h_free_blck_m_x_y.
          !intros.
          intro abs'.
          apply (abs perm).
          (* splitting in m -> m_pre_chain  -> m_chain *)
          assert (Mem.perm m_pre_chain x y Cur perm).
          { eapply Mem.perm_alloc_1 with (m1:=m);eauto. }
          !inversion h_exec_stmt_chain_param_Out_normal.
          unfold sp_proc in h_CM_eval_expr_vaddr.
          subst_det_addrstack_zero.
          unfold Mem.storev in heq_storev_v_m_chain.
          eapply Mem.perm_store_1 with (m1:=m_pre_chain);eauto. }
        clear h_unchanged_on_m_chain_m_init_params.
        autorename h_unchanged_on_m_chain_m_init_params0.
          
        assert (Mem.unchanged_on (forbidden st CE_proc g astnum e_initparams sp_proc m_init_params m_init_params) m_init_params m_locvarinit
                ∧ chained_stack_structure m_locvarinit (S (Datatypes.length CE_sufx)) sp_proc
                ∧ unchange_forbidden st CE_proc g astnum e_initparams e_locvarinit sp_proc m_init_params m_locvarinit).
        { !inversion h_exec_stmt_locvarinit;eq_same_clear.
          !inversion h_exec_stmt_Sskip_Out_normal.
          eapply init_locals_preserves_structure.
          - eapply build_compilenv_exact_lvl with (2:=heq_build_compilenv) ;eauto.
            eapply exact_lvlG_cut_until;eauto.
          - eapply build_compilenv_stack_no_null_offset with (3:=heq_build_compilenv);eauto.
            eapply exact_lvlG_cut_until;eauto.
          - eassumption.
          - assumption.
          - rewrite <- heq_lgth_CE_proc. assumption.
          - eapply chain_aligned.
            + eassumption.
            + omega.
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
    + eapply IHh_exec_stmt_stmt_t_outc;eauto.
    + eapply IHh_exec_stmt_stmt_t_outc;eauto.
  - destruct b.
    + eapply IHh_exec_stmt_stmt_t_outc;eauto.
    + eapply IHh_exec_stmt_stmt_t_outc;eauto.
  - specialize IHh_exec_stmt_stmt_t_outc1
      with (1:=h_wf_st_st) (2:=eq_refl _) (3:=h_strg_mtch_s_CE_m)
           (4:=h_chain_lvl_sp) (5:=h_inv_comp_CE_st) (6:=heq_transl_stmt0).
    (* Needing match_env preserved here. *)
    admit.
  (* specialize (IHh_exec_stmt_stmt_t_outc2 _ _ _ _ ?  heq0). *)
  (* transitivity of unchanged_on is proved in recent
     Compcert, by changing its definition. *)

  - !assert (chained_stack_structure m1 (Datatypes.length CE) sp
             ∧ (∀ astnum : ast_basics.astnum, Mem.unchanged_on (forbidden st CE g astnum e sp m m) m m1)).
    { eapply IHh_exec_stmt_stmt_t_outc1;eauto. }
    !assert (chained_stack_structure m2 (Datatypes.length CE) sp
             ∧ (∀ astnum : ast_basics.astnum, Mem.unchanged_on (forbidden st CE g astnum e1 sp m1 m1) m1 m2)).
    { eapply IHh_exec_stmt_stmt_t_outc2;eauto.
      - admit. (* need to enrich the property. *)
      - eapply IHh_exec_stmt_stmt_t_outc1;eauto. }
    eapply trans_unchanged with m1.
    + eapply h_and.
    + admit.
  - eapply IHh_exec_stmt_stmt_t_outc;eauto.
  - eapply IHh_exec_stmt_stmt_t_outc;eauto.
  
Admitted.




(* replacing match-env by strong_match_env + unchange_on (forbidden). *)
Lemma transl_stmt_normal_OK : forall stbl (stm:stmt) s norms',
    evalStmt stbl s stm norms' ->
    forall s' CE (stm':Cminor.stmt),
      norms' = OK s' ->
      invariant_compile CE stbl ->
      transl_stmt stbl CE stm = (Errors.OK stm') ->
      forall lvl spb ofs f locenv g m stkptr,
        lvl = Datatypes.length CE -> 
        stkptr = Values.Vptr spb ofs -> 
        chained_stack_structure m lvl stkptr ->
        strong_match_env stbl s CE stkptr locenv g m ->
        exists tr locenv' m',
          Cminor.exec_stmt g f stkptr locenv m stm' tr locenv' m' Out_normal
          /\ strong_match_env stbl s' CE stkptr locenv' g m'
          /\ chained_stack_structure m' lvl stkptr
          /\ forall astnum, unchange_forbidden stbl CE g astnum locenv locenv' stkptr m m'
                            /\ Mem.unchanged_on (forbidden stbl CE g astnum locenv stkptr m m) m m'.
Proof.
  !!intros until 1.
  Opaque transl_stmt.
  induction h_eval_stmt;simpl in *;intros ; rename_all_hyps ; eq_same_clear;
  try (
      let h := match goal with
               | H: transl_stmt _ _ _ = _ |- _ => H
               end in
      rewrite <- transl_stmt_ok in h;
      !functional inversion h;
      subst;
      try rewrite -> transl_stmt_ok in * ); eq_same_clear.
  (* Skip *)
  - eexists. eexists. eexists.
    repeat (apply conj;!!intros).
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
    decomp (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
    !!pose proof (ltac:(eapply strong_match_env_match_env with (1:= h_strg_mtch_s_CE_m))).
    !! (edestruct (me_stack_complete h_match_env);eauto).
    decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e _ _ _ _ _ _
                           h_eval_expr_e_e_v h_match_env).
    (* transl_type never fails *)
    assert (hex:exists nme_type_t, transl_type stbl nme_type =: nme_type_t).
    { simpl in *.
      assert (type_of_name stbl (Identifier astnum id) = Errors.OK nme_type).
      { simpl.
        rewrite heq_fetch_exp_type.
        reflexivity. }
      rename_all_hyps.
      eapply (ci_stbl_var_types_ok h_inv_comp_CE_stbl);eauto. }
    decomp hex.
    (* make_load does not fail on a translated variable coming from CE *)
    decomp (make_load_no_fail _ _ nme_t _ heq_transl_type).
    (* Cminor.eval_expr does not fail on a translated variable (invariant?) *)
    assert (hex: exists vaddr,
               Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t vaddr).
    { !destruct h_match_env.
      !destruct h_safe_cm_CE_m.
      unfold stack_match in h_stk_mtch_s_m.
      generalize (h_stk_mtch_s_m (Identifier astnum id) x nme_t load_addr_nme nme_type nme_type_t).
      intro h.
      !destruct h;auto.
      (* correction of type_of_name wrt to stbl_exp_type *)
      - simpl in heq_fetch_exp_type.
        simpl.
        rewrite heq_fetch_exp_type.
        reflexivity.
      - decomp h_and.
        unfold make_load in heq_make_load.
        destruct (Ctypes.access_mode nme_type_t) eqn:h;simpl in *;try discriminate.
        !invclear heq_make_load.
        !inversion h_CM_eval_expr_load_addr_nme_x0.
        exists nme_t_v.
        assumption. }
    (* A translated variable always results in a Vptr. *)
    !destruct hex.
    specialize transl_variable_Vptr with
    (1:=h_inv_comp_CE_stbl)
    (2:=(me_stack_localstack_aligned h_match_env.(me_safe_cm_env)))
      (3:=heq_transl_variable)
      (4:= h_CM_eval_expr_nme_t_nme_t_v).
    intro hex.
    decomp hex.
    (* Adresses of translated variables are always writable (invariant?) *)
    !assert (Mem.valid_access m nme_chk nme_block (Int.unsigned nme_ofst) Writable). {
      apply Mem.valid_access_implies with (p1:=Freeable).
      - !destruct h_match_env.
        !destruct h_safe_cm_CE_m.
        eapply h_freeable_CE_m;eauto.
        subst.
        assumption.
      - constructor 2. }
    eapply Mem.valid_access_store in h_valid_access_nme_block.
    !!destruct h_valid_access_nme_block as [m' ?].
    !assert (exec_stmt g f (Values.Vptr spb ofs) locenv m (Sstore nme_chk nme_t e_t)
                      Events.E0 locenv m' Out_normal). {
      econstructor;eauto.
      subst.
      simpl.
      eassumption. }
    exists m'.
    repeat (apply conj;!intros).
    * assumption.
    * !invclear h_exec_stmt.
      assert (e_t_v0 = e_t_v).
      { eapply det_eval_expr;eauto. }
      subst e_t_v0.
      !assert (match_env stbl s' CE (Values.Vptr spb ofs) locenv g m').
      { eapply assignment_preserve_match_env;eauto.
        !intros.
        subst.
        eapply eval_expr_overf;eauto. }
      up_type.
      
      apply assignment_preserve_chained_stack_structure_aux with (m:=m).
      admit. (* TODO strong match instead. *)
    *
  (* Assignment with satisifed range constraint (Range l u) *)
  - rename x into nme.
    rename st into stbl.
    rename_all_hyps.
    exists Events.E0.
    exists locenv.
    decomp (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
    !! (edestruct (me_stack_complete h_match_env);eauto).
    decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e _ _ _ _ _ _ h_eval_expr_e h_match_env).
      (* transl_type never fails *)
      assert (hex:exists nme_type_t, transl_type stbl nme_type =: nme_type_t).
      { simpl in *.
        assert (type_of_name stbl (Identifier astnum id) = OK nme_type).
        { simpl.
          rewrite heq_fetch_exp_type.
          reflexivity. }
        eapply (ci_stbl_var_types_ok h_inv_comp_CE_stbl);eauto. }
      decomp hex.
      (* make_load does not fail on a translated variable coming from CE *)
      decomp (make_load_no_fail stbl nme_type nme_t nme_type_t heq_transl_type).
      (* Cminor.eval_expr does not fail on a translated variable (invariant?) *)
      assert (hex: exists vaddr,
                 Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t vaddr).
      { !destruct h_match_env.
        unfold stack_match in h_stk_mtch_s_m.
        generalize (h_stk_mtch_s_m (Identifier astnum id) x nme_t load_addr_nme nme_type nme_type_t).
        intro h.
        !destruct h;auto.
        - simpl in *.
          rewrite heq_fetch_exp_type.
          reflexivity.
        - decomp h_and.
          unfold make_load in heq_make_load.
          destruct (Ctypes.access_mode nme_type_t) eqn:h;simpl in *;try discriminate.
          !invclear heq_make_load.
          !inversion h_CM_eval_expr_load_addr_nme_x0.
          exists nme_t_v.
          assumption. }
      (* A translated variable always results in a Vptr. *)
      !destruct hex.
      specialize transl_variable_Vptr with
      (1:=h_inv_comp_CE_stbl)
        (2:=(me_stack_localstack_aligned h_match_env.(me_safe_cm_env)))
        (3:=heq_transl_variable)
        (4:= h_CM_eval_expr_nme_t_nme_t_v).
      intro hex.
      decomp hex.
      (* Adresses of translated variables are always writable (invariant?) *)
      !assert (Mem.valid_access m nme_chk nme_block (Int.unsigned nme_ofst) Writable). {
        apply Mem.valid_access_implies with (p1:=Freeable).
        - !destruct h_match_env.
          !destruct h_safe_cm_CE_m.
          eapply h_freeable_CE_m;eauto.
          subst.
          assumption.
        - constructor 2. }
      eapply Mem.valid_access_store in h_valid_access_nme_block.
      destruct h_valid_access_nme_block.
      exists x0.
      !assert (exec_stmt g f (Values.Vptr spb ofs) locenv m (Sstore nme_chk nme_t e_t)
                         Events.E0 locenv x0 Out_normal). {
        econstructor;eauto.
        subst.
        simpl.
        eassumption. }
      split.
      * assumption.
      * up_type.
        !invclear h_exec_stmt.
        assert (e_t_v0 = e_t_v). {
          eapply det_eval_expr;eauto. }
        subst e_t_v0.
        constructor;eauto 7.
        -- eapply assignment_preserve_stack_match_CE;eauto.
        -- constructor;eauto 6.
        -- eapply assignment_preserve_stack_safe;eauto.
          !intros.
          !invclear heq.
          eapply eval_expr_overf;eauto.
  (* If statement --> true *)
  - rename x1 into b_then.
    rename x2 into b_else.
    rename_all_hyps.
    + decomp (transl_expr_ok _ _ _ e_t heq_tr_expr_e locenv g m _ _
                             (Values.Vptr spb ofs) h_eval_expr_e h_match_env).
      decomp (IHh_eval_stmt s' eq_refl CE b_then h_inv_comp_CE_st heq_transl_stmt_stmt_b_then spb ofs f
                            locenv g m h_match_env).
      exists tr.
      exists locenv'.
      exists m'.
      decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e locenv g m s _ (Values.Vptr spb ofs) h_eval_expr_e h_match_env).
      assert (exec_stmt g f (Values.Vptr spb ofs) locenv m
                        (Sifthenelse (Ebinop (Ocmp Cne) e_t (Econst (Ointconst Int.zero)))
                                     b_then b_else) tr locenv' m' Out_normal).
      { econstructor;eauto.
        * { econstructor;eauto.
            - econstructor;eauto.
              simpl.
              reflexivity.
            - simpl.
              reflexivity. }
        * inversion  heq_transl_value_e_t_v0.
          subst.
          econstructor.
        * rewrite  Int.eq_false;eauto.
          apply Int.one_not_zero. }
      split.
      * assumption.
      * assumption.
  (* If statement --> false *)
  - rename x1 into b_then.
    rename x2 into b_else.
    rename_all_hyps.
    + decomp (transl_expr_ok _ _ _ e_t heq_tr_expr_e locenv g m _ _
                             (Values.Vptr spb ofs) h_eval_expr_e h_match_env).
      decomp (IHh_eval_stmt s' eq_refl CE b_else h_inv_comp_CE_st heq_transl_stmt_stmt_b_else spb ofs f
                            locenv g m h_match_env).
      exists tr.
      exists locenv'.
      exists m'.
      decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e locenv g m s _ (Values.Vptr spb ofs) h_eval_expr_e h_match_env).
      assert (exec_stmt g f (Values.Vptr spb ofs) locenv m
                        (Sifthenelse (Ebinop (Ocmp Cne) e_t (Econst (Ointconst Int.zero)))
                                     b_then b_else) tr locenv' m' Out_normal).
      { econstructor;eauto.
        * { econstructor;eauto.
            - econstructor;eauto.
              simpl.
              reflexivity.
            - simpl.
              reflexivity. }
        * inversion  heq_transl_value_e_t_v0.
          subst.
          econstructor.
        * rewrite Int.eq_true.
          simpl.
          assumption. }
      split.
      * assumption.
      * assumption.
  (* Procedure call *)
  - rename x1 into chaining_expr.
    subst current_lvl.
    rename f0 into func.
    rename locals_section into f1'_l.
    rename params_section into f1'_p.
    specialize (IHh_eval_stmt ((n, f1'_l ++ f1'_p) :: s3) eq_refl).
    rewrite <- transl_stmt_ok in heq_transl_stmt_stm'.
    !functional inversion heq_transl_stmt_stm';subst;eq_same_clear; clear heq_transl_stmt_stm'.
    rename s1 into suffix_s .
    rename s3 into suffix_s'.
    rename y0 into lvl_p.
    rename x1 into args_t.
    rename x0 into p_sign.
    subst x3.
    subst current_lvl.
    rename n into pb_lvl.
    eq_same_clear.
    up_type.

    (* using the invariant to state that the procedure do
       translate to an address containing the translated code.  *)
    !!pose proof (me_stack_match_functions h_match_env.(me_safe_cm_env)).
    red in h_stk_mtch_fun.
    specialize (h_stk_mtch_fun _ _ _ h_fetch_proc_p).
    !!destruct h_stk_mtch_fun as [CE_prefx [CE_sufx [paddr [pnum [fction [lglobdef [? [? [? ?]]]]]] ]]].
    up_type.

    (* Core of the proof, link the different phase of execution with
       the pieces of code built by transl_procedure (in h_tr_proc). *)
    (* ideally functional inversion here would be great but it fails, bug(s) reported *)
    (* rewrite transl_procedure_ok in h_tr_proc. *)
    (* !functional inversion h_tr_proc. ;subst;eq_same_clear; clear heq_transl_stmt_stm'. *)
    (* ************** emulating functional inversion ********************** *)
    destruct pb eqn:heq_pb;eq_same_clear.
    rewrite <- ?heq_pb in h_fetch_proc_p. (* to re-fold pb where it didn't reduce. *)
    simpl in *.
    rename heq_transl_proc_pb into h_tr_proc. (* displays better with a short name. *)

    repeat match type of h_tr_proc with
           | (bind2 ?x _) = _  => destruct x as  [ [CE''_bld stcksize]|] eqn:heq_bldCE; simpl in h_tr_proc; try discriminate
           | context [ ?x <=? ?y ]  => let heqq := fresh "heq" in destruct (Z.leb x y) eqn:heqq; try discriminate
           | (bind ?y ?x) = _ =>
             let heqq := fresh "heq" in !destruct y !eqn:heqq; [ 
                                          match type of heqq with
                                          | transl_stmt _ _ _ = OK ?x => rename x into s_pbdy                   
                                          | init_locals _ _ _ = OK ?x => rename x into s_locvarinit
                                          | store_params _ _ _ = OK ?x => rename x into s_parms
                                          | copy_out_params _ _ _ = OK ?x => rename x into s_copyout
                                          | transl_lparameter_specification_to_procsig _ _ _ = OK ?x => rename x into p_sig
                                          | _ => idtac
                                          end
                                          ; autorename heqq; simpl in h_tr_proc
                                        | discriminate]
           end.
    up_type.
    !inversion h_tr_proc;clear h_tr_proc.
    simpl in heq.
    !invclear heq.
    match type of heq_find_func_paddr_fction with
    | (_ = Some (AST.Internal ?f)) => set (the_proc := f) in *
    end.
    up_type.
    (* ************** END OF emulating functional inversion ********************** *)
    (* more or less what functional inversion would have produced in one step *)
    (* CE' is the new CE built from CE and the called procedure parameters and local variables *)

    specialize (IHh_eval_stmt CE''_bld).
    rewrite heq_transl_stmt_procedure_statements_s_pbdy in IHh_eval_stmt.
    specialize (IHh_eval_stmt s_pbdy).
    assert (h_inv_CE''_bld:invariant_compile CE''_bld st).
    { eapply build_compilenv_preserve_invariant_compile;eauto.
      eapply invariant_compile_sublist with CE_prefx.
      assert (h_CE:CE_prefx ++ CE_sufx = CE).
      - eapply CompilEnv.cut_until_spec1;eassumption. (* Lemma todo *)
      - rewrite h_CE.
        assumption. }
    specialize (IHh_eval_stmt h_inv_CE''_bld eq_refl).

    unfold transl_params in heq_transl_params_p_x.
    unfold symboltable.fetch_proc in h_fetch_proc_p.
    rewrite h_fetch_proc_p in heq_transl_params_p_x.
    rewrite heq_pb in heq_transl_params_p_x.
    simpl in heq_transl_params_p_x.

    assert (heq_bldCE': build_compilenv st CE_sufx pb_lvl procedure_parameter_profile procedure_declarative_part =: (CE''_bld, stcksize))
      by assumption.
    apply compilenv_inv in heq_bldCE'.
    destruct heq_bldCE' as [sto [sto_sz [init_sto_sz [fr_prm heq_bldCE']]]].
    !!decompose [and] heq_bldCE'; clear heq_bldCE'.
    
    assert (hfrsh:fresh_params procedure_parameter_profile sto) by admit. (* spark typing *)
    assert (hnodup_arg:NoDupA eq_param_name procedure_parameter_profile) by admit. (* spark typing *)
    assert (hnodup_decl:NoDupA eq (decl_to_lident st procedure_declarative_part)) by admit. (* spark typing *)
    assert (heq_lgth_CE_sufx:Datatypes.length CE_sufx = pb_lvl).
    { erewrite (cut_until_CompilEnv.exact_levelG _ _ _ _ _ _ h_CEcut_CE_pb_lvl).
      reflexivity. }
    rewrite heq_lgth_CE_sufx in heq.
    !invclear heq.
    
    unfold newFrame in h_copy_in.
    !destruct f.
    destruct (copy_in_lvl _ _ _ _ _ _ _ h_copy_in) as [f h_pair].
    !inversion h_pair.
    !!destruct (copy_in_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _
                             h_match_env heq_transl_params_p_x h_copy_in) as [args_t_v ?].
    assert (h_ex:exists chaining_expr_from_caller_v,Cminor.eval_expr g (Values.Vptr spb ofs) locenv m chaining_expr chaining_expr_from_caller_v).
    { admit. (* invariant to add: The chaining parameter is always evaluable to a value (an address). *) }
    destruct h_ex as [chaining_expr_from_caller_v h_chaining_expr_from_caller_v].
    destruct (Mem.alloc m 0 (fn_stackspace the_proc)) as [m_proc_pre_init spb_proc] eqn:h_alloc.
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
    enough (h_ex:exists m_postfree trace_postfree v,
               eval_funcall g m (AST.Internal the_proc) (chaining_expr_from_caller_v :: args_t_v) trace_postfree m_postfree v
               /\ match_env st s' CE (Values.Vptr spb ofs) locenv g m_postfree).
    { destruct h_ex as [m_postfree [trace_postfree [ vres [h_decl_ok_exec h_decl_ok_matchenv]]]].
      exists trace_postfree locenv m_postfree.
      split.
      econstructor;eauto.
      - econstructor;eauto.
      - cbn.
        unfold transl_procsig in *.        
        rewrite  h_fetch_proc_p in heq_transl_procsig_p.
        rewrite heq_pb in heq_transl_procsig_p.
        cbn in heq_transl_procsig_p.
        rewrite heq_transl_lprm_spec_procedure_parameter_profile_p_sig in heq_transl_procsig_p.
        cbn in heq_transl_procsig_p.
        inversion heq_transl_procsig_p.
        reflexivity.
      - assumption. }

    enough (h_ex:exists locenv_postcpout m_postcpout trace_postcpout,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (fn_body the_proc) trace_postcpout locenv_postcpout m_postcpout Out_normal
               /\ exists m_postfree, Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree
               /\ match_env st s' CE (Values.Vptr spb ofs) locenv g m_postfree).
    { destruct h_ex as [locenv_postcpout [m_postcpout [trace_postcpout [h_exec_ok [m_postfree [h_free_ok h_matchenv_ok]]]]]].
      exists m_postfree trace_postcpout Values.Vundef.
      split.
      - econstructor;eauto.
        + rewrite <- Heqlocenv_init. eassumption.
        + cbn. reflexivity.
        + cbn. assumption.
      - assumption. }

    (* Same as above but just before the free performed at the end of funcall *)
    enough (h_ex:exists locenv_postcpout m_postcpout trace_postcpout,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (fn_body the_proc) trace_postcpout locenv_postcpout m_postcpout Out_normal
               /\ match_env st s' CE (Values.Vptr spb ofs) locenv g m_postcpout).
    { destruct h_ex as [locenv_postcpout [m_postcpout [trace_postcpout [h_exec_ok h_matchenv_ok]]]].
      exists locenv_postcpout m_postcpout trace_postcpout.
      split.
      - assumption.
      - destruct (Mem.free m_postcpout spb_proc 0 sto_sz) eqn:heq_free.
        + exists m0;split;auto.
          admit. (* no variable of CE and st are in m_postcpout, so the free maintains match_env. *)
        + admit. (* free is always possible on a stackframe (should be in the invariant). *)
    }

    enough (h_ex:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ forall locenv_caller,
                 match_env st (intact_s ++ suffix_s') CE (Values.Vptr spb ofs) locenv_caller g m_postbdy).
    { destruct h_ex as [locenv_postbdy [m_postbdy [trace_postbdy [h_exec_ok h_matchenv_ok]]]].
      !assert ( ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace),
                  exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postbdy m_postbdy
                            s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal).
      { admit. (* exec_stmt s_copyout does not raise any error *) }
      destruct h_ex as[locenv_postcpout [m_postcpout [trace_postcpout h_exec_ok2]]].
      exists locenv_postcpout m_postcpout (Events.Eapp trace_postbdy trace_postcpout).      
      split.
      - unfold the_proc at 2;cbn.
        apply exec_stmt_assoc.
        apply exec_stmt_assoc.
        econstructor;eauto.
      - 
        (* temporary patch before switching to strong_match: *)
        match goal with
        | H: context P [(match_env st (intact_s ++ suffix_s'))] |- _
          => let x := context P [(strong_match_env st (intact_s ++ suffix_s'))] in
             assert (h_str_matchenv_ok:x) by admit
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
              (forall locenv_caller, strong_match_env st s CE (Values.Vptr spb ofs) locenv_caller g m_postbdy) ->
              forall locenv,  strong_match_env st s' CE (Values.Vptr spb ofs) locenv g m_postcpout.
        Proof.
          !!intros until 1. 
          !induction h_copy_out_s_opt_s'; !!intros until 4; !!intros ? h_strg_mtch;try discriminate;subst;up_type.
          - !invclear heq.
            cbn in h_cpout_prm.
            !invclear h_cpout_prm.
            inversion h_exec_stmt_s_copyout;subst.
            apply h_strg_mtch.
          - rename n into real_param_name.
            rename v into param_v.
            intros locenv.
            specialize (IHh_copy_out_s_opt_s' s'0 g the_proc spb ofs spb_proc CE).
            rewrite copy_out_params_ok in h_cpout_prm.
            !functional inversion h_cpout_prm;subst;rewrite <- copy_out_params_ok in *.
            + (* In parameter, no problem *)
              !destruct h_or;
              match goal with
              | H: parameter_mode param = _, H': parameter_mode param = _ |- _ => rewrite H in H';discriminate
              end.
            + (* In or InOut *)
              clear h_or.
              rename x into chk. rename x0 into cpout_stmt. rename x1 into prm_nme_t.
              !inversion h_exec_stmt_s_copyout;try eq_same_clear.
              clear h_exec_stmt_s_copyout. (* should be useless now *)
              rename e1 into locenv_id_stored.
              rename m1 into m_id_stored.
              rename t2 into trace_id_stored.
              up_type.
              eapply IHh_copy_out_s_opt_s';eauto.
              intros locenv_caller. 


              admit. 

              enough (match_env st s' CE (Values.Vptr spb ofs) locenv_caller g m_id_stored).
              { admit. } (* temporary until strong_match_env everywhere *)
              assert (stack_match st s' CE (Values.Vptr spb ofs) locenv_caller g m_id_stored).
              { (* Need here something stating thate local variable correspond to params addresses. *)
                xxx
              }

              specialize (IHh_copy_out_s_opt_s' cpout_stmt m_postcpout m_id_stored locenv_postcpout trace_id_stored).

            

            cbn in h_cpout_prm.
            !assert ((compute_chnk_id st (parameter_name param)) = OK AST.Mint32).
            { admit. (* TODO *) }
            rewrite heq0 in h_cpout_prm.
            simpl in h_cpout_prm.
            !!destruct (copy_out_params st CE lparam) eqn:?; try discriminate.
            simpl in h_cpout_prm.
            !!destruct (transl_variable st CE 0%nat (parameter_name param)) eqn:?; try discriminate.
            simpl in h_cpout_prm.
            !destruct h_or.
            + rewrite heq1 in h_cpout_prm.
              !invclear h_cpout_prm.
              !inversion h_exec_stmt;subst;auto.
              * eapply IHh_copy_out_s_opt_s' ;eauto.
                specialize 
                  (IHh_copy_out_s_opt_s' s'0 g the_proc spb ofs spb_proc CE s0 m_postbdy m_postcpout locenv_postcpout t2 locenv_postbdy eq_refl h_inv_comp_CE_st heq h_cpout_prm_lparam_s0).
                apply IHh_copy_out_s_opt_s';auto.
                intros locenv.
                !assert (∀ locenv : env, strong_match_env st s'0 CE (Values.Vptr spb ofs) locenv g m_postcpout).
                { 
                eapply IHh_copy_out_s_opt_s';eauto.
              inversion h_exec_stmt;subst;eauto.
              eapply IHh_copy_out_s_opt_s';eauto.
              * 
            
            

            eapply IHh_copy_out_s_opt_s';eauto.
            + ec

            !assert (compute_chnk_id st (parameter_name param) =: ast_num_type).
            { admit. (* well formedness of st wrt to ast nums *) }
            rewrite heq_fetch_exp_type0 in h_cpout_prm.
            
            
        Qed.
        admit.
        (* copy_out property *)
      
      
      
    }



    enough (h_ex:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env st ((pb_lvl, f1'_l ++ f1'_p)::suffix_s') ((pb_lvl, sto)::CE_sufx)
                            (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy).
    { destruct h_ex as [locenv_postbdy [m_postbdy [trace_postbdy [h_exec_ok h_matchenv_ok]]]].
      !assert (strong_match_env st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto)::CE_sufx)
                                (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy).
      { admit. (* to be added (replace it actually) in the invariant *) }
      (* Just before cpout, the suffix of s match with the enclosing stack  *)
      assert (h_match_env_suffix_s': forall enclosingstack locenv_caller,
                 Mem.loadv AST.Mint32 m_postbdy (Values.Vptr spb_proc Int.zero) = Some enclosingstack ->
                 strong_match_env st suffix_s' CE_sufx enclosingstack locenv_caller g m_postbdy).
      { !intros.
        !inversion h_strg_mtch.
        rewrite heq2 in heq.
        !invclear heq.
        apply strong_match_env_inv_locenv with locenv0;assumption. }

      !assert ( ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace) m_postfree,
                   exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postbdy m_postbdy
                             s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
                   ∧ Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree).
      { admit. }
      destruct h_ex as[locenv_postcpout [m_postcpout [trace_postcpout [m_postfree [h_exec_ok2 h_free]]]]].
        

    enough (h_ex:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env st ((pb_lvl, f1'_l ++ f1'_p)::suffix_s') ((pb_lvl, sto)::CE_sufx)
                            (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy
               /\ ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace) m_postfree,
                   exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postbdy m_postbdy
                             s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
                   ∧ Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree).
    { destruct h_ex as
          [locenv_postbdy
             [m_postbdy
                [trace_postbdy [h_exec_ok [h_matchenv_ok [locenv_postcpout [m_postcpout [trace_postcpout [m_postfree [h_exec_ok2 h_free]]]]]]]]]].

      !assert (strong_match_env st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto)::CE_sufx)
                                (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy).
      { admit. (* to be added (replace it actually) in the invariant *) }

      (* Just before cpout, the suffix of s match with the enclosing stack  *)
      assert (h_match_env_suffix_s': forall enclosingstack locenv_caller,
                 Mem.loadv AST.Mint32 m_postbdy (Values.Vptr spb_proc Int.zero) = Some enclosingstack ->
                 strong_match_env st suffix_s' CE_sufx enclosingstack locenv_caller g m_postbdy).
      { !intros.
        !inversion h_strg_mtch.
        rewrite heq2 in heq.
        !invclear heq.
        apply strong_match_env_inv_locenv with locenv0;assumption. }

      assert (h_ex:exists intact_s', cut_until s' pb_lvl intact_s' suffix_s').
      { admit. (* property of copy_out *) }
      destruct h_ex as [intact_s' h_intact_s'].
      assert (s' = intact_s' ++ suffix_s'). {
        symmetry.
        eapply cut_until_spec1;eauto. }
      subst s'.
      assert (h_match_env_intact_s_suffix_ss: forall locenv_caller,
                 strong_match_env st (intact_s ++ suffix_s') CE (Values.Vptr spb ofs) locenv_caller g m_postbdy).
      { (* Hard part, needs the fact that intact_s did not change *) }                  
        
        assert (strong_match_env intact_s ).

      exists locenv_postcpout m_postcpout (Events.Eapp trace_postbdy trace_postcpout) m_postfree.
      split;[|split].
      - unfold the_proc at 2;cbn.
        apply exec_stmt_assoc.
        econstructor;eauto.
      - assumption.
      - 
      
      

XXXX

    enough (h_ex:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq
                         (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                            (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env st ((pb_lvl, f1'_l ++ f1'_p)::suffix_s') CE (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy
               /\ ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace) m_postfree,
                   exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postbdy m_postbdy
                             s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
                   /\ Mem.free m_postcpout spb_proc 0 sto_sz = Some m_postfree
                   /\ match_env st s' CE (Values.Vptr spb ofs) locenv g m_postfree).
    {
      destruct h_ex as
          [locenv_postbdy [m_postbdy [trace_postbdy [h_exec_ok [h_matchenv_ok [locenv_postcpout
                                                                                 [m_postcpout
                                                                                    [trace_postcpout
                                                                                       [ m_postfree
                                                                                           [h_exec_ok2 [h_free_ok h_matchenv_ok2]]]]]]]]]]].

      (* the suffix match before cpout *)
      assert (forall enclosingstack locenv_caller,
                 Mem.loadv AST.Mint32 m_postbdy (Values.Vptr spb_proc Int.zero) = Some enclosingstack ->
                 match_env st suffix_s' CE_sufx enclosingstack locenv_caller g m_postbdy).
      { !assert (strong_match_env st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE_sufx) (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy).
        { admit. (* TODO: put this in the invariant *) }
        !inversion H.
        !intros.
        rewrite heq2 in heq.
        !invclear heq.
        !inversion H9.
        - apply match_env_inv_locenv with locenv0;assumption.
        - apply match_env_inv_locenv with locenv0;assumption. }


      assert (match_env st (intact_s ++ suffix_s') CE (Values.Vptr spb ofs) locenv g m_postcpout).
      { 

      

      exists locenv_postcpout m_postcpout (Events.Eapp trace_postbdy trace_postcpout) m_postfree.
      split;[|split] ;try assumption.
      unfold the_proc at 2;cbn.
      apply exec_stmt_assoc.
      econstructor;eauto. }

    enough (h_ex:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq
                         (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                            (Sseq s_parms (Sseq s_locvarinit Sskip))) s_pbdy)
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env st (intact_s ++ suffix_s') CE (Values.Vptr spb_proc Int.zero) locenv_postbdy g m_postbdy).
    { destruct h_ex as [locenv_postbdy [m_postbdy [trace_postbdy [h_exec_ok h_matchenv_ok]]]].
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
          match_env st (intact_s ++ suffix_s') CE (Values.Vptr spb_proc ofs_proc) locenv_postbdy g m_postbdy ->
          (* strong_match implies that match_env suffix_s' CE_sufx (Vptr (Load^n 0) 0) holds too *)
          ∃ (locenv_postcpout : env) (m_postcpout : mem) (trace_postcpout : Events.trace),
            exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postbdy m_postbdy
                      s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
            /\ ∃ m_postfree, Mem.free m_postcpout spb_proc 0 (fn_stackspace the_proc) = Some m_postfree
                             /\ forall locenv, match_env st (intact_s' ++ suffix_s') CE (Values.Vptr spb_caller ofs) locenv g m_postfree.
        .

        admit. (* Separate lemma about copy_out_params vs copy_out. We need more hypothesis probably. *)
    }

       
    

    
    enough (h_ex:exists locenv_postdecl m_postdecl trace_postdecl,
            exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                      (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                            (Sseq s_parms (Sseq s_locvarinit Sskip)))
                      trace_postdecl locenv_postdecl m_postdecl Out_normal).


XXXx
    (* execute all the procedure except the cpout part. *)
    enough (h_ex:exists locenv_postbdy m_postbdy trace_postbdy,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                         (Sseq (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) (Sseq s_pbdy Sskip))
                         trace_postbdy locenv_postbdy m_postbdy Out_normal
               /\ match_env st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE_sufx) (Values.Vptr spb_proc Int.zero)
                              locenv_postbdy g m_postbdy
).
    { destruct h_ex as [locenv_postbdy [m_postbdy [trace_postbdy [h_decl_ok_exec h_decl_ok_matchenv]]]].
      assert({ m_postfree| Mem.free m_postbdy spb_proc 0 sto_sz = Some m_postfree}) as h_exT.
      { apply Mem.range_perm_free.
        !!pose proof Mem.perm_alloc_2 _ _ _ _ _ h_alloc.
        red.
        !intros.
        specialize (H ofs0 Cur h_and).
        admit. (* from H and no change in freeable status in compiled programs. *)
      }
      !!destruct h_exT as [m_postfree ?].
      exists m_postfree trace_postbdy Values.Vundef.
      pose (the_proc' := {|
            fn_sig := p_sig;
            fn_params := chaining_param :: transl_lparameter_specification_to_lident st procedure_parameter_profile;
            fn_vars := transl_decl_to_lident st procedure_declarative_part;
            fn_stackspace := sto_sz;
            fn_body := Sseq (Sseq
                               (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                     (Sseq s_parms (Sseq s_locvarinit Sskip))) (Sseq s_pbdy Sskip)) s_copyout |}).
      !!enough (eval_funcall g m (AST.Internal the_proc') (chaining_expr_from_caller_v :: args_t_v) trace_postbdy m_postfree Values.Vundef
              ∧ match_env st s' CE (Values.Vptr spb ofs) locenv g m_postfree).
      { admit. (* Lemma: associativity of Sseq wrt exec_stmt *) }
      !assert (fn_vars the_proc = fn_vars the_proc').
      { cbn.
        reflexivity. }
      !assert (fn_params the_proc = fn_params the_proc').
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

              enough (h_ex:exists locenv_postcpout m_postcpout trace_postcpout,
                         exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_init m_proc_pre_init
                                   s_copyout trace_postcpout locenv_postcpout m_postcpout Out_normal
                         /\ match_env st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE_sufx) (Values.Vptr spb_proc Int.zero)
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
          !!pose proof  Mem.valid_access_alloc_same _ _ _ _ _ h_alloc.
          reflexivity.
        + 



      Lemma copy_out_OK: forall intact_s suffix_s' pb_lvl f1'_p params args s',
          copy_out st (intact_s ++ suffix_s') (pb_lvl, f1'_p) params args (OK s') -> 
          match_env st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE_sufx) (Values.Vptr spb_proc Int.zero)
                    locenv_postbdy g m_postbdy -> 
          exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) 
      
xxxxx
      assert({ m_postfree| Mem.free m_postbdy spb_proc 0 sto_sz = Some m_postfree}) as h_exT.
      { apply Mem.range_perm_free.
        !!pose proof Mem.perm_alloc_2 _ _ _ _ _ h_alloc.
        red.
        !intros.
        specialize (H ofs0 Cur h_and).
        admit. (* from H and no change in freeable status in compiled programs. *)
      }
      !!destruct h_exT as [m_postfree ?].

XXXXXXXXXXX
    (* After executing intialization of parameters and local variables, we have the usual invariant back *)
    assert (h_ex:exists locenv_postdecl m_postdecl trace_postdecl,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_empty m_proc_pre_init
                         (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                               (Sseq s_parms (Sseq s_locvarinit Sskip))) 
                         trace_postdecl locenv_postdecl m_postdecl Out_normal
               /\ match_env st (f1 :: suffix_s) ((pb_lvl, sto) :: CE_sufx)
                            (Values.Vptr spb_proc Int.zero) locenv_postdecl g m_postdecl).
    { 
      (* After copying parameters into the stack we have a hybrid invariant: parameters are visible, but not local variables *)
      assert (h_ex:exists locenv_postprms m_postprms trace_postprms,
                 exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_empty m_proc_pre_init
                           (Sseq (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                                 s_parms)
                           trace_postprms locenv_postprms m_postprms Out_normal
                 /\ match_env st ((pb_lvl,f) :: suffix_s) ((pb_lvl, fst fr_prm) :: CE_sufx)
                              (Values.Vptr spb_proc Int.zero) locenv_postprms g m_postprms ).
      {
        (* Evaluating the first argument allows to link to the
           enclosing procedure, all variable accessible on the spark side
           are accessible with one more "load" than before. *)
        (* First we prove that there exists a resulting state *)
        assert (h_ex:exists locenv_postchain m_postchain trace_postchain,
                   exec_stmt g the_proc (Values.Vptr spb_proc Int.zero)
                             locenv_empty m_proc_pre_init
                             (Sstore AST.Mint32 (Econst (Oaddrstack Int.zero)) (Evar chaining_param))
                             trace_postchain locenv_postchain m_postchain Out_normal
                   /\ (stack_match st ((pb_lvl,nil) :: suffix_s) ((pb_lvl, nil) :: CE_sufx)
                                   (Values.Vptr spb_proc Int.zero) locenv_postchain g m_postchain)).
        { destruct (Mem.valid_access_store m_proc_pre_init AST.Mint32 spb_proc
                                           (Int.unsigned (Int.add Int.zero Int.zero))
                                           chaining_expr_from_caller_v) as [m_postchain h_m_postchain].
          { apply Mem.valid_access_freeable_any.
            eapply Mem.valid_access_alloc_same;eauto.
            - apply Int.unsigned_range.
            - simpl.
              rewrite Int.add_zero,Int.unsigned_zero; cbn.
              subst init_sto_sz.
              !!pose proof build_frame_lparams_mon_sz _ _ _ _ heq_bld_frm_procedure_parameter_profile.
              cbn in h_le.
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
            assert (h_stck_mtch_CE:=me_stack_match h_match_env).
            (* From the point of view of the caller, all variables visible in suffix_s are still there. *)
            !assert (stack_match st suffix_s CE (Values.Vptr spb ofs) locenv g m).
            { red.
              !intros.
              red in h_stck_mtch_CE.
              specialize (h_stck_mtch_CE nme v nme_t load_addr_nme typ_nme cm_typ_nme).
              !assert (evalName st s nme (OK v)).
              { admit. (* if it is mapped to v in suffix_s, then it is also in s (no clash name). *)  }
              specialize (h_stck_mtch_CE h_eval_name_nme_v0 heq_type_of_name heq_transl_name heq_transl_type heq_make_load).
              !!destruct h_stck_mtch_CE as [? [? ?]].
              exists load_addr_nme_v;split;auto. }

            !assert (stack_match st suffix_s CE_sufx (Values.Vptr spb ofs) locenv g m).
            { (* Lemma: taking a suffix of CE makes stack_match weaker *)
              red; !intros.
              eapply h_stk_mtch_suffix_s_m; try eassumption.
              admit. (* because CE is an extension of CE_sufx, without clash. *) }
            
            (* from the point of view of the called procedure, once the chaining arg has been copied to the stack,
               all previous variables visible from suffix_s are still visible but with one more load, due to the
               one more level in CE. *)
            (* reduce the size of the current goal *)
            clear - h_stk_mtch_suffix_s_m h_stk_mtch_suffix_s_m0 h_cut_until
                    h_m_postchain Heqlocenv_empty h_alloc h_chaining_expr_from_caller_v h_inv_CE''_bld.
            clearbody the_proc.
            red.
            !intros.

            (* We need to instantiate the stack_match hypothesis on something, we need first to prove that
                 [evalName st s nme (OK v)].
                 Sketch: 
                   -> [ evalName st ((pb_lvl, [ ]) :: suffix_s) nme (OK v)]
                   -> [evalName st suffix_s nme (OK v)]
                   -> [evalName st s nme (OK v)]
             *)
            !assert (evalName st suffix_s nme (OK v)).
            { (* should be lemma about empty top frame.  *)
              !inversion h_eval_name_nme_v.
              - constructor.
                cbn in heq_SfetchG_x.
                assumption.
              - admit. (* array *)
              - admit. (* record *) }
            (* ****************** *)
            (* Now we need to prove the other premisses of h_stk_mtch_suffix_s_m.
                 This is very painful for something trivial. *)
            !assert (exists δ nme_t_sub_indirections, nme_t = Ebinop Oadd nme_t_sub_indirections δ).
            { !functional inversion heq_transl_name.
              !functional inversion heq_transl_variable.
              unfold build_loads.
              eexists;eexists;eauto. }
            !!destruct h_ex as [δ [nme_t_sub_indirections ?]].
            subst nme_t.
            
            !assert (exists pb_lvl_sub, (pb_lvl = S pb_lvl_sub /\ CompilEnv.level_of_top CE_sufx = Some pb_lvl_sub)).
            { !!assert (h_ce_lvl := ci_exact_lvls _ _ h_inv_CE''_bld).
              !inversion h_exct_lvlG.
              destruct (Datatypes.length CE_sufx) eqn:heq_lgthCE_sufx.
              - apply length_zero_iff_nil in heq_lgthCE_sufx.
                subst.
                functional inversion heq_transl_name.
              - exists n;split;auto.
                !assert (invariant_compile CE_sufx st).
                { eapply invariant_compile_sublist with (CE1:=[(S n, sto)]);auto. }
                !!pose proof ci_exact_lvls _ _ h_inv_comp_CE_sufx_st.
                inversion h_exct_lvlG_CE_sufx0.
                + subst CE_sufx.
                  !inversion h_exct_lvlG;subst.
                  inversion heq.
                + cbn.
                  subst CE_sufx.
                  cbn in heq_lgthCE_sufx.
                  !inversion heq_lgthCE_sufx.
                  reflexivity. }
            !!destruct h_ex as [pb_sub_lvl [? ?]]; subst pb_lvl.

            !functional inversion heq_make_load;subst load_addr_nme.
            !functional inversion heq_transl_name.
            !functional inversion heq_transl_variable.
            subst.
            cbn in heq_lvloftop_m'.
            inversion heq_lvloftop_m'.
            subst m'; eq_same_clear.
            !assert (transl_name st CE_sufx (Identifier astnum id) =:
                                 Ebinop Oadd (build_loads_ (pb_sub_lvl - lvl_id))
                                 (Econst (Ointconst (Int.repr δ_id)))).
            { unfold transl_name.
              unfold transl_variable.
              simpl in heq_CEfetchG_id,heq_CEframeG_id.
              rewrite heq_CEfetchG_id,heq_CEframeG_id,heq_lvloftop_CE_sufx_pb_sub_lvl.
              unfold build_loads.
              reflexivity. }
            !assert (make_load (Ebinop Oadd (build_loads_ (pb_sub_lvl - lvl_id)) (Econst (Ointconst (Int.repr δ_id)))) cm_typ_nme
                               =: Eload chunk (Ebinop Oadd (build_loads_ (pb_sub_lvl - lvl_id)) (Econst (Ointconst (Int.repr δ_id))))).
            { unfold make_load.
              rewrite h_access_mode_cm_typ_nme.
              reflexivity. }

            red in h_stk_mtch_suffix_s_m0.
            pose proof (h_stk_mtch_suffix_s_m0
                          _ _ _ _ _ _
                          h_eval_name_nme_v0 heq_type_of_name heq_transl_name0 heq_transl_type heq_make_load0)
              as h_stk_mtch_suffix_s_m'.
            (* instantiation done *)
            (* ****************** *)
            !!destruct h_stk_mtch_suffix_s_m' as [v_t [? ?]].
            exists v_t.
            split;auto.
            !inversion h_CM_eval_expr_v_t.
            !inversion h_CM_eval_expr_vaddr.
            apply eval_Eload with (vaddr := vaddr).
            + remember (set_locals (fn_vars the_proc) (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc)))
                as locenv_postchain.
              apply eval_Ebinop with (v1:=v1) (v2:=v2);auto.
              * (* 1 loads are evaluated only from m, locenv is orthogonal.
                   2 there one more load than in h_CM_eval_expr_v1, but m_post_chain has one mode frame on the stack. *)
                admit.
              * (* lemma: a constant expression is evaluated indenpendently of the state, hence h_CM_eval_expr_v2 is sufficient *)
                admit.
            + (* 1 vaddr is the address of a spark variable in Cminor, which exists in m.
                 2 The only difference between m and m_postchain is the new frame (see h_alloc)
                   and the store on the chaining arg located in the new frame (h_m_postchain).
                 Hence the value stored at vaddr has not changed.  *)
              admit.
              (*TBC.*)
        }
        !!destruct h_ex as [locenv_postchain [m_postchain [trace_postchain [h_decl_ok_exec ?]]]].

xxxx
        assert (match_env st suffix_s CE_sufx (Values.Vptr spb_proc Int.zero) locenv_postchain g m_postchain).

        !assert (match_env st ((pb_lvl, nil) :: suffix_s) ((pb_lvl, nil) :: CE_sufx)
                           (Values.Vptr spb_proc Int.zero) locenv_postchain g m_postchain).
        { split.
          + apply h_stk_mtch.
          + admit.
          + up_type.
            pose proof (me_stack_match_functions h_match_env) as h_sck_mtch_fun.
            red in h_sck_mtch_fun.
            red.
            !intros.
            specialize (h_sck_mtch_fun p0 pb_lvl0 pb0 h_fetch_proc_p0).
            destruct h_sck_mtch_fun as [CE_prefx' [CE_sufx' [p0addr [p_id [p0_fundef [p_lsubprocs hand]]]]]].
            decomp hand.
            destruct (Compare.le_dec pb_lvl0 pb_lvl).
            * exists ((pb_lvl, [ ]) :: CE_prefx') CE_sufx' p0addr p_id p0_fundef p_lsubprocs.
              assert (Cminor.eval_expr g (Values.Vptr spb_proc Int.zero) locenv_postchain m_postchain
                                       (Econst (Oaddrsymbol (transl_procid p0) (Int.repr 0))) p0addr).
              { inversion h_CM_eval_expr_p0addr;subst.
                constructor;auto. }

              split;[|split];auto.
              apply CompilEnv.Cut_Until_Tail.
              -- simpl.
                 omega.
              -- assumption.
            

            

            rewrite transl_procedure_ok in heq_transl_proc_pb0.
            functional inversion heq_transl_proc_pb0.
                  
(*              


Lemma foo: forall CE (st : symboltable) pb pb_lvl res prfx,
    transl_procedure st CE pb_lvl pb = OK res ->
    invariant_compile CE st ->
    invariant_compile (List.app prfx CE) st ->
    transl_procedure st (List.app prfx CE) pb_lvl pb = OK res.
Proof.
  !!intros.
  

              Lemma foo: forall CE (st : symboltable) pb pb_lvl,
                  transl_procedure st ((Datatypes.length CE, nil) :: CE) pb_lvl pb = transl_procedure st CE pb_lvl pb.
              Proof.
                !!intros.
                rewrite transl_procedure_ok.
                !!functional induction function_utils.transl_procedure st CE pb_lvl pb
                  using transl_procedure_ind2
                with (P0:= fun enclosingCE (lvl : level) (decl : declaration) res =>
                             function_utils.transl_declaration st ((Datatypes.length enclosingCE, nil) :: enclosingCE) lvl decl = res )
                ;up_type.
                - simpl.
                  rewrite <- build_compilenv_ok in heq.
                  !functional inversion heq;subst.
                  unfold build_compilenv.
                  unfold stoszchainparam in *.
                  rewrite heq_bld_frm_lparams;simpl.
                  rewrite heq2;simpl.
                  rewrite heq_bool_true.
                  rewrite <- IHr.
xxxx


                functional induction (transl_procedure st CE pb_lvl' pb).
*)                
              admit.

              
            * inversion h_CM_eval_expr_x.
              constructor;auto.
            * assumption.
            
          + admit.
          + admit.
          + admit.
          + admit.
          + admit.
          + admit. }
            
        (* Storing values of parameters of the procedure. *)
        assert (h_ex:exists locenv_post_parms m_post_parms trace_post_parms,
               exec_stmt g the_proc (Values.Vptr spb_proc Int.zero)
                         locenv_postchain m_postchain  s_parms
                         trace_post_parms locenv_post_parms m_post_parms Out_normal
             /\ match_env st ((pb_lvl, f) :: suffix_s) ((pb_lvl, fst fr_prm) :: CE)
                          (Values.Vptr spb_proc Int.zero) locenv_post_parms g m_post_parms).
        {
          admit.
        }
        !!destruct h_ex as [locenv_postparms [m_postparms [trace_postparms [? ?]]]].
        exists locenv_postparms m_postparms (Events.Eapp trace_postchain trace_postparms).
        split.
        - eapply exec_Sseq_continue;eauto.
        - assumption.
      }
      destruct h_ex as [locenv_postprms [m_postprms [trace_postprms [h_decl_ok_exec h_decl_ok_matchenv]]]].
      admit.
    }
    destruct h_ex as [locenv_postdecl [m_postdecl [trace_postdecl [h_decl_ok_exec h_decl_ok_matchenv]]]].
    assert (h_ex:exists locenv_postcpout m_postcpout trace_postcpout m_postfree vres,
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
                match_env st ((pb_lvl, f1'_l ++ f1'_p)::s') ((pb_lvl, sto) :: CE) (Values.Vptr spb_proc Int.zero) locenv_postcpout g
                m_postcpout*)
               match_env st s' CE (Values.Vptr spb ofs) locenv g m_postfree).
    { 
      (* Executing the body of the procedure: induction hypothesis applies, match_env is preserved. *)
      assert (h_ex:exists locenv_postbdy m_postbdy trace_postbdy,
                 exec_stmt g the_proc (Values.Vptr spb_proc Int.zero) locenv_postdecl m_postdecl 
                           s_pbdy
                           trace_postbdy locenv_postbdy m_postbdy Out_normal
                 /\ match_env st ((pb_lvl, f1'_l ++ f1'_p) :: suffix_s') ((pb_lvl, sto) :: CE) (Values.Vptr spb_proc Int.zero)
                              locenv_postbdy g m_postbdy).
      { specialize (IHh_eval_stmt _ _ the_proc _ _ _ h_decl_ok_matchenv).
        destruct IHh_eval_stmt as [trace_postbdy [locenv_postbdy [m_postbdy [IH_exec_stmt IH_match_env] ]]].
        exists locenv_postbdy m_postbdy trace_postbdy;split;auto. }
      destruct h_ex as [locenv_postbdy [m_postbdy [trace_postbdy [h_bdy_ok_1 h_bdy_ok_2]]]].
      admit. (* Lemma about copy_out *) }
    destruct h_ex as [locenv_postcpout [m_postcpout [trace_postcpout [m_postfree [vres [ h_exec [h_outcome [h_vres h_matchenv ]]]]]]]].

    exists (Events.Eapp trace_postdecl trace_postcpout).
    exists (set_optvar None vres locenv) m_postfree.
    split.
    + eapply exec_Scall;eauto.
      * econstructor;eauto.
      * simpl.
        unfold transl_procsig in heq_transl_procsig_p.
        rewrite h_fetch_proc_p in heq_transl_procsig_p.
        rewrite heq_pb in heq_transl_procsig_p.
        simpl in heq_transl_procsig_p.
        rewrite heq_transl_lprm_spec_procedure_parameter_profile_p_sig in heq_transl_procsig_p.
        simpl in heq_transl_procsig_p.
        inversion heq_transl_procsig_p.
        reflexivity.
      * (* gather every intermediate parts together to get funcall ---> m_postfree *)
        eapply eval_funcall_internal with (e2:=locenv_postcpout) (out:=Out_normal);eauto.
        simpl fn_body.
        subst locenv_empty. 
        eapply exec_Sseq_continue.
        -- eapply h_decl_ok_exec.
        -- eapply h_exec.
        -- reflexivity.
    + simpl.
      assumption.
  (* Sequence *)
  - simpl in *.
    decomp (IHh_eval_stmt1 s1 eq_refl CE _ h_inv_comp_CE_st
                           heq1 spb ofs f  locenv g m h_match_env).
    decomp (IHh_eval_stmt2 s' eq_refl CE _ h_inv_comp_CE_st
                           heq0 spb ofs f _ _ _ h_match_env0).
    exists (Events.Eapp x1 x4).
    exists x5.
    exists x6.
    split.
    + econstructor;eauto.
    + assumption.
(* lots of shelved.  *)
Admitted.

    (* TODO: deal with lvl_p = 0. *)
