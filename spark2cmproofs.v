Require Import
 ZArith function_utils LibHypsNaming Errors spark2Cminor Cminor
 symboltable semantics semantics_properties Sorted Relations
 compcert.lib.Integers compcert_utils more_stdlib.
Require Import SetoidList.
Require Ctypes.
Import Symbol_Table_Module Memory.

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


(* Specialize the first arguments of a hypothesis *)
Inductive espec_rename:Type:=
  | ESPEC_Clear
  | ESPEC_Explicit
  | ESPEC_Automatic.

Ltac tac_especialize h keepeqn nme :=
  let tac x :=
      match keepeqn with
      | ESPEC_Clear => clear x
      | ESPEC_Explicit => rename x into nme
      | ESPEC_Automatic => idtac
      end in
  let t := type of h in
  match t with
    (?a -> ?b) =>
    let harg := fresh h "_arg" in
    assert (harg:a) ;[ | specialize (h harg); tac harg ]
  end.

Tactic Notation "especialize"  hyp(h) := let dummy := fresh in tac_especialize h ESPEC_Clear dummy.
Tactic Notation "especialize"  hyp(h) ":" "_" := especialize h.
Tactic Notation "especialize"  hyp(h) ":" "_" "_" := especialize h;[|especialize h].
Tactic Notation "especialize"  hyp(h) ":" "?" := let dummy := fresh in tac_especialize h ESPEC_Automatic dummy.
Tactic Notation "especialize"  hyp(h) ":" "?" "?" := especialize h : ? ; [|especialize h : ?].
Tactic Notation "especialize"  hyp(h) ":" "_" "?" := especialize h : _ ; [|especialize h : ?].
Tactic Notation "especialize"  hyp(h) ":" "?" "_" := especialize h : ? ; [|especialize h : _].
Tactic Notation "especialize"  hyp(h) ":" ident(id)  := tac_especialize h ESPEC_Explicit id.
Tactic Notation "especialize"  hyp(h) ":" ident(id) ident(id2)  :=
  tac_especialize h true id; [ | tac_especialize h true id2].




(** Hypothesis renaming stuff from other files *)
Ltac rename_hyp_prev h th :=
  match th with
  | NoDupA _ ?l => fresh "h_NoDupA_" l
  | NoDupA _ _ => fresh "h_NoDupA"
  | _ => (semantics_properties.rename_hyp1 h th)
  | _ => (spark2Cminor.rename_hyp1 h th)
  | _ => (compcert_utils.rename_hyp1 h th)
  end.

Ltac rename_hyp ::= rename_hyp_prev.

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
               | H: Some ?A = Some ?B |- _ => !inversion H
               | H: Normal ?A = Normal ?B |- _ => !inversion H
               | H: Normal ?A = Run_Time_Error ?B |- _ => discriminate H
               | H: Run_Time_Error ?B= Normal ?A |- _ => discriminate H
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

(* TODO: replace this y the real typing function *)
Definition type_of_name (stbl:symboltable) (nme:name): res type :=
  match nme with
  | E_Identifier astnum id =>
    match symboltable.fetch_exp_type astnum stbl with
      Some x => OK x
    | None =>  Error (msg "type_of_name: unknown type for astnum")
    end
  | E_Indexed_Component astnum x0 x1 =>
    match symboltable.fetch_exp_type astnum stbl with
      Some x => OK x
    | None =>  Error (msg "type_of_name: unknown type for astnum (indexed_component")
    end
  | E_Selected_Component astnum x0 x1 =>
    match symboltable.fetch_exp_type astnum stbl with
      Some x => OK x
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
  | expression => fresh "e"
  | statement => fresh "stmt"
  | Cminor.expr => match goal with
                   | H: transl_expr ?stbl ?CE ?x = OK h |- _ => fresh x "_t"
                   | H: transl_name ?stbl ?CE ?x = OK h |- _ => fresh x "_t"
                   end
  | AST.memory_chunk => match goal with
                   | H: compute_chnk ?stbl ?x = OK h |- _ => fresh x "_chk"
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
    | H:  eval_expr _ _ ?e (Normal h) |- _ => fresh e "_v"
    | H:  eval_expr _ _ ?e h |- _ => fresh e "_v"
    end
  | _ => (rename_hyp_prev h th)
  end.

Ltac rename_hyp ::= rename_hyp1.

Lemma transl_value_det: forall v tv1 tv2,
    transl_value v tv1 -> transl_value v tv2 -> tv1 = tv2.
Proof.
  !intros.
  inversion heq_transl_value_v_tv1; inversion heq_transl_value_v_tv2;subst;auto;inversion H1;auto.
Qed.

(* clear may fail if h is not a hypname *)
(* Tactic Notation "decomp" constr(h) := *)
(*        !! (decompose [and ex or] h). *)

Lemma transl_value_tot: forall v,
    (forall y:nat,(exists b, v = Bool b \/ exists n, v = Int n))
    -> exists tv, transl_value v tv.
Proof.
  !intros.
  decomp (H 0%nat);subst.
  - destruct x;eexists;econstructor.
  - eexists;econstructor.
Qed.


Lemma transl_literal_ok1 : forall g (l:literal) v,
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

Lemma transl_literal_ok2 : forall g (l:literal) v,
    eval_literal l (Normal v) ->
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
(* shortening the name to shorten the tactic below *)
Notation rtc_binop := do_run_time_check_on_binop (only parsing).
Ltac inv_rtc :=
  repeat
    progress
    (try match goal with
         | H: rtc_binop ?op Undefined _ (Normal _) |- _ => now inversion H
         | H: rtc_binop ?op _ Undefined (Normal _) |- _ => now inversion H
         | H: rtc_binop ?op _ (ArrayV _) (Normal _) |- _ => now inv_if_intop op H
         | H: rtc_binop ?op (ArrayV _) _ (Normal _) |- _ => now inv_if_intop op H
         | H: rtc_binop ?op _ (RecordV _) (Normal _) |- _ => now inv_if_intop op H
         | H: rtc_binop ?op (RecordV _) _ (Normal _) |- _ => now inv_if_intop op H
         | H: rtc_binop ?op _ (Bool _) (Normal _) |- _ => inv_if_intop op H
         | H: Math.binary_operation ?op _ (Bool _) = (Some _) |- _ => inv_if_intop op H
         | H: rtc_binop ?op (Bool _) _ (Normal _) |- _ => inv_if_intop op H
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
  !destruct v1;try discriminate; !destruct v2;try discriminate;simpl in *.
  eq_same_clear.
  inversion heq_transl_value_v1_x;subst;simpl.
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

Lemma add_ok : forall v v1 v2 n1 n2,
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
    do_run_time_check_on_binop Minus v1 v2 (Normal v) ->
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
    do_run_time_check_on_binop Multiply v1 v2 (Normal v) ->
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
Qed.


(** * Memory invariant and bisimilarity *)


Lemma eval_literal_overf : forall (l:literal) n,
    eval_literal l (Normal (Int n)) ->
    do_overflow_check n (Normal (Int n)).
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
    do_overflow_check n (Normal (Int n)).

(** Hypothesis renaming stuff *)
Ltac rename_hyp2' h th :=
  match th with
  | safe_stack ?s => fresh "h_safe_stack_" s
  | safe_stack _ => fresh "h_safe_stack"
  | _ => rename_hyp2 h th
  end.

Ltac rename_hyp ::= rename_hyp2'.

Lemma eval_name_overf: forall s st nme n,
    safe_stack s
    -> eval_name st s nme (Normal (Int n))
    -> do_overflow_check n (Normal (Int n)).
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
      eval_expr st s e (Normal (Int n)) ->
      do_overflow_check n (Normal (Int n)).
Proof.
  !intros.
  revert h_safe_stack_s.
  remember (Normal (Int n)) as hN.
  revert HeqhN.
  !induction h_eval_expr_e;!intros;subst;try discriminate.
  - eapply eval_literal_overf;eauto.
  - eapply eval_name_overf;eauto.
  - !invclear h_do_rtc_binop.
    + inversion h_overf_check;subst;auto.
    + inversion h_overf_check;subst;auto.
    + rewrite binopexp_ok in *.
      functional inversion heq;subst
      ;try match goal with H: ?A <> ?A |- _ => elim H;auto end.
  - !invclear h_do_rtc_unop.
    + inversion h_overf_check;subst;auto.
    + rewrite unopexp_ok in *.
      !functional inversion heq;subst
      ;try match goal with H: ?A <> ?A |- _ => elim H;auto end.
      !invclear heq.
      apply IHh_eval_expr_e;auto.
Qed.

Lemma eval_expr_overf2 : forall st s,
    safe_stack s ->
    forall (e:expression) e_v,
      eval_expr st s e (Normal e_v) -> check_overflow_value e_v.
Proof.
  !intros.
  destruct e_v;simpl in *;auto.
  eapply eval_expr_overf;eauto.
Qed.

Hint Resolve eval_expr_overf2.

Definition stack_complete stbl s CE := forall a nme addr_nme,
    transl_variable stbl CE a nme = OK addr_nme
    -> exists v, eval_name stbl s (E_Identifier a nme) (Normal v).

Definition stack_no_null_offset stbl CE := forall a nme δ_lvl δ_id,
    transl_variable stbl CE a nme = OK (build_loads δ_lvl δ_id) ->
    4 <= Int.unsigned (Int.repr δ_id).

(* CE gives the maximum number of loads. *)
Definition stack_localstack_aligned (CE:compilenv) locenv g m := forall b δ_lvl v,
    (δ_lvl < Datatypes.length CE)%nat -> 
    Cminor.eval_expr g b locenv m (build_loads_ δ_lvl) v ->
    exists b', v = Values.Vptr b' Int.zero.

(* The spark dynamic and the compiler static stack have the same structure. *)
Definition stack_match_CE (s : STACK.stack) (CE : compilenv) :=
  forall nme lvl sto,
    STACK.frameG nme s = Some (lvl,sto) ->
    exists CE_sto,
    CompilEnv.frameG nme CE = Some (lvl,CE_sto).


(* Observationnal equivalence of the spark dynamic stack and the compile environment. *)
Definition stack_match st s CE sp locenv g m :=
  forall nme v addr_nme load_addr_nme typ_nme cm_typ_nme,
    eval_name st s nme (Normal v) ->
    type_of_name st nme = OK typ_nme ->
    transl_name st CE nme = OK addr_nme ->
    transl_type st typ_nme = OK cm_typ_nme ->
    make_load addr_nme cm_typ_nme = OK load_addr_nme ->
    exists v_t,
      (transl_value v v_t /\
       Cminor.eval_expr g sp locenv m load_addr_nme v_t).


(* We have translated all procedures of stbl, and they have all an address
   pointing to there translation *)
Definition stack_match_functions st stckptr CE locenv g m :=
  forall p pb_lvl pb,
    symboltable.fetch_proc p st = Some (pb_lvl, pb) (* p exists in st *)
    -> exists CE' CE'' paddr pnum fction lglobdef, (* then there we can compute its address in Cminor. *)
      CompilEnv.cut_until CE pb_lvl CE' CE''
      ∧ transl_procedure st CE'' pb_lvl pb = OK ((pnum,@AST.Gfun _ _ fction) :: lglobdef) (*  *)
      ∧ Cminor.eval_expr g stckptr locenv m
                         (Econst (Oaddrsymbol (transl_procid p) (Int.repr 0))) paddr
      ∧ Globalenvs.Genv.find_funct g paddr = Some fction.


(* Variable addresses are all disjoint *)
Definition stack_separate st CE sp locenv g m :=
  forall nme nme' addr_nme addr_nme'
         typ_nme typ_nme'  cm_typ_nme cm_typ_nme'
         k₁ δ₁ k₂ δ₂ chnk₁ chnk₂ ,
    type_of_name st nme = OK typ_nme ->
    type_of_name st nme' = OK typ_nme' ->
    transl_name st CE nme = OK addr_nme ->
    transl_name st CE nme' = OK addr_nme' ->
    transl_type st typ_nme = OK cm_typ_nme ->
    transl_type st typ_nme' = OK cm_typ_nme' ->
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
    transl_variable st CE a id = OK id_t ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g sp locenv m id_t (Values.Vptr b ofs) ->
    (* Size of variable in Cminor memorry *)
    compute_chnk st (E_Identifier a id) = OK chk ->
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

Definition all_addr_no_overflow CE := forall id δ,
    CompilEnv.fetchG id CE = Some δ -> 0 <= δ < Integers.Int.modulus.

Definition upper_bound fr sz := forall nme nme_ofs,
    CompilEnv.fetches nme fr = Some nme_ofs -> Zlt nme_ofs sz.

(** levels in the global stack match exactly their nesting levels. *)
Inductive exact_levelG:  CompilEnv.stack -> Prop :=
  | exact_levelG_nil: exact_levelG nil
  | exact_levelG_cons: ∀ stk fr,
      exact_levelG stk -> exact_levelG ((List.length stk, fr)::stk).

(* the global stack is in incresing level. *)
(* Lemma exact_level_increasing_orderG: ∀ stk: CompilEnv.stack, *)
(*     exact_levelG stk -> StronglySorted gt_fst stk. *)

Definition stbl_var_types_ok st :=
  ∀ nme t, type_of_name st nme = OK t ->
           ∃ nme_type_t, transl_type st t = OK nme_type_t.

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
   Its translation is currently (an expression of the form
   ELoad((Eload(Eload ...(Eload(0)))) + n)).
 - spark variables and there translated address yield the same
   (translated) value. i.e. the two memories commute. *)
Record match_env st s CE sp locenv g m: Prop :=
  mk_match_env {
      me_stack_match: stack_match st s CE sp locenv g m;
      me_stack_match_CE: stack_match_CE s CE;
      me_stack_match_functions: stack_match_functions st sp CE locenv g m ;
      me_stack_complete: stack_complete st s CE;
      me_stack_separate: stack_separate st CE sp locenv g m;
      me_stack_localstack_aligned: stack_localstack_aligned CE locenv g m;
      me_stack_no_null_offset: stack_no_null_offset st CE;
      me_stack_freeable: stack_freeable st CE sp g locenv m;
      me_overflow: safe_stack s; (* Put this somewhere else, concerns only s *)
(*       me_nodup_stack: NoDupA  *)
    }.

Arguments me_stack_match : default implicits.
Arguments me_stack_match_CE : default implicits.
Arguments me_stack_match_functions : default implicits.
Arguments me_overflow : default implicits.
Arguments me_stack_no_null_offset : default implicits.
Arguments me_stack_localstack_aligned : default implicits.
Arguments me_stack_separate : default implicits.
Arguments me_stack_freeable : default implicits.
Arguments me_stack_complete : default implicits.

(** The compilation environment has some intrinsic properties:
 - Frame are numbered in increasing order in the global store
 - In each frame variables are numbered in increasing order
 - variable addresses do not overflow. *)
Record invariant_compile CE stbl :=
  { ci_exact_lvls: exact_levelG CE ;
    ci_increasing_ids: all_frm_increasing CE ;
    ci_no_overflow: all_addr_no_overflow CE ;
    ci_stbl_var_types_ok: stbl_var_types_ok stbl }.

Arguments ci_increasing_ids : default implicits.
Arguments ci_no_overflow : default implicits.
Arguments ci_stbl_var_types_ok : default implicits.

Hint Resolve ci_exact_lvls ci_increasing_ids ci_no_overflow ci_stbl_var_types_ok.
Hint Resolve me_stack_match me_stack_match_CE me_stack_match_functions me_stack_complete me_stack_separate me_stack_localstack_aligned me_stack_no_null_offset me_overflow.


(** Hypothesis renaming stuff *)
Ltac rename_hyp3 h th :=
  match th with
  | upper_bound ?fr ?sz => fresh "h_upb_" fr "_" sz
  | upper_bound ?fr _ => fresh "h_upb_" fr
  | upper_bound _ _ => fresh "h_upb"
  | match_env _ _ _ _ _ _ _ => fresh "h_match_env"
  | stack_match _ ?s _ _ _ _ ?m => fresh "h_stk_mtch_" s "_" m
  | stack_match _ _ _ _ _ _ _ => fresh "h_stk_mtch"
  | stack_match_CE ?s ?CE => fresh "h_stk_mtch_CE_" s "_" CE
  | stack_match_CE ?s _ => fresh "h_stk_mtch_CE_" s
  | stack_match_CE _ _ => fresh "h_stk_mtch_CE"
  | stack_match_functions _ _ _ _ _ _ => fresh "h_stk_mtch_fun"
  | stack_complete _ ?s ?CE => fresh "h_stk_cmpl_" s "_" CE
  | stack_complete _ ?s _ => fresh "h_stk_cmpl_" s
  | stack_complete _ _ _ => fresh "h_stk_cmpl"
  | stack_localstack_aligned _ _ ?g ?m => fresh "h_aligned_" g "_" m
  | stack_localstack_aligned _ _ _ ?m => fresh "h_aligned_" m
  | stack_localstack_aligned _ _ ?g _ => fresh "h_aligned_" g
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
  | invariant_compile ?CE ?stbl => fresh "h_inv_comp_" CE "_" stbl
  | invariant_compile ?CE _ => fresh "h_inv_comp_" CE
  | invariant_compile _ ?stbl => fresh "h_inv_comp_" stbl
  | invariant_compile _ _ => fresh "h_inv_comp"
  | increasing_order ?l => fresh "h_incr_gt_" l
  | increasing_order _ => fresh "h_incr_ord"
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

Definition eq_param_name p1 p2 := p1.(parameter_name) = p2.(parameter_name).

(* Properties of compile_env *)
Lemma exact_levelG_sublist: forall x CE,
    exact_levelG (x::CE)
    -> exact_levelG CE.
Proof.
  intros x CE H.
  inversion H;cbn in *;auto.
Qed.

Lemma cut_until_exact_levelG:
  forall s pb_lvl s' s'' ,
    exact_levelG s ->
    (pb_lvl <= Datatypes.length s)%nat ->
    CompilEnv.cut_until s pb_lvl s'  s'' ->
    pb_lvl = Datatypes.length s''.
Proof.
  intros s pb_lvl s' s'' h_exactlvlG.
  revert pb_lvl s' s''.
  induction h_exactlvlG;simpl;intros ? ? ? h_lt h_cut.
  - inversion h_cut;subst;simpl in *.
    omega.
  - inversion h_lt;subst.
    + clear h_lt.        
      inversion h_cut;subst.
      * reflexivity.
      * simpl in *.
        exfalso;omega.
    + simpl in *.
      inversion h_cut;subst;simpl in *.
      * exfalso;omega.
      * eapply IHh_exactlvlG;eauto.
Qed.

Lemma cut_until_exact_levelG_2:
  forall s pb_lvl s' s'' ,
    exact_levelG s ->
    (pb_lvl > Datatypes.length s)%nat ->
    CompilEnv.cut_until s pb_lvl s'  s'' ->
    Datatypes.length s = Datatypes.length s''.
Proof.
  intros s pb_lvl s' s'' h_exactlvlG.
  !destruct h_exactlvlG;simpl;!intros.
  - inversion H0.
    reflexivity.
  - inversion H0;simpl in *;subst.
    + reflexivity.
    + exfalso;omega.
Qed.

Lemma all_frm_increasing_sublist: forall x CE,
    all_frm_increasing (x::CE)
    -> all_frm_increasing CE.
Proof.
  intros x CE H.
  inversion H;cbn in *;auto.
Qed.

Lemma all_addr_no_overflow_sublist: forall x CE,
    all_addr_no_overflow (x::CE)
    -> all_addr_no_overflow CE.
Proof.
  intros x CE H.
  red in H.
  red.
  intros id δ H0.
  apply H with id.
  simpl.
  destruct (CompilEnv.fetch id x).
  - admit. (* We need the fact that there are no clash of names in CE *)
  - assumption.
Qed.

Lemma invariant_compile_subcons: forall st x CE,
    invariant_compile (x::CE) st
    -> invariant_compile CE st.
Proof.
  intros st x CE H.
  inversion H;cbn in *.
  split;eauto.
  - eapply exact_levelG_sublist;eauto.
  - eapply all_frm_increasing_sublist;eauto.
  - eapply all_addr_no_overflow_sublist;eauto.
Qed.

Lemma invariant_compile_sublist: forall st CE1 CE2,
    invariant_compile (CE1 ++ CE2) st
    -> invariant_compile CE2 st.
Proof.
  induction CE1;simpl.
  - auto.
  - intros CE2 H.
    apply IHCE1.
    apply invariant_compile_subcons with (x:=a).
    assumption.
Qed.



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

Record CE_well_formed CE :=
  { ce_wf_intra:> stack_CE_NoDup CE;
    ce_wf_extra:> stack_CE_NoDup_G CE }.

Arguments ce_wf_intra : default implicits.
Arguments ce_wf_extra : default implicits.

Hint Resolve ce_wf_extra ce_wf_extra.

Inductive strong_match_env stbl: STACK.stack → compilenv → Values.val → env → genv → mem → Prop :=
| C1: forall v locenv g m,
    match_env stbl [] [] v locenv g m ->
    strong_match_env stbl [] [] v locenv g m
| C2: forall lvl sto s stoCE CE v v' locenv locenv' g m,
    strong_match_env stbl s CE v locenv g m ->
    Mem.loadv AST.Mint32 m v' = Some v ->
    match_env stbl ((lvl,sto)::s) ((lvl,stoCE)::CE) v' locenv' g m ->
    strong_match_env stbl ((lvl,sto)::s) ((lvl,stoCE)::CE) v' locenv' g m.

(* Equivalently
 *)


Inductive repeat_Mem_loadv (chk:AST.memory_chunk) (m : mem): forall (lvl:STACK.scope_level) (sp sp' : Values.val), Prop :=
| Repeat_loadv1: forall sp, repeat_Mem_loadv chk m O sp sp
| Repeat_loadv2: forall lvl sp sp' sp'',
    repeat_Mem_loadv chk m lvl sp' sp'' ->
    Mem.loadv AST.Mint32 m sp = Some sp' ->
    repeat_Mem_loadv chk m (S lvl) sp sp''.


Definition strong_match_env_2 (st : symboltable.symboltable) (s : STACK.stack) (CE : compilenv)
           (sp : Values.val) (locenv : env) (g : genv) (m : mem) : Prop :=
  forall lvl CE' CE'',
    CompilEnv.cut_until CE lvl CE' CE'' ->
    Datatypes.length CE'' = lvl ->
    exists sp'',
      (* following chaining params starting from the current one *)
      repeat_Mem_loadv AST.Mint32 m lvl sp sp''
      ∧ exists s' s'' locenv'', STACK.cut_until s lvl s' s''  ∧  match_env st s'' CE'' sp'' locenv'' g m.


Ltac rename_hyp_strong h th :=
  match th with
  | exact_levelG ?CE => fresh "h_exct_lvl_" CE
  | exact_levelG ?CE => fresh "h_exct_lvl"

  | repeat_Mem_loadv _ ?m ?lvl ?v ?sp => fresh "h_repeat_loadv_" lvl "_" v
  | repeat_Mem_loadv _ ?m ?lvl ?v ?sp => fresh "h_repeat_loadv_" lvl
  | repeat_Mem_loadv _ ?m ?lvl ?v ?sp => fresh "h_repeat_loadv"

  | CompilEnv.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_CEcut_" CE "_" lvl
  | CompilEnv.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_CEcut_" CE
  | CompilEnv.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_CEcut"
  | STACK.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_stkcut_" CE "_" lvl
  | STACK.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_stkcut_" CE
  | STACK.cut_until ?CE ?lvl ?CE' ?CE'' => fresh "h_stkcut"

  | strong_match_env ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch_" s "_" CE "_" m
  | strong_match_env ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch_" s "_" CE
  | strong_match_env ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch_" s
  | strong_match_env ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch"

  | strong_match_env_2 ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch2_" s "_" CE "_" m
  | strong_match_env_2 ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch2_" s "_" CE
  | strong_match_env_2 ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch2_" s
  | strong_match_env_2 ?st ?s ?CE ?sp ?locenv ?g ?m => fresh "h_strg_mtch2"

  | _ => rename_hyp4 h th
  end.
Ltac rename_hyp ::= rename_hyp_strong.


Lemma exact_lvlG_lgth: forall CE lvl,
    exact_levelG CE ->
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
    exact_levelG CE ->
    CompilEnv.level_of_top CE = None ->
    List.length CE = 0%nat.
Proof.
  intros CE H H0.
  destruct CE;cbn in *;try discriminate;auto.
  destruct f;try discriminate.
Qed.



Lemma exact_lvlG_cut_until: forall CE lvl CE' CE'',
    exact_levelG CE ->
    CompilEnv.cut_until CE lvl CE' CE'' ->
    exact_levelG CE''.
Proof.
  !!intros until 1.
  revert lvl CE' CE''.
  !induction h_exct_lvl_CE;!intros .
  - !inversion h_CEcut;subst.
    constructor.
  - !inversion h_CEcut.
    + constructor.
      assumption.
    + eapply IHh_exct_lvl_CE;eauto.
Qed.



Lemma exact_lvlG_nil_left: forall CE,
  exact_levelG CE ->
  CompilEnv.cut_until CE (Datatypes.length CE) [ ] CE.
Proof.
  intros CE.
  destruct CE;simpl;!intros.
  - constructor.
  - constructor.
    inversion h_exct_lvl.
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

Lemma stack_match_CE_empty: stack_match_CE [] [].
Proof.
  red;!intros.
  functional inversion heq.
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
 

Lemma match_env_empty: forall st sp sp' locenv locenv' g m,
    stack_match_functions st sp' [ ] locenv' g m ->
    match_env st [ ] [ ] sp locenv g m.
Proof.
  !intros.
  split (* apply h_match_env. *).
  + apply stack_match_empty.
  + red;!intros.
    functional inversion heq.
  + red;!intros.
    red in h_stk_mtch_fun.
    specialize (h_stk_mtch_fun _ _ _ h_fetch_proc_p).
    !!decomp h_stk_mtch_fun.
    rename x into CE'.
    rename x0 into CE''.
    rename x1 into paddr.
    rename x2 into pnum.
    rename x3 into fdef.
    rename x4 into fdef_t.
    up_type.
    exists CE' CE'' paddr pnum fdef fdef_t.
    repeat split;auto.
    constructor.
    inversion h_CM_eval_expr_x1;subst; simpl in *.
    assumption.
  + red;!intros.
    !functional inversion heq_transl_variable.
    functional inversion heq_CEfetchG_nme.
  + red;!intros.
    functional inversion heq_transl_name.
  + red.
    !intros.
    simpl in *.
    exfalso;omega.
  + red;!intros.
    !functional inversion heq_transl_variable.
    functional inversion heq_CEfetchG_nme.
  + red.
    !intros.
    exfalso.
    !functional inversion heq_transl_variable.
    functional inversion heq_CEfetchG_id.
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



Lemma eval_expr_build_loads__inv_locenv :  forall δ_lvl g sp locenv m  nme_t_v,
    Cminor.eval_expr g sp locenv m (build_loads_ δ_lvl) nme_t_v ->
    forall locenv',
      Cminor.eval_expr g sp locenv' m (build_loads_ δ_lvl) nme_t_v.
Proof.
  intros δ_lvl.
  !!(induction δ_lvl;simpl;intros).
  - eapply eval_expr_Econst_inv_locenv;eauto.
  - inversion h_CM_eval_expr_nme_t_v.
    econstructor;eauto.
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
  - eapply eval_expr_build_loads__inv_locenv;eauto.
  - eapply eval_expr_Econst_inv_locenv;eauto.
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
  specialize (h_stk_mtch_s_m nme v nme_t load_addr_nme typ_nme cm_typ_nme h_eval_name_nme_v heq_type_of_name heq_transl_name heq_transl_type heq_make_load).
  !!destruct h_stk_mtch_s_m as [? [? ?]].
  exists load_addr_nme_v;split;auto.
  !functional inversion heq_make_load;subst.
  !inversion h_CM_eval_expr_load_addr_nme_load_addr_nme_v.
  econstructor;eauto.
  !functional inversion heq_transl_name;subst.
  !functional inversion heq_transl_variable;subst.
  eapply eval_expr_build_load_inv_locenv;eauto.
Qed.

Lemma eval_expr_transl_variable_inv_locenv: forall st CE astnum g sp locenv m nme nme_t v,
          transl_variable st CE astnum nme = OK nme_t ->
          Cminor.eval_expr g sp locenv m nme_t v ->
          forall locenv', Cminor.eval_expr g sp locenv' m nme_t v.
Proof.
  !intros.
  !functional inversion heq_transl_variable;subst.
  eapply eval_expr_build_load_inv_locenv;eauto.
Qed.

Lemma eval_expr_transl_name_inv_locenv: forall st CE  g sp locenv m nme nme_t v,
          transl_name st CE nme = OK nme_t ->
          Cminor.eval_expr g sp locenv m nme_t v ->
          forall locenv', Cminor.eval_expr g sp locenv' m nme_t v.
Proof.
  !intros.
  !functional inversion heq_transl_name;subst.
  eapply eval_expr_transl_variable_inv_locenv;eauto.
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
  split; try now apply h_match_env.
  - eapply stack_match_inv_locenv;eauto.
  - pose proof me_stack_match_functions h_match_env as h_mtch_fun.
    red in h_mtch_fun.
    red;!intros.
    specialize (h_mtch_fun p pb_lvl pb h_fetch_proc_p).
    decomp h_mtch_fun.
    repeat eexists;eauto.
    eapply eval_expr_Econst_inv_locenv;eauto.
  - pose proof me_stack_separate h_match_env as h_separate.
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
  - pose proof me_stack_localstack_aligned h_match_env as h_align.
    red in h_align.
    red.
    !intros.
    assert (Cminor.eval_expr g b locenv m (build_loads_ δ_lvl) v).
    { eapply eval_expr_build_loads__inv_locenv;eauto. }
    eapply h_align;eauto.
  - !!pose proof me_stack_freeable h_match_env.
    red in h_freeable_CE_m.
    red;!intros.
    eapply h_freeable_CE_m;eauto.
    eapply eval_expr_transl_variable_inv_locenv;eauto.
Qed.




Lemma cut_until_exact_lvl:
  forall stoCE CE lvl,
    exact_levelG (stoCE :: CE)
    -> CompilEnv.cut_until (stoCE :: CE) lvl [ ] (stoCE :: CE)
    -> CompilEnv.cut_until CE lvl [ ] CE.
Proof.
  !intros.
  !destruct CE.
  - constructor.
  - !inversion h_CEcut;subst.
    !destruct f.
    !inversion h_exct_lvl;subst;simpl in *.
    constructor 2.
    simpl.
    inversion h_exct_lvl0;subst.
    omega.
Qed.




Lemma strong_match_env_lgth: forall st sp locenv g m s CE,
    strong_match_env st s CE sp locenv g m ->
    invariant_compile CE st ->
    forall CE1 CE2 lvl,
      CompilEnv.cut_until CE lvl CE1 CE2 ->
      exists s1 s2, STACK.cut_until s lvl s1 s2
                    /\ List.length s1 = List.length CE1.
Proof.
  !!intros until 1.
  !induction h_strg_mtch_s_CE_m;!intros.
  - exists (@nil STACK.frame).
    exists (@nil STACK.frame).
    split.
    * constructor.
    * inversion h_CEcut.
      reflexivity.
  - !inversion h_CEcut;subst.
    + !assert (CompilEnv.cut_until CE lvl0 [ ] CE).
      { eapply cut_until_exact_lvl;eauto. }
      !assert (invariant_compile CE st).
      { eapply invariant_compile_subcons.
        eauto. }
      specialize (IHh_strg_mtch_s_CE_m h_inv_comp_CE_st (@nil CompilEnv.frame) CE lvl0  h_CEcut_CE_lvl0).
      !!decompose [and ex] IHh_strg_mtch_s_CE_m.
      rename x into s1.
      rename x0 into s2.
      simpl in *.
      exists s1.
      exists ((lvl, sto) :: s).
      split.
      * assert (s1 =[]).
        { now apply length_zero_iff_nil. }
        subst.
        constructor 2.
        simpl;auto.
      * auto.
    + rename s' into CE1.
      !assert (invariant_compile CE st).
      { eapply invariant_compile_subcons.
        eauto. }
      specialize (IHh_strg_mtch_s_CE_m h_inv_comp_CE_st CE1 CE2 lvl0 h_CEcut_CE_lvl0).
      !!decompose [and ex] IHh_strg_mtch_s_CE_m.
      rename x into s1.
      rename x0 into s2.
      simpl in *.
      exists ((lvl, sto) :: s1).
      exists s2.
      split.
      * constructor 3.
        -- simpl.
           assumption.
        -- assumption.
      * simpl.
        auto.
Qed.

Lemma strong_match_env_match_env_sublist : forall st s CE sp locenv g  m,
    strong_match_env st s CE sp locenv g m ->
    invariant_compile CE st ->
    forall CE' CE'' s' s'' sp'' lvl δ,
      CompilEnv.cut_until CE lvl CE' CE'' -> 
      STACK.cut_until s lvl s' s'' ->
      ((exists toplvl , CompilEnv.level_of_top CE = (Some toplvl)%nat /\ δ = ((toplvl + 1) - lvl)%nat)
       \/  CE = [] /\ δ = 0%nat) ->
      repeat_Mem_loadv AST.Mint32 m δ sp sp'' ->
      forall locenv,
        match_env st s'' CE'' sp'' locenv g m.
Proof.
  !!intros until 1.
  !!induction h_strg_mtch_s_CE_m;!intros.  
  - rename v into sp.
    !invclear h_CEcut;subst.
    !invclear h_stkcut.
    eapply match_env_empty;eauto.
  - !assert (invariant_compile CE st).
    { eapply invariant_compile_subcons.
      eauto. }
    specialize (IHh_strg_mtch_s_CE_m h_inv_comp_CE_st).
    !inversion h_CEcut.
    + assert (s'=[]).
      { !assert(CompilEnv.cut_until CE lvl0 (@nil CompilEnv.frame) CE).
        { eapply cut_until_exact_lvl;eauto. }
        inversion h_stkcut;subst;simpl in *.
        * reflexivity.
        * contradiction. }
      repeat progress (simpl in *;subst).      
      !inversion h_stkcut.
      repeat progress (simpl in *;subst).
      decomp h_or.
      * clear h_lt0.
        apply match_env_inv_locenv with locenv'.
        !assert (v' = sp'').
        { cbn in *.
          !invclear heq_lvloftop_x.
          !assert (δ = 0)%nat.
          { subst. apply Nat.sub_0_le ;omega. }
          rewrite heq_δ0 in *.
          inversion h_repeat_loadv_δ_v' ;subst;auto. }
        subst.
        assumption.
      * discriminate.
    + clear h_CEcut.
      up_type.
      rename s'0 into CE'.
      cbn in *.
      !!assert (lvl0 <= lvl)%nat by omega; clear H1.
      !!pose proof (strong_match_env_lgth _ _ _ _ _ _ _ h_strg_mtch_s_CE_m h_inv_comp_CE_st _ _ _ h_CEcut_CE_lvl0).
      decomp h_ex.
      rename x into s1. rename x0 into s2.
      up_type.
      !!destruct h_or as [[? [? ?]] | [? ?] ];try discriminate.
      !invclear heq0.
      !!assert ((δ>0)%nat) by omega.
      (* linking s' and s1 and s'' and s2 *)
      !inversion h_stkcut;subst;cbn in *; try (exfalso;omega).
      !destruct (STACK.cut_until_uniqueness _ _ _ _ _ _ h_stkcut_s_lvl0 h_stkcut_s_lvl1).
      subst s''.
      subst s'0.
      (* done linking *)
      destruct (CompilEnv.level_of_top CE) eqn:heq_lvltopCE.
      * (* CE is not empty, therefore we are in the non degenerated case*)
        eapply (IHh_strg_mtch_s_CE_m _ _ s1 s2);try eassumption.
        -- left;eauto.
        -- rename s0 into x'.
           !inversion h_repeat_loadv_δ_v'; try now (exfalso;omega).
           !assert (x = S x').
           { !!pose proof (ci_exact_lvls _ _ h_inv_comp_st).
             !inversion h_exct_lvl;subst.
             !!pose proof (ci_exact_lvls _ _ h_inv_comp_CE_st).
             !inversion h_exct_lvl_CE;try now (subst;try discriminate).
             cbn.
             cbn in heq_lvltopCE.
             inversion heq_lvltopCE.
             reflexivity. }
           subst x.
           assert (S x' + 1 - lvl0 = S ( x' + 1 - lvl0))%nat.
           { omega. }
           rewrite <- heq1 in h_repeat_loadv_δ_v'.
           rewrite H in heq1.
           inversion heq1.
           rewrite <- H2.
           rewrite heq0 in heq.
           inversion heq.
           subst v.
           assumption.
      * (* CE is empty, degenerated case. *)
        assert (CE = []).
        { destruct CE;cbn in *;try discriminate;auto.
          destruct f;discriminate. }
        subst.
        
        assert (x=0)%nat.
        { !!pose proof (ci_exact_lvls _ _ h_inv_comp_st).
          inversion h_exct_lvl.
          reflexivity. }
        subst.
        !!assert (lvl0 = 0)%nat by auto with arith.
        subst.
        cbn in *.
        eapply (IHh_strg_mtch_s_CE_m _ _ s1 s2);try eassumption;eauto.
        !inversion h_repeat_loadv_δ_v'.
        rewrite heq0 in heq.
        inversion heq.
        subst v.
        assumption.
Qed.

(** Property of the translation: Since chain variables have always zero
   offset, the offset of a variable in CE is the same as its offset in
   CMinor memory. *)
Lemma eval_build_loads_offset: forall CE g stkptr locenv m δ_lvl δ_id b ofs,
    stack_localstack_aligned CE locenv g m ->
    (δ_lvl < Datatypes.length CE)%nat
    -> Cminor.eval_expr g stkptr locenv m (build_loads δ_lvl δ_id) (Values.Vptr b ofs) ->
    ofs = Int.repr δ_id.
Proof.
  !intros.
  unfold build_loads in *.
  !inversion h_CM_eval_expr.
  !inversion h_CM_eval_expr_v2.
  simpl in *.
  red in h_aligned_g_m.
  specialize (fun x => h_aligned_g_m _ _ _ x h_CM_eval_expr_v1). (* TODO: especialize *)
  edestruct h_aligned_g_m;eauto.
  subst.
  destruct v2;try discriminate.
  simpl in *.
  !invclear heq;subst.
  inversion h_eval_constant.
  rewrite Int.add_zero_l.
  reflexivity.
Qed.


(** Property of the translation: Since chain variables have always
    zero offset, the offset of a variable in CE must be more than 3. *)
Lemma eval_build_loads_offset_non_null_var:
  forall stbl CE g stkptr locenv m nme a bld_lds b ofs,
    exact_levelG CE ->
    stack_no_null_offset stbl CE ->
    stack_localstack_aligned CE locenv g m ->
    transl_variable stbl CE a nme = OK bld_lds ->
    Cminor.eval_expr g stkptr locenv m bld_lds (Values.Vptr b ofs) ->
    4 <= Int.unsigned ofs.
Proof.
  !intros.
  functional inversion heq_transl_variable;subst.
  assert (ofs=(Int.repr n)). {
    eapply (eval_build_loads_offset CE g stkptr locenv m (m' - m0) _ b ofs h_aligned_g_m);auto with arith.
    - erewrite exact_lvlG_lgth with (lvl:=m').
      + omega.
      + assumption.
      + assumption. }
  subst.
  eapply h_nonul_ofs;eauto.
Qed.

Lemma transl_expr_ok : forall stbl CE e e',
    transl_expr stbl CE e = OK e' ->
    forall locenv g m (s:STACK.stack)  (v:value) stkptr,
      eval_expr stbl s e (Normal v) ->
      match_env stbl s CE stkptr locenv g m ->
      exists v_t,
        (transl_value v v_t /\ Cminor.eval_expr g stkptr locenv m e' v_t).
Proof.
  intros until e.
  !functional induction (transl_expr stbl CE e) ;try discriminate;simpl; !intros;
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
    destruct (transl_type stbl astnum_type) eqn:heq_transl_type;simpl in *.
    + !destruct h_match_env.
      eapply h_stk_mtch_s_m;eauto.
      simpl.
      rewrite heq_fetch_exp_type.
      reflexivity.
    + discriminate.
  - decomp (IHr _ heq_tr_expr_e _ _ _ _ _ _ h_eval_expr_e_e_v h_match_env).
    decomp (IHr0 _ heq_tr_expr_e0 _ _ _ _ _ _ h_eval_expr_e0_e0_v h_match_env).
    assert (hex:or (exists b, v = Bool b) (exists n, v = Int n)). {
      apply do_run_time_check_on_binop_ok in h_do_rtc_binop.
      rewrite binopexp_ok in h_do_rtc_binop.
      functional inversion h_do_rtc_binop;subst;eq_same_clear
      ;try contradiction;eauto. }
    decomp hex;subst.
    + destruct x; eexists;(split;[econstructor;eauto|]).
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
    simpl in heq.
    eq_same_clear.
    specialize (IHr e_t heq_tr_expr_e locenv g m s e_v stkptr
                    h_eval_expr_e_e_v h_match_env).
    decomp IHr.
    !invclear h_do_rtc_unop;eq_same_clear.
    !invclear h_overf_check.
    eexists.
    split.
    * econstructor.
    * assert (h:=unaryneg_ok _ _ _ heq_transl_value_e_v_e_t_v heq).
      econstructor;eauto.
      simpl.
      inversion h.
      reflexivity.
  (* Not *)
  - !invclear h_do_rtc_unop;simpl in *;try eq_same_clear.
    specialize (IHr _ heq_tr_expr_e _ _ _ _ _ _ h_eval_expr_e_e_v h_match_env).
    decomp IHr.
    generalize (not_ok _ _ _ heq_transl_value_e_v_e_t_v heq).
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


(** Hypothesis renaming stuff *)
Ltac rename_hyp5 th :=
  match th with
  | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ None  => fresh "h_exec_stmt_None"
  | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ _  => fresh "h_exec_stmt"
  | _ => rename_hyp4 th
  end.

Ltac rename_hyp ::= rename_hyp5.

Scheme Equality for binary_operator.
Scheme Equality for unary_operator.
Scheme Equality for literal.

Ltac finish_eqdec := try subst;try (left;reflexivity);(try now right;intro abs;inversion abs;contradiction).

Lemma expression_dec: forall e1 e2:expression, ({e1=e2} + {e1<>e2})
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
(* Is this true? *)
Axiom det_eval_expr: forall g stkptr locenv m e v v',
    Cminor.eval_expr g stkptr locenv m e v
    -> Cminor.eval_expr g stkptr locenv m e v'
    -> v = v'.

Inductive le_loads (lds: Cminor.expr): Cminor.expr -> Prop :=
  le_loads_n: le_loads lds lds
| le_loads_L: ∀ lds', le_loads lds lds' -> le_loads lds (Eload AST.Mint32 lds').

Definition lt_loads := λ l₁ l₂ , le_loads(Eload AST.Mint32 l₁) l₂.

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


Lemma build_loads__inj : forall i₁ i₂,
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

Lemma build_loads__inj_lt : forall i₁ i₂,
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
  induction h_lt_i₁_i₂;simpl;!intros;subst.
  - constructor 1.
  - constructor 2.
    apply IHh_lt_i₁_i₂;auto.
Qed.

Lemma build_loads__inj_neq : forall i₁ i₂,
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

Lemma build_loads_inj : forall i₁ i₂ k k' ,
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

Lemma build_loads_inj_neq1 : forall i₁ i₂ k k' e₁ e₂,
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

Lemma build_loads_inj_neq2 : forall i₁ i₂ k k' e₁ e₂,
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


Lemma fetches_none_notin: ∀ (a : localframe) (id : idnum) (st : CompilEnv.V), CompilEnv.fetches id a = None → ~List.In (id, st) a.
Proof.
  !intros.
  !!(functional induction (CompilEnv.fetches id a);intros; try discriminate).
  - specialize (IHo heq_CEfetches_id_a).
    intro abs.
    simpl in *.
    !destruct abs.
    + inversion heq;subst.
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
    -> add_to_frame stbl fram_sz nme subtyp_mrk = OK (new_fram, new_sz)
    -> NoDupA eq_fst_idnum (fst fram_sz)
    -> NoDupA eq_fst_idnum new_fram.
Proof.
  !!intros until 0.
  rewrite add_to_frame_ok.
  !!functional induction (function_utils.add_to_frame stbl fram_sz nme subtyp_mrk);simpl;!intros;
    try discriminate.
  !invclear heq.
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
  | Forall ?P ?x => fresh "h_forall_" P "_" x
  | Forall _ ?x => fresh "h_forall_" x
  | Forall ?P _ => fresh "h_forall_" P
  | Forall _ _ => fresh "h_forall"
  | all_frm_increasing ?x => fresh "h_allincr_" x
  | all_frm_increasing _ => fresh "h_allincr"
  | all_addr_no_overflow ?x => fresh "h_bound_addr_" x
  | all_addr_no_overflow _ => fresh "h_bound_addr"
  | _ => rename_hyp5 h th
  end.
Ltac rename_hyp ::= rename_hyp_incro.


Lemma exact_level_top_lvl: forall CE s3,
    exact_levelG CE ->
    CompilEnv.level_of_top CE = Some s3 ->
    List.length CE = S s3.
Proof.
  !intros.
  inversion h_exact_lvlG_CE;subst;cbn in *;try discriminate.
  inversion heq_lvloftop_CE_s3.
  reflexivity.
Qed.


Lemma increase_order_level_of_top_ge: forall CE id s s0 s3,
    exact_levelG CE ->
    CompilEnv.frameG id CE = Some (s, s0) ->
    CompilEnv.level_of_top CE = Some s3 ->
    (s3 >= s)%nat.
Proof.
  !!intros until 1.
  revert id s s0 s3.
  !induction h_exact_lvlG_CE;cbn.
  - discriminate.
  - !intros.
    destruct (CompilEnv.resides id fr) eqn:heq_resides.
    + !invclear heq0.
      !invclear heq.
      auto.
    + !invclear heq0.
      destruct (CompilEnv.level_of_top stk) eqn:heq_lvltop.
      * specialize(IHh_exact_lvlG_CE id s s0 s1).
        specialize (exact_level_top_lvl _ _ h_exact_lvlG_CE heq_lvltop).
        !intro.
        red.
        apply Nat.le_trans with s1.
        -- apply IHh_exact_lvlG_CE;auto.
        -- omega.
      * destruct stk.
        -- cbn in heq.
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
    + rewrite Nat.eqb_refl in heq.
      !invclear heq.
      assert (h:id₂ ≠ i) by auto.
      rewrite <- (Nat.eqb_neq id₂ i) in h.
      rewrite h in heq0.
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
        rewrite Nat.eqb_refl in heq0.
        !invclear heq0.
        assert (h:id₁ ≠ i) by auto.
        rewrite <- (Nat.eqb_neq id₁ i) in h.
        rewrite h in heq.
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
    exact_levelG stk
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
    exact_levelG CE ->
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

  !induction h_exact_lvlG_CE;!intros;simpl in *;try discriminate.
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
    eapply IHh_exact_lvlG_CE ;eauto.
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
    exact_levelG CE ->
    (* In each frame, stacks are also numbered with (increasing) numbers *)
    all_frm_increasing CE ->
    all_addr_no_overflow CE ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a₁ id₁ = OK (build_loads k₁ δ₁) ->
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a₂ id₂ = OK   (build_loads k₂ δ₂) ->
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
  assert (hh:=CEfetchG_inj _ _ _ h_exact_lvlG_CE h_allincr_CE _ _ _ _ _ _  h₁ h₂ h₁' h₂' hneq).
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
    transl_variable stbl CE astnum id' = OK addrof_nme
    -> forall a,transl_variable stbl CE a id' = transl_variable stbl CE astnum id'.
Proof.
  !intros.
  unfold transl_variable.
  !functional inversion heq_transl_variable.
  rewrite  heq_CEfetchG_id'_CE, heq_CEframeG_id'_CE, heq_lvloftop_CE_m'.
  reflexivity.
Qed.



Lemma compute_chk_32 : forall stbl t,
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
Lemma wf_chain_load'2:forall CE g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> stack_localstack_aligned CE locenv g m
    -> 4 <= Int.unsigned ofs (*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl,
        (lvl < Datatypes.length CE)%nat ->
        let load_id := build_loads_ lvl in
        Cminor.eval_expr g stkptr locenv m' load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m load_id vaddr.
Proof.
  !intros.
  rename h_le into h_ofs_non_zero.
  simpl in *.
  subst load_id.
  generalize dependent load_id_v.
  induction lvl;!intros;simpl in *.
  - !inversion h_CM_eval_expr_load_id_v;econstructor;eauto.
  - !invclear h_CM_eval_expr_load_id_v.
    assert (h_CM_eval_expr_on_m:
              Cminor.eval_expr g stkptr locenv m (build_loads_ lvl) vaddr).
    { eapply IHlvl; eauto.
      omega. }
    econstructor.
    + eassumption.
    + destruct vaddr;simpl in *;try discriminate.
      rewrite <- heq.
      symmetry.
      eapply Mem.load_store_other;eauto.
      right.
      left.
      simpl.
      transitivity 4.
      * !assert (lvl < Datatypes.length CE)%nat.
        { omega. }
        !destruct (h_aligned_g_m _ _ _ h_lt_lvl0 h_CM_eval_expr_on_m).
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
Lemma wf_chain_load'3:forall CE g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> stack_localstack_aligned CE locenv g m'
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl,
        (lvl < Datatypes.length CE)%nat ->
        let load_id := build_loads_ lvl in
        Cminor.eval_expr g stkptr locenv m load_id vaddr
        -> Cminor.eval_expr g stkptr locenv m' load_id vaddr.
Proof.
  !intros.
  rename h_le into h_ofs_non_zero.
  simpl in *.
  subst load_id.
  generalize dependent load_id_v.
  induction lvl;!intros;simpl in *.
  - !inversion h_CM_eval_expr_load_id_v;econstructor;eauto.
  - !invclear h_CM_eval_expr_load_id_v.
    assert (h_CM_eval_expr_on_m':
              Cminor.eval_expr g stkptr locenv m' (build_loads_ lvl) vaddr).
    { eapply IHlvl; eauto. omega. }
    econstructor.
    + eassumption.
    + destruct vaddr;simpl in *;try discriminate.
      rewrite <- heq.
      eapply Mem.load_store_other;eauto.
      simpl.
      right. left.
      transitivity 4.
      * !assert (lvl < Datatypes.length CE)%nat.
        { omega. }
        !destruct (h_aligned_g_m' _ _ _ h_lt_lvl0 h_CM_eval_expr_on_m').
        !invclear heq.
        !invclear heq0.
        vm_compute.
        intro abs;discriminate.
      * apply h_ofs_non_zero.
Qed.


Lemma wf_chain_load'':forall CE g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned CE locenv g m)
    -> (stack_localstack_aligned CE locenv g m')
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl,
        (lvl < Datatypes.length CE)%nat ->
        let load_id := build_loads_ lvl in
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
Lemma wf_chain_load':forall CE g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned CE locenv g m')
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl δ_lvl,
        (lvl < Datatypes.length CE)%nat ->
        let load_id := build_loads lvl δ_lvl in
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
Lemma wf_chain_load'_2:forall CE g locenv stkptr chk m m' b ofs e_t_v vaddr,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned CE locenv g m)
    -> (4 <= (Int.unsigned ofs))(*forall n, Integers.Int.repr n = ofs -> 4 <= n*)
    -> forall lvl δ_lvl,
        (lvl < Datatypes.length CE)%nat ->
        let load_id := build_loads lvl δ_lvl in
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
    exact_levelG CE ->
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned CE locenv g m')
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
  pose proof exact_lvlG_lgth _ _ h_exact_lvlG_CE heq_lvloftop_CE_m'0.
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
    exact_levelG CE ->
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (stack_localstack_aligned CE locenv g m)
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
  pose proof exact_lvlG_lgth _ _ h_exact_lvlG_CE heq_lvloftop_CE_m'0.
  rewrite H in *.
  subst δ_lvl.
  omega.
Qed.


(* INVARIANT OF STORE/STOREV: if we do not touch on addresses zero
     of blocks, chaining variables all poitn to zero ofsets. *)
Lemma wf_chain_load_aligned:forall CE g locenv chk m m' b ofs e_t_v,
    Mem.storev chk m (Values.Vptr b ofs) e_t_v = Some m'
    -> (4 <= (Int.unsigned ofs))
    -> stack_localstack_aligned CE locenv g m
    -> stack_localstack_aligned CE locenv g m'.
Proof.
  unfold stack_localstack_aligned at 2.
  !intros.
  revert g locenv chk m m' b ofs e_t_v heq_storev_e_t_v_m' h_le h_aligned_g_m b0 v h_CM_eval_expr_v.
  destruct δ_lvl;simpl;!intros.
  - edestruct (h_aligned_g_m b0 O v).
    + assumption.
    + simpl.
      constructor.
      !inversion h_CM_eval_expr_v.
      assumption.
    + eauto.
  - !inversion h_CM_eval_expr_v.
    generalize h_CM_eval_expr_vaddr.
    !intro.
    eapply wf_chain_load'2 in h_CM_eval_expr_vaddr;eauto;try omega.
    generalize h_CM_eval_expr_vaddr.
    !intro.
    eapply h_aligned_g_m in h_CM_eval_expr_vaddr1;try omega.
    destruct h_CM_eval_expr_vaddr1.
    subst.
    assert (heq_ld_m:Mem.loadv AST.Mint32 m (Values.Vptr x Int.zero) = Some v). {
      simpl.
      erewrite <- (Mem.load_store_other);eauto. }
    red in h_aligned_g_m.
    eapply (h_aligned_g_m _ (S δ_lvl));try omega.
    simpl.
    econstructor;eauto.
Qed.




Lemma assignment_preserve_stack_match :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    exact_levelG CE ->
    all_frm_increasing CE ->
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
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    stack_match stbl s' CE stkptr locenv g m'.
Proof.
  intros until m'.
  !intros.
  !destruct h_match_env.
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
  destruct (h_stk_cmpl_s_CE _ _ _ heq_transl_variable) as [v_id_prev h_eval_name_id_val_prev].
  set (nme:=(E_Identifier a id)) in *.
  (* Getting rid of erronous cases *)
  !functional inversion heq_transl_name.
  subst.
  (* done *)
  rename id0 into other_id.
  set (other_nme:=(E_Identifier astnum other_id)) in *.
  (* other_nme can already be evaluated in s *)
  destruct (h_stk_cmpl_s_CE _ _ _ heq_transl_variable0) as [v_other_id_prev h_eval_name_other_id_val_prev].
  destruct (h_stk_mtch_s_m _ _ _ _ _ _ h_eval_name_other_id_val_prev
                           heq_type_of_name heq_transl_name heq_transl_type heq_make_load)
    as [ cm_v [tr_val_v_other cm_eval_m_v_other]].
  assert (heq_ftch_astnum:symboltable.fetch_exp_type astnum stbl = Some type_other). {
    simpl in heq_type_of_name.
    destruct (symboltable.fetch_exp_type astnum stbl);try discriminate.
    !inversion heq_type_of_name.
    reflexivity. }
  assert (h_tr_exp_other:
            transl_expr stbl CE (E_Name 1%nat (E_Identifier astnum other_id))
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
        !functional inversion heq_transl_type;subst;simpl in h_access_mode_cm_typ_other.
        - inversion h_access_mode_cm_typ_other;auto.
        - inversion h_access_mode_cm_typ_other;auto. }
      subst.
      erewrite (Mem.load_store_same _ _ _ _ _ _ heq_store_e_t_v_m') .
      { destruct e_t_v;auto;destruct e_v;simpl in *;try discriminate;
        now inversion heq_transl_value_e_v_e_t_v. }

  - (* loading a different variable id' than the one stored id.
         2 steps: first prove that the addresses of id' and id did
         not change (the translated expressions did not change + the
         chained stack did not change either), and thus remain
         different, then conclude that the value stored in id' did
         not change. *)
    !assert (chk = AST.Mint32). {
      rewrite function_utils.compute_chnk_ok in heq_compute_chnk.
      functional inversion heq_compute_chnk; reflexivity. }

    assert (v_other_id_prev = other_v). {
      eapply storeUpdate_id_ok_others_eval_name ;eauto. }
    subst.
    exists cm_v.
    split;auto.
    assert (h_aligned_m' : stack_localstack_aligned CE locenv g m'). {
      eapply wf_chain_load_aligned;eauto. }
    !functional inversion heq_make_load;subst.
    !inversion cm_eval_m_v_other.
    generalize (wf_chain_load_var _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                  h_exact_lvlG_CE
                                  heq_storev_e_t_v_m' h_aligned_m'
                                  h_ofs_nonzero heq_transl_variable0
                                  h_CM_eval_expr_addr_other_addr_other_v).
    !intro.
    econstructor.
    + eassumption.
    + destruct addr_other_v; try discriminate;simpl in *.
      clear h_tr_exp_other.
      erewrite Mem.load_store_other;[now eassumption| now eassumption | ].
      subst nme other_nme.
      unfold compute_chnk_astnum in heq_compute_chnk.
      destruct (symboltable.fetch_exp_type a stbl) eqn:heq_fetchvartyp;try discriminate.
      assert (heq_tr_type_id:transl_type stbl t
                             = OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr)). {
        apply compute_chk_32.
        unfold compute_chnk_astnum in heq_compute_chnk.
        assumption. }
      unfold stack_separate in h_separate_CE_m.
      { eapply h_separate_CE_m with (nme:=(E_Identifier a id))
                                      (nme':=(E_Identifier astnum other_id))
                                      (k₂ := b0) (k₁:=b);
        clear h_separate_CE_m;simpl;try eassumption;auto.
        - rewrite heq_fetchvartyp.
          reflexivity.
        - intro abs.
          inversion abs;subst;try discriminate.
          elim hneq;reflexivity. }
Qed.


Lemma storev_inv : forall nme_chk m nme_t_addr e_t_v m',
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m'
    -> exists b ofs, nme_t_addr = Values.Vptr b ofs.
Proof.
  !intros.
  destruct nme_t_addr; try discriminate.
  eauto.
Qed.

Lemma transl_name_OK_inv : forall stbl CE nme nme_t,
    transl_name stbl CE nme = OK nme_t
    -> exists astnum id, (transl_variable stbl CE astnum id =  OK nme_t
                          /\ nme = E_Identifier astnum id).
Proof.
  !intros stbl CE nme nme_t H.
  functional inversion H.
  eauto.
Qed.

Lemma assignment_preserve_stack_match_function :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    exact_levelG CE ->
    all_frm_increasing CE ->
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
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    stack_match_functions stbl stkptr CE locenv g m'.
Proof.
  !intros.
  red.
  !intros.
  !destruct h_match_env.
  up_type.
  red in h_stk_mtch_fun.
  specialize (h_stk_mtch_fun p pb_lvl pb h_fetch_proc_p).
  !! destruct h_stk_mtch_fun as [CE' [CE'' [paddr [pnum [fction [lglobdef [? [? [? ?]]]]]]]]].
  exists CE' CE'' paddr pnum fction lglobdef.
  split;[|split;[|split]];subst;eauto.
  inversion h_CM_eval_expr_paddr.
  constructor.
  assumption.
Qed.

Lemma assignment_preserve_stack_match_CE :
  forall stbl CE s a id id_t e_v s',
    (* translating the variabe to a Cminor load address, so id belongs to CE *)
    transl_variable stbl CE a id = OK id_t ->
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (E_Identifier a id) e_v (Normal s') ->
    stack_match_CE s CE ->
    stack_match_CE s' CE.
Proof.
(*  !intros.
  red.
  !intros.
  up_type.
  red in h_stk_mtch_CE_s_CE.
  !destruct (Nat.eq_dec id nme).
  - subst nme.
    functional inversion heq_transl_variable.
    inversion h_storeUpd;subst.
    pose proof (storeUpdate_id_ok_same _ _ _ _ _ _ h_storeUpd).
    
    
    admit.
  - eapply h_stk_mtch_CE_s_CE. 
    !!pose proof (storeUpdate_id_ok_others _ _ _ _ _ _ h_storeUpd _ hneq).
    admit.
*)
XXX    
Admitted.

Lemma assignment_preserve_stack_complete :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
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
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    invariant_compile CE stbl ->
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
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    stack_separate stbl CE stkptr locenv g m'.
Proof.
  !intros.
  red.
  !intros.
  !destruct h_match_env.
  decompose [ex] (storev_inv _ _ _ _ _ heq_storev_e_t_v_m');subst.
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
    transl_variable stbl CE a id = OK id_t ->
    (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
    transl_value e_v e_t_v ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (E_Identifier a id) = OK chk ->
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (E_Identifier a id) e_v (Normal s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    stack_no_null_offset stbl CE.
Proof.
  !intros.
  destruct h_match_env.
  assumption.
Qed.

Lemma assignment_preserve_stack_safe :
  forall stbl CE g locenv stkptr s m a chk id id_t e_v e_t_v idaddr s' m' ,
    (* translating the variabe to a Cminor load address *)
    transl_variable stbl CE a id = OK id_t ->
    (* translating the value, we may need a overflow hypothesis on e_v/e_t_v *)
    transl_value e_v e_t_v ->
    (* if e_v is an int, then it is not overflowing (we are not trying
       to add an overflowing value to the environment). *)
    (forall n, e_v = Int n -> do_overflow_check n (Normal (Int n))) ->
    (* Evaluating var address in Cminor *)
    Cminor.eval_expr g stkptr locenv m id_t idaddr ->
    (* Size of variable in Cminor memorry *)
    compute_chnk stbl (E_Identifier a id) = OK chk ->
    (* the two storing operation maintain match_env *)
    storeUpdate stbl s (E_Identifier a id) e_v (Normal s') ->
    Mem.storev chk m idaddr e_t_v = Some m' ->
    match_env stbl s CE stkptr locenv g m ->
    safe_stack s'.
Proof.
  !intros.
  match goal with H: context C [do_overflow_check] |- _ => rename H into h_overf_e_v end.
  !destruct h_match_env.
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



Lemma assignment_preserve_loads_offset_non_null:
  forall stbl s CE spb ofs locenv' g m x x0 nme_t nme_chk nme_t_addr e_t_v m',
    invariant_compile CE stbl ->
    match_env stbl s CE (Values.Vptr spb ofs) locenv' g m ->
    transl_name stbl CE (E_Identifier x x0) =: nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv' m nme_t nme_t_addr ->
    Mem.storev nme_chk m nme_t_addr e_t_v = Some m' ->
    stack_localstack_aligned CE locenv' g m'.
Proof.
  !intros.
  decomp (storev_inv _ _ _ _ _ heq_storev_e_t_v_m') ;subst.
  functional inversion heq_transl_name.
  eapply wf_chain_load_aligned;eauto.
  eapply eval_build_loads_offset_non_null_var;eauto.
Qed.

Lemma assignment_preserve_stack_freeable:
  forall stbl s CE spb ofs locenv' g m x x0 nme_t nme_chk nme_t_addr e_t_v m',
    invariant_compile CE stbl ->
    match_env stbl s CE (Values.Vptr spb ofs) locenv' g m ->
    transl_name stbl CE (E_Identifier x x0) =: nme_t ->
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
  - eapply (me_stack_freeable h_match_env);eauto.
    eapply wf_chain_load_var';eauto.
    eapply eval_build_loads_offset_non_null_var
      with (5:=h_CM_eval_expr_nme_t_nme_t_v);eauto.
Qed.


Hint Resolve
     assignment_preserve_stack_match
     assignment_preserve_stack_match_function
     assignment_preserve_stack_complete
     assignment_preserve_stack_separate assignment_preserve_loads_offset_non_null
     assignment_preserve_stack_no_null_offset assignment_preserve_stack_safe
     assignment_preserve_stack_freeable.

(* [make_load] does not fail on transl_type a translated variable coming
   from stbl *)
Lemma make_load_no_fail: forall stbl t nme_t x2,
    transl_type stbl t =: x2 ->
    exists load_addr_nme, make_load nme_t x2 =: load_addr_nme.
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

(** Consequence of chained structure: build_load returns always a pointeur *)
Lemma build_loads_Vptr : forall lvl_nme CE g spb ofs locenv m δ_nme nme_t nme_t_v,
    stack_localstack_aligned CE locenv g m ->
    (lvl_nme < Datatypes.length CE)%nat ->
    build_loads lvl_nme δ_nme = nme_t ->
    Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t nme_t_v ->
    ∃ nme_block nme_ofst, nme_t_v = (Values.Vptr nme_block nme_ofst).
Proof.
  intro.
  !destruct lvl_nme;!intros.
  - unfold build_loads in *.
    simpl in *.
    subst.
    !invclear h_CM_eval_expr_nme_t_nme_t_v.
    !invclear h_CM_eval_expr_v1;simpl in *.
    !invclear h_eval_constant.
    !invclear h_CM_eval_expr_v2;simpl in *.
    !invclear h_eval_constant.
    inversion heq.
    eauto.
  - subst.
    !invclear h_CM_eval_expr_nme_t_nme_t_v.
    destruct (h_aligned_g_m (Values.Vptr spb ofs) (S lvl_nme) v1);auto.
    subst.
    simpl in *.
    !invclear h_CM_eval_expr_v2.
    simpl in *.
    !invclear h_eval_constant.
    !invclear heq.
    eauto.
Qed.


(** Consequence of chained structure: a variable is always translated into a pointer. *)
Lemma transl_variable_Vptr : forall g spb ofs locenv m stbl CE astnm nme nme_t nme_t_v,
    invariant_compile CE stbl ->
    stack_localstack_aligned CE locenv g m ->
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
  | _ => rename_hyp_incro h th
  end.

Ltac rename_hyp ::= rename_hyp_overf.

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
  - !invclear heq.
    split;assumption.
  - rewrite <- build_frame_lparams_ok in *.
    rewrite add_to_frame_ok in heq_add_to_fr_nme.
    !functional inversion heq_add_to_fr_nme;subst.
    rewrite <- add_to_frame_ok in *.
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
      rewrite heq_bool_false in h_ge.
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
  rewrite build_frame_decl_ok.
  !functional induction (function_utils.build_frame_decl st locfrmZ decl);!intros;subst;try discriminate
  ; try rewrite <- build_frame_decl_ok in *.
  - split.
    + !invclear heq.
      !invclear heq0.
      assumption.
    + !invclear heq0.
      !invclear heq.
      assumption.
  - rename x into size.
    !invclear heq.
    !invclear heq0.
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
        rewrite heq_bool_false in h_ge.
        split.
        -- omega.
        -- omega.
      * unfold all_addr_no_overflow_localframe in h_no_overf_localf.
        eapply h_no_overf_localf.
        eassumption.
    + omega.
  - rename x into size.
    up_type.
    !invclear heq0.
    destruct size.
    specialize (IHr _ _ eq_refl lvl s z h_ge_sz0 heq h_no_overf_localf).
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
  !functional induction (function_utils.build_frame_lparams st initz prmprof);!intros;subst;try discriminate.
  - inversion heq;subst;auto.
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


Lemma compute_size_pos stbl t : forall x, compute_size stbl t =: x -> x > 0.
Proof.
  !intros.
  unfold compute_size in *.
  (* functional inbversion would be better *)
  destruct (compute_chnk_of_type stbl t); cbv in  *;try discriminate.
  destruct m;cbv in *;try inversion heq_cmpt_size_t;auto.
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
  !functional induction (function_utils.build_frame_decl st initz decl);!intros;subst;try discriminate.
  - inversion heq;subst;auto.
    inversion heq0;subst;auto.
  - !invclear heq;subst.
    !invclear heq0;subst.
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
    destruct (IHr init z heq0 _ _ heq h_forall_init h_incr_order_init); clear IHr.
    destruct (IHr0 s z0 eq_refl _ _ heq1 H0 H).
    split;assumption.
Qed.

Lemma build_compilenv_preserve_invariant_compile:
  forall st CE pb_lvl prmprof pdeclpart CE' stcksize,
    build_compilenv st CE pb_lvl prmprof pdeclpart =: (CE', stcksize)
    -> invariant_compile CE st
    -> invariant_compile CE' st.
Proof.
  !!(intros until 1).
  rewrite <- build_compilenv_ok in heq.
  !functional inversion heq;subst;intro; rewrite -> ?build_compilenv_ok in *;clear heq.
  - split;eauto.
    + constructor.
      eauto.
    + constructor.
      * red.
        cbn.
        destruct x.
        destruct (build_frame_decl_preserve_increasing_order _ _ _ _ _ _ heq0);auto.
        -- destruct (build_frame_lparams_preserve_increasing_order _ _ _ _ _ _ heq_bld_frm_prmprof);auto.
           ++ constructor;cbn in *;auto.
              unfold gt_snd.
              red. cbn.
              omega.
           ++ constructor;cbn in *;auto.
              constructor.
        -- destruct (build_frame_lparams_preserve_increasing_order _ _ _ _ _ _ heq_bld_frm_prmprof);auto.
           ++ constructor;cbn in *;auto.
              red; cbn.
              omega.
           ++ constructor.
              ** constructor.
              ** constructor.
      * eapply (ci_increasing_ids H).
    + apply all_addr_no_overflow_fetch_OK;eauto.
      destruct x;unfold stoszchainparam in *.
      eapply (build_frame_decl_preserve_no_overflow st pdeclpart s z (Datatypes.length CE) x0 stcksize).
      -- eapply (build_frame_lparams_preserve_pos_addr st prmprof) with (lvl:=0%nat);eauto; try omega.
         red. cbn in *. !intros.
         !destruct id;cbn in *.
         ++ !invclear heq;split;auto with zarith.
            generalize Int.modulus_pos;intro ;omega.
         ++ discriminate.
      -- assumption.
      -- eapply (build_frame_lparams_preserve_no_overflow st prmprof);eauto; try omega.
         red. cbn. !intros.
         !destruct id ;cbn in *.
         ++ !invclear heq;split;auto with zarith.
            generalize Int.modulus_pos;intro ;omega.
         ++ discriminate.
Qed.

Lemma add_to_frame_sz: forall stbl fram_sz parname parsubtype p sz,
    add_to_frame stbl fram_sz parname parsubtype =: p
    -> compute_size stbl parsubtype = OK sz
    -> snd p = snd fram_sz + sz.
Proof.
  !!intros until 1.
  rewrite add_to_frame_ok in heq_add_to_fr_parname.
  functional inversion heq_add_to_fr_parname
  ;rewrite <- ?add_to_frame_ok in *
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
    add_to_frame stbl fram_sz parname parsubtype =: p
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
    add_to_frame stbl fram_sz parname parsubtype =: p
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
    add_to_frame stbl fram_sz parname parsubtype =: new_fram_sz
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
  simpl in heq_bool_true.
  rewrite <- Nat.eqb_neq in hneq.
  rewrite hneq in heq_bool_true.
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
  try rewrite <- function_utils.build_frame_lparams_ok;intros;intros.
  - destruct H0.
    + inversion H0.
    + simpl in *.
      !invclear H.
      assumption.
  - remember {| parameter_astnum := _x; parameter_name := nme; parameter_subtype_mark := subtyp_mrk; parameter_mode := _x0 |}  as p.
    decomp H0.
    + destruct H1.
      * subst.
        eapply IHr;eauto.
        right.
        subst x0;simpl.
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
  - inversion heq. 
    right;assumption.
  - up_type.
    remember {| parameter_astnum := _x; parameter_name := nme; parameter_subtype_mark := subtyp_mrk; parameter_mode := _x0 |}  as p.
    specialize (IHr _ heq_bld_frm_lparam' _ heq_bool_true).
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
    -> add_to_frame stbl fram_sz parname parsubtype =: (new_fr, new_sz)
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
      intros [a a'] [b b'] [c c'] H H1;simpl in *.
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
  - intros nme nme_ofs H;simpl in *.
    assert (x>0) by (unshelve eapply compute_size_pos;eauto).
    destruct (nme =? parname)%nat.
    * inversion H;subst.
      omega.
    * specialize (h_upb _ _ H).
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
  simpl in heq_CEfetches_othername.
  rewrite <- Nat.eqb_neq in hneq.
  rewrite hneq in heq_CEfetches_othername.
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
    | List.In ?e ?l => fresh "h_in_" e "_" l
    | List.In ?e _ => fresh "h_in_" e
    | List.In _ _ => fresh "h_in"
    | InA _ ?e ?l => fresh "h_inA_" e "_" l
    | InA _ ?e _ => fresh "h_inA_" e
    | InA _ _ _ => fresh "h_inA"
    | @Forall _ _ ?l => fresh "h_all_" l
    | @Forall _ _ _ => fresh "h_all"
    | not ?th' => let th'_hyp := rename_hyp_list h th' in
                  fresh "NOT_" th'_hyp
    | _ => rename_hyp_overf h th
  end.

Ltac rename_hyp ::= rename_hyp_list.
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
  !invclear heq.
  red. apply Forall_forall.
  !!intros prm0 ?.
  !assert (parameter_name prm0 <> parameter_name prm).
  { intro abs.
    !inversion h_NoDupA.
    apply NOT_h_inA_prm_lparam'.
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
    -> build_frame_lparams stbl fram_sz lparam = OK res
    -> NoDupA eq_fst_idnum (fst fram_sz)
    -> NoDupA eq_fst_idnum (fst res).
Proof.
  !!intros until fram_sz.
  rewrite build_frame_lparams_ok.
  !!functional induction (function_utils.build_frame_lparams stbl fram_sz lparam);simpl;!intros;
    try discriminate;try rewrite <- ?build_frame_lparams_ok in *.
  - !invclear heq.
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
  revert h_incr_order h_fresh_prms_lparam res heq_bld_frm_lparam e x heq_CEfetches_x h_incr_order0  h_all h_upb.
  !!(functional induction (function_utils.build_frame_lparams stbl fram_sz lparam); try discriminate;
     try rewrite <- ?function_utils.build_frame_lparams_ok in *;intros;up_type).
  - simpl in *.
    !invclear heq.
    assumption.
  - rename x into nme_fram_sz.
    !invclear h_all0.
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
      rewrite Forall_forall in h_all_lparam'.
      specialize (h_all_lparam' prmspec h_in_prmspec_lparam').
      up_type.
      eapply add_to_frame_correct_none with (parname:=nme);eauto.
      !inversion h_NoDupA_lparam.
      intro abs.
      subst nme.
      rewrite InA_alt in NOT_h_inA.
      apply NOT_h_inA. clear NOT_h_inA.
      exists prmspec.
      unfold eq_param_name;simpl.
      split;auto.
Qed.

(* Extract the list of object names from a declaration block *)
Fixpoint decl_to_lident (stbl:symboltable) (decl:declaration): list idnum :=
  match decl with
  | D_Null_Declaration => nil
  | D_Seq_Declaration _ decl1 decl2 =>
    let lident1 := decl_to_lident stbl decl1 in
    let lident2 := decl_to_lident stbl decl2 in
    List.app lident1 lident2
  | D_Object_Declaration _ objdecl => (objdecl.(object_name) :: nil)
  | D_Type_Declaration x x0 => nil
  | D_Procedure_Body x x0 => nil
  end.


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

Ltac rename_hyp_decl h th :=
  match th with
    | Decl_list_form ?d => fresh "h_decl_list_" d
    | Decl_list_form _ => fresh "h_decl_list"
    | Decl_atomic ?d => fresh "h_decl_atom_" d
    | Decl_atomic _ => fresh "h_decl_atom"
    | _ => rename_hyp_list h th
  end.

Ltac rename_hyp ::= rename_hyp_decl.

Ltac spec H := repeat (specialize (H ltac:(assumption))).

Inductive transl_value_list : list value -> list Values.val -> Prop :=
  tr_lval_nil : transl_value_list nil nil
| tr_lval_cons: forall x x' l l', transl_value x x' -> transl_value_list l l' -> transl_value_list (x::l) (x'::l'). 

Inductive transl_prm_value_list : list parameter_specification -> store -> list Values.val -> Prop :=
  tr_lprmval_nil : transl_prm_value_list nil nil nil
| tr_lprmval_cons: forall x x' l l' prm lprm,
    transl_value x x' -> transl_prm_value_list lprm l l' ->
    transl_prm_value_list (prm::lprm) ((parameter_name prm, x)::l) (x'::l'). 


Definition transl_paramexprlist := Eval cbv beta delta [bind bind2 transl_paramexprlist] in transl_paramexprlist.

Function function_utils_transl_paramexprlist (stbl : symboltable) (CE : compilenv) (el : list expression) (lparams : list parameter_specification) {struct el} :
  res (list expr) :=
  let (l, l0) := (el, lparams) in
  match l with
  | nil => match l0 with
           | nil => OK nil
           | _ :: _ => Error (msg "Bad number of arguments")
           end
  | e1 :: e2 =>
      match l0 with
      | nil => Error (msg "Bad number of arguments")
      | p1 :: p2 =>
          match parameter_mode p1 with
          | In =>
              match transl_expr stbl CE e1 with
              | OK x => match function_utils_transl_paramexprlist stbl CE e2 p2 with
                        | OK x0 => OK (x :: x0)
                        | Error msg => Error msg
                        end
              | Error msg => Error msg
              end
          | Out =>
              match e1 with
              | E_Literal _ _ => Error (msg "Out or In Out parameters should be names")
              | E_Name _ nme =>
                  match transl_name stbl CE nme with
                  | OK x => match function_utils_transl_paramexprlist stbl CE e2 p2 with
                            | OK x0 => OK (x :: x0)
                            | Error msg => Error msg
                            end
                  | Error msg => Error msg
                  end
              | E_Binary_Operation _ _ _ _ => Error (msg "Out or In Out parameters should be names")
              | E_Unary_Operation _ _ _ => Error (msg "Out or In Out parameters should be names")
              end
          | In_Out =>
              match e1 with
              | E_Literal _ _ => Error (msg "Out or In Out parameters should be names")
              | E_Name _ nme =>
                  match transl_name stbl CE nme with
                  | OK x => match function_utils_transl_paramexprlist stbl CE e2 p2 with
                            | OK x0 => OK (x :: x0)
                            | Error msg => Error msg
                            end
                  | Error msg => Error msg
                  end
              | E_Binary_Operation _ _ _ _ => Error (msg "Out or In Out parameters should be names")
              | E_Unary_Operation _ _ _ => Error (msg "Out or In Out parameters should be names")
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
Ltac rename_hyp ::= rename_tmp.


(* 
Lemma copy_in_cps:
  forall st s pb_lvl sto prmnme e_v lparam le res,
  copy_in st s (push (pb_lvl, sto) prmnme e_v) lparam le (Normal (pb_lvl, res ++ sto))
  -> copy_in st s (push (pb_lvl, nil) prmnme e_v) lparam le (Normal (push (pb_lvl, nil) prmnme e_v)).
Proof.
  !intros.
  remember (push (pb_lvl, sto) prmnme e_v) as h_push1.
  remember (Normal (pb_lvl, res ++ sto)) as h_res.
  revert Heqh_push1 Heqh_res.
  !induction h_copy_in; !intros;subst; try discriminate; try (now constructor).
  - unfold push;simpl.
    econstructor 3;eauto.
Qed.
 *)

(** eval_exprlist ok if copy_in ok *)
(* We probably need to generalize this first, as copy_in is written in CPS. *)
(* This is false, since for inout parameter, eval_name is called, and for our parameters, nothing is called. *)

Proposition copy_in_lvl : forall st s pb_lvl sto prms_profile args f,
  copy_in st s (pb_lvl,sto) prms_profile args (Normal f) ->
  exists sto', f = (pb_lvl,sto').
Proof.
  !intros.
  remember (pb_lvl, sto) as pb_lvl_sto.
  remember (Normal f) as h_norm_f.
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
    match_env st s CE (Values.Vptr spb ofs) locenv g m
    -> transl_paramexprlist st CE args prms_profile =: args_t
    (* je veux exprimer la propriété qui parle  *)
    -> copy_in st s (pb_lvl,sto) prms_profile args (Normal (pb_lvl,sto'))
    -> exists lval_t, eval_exprlist g (Values.Vptr spb ofs) locenv m args_t lval_t
(*             sto'' /\ copy_in st s (pb_lvl,nil) prms_profile args (Normal (pb_lvl,sto'')) *)
(*                       /\ sto' = List.app sto'' sto *)
.
Proof.
  !intros.
  remember (Normal (pb_lvl, sto')) as res_copy_in.
  remember (pb_lvl, sto) as pb_lvl_sto.
  revert heq_transl_params_args_t h_match_env Heqres_copy_in Heqpb_lvl_sto .
  revert spb ofs locenv g m sto pb_lvl args_t sto'.
  !induction h_copy_in; try discriminate;subst;repeat eq_same_clear;intros.
  - subst.
    rewrite <- transl_paramexprlist_ok in heq_transl_params_args_t;
    functional inversion heq_transl_params_args_t;subst;
      rewrite ?transl_paramexprlist_ok in *.
    inversion Heqres_copy_in;subst;clear Heqres_copy_in.
    exists  (@nil Values.val).
    constructor.
  - rewrite <- transl_paramexprlist_ok in heq_transl_params_args_t;
      functional inversion heq_transl_params_args_t;subst; rewrite ?transl_paramexprlist_ok in *;
      match goal with
      | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
      end.
    !!edestruct IHh_copy_in;clear IHh_copy_in;eauto.
    + unfold push;simpl. reflexivity.
    + assert (h_transl:=transl_expr_ok _ _ _ _ H9 _ _ _ _ _ _ h_eval_expr_e_e_v h_match_env).
      !!destruct h_transl as [v_t [? ?]].
      exists (x_v::x1);repeat split;eauto.
      econstructor;eauto.
  - rewrite <- transl_paramexprlist_ok in heq_transl_params_args_t;
      functional inversion heq_transl_params_args_t;subst; rewrite ?transl_paramexprlist_ok in *;
      match goal with
      | H:parameter_mode param = ?a , H': parameter_mode param = ?b |- _ => try now (rewrite H in H';discriminate H')
      end.
    !!edestruct IHh_copy_in;clear IHh_copy_in;eauto.
    + unfold push;simpl. reflexivity.
    + assert (h_transl:=transl_expr_ok _ _ _ _ H9 _ _ _ _ _ _ h_eval_expr_e h_match_env).
      !!destruct h_transl as [v_t [? ?]].
      exists (x_v::x1);repeat split;eauto.
      econstructor;eauto.
  - !!(rewrite <- transl_paramexprlist_ok in heq_transl_params_args_t;
       functional inversion heq_transl_params_args_t;subst; rewrite ?transl_paramexprlist_ok in *;
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
      assert (h_ex:exists typ_nme, type_of_name st n =: typ_nme).
      { admit. (* well typedness of the program? *) }
      !!destruct h_ex as [typ_nme ?] .
      assert (h_ex:exists typ, transl_type st typ_nme =: typ).
      { admit. (* completness of type translation? *) }
      !!destruct h_ex as [typ ?].
      assert (h_ex: exists load_addr_nme, make_load n_t typ =: load_addr_nme).
      { admit. (* completness of make_load? *) }
      !!destruct h_ex as [load_addr_nme ?].
      assert (h_stack_mtch:=(me_stack_match h_match_env)).
      red in h_stack_mtch.
      !!destruct (h_stack_mtch _ _ _ _ _ _ h_eval_name_n_v heq_type_of_name heq_transl_name heq_transl_type heq_make_load) as [v_t [htrsl h_eval]];eauto.
      up_type.
      (* Currently we only have by_value loads (but with arrays this may change) *)
      !functional inversion heq_make_load.
      subst.
      (* From [Cminor.eval_expr (Eload chunk x) v_t] we can deduce that [x] itself can be evaluated to a value. *)
      !inversion h_CM_eval_expr_load_addr_nme_load_addr_nme_v;subst.
      exists (n_t_v::le_t_v).
      constructor;auto.
  - !!(rewrite <- transl_paramexprlist_ok in heq_transl_params_args_t;
       functional inversion heq_transl_params_args_t;subst; rewrite ?transl_paramexprlist_ok in *;
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
      assert (h_ex:exists typ_nme, type_of_name st n =: typ_nme).
      { admit. (* well typedness of the program? *) }
      !!destruct h_ex as [typ_nme ?] .
      assert (h_ex:exists typ, transl_type st typ_nme =: typ).
      { admit. (* completness of type translation? *) }
      !!destruct h_ex as [typ ?].
      assert (h_ex: exists load_addr_nme, make_load n_t typ =: load_addr_nme).
      { admit. (* completness of make_load? *) }
      !!destruct h_ex as [load_addr_nme ?].
      assert (h_stack_mtch:=(me_stack_match h_match_env)).
      red in h_stack_mtch.
      !!destruct (h_stack_mtch _ _ _ _ _ _ h_eval_name_n heq_type_of_name heq_transl_name heq_transl_type heq_make_load) as [v_t [htrsl h_eval]];eauto.
      up_type.
      (* Currently we only have by_value loads (but with arrays this may change) *)
      functional inversion heq_make_load.
      subst.
      (* From [Cminor.eval_expr (Eload chunk x) v_t] we can deduce that [x] itself can be evaluated to a value. *)
      !inversion h_CM_eval_expr_load_addr_nme_load_addr_nme_v;subst.
      exists (n_t_v::le_t_v).
      constructor;auto.
  - up_type.
    !!(rewrite <- transl_paramexprlist_ok in heq_transl_params_args_t;
       functional inversion heq_transl_params_args_t;subst; rewrite ?transl_paramexprlist_ok in *;
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
      assert (h_ex:exists n_t_v, Cminor.eval_expr g (Values.Vptr spb ofs) locenv m n_t n_t_v).
      { admit. }
      !!destruct h_ex as [? ?].
      exists (n_t_v::le_t_v).
      constructor;auto.
Qed.



Ltac rename_transl_exprlist h th :=
  match th with
  | transl_exprlist _ _ ?x = Error _ => fresh "h_trans_exprl_Err_" x
  | transl_exprlist _ _ _ = Error _ => fresh "h_trans_exprl_Err"
  | transl_exprlist _ _ ?x = Some ?y => fresh "h_trans_exprl_" x "_" y
  | transl_exprlist _ _ ?x = Some _ => fresh "h_trans_exprl_" x
  | transl_exprlist _ _ _ = _ => fresh "h_trans_exprl"

  | transl_paramexprlist _ _ ?x _ = Error _ => fresh "h_trans_prmexprl_Err_" x
  | transl_paramexprlist _ _ _ _ = Error _ => fresh "h_trans_prmexprl_Err"
  | transl_paramexprlist _ _ ?x _ = Some ?y => fresh "h_trans_prmexprl_" x "_" y
  | transl_paramexprlist _ _ ?x _ = Some _ => fresh "h_trans_prmexprl_" x
  | transl_paramexprlist _ _ _ _ = _ => fresh "h_trans_prmexprl"

  | eval_exprlist _ _ _ _ ?x Error _ => fresh "h_eval_exprlist_Err_" x
  | eval_exprlist _ _ _ _ _ Error _ => fresh "h_eval_exprlist_Err"
  | eval_exprlist _ _ _ _ ?x (Some ?y) => fresh "h_eval_exprlist_" x "_" y
  | eval_exprlist _ _ _ _ ?x (Some _) => fresh "h_eval_exprlist_" x
  | eval_exprlist _ _ _ _ _ _ => fresh "h_eval_exprlist"
  | _ => rename_hyp_incro h th
  end.
Ltac rename_hyp ::= rename_transl_exprlist.

(* inversion lemma that let the match lvlv with unresolved. *)
Lemma compilenv_inv:
  forall (stbl : symboltable) (enclosingCE : compilenv) (lvl : level)
         (lparams : list parameter_specification) (decl : declaration) res,
    build_compilenv stbl enclosingCE lvl lparams decl = OK res
    -> exists sto sz init_sto_sz fr_prm, res = (((Datatypes.length enclosingCE, sto)::enclosingCE),sz)
                                         /\ init_sto_sz = (((pair 0%nat  0)::nil), 4)
                                         /\ build_frame_lparams stbl init_sto_sz lparams = OK fr_prm
                                         /\ build_frame_decl stbl fr_prm decl = OK (sto, sz).
Proof.
  intros stbl enclosingCE lvl lparams decl res heq_bldCE.
  rewrite <- build_compilenv_ok in heq_bldCE.
  functional inversion heq_bldCE;subst;try discriminate.
  - eauto 10.
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

  Inductive is_copy_in: list expression -> list parameter_specification -> store -> list Values.val -> Prop :=
  | Is_copy_in_nil: forall sto, is_copy_in nil nil sto nil
  | Is_copy_in_In: ∀ e le prm lprm v sto sto' v_t lv_t,
      parameter_mode prm = In ->
      eval_expr stbl s e (Normal v) ->
      transl_value v v_t ->
      is_copy_in le lprm (store_of sto) lv_t ->
      push sto (parameter_name prm) v = sto' ->
      is_copy_in (e::le) (prm::lprm) (store_of sto') (v_t::lv_t)
  | Is_copy_in_In_Out: ∀ ast_num nme le prm lprm v nme_t addr sto v_t lv_t,
      parameter_mode prm = In_Out ->
      eval_name stbl s nme (Normal v) ->
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




Lemma transl_stmt_normal_OK : forall stbl (stm:statement) s s',
    eval_stmt stbl s stm (Normal s') ->
    forall CE (stm':Cminor.stmt),
      invariant_compile CE stbl ->
      transl_stmt stbl CE stm = (OK stm') ->
      forall spb ofs f locenv g m,
        match_env stbl s CE (Values.Vptr spb ofs) locenv g m ->
        exists tr locenv' m',
          Cminor.exec_stmt g f (Values.Vptr spb ofs) locenv m stm' tr locenv' m' Out_normal
          /\  match_env stbl s' CE (Values.Vptr spb ofs) locenv' g m'.
(*with transl_fcall_normal_OK : forall ge m fd vargs t m' vres,
    ...
    eval_funcall ge m fd vargs t m' vres.*)
Proof.
  intros until 1.
  remember (Normal s') as norms'.
  revert dependent s'.
  rename_all_hyps.
  Opaque transl_stmt.
  induction h_eval_stmt;simpl in *;intros ; rename_all_hyps ; eq_same_clear;
  try (rewrite <- transl_stmt_ok in heq_transl_stmt_stm';
        !functional inversion heq_transl_stmt_stm';
        subst;
        try rewrite -> transl_stmt_ok in *); eq_same_clear.
  - eexists. eexists. eexists.
    split.
    + try now constructor.
    + assumption.
  (* assignment no range constraint *)
  - rename x into nme.
    rename st into stbl.
    rename_all_hyps.
    exists Events.E0.
    exists locenv.
    decomp (transl_name_OK_inv _ _ _ _ heq_transl_name);subst.
    !! (edestruct (me_stack_complete h_match_env);eauto).
    decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e _ _ _ _ _ _
                           h_eval_expr_e_e_v h_match_env).
    (* transl_type never fails *)
    assert (hex:exists nme_type_t, transl_type stbl nme_type =: nme_type_t).
    { simpl in *.
      assert (type_of_name stbl (E_Identifier x x0) = OK nme_type).
      { simpl.
        rewrite heq_fetch_exp_type.
        reflexivity. }
      rename_all_hyps.
      eapply (ci_stbl_var_types_ok h_inv_comp_CE_stbl);eauto. }
    !destruct hex.
    (* make_load does not fail on a translated variable coming from CE *)
    !destruct (make_load_no_fail _ _ nme_t _ heq_transl_type).
    (* Cminor.eval_expr does not fail on a translated variable (invariant?) *)
    assert (hex: exists vaddr,
               Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t vaddr).
    { !destruct h_match_env.
      unfold stack_match in h_stk_mtch_s_m.
      generalize (h_stk_mtch_s_m (E_Identifier x x0) x1 nme_t x3 nme_type x2).
      intro h.
      !destruct h;auto.
      (* correction of type_of_name wrt to stbl_exp_type *)
      - simpl in heq_fetch_exp_type.
        simpl.
        rewrite heq_fetch_exp_type.
        reflexivity.
      - decomp h_and.
        unfold make_load in heq_make_load.
        destruct (Ctypes.access_mode x2) eqn:h;simpl in *;try discriminate.
        !invclear heq_make_load.
        !inversion h_CM_eval_expr_x3_x4.
        exists nme_t_v.
        assumption. }
    (* A translated variable always results in a Vptr. *)
    !destruct hex.
    specialize transl_variable_Vptr with
    (1:=h_inv_comp_CE_stbl)
    (2:=(me_stack_localstack_aligned h_match_env))
      (3:=heq_transl_variable)
      (4:= h_CM_eval_expr_nme_t_nme_t_v).
    intro hex.
    decomp hex.
    (* Adresses of translated variables are always writable (invariant?) *)
    !assert (Mem.valid_access m nme_chk x4 (Int.unsigned x5) Writable). {
      apply Mem.valid_access_implies with (p1:=Freeable).
      - !destruct h_match_env.
        eapply h_freeable_CE_m;eauto.
        subst.
        assumption.
      - constructor 2. }
    eapply Mem.valid_access_store in h_valid_access_x4.
    destruct h_valid_access_x4.
    exists x6.
    !assert (exec_stmt g f (Values.Vptr spb ofs) locenv m (Sstore nme_chk nme_t e_t)
                      Events.E0 locenv x6 Out_normal). {
      econstructor;eauto.
      subst.
      simpl.
      eassumption. }
    split.
    * assumption.
    * !invclear h_exec_stmt.
      assert (e_t_v0 = e_t_v).
      { eapply det_eval_expr;eauto. }
      subst e_t_v0.
      constructor; eauto 10.
      -- admit.
      -- eapply assignment_preserve_stack_safe;eauto.
         !intros.
         subst.
         eapply eval_expr_overf;eauto.
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
        assert (type_of_name stbl (E_Identifier x x0) = OK nme_type).
        { simpl.
          rewrite heq_fetch_exp_type.
          reflexivity. }
        eapply (ci_stbl_var_types_ok h_inv_comp_CE_stbl);eauto. }
      !destruct hex.
      (* make_load does not fail on a translated variable coming from CE *)
      !destruct (make_load_no_fail stbl nme_type nme_t x2 heq_transl_type).
      (* Cminor.eval_expr does not fail on a translated variable (invariant?) *)
      assert (hex: exists vaddr,
                 Cminor.eval_expr g (Values.Vptr spb ofs) locenv m nme_t vaddr).
      { !destruct h_match_env.
        unfold stack_match in h_stk_mtch_s_m.
        generalize (h_stk_mtch_s_m (E_Identifier x x0) x1 nme_t x3 nme_type x2).
        intro h.
        !destruct h;auto.
        - simpl in *.
          rewrite heq_fetch_exp_type.
          reflexivity.
        - decomp h_and.
          unfold make_load in heq_make_load.
          destruct (Ctypes.access_mode x2) eqn:h;simpl in *;try discriminate.
          !invclear heq_make_load.
          !inversion h_CM_eval_expr_x3_x4.
          exists nme_t_v.
          assumption. }
      (* A translated variable always results in a Vptr. *)
      !destruct hex.
      specialize transl_variable_Vptr with
      (1:=h_inv_comp_CE_stbl)
        (2:=(me_stack_localstack_aligned h_match_env))
        (3:=heq_transl_variable)
        (4:= h_CM_eval_expr_nme_t_nme_t_v).
      intro hex.
      decomp hex.
      (* Adresses of translated variables are always writable (invariant?) *)
      !assert (Mem.valid_access m nme_chk x4 (Int.unsigned x5) Writable). {
        apply Mem.valid_access_implies with (p1:=Freeable).
        - !destruct h_match_env.
          eapply h_freeable_CE_m;eauto.
          subst.
          assumption.
        - constructor 2. }
      eapply Mem.valid_access_store in h_valid_access_x4.
      destruct h_valid_access_x4.
      exists x6.
      !assert (exec_stmt g f (Values.Vptr spb ofs) locenv m (Sstore nme_chk nme_t e_t)
                         Events.E0 locenv x6 Out_normal). {
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
        -- eapply assignment_preserve_stack_match_CE.
           7: eapply h_storeUpd. ;eauto. 
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
      exists x.
      exists x0.
      exists x1.
      decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e locenv g m s _ (Values.Vptr spb ofs) h_eval_expr_e h_match_env).
      assert (exec_stmt g f (Values.Vptr spb ofs) locenv m
                        (Sifthenelse (Ebinop (Ocmp Cne) e_t (Econst (Ointconst Int.zero)))
                                     b_then b_else) x x0 x1 Out_normal).
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
      exists x.
      exists x0.
      exists x1.
      decomp (transl_expr_ok _ _ _ _ heq_tr_expr_e locenv g m s _ (Values.Vptr spb ofs) h_eval_expr_e h_match_env).
      assert (exec_stmt g f (Values.Vptr spb ofs) locenv m
                        (Sifthenelse (Ebinop (Ocmp Cne) e_t (Econst (Ointconst Int.zero)))
                                     b_then b_else) x x0 x1 Out_normal).
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
    rename H1 into h_cut_until.
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
    !!pose proof (me_stack_match_functions h_match_env).
    red in h_stk_mtch_fun.
    specialize (h_stk_mtch_fun _ _ _ h_fetch_proc_p).
    !!destruct h_stk_mtch_fun as [CE_prefx [CE_sufx [paddr [pnum [fction [lglobdef [h_cut_until_CE [? [? ?]]]]]] ]]].
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
      - eapply semantics_properties.cut_until_spec1;eassumption. (* Lemma todo *)
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
    { admit. (* add to invariant_compile. *) }
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
    remember (set_locals (fn_vars the_proc) (set_params (chaining_expr_from_caller_v :: args_t_v) (fn_params the_proc))) as locenv_empty.

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
              admit. (* from heq_init_sto_sz heq_bld_frm_procedure_parameter_profile and heq1 by monoticity *)
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
              !assert (eval_name st s nme (Normal v)).
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
                 [eval_name st s nme (Normal v)].
                 Sketch: 
                   -> [ eval_name st ((pb_lvl, [ ]) :: suffix_s) nme (Normal v)]
                   -> [eval_name st suffix_s nme (Normal v)]
                   -> [eval_name st s nme (Normal v)]
             *)
            !assert (eval_name st suffix_s nme (Normal v)).
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
              !inversion h_exact_lvlG.
              destruct (Datatypes.length CE_sufx) eqn:heq_lgthCE_sufx.
              - apply length_zero_iff_nil in heq_lgthCE_sufx.
                subst.
                functional inversion heq_transl_name.
              - exists n;split;auto.
                !assert (invariant_compile CE_sufx st).
                { eapply invariant_compile_sublist with (CE1:=[(S n, sto)]);auto. }
                !!pose proof ci_exact_lvls _ _ h_inv_comp_CE_sufx_st.
                inversion h_exact_lvlG_CE_sufx0.
                + subst CE_sufx.
                  !inversion h_exact_lvlG;subst.
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
            !assert (transl_name st CE_sufx (E_Identifier astnum id) =:
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

        assert (match_env st suffix_s CE_sufx (Values.Vptr spb_proc Int.zero) locenv_postchain g m_postchain).

        !assert (match_env st ((pb_lvl, nil) :: suffix_s) ((pb_lvl, nil) :: CE_sufx)
                           (Values.Vptr spb_proc Int.zero) locenv_postchain g m_postchain).
        { split.
          + apply h_stk_mtch.
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
              eapply CompilEnv.Cut_Until_Tail.
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
