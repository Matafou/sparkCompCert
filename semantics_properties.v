Require Import LibHypsNaming.
Require Import semantics.
Require Import Errors.
Require Import more_stdlib function_utils spark2Cminor.
Require Import Morphisms Relations.
Import STACK.

Functional Scheme update_ind := Induction for update Sort Prop.
Functional Scheme updates_ind := Induction for updates Sort Prop.
Functional Scheme fetch_ind := Induction for fetch Sort Prop.

Ltac rename_hyp1 h th :=
  match th with
    | in_bound _ _ _ => fresh "h_inbound"
    | updates ?sto ?x _ = _ => fresh "heq_updates_" sto "_" x
    | updates ?sto ?x _ = _ => fresh "heq_updates_" sto
    | updates ?sto ?x _ = _ => fresh "heq_updates_" x
    | updates ?sto ?x _ = _ => fresh "heq_updates"
    | update ?frm ?x _ = _ => fresh "heq_update_" frm "_" x
    | update ?frm ?x _ = _ => fresh "heq_update_" frm
    | update ?frm ?x _ = _ => fresh "heq_update_" x
    | update ?frm ?x _ = _ => fresh "heq_update"
    | updateG ?stk ?x _ = _ => fresh "heq_updateG_" stk "_" x
    | updateG ?stk ?x _ = _ => fresh "heq_updateG_" stk
    | updateG ?stk ?x _ = _ => fresh "heq_updateG_" x
    | updateG ?stk ?x _ = _ => fresh "heq_updateG"
    | STACK.fetchG ?x ?stk = _ => fresh "heq_SfetchG_" x "_" stk
    | STACK.fetchG ?x ?stk = _ => fresh "heq_SfetchG_" stk
    | STACK.fetchG ?x ?stk = _ => fresh "heq_SfetchG_" x
    | STACK.fetchG ?x ?stk = _ => fresh "heq_SfetchG"
    | fetch ?x ?frm = _ => fresh "heq_fetch_" x "_" frm
    | fetch ?x ?frm = _ => fresh "heq_fetch_" frm
    | fetch ?x ?frm = _ => fresh "heq_fetch_" x
    | fetch ?x ?frm = _ => fresh "heq_fetch"
    | fetches ?x ?sto = _ => fresh "heq_fetches_" x "_" sto
    | fetches ?x ?sto = _ => fresh "heq_fetches_" sto
    | fetches ?x ?sto = _ => fresh "heq_fetches_" x
    | fetches ?x ?sto = _ => fresh "heq_fetches"
    | storeUpdate ?stbl ?s ?nme ?x (Normal ?rs) => fresh "h_storeUpd"
    | storeUpdate ?stbl ?s ?nme ?x ?rs => fresh "h_storeUpd"
    | fetch_var_type _ _ = Error _ => fresh "heq_fetch_var_type_ERR"
    | fetch_var_type _ _ = _ => fresh "heq_fetch_var_type"
    | spark2Cminor.compute_chnk _ ?name = OK ?chk => fresh "heq_compute_chnk_" name "_" chk
    | spark2Cminor.compute_chnk _ ?name = ?chk => fresh "heq_compute_chnk_" name "_" chk
    | spark2Cminor.compute_chnk _ ?name = _ => fresh "heq_compute_chnk_" name
    | spark2Cminor.compute_chnk _ _ = _ => fresh "heq_compute_chnk"
    | symboltable.fetch_exp_type _ _ = _ => fresh "heq_fetch_exp_type"
    | symboltable.fetch_exp_type _ _ = Error _ => fresh "heq_fetch_exp_type_ERR"
    | fetch_exp_type _ _ = None => fresh "heq_fetch_exp_type_none"
    | fetch_exp_type _ _ = _ => fresh "heq_fetch_exp_type"
    | eval_expr _ _ _ (Run_Time_Error _) => fresh "h_eval_expr_RE"
    | eval_expr _ _ ?e (Normal ?v) => fresh "h_eval_expr_" e "_" v
    | eval_expr _ _ _ (Normal ?v) => fresh "h_eval_expr_" v
    | eval_expr _ _ ?e ?v => fresh "h_eval_expr_" e "_" v
    | eval_expr _ _ ?e _ => fresh "h_eval_expr_" e
    | eval_expr _ _ _ ?v => fresh "h_eval_expr_" v
    | eval_expr _ _ _ _ => fresh "h_eval_expr"
    | eval_name _ _ _ (Run_Time_Error _) => fresh "h_eval_name_RE"
    | eval_name _ _ ?e (Normal ?v) => fresh "h_eval_name_" e "_" v
    | eval_name _ _ _ (Normal ?v) => fresh "h_eval_name_" v
    | eval_name _ _ ?e ?v => fresh "h_eval_name_" e "_" v
    | eval_name _ _ ?e _ => fresh "h_eval_name_" e
    | eval_name _ _ _ ?v => fresh "h_eval_name_" v
    | eval_name _ _ _ _ => fresh "h_eval_name"
    | do_overflow_check _ (Run_Time_Error _) => fresh "h_overf_check_RE"
    | do_overflow_check _ _ => fresh "h_overf_check"
    | do_range_check _ _ _ (Run_Time_Error _) => fresh "h_do_range_check_RE"
    | do_range_check _ _ _ _ => fresh "h_do_range_check"
    | do_run_time_check_on_binop _ _ _ (Run_Time_Error _) => fresh "h_do_rtc_binop_RTE"
    | do_run_time_check_on_binop _ _ _ _ => fresh "h_do_rtc_binop"
    | eval_literal _ (Run_Time_Error _)  => fresh "h_eval_literal_RE"
    | eval_literal _ _  => fresh "h_eval_literal"
    | eval_stmt _ _ _ (Run_Time_Error _) => fresh "h_eval_stmt_RE"
    | eval_stmt _ _ _ _ => fresh "h_eval_stmt"
    | eval_decl _ _ _ _ (Run_Time_Error _) => fresh "h_eval_stmt_RE"
    | eval_decl _ _ _ _ _ => fresh "h_eval_stmt"
    | storeUpdate _ _ _ _ (Run_Time_Error _) => fresh "h_storeupdate_RTE"
    | storeUpdate _ _ _ _ _ => fresh "h_storeupdate"
    | do_run_time_check_on_binop _ _ _ (Run_Time_Error _) =>  fresh "h_do_rtc_binop_RE"
    | do_run_time_check_on_binop _ _ _ _ =>  fresh "h_do_rtc_binop"
    | do_run_time_check_on_unop _ _ (Run_Time_Error _) =>  fresh "h_do_rtc_unop_RE"
    | do_run_time_check_on_unop _ _ _ =>  fresh "h_do_rtc_unop"
    | do_division_check _ _ (Run_Time_Error _) => fresh "h_do_division_check_RTE"
    | do_division_check _ _ _ => fresh "h_do_division_check"
    | extract_subtype_range _ ?t ?rge => fresh "subtype_rge_" t "_" rge
    | extract_subtype_range _ ?t _ => fresh "subtype_rge_" t
    | extract_subtype_range _ _ _ => fresh "subtype_rge"
    | copy_out ?st ?s ?pstmt ?paramsprf ?args (Run_Time_Error ?er) => fresh "h_copy_out_RE"
    | copy_out ?st ?s ?pstmt ?paramsprf ?args (Normal ?s') => fresh "h_copy_out_" s "_" s'
    | copy_out ?st ?s ?pstmt ?paramsprf ?args ?s' => fresh "h_copy_out_" s "_" s'
    | copy_out ?st ?s ?pstmt ?paramsprf ?args _ => fresh "h_copy_out_" s
    | copy_out ?st ?s ?pstmt ?paramsprf ?args _ => fresh "h_copy_out"

    | copy_in ?st ?s ?fr ?paramsprf ?args (Run_Time_Error ?er) => fresh "h_copy_in_RE"
    | copy_in ?st ?s ?fr ?paramsprf ?args (Normal ?fr') => fresh "h_copy_in_" fr "_" fr'
    | copy_in ?st ?s ?fr ?paramsprf ?args ?fr' => fresh "h_copy_in_" fr "_" fr'
    | copy_in ?st ?s ?fr ?paramsprf ?args _ => fresh "h_copy_in_" fr
    | copy_in ?st ?s ?fr ?paramsprf ?args _ => fresh "h_copy_in"
    | cut_until ?st ?s ?fr ?paramsprf ?args (Run_Time_Error ?er) => fresh "h_cut_until_RE"
    | cut_until ?st ?s ?fr ?paramsprf ?args (Normal ?fr') => fresh "h_cut_until_" fr "_" fr'
    | cut_until ?st ?s ?fr ?paramsprf ?args ?fr' => fresh "h_cut_until_" fr "_" fr'
    | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "h_cut_until_" fr
    | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "h_cut_until"

    | symboltable.fetch_proc ?p _ = None => fresh "h_fetch_proc_None_" p
    | symboltable.fetch_proc _ _ = None => fresh "h_fetch_proc_None"
    | symboltable.fetch_proc ?p _ = Some ?r => fresh "h_fetch_proc_" p "_" r
    | symboltable.fetch_proc ?p _ = ?r => fresh "h_fetch_proc_" p "_" r
    | symboltable.fetch_proc ?p _ = _ => fresh "h_fetch_proc_" p
    | symboltable.fetch_proc _ _ = _ => fresh "h_fetch_proc"
  end.

Ltac rename_hyp ::= rename_hyp1.


Lemma updates_ok_none : forall sto x v, updates sto x v = None <-> fetches x sto = None.
Proof.
  !intros.
  split;!intro.
  - !functional induction (updates sto x v).
    + discriminate.
    + discriminate.
    + unfold id in *. (* scorie from libhyprenaming *)
      simpl.
      rewrite hbeqnat_false.
      apply IHo.
      assumption.
    + reflexivity.
  - !functional induction (fetches x sto).
    + discriminate.
    + unfold id in *. (* scorie from libhyprenaming *)
      simpl.
      rewrite hbeqnat_false.
      rewrite IHo;auto.
    + reflexivity.
Qed.

(* the none version could be solved by functiona inversion but it is
   ot applicable here due to a bug in Function with functors. *)
Lemma update_ok_none : forall frm x v, update frm x v = None <-> fetch x frm = None.
Proof.
  !intros.
  split.
  - !functional induction (update frm x v);!intro.
    + discriminate.
    + unfold fetch.
      eapply updates_ok_none;eauto.
  - unfold fetch, update.
    !intro.
    rewrite <- updates_ok_none in heq_fetches_x.
    rewrite heq_fetches_x.
    reflexivity.
Qed.


(* the none version could be solved by functiona inversion but it is
   ot applicable here due to a bug in Function with functors. *)
Lemma updateG_ok_none : forall stk x v, updateG stk x v = None <-> fetchG x stk = None.
Proof.
  !intros.
  split.
  - !functional induction (updateG stk x v);!intro.
    + discriminate.
    + discriminate.
    + unfold id in *.
      simpl.
      apply update_ok_none in heq_update_f_x.
      rewrite heq_update_f_x.
      auto.
    + reflexivity.
  - !functional induction (fetchG x stk);!intro.
    + discriminate.
    + simpl.
      rewrite IHo;auto.
      rewrite <- update_ok_none in heq_fetch_x_f;eauto.
      rewrite heq_fetch_x_f;auto.
   + reflexivity.
Qed.

Lemma fetches_ok: forall id sto v, fetches id sto = Some v -> resides id sto = true.
Proof.
  intros id sto v.
  !functional induction (fetches id sto);!intros;try discriminate.
  - inversion heq.
    subst.
    cbn.
    rewrite hbeqnat_true.
    reflexivity.
  - cbn.
    rewrite hbeqnat_false.
    auto.
Qed.

Lemma compilenv_fetches_resides: forall nme x,
    (exists res, CompilEnv.fetches nme x = Some res) <->
    CompilEnv.resides nme x = true.
Proof.
  !!intros ? ?.
  !functional induction (CompilEnv.fetches nme x);cbn;!intros;subst.
  - rewrite hbeqnat_true.
    split;eauto.
  - rewrite hbeqnat_false.
    assumption.
  - split;!intros; try discriminate.
    decompose [ex] h_ex.
    discriminate.
Qed.


Lemma fetches_ok_none: forall id sto, fetches id sto = None -> resides id sto = false.
Proof.
  intros id sto.
  !functional induction (fetches id sto);!intros;try discriminate.
  - cbn.
    rewrite hbeqnat_false.
    auto.
  - cbn.
    reflexivity.
Qed.

Lemma fetch_ok: forall id sto v, fetch id sto = Some v -> reside id sto = true.
Proof.
  unfold fetch, reside.
  !intros.
  apply fetches_ok in heq_fetches_id.
  assumption.
Qed.

Lemma fetch_ok_none: forall id sto, fetch id sto = None -> reside id sto = false.
Proof.
  unfold fetch, reside.
  !intros.
  apply fetches_ok_none in heq_fetches_id.
  assumption.
Qed.

Lemma fetchG_ok_none: forall id sto, fetchG id sto = None -> resideG id sto = false.
Proof.
  intros id sto.
  !functional induction (fetchG id sto);!intros;try discriminate.
  - simpl.
    !!destruct (reside id f) eqn:heq_reside.
    + apply fetch_ok_none in heq_fetch_id_f.
      rewrite heq_fetch_id_f in heq_bool_true;discriminate.
    + auto.
  - reflexivity. 
Qed.

Lemma fetchG_ok: forall id sto v, fetchG id sto = Some v -> resideG id sto = true.
Proof.
  intros id sto.
  !functional induction (fetchG id sto);!intros;try discriminate.
  - simpl.
    !!destruct (reside id f) eqn:heq_reside.
    + reflexivity.
    + apply fetch_ok in heq_fetch_id_f.
      rewrite heq_fetch_id_f in heq_bool_false;discriminate.
  - simpl.
    !!destruct (reside id f) eqn:heq_reside.
    + reflexivity.
    + apply IHo in heq_SfetchG_id_s'.
      assumption.
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
    !invclear heq_updates_s'_x;simpl.
    rewrite hbeqnat_false.
    apply IHo.
    assumption.
  - discriminate.
  - discriminate.
Qed.

Lemma updates_ok_same_orig: forall sto id v sto',
    updates sto id v = Some sto'
    -> exists v', fetches id sto = Some v'.
Proof.
  intros sto id v.
  !functional induction (updates sto id v);!intros;simpl in *;intros.
  - rewrite hbeqnat_true.
    eauto.
  - rewrite hbeqnat_false.
    eapply IHo;eauto.
  - discriminate.
  - discriminate.
Qed.

Lemma updates_ok_same_resides: forall sto id v sto',
    updates sto id v = Some sto'
    -> resides id sto' = true.
Proof.
  !intros.
  eapply fetches_ok.
  eapply updates_ok_same;eauto.
Qed.

Lemma updates_ok_same_resides_orig: forall sto id v sto',
    updates sto id v = Some sto'
    -> resides id sto = true.
Proof.
  !intros.
  !!pose proof updates_ok_same_orig _ _ _ _ heq_updates_sto_id.
  destruct h_ex.
  eapply fetches_ok;eauto.
Qed.

Lemma update_ok_same: forall frm id v frm',
    update frm id v = Some frm'
    -> fetch id frm' = Some v.
Proof.
  intros until v.
  unfold fetch, update.
  !intros.
  destruct (updates (store_of frm) id v) eqn:heq_upd.
  - !invclear heq;simpl.
    eapply updates_ok_same;eauto.
  - discriminate.
Qed.


Lemma update_ok_same_orig: forall frm id v frm',
    update frm id v = Some frm'
    -> exists v', fetch id frm = Some v'.
Proof.
  intros until v.
  unfold fetch, update.
  !intros.
  destruct (updates (store_of frm) id v) eqn:heq_upd.
  - !invclear heq;simpl.
    !!pose proof updates_ok_same_orig _ _ _ _ heq_upd.
    assumption.
  - discriminate.
Qed.

Lemma update_ok_same_reside: forall sto id v sto',
    update sto id v = Some sto'
    -> reside id sto' = true.
Proof.
  !intros.
  eapply fetch_ok.
  eapply update_ok_same;eauto.
Qed.

Lemma update_ok_same_reside_orig: forall sto id v sto',
    update sto id v = Some sto'
    -> reside id sto = true.
Proof.
  !intros.
  !!pose proof update_ok_same_orig _ _ _ _ heq_update_sto_id.
  destruct h_ex.
  eapply fetch_ok;eauto.
Qed.

Lemma updateG_ok_same: forall stk id v stk',
    updateG stk id v = Some stk'
    -> fetchG id stk' = Some v.
Proof.
  intros until v.
  !functional induction (updateG stk id v);simpl;!intros.
  - !invclear heq;simpl.
    apply update_ok_same in heq_update_f_x.
    rewrite heq_update_f_x.
    reflexivity.
  - !invclear heq;simpl.
    specialize (IHo _ heq_updateG_s'_x).
    destruct (fetch x f) eqn:h.
    + apply update_ok_none in heq_update_f_x.
      rewrite heq_update_f_x in h;discriminate.
    + assumption.
  - discriminate.
  - discriminate.
Qed.

Lemma updateG_ok_same_orig: forall stk id v stk',
    updateG stk id v = Some stk'
    -> exists v', fetchG id stk = Some v'.
Proof.
  intros until v.
  !functional induction (updateG stk id v);simpl;!intros;try discriminate.
  - !invclear heq;simpl.
    !destruct (update_ok_same_orig _ _ _ _ heq_update_f_x).
    rewrite heq_fetch_x_f.
    eauto.
  - !invclear heq;simpl.
    apply update_ok_none in heq_update_f_x.
    rewrite heq_update_f_x.
    eapply IHo.
    eauto.
Qed.

Lemma updateG_ok_same_resideG: forall stk id v stk',
    updateG stk id v = Some stk'
    -> resideG id stk' = true.
Proof.
  !intros.
  eapply fetchG_ok.
  eapply updateG_ok_same.
  eauto.
Qed.



Lemma updates_ok_others: forall sto id v sto',
    updates sto id v = Some sto' ->
    forall id', id<>id' -> fetches id' sto = fetches id' sto'.
Proof.
  intros until v.
  !functional induction (updates sto id v);!intros;simpl in *;intros.
  - !invclear heq;simpl.
    rewrite -> Nat.eqb_eq in hbeqnat_true.
    subst.
    apply Nat.neq_sym in hneq.
    rewrite <- Nat.eqb_neq in hneq.
    rewrite hneq in *.
    reflexivity.
  - !invclear heq;simpl.
    destruct (Nat.eq_dec id' y).
    + subst.
      rewrite Nat.eqb_refl in *.
      reflexivity.
    + rewrite <- Nat.eqb_neq in n.
      rewrite n in *.
      eapply IHo;eauto.
  - discriminate.
  - discriminate.
Qed.

Lemma update_ok_others: forall frm id v frm',
    update frm id v = Some frm' ->
    forall id', id<>id' -> fetch id' frm = fetch id' frm'.
Proof.
  intros until v.
  !functional induction (STACK.update frm id v);!destruct frm;simpl in *;!intros.
  - !invclear heq;simpl.
    eapply updates_ok_others in heq_updates_id;eauto.
  - discriminate.
Qed.

Lemma update_ok_others_reside: forall frm id v frm',
    update frm id v = Some frm' ->
    forall id', id<>id' -> reside id' frm = reside id' frm'.
Proof.
  !intros.
  !!pose proof update_ok_others _ _ _ _ heq_update_frm_id _ hneq.
  destruct (fetch id' frm) eqn:heq_fetch.
  - apply fetch_ok in heq_fetch.
    rewrite heq_fetch.
    symmetry in heq_fetch_id'_frm.
    apply fetch_ok in heq_fetch_id'_frm.
    rewrite heq_fetch_id'_frm.
    reflexivity.
  - apply fetch_ok_none in heq_fetch.
    rewrite heq_fetch.
    symmetry in heq_fetch_id'_frm.
    apply fetch_ok_none in heq_fetch_id'_frm.
    rewrite heq_fetch_id'_frm.
    reflexivity.
Qed.

Lemma updateG_ok_others: forall stk id v stk',
    updateG stk id v = Some stk' ->
    forall id', id<>id' -> fetchG id' stk = fetchG id' stk'.
Proof.
  intros until v.
  !functional induction (updateG stk id v);simpl;!intros.
  - !invclear heq;simpl.
    !! (destruct (fetch id' f) eqn:h).
    + erewrite update_ok_others in heq_fetch_id'_f;eauto.
      rewrite heq_fetch_id'_f.
      reflexivity.
    + erewrite update_ok_others in heq_fetch_id'_f;eauto.
      rewrite heq_fetch_id'_f.
      reflexivity.
  - !invclear heq;simpl.
    !! (destruct (fetch id' f) eqn:h).
    + reflexivity.
    + eapply IHo;eauto.
  - discriminate.
  - discriminate.
Qed.


Lemma updateG_ok_others_resideG: forall frm id v frm',
    updateG frm id v = Some frm' ->
    forall id', id<>id' -> resideG id' frm = resideG id' frm'.
Proof.
  !intros.
  !!pose proof updateG_ok_others _ _ _ _ heq_updateG_frm_id _ hneq.
  destruct (fetchG id' frm) eqn:heq_fetchG.
  - apply fetchG_ok in heq_fetchG.
    rewrite heq_fetchG.
    symmetry in heq_SfetchG_id'_frm.
    apply fetchG_ok in heq_SfetchG_id'_frm.
    rewrite heq_SfetchG_id'_frm.
    reflexivity.
  - apply fetchG_ok_none in heq_fetchG.
    rewrite heq_fetchG.
    symmetry in heq_SfetchG_id'_frm.
    apply fetchG_ok_none in heq_SfetchG_id'_frm.
    rewrite heq_SfetchG_id'_frm.
    reflexivity.
Qed.


Lemma updateG_ok_same_frameG: forall stk id v lvl sto stk',
    updateG stk id v = Some stk'
    -> frameG id stk = Some (lvl,sto)
    -> exists sto', frameG id stk' = Some (lvl,sto').
Proof.
  intros until v.
  !functional induction (updateG stk id v);simpl;!intros;try discriminate.
  - !invclear heq;simpl.
    !!pose proof update_ok_same_reside _ _ _ _ heq_update_f_x.
    !!pose proof update_ok_same_reside_orig _ _ _ _ heq_update_f_x.
    rewrite heq_bool_true.
    rewrite heq_bool_true0 in heq0.
    !invclear heq0.
    unfold update in heq_update_f_x.
    cbn in *.
    destruct (updates sto x v) eqn:heq.
    + eauto.
    + discriminate.
  - !invclear heq;simpl.
    rewrite update_ok_none in heq_update_f_x.
    apply fetch_ok_none in heq_update_f_x.
    rewrite heq_update_f_x.
    rewrite heq_update_f_x in heq0.
    eauto.
Qed.

Lemma updateG_ok_same_frameG_orig: forall stk id v lvl sto stk',
    updateG stk id v = Some stk'
    -> frameG id stk' = Some (lvl,sto)
    -> exists sto', frameG id stk = Some (lvl,sto').
Proof.
  intros until v.
  !functional induction (updateG stk id v);simpl;!intros;try discriminate.
  - !invclear heq;simpl.
    !!pose proof update_ok_same_reside _ _ _ _ heq_update_f_x.
    !!pose proof update_ok_same_reside_orig _ _ _ _ heq_update_f_x.
    simpl in heq0.
    rewrite heq_bool_true in heq0.
    rewrite heq_bool_true0.
    !invclear heq0.
    unfold update in heq_update_f_x.
    cbn in *.
    destruct (updates (store_of f) x v) eqn:heq.
    + destruct f;simpl in *.
      !invclear heq_update_f_x.
      eauto.
    + discriminate.
  - !invclear heq;simpl.
    simpl in heq0.
    rewrite update_ok_none in heq_update_f_x.
    apply fetch_ok_none in heq_update_f_x.
    rewrite heq_update_f_x.
    rewrite heq_update_f_x in heq0.
    eapply IHo; eauto.
Qed.

Lemma storeUpdate_id_ok_others: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (E_Identifier ast_num id) v (Normal stk') ->
    forall id', id<>id' -> fetchG id' stk = fetchG id' stk'.
Proof.
  !intros.
  !invclear h_storeUpd.
  eapply updateG_ok_others;eauto.
Qed.

Lemma storeUpdate_id_ok_same: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (E_Identifier ast_num id) v (Normal stk') ->
    fetchG id stk' = Some v.
Proof.
  !intros.
  !invclear h_storeUpd.
  eapply updateG_ok_same;eauto.
Qed.

Lemma storeUpdate_id_ok_same_eval_name: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (E_Identifier ast_num id) v (Normal stk') ->
    forall ast_num' v',
      eval_name stbl stk' (E_Identifier ast_num' id) (Normal v') ->
      v = v'.
Proof.
  !intros.
  !inversion h_eval_name_v'.
  specialize (storeUpdate_id_ok_same _ _ _ _ _ _ h_storeUpd).
  !intro.
  rewrite heq_SfetchG_id_stk' in heq_SfetchG_id_stk'0.
  inversion heq_SfetchG_id_stk'0.
  reflexivity. 
Qed.

Lemma storeUpdate_id_ok_others_eval_name: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (E_Identifier ast_num id) v (Normal stk') ->
    forall ast_num' ast_num'' id' v' v'',
      id<>id' ->
      eval_name stbl stk (E_Identifier ast_num' id') (Normal v') ->
      eval_name stbl stk' (E_Identifier ast_num'' id') (Normal v'') ->
      v' = v''.
Proof.
  !intros.
  !inversion h_eval_name_v'.
  !inversion h_eval_name_v''.
  specialize (storeUpdate_id_ok_others _ _ _ _ _ _ h_storeUpd).
  !intro.
  specialize (H id' hneq).
  rewrite heq_SfetchG_id'_stk in H.
  rewrite heq_SfetchG_id'_stk' in H.
  inversion H.
  reflexivity.
Qed.



Lemma updateIndexedComp_id_ok_others: forall arr k v arr',
    arr' = updateIndexedComp arr k v
    -> forall k', k<>k' -> array_select arr' k' = array_select arr k'.
Proof.
  intros until v.
  !functional induction (updateIndexedComp arr k v);!intros;subst;simpl in *.
  - apply Zeq_bool_eq in heq_Z_true;subst;simpl.
    apply Zeq_is_neq_bool in hneq.
    rewrite hneq.
    reflexivity.
  - specialize (IHl (updateIndexedComp a1 i v) eq_refl _ hneq).
    rewrite IHl.
    reflexivity.
  - apply Zeq_is_neq_bool in hneq.
    rewrite hneq.
    reflexivity.
Qed.

Lemma updateIndexedComp_id_ok_same: forall arr k v arr',
    arr' = updateIndexedComp arr k v
    -> array_select arr' k = Some v.
Proof.
  intros until v.
  !functional induction (updateIndexedComp arr k v);!intros;subst;simpl in *.
  - rewrite heq_Z_true.
    reflexivity.
  - rewrite heq_Z_false.
    apply IHl;auto.
  - replace (Zeq_bool i i) with true;auto.
    symmetry.
    apply Zeq_is_eq_bool.
    reflexivity.
Qed.

Set Printing Width 120.

Lemma arrayUpdate_id_ok_others: forall arr k v arr',
    arrayUpdate (ArrayV arr) k v = Some (ArrayV arr')
    -> forall k', k<>k' -> array_select arr' k' = array_select arr k'.
Proof.
  intros arr k v arr' heq_arrayUpdate k'.
  simpl in *.
  !invclear heq_arrayUpdate.
  eapply updateIndexedComp_id_ok_others;eauto.
Qed.


(* 
Inductive follow_chaining: Values.val -> Memory.Mem.mem -> nat -> Values.val -> Prop :=
  FC1: forall sp m, follow_chaining sp m 0 sp
| FC2: forall vsp m lvl vsp' v,
        Memory.Mem.loadv AST.Mint32 m vsp = Some vsp'
        -> follow_chaining vsp' m lvl v
        -> follow_chaining vsp m (S lvl) v.
 *)

(** [eq_frame sto b ofs m] means that the memory m contains a block
    at address b, and this block from offset [ofs] matches the spark
    frame [sto]. *)
(* FIXME: are we looking at the stack in the wrong direction? *)
Inductive eq_frame:
  STACK.store -> Values.block -> Integers.Int.int -> Memory.Mem.mem -> Prop :=
  MF1: forall spb ofs m, eq_frame nil spb ofs m
| MF2: forall fr spb ofs m id vid t_vid,
    Memory.Mem.load AST.Mint32 m spb ofs = Some t_vid ->
    transl_value vid t_vid ->
    eq_frame fr spb (Integers.Int.add (Integers.Int.repr ofs)
                                      (Integers.Int.repr 4)) m ->
    eq_frame ((id,vid)::fr) spb (Integers.Int.repr ofs) m.

(** [match_env sta b m] means that the chained Cminor stack at address
    [b] in memory m ([b] is the adress of the bottom of the top stack)
    matches spark stack [s]. *)
Inductive eq_env: STACK.stack -> Values.block -> Memory.Mem.mem -> Prop :=
  ME1: forall spb m, eq_env nil spb m
| ME2: forall s sto (lvl:STACK.scope_level) fr spb spb' m,
         eq_frame fr spb (Integers.Int.repr 4) m
         -> eq_env s spb' m
         -> eq_env ((lvl,sto)::s) spb m.



(*
Lemma spec_transl_name : forall stbl CE astnum id e,
    transl_variable stbl CE astnum id = OK e ->

.
Proof.
  #
Qed.



(** ** Normalized names

Normalized names are like names, except that any expression in it has
been evaluated into a cell number. *)
Inductive Nname: Type :=
  NE_Identifier : idnum -> Nname
| NE_Indexed_Component : Nname -> Z -> Nname
| NE_Selected_Component : Nname -> idnum -> Nname. (* what if (f(x,y,z).foo?? *)




Inductive solve_name (stbl:symboltable) (stck:stack): name -> Nname -> Prop :=
  Solve_E_Identifier: forall _x id,
    solve_name stbl stck (E_Identifier _x id) (NE_Identifier id)
| Solve_E_Indexed_Component : forall _x (id:name) e nid n,
    eval_expr stbl stck e (Normal (Int n)) ->
    solve_name stbl stck id nid->
    solve_name stbl stck (E_Indexed_Component _x id e) (NE_Indexed_Component nid n)
| Solve_E_Selected_Component : forall _x id nme nnme,
    solve_name stbl stck nme nnme ->
    solve_name stbl stck (E_Selected_Component _x nme id) (NE_Selected_Component nnme id).

Lemma foramm: forall stbl stck e v,
    eval_expr stbl stck e (Normal v) ->
    eval_expr
.
Proof.
  #
Qed.

*)




(*
Lemma storeUpdate_arr_ok_others:
  forall astnum (idarr:idnum) stk varr i v  varr' stbl stk',
  fetchG idarr stk = Some (ArrayV varr) ->
  arrayUpdate (ArrayV varr) i v = Some (ArrayV varr') ->
  storeUpdate stbl stk (E_Identifier astnum idarr) (ArrayV varr') (Normal stk') ->
  fetchG idarr stk' = Some (ArrayV varr') ->
  
.
Proof.
  !intros.
  eapply storeUpdate_id_ok_same;eauto.
Qed.





Lemma storeUpdate_arr_ok_others:
  forall astnum (idarr:idnum) stk varr i v  varr' stbl stk',
  fetchG idarr stk = Some (ArrayV varr) ->
  arrayUpdate (ArrayV varr) i v = Some (ArrayV varr') ->
  storeUpdate stbl stk (E_Identifier astnum idarr) (ArrayV varr') (Normal stk') ->
  fetchG idarr stk' = Some (ArrayV varr').

  
  
  storeUpdate stbl stk (E_Indexed_Component ast_num nmearr i) (ArrayV varr) (Normal stk') ->
  forall id', id<>id' -> fetchG id' stk = fetchG id' stk'.
Proof.
  !intros.
  !invclear h_storeUpd.
  eapply updateG_ok_others;eauto.
Qed.
*)


(* not true since the storing may change the value of nme itself:
    { t[2] == 2, thus: t[t[2]] = t[2] = 2 }
    t[t[2]] := 5;
    { now t[2] = 5 and thus t[t[2]] = t[5] which is different from 5. }
 if [t[i]] is initally equal to i, then t[t[i]]
 *)
(*
Lemma storeUpdate_ok_same:
  forall stbl s nme (v:value) s',
    storeUpdate stbl s nme v (Normal s') ->
    eval_name stbl s' nme (Normal x).
Proof.
*)
