Require Import LibHypsNaming.
Require Import Errors.
Require Import eval.
Require Import more_stdlib function_utils spark2Cminor.
Require Import Morphisms Relations.
Import STACK.
Require Import store_util.
(* Import STACK.ST. *)


(* Functional Scheme update_ind := Induction for update Sort Prop. *)
(* Functional Scheme updates_ind := Induction for updates Sort Prop. *)
(* Functional Scheme fetch_ind := Induction for fetch Sort Prop. *)

Ltac rename_hyp_sem h th :=
  match th with
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
  | evalExp _ _ _ (RTE _) => fresh "h_eval_expr_RE"
  | evalExp _ _ ?e (OK ?v) => fresh "h_eval_expr_" e "_" v
  | evalExp _ _ _ (OK ?v) => fresh "h_eval_expr_" v
  | evalExp _ _ ?e ?v => fresh "h_eval_expr_" e "_" v
  | evalExp _ _ ?e _ => fresh "h_eval_expr_" e
  | evalExp _ _ _ ?v => fresh "h_eval_expr_" v
  | evalExp _ _ _ _ => fresh "h_eval_expr"
  | evalName _ _ _ (RTE _) => fresh "h_eval_name_RE"
  | evalName _ _ ?e (OK ?v) => fresh "h_eval_name_" e "_" v
  | evalName _ _ _ (OK ?v) => fresh "h_eval_name_" v
  | evalName _ _ ?e ?v => fresh "h_eval_name_" e "_" v
  | evalName _ _ ?e _ => fresh "h_eval_name_" e
  | evalName _ _ _ ?v => fresh "h_eval_name_" v
  | evalName _ _ _ _ => fresh "h_eval_name"
  | overflowCheck _ (RTE _) => fresh "h_overf_check_RE"
  | overflowCheck _ _ => fresh "h_overf_check"
  | rangeCheck _ _ _ (RTE _) => fresh "h_do_range_check_RE"
  | rangeCheck _ _ _ _ => fresh "h_do_range_check"
  | do_run_time_check_on_binop _ _ _ (RTE _) => fresh "h_do_rtc_binop_RTE"
  | do_run_time_check_on_binop _ _ _ _ => fresh "h_do_rtc_binop"
  | evalLiteral _ (RTE _)  => fresh "h_eval_literal_RE"
  | evalLiteral _ _  => fresh "h_eval_literal"
  | evalStmt _ _ _ (RTE _) => fresh "h_eval_stmt_RE"
  | evalStmt _ _ _ _ => fresh "h_eval_stmt"
  | evalDecl _ _ _ _ (RTE _) => fresh "h_eval_decl_RE"
  | evalDecl _ _ _ _ _ => fresh "h_eval_decl"
  | storeUpdate _ _ _ _ (RTE _) => fresh "h_storeUpd_RE"
  | storeUpdate _ _ _ _ _ => fresh "h_storeUpd"
  | do_run_time_check_on_binop _ _ _ (RTE _) =>  fresh "h_do_rtc_binop_RE"
  | do_run_time_check_on_binop _ _ _ _ =>  fresh "h_do_rtc_binop"
  | do_run_time_check_on_unop _ _ (RTE _) =>  fresh "h_do_rtc_unop_RE"
  | do_run_time_check_on_unop _ _ _ =>  fresh "h_do_rtc_unop"
  | divCheck _ _ _ (RTE _) => fresh "h_do_division_check_RTE"
  | divCheck _ _ _ _ => fresh "h_do_division_check"
  | extract_subtype_range _ ?t ?rge => fresh "subtype_rge_" t "_" rge
  | extract_subtype_range _ ?t _ => fresh "subtype_rge_" t
  | extract_subtype_range _ _ _ => fresh "subtype_rge"
  | copyOut ?st ?s ?pstmt ?paramsprf ?args (RTE ?er) => fresh "h_copy_out_RE"
  | copyOut ?st ?s ?pstmt ?paramsprf ?args (OK ?s') => fresh "h_copy_out_" s "_" s'
  | copyOut ?st ?s ?pstmt ?paramsprf ?args ?s' => fresh "h_copy_out_" s "_" s'
  | copyOut ?st ?s ?pstmt ?paramsprf ?args _ => fresh "h_copy_out_" s
  | copyOut ?st ?s ?pstmt ?paramsprf ?args _ => fresh "h_copy_out"

  | copyIn ?st ?s ?fr ?paramsprf ?args (RTE ?er) => fresh "h_copy_in_RE"
  | copyIn ?st ?s ?fr ?paramsprf ?args (OK ?fr') => fresh "h_copy_in_" fr "_" fr'
  | copyIn ?st ?s ?fr ?paramsprf ?args ?fr' => fresh "h_copy_in_" fr "_" fr'
  | copyIn ?st ?s ?fr ?paramsprf ?args _ => fresh "h_copy_in_" fr
  | copyIn ?st ?s ?fr ?paramsprf ?args _ => fresh "h_copy_in"

  | symboltable.fetch_proc ?p _ = None => fresh "h_fetch_proc_None_" p
  | symboltable.fetch_proc _ _ = None => fresh "h_fetch_proc_None"
  | symboltable.fetch_proc ?p _ = Some ?r => fresh "h_fetch_proc_" p "_" r
  | symboltable.fetch_proc ?p _ = ?r => fresh "h_fetch_proc_" p "_" r
  | symboltable.fetch_proc ?p _ = _ => fresh "h_fetch_proc_" p
  | symboltable.fetch_proc _ _ = _ => fresh "h_fetch_proc"
  end.


Ltac rename_hyp1 h th :=
  match th with
  | _ => rename_hyp_sem h th
  | _ => STACK.rename_hyp1 h th
  | _ => LibHypsNaming.rename_hyp_neg h th
  end.

Ltac rename_hyp ::= rename_hyp1.

Lemma storeUpdate_id_ok_others: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (Identifier ast_num id) v (OK stk') ->
    forall id', id<>id' -> fetchG id' stk = fetchG id' stk'.
Proof.
  !intros.
  !invclear h_storeUpd.
  eapply STACK.updateG_ok_others;eauto.
Qed.

Lemma storeUpdate_id_ok_same: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (Identifier ast_num id) v (OK stk') ->
    fetchG id stk' = Some v.
Proof.
  !intros.
  !invclear h_storeUpd.
  eapply updateG_ok_same;eauto.
Qed.

Lemma storeUpdate_id_ok_same_eval_name: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (Identifier ast_num id) v (OK stk') ->
    forall ast_num' v',
      evalName stbl stk' (Identifier ast_num' id) (OK v') ->
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
    storeUpdate stbl stk (Identifier ast_num id) v (OK stk') ->
    forall ast_num' ast_num'' id' v' v'',
      id<>id' ->
      evalName stbl stk (Identifier ast_num' id') (OK v') ->
      evalName stbl stk' (Identifier ast_num'' id') (OK v'') ->
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
  store -> Values.block -> Integers.Int.int -> Memory.Mem.mem -> Prop :=
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
Inductive eq_env: state -> Values.block -> Memory.Mem.mem -> Prop :=
  ME1: forall spb m, eq_env nil spb m
| ME2: forall s sto (lvl:scope_level) fr spb spb' m,
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



(** ** OKized names

OKized names are like names, except that any expression in it has
been evaluated into a cell number. *)
Inductive Nname: Type :=
  NIdentifier : idnum -> Nname
| NE_Indexed_Component : Nname -> Z -> Nname
| NE_Selected_Component : Nname -> idnum -> Nname. (* what if (f(x,y,z).foo?? *)




Inductive solve_name (stbl:symboltable) (stck:state): name -> Nname -> Prop :=
  Solve_Identifier: forall _x id,
    solve_name stbl stck (Identifier _x id) (NIdentifier id)
| Solve_E_Indexed_Component : forall _x (id:name) e nid n,
    evalExp stbl stck e (OK (Int n)) ->
    solve_name stbl stck id nid->
    solve_name stbl stck (E_Indexed_Component _x id e) (NE_Indexed_Component nid n)
| Solve_E_Selected_Component : forall _x id nme nnme,
    solve_name stbl stck nme nnme ->
    solve_name stbl stck (E_Selected_Component _x nme id) (NE_Selected_Component nnme id).

Lemma foramm: forall stbl stck e v,
    evalExp stbl stck e (OK v) ->
    evalExp
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
  storeUpdate stbl stk (Identifier astnum idarr) (ArrayV varr') (OK stk') ->
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
  storeUpdate stbl stk (Identifier astnum idarr) (ArrayV varr') (OK stk') ->
  fetchG idarr stk' = Some (ArrayV varr').

  
  
  storeUpdate stbl stk (E_Indexed_Component ast_num nmearr i) (ArrayV varr) (OK stk') ->
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
    storeUpdate stbl s nme v (OK s') ->
    evalName stbl s' nme (OK x).
Proof.
*)
