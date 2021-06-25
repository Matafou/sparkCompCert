Require Import LibHyps.LibHyps sparkfrontend.LibTac.
Require Import Errors FunInd.
Require Import eval.
From sparkfrontend Require more_stdlib function_utils spark2Cminor  spark_utils.
Import more_stdlib function_utils spark2Cminor.
Require Import Morphisms Relations.
Import STACK.
Require Import store_util.
(* Import STACK.ST. *)


(* Functional Scheme update_ind := Induction for update Sort Prop. *)
(* Functional Scheme updates_ind := Induction for updates Sort Prop. *)
(* Functional Scheme fetch_ind := Induction for fetch Sort Prop. *)

Local Open Scope autonaming_scope.
Ltac rename_hyp_sem n th :=
  match th with
  | Identifier _ ?id => name(id#(S n))
  | Name _ ?id => name(`_Name` ++ id#(S n))
  | Literal _ ?x => name(`_Literal` ++ x#(S n))
  | BinOp _ ?o ?e1 ?e2 => name(o#n ++ e1#n ++ e2#(S n))
  | UnOp _ ?o ?e => name(o#n ++ e#(S n))
  | OK ?x => name(x#(S n))
  | RTE ?msg => name(`_RE`)
  | fetch_var_type _ _ = _ => name (`_eq_fetch_var_type`)
  | spark2Cminor.compute_chnk _ ?name = ?chk => name (`_eq_compute_chnk` ++ name#n ++ chk#n)
  | symboltable.fetch_exp_type _ _ = _ => name (`_eq_fetch_exp_type`)
  | fetch_exp_type _ _ = _ => name (`_eq_fetch_exp_type`)
  | evalExp _ _ _ (RTE _) => name (`_eval_expr_RE`)
  | evalExp _ _ ?e ?v => name (`_eval_expr` ++ e#n ++ v#n)
  | evalName _ _ ?e ?v => name (`_eval_name` ++ e#n ++ v#n)
  | overflowCheck _ ?x => name (`_overf_check` ++ x#n)
  | rangeCheck _ _ _ (RTE _) => name (`_do_range_check_RE`)
  | rangeCheck _ _ _ _ => name (`_do_range_check`)
  | do_run_time_check_on_binop _ _ _ (RTE _) => name (`_do_rtc_binop_RTE`)
  | do_run_time_check_on_binop _ _ _ _ => name (`_do_rtc_binop`)
  | evalLiteral _ (RTE _)  => name (`_eval_literal_RE`)
  | evalLiteral _ _  => name (`_eval_literal`)
  | evalStmt _ _ _ (RTE _) => name (`_eval_stmt_RE`)
  | evalStmt _ _ _ _ => name (`_eval_stmt`)
  | evalDecl _ _ _ _ (RTE _) => name (`_eval_decl_RE`)
  | evalDecl _ _ _ _ _ => name (`_eval_decl`)
  | storeUpdate _ _ _ _ (RTE _) => name (`_storeUpd_RE`)
  | storeUpdate _ _ _ _ _ => name (`_storeUpd`)
  | do_run_time_check_on_binop _ _ _ (RTE _) =>  name (`_do_rtc_binop_RE`)
  | do_run_time_check_on_binop _ _ _ _ =>  name (`_do_rtc_binop`)
  | do_run_time_check_on_unop _ _ (RTE _) =>  name (`_do_rtc_unop_RE`)
  | do_run_time_check_on_unop _ _ _ =>  name (`_do_rtc_unop`)
  | divCheck _ _ _ (RTE _) => name (`_do_division_check_RTE`)
  | divCheck _ _ _ _ => name (`_do_division_check`)
  | extract_subtype_range _ ?t ?rge => name (`_subtype_rge` ++ t#n ++ rge#n)
  | copyOut ?st ?s ?pstmt ?paramsprf ?args ?s' => name (`_copy_out` ++ s#n ++ s'#n)
  | copyIn ?st ?s ?fr ?paramsprf ?args ?fr' => name (`_copy_in` ++ fr#n ++ fr'#n)
  | symboltable.fetch_proc ?p _ = None => name (`_eq_fetch_proc_None` ++ p#n)
  | symboltable.fetch_proc ?p _ = ?r => name (`_eq_fetch_proc` ++ p#n + r#n)
  end.


Ltac rename_hyp1 n th :=
  match th with
  | ?a = ?b => name (`_eq` ++ a#(S n) ++ b#n) (* favoring lhs of equality *)
  | _ => rename_hyp_sem n th
  | _ => spark_utils.rename_hyp_spark n th
  | _ => LibHypsNaming.rename_hyp_neg n th
  | _ => more_stdlib.rename_hyp1 n th
  end.

Local Ltac rename_hyp ::= rename_hyp1.

Lemma storeUpdate_id_ok_others: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (Identifier ast_num id) v (OK stk') ->
    forall id', id<>id' -> fetchG id' stk = fetchG id' stk'.
Proof.
  intros /sng.
  invclear h_storeUpd_ /sng.
  eapply STACK.updateG_ok_others;eauto.
Qed.

Lemma storeUpdate_id_ok_same: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (Identifier ast_num id) v (OK stk') ->
    fetchG id stk' = Some v.
Proof.
  intros /sng.
  invclear h_storeUpd_ /sng.
  eapply updateG_ok_same;eauto.
Qed.


Lemma storeUpdate_id_ok_same_eval_name: forall ast_num stbl stk id v stk',
    storeUpdate stbl stk (Identifier ast_num id) v (OK stk') ->
    forall ast_num' v',
      evalName stbl stk' (Identifier ast_num' id) (OK v') ->
      v = v'.
Proof.
  intros /sng.
  inversion h_eval_name_id_v'_ /sng.
  specialize (storeUpdate_id_ok_same _ _ _ _ _ _ h_storeUpd_).
  intro /sng.
  rewrite h_eq_SfetchG_id_stk'_v_ in h_eq_SfetchG_id_stk'_v'_.
  inversion h_eq_SfetchG_id_stk'_v'_.
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
  intros /sng.
  inversion h_eval_name_id'_v'_ /sng.
  inversion h_eval_name_id'_v''_ /sng.
  specialize (storeUpdate_id_ok_others _ _ _ _ _ _ h_storeUpd_).
  intro /sng.
  specialize (h_all_eq_SfetchG_ id' h_neq_id_id'_).
  rewrite h_eq_SfetchG_id'_stk_v'_ in h_all_eq_SfetchG_.
  rewrite h_eq_SfetchG_id'_stk'_v''_ in h_all_eq_SfetchG_.
  inversion h_all_eq_SfetchG_.
  reflexivity.
Qed.



Lemma updateIndexedComp_id_ok_others: forall arr k v arr',
    arr' = updateIndexedComp arr k v
    -> forall k', k<>k' -> array_select arr' k' = array_select arr k'.
Proof.
  intros until v.
  functional induction (updateIndexedComp arr k v);intros;subst;simpl in * /sng.
  - apply Zeq_bool_eq in h_eq_Zeqb_i0_i_true_;subst;simpl.
    apply Zeq_is_neq_bool in h_neq_i_k'_.
    rewrite h_neq_i_k'_.
    reflexivity.
  - specialize (h_all_eq_array_select_ (updateIndexedComp a1 i v) eq_refl _ h_neq_i_k'_).
    rewrite h_all_eq_array_select_.
    reflexivity.
  - apply Zeq_is_neq_bool in h_neq_i_k'_.
    rewrite h_neq_i_k'_.
    reflexivity.
Qed.

Lemma updateIndexedComp_id_ok_same: forall arr k v arr',
    arr' = updateIndexedComp arr k v
    -> array_select arr' k = Some v.
Proof.
  intros until v.
  functional induction (updateIndexedComp arr k v);intros;subst;simpl in * /sng.
  - rewrite h_eq_Zeqb_i0_i_true_.
    reflexivity.
  - rewrite h_eq_Zeqb_i0_i_false_.
    apply h_all_eq_array_select_;auto.
  - replace (Zeq_bool i i) with true;auto.
    symmetry.
    apply Zeq_is_eq_bool.
    reflexivity.
Qed.



Lemma arrayUpdate_id_ok_others: forall arr k v arr',
    arrayUpdate (ArrayV arr) k v = Some (ArrayV arr')
    -> forall k', k<>k' -> array_select arr' k' = array_select arr k'.
Proof.
  intros arr k v arr' heq_arrayUpdate_ k'.
  simpl in *.
  invclear heq_arrayUpdate_ /sng.
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

(** [match_env_ sta b m] means that the chained Cminor stack at address
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
  intros /sng.
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
  intros /sng.
  invclear h_storeUpd_ /sng.
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
