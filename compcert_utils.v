Require Import LibHypsNaming spark2Cminor.
Import ZArith Memory Cminor Integers.
Open Scope Z_scope.

Ltac rename_hyp1 h th :=
  match th with
    | ?min <= ?x and ?x < ?max => fresh "h_" x "_bounded_" min "_" max 
    | ?min <= ?x and ?x < ?max => fresh "h_" x "_bounded_"
    | ?min <= ?x and ?x < ?max => fresh "h_bounded"
    | Ctypes.access_mode ?x = _ => fresh "h_access_mode_" x
    | Mem.valid_access ?m ?chk ?b ?ofs ?perm => fresh "h_valid_access_" b
    | Mem.valid_access ?m ?chk ?b ?ofs ?perm => fresh "h_valid_access"
    | Ctypes.access_mode _ = _ => fresh "h_access_mode"
    | Cminor.exec_stmt _ _ _ _ _ ?stmt _ _ _ None  => fresh "h_exec_stmt_None_" stmt 
    | Cminor.exec_stmt _ _ _ _ _ ?stmt _ _ _ None  => fresh "h_exec_stmt_None"
    | Cminor.exec_stmt _ _ _ _ _ ?stmt _ _ _ (Some ?res)  => fresh "h_exec_stmt_" stmt "_" res
    | Cminor.exec_stmt _ _ _ _ _ ?stmt _ _ _ ?res => fresh "h_exec_stmt_" stmt "_" res
    | Cminor.exec_stmt _ _ _ _ _ ?stmt _ _ _ _ => fresh "h_exec_stmt_" stmt
    | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ _  => fresh "h_exec_stmt"
    | Cminor.eval_constant _ _ _ = (Some _)  => fresh "h_eval_constant"
    | Cminor.eval_constant _ _ _ = None  => fresh "h_eval_constant_None"
    | Cminor.eval_expr _ _ _ _ ?x ?y => fresh "h_CM_eval_expr_" x "_" y
    | Cminor.eval_expr _ _ _ _ ?x _ => fresh "h_CM_eval_expr_" x
    | Cminor.eval_expr _ _ _ _ _ ?y => fresh "h_CM_eval_expr_" y
    | Cminor.eval_expr _ _ _ _ _ _ => fresh "h_CM_eval_expr"

    | Cminor.eval_funcall ?g ?m ?proc_value ?vargs ?t ?m' ?vres => fresh "h_evalfuncall_" proc_value "_" vargs "_" vres
    | Cminor.eval_funcall ?g ?m ?proc_value ?vargs ?t ?m' ?vres => fresh "h_evalfuncall_" proc_value "_" vargs
    | Cminor.eval_funcall ?g ?m ?proc_value ?vargs ?t ?m' ?vres => fresh "h_evalfuncall_" proc_value
    | Cminor.eval_funcall ?g ?m ?proc_value ?vargs ?t ?m' ?vres => fresh "h_evalfuncall"

    | Cminor.eval_exprlist _ _ _ _ ?x ?y => fresh "h_CM_eval_exprl_" x "_" y
    | Cminor.eval_exprlist _ _ _ _ ?x _ => fresh "h_CM_eval_exprl_" x
    | Cminor.eval_exprlist _ _ _ _ _ ?y => fresh "h_CM_eval_exprl_" y
    | Cminor.eval_exprlist _ _ _ _ _ _ => fresh "h_CM_eval_exprl"

    | Mem.store ?chk ?m ?blk ?n ?v = None => fresh "heq_store_" v "_none"
    | Mem.store ?chk ?m ?blk ?n ?v = Some ?m2 => fresh "heq_store_" v "_" m2
    | Mem.store ?chk ?m ?blk ?n ?v = ?m2 => fresh "heq_store_" v "_" m2
    | Mem.store ?chk ?m ?blk ?n ?v = ?m2 => fresh "heq_store_" v
    | Mem.store ?chk ?m ?blk ?n ?v = ?m2 => fresh "heq_store"
    | Mem.storev ?chk ?m ?vaddr ?v = None => fresh "heq_storev_" v "_none"
    | Mem.storev ?chk ?m ?vaddr ?v = Some ?m2 => fresh "heq_storev_" v "_" m2
    | Mem.storev ?chk ?m ?vaddr ?v = ?m2 => fresh "heq_storev_" v "_" m2
    | Mem.storev ?chk ?m ?vaddr ?v = ?m2 => fresh "heq_storev_" v
    | Mem.storev ?chk ?m ?vaddr ?v = ?m2 => fresh "heq_storev"

    | Mem.unchanged_on ?prd ?m ?m' => fresh "h_unchanged_on_" prd "_" m "_" m'
    | Mem.unchanged_on ?prd ?m ?m' => fresh "h_unchanged_on_" m "_" m'
    | Mem.unchanged_on ?prd ?m ?m' => fresh "h_unchanged_on_" prd
    | Mem.unchanged_on ?prd ?m ?m' => fresh "h_unchanged_on"


    | outcome_result_value ?out ?typ ?res => fresh "h_outc_resval_" out "_" res
    | outcome_result_value ?out ?typ ?res => fresh "h_outc_resval_" out
    | outcome_result_value ?out ?typ ?res => fresh "h_outc_resval_" res
    | outcome_result_value ?out ?typ ?res => fresh "h_outc_resval"

    | outcome_free_mem ?out ?m1 ?sp ?size ?m2 => fresh "h_outc_freemem_" out "_" m1 "_" m2
    | outcome_free_mem ?out ?m1 ?sp ?size ?m2 => fresh "h_outc_freemem_" m1 "_" m2
    | outcome_free_mem ?out ?m1 ?sp ?size ?m2 => fresh "h_outc_freemem_" m1
    | outcome_free_mem ?out ?m1 ?sp ?size ?m2 => fresh "h_outc_freemem_" m2
    | outcome_free_mem ?out ?m1 ?sp ?size ?m2 => fresh "h_outc_freemem"

    | eval_binop ?op ?v1 ?v2 ?m = Some ?res => fresh "h_eval_binop_" op "_" v1 "_" v2
    | eval_binop ?op ?v1 ?v2 ?m = Some ?res => fresh "h_eval_binop_" op "_" v1
    | eval_binop ?op ?v1 ?v2 ?m = Some ?res => fresh "h_eval_binop_" op "_" v2
    | eval_binop ?op ?v1 ?v2 ?m = Some ?res => fresh "h_eval_binop_" op
    | eval_binop ?op ?v1 ?v2 ?m = Some ?res => fresh "h_eval_binop"
    | eval_binop ?op ?v1 ?v2 ?m = None => fresh "h_eval_binop_None_" op "_" v1 "_" v2
    | eval_binop ?op ?v1 ?v2 ?m = None => fresh "h_eval_binop_None_" op "_" v1
    | eval_binop ?op ?v1 ?v2 ?m = None => fresh "h_eval_binop_None_" op "_" v2
    | eval_binop ?op ?v1 ?v2 ?m = None => fresh "h_eval_binop_None_" op
    | eval_binop ?op ?v1 ?v2 ?m = None => fresh "h_eval_binop_None"


    | Values.Val.add ?v1 ?v2 = ?res => fresh "h_val_add_" v1 "_" v2 "_" res
    | Values.Val.add ?v1 ?v2 = ?res => fresh "h_val_add_" v1 "_" v2
    | Values.Val.add ?v1 ?v2 = ?res => fresh "h_val_add_" v1
    | Values.Val.add ?v1 ?v2 = ?res => fresh "h_val_add_" v2
    | Values.Val.add ?v1 ?v2 = ?res => fresh "h_val_add"

    | Mem.loadv ?chk ?m ?vaddr = Some ?res => fresh "h_loadv_" vaddr "_" res
    | Mem.loadv ?chk ?m ?vaddr = Some ?res => fresh "h_loadv_" res
    | Mem.loadv ?chk ?m ?vaddr = Some ?res => fresh "h_loadv"
    | Mem.loadv ?chk ?m ?vaddr = None => fresh "h_loadv_None_" vaddr
    | Mem.loadv ?chk ?m ?vaddr = None => fresh "h_loadv_None"


    | Globalenvs.Genv.find_funct ?g ?paddr = Some ?res => fresh "heq_find_func_" paddr "_" res
    | Globalenvs.Genv.find_funct ?g ?paddr = Some _ => fresh "heq_find_func_" paddr
    | Globalenvs.Genv.find_funct ?g _ = Some _ => fresh "heq_find_func"
    | Globalenvs.Genv.find_funct ?g ?paddr = None => fresh "heq_find_func_" paddr "_NONE"
    | Globalenvs.Genv.find_funct ?g ?paddr = None => fresh "heq_find_func_None"
  end.


(* Auxiliary lemmas, should go in Compcert? *)
Lemma repr_inj:
  forall v1 v2,
    Integers.Int.min_signed <= v1 <= Integers.Int.max_signed ->
    Integers.Int.min_signed <= v2 <= Integers.Int.max_signed ->
    Integers.Int.repr v1 = Integers.Int.repr v2 ->
    v1 = v2.
Proof.
  intros v1 v2 hinbound1 hinboun2 heq_repr.
  assert (h: Integers.Int.signed(Integers.Int.repr v1)
             = Integers.Int.signed(Integers.Int.repr v2)).
  { rewrite heq_repr. reflexivity. }
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


(* no permission mean free. *)
Definition is_free_block := fun m sp_id ofs_id => forall perm, ~ Mem.perm m sp_id ofs_id Cur perm.
(* never allocated blocks are invalid, thus free. *)

Lemma fresh_block_alloc_perm:
  forall (m1 : mem) (lo hi : Z) (m2 : mem) (b : Values.block),
    Mem.alloc m1 lo hi = (m2, b) ->
    forall (ofs : Z) (k : perm_kind) p,
      ~ Mem.perm m1 b ofs k p. (* is_free m1 b.*)
Proof.  
  !intros.
  intro abs.
  eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.perm_valid_block;eauto.
Qed.


Lemma mem_unchanged_on_mon : forall P m m',
    Mem.unchanged_on P m m' ->
    forall Q: Values.block -> Z -> Prop,
      (forall x y, Q x y -> P x y) ->
      Mem.unchanged_on Q m m'.
Proof.
  intros P m m' H Q H0. 
  !destruct H.
  split;!intros.
  - split;!intros.
    + apply unchanged_on_perm;auto.
    + apply unchanged_on_perm;auto.
  - apply unchanged_on_contents;auto.
Qed.
