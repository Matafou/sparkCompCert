Require Import LibHypsNaming spark2Cminor more_stdlib.
Import ZArith Memory Cminor Integers Errors.
Open Scope Z_scope.

(* no permission mean free. *)
Definition is_free_block := fun m sp_id ofs_id => forall perm, ~ Mem.perm m sp_id ofs_id Cur perm.

Ltac rename_hyp1 h th :=
  match th with
    | ?min <= ?x and ?x < ?max => fresh "h_" x "_bounded_" min "_" max 
    | ?min <= ?x and ?x < ?max => fresh "h_" x "_bounded_"
    | ?min <= ?x and ?x < ?max => fresh "h_bounded"
    | Ctypes.access_mode ?x = _ => fresh "h_access_mode_" x
    | Values.Vptr ?b ?v = _ => fresh "heq_vptr_" b "_" v
    | Values.Vptr ?b = _ => fresh "heq_vptr_" b
    | Values.Vptr _ _ = _ => fresh "heq_vptr"
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

    | Mem.valid_block ?m ?sp => fresh "h_valid_blck_" m "_" sp
    | Mem.valid_block ?m ?sp => fresh "h_valid_blck_" m
    | Mem.valid_block ?m ?sp => fresh "h_valid_blck_" sp
    | Mem.valid_block _ _ => fresh "h_valid_blck"

    | Mem.alloc ?m ?ofs ?sz = (?m', ?sp) => fresh "h_malloc_" m "_" m'
    | Mem.alloc ?m ?ofs ?sz = ?res       => fresh "h_malloc_" m "_" res
    | Mem.alloc ?m ?ofs ?sz = _ => fresh "h_malloc_" m
    | Mem.alloc _ _ _ = _ => fresh "h_malloc"

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

    | Maps.PTree.get ?k ?m = Some ?v => fresh "heq_mget_" k "_" m "_" v
    | Maps.PTree.get ?k _ = Some ?v => fresh "heq_mget_" k "_" v
    | Maps.PTree.get ?k _ = Some _ => fresh "heq_mget_" k
    | Maps.PTree.get _ _ = Some _ => fresh "heq_mget"

    | is_free_block ?m ?sp ?ofs => fresh "h_free_blck_" m "_" sp "_" ofs
    | is_free_block ?m ?sp ?ofs => fresh "h_free_blck_" sp "_" ofs
    | is_free_block ?m ?sp ?ofs => fresh "h_free_blck_" m
    | is_free_block ?m ?sp ?ofs => fresh "h_free_blck"
  end.

Ltac rename_hyp2 h th :=
  match th with
    | _ => rename_hyp1 h th
    | _ => (more_stdlib.rename_hyp1 h th)
    | _ => (spark2Cminor.rename_hyp1 h th)
    | _ => (LibHypsNaming.rename_hyp_neg h th)
  end.

Ltac rename_hyp ::= rename_hyp2.

(* Sometme inversion unfolds to much things under OK (like Int.repr for instance).
   Then this lemma is useful. *)
Lemma OK_inv: forall A (x y:A), OK x = OK y -> x = y.
Proof.
  intros A x y H.
  inversion H.
  reflexivity.
Qed.


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



Lemma map_get_set_same_nodup :
  forall l m k v,
    (forall i, List.In i l -> i <> k) ->
    Maps.PTree.get k (set_locals l (Maps.PTree.set k v m)) = Some v.
Proof.
  !!induction l;cbn;!intros.
  - apply Maps.PTree.gss.
  - rename H into h_diff.
    rewrite Maps.PTree.gso.
    + eapply IHl.
      !intros.
      apply h_diff.
      right;assumption.
    + apply not_eq_sym.
      eapply h_diff.
      left.
      reflexivity.
Qed.


Lemma map_get_set_locals_diff: forall decl x env,
    ~List.In x decl ->
    Maps.PTree.get x (set_locals decl env) =
    Maps.PTree.get x env.
Proof.
  !intro.
  !!induction decl;!intros;cbn.
  - reflexivity.
  - rewrite Maps.PTree.gso.
    + eapply IHdecl.
      intro abs.
      apply neg_h_in_x.
      constructor 2.
      assumption.
    + intro abs.
      apply neg_h_in_x.
      subst.
      constructor 1.
      reflexivity.
Qed.
