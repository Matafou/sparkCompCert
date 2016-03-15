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
    | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ None  => fresh "h_exec_stmt_None"
    | Cminor.exec_stmt _ _ _ _ _ _ _ _ _ _  => fresh "h_exec_stmt"
    | Cminor.eval_constant _ _ _ = (Some _)  => fresh "h_eval_constant"
    | Cminor.eval_constant _ _ _ = None  => fresh "h_eval_constant_None"
    | Cminor.eval_expr _ _ _ _ ?x ?y => fresh "h_CM_eval_expr_" x "_" y
    | Cminor.eval_expr _ _ _ _ ?x _ => fresh "h_CM_eval_expr_" x
    | Cminor.eval_expr _ _ _ _ _ ?y => fresh "h_CM_eval_expr_" y
    | Cminor.eval_expr _ _ _ _ _ _ => fresh "h_CM_eval_expr"

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
