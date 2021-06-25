Require Import SetoidList ZArith Lia.
Require Import Flocq.Core.Zaux.
Require Import  LibHyps.LibHyps.
From compcert Require Import common.Errors backend.Cminor lib.Integers.

From sparkfrontend Require Import compcert_utils more_stdlib LibTac.
Import compcert.common.Memory.
Require compcert.cfrontend.Ctypes.

(*Require Import (*sparkfrontend.LibTac*) sparkfrontend.LibHypsNaming  compcert.common.Errors
        compcert.common.Cminor compcert.lib.Integers sparkfrontend.compcert_utils sparkfrontend.more_stdlib.*)

Open Scope nat_scope.
(** The Chaining structure of the stacks.

In this section we describe the way the first element of each local
stack points to another local stack up to a given depth. This give a
stack of stacks that is isomrphic to Spark's stack of stacks. *)

(* We need this structural invariant at least to prove that execution
   never modifies the chaining pointers. *) 
Inductive chained_stack_structure m : nat -> Values.val -> Prop :=
| chained_0: forall b, chained_stack_structure m 0 (Values.Vptr b Ptrofs.zero) (* Should b null? *)
| chained_S: forall n b' b,
    chained_stack_structure m n (Values.Vptr b' Ptrofs.zero) ->
    Mem.loadv AST.Mint32 m (Values.Vptr b Ptrofs.zero) = Some (Values.Vptr b' Ptrofs.zero) ->
    chained_stack_structure m (S n) (Values.Vptr b Ptrofs.zero).


Inductive repeat_Mem_loadv (chk:AST.memory_chunk) (m : mem): forall (lvl:nat) (sp sp' : Values.val), Prop :=
| Repeat_loadv1: forall sp, repeat_Mem_loadv chk m O sp sp
| Repeat_loadv2: forall lvl sp sp' sp'',
    repeat_Mem_loadv chk m lvl sp' sp'' ->
    Mem.loadv AST.Mint32 m sp = Some sp' ->
    repeat_Mem_loadv chk m (S lvl) sp sp''.


(* CE gives the maximum number of loads. *)
Definition stack_localstack_aligned lvl locenv g m sp :=
  forall δ_lvl,
    (δ_lvl <= lvl)%nat ->
    exists b_δ,
      Cminor.eval_expr g sp locenv m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) δ_lvl) (Values.Vptr b_δ Ptrofs.zero).

Local Open Scope autonaming_scope.
Ltac rename_chained n th :=
  match th with
| chained_stack_structure ?m ?lvl ?sp => name(`_chain` ++ m#n ++ lvl#n ++ sp#n)
| repeat_Mem_loadv _ ?m ?lvl ?v ?sp => name( `_repeat_loadv` ++ lvl#n ++ v#n)
| stack_localstack_aligned _ _ ?g ?m ?sp => name(`_aligned` ++ g#n ++ m#n)
end.

Local Close Scope autonaming_scope.
(*
Ltac prefixable h th ::=
  match th with
  | _ => prefixable_compcert h th
  | _ => prefixable_eq_neq h th
  end.
*)

Ltac rename_hyp n th ::=
  match th with
  | _ => (compcert_utils.rename_hyp1 n th)
  | _ => (rename_chained n th)
  end.
Ltac rename_depth ::= constr:(2%nat).

Lemma chained_stack_structure_le m sp : forall n,
    chained_stack_structure m n sp ->
    forall n', (n' <= n)%nat -> 
               chained_stack_structure m n' sp.
Proof.
  intros ? ? /sng.
  induction h_chain_m_n_sp_;intros /sng.
  - assert (n'=0)%nat by lia;subst.
    constructor.
  - destruct n'.
    * constructor.
    * econstructor;eauto.
      apply h_all_chain_;eauto;lia.
Qed.

Lemma chained_stack_struct_inv_sp_zero: forall m n sp,
    chained_stack_structure m n sp -> exists b',  sp = (Values.Vptr b' Ptrofs.zero).
Proof.
  intros /sng.
  inversion h_chain_m_n_sp_;subst;eauto.
Qed.

Lemma chained_stack_struct_sp_add: forall m n sp,
    chained_stack_structure m n sp -> (Values.Val.add sp (Values.Vint Int.zero)) = sp.
Proof.
  intros /sng.
  destruct (chained_stack_struct_inv_sp_zero m n sp);subst;auto.
Qed.

Lemma cm_eval_addrstack_zero:
  forall b ofs m g e,
      Cminor.eval_expr g (Values.Vptr b ofs) e m (Econst (Oaddrstack Ptrofs.zero)) (Values.Vptr b ofs).
Proof.
  intros /sng.
  constructor;cbn.
  rewrite Ptrofs.add_zero.
  reflexivity.
Qed.

Lemma cm_eval_addrstack_zero_chain:
  forall n sp m,
    chained_stack_structure m n sp ->
    forall g e,
      Cminor.eval_expr g sp e m (Econst (Oaddrstack Ptrofs.zero)) sp.
Proof.
  intros /sng.
  destruct (chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_n_sp_).
  subst.
  apply cm_eval_addrstack_zero.
Qed.

(* a useful formulation of the two previous lemmas. *)
Lemma det_cm_eval_addrstack_zero_chain : forall m lvl sp e g vaddr,
    chained_stack_structure m lvl sp ->
    Cminor.eval_expr g sp e m (Econst (Oaddrstack Ptrofs.zero)) vaddr ->
    vaddr = sp.
Proof.
  intros /sng.
  pose proof cm_eval_addrstack_zero_chain lvl sp m h_chain_m_lvl_sp_ g e.
  eapply det_eval_expr;eauto.
Qed.

Lemma det_cm_eval_addrstack_zero : forall b i m e g vaddr,
    Cminor.eval_expr g (Values.Vptr b i) e m (Econst (Oaddrstack Ptrofs.zero)) vaddr ->
    vaddr = (Values.Vptr b i).
Proof.
  intros /sng.
  pose proof cm_eval_addrstack_zero b i m g e.
  eapply det_eval_expr;eauto.
Qed.

Ltac subst_det_addrstack_zero :=

  match goal with
  | H:Cminor.eval_expr ?g ?sp ?e ?m ?exp ?vaddr,
      H':Cminor.eval_expr ?g ?sp ?e ?m ?exp ?vaddr' |- _ =>
    assert (vaddr=vaddr') by (eapply det_eval_expr;eauto);
    try (subst vaddr + subst vaddr');
    clear H
    (* to avoid useless applications *)
  | H:Cminor.eval_expr ?g ?sp ?e ?m ?exp ?sp |- _ =>
    fail 1
  | H:Cminor.eval_expr ?g (Values.Vptr ?b ?i) ?e ?m (Econst (Oaddrstack Ptrofs.zero)) ?vaddr |- _ =>
    assert (vaddr=(Values.Vptr b i)) by (eapply det_cm_eval_addrstack_zero;eauto);
    try subst vaddr
  | H:Cminor.eval_expr ?g ?sp ?e ?m (Econst (Oaddrstack Ptrofs.zero)) ?vaddr,
      H':chained_stack_structure ?m ?n ?sp |- _ =>
    assert (vaddr=sp) by (eapply det_cm_eval_addrstack_zero_chain;eauto);
    try subst vaddr

  end.

Lemma chained_stack_structure_aux m sp : forall n,
    chained_stack_structure m (S n) sp ->
    forall g e, exists b',
      chained_stack_structure m n (Values.Vptr b' Ptrofs.zero)
      /\ Mem.loadv AST.Mint32 m sp = Some (Values.Vptr b' Ptrofs.zero)
      /\ Cminor.eval_expr g sp e m (Eload AST.Mint32 (Econst (Oaddrstack Ptrofs.zero))) (Values.Vptr b' Ptrofs.zero).
Proof.
  intros until 1 /sng.
  inversion h_chain_m_S_sp_;subst;intros /sng.
  exists b';split;[|split];eauto.
  econstructor;eauto.
  constructor.
  cbn.
  reflexivity.
Qed.

Ltac rename_depth ::= constr:(2%nat).

Lemma build_loads__decomp_S: forall m b0 g e b, 
    Cminor.eval_expr g (Values.Vptr b0 Ptrofs.zero) e m 
                     (Eload AST.Mint32 (Econst (Oaddrstack Ptrofs.zero)))
                     (Values.Vptr b Ptrofs.zero) ->
    forall n v,
      Cminor.eval_expr g (Values.Vptr b0 Ptrofs.zero) e m
                       (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n)) v ->
      exists sp',
        Cminor.eval_expr g (Values.Vptr b0 Ptrofs.zero) e m
                         (Eload AST.Mint32 (Econst (Oaddrstack Ptrofs.zero))) sp'
        /\ Cminor.eval_expr g sp' e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v.
Proof.
  intros /sng.
  revert v b h_CM_eval_expr_Eload_vptr_ h_CM_eval_expr_bldlds_v_.
  induction n /sng.
  - intros /sng.
    cbn in *.
    exists v;split;auto.
    constructor;cbn.
    subst_det_addrstack_zero.
    cbn.
    rewrite Ptrofs.add_zero.
    reflexivity.
  - intros /sng.
    cbn in h_CM_eval_expr_bldlds_v_.
    invclear h_CM_eval_expr_bldlds_v_;subst /sng.
    change (Eload AST.Mint32 (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) with (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n)) in h_CM_eval_expr_Eload_vaddr_.
    specialize (h_all_and_ _ _ h_CM_eval_expr_Eload_vptr_ h_CM_eval_expr_Eload_vaddr_).
    decomp h_all_and_.
    exists sp';split;auto.
    cbn.
    econstructor;eauto.
Qed.

Lemma chained_stack_structure_decomp_S: forall m max sp g e, 
    forall n v, chained_stack_structure m max sp ->
      n < max ->
      Cminor.eval_expr g sp e m
                       (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n))
                       v ->
         exists sp',
           Cminor.eval_expr g sp e m (Eload AST.Mint32 (Econst (Oaddrstack Ptrofs.zero))) sp' /\
           Cminor.eval_expr g sp' e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v.
Proof.
  intros until n /sng.
  induction n /sng.
  - intros /sng.
    cbn in *.
    exists v;split;auto.
    eapply cm_eval_addrstack_zero_chain with (n:=Nat.pred max);eauto.
    rewrite <- (PeanoNat.Nat.succ_pred_pos _ h_lt_0_max_) in h_chain_m_max_sp_.
    inversion h_chain_m_max_sp_ /sng.
    inversion h_CM_eval_expr_bldlds_v_ /sng.
    subst_det_addrstack_zero.
    rewrite h_eq_loadv_vptr_ in h_eq_loadv_v_.
    inversion h_eq_loadv_v_.
    assumption.
  - intros /sng.
    cbn in h_CM_eval_expr_bldlds_v_.
    invclear h_CM_eval_expr_bldlds_v_;subst /sng.
    change (Eload AST.Mint32 (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) with (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n)) in h_CM_eval_expr_Eload_vaddr_.
    assert (n<max) by lia /sng.
    specialize h_all_and_ with (1:=h_chain_m_max_sp_)(2:=h_lt_n_max_)(3:=h_CM_eval_expr_Eload_vaddr_).
    decomp h_all_and_.
    exists sp';split;auto.
    cbn.
    econstructor;eauto.
Qed.



Lemma chained_stack_structure_spec :
  forall  g e m n b,
    (forall lvl,
        (lvl <= n)%nat
        -> exists b',
          Cminor.eval_expr g (Values.Vptr b Ptrofs.zero) e m
                           (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) lvl)
                           (Values.Vptr b' Ptrofs.zero))
    -> chained_stack_structure m n (Values.Vptr b Ptrofs.zero).
Proof.
  induction n;intros /sng.
  - constructor.
  - assert (1 <= S n) by lia /sng.
    (pose proof  (h_all_CM_eval_expr_ 1%nat h_le_1_S_)) /sng.
    decomp h_ex_CM_eval_expr_ .
    assert (S n <= S n) by lia /sng.
    (pose proof  (h_all_CM_eval_expr_ _ h_le_S_S_)) /sng.
    decomp h_ex_CM_eval_expr_.
    cbn in *.
    specialize build_loads__decomp_S with (1:=h_CM_eval_expr_bldlds_vptr_)(2:=h_CM_eval_expr_bldlds_vptr_0) as ? /d/sng.
    subst_det_addrstack_zero.
    eapply chained_S with (b':=b');eauto.
    + eapply h_all_chain_.
      intros /sng.
      assert (S lvl <= S n) by lia /sng.
      (pose proof  (h_all_CM_eval_expr_ _ h_le_S_S_0)) /sng.
      decomp h_ex_CM_eval_expr_ .
      cbn in *.
      specialize build_loads__decomp_S with (1:=h_CM_eval_expr_Eload_sp'_) (2:=h_CM_eval_expr_bldlds_vptr_) as ? /d/sng.
      subst_det_addrstack_zero.
      eauto.
    + inversion h_CM_eval_expr_Eload_sp'_ /sng.
      subst_det_addrstack_zero.
      assumption.
Qed.

Lemma assignment_preserve_chained_stack_structure_aux:
  forall stkptr m chk e_t_v addr_blck addr_ofs m' n,
    chained_stack_structure m n stkptr ->
    (4 <= (Ptrofs.unsigned addr_ofs))%Z ->
    Mem.storev chk m (Values.Vptr addr_blck addr_ofs) e_t_v = Some m' ->
    chained_stack_structure m' n stkptr.
Proof.
  intros /sng.
  induction h_chain_m_n_stkptr_ /sng.
  - constructor.
  - econstructor.
    all:swap 1 2.
    + unfold Mem.loadv.
      unfold Mem.storev in h_eq_storev_m'_.
      erewrite Mem.load_store_other with (m1:=m);eauto.
    + assumption.
Qed.


(*
Lemma add_Vint_zero: forall m vaddr x,
    Mem.loadv AST.Mint32 m vaddr = Some x ->
    Values.Val.add x (Values.Vint Int.zero) = x.
Proof.
  intros /sng. 
  destruct vaddr;cbn in *; try discriminate.
  cbn.
Qed.
 *)

Lemma chained_stack_structure_decomp_S_2': forall n m sp,
    chained_stack_structure m (S n) sp ->
    forall g e v sp',
      Cminor.eval_expr g sp e m (Eload AST.Mint32 (Econst (Oaddrstack Ptrofs.zero))) sp' ->
      Cminor.eval_expr g sp' e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v ->
      Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n)) v.
Proof.
  intro n.
  induction n;intros /sng.
  - cbn in *.
    inversion h_CM_eval_expr_Eload_sp'_ /sng.
    inversion h_CM_eval_expr_Econst_vaddr_ /sng.
    inversion h_CM_eval_expr_bldlds_v_ /sng.
    cbn in *.
    invclear h_eq_evalcst_v_ /sng.
    invclear h_eq_evalcst_vaddr_;subst /sng.
    assert (exists b, sp' = Values.Vptr b Ptrofs.zero).
    { inversion h_chain_m_1_sp_ /sng.
      cbn in *.
      rewrite Ptrofs.add_zero in h_eq_loadv_sp'_.
      rewrite h_eq_loadv_sp'_ in h_eq_loadv_vptr_.
      inversion h_eq_loadv_vptr_.
      eauto. }
    decomp H;subst.
    econstructor;cbn;eauto.
  - cbn in h_CM_eval_expr_bldlds_v_.
    cbn.
    inversion h_CM_eval_expr_bldlds_v_;subst.
    econstructor;eauto.
    eapply h_all_CM_eval_expr_;eauto.
    eapply chained_stack_structure_le;eauto.
Qed.




Lemma chain_structure_spec:
  forall n m sp ,
    chained_stack_structure m n sp ->
    forall g e,
      exists b, Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) (Values.Vptr b Ptrofs.zero).
Proof.
  intros until 1 /sng.
  induction h_chain_m_n_sp_;intros /sng.
  - exists b.
    eapply cm_eval_addrstack_zero;eauto.
  - specialize (h_all_CM_eval_expr_ g e).
    decomp h_all_CM_eval_expr_.
    exists b0.
    eapply chained_stack_structure_decomp_S_2';eauto.
    + econstructor;eauto.
    + econstructor;eauto.
      constructor.
      reflexivity.
Qed.

Lemma chain_repeat_loadv_1 : forall m n sp,
    chained_stack_structure m n sp ->
    forall v g e, repeat_Mem_loadv AST.Mint32 m n sp v ->
                  Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v.
Proof.
  intros until 1 /sng.
  induction h_chain_m_n_sp_;cbn;intros /sng.
  - inversion h_repeat_loadv_0_vptr_ /sng.
    apply cm_eval_addrstack_zero.
  - eapply chained_stack_structure_decomp_S_2'.
    + econstructor;eauto.
    + econstructor;eauto.
      econstructor;eauto.
    + eapply h_all_CM_eval_expr_;eauto.
      inversion h_repeat_loadv_S_vptr_ /sng.
      rewrite h_eq_loadv_vptr_ in h_eq_loadv_sp'_.
      invclear h_eq_loadv_sp'_ /sng.
      assumption.
Qed.

Lemma chained_stack_structure_decomp_S_2: forall n m sp,
    chained_stack_structure m (S n) sp ->
    forall g e v,
      Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n)) v ->
      exists sp',
        Cminor.eval_expr g sp e m (Eload AST.Mint32 (Econst (Oaddrstack Ptrofs.zero))) sp' /\
        Cminor.eval_expr g sp' e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v.
Proof.
  intro n.
  induction n /sng.
  - intros /sng.
    cbn in *.
    exists v;split;auto.
    constructor;cbn.
    (pose proof chained_stack_structure_aux _ _ _ h_chain_m_1_sp_ g e) /sng.
    decomp h_ex_and_.
    subst_det_addrstack_zero.
    cbn.
    rewrite Ptrofs.add_zero.  
    reflexivity.
  - intros /sng.
    cbn in h_CM_eval_expr_bldlds_v_.
    inversion h_CM_eval_expr_bldlds_v_;subst /sng.
    change (Eload AST.Mint32 (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) with (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n)) in h_CM_eval_expr_Eload_vaddr_.
    assert (chained_stack_structure m (S n) sp) /sng.
    { eapply chained_stack_structure_le;eauto. }
    specialize h_all_and_ with (1:=h_chain_m_S_sp_0) (2:=h_CM_eval_expr_Eload_vaddr_).
    decomp h_all_and_.
    exists sp';split;auto.
    cbn.
    econstructor;eauto.
Qed.



(* We can cut a chain into a smaller chain. *)
Lemma chain_structure_cut:
  forall n'' n' m sp ,
    chained_stack_structure m (n'+n'') sp ->
    forall g e,
      exists v sp' : Values.val, 
        Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (n'+n'')%nat) v
        /\ Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n'') sp'
        /\ Cminor.eval_expr g sp' e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n') v
        /\ chained_stack_structure m n' sp'.
Proof.
  intros * ? * /sng.
  (pose proof chain_structure_spec _ _ _ h_chain_m_add_sp_ g e) /sng.
  decomp h_ex_CM_eval_expr_ .
  exists (Values.Vptr b Ptrofs.zero).
  revert dependent h_CM_eval_expr_bldlds_vptr_.
  revert dependent h_chain_m_add_sp_.
  revert n' m sp g e b.
  induction n''; intros /sng.
  - replace (n'+0)%nat with n' in * by lia.
    exists sp;split;[eauto| split;eauto].
    cbn.
    eapply cm_eval_addrstack_zero_chain;eauto.
  - specialize (h_all_and_ (S n') m sp g e b).
    assert (chained_stack_structure m (S n' + n'') sp) /sng.
    { replace (n' + S n'')%nat with (S n' + n'')%nat in h_chain_m_add_sp_; try lia.
      assumption. }
    specialize (h_all_and_ h_chain_m_add_sp_0).
    replace (n' + S n'')%nat with (S n' + n'')%nat in h_CM_eval_expr_bldlds_vptr_; try lia.
    specialize (h_all_and_ h_CM_eval_expr_bldlds_vptr_).
    decomp h_all_and_ .
    specialize chained_stack_structure_decomp_S_2 with (1:=h_chain_m_S_sp'_)(2:=h_CM_eval_expr_bldlds_vptr_1) as ? /d/sng.
    exists sp'0;split;[|split;[|split]];eauto.
    + replace (n' + S n'')%nat with (S n' + n'')%nat; try lia.
      assumption.
    + cbn.
      econstructor.
      * eassumption.
      * inversion h_CM_eval_expr_Eload_sp'0_ /sng.
        repeat subst_det_addrstack_zero.
        assumption.
    + inversion h_CM_eval_expr_Eload_sp'0_ /sng.
      repeat subst_det_addrstack_zero/sng.
      (* clear h_chain_m_ h_chain_m0_. *)
      inversion h_chain_m_S_sp'_ /sng.
      inversion h_chain_m_add_sp_0 /sng.
      cbn in *.
      rewrite h_eq_loadv_sp'0_ in h_eq_loadv_vptr_.
      inversion h_eq_loadv_vptr_ /sng.
      assumption.
Qed.




Lemma chained_stack_structure_decomp_S_3: forall n m sp n_base,
    chained_stack_structure m (S n + n_base) sp ->
    let base := (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n_base) in
    forall g e v,
      Cminor.eval_expr g sp e m (build_loads_ base (S n)) v ->
      exists sp',
        Cminor.eval_expr g sp e m (Eload AST.Mint32 (Econst (Oaddrstack Ptrofs.zero))) sp' /\
        Cminor.eval_expr g sp' e m (build_loads_ base n) v.
Proof.
  intros /sng.
  unfold base in h_CM_eval_expr_bldlds_v_.
  rewrite <- build_loads_compos in h_CM_eval_expr_bldlds_v_.
  cbn [plus] in h_CM_eval_expr_bldlds_v_.
  specialize chained_stack_structure_decomp_S_2 with (1:=h_chain_m_add_sp_) (2:=h_CM_eval_expr_bldlds_v_) as ? /d/sng.
  exists sp';split;eauto.
  unfold base.
  rewrite <- build_loads_compos_comm.
  rewrite Nat.add_comm.
  assumption.
Qed.

Lemma chained_stack_structure_decomp_add: forall n1 n2 m sp,
    chained_stack_structure m (n1 + n2) sp ->
    forall g e v,
      Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (n1 + n2)) v ->
      exists sp',
        Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n2) sp' /\
        Cminor.eval_expr g sp' e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n1) v.
Proof.
  intros until e /sng.
  specialize chain_structure_cut with (1:=h_chain_m_add_sp_)(g:=g)(e:=e) as h /d.
  intros.
  subst_det_addrstack_zero.
  exists sp'.
  split;auto.
Qed.

Lemma chained_stack_structure_decomp_add': forall n1 n2 m sp sp' g e v,
    chained_stack_structure m (n1 + n2) sp ->
    Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n2) sp' ->
    Cminor.eval_expr g sp' e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n1) v -> 
    Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (n1 + n2)) v.
Proof.
  intros until 1 /sng.
  specialize chain_structure_cut with (1:=h_chain_m_add_sp_)(g:=g)(e:=e) as h /d.
  intros.
  repeat subst_det_addrstack_zero.
  assumption.
Qed.




Lemma chain_repeat_loadv_2: forall (m : mem) (n : nat) (sp : Values.val),
    chained_stack_structure m n sp
    -> forall (v : Values.val) (g : genv) (e : env),
      eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v
      -> repeat_Mem_loadv AST.Mint32 m n sp v.
Proof.
  intros until 1 /sng.
  induction h_chain_m_n_sp_;intros /sng.
  - inversion h_CM_eval_expr_bldlds_v_ /sng.
    inversion h_eq_evalcst_v_.
    rewrite Ptrofs.add_zero_l.
    constructor.
  - assert (chained_stack_structure m (S n) (Values.Vptr b Ptrofs.zero)) by (econstructor;eauto).    
    econstructor 2.
    all:swap 1 2.
    + eassumption.
    + eapply h_all_repeat_loadv_ with (g:=g)(e:=e).
      cbn in h_CM_eval_expr_bldlds_v_.
      specialize chained_stack_structure_decomp_S_2 with (1:=H)(2:=h_CM_eval_expr_bldlds_v_) as ? /d/sng.
      assert ((Values.Vptr b' Ptrofs.zero) = sp') /ng.
      { clear h_CM_eval_expr_bldlds_v_0.
        inversion h_CM_eval_expr_Eload_sp'_;subst /sng.
        inversion h_CM_eval_expr_Econst_vaddr_ /sng.
        cbn in h_eq_evalcst_vaddr_.
        rewrite Ptrofs.add_zero_l in h_eq_evalcst_vaddr_.
        inversion h_eq_evalcst_vaddr_.
        subst.
        rewrite h_eq_loadv_vptr_ in h_eq_loadv_sp'_.
        inversion h_eq_loadv_sp'_.
        auto. }
      rewrite h_eq_vptr_sp'_.
      assumption.
Qed.

Lemma chain_repeat_loadv: forall (m : mem) (n : nat) (sp : Values.val),
    chained_stack_structure m n sp
    -> forall (v : Values.val) (g : genv) (e : env),
      repeat_Mem_loadv AST.Mint32 m n sp v
      <-> eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v.
Proof.
  split.
  - apply chain_repeat_loadv_1;auto.
  - apply chain_repeat_loadv_2;auto.
Qed.


Lemma chain_struct_build_loads_ofs : forall  m n sp_init,
    chained_stack_structure m n sp_init ->
    forall δ_var g e b ofs,
      (δ_var mod Ptrofs.modulus)%Z = δ_var ->
      Cminor.eval_expr g sp_init e m (build_loads n δ_var) (Values.Vptr b ofs) ->
      ofs = Ptrofs.repr δ_var.
Proof.
  intros /sng.
  specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_n_sp_init_) as ? /d/sng.
    unfold build_loads in h_CM_eval_expr_bldlds_vptr_;cbn.
  invclear h_CM_eval_expr_bldlds_vptr_ /sng.
  inversion h_CM_eval_expr_Econst_v2_  /sng; cbn in *.
  invclear h_eq_evop_Oadd_vptr_ /sng.
  invclear h_eq_evalcst_v2_ /sng.  
  replace n with (0+n)%nat in h_CM_eval_expr_bldlds_v1_,h_chain_m_n_sp_init_ by auto with arith.
  specialize chain_structure_cut with (1:=h_chain_m_n_sp_init_) (g:=g)(e:=e) as ? /d/sng.
  replace (0+n)%nat with n in h_CM_eval_expr_bldlds_v1_,h_chain_m_n_sp_init_ by auto with arith.  
  subst_det_addrstack_zero.
  specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_0_sp'_) as ? /d/sng.
  cbn in h_eq_val_add_vptr_.
  rewrite Ptrofs.add_zero_l in h_eq_val_add_vptr_.
  destruct Archi.ptr64 eqn:heq.
  - inversion h_eq_val_add_vptr_.
  - inversion h_eq_val_add_vptr_ /sng.
    unfold Ptrofs.of_int.
    rewrite Int.unsigned_repr_eq.
    apply f_equal.
    auto.
    unfold Ptrofs.modulus, Int.modulus.
    unfold Ptrofs.wordsize, Int.wordsize.
    unfold Wordsize_Ptrofs.wordsize, Wordsize_32.wordsize.
    rewrite heq.
    apply Z.mod_mod.
    assert (h:=Coqlib.two_power_nat_pos 32).
    lia.
Qed.


Lemma malloc_preserves_chained_structure : 
  forall lvl m sp b ofs  m' new_sp,
    Mem.alloc m b ofs = (m', new_sp) ->
    chained_stack_structure m lvl sp ->
    chained_stack_structure m' lvl sp.
Proof.
  intro lvl.
  induction lvl;intros /sng.
  - inversion h_chain_m_0_sp_ /sng.
    constructor.
  - inversion h_chain_m_S_sp_ /sng.
    cbn in *.
    econstructor.
    + eapply h_all_chain_;eauto.
    + cbn.
      eapply Mem.load_alloc_other;eauto.
Qed.


Lemma malloc_preserves_chaining_loads : 
  forall m lvl sp sz m' new_sp,
    Mem.alloc m 0 sz = (m', new_sp) ->
    forall n, (n <= lvl)%nat ->
         chained_stack_structure m lvl sp ->
         forall e g sp',
           Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) sp'
           -> Cminor.eval_expr g sp e m' (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) sp'.
Proof.
  intros until n /sng.
  induction n;intros /sng.
  - cbn in *.
    specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_lvl_sp_) as ? /d/sng.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - assert (n <= lvl)%nat by lia /sng.
    specialize (h_impl_CM_eval_expr_ h_le_n_lvl_ h_chain_m_lvl_sp_).
    cbn -[Mem.storev] in *.
    inversion h_CM_eval_expr_bldlds_sp'_ /sng.
    specialize h_impl_CM_eval_expr_ with (1:=h_CM_eval_expr_bldlds_vaddr_).
    econstructor.
    + eassumption.
    + cbn in *.
      rewrite <- h_eq_loadv_sp'_.
      destruct vaddr; try discriminate.
      cbn in *.
      eapply Mem.load_alloc_unchanged;eauto.
      eapply Mem.valid_access_valid_block.
      apply Mem.load_valid_access in h_eq_loadv_sp'_.
       eapply Mem.valid_access_implies with (1:=h_eq_loadv_sp'_).
      constructor.
Qed.


Lemma malloc_preserves_chaining_loads_2 : 
  forall m lvl sp sz m' new_sp,
    Mem.alloc m 0 sz = (m', new_sp) ->
    forall n, (n <= lvl)%nat ->
         chained_stack_structure m lvl sp ->
         forall e g sp',
           Cminor.eval_expr g sp e m' (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) sp'
           -> Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) sp'.
Proof.
  intros until n /sng.
  induction n;intros /sng.
  - cbn in *.
    specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_lvl_sp_) as ? /d/sng.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - assert (n <= lvl)%nat by lia /sng.
    specialize (h_impl_CM_eval_expr_ h_le_n_lvl_ h_chain_m_lvl_sp_).
    cbn -[Mem.storev] in *.
    inversion h_CM_eval_expr_bldlds_sp'_ /sng.
    specialize (h_impl_CM_eval_expr_ _ _ _ h_CM_eval_expr_bldlds_vaddr_).
    econstructor.
    + eassumption.
    + cbn in *.
      rewrite <- h_eq_loadv_sp'_.
      destruct vaddr; try discriminate.
      cbn in *.
      symmetry.
      eapply Mem.load_alloc_unchanged;eauto.
      destruct (Mem.valid_block_alloc_inv _ _ _ _ _ h_malloc_m_m'_ b).
      * eapply Mem.valid_access_valid_block.
        apply Mem.load_valid_access in h_eq_loadv_sp'_.
        eapply Mem.valid_access_implies with (1:=h_eq_loadv_sp'_).
        constructor.
      * exfalso.
        subst.
        assert ((lvl-n) + n = lvl)%nat by lia /ng.
        rewrite <- h_eq_add_lvl_ in h_chain_m_lvl_sp_.
        specialize chain_structure_cut with (1:=h_chain_m_lvl_sp_) (g:=g) (e:=e) as ? /d/sng.
        rewrite h_eq_add_lvl_ in h_CM_eval_expr_bldlds_v_.
        subst_det_addrstack_zero.
        destruct (lvl - n)%nat eqn:heq'.
        -- exfalso; lia.
        -- cbn in h_CM_eval_expr_bldlds_v_0.
           eapply chained_stack_structure_decomp_S_2 in h_CM_eval_expr_bldlds_v_0.
           ++ decomp h_CM_eval_expr_bldlds_v_0.
              inversion h_CM_eval_expr_Eload_sp'0_ /sng.
              subst_det_addrstack_zero.
              absurd (Mem.valid_block m new_sp).
              ** eapply Mem.fresh_block_alloc;eauto.
              ** unfold Mem.loadv in h_CM_eval_expr_Eload_sp'0_.
                 eapply  Mem.load_valid_access in h_eq_loadv_sp'0_.
                 eapply Mem.valid_access_valid_block.
                 eapply Mem.valid_access_implies;eauto.
                 constructor.
           ++ assumption.
      * assumption.
Qed.




Lemma malloc_distinct_from_chaining_loads : 
  forall lvl m sp, 
    chained_stack_structure m lvl sp ->
    forall n sz m' new_sp,
      Mem.alloc m 0 sz = (m', new_sp) ->
      forall e g, (n < lvl)%nat -> forall b' ,
          Cminor.eval_expr g sp e m 
                           ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)
          -> b' <> new_sp.
Proof.
  intros * ? /sng.
  induction h_chain_m_lvl_sp_;cbn;intros /sng.
  - exfalso;lia.
  - destruct n0.
    + cbn in *.
      subst_det_addrstack_zero /sng.
      invclear H /sng.
      intro abs;subst b.
      specialize Mem.load_valid_access with (1:=h_eq_loadv_vptr_) as ?/sng.
      specialize Mem.fresh_block_alloc with (1:=h_malloc_m_m'_) as ? /sng.
      apply h_not_valid_blck_.
      eapply Mem.valid_access_valid_block.
      eapply Mem.valid_access_implies with (1:=h_valid_access_new_sp_).
      constructor.
    + eapply h_all_neq_ with (n0:=n0);eauto.
      * lia.
      * assert(chained_stack_structure m (S n) (Values.Vptr b Ptrofs.zero)) /sng.
        { econstructor;eauto. }
        assert(chained_stack_structure m (S n0) (Values.Vptr b Ptrofs.zero)) /sng.
        { eapply chained_stack_structure_le with (n:=S n).
          - assumption.
          - lia. }
        specialize chained_stack_structure_decomp_S_2 with (1:=h_chain_m_S_vptr_0) (2:=h_CM_eval_expr_bldlds_vptr_) as ? /d/sng.
        inversion h_CM_eval_expr_Eload_sp'_ /sng.
        subst_det_addrstack_zero.
        subst.
        rewrite h_eq_loadv_vptr_ in h_eq_loadv_sp'_.
        inversion h_eq_loadv_sp'_.
        subst.
        eassumption.
Qed.


(* if we store in a block [sp0] not invovlved in the chaining from [sp], then
   all chainging addresses reachable from sp from sp'' are unchanged. *)
Lemma chain_aligned: forall m n stkptr,
  chained_stack_structure m n stkptr ->
  forall lgth_CE_,
    (lgth_CE_ <= n)%nat ->
    forall locenv g,
      stack_localstack_aligned lgth_CE_ locenv g m stkptr.
Proof.
  intros until 1 /sng.
  unfold stack_localstack_aligned.
  induction h_chain_m_n_stkptr_; intros /sng.
  - exists b.
    assert (δ_lvl = 0%nat) by lia;subst.
    cbn.
    apply cm_eval_addrstack_zero.
  - destruct δ_lvl.
    + cbn.
      exists b.
      apply cm_eval_addrstack_zero.
    + cbn.
      destruct lgth_CE_;[cbn in h_le_δ_lvl_lgth_CE__;exfalso;lia|] /sng.
      specialize (h_all_CM_eval_expr_ lgth_CE_).
      assert (lgth_CE_ <= n) by lia /sng.
      assert (δ_lvl <= lgth_CE_)%nat by lia /sng.
      specialize h_all_CM_eval_expr_ with (1:= h_le_lgth_CE__n_) (2:=h_le_δ_lvl_lgth_CE__0).
      specialize (h_all_CM_eval_expr_ locenv g).
      decomp h_all_CM_eval_expr_.
      exists b_δ.
      assert (chained_stack_structure m (S δ_lvl) (Values.Vptr b Ptrofs.zero)).
      { econstructor; eauto.
        eapply chained_stack_structure_le;eauto.
        lia. }
      eapply chained_stack_structure_decomp_S_2';eauto.
      econstructor;eauto.
      eapply cm_eval_addrstack_zero_chain;eauto.
Qed.

Lemma storev_outside_struct_chain_preserves_chaining:
  forall sp0 e sp g m lvl,
      (* chainging addresses are unchanged. *)
      (forall n, (n < lvl)%nat -> forall b' ,
            Cminor.eval_expr g sp e m 
                             ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)
            -> b' <> sp0) ->
      forall n, chained_stack_structure m lvl sp ->
           forall x _v _chk m', Mem.storev _chk m (Values.Vptr sp0 _v) x = Some m' ->
                   (n <= lvl)%nat -> forall v,
                       Cminor.eval_expr g sp e m ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) v
                       -> Cminor.eval_expr g sp e m' ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) v.
Proof.
  intros until lvl /sng.
  intros h_eval_sp_lds_ n.
  induction n; intros /sng.
  - cbn in *.
    specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_lvl_sp_) as ? /d/sng.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - assert (n <= lvl)%nat by lia /sng.
    specialize h_impl_CM_eval_expr_ with (1 := h_chain_m_lvl_sp_) (2:=h_eq_storev_m'_) (3:=h_le_n_lvl_).
    cbn -[Mem.storev] in *.
    inversion h_CM_eval_expr_bldlds_v0_ /sng.
    specialize (h_impl_CM_eval_expr_ _ h_CM_eval_expr_bldlds_vaddr_).
    econstructor.
    + eassumption.
    + cbn in *.
      destruct vaddr; try discriminate.
      cbn in *.
      specialize Mem.load_store_other with (1:=h_eq_storev_m'_) (chunk':=AST.Mint32) (b':=b) (ofs' := (Ptrofs.unsigned i)) as h.
      rewrite h.
      * assumption.
      * left.
        eapply h_eval_sp_lds_ with (n:=n).
        -- lia.
        -- assert (i = Ptrofs.zero). 
           { specialize chain_aligned with (1 := h_chain_m_lvl_sp_) (locenv:=e) (g:=g) as ? /sng.
             especialize h_all_aligned_ at 1.
             { apply le_n. }
             red in h_all_aligned_.
             assert (n <= lvl) by lia /sng.
             specialize (h_all_aligned_ _ h_le_n_lvl_0).
             decomp h_all_aligned_.
              (subst_det_addrstack_zero;idtac) /sng.
             inversion h_eq_vptr_vptr_.
             reflexivity. }
           subst.
           eassumption.
Qed.

(* more general result: we can change something in the chained
structure but not the structure itself (chainging pointers. *)
Lemma gen_storev_outside_struct_chain_preserves_chaining:
  forall sp0 e sp g m lvl ofs0,
    (* chainging addresses are unchanged. *)
    ((4 <= (Ptrofs.unsigned ofs0))%Z \/
    (forall n, (n < lvl)%nat -> forall b' ,
          Cminor.eval_expr
            g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)
            (Values.Vptr b' Ptrofs.zero)
          -> b' <> sp0)) ->
    forall n, chained_stack_structure m lvl sp ->
              forall x _chk m', Mem.storev _chk m (Values.Vptr sp0 ofs0) x = Some m' ->
                                (n <= lvl)%nat -> forall v,
                                    Cminor.eval_expr g sp e m ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) v
                                    -> Cminor.eval_expr g sp e m' ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) v.
Proof.
  intros until ofs0 /sng.
  intros h_eval_sp_lds_ n.
  induction n;intros /sng.
  - cbn in *.
    specialize chained_stack_struct_inv_sp_zero with (1 := h_chain_m_lvl_sp_) as ? /d/sng.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - assert (n <= lvl)%nat by lia /sng.
    specialize h_impl_CM_eval_expr_ with (1:=h_chain_m_lvl_sp_)(2:=h_eq_storev_m'_) (3:=h_le_n_lvl_).
    cbn -[Mem.storev] in *.
    inversion h_CM_eval_expr_bldlds_v_ /sng.
    specialize (h_impl_CM_eval_expr_ _ h_CM_eval_expr_bldlds_vaddr_).
    econstructor.
    + eassumption.
    + cbn in *.
      destruct vaddr; try discriminate.
      cbn in *.
      specialize Mem.load_store_other with (1 := h_eq_storev_m'_) (chunk':=AST.Mint32) (b':=b) (ofs':=Ptrofs.unsigned i) as h.
      rewrite h.
      * assumption.
      * destruct h_eval_sp_lds_ /sng.
        -- right.
           assert (i = Ptrofs.zero).
           { specialize chained_stack_structure_le with (1:=h_chain_m_lvl_sp_) (2:=h_le_n_lvl_) as ? /sng.
             specialize chain_structure_spec with (1:=h_chain_m_n_sp_) (g:=g)(e:=e) as ? /sng.
             decomp h_ex_CM_eval_expr_.
             specialize det_eval_expr with (1:=h_CM_eval_expr_bldlds_vptr_) (2:=h_CM_eval_expr_bldlds_vaddr_) as ? /sng.
             inversion h_eq_vptr_vptr_ /sng.
             reflexivity. }
           subst.
           left.
           cbn.
           rewrite Ptrofs.unsigned_zero.
           lia.
        -- left.
           eapply h_all_neq_ with (n:=n).
           ++ lia.
           ++ assert (i = Ptrofs.zero). 
              { specialize chain_aligned with (1 := h_chain_m_lvl_sp_) (locenv:=e) (g:=g) as hh.
                especialize hh at 1 as hh' /sng. (* hh' to make /sng rename it *)
                { apply le_n. }
                red in h_aligned_g_m_.
                assert (n <= lvl) by lia /sng.
                specialize (h_aligned_g_m_ _ h_le_n_lvl_0).
                decomp h_aligned_g_m_.
                 (subst_det_addrstack_zero;idtac) /sng.
                inversion h_eq_vptr_vptr_.
                reflexivity. }
              subst.
              eassumption.
Qed.


Lemma storev_outside_struct_chain_preserves_chaining2:
  forall sp0 e sp g m lvl,
      (* chainging addresses are unchanged. *)
      (forall n, (n < lvl)%nat -> forall b' ,
            Cminor.eval_expr g sp e m 
                             ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)
            -> b' <> sp0) ->
      forall n, chained_stack_structure m lvl sp ->
           forall x _v _chk m', Mem.storev _chk m (Values.Vptr sp0 _v) x = Some m' ->
                   (n <= lvl)%nat -> forall v,
                       Cminor.eval_expr g sp e m' ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) v
                       -> Cminor.eval_expr g sp e m ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) v.
Proof.
  intros until lvl /sng.
  intros h_eval_sp_lds_ n.
  induction n;intros /sng.
  - cbn in *.
    specialize chained_stack_struct_inv_sp_zero with (1 := h_chain_m_lvl_sp_) as ? /d/sng.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - assert (n <= lvl)%nat by lia /sng.
    specialize h_impl_CM_eval_expr_ with (1:=h_chain_m_lvl_sp_) (2:=h_eq_storev_m'_) (3:=h_le_n_lvl_).
    cbn -[Mem.storev] in *.
    inversion h_CM_eval_expr_bldlds_v0_ /sng.
    specialize (h_impl_CM_eval_expr_ _ h_CM_eval_expr_bldlds_vaddr_).
    econstructor.
    + eassumption.
    + cbn in *.
      destruct vaddr; try discriminate.
      cbn in *.
      specialize Mem.load_store_other with (1 := h_eq_storev_m'_) (chunk':=AST.Mint32) (b':=b)(ofs':=Ptrofs.unsigned i) as h.
      rewrite <- h.
      * assumption.
      * left.
        eapply h_eval_sp_lds_ with (n:=n).
        -- lia.
        -- assert (i = Ptrofs.zero). 
           { specialize chain_aligned with (1:=h_chain_m_lvl_sp_)(locenv:=e)(g:=g) as hh.
             especialize hh at 1 as hh' /sng.
             { apply le_n. }
             red in h_aligned_g_m_.
              assert (n <= lvl) by lia /sng.
             specialize (h_aligned_g_m_ _ h_le_n_lvl_0).
             decomp h_aligned_g_m_.
              (subst_det_addrstack_zero;idtac) /sng.
             inversion h_eq_vptr_vptr_.
             reflexivity. }
           subst.
           eassumption.
Qed.

(* More general result *)
Lemma gen_storev_outside_struct_chain_preserves_chaining2:
  forall sp0 e sp g m lvl ofs0,
    (* chainging addresses are unchanged. *)
    ((4 <= (Ptrofs.unsigned ofs0))%Z \/
     forall n, (n < lvl)%nat -> forall b' ,
         Cminor.eval_expr g sp e m 
                          ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)
         -> b' <> sp0) ->
    forall n, chained_stack_structure m lvl sp ->
              forall x _chk m', Mem.storev _chk m (Values.Vptr sp0 ofs0) x = Some m' ->
                                   (n <= lvl)%nat -> forall v,
                                       Cminor.eval_expr g sp e m' ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) v
                                       -> Cminor.eval_expr g sp e m ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) v.
Proof.
  intros until ofs0 /sng.
  intros h_eval_sp_lds_ n/g.
  induction n;intros /sng.
  - cbn in *.
    specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_lvl_sp_) as ? /d/sng.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - assert (n <= lvl)%nat by lia /sng.
    specialize h_impl_CM_eval_expr_ with (1:=h_chain_m_lvl_sp_) (2:=h_eq_storev_m'_) (3:=h_le_n_lvl_).
    cbn -[Mem.storev] in *.
    inversion h_CM_eval_expr_bldlds_v_ /sng.
    specialize h_impl_CM_eval_expr_ with (1:=h_CM_eval_expr_bldlds_vaddr_).
    econstructor.
    + eassumption.
    + cbn in *.
      destruct vaddr; try discriminate.
      cbn in *.
      specialize Mem.load_store_other with (1 := h_eq_storev_m'_) (chunk':=AST.Mint32) (b':=b) (ofs':=Ptrofs.unsigned i) as h.
      rewrite <- h.
      * assumption.
      * destruct h_eval_sp_lds_ /sng.
        -- right.
           assert (i = Ptrofs.zero).
           { specialize chained_stack_structure_le with (1:=h_chain_m_lvl_sp_) (2:=h_le_n_lvl_) as ? /sng.
             specialize chain_structure_spec with (1:=h_chain_m_n_sp_) (g:=g)(e:=e) as ? /d/sng.
             inversion h_CM_eval_expr_bldlds_v_ /sng.
             specialize det_eval_expr with (1:=h_CM_eval_expr_bldlds_vptr_) (2:=h_impl_CM_eval_expr_) as ? /sng.
             inversion h_eq_vptr_vptr_.
             reflexivity. }
           subst.
           left.
           cbn.
           rewrite Ptrofs.unsigned_zero.
           lia.
        -- left.
           eapply h_all_neq_ with (n:=n).
           ++ lia.
           ++ assert (i = Ptrofs.zero). 
              { specialize chain_aligned with (1 := h_chain_m_lvl_sp_) (locenv:=e)(g:=g) as hh.
                especialize hh at 1.
                { apply le_n. }
                autorename hh.
                red in h_aligned_g_m_.
                assert (n <= lvl) by lia /sng.
                specialize (h_aligned_g_m_ _ h_le_n_lvl_0).
                decomp h_aligned_g_m_.
                 (subst_det_addrstack_zero;idtac) /sng.
                inversion h_eq_vptr_vptr_.
                reflexivity. }
              subst.
              eassumption.
Qed.

Lemma storev_outside_struct_chain_preserves_var_addresses:
  forall sp0 e sp g m lvl,
      (* chainging addresses are unchanged. *)
      (forall n, (n < lvl)%nat -> forall b' ,
            Cminor.eval_expr g sp e m 
                             ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)
            -> b' <> sp0) ->
      forall n, chained_stack_structure m lvl sp ->
           forall x va _chk m' δ, Mem.storev _chk m (Values.Vptr sp0 va) x = Some m' ->
                   (n <= lvl)%nat -> forall v,
                       Cminor.eval_expr g sp e m ((build_loads n δ)) v
                       -> Cminor.eval_expr g sp e m' ((build_loads n δ)) v.
Proof.
  intros until lvl /sng.
  intros h_eval_sp_lds_ n.
  intros /sng.
  unfold build_loads in *.
  invclear h_CM_eval_expr_bldlds_v_ /sng.
  econstructor;[ | |eassumption].
  - eapply storev_outside_struct_chain_preserves_chaining;eauto.
  - inversion h_CM_eval_expr_Econst_v2_ /sng.
    constructor.
    assumption.
Qed.

Lemma storev_outside_struct_chain_preserves_var_addresses2:
  forall sp0 e sp g m lvl,
      (* chainging addresses are unchanged. *)
      (forall n, (n < lvl)%nat -> forall b' ,
            Cminor.eval_expr g sp e m 
                             ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)
            -> b' <> sp0) ->
      forall n, chained_stack_structure m lvl sp ->
           forall x va _chk m' δ, Mem.storev _chk m (Values.Vptr sp0 va) x = Some m' ->
                   (n <= lvl)%nat -> forall v,
                       Cminor.eval_expr g sp e m' ((build_loads n δ)) v
                       -> Cminor.eval_expr g sp e m ((build_loads n δ)) v.
Proof.
  intros until lvl /sng.
  intros h_eval_sp_lds_ n.
  intros /sng.
  unfold build_loads in *.
  invclear h_CM_eval_expr_bldlds_v_ /sng.
  econstructor;[ | |eassumption].
  - eapply storev_outside_struct_chain_preserves_chaining2;eauto.
  - inversion h_CM_eval_expr_Econst_v2_ /sng.
    constructor.
    assumption.
Qed.

(* The content of variable do not change either (we go one lvl less deep, since we add one ELoad.  *)
Lemma storev_outside_struct_chain_preserves_var_value:
  forall sp0 e sp g m lvl,
      (* chainging addresses are unchanged. *)
      (forall n, (n <= lvl)%nat -> forall b' ,
            Cminor.eval_expr g sp e m 
                             ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)
            -> b' <> sp0) ->
      forall n, chained_stack_structure m lvl sp ->
           forall x va _chk _chk' m' δ, Mem.storev _chk m (Values.Vptr sp0 va) x = Some m' ->
                   (n <= lvl)%nat -> forall v,
                       Cminor.eval_expr g sp e m (Eload _chk' (build_loads n δ)) v
                       -> Cminor.eval_expr g sp e m' (Eload _chk' (build_loads n δ)) v.
Proof.
  intros /sng.
  rename h_all_neq_ into h_unch_.
  inversion h_CM_eval_expr_Eload_v_ /sng.
  assert (h_unch'_:forall n : nat,
             (n < lvl)%nat
             -> forall b' : Values.block,
               Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) (Values.Vptr b' Ptrofs.zero) -> b' <> sp0).
  { intros.
    eapply h_unch_ with (n:=n0).
    - lia.
    - assumption. }
  specialize storev_outside_struct_chain_preserves_var_addresses
    with (1 := h_unch'_)(2:=h_chain_m_lvl_sp_)(3:=h_eq_storev_m'_)(4:=h_le_n_lvl_)(5:=h_CM_eval_expr_bldlds_vaddr_) as ? /n. 
  econstructor;eauto.
  unfold build_loads in h_CM_eval_expr_bldlds_vaddr_, h_CM_eval_expr_bldlds_vaddr_0.
  invclear h_CM_eval_expr_bldlds_vaddr_ /sng.
  invclear h_CM_eval_expr_bldlds_vaddr_0 /sng.
  destruct vaddr;try discriminate.
  specialize Mem.load_store_other  with (1:=h_eq_storev_m'_)(chunk':=_chk')(b':=b)(ofs':=Ptrofs.unsigned i) as h.
  unfold Mem.loadv in *.
  rewrite h.
  - assumption.
  - left.
    assert (v1=(Values.Vptr b Ptrofs.zero)) /sng.
    { clear h. 
      specialize chain_aligned with (1:=h_chain_m_lvl_sp_)(locenv:=e)(g:=g) as hh.
      especialize hh at 1.
      { apply le_n. }
      autorename hh.
      red in h_aligned_g_m_.
      assert (n <= lvl) by lia /sng.
      specialize (h_aligned_g_m_ _ h_le_n_lvl_0).
      decomp h_aligned_g_m_.
      subst_det_addrstack_zero.
      f_equal.
      cbn in *.
      destruct v2;try discriminate.
      inversion h_eq_evop_Oadd_vaddr_.
      destruct Archi.ptr64;auto. }
    subst.
    eapply h_unch_;eauto.
Qed.


Proposition storev_outside_struct_chain_preserves_chained_structure:
  forall (sp0 : Values.block) (e : env) (sp : Values.val) (g : genv) (m : mem) (lvl : nat),
    (forall n : nat,
        (n < lvl)%nat
        -> forall b' : Values.block,
          Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) (Values.Vptr b' Ptrofs.zero) -> b' <> sp0)
    -> chained_stack_structure m lvl sp
    -> forall (x : Values.val) (_v : ptrofs) (_chk : AST.memory_chunk) (m' : mem),
        Mem.storev _chk m (Values.Vptr sp0 _v) x = Some m' ->
        chained_stack_structure m' lvl sp.
Proof.
  intros /sng.
  assert
    ( forall n, (n <= lvl)%nat -> forall v : Values.val,
          Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v
          -> Cminor.eval_expr g sp e m' (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v).
  { intro /sng.
    eapply storev_outside_struct_chain_preserves_chaining;eauto. }
  destruct (chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_lvl_sp_).
  subst.
  eapply chained_stack_structure_spec.
  intros /sng.
  specialize (chain_structure_spec lvl0 m (Values.Vptr x0 Ptrofs.zero)) as ?/sng.
  edestruct h_impl_CM_eval_expr_ with (g:=g) (e:=e) /sng.
  - eapply chained_stack_structure_le;eauto;try lia.
  - eauto.
Qed.


Lemma malloc_distinct_from_chaining_loads_2 : 
  forall lvl m sp, 
    chained_stack_structure m lvl sp ->
    forall n sz m' new_sp,
      Mem.alloc m 0 sz = (m', new_sp) ->
      forall e g, (n < lvl)%nat -> forall b' ,
          Cminor.eval_expr g sp e m'
                           ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)
          -> b' <> new_sp.
Proof.
  intros /sng.
  assert (Cminor.eval_expr g sp e m
                           ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)).
  { eapply malloc_preserves_chaining_loads_2;eauto.
    eapply chained_stack_structure_le;eauto;try lia. }
  eapply malloc_distinct_from_chaining_loads; eauto.
Qed.

