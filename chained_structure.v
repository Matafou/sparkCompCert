Require Import sparkfrontend.LibTac sparkfrontend.LibHypsNaming  Errors
        Cminor compcert.lib.Integers sparkfrontend.compcert_utils sparkfrontend.more_stdlib.
Require Import SetoidList Omega.
Import Memory.
Require Ctypes.

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

Ltac rename_chained t th :=
  match th with
| chained_stack_structure ?m ?lvl ?sp => fresh "chain_" m "_" lvl "_" sp
| chained_stack_structure ?m ?lvl _ => fresh "chain_" m "_" lvl
| chained_stack_structure ?m _ _ => fresh "chain_" m
| chained_stack_structure _ ?lvl _ => fresh "chain_" lvl
| chained_stack_structure _ _ _ => fresh "chain"
| repeat_Mem_loadv _ ?m ?lvl ?v ?sp => fresh "repeat_loadv_" lvl "_" v
| repeat_Mem_loadv _ ?m ?lvl ?v ?sp => fresh "repeat_loadv_" lvl
| repeat_Mem_loadv _ ?m ?lvl ?v ?sp => fresh "repeat_loadv"
| stack_localstack_aligned _ _ ?g ?m ?sp => fresh "aligned_" g "_" m
| stack_localstack_aligned _ _ _ ?m ?sp => fresh "aligned_" m
| stack_localstack_aligned _ _ ?g _ ?sp => fresh "aligned_" g
end.

Ltac prefixable h th ::=
  match th with
  | _ => prefixable_compcert h th
  | _ => prefixable_eq_neq h th
  end.


Ltac rename_hyp h th ::=
  match th with
  | _ => (compcert_utils.rename_hyp1 h th)
  | _ => (LibHypsNaming.rename_hyp_neg h th)
  | _ => (rename_chained h th)
  end.

Lemma chained_stack_structure_le m sp : forall n,
    chained_stack_structure m n sp ->
    forall n', (n' <= n)%nat -> 
               chained_stack_structure m n' sp.
Proof.
  !!intros ? ?.
  !induction h_chain_m_n_sp;!intros.
  - assert (n'=0)%nat by omega;subst.
    constructor.
  - destruct n'.
    * constructor.
    * econstructor;eauto.
      apply h_forall_n';eauto;omega.
Qed.

Lemma chained_stack_struct_inv_sp_zero: forall m n sp,
    chained_stack_structure m n sp -> exists b',  sp = (Values.Vptr b' Ptrofs.zero).
Proof.
  !intros.
  inversion h_chain_m_n_sp;subst;eauto.
Qed.

Lemma chained_stack_struct_sp_add: forall m n sp,
    chained_stack_structure m n sp -> (Values.Val.add sp (Values.Vint Int.zero)) = sp.
Proof.
  !intros.
  destruct (chained_stack_struct_inv_sp_zero m n sp);subst;auto.
Qed.

Lemma cm_eval_addrstack_zero:
  forall b ofs m g e,
      Cminor.eval_expr g (Values.Vptr b ofs) e m (Econst (Oaddrstack Ptrofs.zero)) (Values.Vptr b ofs).
Proof.
  !intros.
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
  !intros.
  destruct (chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_n_sp).
  subst.
  apply cm_eval_addrstack_zero.
Qed.

(* a useful formulation of the two previous lemmas. *)
Lemma det_cm_eval_addrstack_zero_chain : forall m lvl sp e g vaddr,
    chained_stack_structure m lvl sp ->
    Cminor.eval_expr g sp e m (Econst (Oaddrstack Ptrofs.zero)) vaddr ->
    vaddr = sp.
Proof.
  !intros.
  pose proof cm_eval_addrstack_zero_chain lvl sp m h_chain_m_lvl_sp g e.
  eapply det_eval_expr;eauto.
Qed.

Lemma det_cm_eval_addrstack_zero : forall b i m e g vaddr,
    Cminor.eval_expr g (Values.Vptr b i) e m (Econst (Oaddrstack Ptrofs.zero)) vaddr ->
    vaddr = (Values.Vptr b i).
Proof.
  !intros.
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
  !!intros until 1.
  inversion h_chain_m;subst;!intros.
  exists b';split;[|split];eauto.
  econstructor;eauto.
  constructor.
  cbn.
  reflexivity.
Qed.

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
  !intros.
  revert v b h_CM_eval_expr h_CM_eval_expr_v.
  !induction n.
  - !intros.
    cbn in *.
    exists v;split;auto.
    constructor;cbn.
    subst_det_addrstack_zero.
    cbn.
    rewrite Ptrofs.add_zero.
    reflexivity.
  - !intros.
    cbn in h_CM_eval_expr_v.
    !invclear h_CM_eval_expr_v;subst.
    change (Eload AST.Mint32 (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) with (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n)) in h_CM_eval_expr_vaddr.
    specialize (h_forall_v _ _ h_CM_eval_expr h_CM_eval_expr_vaddr).
    decomp h_forall_v.
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
  !!intros until n.
  !induction n.
  - !intros.
    cbn in *.
    exists v;split;auto.
    eapply cm_eval_addrstack_zero_chain with (n:=Nat.pred max);eauto.
    rewrite <- (Nat.succ_pred_pos _ h_lt_O_max) in h_chain_m_max_sp.
    !inversion h_chain_m_max_sp.
    !inversion h_CM_eval_expr_v.
    subst_det_addrstack_zero.
    rewrite h_loadv in h_loadv_vaddr_v.
    inversion h_loadv_vaddr_v.
    assumption.
  - !intros.
    cbn in h_CM_eval_expr_v.
    !invclear h_CM_eval_expr_v;subst.
    change (Eload AST.Mint32 (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) with (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n)) in h_CM_eval_expr_vaddr.
    !!assert (n<max) by omega.
    specialize h_forall_v with (1:=h_chain_m_max_sp)(2:=h_lt_n_max)(3:=h_CM_eval_expr_vaddr).
    decomp h_forall_v.
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
  !!induction n;!intros.
  - constructor.
  - !!assert (1 <= S n) by omega.
    !!pose proof  (h_forall_lvl 1%nat h_le).
    decomp h_ex.
    !!assert (S n <= S n) by omega.
    !!pose proof  (h_forall_lvl _ h_le0).
    decomp h_ex.
    cbn in *.
    !!specialize build_loads__decomp_S with (1:=h_CM_eval_expr)(2:=h_CM_eval_expr0) as ?.
    decomp h_ex.
    subst_det_addrstack_zero.
    eapply chained_S with (b':=b');eauto.
    + eapply h_forall_b.
      !intros.
      !!assert (S lvl <= S n) by omega.
      !!pose proof  (h_forall_lvl _ h_le1).
      decomp h_ex.
      cbn in *.
      !!specialize build_loads__decomp_S with (1:=h_CM_eval_expr_sp') (2:=h_CM_eval_expr) as ?.
      decomp h_ex.
      subst_det_addrstack_zero.
      eauto.
    + !inversion h_CM_eval_expr_sp'.
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
  !intros.
  induction h_chain_m_n_stkptr.
  - constructor.
  - econstructor.
    all:swap 1 2.
    + unfold Mem.loadv.
      unfold Mem.storev in heq_storev_e_t_v_m'.
      erewrite Mem.load_store_other with (m1:=m);eauto.
    + assumption.
Qed.


(*
Lemma add_Vint_zero: forall m vaddr x,
    Mem.loadv AST.Mint32 m vaddr = Some x ->
    Values.Val.add x (Values.Vint Int.zero) = x.
Proof.
  !intros. 
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
  !induction n.
  - !intros.
    cbn in *.
    !inversion h_CM_eval_expr_sp'.
    !inversion h_CM_eval_expr_vaddr.
    !inversion h_CM_eval_expr_v.
    cbn in *.
    !invclear h_eval_constant.
    !invclear h_eval_constant0;subst.
    assert (exists b, sp' = Values.Vptr b Ptrofs.zero).
    { !inversion h_chain_m.
      cbn in *.
      rewrite Ptrofs.add_zero in h_loadv_vaddr_sp'.
      rewrite h_loadv_vaddr_sp' in h_loadv.
      inversion h_loadv.
      eauto. }
    decomp H;subst.
    econstructor;cbn;eauto.
  - !intros.
    cbn in h_CM_eval_expr_v.
    cbn.
    inversion h_CM_eval_expr_v;subst.
    econstructor;eauto.
    eapply h_forall_m;eauto.
    eapply chained_stack_structure_le;eauto.
Qed.




Lemma chain_structure_spec:
  forall n m sp ,
    chained_stack_structure m n sp ->
    forall g e,
      exists b, Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) (Values.Vptr b Ptrofs.zero).
Proof.
  !!intros until 1.
  !induction h_chain_m_n_sp;!intros.
  - exists b.
    eapply cm_eval_addrstack_zero;eauto.
  - specialize (h_forall_g g e).
    decomp h_forall_g.
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
  !!intros until 1.
  !induction h_chain_m_n_sp;cbn;!intros.
  - !inversion h_repeat_loadv_O.
    apply cm_eval_addrstack_zero.
  - eapply chained_stack_structure_decomp_S_2'.
    + econstructor;eauto.
    + econstructor;eauto.
      econstructor;eauto.
    + eapply h_forall_v;eauto.
      !inversion h_repeat_loadv.
      rewrite h_loadv in h_loadv_sp'.
      !invclear h_loadv_sp'.
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
  !induction n.
  - !intros.
    cbn in *.
    exists v;split;auto.
    constructor;cbn.
    !!pose proof chained_stack_structure_aux _ _ _ h_chain_m g e.
    decomp h_ex.
    subst_det_addrstack_zero.
    cbn.
    rewrite Ptrofs.add_zero.  
    reflexivity.
  - !intros.
    cbn in h_CM_eval_expr_v.
    !inversion h_CM_eval_expr_v;subst.
    change (Eload AST.Mint32 (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) with (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) (S n)) in h_CM_eval_expr_vaddr.
    !assert (chained_stack_structure m (S n) sp).
    { eapply chained_stack_structure_le;eauto. }
    specialize h_forall_m with (1:=h_chain_m0) (2:=h_CM_eval_expr_vaddr).
    decomp h_forall_m.
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
  !!intros * ? *.
  !!pose proof chain_structure_spec _ _ _ h_chain_m g e.
  decomp h_ex.
  exists (Values.Vptr b Ptrofs.zero).
  revert dependent h_CM_eval_expr.
  revert dependent h_chain_m.
  revert n' m sp g e b.
  !induction n'';!intros;up_type.
  - replace (n'+0)%nat with n' in * by omega.
    exists sp;split;[eauto| split;eauto].
    cbn.
    eapply cm_eval_addrstack_zero_chain;eauto.
  - specialize (h_forall_n' (S n') m sp g e b).
    !assert (chained_stack_structure m (S n' + n'') sp).
    { replace (n' + S n'')%nat with (S n' + n'')%nat in h_chain_m; try omega.
      assumption. }
    specialize (h_forall_n' h_chain_m0).
    replace (n' + S n'')%nat with (S n' + n'')%nat in h_CM_eval_expr; try omega.
    specialize (h_forall_n' h_CM_eval_expr).
    decomp h_forall_n'.
    !specialize chained_stack_structure_decomp_S_2 with (1:=h_chain_m1)(2:=h_CM_eval_expr1) as ?. 
    decomp h_ex.
    exists sp'0;split;[|split;[|split]];eauto.
    + replace (n' + S n'')%nat with (S n' + n'')%nat; try omega.
      assumption.
    + cbn.
      econstructor.
      * eassumption.
      * !inversion h_CM_eval_expr_sp'0.
        repeat subst_det_addrstack_zero.
        assumption.
    + !inversion h_CM_eval_expr_sp'0;subst.
      repeat subst_det_addrstack_zero.
      clear h_chain_m h_chain_m0.
      !inversion h_chain_m1;subst;up_type.
      cbn in *.
      rewrite h_loadv in h_loadv_vaddr_sp'0.
      inversion h_loadv_vaddr_sp'0.
      subst.
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
  !intros.
  unfold base in h_CM_eval_expr_v.
  rewrite <- build_loads_compos in h_CM_eval_expr_v.
  cbn [plus] in h_CM_eval_expr_v.
  !!pose proof chained_stack_structure_decomp_S_2 _ _ _ h_chain_m g e v h_CM_eval_expr_v.
  decomp h_ex.
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
  !!intros until e.
  specialize chain_structure_cut with (1:=h_chain_m)(g:=g)(e:=e) as h.
  decomp h.
  !intros.
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
  !!intros until 1.
  specialize chain_structure_cut with (1:=h_chain_m)(g:=g)(e:=e) as h.
  decomp h.
  !intros.
  repeat subst_det_addrstack_zero.
  assumption.
Qed.




Lemma chain_repeat_loadv_2: forall (m : mem) (n : nat) (sp : Values.val),
    chained_stack_structure m n sp
    -> forall (v : Values.val) (g : genv) (e : env),
      eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v
      -> repeat_Mem_loadv AST.Mint32 m n sp v.
Proof.
  !!intros until 1.
  !induction h_chain_m_n_sp;!intros.
  - !inversion h_CM_eval_expr_v.
    inversion h_eval_constant.
    rewrite Ptrofs.add_zero_l.
    constructor.
  - assert (chained_stack_structure m (S n) (Values.Vptr b Ptrofs.zero)) by (econstructor;eauto).    
    econstructor 2.
    all:swap 1 2.
    + eassumption.
    + eapply h_forall_v with (g:=g)(e:=e).
      cbn in h_CM_eval_expr_v.
      specialize chained_stack_structure_decomp_S_2 with (1:=H)(2:=h_CM_eval_expr_v) as h.
      decomp h.
      !assert ((Values.Vptr b' Ptrofs.zero) = sp').
      { clear h_CM_eval_expr_v0.
        !inversion h_CM_eval_expr_sp';subst.
        !inversion h_CM_eval_expr_vaddr.
        cbn in h_eval_constant.
        rewrite Ptrofs.add_zero_l in h_eval_constant.
        inversion h_eval_constant.
        subst.
        rewrite h_loadv in h_loadv_vaddr_sp'.
        inversion h_loadv_vaddr_sp'.
        auto. }
      rewrite heq_vptr_b'_zero.
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
  !intros.
  !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_n_sp_init.
  decomp h_ex;subst.
  unfold build_loads in h_CM_eval_expr;cbn.
  !invclear h_CM_eval_expr.
  !inversion h_CM_eval_expr_v2;subst;cbn in *.
  !invclear h_eval_binop_Oadd_v1_v2.
  !invclear h_eval_constant.  
  replace n with (0+n)%nat in h_CM_eval_expr_v1,h_chain_m_n_sp_init by auto with arith.
  !!pose proof chain_structure_cut _ _ _ _ h_chain_m_n_sp_init g e.
  decomp h_ex.
  replace (0+n)%nat with n in h_CM_eval_expr_v1,h_chain_m_n_sp_init by auto with arith.  
  subst_det_addrstack_zero.
  !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_O_sp'.
  decomp h_ex.
  subst.
  cbn in h_val_add_v1_v2.
  rewrite Ptrofs.add_zero_l in h_val_add_v1_v2.
  destruct Archi.ptr64.
  - inversion h_val_add_v1_v2.
  - !inversion h_val_add_v1_v2.
    unfold Ptrofs.of_int.
    rewrite Int.unsigned_repr_eq.
    apply f_equal;auto.
Qed.


Lemma malloc_preserves_chained_structure : 
  forall lvl m sp b ofs  m' new_sp,
    Mem.alloc m b ofs = (m', new_sp) ->
    chained_stack_structure m lvl sp ->
    chained_stack_structure m' lvl sp.
Proof.
  intro lvl.
  !induction lvl;!intros.
  - !inversion h_chain_m_O_sp.
    constructor.
  - !inversion h_chain_m.
    cbn in *.
    econstructor.
    + eapply h_forall_m;eauto.
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
  !!intros until n.
  induction n;!intros.
  - cbn in *.
    !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_lvl_sp.
    decomp h_ex.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - !!assert (n <= lvl)%nat by omega.
    specialize (IHn h_le_n_lvl h_chain_m_lvl_sp).
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
  forall m lvl sp sz m' new_sp,
    Mem.alloc m 0 sz = (m', new_sp) ->
    forall n, (n <= lvl)%nat ->
         chained_stack_structure m lvl sp ->
         forall e g sp',
           Cminor.eval_expr g sp e m' (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) sp'
           -> Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) sp'.
Proof.
  !!intros until n.
  induction n;!intros.
  - cbn in *.
    !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_lvl_sp.
    decomp h_ex.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - !!assert (n <= lvl)%nat by omega.
    specialize (IHn h_le_n_lvl h_chain_m_lvl_sp).
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
        rewrite <- heq_add in h_chain_m_lvl_sp.
        !!pose proof (chain_structure_cut _ _ _ _ h_chain_m_lvl_sp) g e.
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
  !!intros * ?.
  !induction h_chain_m_lvl_sp;cbn;!intros.
  - exfalso;omega.
  - destruct n0.
    + cbn in *.
      !!subst_det_addrstack_zero.
      !invclear H.
      intro abs;subst b.
      !!pose proof Mem.load_valid_access _ _ _ _ _ h_loadv.
      !!pose proof Mem.fresh_block_alloc _ _ _ _ _ h_malloc_m_m'.
      apply h_neg_valid_blck_m_new_sp.
      eapply Mem.valid_access_valid_block.
      eapply Mem.valid_access_implies with (1:=h_valid_access_new_sp).
      constructor.
    + eapply h_forall_n with (n0:=n0);eauto.
      * omega.
      * !assert(chained_stack_structure m (S n) (Values.Vptr b Ptrofs.zero)).
        { econstructor;eauto. }
        !assert(chained_stack_structure m (S n0) (Values.Vptr b Ptrofs.zero)).
        { eapply chained_stack_structure_le with (n:=S n).
          - assumption.
          - omega. }
        !!pose proof chained_stack_structure_decomp_S_2 _ _ _ h_chain_m0 g e _ h_CM_eval_expr.
        decomp h_ex.
        !inversion h_CM_eval_expr_sp'.
        subst_det_addrstack_zero.
        subst.
        rewrite h_loadv in h_loadv_vaddr_sp'.
        inversion h_loadv_vaddr_sp'.
        subst.
        eassumption.
Qed.


(* if we store in a block [sp0] not invovlved in the chaining from [sp], then
   all chainging addresses reachable from sp from sp'' are unchanged. *)
Lemma chain_aligned: forall m n stkptr,
  chained_stack_structure m n stkptr ->
  forall lgth_CE,
    (lgth_CE <= n)%nat ->
    forall locenv g,
      stack_localstack_aligned lgth_CE locenv g m stkptr.
Proof.
  !!intros until 1.
  unfold stack_localstack_aligned.
  !induction h_chain_m_n_stkptr;!intros.
  - exists b.
    assert (δ_lvl = 0%nat) by omega;subst.
    cbn.
    apply cm_eval_addrstack_zero.
  - destruct δ_lvl.
    + cbn.
      exists b.
      apply cm_eval_addrstack_zero.
    + cbn.
      !!destruct lgth_CE;[cbn in h_le_δ_lvl_lgth_CE;exfalso;omega|].
      subst;up_type.
      specialize (h_forall_lgth_CE lgth_CE).
      !!assert (lgth_CE <= n) by omega.
      !!assert (δ_lvl <= lgth_CE)%nat by omega.
      specialize (fun locenv g => h_forall_lgth_CE h_le_lgth_CE_n locenv g δ_lvl h_le_δ_lvl_lgth_CE0).
      specialize (h_forall_lgth_CE locenv g).
      decomp h_forall_lgth_CE.
      exists b_δ.
      assert (chained_stack_structure m (S δ_lvl) (Values.Vptr b Ptrofs.zero)).
      { econstructor; eauto.
        eapply chained_stack_structure_le;eauto.
        omega. }
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
  !!intros until lvl.
  intros h_eval_sp_lds n.
  !induction n;!intros.
  - cbn in *.
    !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_lvl_sp.
    decomp h_ex.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - !!assert (n <= lvl)%nat by omega.
    specialize (h_impl_forall_x h_chain_m_lvl_sp _ _ _ _ heq_storev_x_m' h_le_n_lvl).
    cbn -[Mem.storev] in *.
    !inversion h_CM_eval_expr_v.
    specialize (h_impl_forall_x _ h_CM_eval_expr_vaddr).
    econstructor.
    + eassumption.
    + cbn in *.
      destruct vaddr; try discriminate.
      cbn in *.
      pose proof Mem.load_store_other _ _ _ _ _ _ heq_storev_x_m' AST.Mint32 b (Ptrofs.unsigned i) as h.
      rewrite h.
      * assumption.
      * left.
        eapply h_eval_sp_lds with (n:=n).
        -- omega.
        -- assert (i = Ptrofs.zero). 
           { !!pose proof chain_aligned _ _ _ h_chain_m_lvl_sp lvl (le_n _) e g.
             red in h_aligned_g_m.
             !!assert (n <= lvl) by omega.
             specialize (h_aligned_g_m _ h_le_n_lvl0).
             decomp h_aligned_g_m.
             !! (subst_det_addrstack_zero;idtac).
             inversion heq_vptr_b_i.
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
  !!intros until ofs0.
  intros h_eval_sp_lds n.
  !induction n;!intros.
  - cbn in *.
    !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_lvl_sp.
    decomp h_ex.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - !!assert (n <= lvl)%nat by omega.
    specialize h_impl_forall_x with (1:=h_chain_m_lvl_sp)(2:=heq_storev_x_m') (3:=h_le_n_lvl).
    cbn -[Mem.storev] in *.
    !inversion h_CM_eval_expr_v.
    specialize (h_impl_forall_x _ h_CM_eval_expr_vaddr).
    econstructor.
    + eassumption.
    + cbn in *.
      destruct vaddr; try discriminate.
      cbn in *.
      pose proof Mem.load_store_other _ _ _ _ _ _ heq_storev_x_m' AST.Mint32 b (Ptrofs.unsigned i) as h.
      rewrite h.
      * assumption.
      * !destruct h_eval_sp_lds.
        -- right.
           assert (i = Ptrofs.zero).
           { !!specialize chained_stack_structure_le with (1:=h_chain_m_lvl_sp) (2:=h_le_n_lvl) as ?.
             !!specialize chain_structure_spec with (1:=h_chain_m_n_sp) (g:=g)(e:=e) as ?.
             decomp h_ex.
             !!specialize det_eval_expr with (1:=h_CM_eval_expr) (2:=h_CM_eval_expr_vaddr) as ?.
             !inversion heq_vptr_b0_zero.
             reflexivity. }
           subst.
           left.
           cbn.
           rewrite Ptrofs.unsigned_zero.
           omega.
        -- left.
           eapply h_forall_n with (n:=n).
           ++ omega.
           ++ assert (i = Ptrofs.zero). 
              { !!pose proof chain_aligned _ _ _ h_chain_m_lvl_sp lvl (le_n _) e g.
                red in h_aligned_g_m.
                !!assert (n <= lvl) by omega.
                specialize (h_aligned_g_m _ h_le_n_lvl0).
                decomp h_aligned_g_m.
                !! (subst_det_addrstack_zero;idtac).
                inversion heq_vptr_b_i.
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
  !!intros until lvl.
  intros h_eval_sp_lds n.
  !induction n;!intros.
  - cbn in *.
    !!pose proof chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_lvl_sp.
    decomp h_ex.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - !!assert (n <= lvl)%nat by omega.
    specialize (h_impl_forall_x h_chain_m_lvl_sp _ _ _ _ heq_storev_x_m' h_le_n_lvl).
    cbn -[Mem.storev] in *.
    !inversion h_CM_eval_expr_v.
    specialize (h_impl_forall_x _ h_CM_eval_expr_vaddr).
    econstructor.
    + eassumption.
    + cbn in *.
      destruct vaddr; try discriminate.
      cbn in *.
      pose proof Mem.load_store_other _ _ _ _ _ _ heq_storev_x_m' AST.Mint32 b (Ptrofs.unsigned i) as h.
      rewrite <- h.
      * assumption.
      * left.
        eapply h_eval_sp_lds with (n:=n).
        -- omega.
        -- assert (i = Ptrofs.zero). 
           { !!pose proof chain_aligned _ _ _ h_chain_m_lvl_sp lvl (le_n _) e g.
             red in h_aligned_g_m.
             !!assert (n <= lvl) by omega.
             specialize (h_aligned_g_m _ h_le_n_lvl0).
             decomp h_aligned_g_m.
             !! (subst_det_addrstack_zero;idtac).
             inversion heq_vptr_b_δ_zero.
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
  !!intros until ofs0.
  intros h_eval_sp_lds n.
  !induction n;!intros.
  - cbn in *.
    !!specialize chained_stack_struct_inv_sp_zero with (1:=h_chain_m_lvl_sp) as ?.
    decomp h_ex.
    subst.
    subst_det_addrstack_zero.
    apply cm_eval_addrstack_zero.
  - !!assert (n <= lvl)%nat by omega.
    specialize h_impl_forall_x with (1:=h_chain_m_lvl_sp) (2:=heq_storev_x_m') (3:=h_le_n_lvl).
    cbn -[Mem.storev] in *.
    !inversion h_CM_eval_expr_v.
    specialize (h_impl_forall_x _ h_CM_eval_expr_vaddr).
    econstructor.
    + eassumption.
    + cbn in *.
      destruct vaddr; try discriminate.
      cbn in *.
      pose proof Mem.load_store_other _ _ _ _ _ _ heq_storev_x_m' AST.Mint32 b (Ptrofs.unsigned i) as h.
      rewrite <- h.
      * assumption.
      * !destruct h_eval_sp_lds.
        -- right.
           assert (i = Ptrofs.zero).
           { !!specialize chained_stack_structure_le with (1:=h_chain_m_lvl_sp) (2:=h_le_n_lvl) as ?.
             !!specialize chain_structure_spec with (1:=h_chain_m_n_sp) (g:=g)(e:=e) as ?.
             decomp h_ex.
             !!specialize det_eval_expr with (1:=h_CM_eval_expr) (2:=h_impl_forall_x) as ?.
             !inversion heq_vptr_b0_zero.
             reflexivity. }
           subst.
           left.
           cbn.
           rewrite Ptrofs.unsigned_zero.
           omega.
        -- left.
           eapply h_forall_n with (n:=n).
           ++ omega.
           ++ assert (i = Ptrofs.zero). 
              { !!pose proof chain_aligned _ _ _ h_chain_m_lvl_sp lvl (le_n _) e g.
                red in h_aligned_g_m.
                !!assert (n <= lvl) by omega.
                specialize (h_aligned_g_m _ h_le_n_lvl0).
                decomp h_aligned_g_m.
                !! (subst_det_addrstack_zero;idtac).
                inversion heq_vptr_b_δ_zero.
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
           forall x _v _chk m' δ, Mem.storev _chk m (Values.Vptr sp0 _v) x = Some m' ->
                   (n <= lvl)%nat -> forall v,
                       Cminor.eval_expr g sp e m ((build_loads n δ)) v
                       -> Cminor.eval_expr g sp e m' ((build_loads n δ)) v.
Proof.
  !!intros until lvl.
  intros h_eval_sp_lds n.
  !intros.
  unfold build_loads in *.
  !invclear h_CM_eval_expr_v.
  econstructor;[ | |eassumption].
  - eapply storev_outside_struct_chain_preserves_chaining;eauto.
  - !inversion h_CM_eval_expr_v2.
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
           forall x _v _chk m' δ, Mem.storev _chk m (Values.Vptr sp0 _v) x = Some m' ->
                   (n <= lvl)%nat -> forall v,
                       Cminor.eval_expr g sp e m' ((build_loads n δ)) v
                       -> Cminor.eval_expr g sp e m ((build_loads n δ)) v.
Proof.
  !!intros until lvl.
  intros h_eval_sp_lds n.
  !intros.
  unfold build_loads in *.
  !invclear h_CM_eval_expr_v.
  econstructor;[ | |eassumption].
  - eapply storev_outside_struct_chain_preserves_chaining2;eauto.
  - !inversion h_CM_eval_expr_v2.
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
           forall x _v _chk _chk' m' δ, Mem.storev _chk m (Values.Vptr sp0 _v) x = Some m' ->
                   (n <= lvl)%nat -> forall v,
                       Cminor.eval_expr g sp e m (Eload _chk' (build_loads n δ)) v
                       -> Cminor.eval_expr g sp e m' (Eload _chk' (build_loads n δ)) v.
Proof.
  !!intros.
  rename h_forall_n into h_unch.
  !inversion h_CM_eval_expr_v.
  assert (h_unch':forall n : nat,
             (n < lvl)%nat
             -> forall b' : Values.block,
               Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) (Values.Vptr b' Ptrofs.zero) -> b' <> sp0).
  { intros.
    eapply h_unch with (n:=n0).
    - omega.
    - assumption. }
  !!pose proof storev_outside_struct_chain_preserves_var_addresses _ _ _ _ _ _ h_unch' _ h_chain_m_lvl_sp _ _ _ _ _ heq_storev_x_m' h_le_n_lvl _ h_CM_eval_expr_vaddr.
  econstructor;eauto.
  unfold build_loads in h_CM_eval_expr_vaddr, h_CM_eval_expr_vaddr0.
  !invclear h_CM_eval_expr_vaddr.
  !invclear h_CM_eval_expr_vaddr0.
  destruct vaddr;try discriminate.
  pose proof Mem.load_store_other _ _ _ _ _ _ heq_storev_x_m' _chk' b (Ptrofs.unsigned i) as h.
  unfold Mem.loadv in *.
  rewrite h.
  - assumption.
  - left.
    !assert (v1=(Values.Vptr b Ptrofs.zero)).
    { clear h. 
      !!pose proof chain_aligned _ _ _ h_chain_m_lvl_sp lvl (le_n _) e g.
      red in h_aligned_g_m.
      !!assert (n <= lvl) by omega.
      specialize (h_aligned_g_m _ h_le_n_lvl0).
      decomp h_aligned_g_m.
      subst_det_addrstack_zero.
      f_equal.
      cbn in *.
      destruct v2;try discriminate.
      inversion h_eval_binop_Oadd_v1_v2.
      destruct Archi.ptr64;auto. }
    subst.
    eapply h_unch;eauto.
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
  !intros.
  assert
    ( forall n, (n <= lvl)%nat -> forall v : Values.val,
          Cminor.eval_expr g sp e m (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v
          -> Cminor.eval_expr g sp e m' (build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n) v).
  { !intro.
    eapply storev_outside_struct_chain_preserves_chaining;eauto. }
  destruct (chained_stack_struct_inv_sp_zero _ _ _ h_chain_m_lvl_sp).
  subst.
  eapply chained_stack_structure_spec.
  !intros.
  !!pose proof chain_structure_spec lvl0 m (Values.Vptr x0 Ptrofs.zero).
  !!edestruct h_impl_forall_g with (g:=g) (e:=e).
  eapply chained_stack_structure_le;eauto;try omega.
  eauto.
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
  !intros.
  assert (Cminor.eval_expr g sp e m
                           ((build_loads_ (Econst (Oaddrstack Ptrofs.zero)) n)) (Values.Vptr b' Ptrofs.zero)).
  { eapply malloc_preserves_chaining_loads_2;eauto.
    eapply chained_stack_structure_le;eauto;try omega. }
  eapply malloc_distinct_from_chaining_loads; eauto.
Qed.

