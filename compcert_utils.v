Require Import List LibHyps.LibHyps.
From sparkfrontend Require Import more_stdlib.
From compcert Require Import Memory .
From compcert Require Import Ctypes.
Require Import ZArith Memory Cminor Integers Errors.
Open Scope Z_scope.
Require Import Lia.

Import ListNotations.

Axiom det_eval_expr: forall g stkptr locenv m e v v',
    Cminor.eval_expr g stkptr locenv m e v
    -> Cminor.eval_expr g stkptr locenv m e v'
    -> v = v'.

(** [build_loads_ m] returns the expression denoting the mth
    indirection of the variable of offset Zero (i.e. the pointer to
    enclosing procedure). This is the way we access to enclosing
    procedure frame. The type of all Load is ( void * ). *)
Function build_loads_ base (m:nat) {struct m} : Cminor.expr :=
  match m with
    | O => base
    | S m' => let subloads := build_loads_ base m' in
              Eload AST.Mint32 subloads
  end.

(** [build_loads m n] is the expression denoting the address
    of the variable at offset [n] in the enclosing frame [m] levels
    above the current frame. This is done by following pointers from
    frames to frames. (Load^m 0)+n. *)
Definition build_loads (m:nat) (n:Z) :=
  let indirections := build_loads_ (Econst (Oaddrstack Ptrofs.zero)) m in
  Ebinop Oadd indirections (Econst (Ointconst (Integers.Int.repr n))).

(* no permission mean free. *)
Definition is_free_block := fun m sp_id ofs_id => forall perm, ~ Mem.perm m sp_id ofs_id Cur perm.

Delimit Scope autonaming_scope with autonaming.
Local Open Scope autonaming_scope.
Ltac rename_depth ::= constr:(4%nat).
Local Open Scope list.
Ltac rename_hyp1 n th :=
  match th with
  | OK ?x => name (x#(S n))
  | Error ?msg => name (`_Err`)
  | Integers.Int.min_signed => name (`_SMIN`)
  | Integers.Int.max_signed => name (`_SMAX`)
    (* | (?min <= ?x) /\ (?x < ?max) => name (x#n ++ `_bounded_` ++ min#n ++ `_` ++ max#n) *)
  | ((?min <= ?x) /\ (?x <= ?max)) => name (x#n ++ `_bounded` ++ min#(decr n) ++ max#(decr n))
  | build_loads ?k ?z => name (`_bldlds` ++ k#n ++ z#n)
  | build_loads_ ?k ?z => name (`_bldlds` ++ k#n ++ z#n)
  | Cminor.eval_expr _ _ _ _ ?x ?y => name (`_CM_eval_expr` ++ x#n ++ y#n)
  | Cminor.eval_exprlist _ _ _ _ ?x ?y => name (`_CM_eval_exprl` ++ x#n ++ y#n)
  | Cminor.exec_stmt _ _ _ _ _ ?stmt _ _ _ ?res => name (`_exec_stmt` ++ stmt#n ++ res#n)
  | Mem.valid_access _ _ ?b _ _ => name (`_valid_access` ++ b#n)
  | Cminor.eval_constant _ ?c ?v  => name (`_evalcst` ++ c#n ++ v#n)
  | Cminor.eval_funcall _ _ _ ?vargs _ _ ?vres => name (`_evalfuncall` ++ proc_value#n ++ vargs#n ++ vres#n)

  | Cminor.eval_funcall ?g ?m ?proc_value ?vargs ?t ?m' ?vres => name (`evalfuncall_` ++ proc_value ++ `_` ++ vargs)
  | Values.Vptr ?b ?v => name (`_vptr` ++ b#n ++ v#n)
  | Mem.store ?chk ?m ?blk ?addr ?v => name (`_store` ++ addr#n ++ v#n)
  | Mem.storev ?chk ?m ?vaddr ?v => name (`_storev` ++ vaddr#n ++ v#n)
  | Mem.valid_block ?m ?sp => name (`_valid_blck` ++ m#n ++ sp#n)
  | Mem.alloc ?m ?ofs ?sz = (?m', ?sp) => name (`_malloc` ++ m#n ++ m'#n)
  | Mem.alloc ?m ?ofs ?sz => name (`_malloc` ++ m#n)
  | Mem.unchanged_on ?prd ?m ?m' => name (`_unchanged_on` ++ prd#n ++ m#n ++ m'#n)
  | outcome_result_value ?out ?typ ?res => name (`_outc_resval` ++ out#n ++ res#n)
  | outcome_free_mem ?out ?m1 _ _ ?m2 => name(`_outc_freemem` ++ out#n ++ m1#n ++ m2#n)
  | eval_binop ?op ?v1 ?v2 ?m => name (`_evop` ++ op#(S n) ++ v1#n ++ v2#n) (* hide binop+op = evop_op *)
  | (?min <= ?x) /\ (?x < ?max) => name (x#n ++ `_bounded`)
  | (?min <= ?x) /\ (?x <= ?max) => name (x#n ++ `_bounded`)
  | (?min <= ?x) /\ (?x < ?max) => name (`_bounded`)
  | (?min <= ?x) /\ (?x <= ?max) => name (`_bounded`)
  | Values.Val.add ?v1 ?v2 => name (`_val_add` ++ v1#n ++ v2#n)
  | Values.Val.offset_ptr ?v1 ?v2 => name (`_val_offs` ++ v1#n ++ v2#n)
  | Mem.loadv ?chk ?m ?vaddr => name (`_loadv` ++ vaddr#n)
  | Globalenvs.Genv.find_funct ?g ?paddr => name (`_find_func` ++ paddr#n)
  | Maps.PTree.get ?k ?m => name (`_mget` ++ k#n ++ m#n)
  | is_free_block ?m ?sp ?ofs => name (`_free_blck` ++ m#n ++ sp#n ++ ofs#n)
  | Ctypes.access_mode ?x => name (`_access_mode` ++ x#n)
  | Mem.valid_access ?m ?chk ?b ?ofs ?perm => name (`_valid_access` ++ b#n)
  end.
Local Close Scope autonaming_scope.

(* This adhoc exceptions to the usual prefix heq_ which is replaced by
h_. TODO: go back to regular prefixing. *)
(*Ltac prefixable_compcert h th :=
  match th with
  | Ctypes.access_mode _ = _ => HypH_
  | Mem.alloc _ _ _ = _ => HypH_
  | Mem.loadv _ _ _ = _ => HypH_
  | Values.Val.offset_ptr _ _ = _ => HypH_
  | Values.Val.add _ _ = _ => HypH_
  | eval_binop _ _ _ _ = _ => HypH_
  | outcome_free_mem _ _ _ = _ => HypH_
  | Mem.unchanged_on _ _ _ = _ => HypH_
  | Cminor.eval_constant _ _ _ = _ => HypH_
  end.
*)

Ltac rename_hyp2 n th :=
  match th with
    | _ => rename_hyp1 n th
(*    | _ => (more_stdlib.rename_hyp1 n th)
    | _ => (rename_hyp_neg n th) *)
  end.

Local Ltac rename_hyp ::= rename_hyp2.

(* Sometme inversion unfolds to much things under OK (like Int.repr for instance).
   Then this lemma is useful. *)
Lemma OK_inv: forall A (x y:A), OK x = OK y -> x = y.
Proof.

  intros A x y H.
  inversion H.
  reflexivity.
Qed.

Ltac rename_depth ::= constr:(2%nat).


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
  intros /sng.
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
  eapply Mem.unchanged_on_implies;eauto.
Qed.



Lemma map_get_set_same_nodup :
  forall l m k v,
    (forall i, List.In i l -> i <> k) ->
    Maps.PTree.get k (set_locals l (Maps.PTree.set k v m)) = Some v.
Proof.
  induction l;cbn;intros /sng.
  - apply Maps.PTree.gss.
  - rename h_all_neq_ into h_diff.
    rewrite Maps.PTree.gso.
    + eapply h_all_eq_.
      intros /sng.
      apply h_diff.
      right;assumption.
    + apply not_eq_sym.
      eapply h_diff.
      left.
      reflexivity.
Qed.


Lemma map_get_set_locals_diff: forall decl  x env,
    ~List.In x decl ->
    Maps.PTree.get x (set_locals decl env) =
    Maps.PTree.get x env.
Proof.
  intro /sng.
  induction decl;intros;cbn /sng.
  - reflexivity.
  - rewrite Maps.PTree.gso.
    + eapply h_all_eq_.
      intro abs.
      apply h_not_In_.
      constructor 2.
      assumption.
    + intro abs.
      apply h_not_In_.
      subst.
      constructor 1.
      reflexivity.
Qed.


Lemma build_loads_compos : forall i x j,
    build_loads_ x (i+j)%nat = build_loads_ (build_loads_ x j) i.
Proof.
  induction i;intros /sng.
  - cbn in *.
    reflexivity.
  - cbn in *.
    erewrite h_all_eq_.
   reflexivity.
Qed.

Lemma build_loads_compos_comm : forall i x j,
    build_loads_ x (i+j)%nat = build_loads_ (build_loads_ x i) j.
Proof.
  intros /sng.
  rewrite Nat.add_comm.
  apply build_loads_compos.
Qed.

Ltac rename_depth ::= constr:(2%nat).

Lemma occur_build_loads: forall x n, x = build_loads_ x n -> n = 0%nat.
Proof.
  induction x;cbn;(intros/sng); try now (destruct n;cbn in *; auto) /sng.
  apply IHx.
  destruct n.
  + reflexivity.
  + cbn in *.
    inversion h_eq_Eload_bldlds_ /n.
    rewrite <- h_eq_x_bldlds_ at 2.
    pose proof (build_loads_compos_comm 1 x n).
    cbn in *.
    now symmetry.
Qed.

Lemma build_loads__inj : forall x i₁ i₂,
    (* translating the variabe to a Cminor load address *)
    build_loads_ x i₁ = build_loads_ x i₂ ->
    i₁ = i₂.
Proof.
  intros x i₁.
  induction i₁;intros /sng.
  - cbn in *.
    destruct i₂;auto.
    apply occur_build_loads in h_eq_bldlds_bldlds_.
    exfalso;lia.
  - destruct i₂.
    + unfold build_loads_ in h_eq_bldlds_bldlds_ at 2.
      eapply occur_build_loads;eauto.
    + cbn in *.
      inversion h_eq_bldlds_bldlds_ /n.
      f_equal.
      eapply h_all_eq_;auto.
Qed.

Lemma build_loads__inj_neq : forall x i₁ i₂,
    i₁ <> i₂ ->
    forall e₁ e₂ ,
      (* translating the variabe to a Cminor load address *)
      build_loads_ x i₁ = e₁ ->
      (* translating the variabe to a Cminor load address *)
      build_loads_ x i₂ = e₂ ->
      e₁ <> e₂.
Proof.
  intros /sng.
  intro abs.
  subst.
  eapply build_loads__inj in abs.
  contradiction.
Qed.

Lemma build_loads_inj : forall i₁ i₂ k k' ,
    (* translating the variabe to a Cminor load address *)
    build_loads k i₁ = build_loads k' i₂ ->
    k = k' /\ Integers.Int.Z_mod_modulus i₁ = Integers.Int.Z_mod_modulus i₂.
Proof.
  unfold build_loads.
  intros /sng.
  inversion h_eq_Ebinop_Ebinop_.
  split.
  - eapply build_loads__inj;eauto.
  - auto. 
Qed.

Lemma build_loads_inj_2 : forall i₁ i₂ k k' ,
    (* translating the variabe to a Cminor load address *)
    build_loads k i₁ = build_loads k' i₂ ->
    k = k' /\ Int.repr i₁ = Int.repr i₂.
Proof.
  unfold build_loads.
  intros /sng.
  remember (Int.repr i₁) as rpr1.
  remember (Int.repr i₂) as rpr2.
  inversion h_eq_Ebinop_Ebinop_.
  split.
  - eapply build_loads__inj;eauto.
  - auto.
Qed.

Lemma build_loads_inj_inv:
  forall (i₁ i₂ : Z) (k k' : nat),
    k = k'  ->
    Int.repr i₁ = Int.repr i₂ -> 
    build_loads k i₁ = build_loads k' i₂.
Proof.
  unfold build_loads.
  intros /sng.
  subst.
  rewrite h_eq_repr_repr_.
  reflexivity.
Qed.



Lemma build_loads_inj_neq1 : forall i₁ i₂ k k' e₁ e₂,
    k <> k' ->
    build_loads k i₁ = e₁ ->
    build_loads k' i₂ = e₂ ->
    e₁ <> e₂.
Proof.
  intros /sng.
  intro abs.
  subst.
  apply build_loads_inj in abs.
  destruct abs;contradiction.
Qed.

Lemma build_loads_inj_neq2 : forall i₁ i₂ k k' e₁ e₂,
    Integers.Int.Z_mod_modulus i₁ <> Integers.Int.Z_mod_modulus i₂ ->
    build_loads k i₁ = e₁ ->
    build_loads k' i₂ = e₂ ->
    e₁ <> e₂.
Proof.
  intros /sng.
  intro abs.
  subst.
  apply build_loads_inj in abs.
  destruct abs;contradiction.
Qed.

Lemma is_free_block_disj : forall m sp ofs sp',
    is_free_block m sp ofs ->
    ~ is_free_block m sp' ofs ->
    sp <> sp'
.
Proof.
  intros /sng.
  unfold is_free_block in *.
  intro abs.
  subst sp'.
  contradiction.
Qed.

