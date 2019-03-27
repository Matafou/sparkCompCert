(** ** A specific variant of decompose. Which only decomposes logical connectives. does *)

Ltac decomp_logicals h :=
  match type of h with
  | @ex _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_logicals h1
  | @sig _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_logicals h1
  | @sig2 _ (fun x => _) (fun _ => _) => let x' := fresh x in
                                         let h1 := fresh in
                                         let h2 := fresh in
                                         destruct h as [x' h1 h2];
                                         decomp_logicals h1;
                                         decomp_logicals h2
  | @sigT _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_logicals h1
  | @sigT2 _ (fun x => _) (fun _ => _) => let x' := fresh x in
                                          let h1 := fresh in
                                          let h2 := fresh in
                                          destruct h as [x' h1 h2]; decomp_logicals h1; decomp_logicals h2
  | and _ _ => let h1 := fresh in let h2 := fresh in destruct h as [h1 h2]; decomp_logicals h1; decomp_logicals h2
  | or _ _ => let h' := fresh in destruct h as [h' | h']; [decomp_logicals h' | decomp_logicals h' ]
  | _ => idtac
  end.

(*
Lemma foo : forall x, { aa:nat | (aa = x /\ x=aa) & (aa = aa /\ aa= x) } -> False.
Proof.
  intros x h.
  pose proof h as h'.
Abort.

Lemma foo : { aa:False & True  } -> False.
Proof.
  intros H.
  decomp H.
Abort.


Lemma foo : { aa:False & True & False  } -> False.
Proof.
  intros H.
  decomp H.
Abort.
*)

(* proveprem H at i as h. Create an assert for the ith dependent
premiss of hypothesis H and specialize H with the resulting proof. h
is the (optional) name of the asserted premiss. *)

Ltac proveprem_ H i id :=
  (* prefer this to evar, which is not well "typed" by Ltac (does not
  know that it creates an evar (coq bug?). *)
  let ev := open_constr:((_:Prop)) in
  assert (id:ev);
  [|specialize H with (i:=id)].

Tactic Notation "proveprem" hyp(H) "at" integer(i) "as" ident(id)  :=
  proveprem_ H i id.

Tactic Notation "proveprem" hyp(H) "at" integer(i) :=
  let id := fresh H "_prem" in
  proveprem_ H i id.

(*
Definition test n := n = 1.
Variable Q: nat -> bool -> list nat -> Prop.
Lemma foo:
  (forall n b l, b = true -> test n -> Q n b l) ->
  (true = true -> false = false ->  True) -> Q 1 true (cons 1 nil).
Proof.
  intros hyp hyp'.
  (* proveprem hyp at 2 as h. *)
  let ev := open_constr:((_:Prop)) in
  assert (id:ev).
  2:specialize hyp with (2:=id).
  { reflexivity. }
  Check h.
  proveprem hyp at 1.
  { reflexivity. }
  Check hyp_prem.
  apply hyp.
Qed.

*)