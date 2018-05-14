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
