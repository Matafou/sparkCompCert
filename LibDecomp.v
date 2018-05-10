(** ** Specific redefinition of usual tactics. *)

(** Note that for example !!induction h doesn not work because
    "destruct" is not a ltac function by itself, it is already a
    notation. Hence the special definitions below for this kind of
    tactics: induction ddestruct inversion etc. *)

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

(* decompose and ex and or at once. TODO: generalize. *)
(* clear may fail if h is not a hypname *)
(* Tactic Notation "decomp" hyp(h) :=
   (!! (idtac;decomp_logicals h)). *) (* Why do I need this idtac? Without it no rename happens. *)

Ltac decompose_clear c :=
  let h := fresh "h_decomp" in
  pose proof c as h;
  decomp_logicals c; try clear h.
(*
Lemma foo : forall x, { aa:nat | (aa = x /\ x=aa) & (aa = aa /\ aa= x) } -> False.
Proof.
  intros x H. 
  decomp H.
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
