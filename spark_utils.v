Require Import eval.
Import STACK.
Require Import store_util.
Require Import LibHyps.LibHyps.

Local Open Scope autonaming_scope.

Ltac rename_hyp_spark n th :=
  match th with
  | in_bound _ _ _ => name(`_inbound`)
  | updates ?sto ?x _  => name(`_updates` ++ sto#n ++ x#n)
  | update ?frm ?x _ => name(`_update` ++ frm#n ++ x#n)
  | updateG ?stk ?x _ => name(`_updateG` ++ stk#n ++ x#n)
  | NoDup_G ?x => name(`_nodup_G` ++ x#n)
  | NoDup ?x => name(`_nodup` ++ x#n)
  | fetchG ?x ?stk => name(`_SfetchG` ++ x#n ++ stk#n)
  | fetch ?x ?frm => name(`_fetch` ++ x#n ++ frm#n)
  | fetches ?x ?sto => name(`_fetches` ++ x#n ++ sto#n)
  | cut_until ?st ?s ?fr ?paramsprf ?args (RTE ?er) => name(`_cut_until_RE`)
  | cut_until ?st ?s ?fr ?paramsprf ?args ?fr' => name(`_cut_until` ++ fr#n ++ fr'#n)
  | exact_levelG ?CE => name(`_exct_lvl` ++ CE#n)
  | non_empty_intersection_list ?l1 ?l2 => name(`_nonempty_inters` ++ l1#n ++ l2#n)
  | non_empty_intersection_frame ?l1 ?l2 => name(`_nonempty_inters_fr` ++ l1#n ++ l2#n)
  | Int ?c => name (c#(S n))
  | Bool ?b => name (b#(S n))
  end.

