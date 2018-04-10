Require Import eval.
Import STACK.
Require Import store_util.

Ltac rename_hyp1 h th :=
  match th with
  | in_bound _ _ _ => fresh "inbound"
  | updates ?sto ?x _ = _ => fresh "eq_updates_" sto "_" x
  | updates ?sto ?x _ = _ => fresh "eq_updates_" sto
  | updates ?sto ?x _ = _ => fresh "eq_updates_" x
  | updates ?sto ?x _ = _ => fresh "eq_updates"
  | update ?frm ?x _ = _ => fresh "eq_update_" frm "_" x
  | update ?frm ?x _ = _ => fresh "eq_update_" frm
  | update ?frm ?x _ = _ => fresh "eq_update_" x
  | update ?frm ?x _ = _ => fresh "eq_update"
  | updateG ?stk ?x _ = _ => fresh "eq_updateG_" stk "_" x
  | updateG ?stk ?x _ = _ => fresh "eq_updateG_" stk
  | updateG ?stk ?x _ = _ => fresh "eq_updateG_" x
  | updateG ?stk ?x _ = _ => fresh "eq_updateG"
  | fetchG ?x ?stk = _ => fresh "eq_SfetchG_" x "_" stk
  | fetchG ?x ?stk = _ => fresh "eq_SfetchG_" stk
  | fetchG ?x ?stk = _ => fresh "eq_SfetchG_" x
  | fetchG ?x ?stk = _ => fresh "eq_SfetchG"
  | fetch ?x ?frm = _ => fresh "eq_fetch_" x "_" frm
  | fetch ?x ?frm = _ => fresh "eq_fetch_" frm
  | fetch ?x ?frm = _ => fresh "eq_fetch_" x
  | fetch ?x ?frm = _ => fresh "eq_fetch"
  | fetches ?x ?sto = _ => fresh "eq_fetches_" x "_" sto
  | fetches ?x ?sto = _ => fresh "eq_fetches_" sto
  | fetches ?x ?sto = _ => fresh "eq_fetches_" x
  | fetches ?x ?sto = _ => fresh "eq_fetches"
  | cut_until ?st ?s ?fr ?paramsprf ?args (RTE ?er) => fresh "cut_until_RE"
  | cut_until ?st ?s ?fr ?paramsprf ?args (OK ?fr') => fresh "cut_until_" fr "_" fr'
  | cut_until ?st ?s ?fr ?paramsprf ?args ?fr' => fresh "cut_until_" fr "_" fr'
  | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "cut_until_" fr
  | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "cut_until"
  | exact_levelG ?CE => fresh "exct_lvl_" CE
  | exact_levelG ?CE => fresh "exct_lvl"
  end.
