Require Import sparkfrontend.compcert_utils  compcert.backend.Cminor compcert.lib.Integers.

Notation "[ '**' '|_|' N '+' X ]" := (build_loads_ X N) (at level 0).
Notation "[| OFS |]" := (Econst (Oaddrstack OFS)) (at level 0).
Notation "  '*' b '+' n" := (Values.Vptr b n) (at level 10).
Notation "'00'" := (Ptrofs.zero).
