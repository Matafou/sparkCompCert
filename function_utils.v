
Require Import semantics.

Open Scope Z_scope.

(* *** Hack to workaround a current limitation of Functional Scheme wrt to Function. *)
(*
This should work, but Funcitonal SCheme does not generate the
inversion stuff currently. So we defined by hand the expanded versions
binopexp and unopexp with Function.

Definition binopexp :=
  Eval unfold
       Math.binary_operation
  , Math.and
  , Math.or
  , Math.eq
  , Math.ne
  , Math.lt
  , Math.le
  , Math.gt
  , Math.ge
  , Math.add
  , Math.sub
  , Math.mul
  , Math.div
  in Math.binary_operation.

Definition unopexp :=
  Eval unfold
       Math.unary_operation, Math.unary_plus, Math.unary_minus, Math.unary_not in Math.unary_operation.

Functional Scheme binopnind := Induction for binopexp Sort Prop.
Functional Scheme unopnind := Induction for unopexp Sort Prop.
*)


(* *** And of the hack *)

Function unopexp (op : unary_operator) (v : value) :=
  match op with
    | Unary_Plus =>
      match v with
        | Undefined => None
        | Int _ => Some v
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Unary_Minus =>
      match v with
        | Undefined => None
        | Int v' => Some (Int (- v'))
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Not =>
      match v with
        | Undefined => None
        | Int _ => None
        | Bool v' => Some (Bool (negb v'))
        | ArrayV _ => None
        | RecordV _ => None
      end
  end.

Function binopexp (op : binary_operator) (v1 v2 : value) :=
  match op with
    | And =>
      match v1 with
        | Undefined => None
        | Int _ => None
        | Bool v1' =>
          match v2 with
            | Undefined => None
            | Int _ => None
            | Bool v2' => Some (Bool (v1' && v2'))
            | ArrayV _ => None
            | RecordV _ => None
          end
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Or =>
      match v1 with
        | Undefined => None
        | Int _ => None
        | Bool v1' =>
          match v2 with
            | Undefined => None
            | Int _ => None
            | Bool v2' => Some (Bool (v1' || v2'))
            | ArrayV _ => None
            | RecordV _ => None
          end
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Equal =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (Zeq_bool v1' v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Not_Equal =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (Zneq_bool v1' v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Less_Than =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (v1' <? v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Less_Than_Or_Equal =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (v1' <=? v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Greater_Than =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (v1' >? v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Greater_Than_Or_Equal =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Bool (v1' >=? v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Plus =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Int (v1' + v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Minus =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Int (v1' - v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Multiply =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Int (v1' * v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
    | Divide =>
      match v1 with
        | Undefined => None
        | Int v1' =>
          match v2 with
            | Undefined => None
            | Int v2' => Some (Int (v1' ÷ v2'))
            | Bool _ => None
            | ArrayV _ => None
            | RecordV _ => None
          end
        | Bool _ => None
        | ArrayV _ => None
        | RecordV _ => None
      end
  end.

Lemma binopexp_ok: forall x y z, Math.binary_operation x y z = binopexp x y z .
Proof.
  reflexivity.
Qed.

Lemma unopexp_ok: forall x y, Math.unary_operation x y = unopexp x y.
Proof.
  reflexivity.
Qed.
