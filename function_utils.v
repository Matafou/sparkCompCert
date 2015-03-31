
Require Import semantics LibHypsNaming.

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


Require Import Errors.
Require Import Cminor.
Require Import spark2Cminor.

(* Definition foo := Eval cbv beta delta [bind transl_expr] in transl_expr. *)
Function transl_expr (stbl : symboltable) (CE : compilenv) 
                (e : expression) {struct e} : res expr :=
  match e with
  | E_Literal _ lit => OK (Econst (transl_literal lit))
  | E_Name _ (E_Identifier astnum1 id) =>
      match transl_variable stbl CE astnum1 id with
      | OK x =>
          match fetch_exp_type astnum1 stbl with
          | Some typ => value_at_addr stbl typ x
          | None =>
              Error
                [MSG "transl_expr unknown type at astnum: ";
                CTX (Pos.of_nat astnum1)]
          end
      | Error msg => Error msg
      end
  | E_Name _ (E_Indexed_Component _ _ _) =>
      Error (msg "transl_expr: Array not yet implemented")
  | E_Name _ (E_Selected_Component _ _ _) =>
      Error (msg "transl_expr: record not yet implemented")
  | E_Binary_Operation _ op e1 e2 =>
      match transl_expr stbl CE e1 with
      | OK x =>
          match transl_expr stbl CE e2 with
          | OK x0 => OK (Ebinop (transl_binop op) x x0)
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | E_Unary_Operation _ (Unary_Plus as op) e0 =>
      match transl_expr stbl CE e0 with
      | OK x =>
          match transl_unop op with
          | OK x0 => OK (Eunop x0 x)
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | E_Unary_Operation _ (Unary_Minus as op) e0 =>
      match transl_expr stbl CE e0 with
      | OK x =>
          match transl_unop op with
          | OK x0 => OK (Eunop x0 x)
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | E_Unary_Operation _ Not e0 =>
      match transl_expr stbl CE e0 with
      | OK x =>
          OK
            (Ebinop (Ocmp Integers.Ceq) x
               (Econst (Ointconst Integers.Int.zero)))
      | Error msg => Error msg
      end
  end.


Lemma transl_expr_ok : forall x y z, transl_expr x y z = spark2Cminor.transl_expr x y z.
Proof.
  reflexivity.
Qed.




(* Definition transl_stmt := Eval cbv beta delta [bind bind2 transl_stmt] in transl_stmt. *)


Function transl_stmt (stbl : Symbol_Table_Module.symboltable) 
                (CE : compilenv) (e : statement) {struct e} : 
res stmt :=
  match e with
  | S_Null => OK Sskip
  | S_Assignment _ nme e0 =>
      match spark2Cminor.transl_expr stbl CE e0 with
      | OK x =>
          match transl_name stbl CE nme with
          | OK x0 =>
              match compute_chnk stbl nme with
              | OK x1 => OK (Sstore x1 x0 x)
              | Error msg => Error msg
              end
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | S_If _ e0 s1 s2 =>
      match spark2Cminor.transl_expr stbl CE e0 with
      | OK x =>
          match
            OK
              (Ebinop (Ocmp Integers.Cne) x
                 (Econst (Ointconst Integers.Int.zero)))
          with
          | OK x0 =>
              match transl_stmt stbl CE s1 with
              | OK x1 =>
                  match transl_stmt stbl CE s2 with
                  | OK x2 => OK (Sifthenelse x0 x1 x2)
                  | Error msg => Error msg
                  end
              | Error msg => Error msg
              end
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | S_While_Loop _ _ _ => Error (msg "transl_stmt:Not yet implemented")
  | S_Procedure_Call _ _ pnum lexp =>
      match transl_params stbl pnum CE lexp with
      | OK x =>
          match transl_procsig stbl pnum with
          | OK (x0, y) =>
              let current_lvl := (Datatypes.length CE - 1)%nat in
              let x1 := build_loads_ (current_lvl - y) in
                  match OK (x1 :: x) with
                  | OK x2 =>
                      OK
                        (Scall None x0
                           (Econst
                              (Oaddrsymbol (transl_procid pnum)
                                 (Integers.Int.repr 0))) x2)
                  | Error msg => Error msg
                  end
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | S_Sequence _ s1 s2 =>
      match transl_stmt stbl CE s1 with
      | OK x =>
          match transl_stmt stbl CE s2 with
          | OK x0 => OK (Sseq x x0)
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  end.




Lemma transl_stmt_ok : forall x y z, transl_stmt x y z = spark2Cminor.transl_stmt x y z.
Proof.
  reflexivity.
Qed.

(* Definition transl_basetype := Eval lazy beta delta [transl_basetype bind] in spark2Cminor.transl_basetype. *)
Function transl_basetype (stbl : Symbol_Table_Module.symboltable) 
         (ty : base_type) {struct ty} :
  res Ctypes.type :=
  match ty with
  | BBoolean => OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr)
  | BInteger _ => OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr)
  | BArray_Type tpcell (Range min max) =>
      match transl_basetype stbl tpcell with
      | OK x => OK (Ctypes.Tarray x (max - min) Ctypes.noattr)
      | Error msg => Error msg
      end
  | BRecord_Type _ => Error (msg "transl_basetype: Not yet implemented!!.")
  end.

Lemma transl_basetype_ok : forall x y, transl_basetype x y = spark2Cminor.transl_basetype x y.
Proof.
  reflexivity.
Qed.



(* Definition transl_typenum := Eval lazy beta delta [transl_typenum bind] in spark2Cminor.transl_typenum. *)
Function transl_typenum (stbl : Symbol_Table_Module.symboltable) 
                   (id : typenum) {struct stbl} : res Ctypes.type :=
  match Symbol_Table_Module.fetch_type id stbl with
  | Some t =>
      match type_of_decl t with
      | OK x =>
          match reduce_type stbl x max_recursivity with
          | OK x0 => transl_basetype stbl x0
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | None => Error (msg "transl_typenum: no such type")
  end.

Lemma transl_typenum_ok : forall x y, transl_typenum x y = spark2Cminor.transl_typenum x y.
Proof.
  reflexivity.
Qed.

(* Definition transl_type := Eval lazy iota beta delta [spark2Cminor.transl_type spark2Cminor.transl_basetype bind] in spark2Cminor.transl_type. *)

Function transl_type (stbl : Symbol_Table_Module.symboltable) (t : type) :=
  match t with
  | Boolean => OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr)
  | Integer => OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr)
  | Subtype _ => Error (msg "transl_type: type not treated yet")
  | Derived_Type _ => Error (msg "transl_type: type not treated yet")
  | Integer_Type _ => Error (msg "transl_type: type not treated yet")
  | Array_Type _ => Error (msg "transl_type: type not treated yet")
  | Record_Type _ => Error (msg "transl_type: type not treated yet")
  end.


Lemma transl_type_ok : forall x y, transl_type x y = spark2Cminor.transl_type x y.
Proof.
  reflexivity.
Qed.



(* Definition foo:= Eval lazy beta delta [Memory.Mem.storev] in Memory.Mem.storev. *)
Function cm_storev (chunk : AST.memory_chunk) (m : Memory.Mem.mem) (addr v : Values.val):=
match addr with
| Values.Vundef => None
| Values.Vint _ => None
| Values.Vlong _ => None
| Values.Vfloat _ => None
| Values.Vsingle _ => None
| Values.Vptr b ofs =>
    Memory.Mem.store chunk m b (Integers.Int.unsigned ofs) v
end.

Lemma cm_storev_ok : forall x y, cm_storev x y = Memory.Mem.storev x y.
Proof.
  reflexivity.
Qed.



(* Definition foo_compute_chk:= Eval lazy beta iota delta [compute_chnk compute_chnk_id compute_chnk_astnum compute_chnk_of_type bind] in compute_chnk. *)
Function compute_chnk (stbl' : symboltable) (nme : name) :=
match nme with
| E_Identifier astnum0 _ =>
    match fetch_exp_type astnum0 stbl' with
    | Some typ =>
        match reduce_type stbl' typ max_recursivity with
        | OK BBoolean => OK AST.Mint32
        | OK (BInteger _) => OK AST.Mint32
        | OK (BArray_Type _ _) => Error (msg "compute_chnk_of_type: Arrays types not yet implemented!!.")
        | OK (BRecord_Type _) => Error (msg "compute_chnk_of_type: Records types not yet implemented!!.")
        | Error x => Error x
        end
    | None =>
        Error [MSG "compute_chnk_astnum: unkniwn type on astnum: ";
          CTX (Pos.of_nat astnum0)] end
| E_Indexed_Component _ _ _ => Error (msg "compute_chnk: arrays not implemented yet")
| E_Selected_Component _ _ _ => Error (msg "compute_chnk: records not implemented yet")
end.
(*
Function compute_chnk (stbl' : symboltable) (nme : name) :=
match nme with
| E_Identifier _ idnt =>
    match fetch_var_type idnt stbl' with
    | OK x =>
        match reduce_type stbl' x max_recursivity with
        | OK BBoolean => OK AST.Mint32
        | OK (BInteger _) => OK AST.Mint32
        | OK (BArray_Type _ _) => Error (msg "compute_chnk_of_type: Arrays types not yet implemented!!.")
        | OK (BRecord_Type _) => Error (msg "compute_chnk_of_type: Records types not yet implemented!!.")
        | Error x0 => Error x0
        end
    | Error msge => Error msge
    end
| E_Indexed_Component _ _ _ => Error (msg "compute_chnk: arrays not implemented yet")
| E_Selected_Component _ _ _ => Error (msg "compute_chnk: records not implemented yet")
end.
*)
Lemma compute_chnk_ok : forall x y, spark2Cminor.compute_chnk x y = compute_chnk x y.
Proof.
  reflexivity.
Qed.
