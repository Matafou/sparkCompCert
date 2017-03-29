
Require Import eval LibHypsNaming Memory.
Require Import Errors.
Require Import Cminor.
Require Import spark2Cminor.
Require Import compcert_utils.


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
| Modulus => Math.mod' v1 v2
end.

Lemma binopexp_ok: forall x y z, Math.binary_operation x y z = binopexp x y z .
Proof.
  reflexivity.
Qed.

Lemma unopexp_ok: forall x y, Math.unary_operation x y = unopexp x y.
Proof.
  reflexivity.
Qed.



(* Definition foo := Eval cbv beta delta [bind transl_expr] in transl_expr. *)

Function transl_expr
         (stbl : Symbol_Table_Module.symboltable) (CE : compilenv) 
         (e : exp) {struct e} : res expr :=
  match e with
  | Literal _ lit => OK (Econst (transl_literal lit))
  | Name _ (Identifier astnum1 id) =>
      match transl_variable stbl CE astnum1 id with
      | OK x =>
          match fetch_exp_type astnum1 stbl with
          | Some typ => value_at_addr stbl typ x
          | None =>
              Error
                [MSG "transl_expr unknown type at astnum: "; CTX (Pos.of_nat astnum1)]
          end
      | Error msg => Error msg
      end
  | Name _ (IndexedComponent _ _ _) =>
      Error (msg "transl_expr: Array not yet implemented")
  | Name _ (SelectedComponent _ _ _) =>
      Error (msg "transl_expr: record not yet implemented")
  | BinOp _ op e1 e2 =>
      match transl_expr stbl CE e1 with
      | OK x =>
          match transl_expr stbl CE e2 with
          | OK x0 => OK (Ebinop (transl_binop op) x x0)
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | UnOp _ (Unary_Minus as op) e0 =>
      match transl_expr stbl CE e0 with
      | OK x =>
          match transl_unop op with
          | OK x0 => OK (Eunop x0 x)
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | UnOp _ Not e0 =>
      match transl_expr stbl CE e0 with
      | OK x => OK (Ebinop (Ocmp Integers.Ceq) x (Econst (Ointconst Integers.Int.zero)))
      | Error msg => Error msg
      end
  end.

Lemma transl_expr_ok : forall x y z, transl_expr x y z = spark2Cminor.transl_expr x y z.
Proof.
  reflexivity.
Qed.




(* Definition transl_stmt := Eval cbv beta delta [bind bind2 transl_stmt] in transl_stmt. *)

Function transl_stmt (stbl : Symbol_Table_Module.symboltable) (CE : compilenv) 
            (e : ast.stmt) {struct e} : res stmt :=
  match e with
  | Null => OK Sskip
  | Assign _ nme e0 =>
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
  | If _ e0 s1 s2 =>
      match spark2Cminor.transl_expr stbl CE e0 with
      | OK x =>
          match transl_stmt stbl CE s1 with
          | OK x0 =>
              match transl_stmt stbl CE s2 with
              | OK x1 =>
                  OK
                    (Sifthenelse
                       (Ebinop (Ocmp Integers.Cne) x
                          (Econst (Ointconst Integers.Int.zero))) x0 x1)
              | Error msg => Error msg
              end
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | While _ _ _ => Error (msg "transl_stmt:Not yet implemented")
  | Call _ _ pnum lexp =>
      match transl_params stbl pnum CE lexp with
      | OK x =>
          match transl_procsig stbl pnum with
          | OK (x0, y) =>
              let current_lvl := Datatypes.length CE in
              let addr_enclosing_frame :=
                build_loads_ (Econst (Oaddrstack Integers.Int.zero)) (current_lvl - y)
                in
              OK
                (Scall None x0
                   (Econst (Oaddrsymbol (transl_procid pnum) (Integers.Int.repr 0)))
                   (addr_enclosing_frame :: x))
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  | Seq _ s1 s2 =>
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
Function transl_basetype (stbl : Symbol_Table_Module.symboltable) (ty : base_type) {struct ty} :
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
Function transl_typenum (stbl : Symbol_Table_Module.symboltable) (id : typenum) :=
match Symbol_Table_Module.fetch_type id stbl with
| Some t =>
    match type_of_decl t with
    | OK x =>
        match reduce_type stbl x max_recursivity with
        | OK x0 => spark2Cminor.transl_basetype stbl x0
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

(* Definition build_compilenv:= Eval lazy beta iota delta [build_compilenv bind bind2] in build_compilenv. *)
(* using the explicit version because of a bug in Function. *)

Function build_compilenv
         (stbl : Symbol_Table_Module.symboltable) (enclosingCE : compilenv)
         (_ : Symbol_Table_Module.level) (lparams : list paramSpec) 
         (decl : decl) :=
let stoszchainparam :=
    @pair (list (prod idnum OffsetEntry.T)) Z (@nil (prod idnum OffsetEntry.T))
          (Zpos (xO (xO xH))) in
match
  build_frame_lparams stbl stoszchainparam lparams
  return (res (prod (list (prod nat CompilEnv.store)) Z))
with
| OK x =>
  match
    build_frame_decl stbl x decl
    return (res (prod (list (prod nat CompilEnv.store)) Z))
  with
  | OK p =>
    match p return (res (prod (list (prod nat CompilEnv.store)) Z)) with
    | pair x0 y =>
      let scope_lvl := @Datatypes.length CompilEnv.frame enclosingCE in
      @OK (prod (list (prod nat CompilEnv.store)) Z)
          (@pair (list (prod nat CompilEnv.store)) Z
                 (@cons (prod nat CompilEnv.store)
                        (@pair nat CompilEnv.store scope_lvl x0) enclosingCE) y)
    end
  | Error msg => @Error (prod (list (prod nat CompilEnv.store)) Z) msg
  end
| Error msg => @Error (prod (list (prod nat CompilEnv.store)) Z) msg
end.


Lemma build_compilenv_ok : build_compilenv = spark2Cminor.build_compilenv.
Proof.
  reflexivity.
Qed.


(* Definition foo_compute_chk:= Eval lazy beta iota delta [compute_chnk compute_chnk_id compute_chnk_astnum compute_chnk_of_type bind] in compute_chnk. *)

Definition foo_compute_chk:= Eval lazy beta iota delta [compute_chnk compute_chnk_id compute_chnk_astnum compute_chnk_of_type bind] in compute_chnk.

Function compute_chnk (stbl : Symbol_Table_Module.symboltable) (nme : name) :=
match nme with
| Identifier _ id =>
  match fetch_var_type id stbl with
  | OK x =>
    match reduce_type stbl x max_recursivity with
    | OK BBoolean => OK AST.Mint32
    | OK (BInteger _) => OK AST.Mint32
    | OK (BArray_Type _ _) =>
      Error (msg "compute_chnk_of_type: Arrays types not yet implemented!!.")
    | OK (BRecord_Type _) =>
      Error (msg "compute_chnk_of_type: Records types not yet implemented!!.")
    | Error x0 => Error x0
    end
  | Error msg => Error msg
  end
| IndexedComponent _ _ _ => Error (msg "compute_chnk: arrays not implemented yet")
| SelectedComponent _ _ _ => Error (msg "compute_chnk: records not implemented yet")
end.

Lemma compute_chnk_ok : forall x y, spark2Cminor.compute_chnk x y = compute_chnk x y.
Proof.
  reflexivity.
Qed.


(* Definition add_to_frame:= Eval lazy beta iota delta [add_to_frame bind] in add_to_frame. *)

Function add_to_frame (stbl : Symbol_Table_Module.symboltable) (cenv_sz : localframe * Z) (nme : idnum) (subtyp_mrk : type) :=
  let (cenv, sz) := cenv_sz in
  match compute_size stbl subtyp_mrk with
  | OK x =>
    let new_size := sz + x in
    if new_size >=? Integers.Int.modulus
    then Error (msg "add_to_frame: memory would overflow")
    else let new_cenv := (nme, sz) :: cenv in OK (new_cenv, new_size)
  | Error msg => Error msg
  end.

Lemma add_to_frame_ok : spark2Cminor.add_to_frame = add_to_frame.
Proof.
  reflexivity.
Qed.


(* Definition compute_size:= Eval lazy beta iota delta [compute_size bind] in compute_size. *)
Function compute_size stbl typ :=  match compute_chnk_of_type stbl typ with
                                     | OK x => OK (size_chunk x)
                                     | Error msg => Error msg
                                     end.
Lemma compute_size_ok : forall stbl typ ,
    compute_size stbl typ = spark2Cminor.compute_size stbl typ.
Proof.
  intros;reflexivity.
Qed.


(* Definition build_frame_lparams:= Eval lazy beta iota delta [build_frame_lparams bind] in build_frame_lparams. *)

Function build_frame_lparams (stbl : Symbol_Table_Module.symboltable) (fram_sz : localframe * Z) (lparam : list paramSpec)
                    {struct lparam} : res (localframe * Z) :=
  match lparam with
  | [ ] => OK fram_sz
  | {| parameter_name := nme; parameter_subtype_mark := subtyp_mrk |} :: lparam' =>
      match spark2Cminor.add_to_frame stbl fram_sz nme subtyp_mrk with
      | OK x => build_frame_lparams stbl x lparam'
      | Error msg => Error msg
      end
  end.


Lemma build_frame_lparams_ok : spark2Cminor.build_frame_lparams = build_frame_lparams.
Proof.
  reflexivity.
Qed.


(* Definition build_frame_decl := Eval lazy beta iota delta [build_frame_decl bind] in build_frame_decl. *)

Function build_frame_decl (stbl : Symbol_Table_Module.symboltable) (fram_sz : localframe * Z)
                 (decl : decl) {struct decl} : res (localframe * Z) :=
  let (fram, sz) := fram_sz in
  match decl with
  | NullDecl => OK fram_sz
  | TypeDecl _ _ => Error (msg "build_frame_decl: type decl no implemented yet")
  | ObjDecl _ objdecl =>
      match spark2Cminor.compute_size stbl (object_nominal_subtype objdecl) with
      | OK x =>
          let new_size := sz + x in
          if new_size >=? Integers.Int.modulus
          then Error (msg "build_frame_decl: memory would overflow")
          else OK ((object_name objdecl, sz) :: fram, new_size)
      | Error msg => Error msg
      end
  | ProcBodyDecl _ _ => Error (msg "build_frame_decl: proc decl no implemented yet")
  | SeqDecl _ decl1 decl2 =>
      match build_frame_decl stbl fram_sz decl1 with
      | OK x => build_frame_decl stbl x decl2
      | Error msg => Error msg
      end
  end.

Lemma build_frame_decl_ok : spark2Cminor.build_frame_decl = build_frame_decl.
Proof.
  reflexivity.
Qed.

Definition msg1:string := "transl_declaration: D_Type_Declaration not yet implemented".

(* Definition transl_procedure := Eval cbv beta delta [bind bind2 transl_procedure] in transl_procedure. *)


(* We add implicit args to Gfun "(AST.fundef function) unit" to work
   around a limitation of Function *)
Function transl_procedure  (stbl : Symbol_Table_Module.symboltable) (enclosingCE : compilenv)
                 (lvl : Symbol_Table_Module.level) (pbdy : procBodyDecl) {struct pbdy} :
  res CMfundecls :=
  match pbdy with
  | mkprocBodyDecl _ pnum lparams decl0 statm =>
      match spark2Cminor.build_compilenv stbl enclosingCE lvl lparams decl0 with
      | OK (x, y) =>
          if y <=? Integers.Int.max_unsigned
          then
           match transl_declaration stbl x (S lvl) decl0 with
           | OK x0 =>
               match spark2Cminor.transl_stmt stbl x statm with
               | OK x1 =>
                   match init_locals stbl x decl0 with
                   | OK x2 =>
                       match store_params stbl x lparams with
                       | OK x3 =>
                           let chain_param :=
                             Sstore AST.Mint32 (Econst (Oaddrstack Integers.Int.zero))
                               (Evar chaining_param) in
                           match copy_out_params stbl x lparams with
                           | OK x4 =>
                               let proc_t :=
                                 Sseq chain_param
                                   (Sseq (Sseq x3 (Sseq x2 Sskip)) (Sseq x1 x4)) in
                               match
                                 transl_lparameter_specification_to_procsig stbl lvl
                                   lparams
                               with
                               | OK x5 =>
                                   let tlparams :=
                                     transl_lparameter_specification_to_lident stbl
                                       lparams in
                                   let newGfun :=
                                     (transl_paramid pnum,
                                     @AST.Gfun (AST.fundef function) unit
                                       (AST.Internal
                                          {|
                                          fn_sig := x5;
                                          fn_params := chaining_param :: tlparams;
                                          fn_vars := transl_decl_to_lident stbl decl0;
                                          fn_stackspace := y;
                                          fn_body := proc_t |})) in
                                   OK (newGfun :: x0)
                               | Error msg => Error msg
                               end
                           | Error msg => Error msg
                           end
                       | Error msg => Error msg
                       end
                   | Error msg => Error msg
                   end
               | Error msg => Error msg
               end
           | Error msg => Error msg
           end
          else Error (msg "spark2Cminor: too many local variables, stack size exceeded")
      | Error msg => Error msg
      end
  end
with
transl_declaration (stbl : Symbol_Table_Module.symboltable) 
                   (enclosingCE : compilenv) (lvl : Symbol_Table_Module.level)
                   (decl : decl) {struct decl} : res CMfundecls :=
  match decl with
  | NullDecl => OK [ ]
  | TypeDecl _ _ => Error (msg "transl_declaration: TypeDecl not yet implemented")
  | ObjDecl _ objdecl =>
      OK
        [(transl_paramid (object_name objdecl),
         AST.Gvar
           {|
           AST.gvar_info := tt;
           AST.gvar_init := [ ];
           AST.gvar_readonly := false;
           AST.gvar_volatile := false |})]
  | ProcBodyDecl _ pbdy => transl_procedure stbl enclosingCE lvl pbdy
  | SeqDecl _ decl1 decl2 =>
      match transl_declaration stbl enclosingCE lvl decl1 with
      | OK x =>
          match transl_declaration stbl enclosingCE lvl decl2 with
          | OK x0 => OK (x ++ x0)
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  end.


Functional Scheme transl_procedure_ind2 := Induction for transl_procedure Sort Prop
with transl_declaration_ind2 := Induction for transl_declaration Sort Prop.

Lemma transl_declaration_ok : spark2Cminor.transl_declaration = transl_declaration.
Proof.
  reflexivity.
Qed.

Lemma transl_procedure_ok : spark2Cminor.transl_procedure = transl_procedure.
Proof.
  reflexivity.
Qed.

(* Definition copy_out_params:= Eval lazy beta iota delta [copy_out_params bind] in copy_out_params. *)
Function copy_out_params  (stbl : Symbol_Table_Module.symboltable) (CE : compilenv)
                (lparams : list paramSpec) {struct lparams} : 
res stmt :=
  match lparams with
  | [ ] => OK Sskip
  | prm :: lparams' =>
      let id := transl_paramid (parameter_name prm) in
      match spark2Cminor.compute_chnk stbl (Identifier 0%nat (parameter_name prm)) with
      | OK x =>
          match copy_out_params stbl CE lparams' with
          | OK x0 =>
              match transl_name stbl CE (Identifier 0%nat (parameter_name prm)) with
              | OK x1 =>
                  match parameter_mode prm with
                  | In => OK x0
                  | Out => OK (Sseq (Sstore x (Evar id) (Eload x x1)) x0)
                  | In_Out => OK (Sseq (Sstore x (Evar id) (Eload x x1)) x0)
                  end
              | Error msg => Error msg
              end
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  end.

Lemma copy_out_params_ok : forall stbl CE lparams, spark2Cminor.copy_out_params stbl CE lparams = copy_out_params stbl CE lparams.
Proof.
  reflexivity.
Qed.

(* Definition store_params:= Eval lazy beta iota delta [store_params bind] in store_params. *)

Function store_params (stbl : Symbol_Table_Module.symboltable) (CE : compilenv)
             (lparams : list paramSpec) {struct lparams} : 
res stmt :=
  match lparams with
  | [ ] => OK Sskip
  | prm :: lparams' =>
      let id := transl_paramid (parameter_name prm) in
      match spark2Cminor.compute_chnk stbl (Identifier 0%nat (parameter_name prm)) with
      | OK x =>
          match store_params stbl CE lparams' with
          | OK x0 =>
              match transl_name stbl CE (Identifier 0%nat (parameter_name prm)) with
              | OK x1 =>
                  let rexp :=
                    match parameter_mode prm with
                    | In => Evar id
                    | Out => Eload x (Evar id)
                    | In_Out => Eload x (Evar id)
                    end in
                  OK (Sseq (Sstore x x1 rexp) x0)
              | Error msg => Error msg
              end
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  end.

Lemma store_params_ok : forall stbl CE lparams, spark2Cminor.store_params stbl CE lparams = store_params stbl CE lparams.
Proof.
  reflexivity.
Qed.

(* Definition init_locals:= Eval lazy beta iota delta [init_locals bind] in init_locals. *)
Function init_locals (stbl : Symbol_Table_Module.symboltable) (CE : compilenv) 
            (decl : decl) {struct decl} : res stmt :=
  match decl with
  | NullDecl => OK Sskip
  | TypeDecl _ _ => OK Sskip
  | ObjDecl _ objdecl =>
      match initialization_exp objdecl with
      | Some e =>
          match
            spark2Cminor.compute_chnk stbl (Identifier 0%nat (object_name objdecl))
          with
          | OK x =>
              match spark2Cminor.transl_expr stbl CE e with
              | OK x0 =>
                  match
                    transl_name stbl CE (Identifier 0%nat (object_name objdecl))
                  with
                  | OK x1 => OK (Sstore x x1 x0)
                  | Error msg => Error msg
                  end
              | Error msg => Error msg
              end
          | Error msg => Error msg
          end
      | None => OK Sskip
      end
  | ProcBodyDecl _ _ => OK Sskip
  | SeqDecl _ decl1 decl2 =>
      match init_locals stbl CE decl1 with
      | OK x =>
          match init_locals stbl CE decl2 with
          | OK x0 => OK (Sseq x x0)
          | Error msg => Error msg
          end
      | Error msg => Error msg
      end
  end.

Lemma init_locals_ok : forall stbl CE decl, spark2Cminor.init_locals stbl CE decl = init_locals stbl CE decl.
Proof.
  reflexivity.
Qed.

Function eval_constant (ge : genv) (sp : Values.val) (cst : constant) :=
  match cst with
  | Ointconst n => Some (Values.Vint n)
  | Ofloatconst n => Some (Values.Vfloat n)
  | Osingleconst n => Some (Values.Vsingle n)
  | Olongconst n => Some (Values.Vlong n)
  | Oaddrsymbol s ofs => Some match Globalenvs.Genv.find_symbol ge s with
                              | Some b => Values.Vptr b ofs
                              | None => Values.Vundef
                              end
  | Oaddrstack ofs => Some (Values.Val.add sp (Values.Vint ofs))
  end.

Lemma eval_constant_ok : forall ge sp cst, eval_constant ge sp cst = Cminor.eval_constant ge sp cst.
Proof.
  reflexivity.
Qed.

Function add v1 v2 :=
  match v1 with
  | Values.Vundef => Values.Vundef
  | Values.Vint n1 =>
    match v2 with
    | Values.Vundef => Values.Vundef
    | Values.Vint n2 => Values.Vint (Integers.Int.add n1 n2)
    | Values.Vlong _ => Values.Vundef
    | Values.Vfloat _ => Values.Vundef
    | Values.Vsingle _ => Values.Vundef
    | Values.Vptr b2 ofs2 => Values.Vptr b2 (Integers.Int.add ofs2 n1)
    end
  | Values.Vlong _ => Values.Vundef
  | Values.Vfloat _ => Values.Vundef
  | Values.Vsingle _ => Values.Vundef
  | Values.Vptr b1 ofs1 =>
    match v2 with
    | Values.Vundef => Values.Vundef
    | Values.Vint n2 => Values.Vptr b1 (Integers.Int.add ofs1 n2)
    | Values.Vlong _ => Values.Vundef
    | Values.Vfloat _ => Values.Vundef
    | Values.Vsingle _ => Values.Vundef
    | Values.Vptr _ _ => Values.Vundef
    end
  end.
Lemma add_ok : forall x y, add x y = Values.Val.add x y.
Proof.
  reflexivity.
Qed.
