

Require Import symboltable.
Require Import Errors.
(* Require Import language. *)
Require Import Cminor.
Require Cshmgen.
Require Cminorgen.
Require Import BinPosDef.

Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

(** * A symbol table with concrete types only *)

(** We suppose the existence of a completely expansed symbol table.
    This table contains a mapping from variable names to basic types,
    i.e. types with no reference to any derived or subtype, only to
    the concrete type used to represent it. It is not the so called
    "base type" of Ada jargon, since for instance the base type of a
    derived type is its (immedaite) parent type. The building of this
    expanded table from the AST should be a recursive function. This
    function is not trivially structurally recursive. Krebbers seems
    to have a working trick (remove the type definition once
    traversed). *)

Import Symbol_Table_Module.
Open Scope error_monad_scope.

Parameter MinInt MaxInt: Z.

(** The [base_type] of a type is the corresponding concrete type. *)
Inductive base_type: Type :=
| BBoolean
| BInteger (rg:range)
| BArray_Type (t: base_type) (rg:range)
| BRecord_Type (t: base_type). (* + record info *)





(** symbol table for unflagged program, with expanded type defs. *)
Module Symbol_Table_Elements <: SymTable_Element.
  Definition Procedure_Decl := procedure_body.
  Definition Type_Decl := base_type.
  Definition Source_Location := source_location.
End Symbol_Table_Elements.

(* TODO: have a set of function returning res type instead of option type. *)

Module Symbol_Table_Module := SymbolTableM (Symbol_Table_Elements).
Definition symboltable := Symbol_Table_Module.symboltable.
Definition mkSymbolTable := Symbol_Table_Module.mkSymbolTable.
Definition proc_decl := Symbol_Table_Module.proc_decl.
Definition type_decl := Symbol_Table_Module.type_decl.
Definition reside_symtable_vars := Symbol_Table_Module.reside_symtable_vars.
Definition reside_symtable_procs := Symbol_Table_Module.reside_symtable_procs.
Definition reside_symtable_types := Symbol_Table_Module.reside_symtable_types.
Definition reside_symtable_exps := Symbol_Table_Module.reside_symtable_exps.
Definition reside_symtable_sloc := Symbol_Table_Module.reside_symtable_sloc.
(* useless, vars are not filled in stbl. *)
(* Definition fetch_var := Symbol_Table_Module.fetch_var. *)
Definition fetch_proc := Symbol_Table_Module.fetch_proc.
Definition fetch_type := Symbol_Table_Module.fetch_type.
Definition fetch_exp_type := Symbol_Table_Module.fetch_exp_type.
Definition fetch_sloc := Symbol_Table_Module.fetch_sloc.
Definition update_vars := Symbol_Table_Module.update_vars.
Definition update_procs := Symbol_Table_Module.update_procs.
Definition update_types := Symbol_Table_Module.update_types.
Definition update_exps := Symbol_Table_Module.update_exps.
Definition update_sloc := Symbol_Table_Module.update_sloc.



Require symboltable.
Definition range_of (tpnum:type): res range :=
  OK (Range 0 10) (* FIXME *).


(** [reduce_type stbl ty n] returns the basic type (which is not a
    base type à la Ada) of a type. Currently this function iters on a
    arbitrary n but in fine we should remove this n.
 Idea from Krebber: remove the type defiition from stbl after fetching
 it. That way we have a decreasing argument. *)
Fixpoint reduce_type (stbl:symboltable.symboltable) (ty:type) (n:nat): res base_type :=
  match n with
    | O => Error (msg "transl_basetype: exhausted recursivity")
    | S n' =>
      match ty with
        (* currently our formalization only defines one scalar type:
       INTEGER, that we match to compcert 32 bits ints. *)
        | Integer => OK (BInteger (Range 0 Integers.Int.max_unsigned))

        (* Let us say that booleans are int32, which is probably stupid. *)
        | Boolean => OK BBoolean

        | Array_Type typnum =>
          match symboltable.fetch_type typnum stbl with
            | None => Error [ MSG "transl_basetype: no such type num :" ; CTX (Pos.of_nat typnum)]
            | Some (Array_Type_Declaration _ _ tpidx tpcell) =>
              do typofcells <- reduce_type stbl tpcell n' ;
                do rge <- range_of tpidx ;
                OK (BArray_Type typofcells rge)
            | _ => Error [ MSG "transl_basetype: not an array type :" ; CTX (Pos.of_nat typnum)]
          end
        (* TODO: array and record types *)
        | Integer_Type _ => Error (msg "transl_basetype: Integer_Type Not yet implemented!!.")
        | Subtype _ => Error (msg "transl_basetype: Subtype Not yet implemented!!.")
        | Derived_Type _ => Error (msg "transl_basetype: Derived Not yet implemented!!.")
        | Record_Type _ => Error (msg "transl_basetype: Record Not yet implemented!!.")
      end
  end.

Definition type_of_decl (typdecl:type_declaration): res type :=
  match typdecl with
    | Integer_Type_Declaration _ typnum range => OK (Integer_Type typnum)
    | Array_Type_Declaration _ typnum typidx typcell => OK (Array_Type typnum)
    | Record_Type_Declaration x x0 x1 => Error (msg "type_of_decl: Record Not yet implemented!!.")
    | Subtype_Declaration x x0 x1 x2 => Error (msg "type_of_decl: Subtype Not yet implemented!!.")
    | Derived_Type_Declaration x x0 x1 x2 => Error (msg "type_of_decl: Derived Not yet implemented!!.")
  end.


Definition max_recursivity:nat := 30.

Fixpoint reduce_stbl (stbl:symboltable.symboltable): res symboltable :=
  match stbl with
    | symboltable.mkSymbolTable vars procs types exps sloc =>
      do redtypes <- mmap
                  (fun x =>
                     do typ <- type_of_decl (snd x);
                     do redtype <- reduce_type stbl typ max_recursivity;
                     OK (fst x , redtype))
                  types;
      OK (mkSymbolTable vars procs redtypes exps sloc)
  end.









(** A stack-like compile environment. *)

Module OffsetEntry <: environment.ENTRY.
  Definition T := Z.
End OffsetEntry.

Module CompilEnv := environment.STORE OffsetEntry.
Definition compilenv := CompilEnv.stack.










(** We book one identifier for the chaining argument of all functions.
    Hopefully we can reuse it everywhere. *)

Definition chaining_param := xH.


Definition transl_literal (l:literal): Cminor.constant :=
  match l with
    | Integer_Literal x => Ointconst (Integers.Int.repr x)
    (** In spark, boolean are a real type, we translate it to int (0
        for false, and anything else for true). *)
    | Boolean_Literal true => Ointconst Integers.Int.one
    | Boolean_Literal false => Ointconst Integers.Int.zero
  end.



Definition make_load (addr : Cminor.expr) (ty_res : Ctypes.type) :=
match Ctypes.access_mode ty_res with
| Ctypes.By_value chunk => OK (Eload chunk addr)
| Ctypes.By_reference => OK addr
| Ctypes.By_copy => OK addr
| Ctypes.By_nothing => Error (msg "spark2compcert.make_load")
end.

Definition default_attr: Ctypes.attr := {| Ctypes.attr_volatile := false;
                                           Ctypes.attr_alignas := None |}.
Definition void_star := (Ctypes.Tpointer Ctypes.Tvoid default_attr).


(** [build_loads_ m] returns the expression denoting the mth
    indirection of the variable of offset Zero (i.e. the pointer to
    enclosing procedure). This is the way we access to enclosing
    procedure frame. The type of all Load is ( void * ). *)
Fixpoint build_loads_ (m:nat) {struct m} : res Cminor.expr :=
  match m with
    | 0 => OK (Econst (Oaddrstack (Integers.Int.zero)))
    | S m' =>
      do subloads <- build_loads_ m' ;
        make_load subloads void_star
  end.

Eval compute in build_loads_ 4.

(** [build_loads m n] is the expression denoting the address
    of the variable at offset [n] in the enclosing frame [m] levels
    above the current frame. This is done by following pointers from
    frames to frames. (Load (Load ...)). *)
Definition build_loads (m:nat) (n:Z) :=
  do indirections <- build_loads_ m ;
  OK (Ebinop Oadd indirections (Econst (Ointconst (Integers.Int.repr n)))).

Eval compute in build_loads 4 2.

Fixpoint transl_basetype (stbl:symboltable) (ty:base_type): res Ctypes.type :=
  match ty with
    (* currently our formalization only defines one scalar type:
       INTEGER, that we match to compcert 32 bits ints. *)
    | BInteger rge => OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr)

    (* Let us say that booleans are int32, which is probably stupid. *)
    | BBoolean => OK (Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr)

    | BArray_Type tpcell (Range min max) =>
      do typofcells <- transl_basetype stbl tpcell ;
        OK (Ctypes.Tarray typofcells (max - min)%Z Ctypes.noattr) (* replace 0 by size of the array *)

    | _ => Error (msg "transl_basetype: Not yet implemented!!.")
  end.


Definition transl_typenum (stbl:symboltable) (id:typenum): res Ctypes.type :=
  match fetch_type id stbl with
    | None => Error (msg "transl_typenum: no such type")
    | Some t => transl_basetype stbl t
  end.

Definition transl_type(stbl:symboltable) (t:type): res Ctypes.type :=
  match t with
    | Boolean => transl_basetype stbl BBoolean
    | Integer => transl_basetype stbl (BInteger (Range MinInt MaxInt))
    | Subtype t' => transl_typenum stbl t'
    | Derived_Type t' => transl_typenum stbl t'
    | Integer_Type t' => transl_typenum stbl t'
    | Array_Type t' => transl_typenum stbl t'
    | Record_Type t => Error (msg "transl_type: no such type")
  end.


Definition error_msg_with_loc stbl astnum (nme:nat) :=
  match fetch_sloc astnum stbl with
      Some loc => [CTX (Pos.of_nat nme) ; MSG " at line: " ;
                   CTX (Pos.of_nat (loc.(line))) ;
                   MSG " and column: " ; CTX (Pos.of_nat (loc.(col)))]
    | None => [CTX (Pos.of_nat nme) ; MSG "no location found" ]
  end.

(** [transl_idnum stbl CE astnum nme] returns the expression that would
    evaluate to the *address* of variable [nme]. The compiler
    environment [CE] allows to 1) know the nesting level of the
    current procedure, 2) the nesting level of the procedure defining
    [nme]. From these two numbers we generate the right number of
    Loads to access the frame of [nme]. *)
Definition transl_idnum (stbl:symboltable) (CE:compilenv) astnum (nme:idnum) : res Cminor.expr :=
  match (CompilEnv.fetchG nme CE) with
    | None =>  Error (MSG "transl_idnum: no such idnum." :: error_msg_with_loc stbl astnum nme)
    | Some n =>
      match (CompilEnv.frameG nme CE) with
        | None =>  Error (msg "assert false.")
        | Some (m,_) =>
          match CompilEnv.level_of_top CE with
            | None =>  Error (msg "no frame on compile env. assert false.")
            | Some m' =>
              build_loads (m' - m) n (* get the adress of the variable *)
          end
      end
  end.



Definition transl_binop (op:binary_operator): binary_operation :=
  match op with
    | And => Cminor.Oand
    | Or => Cminor.Oor
    | Plus => Cminor.Oadd
    | Minus => Cminor.Osub
    | Multiply => Cminor.Omul
    | Divide => Cminor.Odiv (* divu? *)
    | Equal => Cminor.Ocmp Integers.Ceq
    | Not_Equal => Cminor.Ocmp Integers.Cne
    | Less_Than => Cminor.Ocmp Integers.Clt
    | Less_Than_Or_Equal => Cminor.Ocmp Integers.Cle
    | Greater_Than => Cminor.Ocmp Integers.Cgt
    | Greater_Than_Or_Equal => Cminor.Ocmp Integers.Cge
  end.

Definition transl_unop (op:unary_operator) : res Cminor.unary_operation :=
  match op with
    | Unary_Plus => Error (msg "unary plus should be removed")
    | Unary_Minus => OK Cminor.Onegint
    | Not => OK Cminor.Onotint
  end.



Notation "{{ n }}" := (Integers.Int.repr n) : spark_scope.
Notation "'[<<' n '>>]'" := (Econst (Ointconst (Integers.Int.repr n))) (at level 9) : spark_scope.
Notation "'[<' n '>]'" := (E_Literal 704 (Integer_Literal n)%Z) (at level 9) : spark_scope.
Notation "e1 <<*>> e2" := (Ebinop Omul e1 e2) (left associativity,at level 40) : spark_scope.
Notation "e1 <<+>> e2" := (Ebinop Oadd e1 e2) (left associativity,at level 50) : spark_scope.
Notation "e1 <<->> e2" := (Ebinop Osub e1 e2) (left associativity,at level 50) : spark_scope.
Notation " <<->> e" := (Eunop Onegint e) (at level 35) : spark_scope.
Notation "'VI'" := (Evar 112%positive) : spark_scope.
Notation "'VARR'" := (Evar 113%positive) : spark_scope.

Notation "X ++ Y" := (String.append X Y) : spark_scope.

Open Scope spark_scope.

(* This Fixpoint can be replaced by a Function if:
 1) in trunk (v8.5 when ready)
 2) we replace the notation for "do" expanding the def of bind.
Notation "'do' X <- A ; B" := (match A with
                                 | OK x => ((fun X => B) x)
                                 | Error msg => Error msg
                               end)
                                (at level 200, X ident, A at level 100, B at level 200)
 : error_monad_scope. *)
(** [transl_expr stbl CE e] returns the code that evaluates to the
    value of expression [e]. *)
Fixpoint transl_expr (stbl:symboltable) (CE:compilenv) (e:expression): res Cminor.expr :=
  match e with
    | E_Literal _ lit => OK (Econst (transl_literal lit))
    | E_Name astnum (E_Identifier _ id) =>
      do addrid <- transl_idnum stbl CE astnum id ; (* get the address of the variable *)
(*         match fetch_var id stbl with (* get its type *) *)
        match fetch_exp_type astnum stbl with (* get its type *)
          | None => Error ([MSG "transl_expr: no such variable " ; CTX (Pos.of_nat id)])
          | Some (typ) =>
            do ttyp <- transl_type stbl typ ;
              make_load addrid ttyp (* load its content *)
        end
    | E_Name _ (E_Selected_Component _ _ _ _) => Error (msg "Not yet implemented")
    | E_Binary_Operation _ op e1 e2 =>
      do te1 <- transl_expr stbl CE e1;
        do te2 <- transl_expr stbl CE e2;
        OK (Ebinop (transl_binop op) te1 te2)
    | E_Unary_Operation _ op e =>
      do te <- transl_expr stbl CE e;
        do top <- transl_unop op;
        OK (Eunop top te)
    | E_Name astnum (E_Indexed_Component _ _ id e) => (* deref? *)
      do tid <- (transl_idnum stbl CE astnum id);
(*         match fetch_var id stbl with *)
        match fetch_exp_type astnum stbl with
          (* typid = type of the array (in spark) *)
          | Some (language_basics.Array_Type typid) =>
            match fetch_type typid stbl with
              | None => Error (msg "transl_expr: no such type")
              | Some (BArray_Type ty (Range min max)) =>
                (** [id[e]] becomes  [Eload (<id>+(<e>-rangemin(id))*sizeof(<ty>))] *)
                do tty <- transl_basetype stbl ty ;
                  do cellsize <- OK [<< Ctypes.sizeof tty >>];
                  do te <- transl_expr stbl CE e ;
                  do offs <- OK(Ebinop Cminor.Osub te [<<min>>]) ;
                  make_load
                    (Ebinop Cminor.Oadd tid (Ebinop Cminor.Omul offs cellsize)) tty
              | _ => Error (msg "transl_expr: is this really an array type?")
            end
          | _ => Error (msg "transl_expr: ")
        end
  end.

(** [transl_name stbl CE nme] returns the code that evaluates to the
    *address* where the value of name [nme] is stored. *)
Fixpoint transl_name (stbl:symboltable) (CE:compilenv) (nme:name): res Cminor.expr :=
  match nme with
    | E_Identifier astnum id => (transl_idnum stbl CE astnum id) (* address of the variable *)
    | E_Indexed_Component  astnum _ id e =>
      do tid <- transl_idnum stbl CE astnum id; (* address of the variable *)
(*         match fetch_var id stbl with *)
        match fetch_exp_type astnum stbl with
          (* typid = type of the array (in spark) *)
          | Some (language_basics.Array_Type typid) =>
            match fetch_type typid stbl with
              | None => Error (msg "transl_expr: no such type")
              | Some (BArray_Type ty (Range min max)) =>
                (** [id[e]] becomes  [Eload (<id>+(<e>-rangemin(id))*sizeof(<ty>))] *)
                do tty <- transl_basetype stbl ty ;
                  do cellsize <- OK [<<Ctypes.sizeof tty>>];
                  do te <- transl_expr stbl CE e ;
                  do offs <- OK(Ebinop Cminor.Osub te [<<min>>]) ;
                  OK (Ebinop Cminor.Oadd tid (Ebinop Cminor.Omul offs cellsize))
            | _ => Error (msg "transl_expr: is this really an array type?")
          end
        | _ => Error (msg "transl_expr: ")
      end
    | E_Selected_Component  _ _ _ _ =>  Error (msg "transl_name:Not yet implemented")
  end.

Fixpoint transl_exprlist (stbl: symboltable) (CE: compilenv) (el: list expression)
                     {struct el}: res (list Cminor.expr) :=
  match el with
  | nil => OK nil
  | e1 :: e2 =>
      do te1 <- transl_expr stbl CE e1;
      do te2 <- transl_exprlist stbl CE e2;
      OK (te1 :: te2)
  end.


(* FIXME *)
Definition compute_chnk (stbl:symboltable) (nme:name): res AST.memory_chunk :=
  OK AST.Mint32.


Fixpoint transl_lparameter_specification_to_ltype
         (stbl:symboltable) (lpspec:list parameter_specification): res (list AST.typ) :=
  match lpspec with
    | nil => OK nil
    | cons pspec lpspec' =>
      do ttyp <- transl_type stbl (pspec.(parameter_subtype_mark)) ;
      do tltyp <- transl_lparameter_specification_to_ltype stbl lpspec' ;
      OK (Ctypes.typ_of_type ttyp :: tltyp)
  end.

Definition transl_paramid := Pos.of_nat.

Fixpoint transl_lparameter_specification_to_lident
         (stbl:symboltable) (lpspec:list parameter_specification): (list AST.ident) :=
  match lpspec with
    | nil => nil
    | cons pspec lpspec' =>
      let tid := transl_paramid (pspec.(parameter_name)) in
      let tlid := transl_lparameter_specification_to_lident stbl lpspec' in
      tid :: tlid
  end.


Fixpoint transl_decl_to_lident_ (stbl:symboltable) (decl:declaration): list AST.ident :=
  match decl with
    | D_Null_Declaration => nil
    | D_Seq_Declaration _ decl1 decl2 =>
      let lident1 := transl_decl_to_lident_ stbl decl1 in
      let lident2 := transl_decl_to_lident_ stbl decl2 in
      List.app lident1 lident2
    | D_Object_Declaration _ objdecl => [transl_paramid objdecl.(object_name)]
    | D_Type_Declaration x x0 => nil
    | D_Procedure_Body x x0 => nil
  end.

Definition transl_decl_to_lident (stbl:symboltable) (lpspec:list parameter_specification)
           (decl:declaration): list AST.ident :=
  let original := transl_decl_to_lident_ stbl decl in
  let with_parameter_copy := List.app (transl_lparameter_specification_to_lident stbl lpspec)
                                      original in
  (* Adding the local copy of the chaining parameter *)
  chaining_param :: with_parameter_copy.

(*Definition transl_lparameter_id
         (CE:compilenv) (lpspec:list parameter_specification): (list AST.ident) :=
  List.map (fun spec => transl_idnum astnum stbl CE (spec.(parameter_name))) lpspec.
*)
Definition default_calling_convention := {| AST.cc_vararg := true;
                                            AST.cc_structret := true |}.

Definition transl_lparameter_specification_to_procsig
           (stbl:symboltable) (lvl:Symbol_Table_Module.level)
           (lparams:list parameter_specification) : res (AST.signature * Symbol_Table_Module.level) :=
  do tparams <- transl_lparameter_specification_to_ltype stbl lparams ;
  OK ({|
         (* add a void* to the list of parameters, for frame chaining *)
         AST.sig_args:= AST.Tint :: tparams ;
         AST.sig_res := None ; (* procedure: no return type *)
         AST.sig_cc := default_calling_convention
       |}, lvl).




Definition transl_procsig (stbl:symboltable) (pnum:procnum)
  : res (AST.signature * Symbol_Table_Module.level) :=
  match fetch_proc pnum stbl with
      | None => Error (msg "Unkonwn procedure")
      | Some (lvl , pdecl) => transl_lparameter_specification_to_procsig
                                stbl lvl (procedure_parameter_profile pdecl)
  end.

(* We don't want to change procedure names so we probably need to
   avoid zero as a procedure name in spark. *)
Definition transl_procid := Pos.of_nat.

Fixpoint transl_stmt (stbl:symboltable) (CE:compilenv) (e:statement) {struct e}: res stmt :=
  match e with
    | S_Null => OK Sskip
    | S_Sequence _ s1 s2 =>
      do ts1 <- transl_stmt stbl CE s1;
        do ts2 <- transl_stmt stbl CE s2;
        OK (Sseq ts1 ts2)
    | S_Assignment _ nme e =>
      do te <- transl_expr stbl CE e;
        do tnme <- transl_name stbl CE nme ;
        do chnk <- compute_chnk stbl nme ;
        OK (Sstore chnk tnme te)
    | S_If _ e s1 s2 =>
      do te1 <- transl_expr stbl CE e ;
        do te <- OK (Ebinop (Ocmp Integers.Cne)
                            te1 (Econst (Ointconst Integers.Int.zero)));
        do ts1 <- transl_stmt stbl CE s1;
        do ts2 <- transl_stmt stbl CE s2;
        OK (Sifthenelse te ts1 ts2)

    (* Procedure call. Ada RM tells that scalar parameters are always
       taken by value and if they are out or inout the copy is done
       *at the end* of the procedure. For composite types (arrays and
       record) the choice is left to the compiler (it is done by copy
       in the reference semantics), and for complex types (tasks,
       protected types) they are always taken by reference.

       Question: Since no aliasing is allowed in spark, it should not
       be possible to exploit one or the other strategy for arrays and
       records? *)
    | S_Procedure_Call _ _ pnum lexp =>
      do tle <- transl_exprlist stbl CE lexp ;
        do (procsig,lvl) <- transl_procsig stbl pnum ;
        (* The height of CE is exactly the nesting level of the current procedure *)
        let current_lvl := List.length CE in
        (* compute the expression denoting the address of the frame of
           the enclosing procedure. Note that it is not the current
           procedure. We have to get down to the depth of the called
           procedure (minus 1). *)
        do addr_enclosing_frame <- build_loads_ (current_lvl - lvl) ;
        (* Add it as one more argument to the procedure called. *)
        do tle' <- OK (addr_enclosing_frame :: tle) ;
        (* Call the procedure; procedure name does not change (except it is a positive) ? *)
        (* Question: what should be the name of a procedure in Cminor? *)
        OK (Scall None procsig (Evar (transl_procid pnum)) tle')

    (* No loops yet. Cminor loops (and in Cshminor already) are
       infinite loops, and a failing test (the test is a statement,
       not an expression) does a "exit n" where is nb of level to go
       out of the loop (if the test contains a block...). See
       Cshmgen.transl_statement, we need to have the number of
       necessary breaks to get out. *)
    | S_While_Loop x x0 x1 => Error (msg "transl_stmt:Not yet implemented")
  end.


(* [compute_size stbl typ] return the size needed to store values of typpe subtyp_mrk *)
Definition compute_size (stbl:symboltable) (typ:type) := 4%Z.


Definition add_to_compilenv stbl (cenv_sz:CompilEnv.store*Z) nme subtyp_mrk: CompilEnv.store*Z  :=
  let (cenv,sz) := cenv_sz in
  let size := compute_size stbl subtyp_mrk in
  let new_size := (sz+size)%Z in
  let new_cenv := (nme,sz) :: cenv in
  (new_cenv,new_size).

(* [build_frame_lparams stbl (cenv,sz) lparam] uses cenv as an
   accumulator to build a compilation env for lparam. It also compute
   the overall size of the store. *)
Fixpoint build_frame_lparams (stbl:symboltable) (cenv_sz:CompilEnv.store * Z)
         (lparam:list parameter_specification): CompilEnv.store*Z :=
  match lparam with
    | nil => cenv_sz
    | mkparameter_specification _ nme subtyp_mrk mde :: lparam' =>
      let new_cenv_sz := add_to_compilenv stbl cenv_sz nme subtyp_mrk in
      build_frame_lparams stbl new_cenv_sz lparam'
  end.

(* [build_frame_decl stbl (cenv,sz) decl] uses cenv as an
   accumulator to build a compilation env for decl. It also compute
   the overall size of the store. *)
Fixpoint build_frame_decl (stbl:symboltable) (cenv_sz:CompilEnv.store * Z)
         (decl:declaration): CompilEnv.store*Z :=
  let (cenv,sz) := cenv_sz in
  match decl with
    | D_Null_Declaration => cenv_sz
    | D_Seq_Declaration _ decl1 decl2 =>
      let cenv2_sz1 := build_frame_decl stbl cenv_sz decl1 in
      build_frame_decl stbl cenv2_sz1 decl2
    | D_Object_Declaration _ objdecl =>
      let size := compute_size stbl (objdecl.(object_nominal_subtype)) in
      let new_size := (sz+size)%Z in
      (((objdecl.(object_name),sz)::cenv) ,new_size)
    | _ => cenv_sz
  end.



(* [build_compilenv stbl enclosingCE pbdy] returns the new compilation
   environment built from the one of the enclosing procedure
   [enclosingCE] and the list of parameters [lparams] and local
   variables [decl]. One of the things to note here is that it adds a
   variable at address 0 which contains the address of the frame of
   the enclosing procedure, for chaining. *)
Fixpoint build_compilenv (stbl:symboltable) (enclosingCE:compilenv) (lvl:Symbol_Table_Module.level)
         (lparams:list parameter_specification) (decl:declaration) : res (compilenv*Z) :=
  let stosz := build_frame_lparams stbl ((0,0%Z) :: nil, 4%Z) lparams in
  let (sto2,sz2) := build_frame_decl stbl stosz decl in
  let scope_lvl := List.length enclosingCE in
  OK (((scope_lvl,sto2)::enclosingCE),sz2).


(** [store_params lparams statm] adds a prelude to statement [statm]
    which effect is to store all parameters values listed in [lparams]
    into local (non temporary) variables. This is needed by nested
    procedure who need a way to read and write the parameters.

    Possible optimizations: 1) Do this only if there are nested procedures
    2) Do this only for variables that are indeed accessed (read or
       write) by nested procedures.

    Remark 1 about optimizations: during compilation we would need to
    remember which parameter is a temporary variable and which is not.
    Maybe in a new preliminary pass spark -> (spark with temporaries)?

    Remark2 about optimizations: Compcert do that in
    cfrontend/SimplLocals.v. In Clight parameters are all put into
    temporary variables and the one that cannot really be "lifted" to
    temporary (because their address is needed) are copied in the
    stack by the generated prelude of the procedure. *)
Fixpoint store_params stbl (CE:compilenv) (lparams:list parameter_specification) (statm:stmt)
         {struct lparams} : res stmt :=
  match lparams with
    | nil => OK statm
    | cons prm lparams' =>
      let id := transl_paramid prm.(parameter_name) in
      do chnk <- compute_chnk stbl (E_Identifier 0 (prm.(parameter_name))) ;
      do recres <- (store_params stbl CE lparams' statm) ;
      do lexp <- transl_name stbl CE (E_Identifier 0 (prm.(parameter_name))) ;
      OK (Sseq (Sstore chnk lexp (Evar id)) recres)
  end.

Fixpoint init_locals (stbl:symboltable) (CE:compilenv) (decl:declaration) (statm:stmt)
  : res stmt :=
  match decl with
    | D_Null_Declaration => OK statm
    | D_Seq_Declaration _ decl1 decl2 =>
      do stmt1 <- init_locals stbl CE decl2 statm ;
      init_locals stbl CE decl1 stmt1
    | D_Object_Declaration _ objdecl =>
      match objdecl.(initialization_expression) with
        | None => OK statm
        | Some e =>
          do chnk <- compute_chnk stbl (E_Identifier 0 objdecl.(object_name)) ;
          do exprinit <- transl_expr stbl CE e;
          do lexp <- transl_name stbl CE (E_Identifier 0 objdecl.(object_name)) ;
          OK (Sseq (Sstore chnk lexp exprinit) statm)
      end
    | _ => OK statm
  end.

Definition transl_procedure_body (stbl:symboltable) (enclosingCE:compilenv)
           (lvl:Symbol_Table_Module.level) (pbdy:procedure_body)
  : res (AST.ident * AST.globdef fundef unit) :=
  match pbdy with
    | mkprocedure_body _ pnum lparams decl statm =>
      do (procsig,_) <- transl_lparameter_specification_to_procsig stbl lvl lparams ;
        (* setup frame chain *)
        do (CE,stcksize) <- build_compilenv stbl enclosingCE lvl lparams decl ;
        if Coqlib.zle stcksize Integers.Int.max_unsigned
        then
          do bdy <- transl_stmt stbl CE statm ;
          do bdy_with_init <- init_locals stbl CE decl bdy ;
          do bdy_with_init_and_prelude_storing_params <- store_params stbl CE lparams bdy_with_init ;
          do bdy_with_init_and_prelude_storing_params_and_chain <-
             OK (Sseq (Sstore AST.Mint32 ((Econst (Oaddrstack (Integers.Int.zero)))) (Evar chaining_param))
                      bdy_with_init_and_prelude_storing_params) ;
          (** TODO: add the code that would copy out argument with
             "out" or "inout" mode. This should be done by doing the
             following for a given "out" argument x of type T of a
             procedure P:
             - transforme T into T*, and change conequently the calls to P and signature of P.
             - add code to copy *x into the local stack at the
               beginning of the procedure (by default we copy x
               itself for now), lets call x' this new variable
             - replace all operations on x by operations on x'
             - add code at the end of the procedure to copy the value
               of x' into *x (this achieves the copyout operation). *)
          let tlparams := transl_lparameter_specification_to_lident stbl lparams in
          OK (transl_paramid pnum,
              AST.Gfun (AST.Internal {|
                            fn_sig:= procsig;
                            (** list of idents of parameters (including the chaining one) *)
                            fn_params := chaining_param :: tlparams;
                            (* list ident of local vars, including copy of parameters and chaining parameter *)
                            fn_vars:= transl_decl_to_lident stbl lparams decl;
                            fn_stackspace:= stcksize%Z;
                            fn_body:= bdy_with_init_and_prelude_storing_params_and_chain
                          |}))
        else Error(msg "spark2Cminor: too many local variables, stack size exceeded")
  end.

(* FIXME: check the size needed for the declarations *)
Fixpoint transl_global_declaration_ (stbl:symboltable) (enclosingCE:compilenv)
           (decl:declaration) (p:Cminor.program) : res (Cminor.program) :=
  match decl with
      | D_Procedure_Body _ pbdy =>
        do tdecl <- transl_procedure_body stbl enclosingCE 0 pbdy;
          OK {| AST.prog_defs := tdecl :: p.(AST.prog_defs); AST.prog_main := p.(AST.prog_main) |}
      | D_Seq_Declaration _ decl1 decl2 =>
        do p1 <- transl_global_declaration_ stbl enclosingCE decl1 p;
        do p2 <- transl_global_declaration_ stbl enclosingCE decl2 p1;
        OK p2
      | D_Object_Declaration astnum objdecl =>
        do tobjdecl <- OK (transl_paramid objdecl.(object_name),
                           AST.Gvar {| AST.gvar_info := tt;
                                       AST.gvar_init := nil; (* TODO. list AST.init_data *)
                                       AST.gvar_readonly := false; (* FIXME? *)
                                       AST.gvar_volatile := false |} (* FIXME? *)
                          ) ; (*transl_objdecl stbl 0  ;*)
        OK {| AST.prog_defs := tobjdecl :: p.(AST.prog_defs); AST.prog_main := p.(AST.prog_main) |}
      | D_Type_Declaration _ _ => Error (msg "transl_global_declaration: D_Type_Declaration not yet implemented")
      | D_Null_Declaration => Error (msg "transl_global_declaration: D_Null_Declaration not yet implemented")
  end.

Definition transl_global_declaration (stbl:symboltable) (decl:declaration) (p:Cminor.program)
  :res (Cminor.program) :=
  do (cenv,sz) <- build_compilenv stbl nil 0(*module lvl*) nil(*params*) decl ;
  transl_global_declaration_ stbl cenv decl p.

Definition empty_program:program :=
  {| AST.prog_defs := nil;
     AST.prog_main := 39%positive |}.

Definition transl_program (stbl:symboltable) (decl:declaration) : res (Cminor.program) :=
transl_global_declaration stbl decl empty_program.



(* * Generation of a symbol table for a procedure.

No need to add the chaining parameter here, the symbol table is never
searched for it. *)

Definition empty_stbl:symboltable :=
  {|
    Symbol_Table_Module.vars  := nil; (*list (idnum * (mode * type)) *)
    Symbol_Table_Module.procs := nil; (*list (procnum * (Symbol_Table_Module.level * Symbol_Table_Module.proc_decl))*)
    Symbol_Table_Module.types := nil; (*list (typenum * Symbol_Table_Module.type_decl)*)
    Symbol_Table_Module.exps  := nil; (*list (astnum * type) *)
    Symbol_Table_Module.sloc  := nil (* list (astnum * Symbol_Table_Module.source_location) *)
  |}.


Fixpoint transl_lparameter_specification_to_stbl
         (stbl:symboltable) (lpspec:list parameter_specification)
  : symboltable :=
  match lpspec with
    | nil => stbl
    | cons pspec lpspec' =>
      let stblrec := transl_lparameter_specification_to_stbl stbl lpspec' in
      (update_vars stblrec pspec.(parameter_name) (pspec.(parameter_mode),pspec.(parameter_subtype_mark)))
  end.


Fixpoint transl_decl_to_stbl (stbl:symboltable) (decl:declaration): symboltable :=
  match decl with
    | D_Null_Declaration => stbl
    | D_Seq_Declaration _ decl1 decl2 =>
      let stbl1 := transl_decl_to_stbl stbl decl1 in
      let stbl2 := transl_decl_to_stbl stbl1 decl2 in
      stbl2
    | D_Object_Declaration _ objdecl =>
      update_vars stbl objdecl.(object_name) (In_Out,objdecl.(object_nominal_subtype))
    | D_Type_Declaration x x0 => stbl (* not implemented yet *)
    | D_Procedure_Body _ pbdy =>
      (* FIXME: we should look for blocks inside the body of the procedure. *)
      let stbl1 := transl_lparameter_specification_to_stbl stbl (procedure_parameter_profile pbdy) in
      let stbl2 := transl_decl_to_stbl stbl1 (procedure_declarative_part pbdy) in
      stbl2
  (* TODO: go recursively there *)
  end.

Definition stbl_of_proc (pbdy:procedure_body) :=
  let stbl1 := transl_lparameter_specification_to_stbl empty_stbl (procedure_parameter_profile pbdy) in
  let stbl2 := transl_decl_to_stbl stbl1 (procedure_declarative_part pbdy) in
  stbl2.

Definition empty_CE: compilenv := nil.

(* Module examples. *)

(*   Require Import Tests. *)
(*   Import Example1. *)
(*   Require Import testing_language. *)
(*   Open Scope spark_scope. *)

(*   Definition stbl1: symboltable := stbl_of_proc P1. *)
(*   Definition stbl2: symboltable := stbl_of_proc P2. *)
(*   Definition stbl3: symboltable := stbl_of_proc P3. *)


(*   Eval compute in transl_procedure_body stbl1 empty_CE 0 P1. *)
(*   Eval compute in transl_procedure_body stbl2 empty_CE 0 P2. *)
(*   Eval compute in transl_procedure_body stbl3 empty_CE 0 P3. *)


(*   Eval compute in build_compilenv stbl3 empty_CE 0 *)
(*                                   (procedure_parameter_profile P3) *)
(*                                   (procedure_declarative_part P3). *)

(*   Eval compute in build_frame_lparams stbl3 ((0,0%Z) :: nil, 4%Z) (procedure_parameter_profile P2). *)
(*   Eval compute in build_frame_decl stbl3 ([(23, 8%Z); (24, 4%Z); (0, 0%Z)], 12%Z) (procedure_declarative_part P2). *)
(*   Eval compute in build_compilenv stbl3 empty_CE 0 *)
(*                                   (procedure_parameter_profile P2) *)
(*                                   (procedure_declarative_part P2). *)



(*   Definition Tproc_referencing_glob := *)
(*     PROC P₃ [INOUT ARG Integer; IN ARG2 Boolean] IS *)
(*       N :: Boolean := Some TRUE *)
(*     BEGIN *)
(*       ARG := ARG + X *)
(*     ENDPROC. *)
(* (* Close Scope spark_scope. *) *)
(*   Definition Tproc_referencing_glob2 := *)
(*     PROC P₃ [INOUT ARG Integer; IN ARG2 Boolean] IS *)
(*       N :: Boolean := Some TRUE;;; *)
(*       TD_Procedure_Body *)
(*         PROC P₃ [INOUT ARG Integer; IN ARG2 Boolean] IS *)
(*            N :: Boolean := Some TRUE *)
(*         BEGIN *)
(*           ARG := ARG + X *)
(*         ENDPROC *)
(*     BEGIN *)
(*       ARG := ARG + X *)
(*     ENDPROC. *)




(*   Definition update_lvars (stbl:symboltable) (l:list ((idnum*(mode * type)))): symboltable := *)
(*     List.fold_left (fun acc elt => let '(id,modetyp) := elt in update_vars acc id modetyp) l stbl. *)

(*   Definition proc_referencing_glob := fst (number_procbdy Tproc_referencing_glob 0). *)
(*   Definition proc_referencing_glob2 := fst (number_procbdy Tproc_referencing_glob2 0). *)

(*   Definition frame0:CompilEnv.frame := (0, (4,4%Z) :: nil). *)
(*   Definition frame1:CompilEnv.frame := (2, (4,4%Z) :: nil). *)
(*   Definition stbl_referencing_glob := update_lvars (stbl_of_proc proc_referencing_glob2) [(4,(In_Out, Integer))]. *)

(*   Eval compute in transl_procedure_body stbl_referencing_glob (frame0::empty_CE) 1 proc_referencing_glob2 . *)


(*   Require Import examples_spark.proc1. *)

(*   Eval compute in *)
(*       do bstbl <- reduce_stbl Symbol_Table ; *)
(*     match Coq_AST_Tree with *)
(*       | D_Procedure_Body _ x => transl_procedure_body bstbl nil 0 x *)
(*       | _ => Error(msg "cannot compile this declaration") *)
(*     end . *)


(*   Definition empty_program:program := *)
(*     {| *)
(*       AST.prog_defs := nil; *)
(*       AST.prog_main := xH *)
(*     |}. *)

(*   Eval compute in *)
(*       do bstbl <- reduce_stbl Symbol_Table ; *)
(*     transl_global_declaration bstbl Coq_AST_Tree empty_program. *)


(* End examples. *)



