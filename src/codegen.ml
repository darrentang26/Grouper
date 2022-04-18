module L = Llvm

open Ast
open Sast

module StringMap = Map.Make(String)

let translate (typ_decls, letb) =
  let context = L.global_context () in 

  let gamma = List.fold_left (fun env (name, texpr) -> StringMap.add name texpr env) 
  StringMap.empty 
  typ_decls in 

  let i32_t     = L.i32_type    context 
  and i8_t      = L.i8_type     context 
  and i1_t      = L.i1_type     context
  and float_t   = L.double_type context
  and void_t    = L.void_type   context 
  and struct_t fields = L.struct_type context fields in
  (* and string_t  = L.pointer_type (L.i8_type context)  *)

  
  let rec ltype_of_typ = function
      IntExpr -> i32_t
    | BoolExpr -> i1_t
    | FloatExpr -> float_t
    | VoidExpr -> void_t
    | TypNameExpr name -> ltype_of_typ (StringMap.find name gamma)
    | StructTypeExpr fields -> struct_t (Array.of_list (List.map (fun (_, typ) -> 
                                                        ltype_of_typ typ) fields))
    | ListType tau -> struct_t [| (ltype_of_typ tau); L.pointer_type i8_t |]
    | EmptyListType -> L.pointer_type i8_t
    | PairType (tau1, tau2) -> struct_t [| (ltype_of_typ tau1); (ltype_of_typ tau2) |]
    | ty -> raise (Failure ("type not implemented: " ^ string_of_type_expr ty))

in 
  let rec ltype_of_list = function
      (_, SConsExpr((t1, e1), (t2, e2))) -> 
        let tau1 = match t1 with 
          ListType _ -> ltype_of_list (t1, e1)
          | _        -> ltype_of_typ t1
        in struct_t [| tau1; L.pointer_type (ltype_of_list (t2, e2)) |]
    | (_, SEmptyListExpr) -> L.pointer_type i8_t



  and grp_module = L.create_module context "Grouper" in

  let print_t : L.lltype = 
    L.var_arg_function_type i32_t [| L.pointer_type i8_t |] in
  let print_func : L.llvalue = 
    L.declare_function "printf" print_t grp_module in 

  let main_type = L.function_type i32_t (Array.make 0 i32_t) in
  let main_defn = L.define_function "main" main_type grp_module in 
  let main_builder = L.builder_at_end context (L.entry_block main_defn) in

  let add_terminal builder instr =
    match L.block_terminator (L.insertion_block builder) with
      Some _ -> ()
    | None -> ignore (instr builder) in

  let rec expr builder scope gamma ((t,e) : sexpr) = match e with
    SLiteral i -> L.const_int i32_t i
  | SBoolLit b -> L.const_int i1_t (if b then 1 else 0)
  | SFliteral l -> L.const_float_of_string float_t l
  | SStringLit str -> L.build_global_stringptr str "" builder
  | SStructInit binds -> L.const_struct context 
                           (Array.of_list (List.map (fun (_, bound) -> expr builder scope gamma bound) binds))
  | SStructRef (var, field) -> let
      struct_name = match (StringMap.find var gamma ) with 
                       TypNameExpr(typ_name) -> typ_name 
                    |  _ -> raise (Failure "Should not happen, non-struct name accessed should be caught in semant") in let
      struct_def = StringMap.find struct_name gamma in let rec
      idx_finder curr_idx = function
        (curr_field, _)::binds -> if field = curr_field then curr_idx else 
                                   idx_finder (curr_idx + 1) binds
      | [] -> raise (Failure "Should not happen, invalid field lookup should be caught in semant") in let
      field_idx = match struct_def with 
                    StructTypeExpr(struct_binds) -> idx_finder 0 struct_binds
                  | _ -> raise (Failure "Should not happen, non-struct type should be caught in semant") in 
        let lstruct = (StringMap.find var scope) in
        L.build_load (L.build_struct_gep lstruct field_idx (var ^ "." ^ field) builder) (var ^ "." ^ field) builder
        
  | SConsExpr ((t1, e1), (t2, e2)) ->
      let ptr = L.build_alloca (ltype_of_list (t2, e2)) "cons" builder
      in let _ = L.build_store (expr builder scope gamma (t2, e2)) ptr builder in
      L.const_struct context [| expr builder scope gamma (t1, e1);  
                                ptr|]
  | SPairExpr (sexp1, sexp2) -> L.const_struct context
                                  (Array.of_list 
                                    (List.map 
                                      (fun (sexp) -> expr builder scope gamma sexp) 
                                    [sexp1; sexp2]))
  | SCarExpr ((t, e)) -> (match t with
        PairType (t1, t2) ->
          let pr = expr builder scope gamma (t, e) in
          (*let _ = raise (Failure "then") in*)
          let p = L.build_struct_gep pr 0 "pair.fst" builder in
          let _ = raise (Failure "now") in
          L.build_load p "pair.cfst" builder
      | ListType _ -> 
      (*raise (Failure "Got to car")*)
      L.build_load (L.build_struct_gep (expr builder scope gamma (t, e)) 0 "car" builder) "car2" builder
      (*raise (Failure "Got past load")*))
  | SCdrExpr (sexp) ->
      L.build_load (
        L.build_load (
          L.build_struct_gep (expr builder scope gamma sexp) 1 "ptr" builder) 
        "ptr" builder)
      "cdr" builder
  | SEmptyListExpr ->
      L.const_pointer_null i8_t           
  | SPrint sexpr -> (match sexpr with
      (StringExpr, sx) -> let
        value = expr builder scope gamma (StringExpr, sx) 
          (* in let sval = match (L.string_of_const value) with
                          Some s -> s
                        | None -> "" *)
          in let sval = value
          in let str = L.build_in_bounds_gep sval [| (L.const_int i32_t 0) |] "" builder
          in let _ = L.build_call print_func [| str |] "printf" builder
            in value
    | _ -> raise (Failure "not yet implemented-- print only expects strings"))
  | SName name -> L.build_load (StringMap.find name scope) name builder
  | SBinop ((tl, sl), op, (tr, sr)) -> let
    left = expr builder scope gamma (tl, sl) and
    right = expr builder scope gamma (tr, sr)
    in (match op, tl with
      (Add, IntExpr)        -> L.build_add left right "" builder
    | (Add, FloatExpr)      -> L.build_fadd left right "" builder
    | (Add, StringExpr)     -> raise (Failure "not yet implemented-- string concatenation")
        (* left = L.build_load left "" builder and
        right = L.build_load right "" builder in let
        left_type = L.type_of left and
        right_type = L.type_of right in let
        left_length = L.size_of left_type and
        right_length = L.size_of right_type in let

          combined_length = L.build_add left_length right_length "" builder
        in let
          (* dest_length = L.build_sub combined_length (L.const_int i32_t 1) "" builder  *)
          dest_length = L.const_int i32_t 3
        in let
          dest_size = (L.array_length left_type) + (L.array_length right_type) - 1
        in let
          dest_type = L.array_type i8_t dest_size
        in let
          dest_first_ptr = L.build_array_malloc i8_t dest_length "" builder 
        in let
          dest_second_offset = L.build_sub combined_length right_length "" builder 
        in let
          dest_first = L.build_store left dest_first_ptr builder 
        in let dest_second_ptr = L.ptrtoint i8_t dest_first_ptr + 
        (* in let *)
          (* dest_second_ptr = L.build_gep dest_second_offset [| dest_first_ptr |] "" builder *)
        (* in let *)
          (* dest_second = L.build_store right dest_second_ptr builder *)
            (* in dest_first_ptr *)
            in right *)
    | (Sub, IntExpr)        -> L.build_sub left right "" builder
    | (Sub, FloatExpr)      -> L.build_fsub left right "" builder
    | (Mult, IntExpr)       -> L.build_mul left right "" builder
    | (Mult, FloatExpr)     -> L.build_fmul left right "" builder
    | (Div, IntExpr)        -> L.build_sdiv left right "" builder
    | (Div, FloatExpr)      -> L.build_fdiv left right "" builder
    | (Equal, IntExpr)      -> L.build_icmp L.Icmp.Eq left right "" builder
    | (Equal, FloatExpr)    -> L.build_fcmp L.Fcmp.Ueq left right "" builder (* not quite sure how this works... *)
    | (Equal, StringExpr)   -> raise (Failure "not yet implemented-- string equality")
    | (Neq, IntExpr)        -> L.build_icmp L.Icmp.Ne left right "" builder
    | (Neq, FloatExpr)      -> L.build_fcmp L.Fcmp.Une left right "" builder (* not quite sure how this works... *)
    | (Less, IntExpr)       -> L.build_icmp L.Icmp.Slt left right "" builder
    | (Less, FloatExpr)     -> L.build_fcmp L.Fcmp.Ult left right "" builder (* not quite sure how this works... *)
    | (Leq, IntExpr)        -> L.build_icmp L.Icmp.Sle left right "" builder
    | (Leq, FloatExpr)      -> L.build_fcmp L.Fcmp.Ule left right "" builder (* not quite sure how this works... *)
    | (Greater, IntExpr)    -> L.build_icmp L.Icmp.Sgt left right "" builder
    | (Greater, FloatExpr)  -> L.build_fcmp L.Fcmp.Ugt left right "" builder (* not quite sure how this works... *)
    | (Geq, IntExpr)        -> L.build_icmp L.Icmp.Sge left right "" builder
    | (Geq, FloatExpr)      -> L.build_fcmp L.Fcmp.Uge left right "" builder (* not quite sure how this works... *)
    | (And, BoolExpr)       -> L.build_and left right "" builder
    | (Or, BoolExpr)        -> L.build_or left right "" builder
    | (Mod, IntExpr)        -> L.build_srem left right "" builder)
  | SUnop (uop, (ty, sx)) -> let
    value = expr builder scope gamma (ty, sx)
    in (match uop, ty with
      (Neg, IntExpr)  -> L.build_neg value "" builder
    | (Neg, FloatExpr)-> L.build_fneg value "" builder
    | (Not, BoolExpr) -> L.build_not value "" builder)
  | SLet (binds, body) -> let
    store_typ gamma ((name, ty), sexpr) = (StringMap.add name ty gamma) in let
    store_val scope ((name, ty), sexpr) = let
      local = L.build_alloca (ltype_of_typ ty) "" builder in let
      value = expr builder scope gamma sexpr in let
      _ = L.build_store value local builder in
        (StringMap.add name local scope) in let
    scope' = List.fold_left 
        store_val
        scope
        binds in let 
    gamma' = List.fold_left store_typ gamma binds
      in   
      expr builder scope' gamma' body
  | SIf (cond_sexpr, then_sexpr, else_sexpr) ->
    let cond_value = expr builder scope gamma cond_sexpr
    in let start_bb = L.insertion_block builder
    in let the_function = L.block_parent start_bb

    in let then_bb = L.append_block context "then" the_function
    in let _ = L.position_at_end then_bb builder
    in let then_value = expr builder scope gamma then_sexpr
    in let then_bb = L.insertion_block builder

    in let else_bb = L.append_block context "else" the_function
    in let _ = L.position_at_end else_bb builder
    in let else_value = expr builder scope gamma else_sexpr
    in let else_bb = L.insertion_block builder

    in let merge_bb = L.append_block context "ifcont" the_function
    in let _ = L.position_at_end merge_bb builder
    in let incoming = [(then_value, then_bb); (else_value, else_bb)]
    in let phi = L.build_phi incoming "iftmp" builder

    in let _ = L.position_at_end start_bb builder
    in let _ = L.build_cond_br cond_value then_bb else_bb builder

    in let _ = L.position_at_end then_bb builder
    in let _ = L.build_br merge_bb builder

    in let _ = L.position_at_end else_bb builder
    in let _ = L.build_br merge_bb builder

    in let _ = L.position_at_end merge_bb builder in phi
  | _ -> raise (Failure ("sexpr " ^ (Sast.string_of_sexpr (t,e)) ^ " not yet implemented"))
in let _ = expr main_builder StringMap.empty gamma letb
in let _ = L.build_ret (L.const_int i32_t 0) main_builder
in grp_module 