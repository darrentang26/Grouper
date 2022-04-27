module L = Llvm

open Ast
open Sast

module StringMap = Map.Make(String)

let translate (typ_decls, fns, letb) =
  let context = L.global_context () in 

  let gamma = List.fold_left (fun env (name, texpr) -> StringMap.add name texpr env) 
  StringMap.empty 
  typ_decls in 

  let i32_t     = L.i32_type    context 
  and i8_t      = L.i8_type     context 
  and i1_t      = L.i1_type     context
  and float_t   = L.double_type context
  and void_t    = L.void_type   context 
  and string_t  = L.pointer_type (L.i8_type context) 
  and struct_t fields = L.struct_type context fields in
  let list_node = L.struct_type context [| L.pointer_type i8_t; L.pointer_type i8_t |] in
  let list_node_p = L.pointer_type list_node in
  let double_ptr ty = (L.pointer_type (L.pointer_type ty)) in
  (*let _ = L.struct_set_body list_node [| L.pointer_type i8_t; L.pointer_type i8_t |] in
  and string_t  = L.pointer_type (L.i8_type context)  *)

  let rec ltype_of_typ = function
      IntExpr -> i32_t
    | BoolExpr -> i1_t
    | FloatExpr -> float_t
    | VoidExpr -> void_t
    | StringExpr -> string_t
    | TypNameExpr name -> ltype_of_typ (StringMap.find name gamma)
    | StructTypeExpr fields -> struct_t (Array.of_list (List.map (fun (_, typ) -> 
                                                        ltype_of_typ typ) fields))
    | ListType tau -> list_node_p
    | EmptyListType -> list_node_p
    | PairType (tau1, tau2) -> struct_t [| (ltype_of_typ tau1); (ltype_of_typ tau2) |]
    | FunType (ParamType pts, rt) -> L.pointer_type (L.function_type (ltype_of_typ rt) (Array.of_list (List.map ltype_of_typ pts)))
    | ty -> raise (Failure ("type not implemented: " ^ string_of_type_expr ty))

 
  (*let rec ltype_of_list = function
      (_, SConsExpr((t1, e1), (t2, e2))) -> 
        let tau1 = match t1 with 
          ListType _ -> ltype_of_list (t1, e1)
          | _        -> ltype_of_typ t1
        in struct_t [| tau1; L.pointer_type (ltype_of_list (t2, e2)) |]
    | (_, SEmptyListExpr) -> L.pointer_type i8_t*)



  and ltype_of_functionty ty = (match ty with
      FunType (ParamType pts, rt) -> L.function_type (ltype_of_typ rt) (Array.of_list (List.map ltype_of_typ pts))
    | _ -> raise (Failure ("cannot create function of non function type " ^ string_of_type_expr ty)))

  and grp_module = L.create_module context "Grouper" in

  let print_t : L.lltype = 
    L.var_arg_function_type i32_t [| L.pointer_type i8_t |] in
  let print_func : L.llvalue = 
    L.declare_function "printf" print_t grp_module in 

  (* create user function builders *)
  let create_function user_functions (((name, ty), (t', body)) : bind * sexpr) =
    let fun_type = ltype_of_functionty ty in
    let fun_defn = L.define_function (name ^ ".fun") fun_type grp_module in
    let fun_builder = L.builder_at_end context (L.entry_block fun_defn)
      in StringMap.add name (fun_type, fun_defn, fun_builder) user_functions in
  let user_functions = List.fold_left create_function StringMap.empty fns in

  let create_fp user_fps (((name, ty), (t', body)) : bind * sexpr) =
    let (_, fun_defn, _) = StringMap.find name user_functions in
    let gloabl_fp = L.define_global name fun_defn grp_module
      in StringMap.add name gloabl_fp user_fps in
  let user_fps = List.fold_left create_fp StringMap.empty fns in

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
  (*| SStructInit binds -> L.const_struct context 
                           (Array.of_list (List.map (fun (_, bound) ->
                                                       match bound with
                                                        (typ, SName name) -> StringMap.find name scope
                                                       | _ -> expr builder scope gamma bound) binds))*)
  | SStructInit binds ->
      let struct_name = match t with 
        TypNameExpr(name) -> name
      | _ -> raise (Failure "Initializing a non-struct(?)") in
      let curr_struct_type =  ltype_of_typ (StringMap.find struct_name gamma) in
      let undef_struct = L.build_malloc curr_struct_type
                                    struct_name
                                    builder in
      let init_struct = L.build_pointercast undef_struct (L.pointer_type curr_struct_type) struct_name builder in
      let rec add_elem curr_idx = function
        (typ, value)::rest -> 
          let _ = add_elem (curr_idx + 1) rest in
          let field_ptr = L.build_struct_gep init_struct 
                                             curr_idx 
                                             (struct_name ^ "." ^ typ) 
                                             builder in
            L.build_store (expr builder scope gamma value) field_ptr builder
      | [] -> init_struct in
        let _ = add_elem 0 binds in L.build_load init_struct "" builder
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
      let v1 = expr builder scope gamma (t1, e1) in
      let v2 = expr builder scope gamma (t2, e2) in
      
      let ptr = L.build_malloc list_node "Cons2" builder in
      (*let () = print_string "wow " in*)
      let ptr_cast = L.build_pointercast ptr list_node_p "Cons" builder in
      let data = L.build_struct_gep ptr_cast 0 "Data_p" builder in
      let next = L.build_struct_gep ptr_cast 1 "Next_p" builder in
      (*let data = L.build_load p1 "Data" builder in*)
      let data_c = L.build_pointercast data (double_ptr (ltype_of_typ t1)) "Data_c" builder in
      let d_ptr = L.build_malloc (ltype_of_typ t1) "D_ptr" builder in
      let _ = L.build_store v1 d_ptr builder in
      let _ = L.build_store d_ptr data_c builder in
      (*let next = L.build_load p2 "Next" builder in*)
      let next_c = L.build_pointercast next (L.pointer_type list_node_p) "Next_c" builder in
      let _ = L.build_store v2 next_c builder in
      ptr_cast
      (*L.const_struct context [| v1; ptr|]*)
  | SEmptyListExpr ->
      L.const_pointer_null list_node_p 
  | SPairExpr (sexp1, sexp2) -> L.const_struct context
                                  (Array.of_list 
                                    (List.map 
                                      (fun (sexp) -> expr builder scope gamma sexp) 
                                    [sexp1; sexp2]))
  | SCarExpr ((t, e)) -> (match t with
      PairType (t1, t2) ->
          let v = (match e with 
                      SName name -> StringMap.find name scope
                    | _ -> expr builder scope gamma (t, e)) in
          let pr = L.build_struct_gep v 0 "pair.fst" builder in
          L.build_load pr "pair.fst" builder
    | ListType tau ->
          let node = expr builder scope gamma (t, e) in
          let pr = L.build_struct_gep node 0 "List.car" builder in
          let data = L.build_load pr "Data" builder in
          let data_c = L.build_pointercast data (L.pointer_type (ltype_of_typ tau)) "Data_c" builder in
          L.build_load data_c "Data" builder)
  | SCdrExpr ((t, e)) -> (match t with
      PairType (t1, t2) ->
        let v = (match e with
                    SName name -> StringMap.find name scope
                  | _ -> expr builder scope gamma (t, e)) in
        let pr = L.build_struct_gep v 1 "pair.snd" builder in
        L.build_load pr "pair.fst" builder
      | ListType _ ->
          let node = expr builder scope gamma (t, e) in
          let pr = L.build_struct_gep node 1 "List.cdr" builder in
          let next = L.build_load pr "Next" builder in
          L.build_pointercast next list_node_p "Next_c" builder)
  | SPrint (typ, sx) -> 
      let int_format_str = L.build_global_stringptr "%d\n" "fmt" builder in
      let float_format_str = L.build_global_stringptr "%g\n" "fmt" builder in let 
      value = expr builder scope gamma (typ, sx) in                          
      (match typ with 
        StringExpr -> let
          str = L.build_in_bounds_gep value [| (L.const_int i32_t 0) |] "" builder in let
          _ = L.build_call print_func [| str |] "printf" builder 
          in value
      | IntExpr -> L.build_call print_func [| int_format_str ;  value |] "printf" builder
      | FloatExpr -> L.build_call print_func [| float_format_str ; value|] "printf" builder
      | BoolExpr -> let
          lbool = L.string_of_llvalue value in
          if lbool = "i1 true" then expr builder scope gamma (StringExpr, SPrint(StringExpr, SStringLit "true"))
          else expr builder scope gamma (StringExpr, SPrint(StringExpr, SStringLit "false"))
      (*| StructTypeExpr fields ->*)
      | _ -> raise (Failure ("printing of " ^ (string_of_type_expr typ) ^ " is not yet implemented")))
  
  (*| SPrint sexpr -> (match sexpr with 
     (StringExpr, sx) -> let
        value = expr builder scope gamma (StringExpr, sx) 
          (* in let sval = match (L.string_of_const value) with
                          Some s -> s
                        | None -> "" *)
          (*in let sval = value*)
          in let str = L.build_in_bounds_gep value [| (L.const_int i32_t 0) |] "" builder
          in let _ = L.build_call print_func [| str |] "printf" builder
            in value
    | _ -> raise (Failure "not yet implemented-- print only expects strings"))*)
  | SName name -> (match t with
      FunType _ -> let
        global_lookup = L.lookup_global name grp_module
          in (match global_lookup with
            Some global ->
              (* global *)
              L.build_load global name builder
          | None -> L.build_load (StringMap.find name scope) name builder)
    | _ -> L.build_load (StringMap.find name scope) name builder)
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
  | SCall (fun_sexpr, params) ->
    let fun_value = expr builder scope gamma fun_sexpr in
    let param_values = Array.of_list (List.map (expr builder scope gamma) params)
      in L.build_call fun_value param_values "" builder
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

  
in let populate_function fun_type fun_defn fun_builder sexpr =
  let add_formal scope (name, ty) param =
    let local = L.build_alloca (ltype_of_typ ty) "" fun_builder in
    let _ = L.build_store param local fun_builder in
      (StringMap.add name local scope)
  
  in match sexpr with (_, SFunction (binds, body)) -> 
    let params = Array.to_list (L.params fun_defn)

    in let scope = List.fold_left2 add_formal StringMap.empty binds params
    in let value = expr fun_builder scope gamma body
      in L.build_ret value fun_builder

in let _ = List.map
  (fun (((name, _), sexpr) : bind * sexpr) ->
    let (fun_type, fun_defn, fun_builder) = StringMap.find name user_functions
      in populate_function fun_type fun_defn fun_builder sexpr)
  fns

in let _ = expr main_builder StringMap.empty gamma letb
in let _ = L.build_ret (L.const_int i32_t 0) main_builder
in grp_module 