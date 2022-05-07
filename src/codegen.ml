module L = Llvm

open Ast
open Sast

module StringMap = Map.Make(String)

exception Failure of string

let idx_lookup field fs =
  List.fold_right (fun name acc ->
                      if acc > 0 then acc + 1 
                                 else if name == field then 1
                                                       else 0)
                  fs 0
(* FIELDMOD *)
let group_names = ["zero"; "equals"; "plus"; "neg"; "minus"]
let field_names = group_names @ ["one"; "times"; "inv"; "div"; "pow"; "make_poly"; 
                                 "poly_deg"; "poly_eval"; "poly_equals"; 
                                 "poly_plus"; "poly_minus"; "poly_neg"; "poly_times"; 
                                 "poly_div"; "poly_mod"; "poly_gcd"]
let ring_names = group_names @ ["one"; "times"; "div"; "mod"; "gcd"; "pow"]


let compare_type ty = FunType (ParamType [ty; ty], BoolExpr)
let binop_type ty = FunType (ParamType [ty; ty], ty)
let poly_binop_type ty = FunType (ParamType [PolyType ty; PolyType ty; ty], PolyType ty)
let unop_type ty = FunType (ParamType [ty], ty)
let poly_unop_type ty = FunType (ParamType [PolyType ty; PolyType ty; ty], PolyType ty)
let mpoly_type ty = FunType (ParamType [ListType ty], PolyType ty)
let pdeg_type ty = FunType (ParamType [PolyType ty], IntExpr)
let gcd_type ty = FunType (ParamType [ty; ty; ty], ty)
let pow_type ty = FunType (ParamType [ty; IntExpr], ty)
let eval_type ty = FunType (ParamType [PolyType ty; ty], ty)

let group_list ty = [("zero", ty); ("equals", compare_type ty); ("plus", binop_type ty);
                    ("neg", unop_type ty); ("minus", binop_type ty)]
let group_to_struct ty = StructTypeExpr (group_list ty)

let field_list ty = (group_list ty) @ [("one", ty); ("times", binop_type ty); 
                       ("inv", unop_type ty); ("div", binop_type ty); ("pow", pow_type ty);
                       ("make_poly", mpoly_type ty); ("poly_deg", pdeg_type ty);
                       ("poly_eval", eval_type ty);
                       ("poly_equals", compare_type (PolyType ty));
                       ("poly_plus", poly_binop_type ty);
                       ("poly_minus", poly_binop_type ty);
                       ("poly_neg", unop_type (PolyType ty));
                       ("poly_times", poly_binop_type ty);
                       ("poly_div", poly_binop_type ty);
                       ("poly_mod", poly_binop_type ty);
                       ("poly_gcd", poly_binop_type ty)]
let ring_list ty = (group_list ty) @ [("one", ty); ("times", binop_type ty); 
                       ("div", binop_type ty); ("mod", binop_type ty);
                       ("gcd", gcd_type ty); ("pow", pow_type ty)]
let field_to_struct ty = StructTypeExpr (field_list ty)
let ring_to_struct ty = StructTypeExpr (ring_list ty)

let translate (typ_decls, fns, letb) =
  let context = L.global_context () in 

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

  let gamma = List.fold_left
    (fun env (name, texpr) -> StringMap.add name texpr env) 
    StringMap.empty 
    typ_decls in

  let rho = List.fold_left 
    (fun env (name, texpr) -> match texpr with
      AdtTypeExpr (binds) -> (match (List.fold_left
        (fun (env, enum) (adtname, ty) ->
          (StringMap.add adtname (enum, ty) env, enum + 1))
        (env, 0)
        binds) with (env, _) -> env)
      | _ -> env)
    StringMap.empty
    typ_decls in

  let max x1 x2 = if x1 > x2 then x1 else x2 in
  
  let rec ltype_of_typ = function
      IntExpr -> i32_t
    | BoolExpr -> i1_t
    | FloatExpr -> float_t
    | VoidExpr -> void_t
    | StringExpr -> string_t
    | TypNameExpr name -> ltype_of_typ (try StringMap.find name gamma with Not_found -> raise (Failure ("unknown type: " ^ name)))
    | AdtTypeExpr binds -> struct_t [| i8_t ; L.pointer_type i8_t |]
    | StructTypeExpr fields -> struct_t (Array.of_list (List.map (fun (_, typ) -> ltype_of_typ typ) fields))
    | ListType tau -> list_node_p
    | EmptyListType -> list_node_p
    | PolyType tau -> ltype_of_typ (ListType tau)
    | PairType (tau1, tau2) -> L.pointer_type (struct_t [| (ltype_of_typ tau1); (ltype_of_typ tau2) |])
    | FunType (ParamType pts, rt) -> L.pointer_type (L.function_type (ltype_of_typ rt) (Array.of_list (List.map ltype_of_typ pts)))
    | GroupType ty -> ltype_of_typ (group_to_struct ty)
    | FieldType ty -> ltype_of_typ (field_to_struct ty)
    | RingType ty -> ltype_of_typ (ring_to_struct ty)
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

  let exit_t = L.function_type void_t [| i32_t |] in
  let exit_func = L.declare_function "exit" exit_t grp_module in

  (* create user function builders *)
  let create_function user_functions (((name, ty), (t', body)) : bind * sexpr) =
    let fun_type = ltype_of_functionty ty in
    let fun_defn = L.define_function (name ^ ".fun") fun_type grp_module in
    let fun_builder = L.builder_at_end context (L.entry_block fun_defn)
      in StringMap.add name (fun_type, fun_defn, fun_builder) user_functions in
  let user_functions = List.fold_left create_function StringMap.empty fns in

  let create_fp user_fps (((name, ty), (t', body)) : bind * sexpr) =
    let (_, fun_defn, _) = (try StringMap.find name user_functions with Not_found -> raise (Failure ("cannot find function: " ^ name))) in 
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
      let struct_name = (match t with 
        TypNameExpr name -> name
      | StructTypeExpr field -> ""
      | GroupType ty -> "group"
      | FieldType ty -> "field"
      | RingType ty -> "ring"
      | _ -> raise (Failure "Initializing a non-struct(?)")) in
      let struct_type = (match t with 
        TypNameExpr name -> (try StringMap.find name gamma with Not_found -> raise (Failure ("cannot find type: " ^ name)))
      | StructTypeExpr fields -> t
      | GroupType ty -> group_to_struct ty
      | FieldType ty -> field_to_struct ty
      | RingType ty -> ring_to_struct ty
      | _ -> raise (Failure "Initializing a non-struct(?)")) in
      let curr_struct_type =  ltype_of_typ struct_type in
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
      struct_def = match (try (StringMap.find var gamma) with Not_found -> raise (Failure var)) with 
                      TypNameExpr(typ_name) -> (try StringMap.find typ_name gamma with Not_found -> raise (Failure typ_name))
                    | GroupType ty -> group_to_struct ty
                    | FieldType ty -> field_to_struct ty
                    | RingType ty -> ring_to_struct ty
                    |  _ -> raise (Failure "Should not happen, non-struct name accessed should be caught in semant") in 
      let rec idx_finder curr_idx = function
            (curr_field, _)::binds -> if field = curr_field 
                                      then curr_idx 
                                      else idx_finder (curr_idx + 1) binds
      | [] -> raise (Failure "Should not happen, invalid field lookup should be caught in semant") in let
      field_idx = match struct_def with 
                    StructTypeExpr(struct_binds) -> idx_finder 0 struct_binds
                  | GroupType ty -> idx_lookup field group_names
                  | FieldType ty -> idx_lookup field field_names
                  | RingType ty -> idx_lookup field ring_names
                  | _ -> raise (Failure "Should not happen, non-struct type should be caught in semant") in 
        let lstruct = (try (StringMap.find var scope) with Not_found -> raise (Failure var)) in
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
  | SPairExpr ((t1, e1), (t2, e2)) -> 
    let v1 = expr builder scope gamma (t1, e1) in
    let v2 = expr builder scope gamma (t2, e2) in
    let pair_type = struct_t [|ltype_of_typ t1; ltype_of_typ t2|] in
    let pair = L.build_malloc pair_type "Pair" builder in
    let pair_c = L.build_pointercast pair (L.pointer_type pair_type) "Pair_c" builder in
    let fst_ptr = L.build_struct_gep pair_c 0 "Fst_p" builder in
    let _ = L.build_store v1 fst_ptr builder in
    let snd_ptr = L.build_struct_gep pair_c 1 "Snd_p" builder in
    let _ = L.build_store v2 snd_ptr builder in 
    pair_c
  (*L.const_struct context
                                  (Array.of_list 
                                    (List.map 
                                      (fun (sexp) -> expr builder scope gamma sexp) 
                                    [sexp1; sexp2]))*)
  | SCarExpr ((t, e)) -> (match t with
      PairType (t1, t2) ->
          let v = expr builder scope gamma (t, e) in
          let pr = L.build_struct_gep v 0 "pair.fst" builder in
          L.build_load pr "pair.fst" builder
    | ListType tau | PolyType tau ->
          let node = expr builder scope gamma (t, e) in
          let pr = L.build_struct_gep node 0 "List.car" builder in
          let data = L.build_load pr "Data" builder in
          let data_c = L.build_pointercast data (L.pointer_type (ltype_of_typ tau)) "Data_c" builder in
          L.build_load data_c "Data" builder)
  | SCdrExpr ((t, e)) -> (match t with
      PairType (t1, t2) ->
        let v = expr builder scope gamma (t, e) in
        let pr = L.build_struct_gep v 1 "pair.snd" builder in
        L.build_load pr "pair.fst" builder
      | ListType _ | PolyType _ ->
          let node = expr builder scope gamma (t, e) in
          let pr = L.build_struct_gep node 1 "List.cdr" builder in
          let next = L.build_load pr "Next" builder in
          L.build_pointercast next list_node_p "Next_c" builder)
  | SPrint (typ, sx) -> 
      let int_format_str = L.build_global_stringptr "%d" "fmt" builder in
      let float_format_str = L.build_global_stringptr "%g" "fmt" builder in
      let bool_format_str = L.build_global_stringptr "b%d" "fmt" builder in let
      value = expr builder scope gamma (typ, sx) in                          
      (match typ with 
        StringExpr -> let
          str = L.build_in_bounds_gep value [| (L.const_int i32_t 0) |] "" builder in let
          _ = L.build_call print_func [| str |] "printf" builder 
          in value
      | IntExpr -> let _ = L.build_call print_func [| int_format_str ;  value |] "printf" builder in value
      | FloatExpr -> let _ = L.build_call print_func [| float_format_str ; value|] "printf" builder in value
      | BoolExpr -> let _ = L.build_call print_func [|bool_format_str ; value|] "printf" builder in value
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
          | None -> L.build_load (try (StringMap.find name scope) with Not_found -> raise (Failure name)) name builder)
    | _ -> L.build_load (try (StringMap.find name scope) with Not_found -> raise (Failure ("unbound variable " ^ name))) name builder)
  | SBinop ((tl, sl), op, (tr, sr)) -> let
    left = expr builder scope gamma (tl, sl) and
    right = expr builder scope gamma (tr, sr) in
    let unalias = function 
      TypNameExpr name -> (try StringMap.find name gamma with Not_found -> raise (Failure ("cannot find aliased function: " ^ name)))
    | typ -> typ
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
    | (Equal, StructTypeExpr fields) -> (*raise (Failure ("left: " ^ (L.string_of_llvalue left)))*)
      let left_ptr = L.build_alloca (ltype_of_typ (StructTypeExpr fields)) "left" builder in
      let right_ptr = L.build_alloca (ltype_of_typ (StructTypeExpr fields)) "right" builder in
      let left_store = L.build_store left left_ptr builder in
      let right_store = L.build_store right right_ptr builder in 
      let type_order = List.map (fun (name, typ) -> typ) fields in
      let rec load_fields lstruct idx = function
        IntExpr::rest | FloatExpr::rest -> (L.build_load (L.build_struct_gep lstruct idx "" builder) "" builder)::(load_fields lstruct (idx + 1) rest)
      | typ::rest -> raise (Failure ("(struct equality) cannot check equality of " ^ (string_of_type_expr typ)))
      | [] -> [] in
      let left_loads = load_fields left_ptr 0 type_order in
      let right_loads = load_fields right_ptr 0 type_order in
      let rec cmp_left_right (left_list, right_list, typs) = match (left_list, right_list, typs) with
        (left_val::lrest, right_val::rrest, typ::trest) -> 
          let cmp_fn = match typ with
            IntExpr -> L.build_icmp L.Icmp.Eq
          | FloatExpr -> L.build_fcmp L.Fcmp.Ueq
          | _ -> raise (Failure "Other types should not be present") in
            (cmp_fn left_val right_val "" builder)::(cmp_left_right (lrest, rrest, trest))
      | ([], [], []) -> []
      | _ -> raise (Failure "unequal list lengths in struct equality check (somehow)") in
      let cmpd_values = cmp_left_right (left_loads, right_loads, type_order) in
      let rec build_ands = function
         [] -> raise (Failure "There's literally no way the list can be empty")
      |  val1::[] -> val1
      |  val1::rest -> L.build_and val1 (build_ands rest) "" builder 
       in
      build_ands cmpd_values  
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
    | (Not, BoolExpr) -> L.build_not value "" builder
    | (Null, EmptyListType) -> L.const_int i1_t 1
    | (Null, ListType tau) -> L.build_is_null value "" builder)
  | SLet (binds, body) -> let
    store_typ gamma ((name, ty), sexpr) = (StringMap.add name ty gamma) in let
    store_val scope' ((name, ty), sexpr) = let
      local = L.build_alloca (ltype_of_typ ty) "" builder in let
      value = expr builder scope gamma sexpr in let
      _ = L.build_store value local builder in
        (StringMap.add name local scope') in let
    scope' = List.fold_left 
        store_val
        scope
        binds in let 
    gamma' = List.fold_left store_typ gamma binds
      in   
      expr builder scope' gamma' body
  | SAdtExpr target -> (match target with
      STargetWildName name ->
        let (enum, _) = (try StringMap.find name rho with Not_found -> raise (Failure ("cannot find definition for ADT constructor (no arguments): " ^ name))) in
        let target_type = ltype_of_typ t in
        let location = L.build_alloca target_type name builder in
        let enum_location = L.build_struct_gep location 0 (name ^ "-enum") builder in
        let store = L.build_store (L.const_int i8_t enum) enum_location builder
          in L.build_load location "" builder
    | STargetWildApp (name, STargetWildLiteral sexpr) -> 
        let (enum, ty) = (try StringMap.find name rho with Not_found -> raise (Failure ("cannot find definition for ADT constructor: " ^ name))) in
        let target_type = ltype_of_typ t in
        let location = L.build_alloca target_type name builder in
        let enum_location = L.build_struct_gep location 0 (name ^ "-enum") builder in
        let _ = L.build_store (L.const_int i8_t enum) enum_location builder in
        let value_location = L.build_struct_gep location 1 (name ^ "-value") builder in
        let value_location = L.build_pointercast value_location (L.pointer_type (L.pointer_type (ltype_of_typ ty))) "" builder 
        in let value_location_alloca = L.build_alloca (ltype_of_typ ty) "" builder
        in let _ = L.build_store (expr builder scope gamma sexpr) value_location_alloca builder
        in let _ = L.build_store value_location_alloca value_location builder
          in L.build_load location "" builder)
  | SCall (fun_sexpr, params) ->
      let fun_value = expr builder scope gamma fun_sexpr in
      let param_values = Array.of_list (List.map (expr builder scope gamma) params)
        in L.build_call fun_value param_values "" builder
  | SMatch (binds, bodies) ->
      let match_vals = List.rev_map (fun (name, ty) -> expr builder scope gamma (ty, SName name)) binds
      
      in let start_bb = L.insertion_block builder
      in let the_function = L.block_parent start_bb

      in let default_bb = L.append_block context "matchdefault" the_function
      in let _ = L.position_at_end default_bb builder
      in let _ = L.build_call exit_func [| (L.const_int i32_t 2) |] "" builder 
      in let default_value = L.const_null (ltype_of_typ t)
      in let default_bb = L.insertion_block builder

      in let merge_bb = L.append_block context "matchcont" the_function
      in let _ = L.position_at_end merge_bb builder

      in let _ = L.position_at_end default_bb builder
      in let _ = L.build_br merge_bb builder

      in let (cases, first_bb) = List.fold_left
        (fun (cases, next_bb) (pattern, sexpr) ->
          let targets = match pattern with SPattern (targets) -> targets
          in let target_vals = List.combine targets match_vals

          in let then_bb = L.append_block context "matchthen" the_function
          in let _ = L.position_at_end then_bb builder
          
          in let (cond_value, scope') = List.fold_left
            (fun (cond_value, scope) (target, value) ->
              let (target_cond, scope') =
                let rec codegen_target target value = match target with
                    STargetWildName name -> 
                      let (enum_target, _) = (try StringMap.find name rho with Not_found -> raise (Failure ("(match) cannot find definition for ADT constructor (no arguments): " ^ name)))
                      in let value_location = L.build_alloca (L.type_of value) "" builder
                      in let _ = L.build_store value value_location builder
                      in let enum_target_value = L.const_int i8_t enum_target
                      in let enum_match_location = L.build_struct_gep value_location 0 (name ^ "-enum") builder
                      in let enum_match_value = L.build_load enum_match_location "" builder 
                      in let cond_value = L.build_icmp L.Icmp.Eq enum_target_value enum_match_value ("is-" ^ name) builder
                        in (cond_value, scope)
                  | STargetWildApp (name, STargetWildLiteral sexpr) ->
                      let (enum_target, target_type) = (try StringMap.find name rho with Not_found -> raise (Failure ("(match) cannot find definition for ADT constructor: " ^ name)))
                      in let value_location = L.build_alloca (L.type_of value) "" builder
                      in let _ = L.build_store value value_location builder
                      in let enum_target_value = L.const_int i8_t enum_target
                      in let enum_match_location = L.build_struct_gep value_location 0 (name ^ "-enum") builder
                      in let enum_match_value = L.build_load enum_match_location "" builder
                      in let enum_cond_value = L.build_icmp L.Icmp.Eq enum_target_value enum_match_value ("is-" ^ name) builder
                      in let (sexpr_cond_value, scope') = match sexpr with
                          (ty, SName name_to_bind) ->
                            let target_location = L.build_struct_gep value_location 1 (name ^ "-value") builder
                            in let target_location = L.build_pointercast target_location (L.pointer_type (L.pointer_type (ltype_of_typ ty))) (name ^ "-value-casted") builder
                            in let target_location = L.build_load target_location "" builder
                            in let scope' = StringMap.add name_to_bind target_location scope
                            in let const_int_location = L.build_alloca i1_t "" builder
                            in let _ = L.build_store (L.const_int i1_t 1) const_int_location builder
                              in (L.build_load const_int_location "" builder, scope')
                        | (ty, sx) ->
                            let sexpr_target_value = expr builder scope gamma (ty, sx)
                            in let sexpr_match_location = L.build_struct_gep value_location 1 (name ^ "-value") builder
                            in let sexpr_match_location = L.build_pointercast sexpr_match_location (L.pointer_type (L.pointer_type (L.type_of sexpr_target_value))) (name ^ "-value-casted") builder
                            in let sexpr_match_value = L.build_load sexpr_match_location "value-pointer" builder
                            in let sexpr_match_value = L.build_load sexpr_match_value "value" builder
                            in let sexpr_cond_value = match ty with
                                IntExpr | BoolExpr -> L.build_icmp L.Icmp.Eq sexpr_target_value sexpr_match_value "value-matches" builder
                              | FloatExpr -> L.build_fcmp L.Fcmp.Ueq sexpr_target_value sexpr_match_value "value-matches" builder
                              in (sexpr_cond_value, scope)
                      in let cond_value = L.build_and enum_cond_value sexpr_cond_value "enum-literal-matches" builder
                        in (cond_value, scope')
                  | STargetWildApp (name, inner_target) ->
                      let (enum_target, target_type) = (try StringMap.find name rho with Not_found -> raise (Failure ("(match) cannot find definition for ADT constructor (inner target): " ^ name)))
                      in let value_location = L.build_alloca (L.type_of value) "" builder
                      in let _ = L.build_store value value_location builder

                      in let enum_target_value = L.const_int i8_t enum_target
                      in let enum_match_location = L.build_struct_gep value_location 0 (name ^ "-enum") builder
                      in let enum_match_value = L.build_load enum_match_location "" builder
                      in let enum_cond_value = L.build_icmp L.Icmp.Eq enum_target_value enum_match_value ("is-" ^ name) builder

                      in let target_location = L.build_struct_gep value_location 1 (name ^ "-value") builder
                      in let target_location = L.build_pointercast target_location (L.pointer_type (L.pointer_type (ltype_of_typ target_type))) (name ^ "-value-casted") builder
                      in let target_value = L.build_load target_location "" builder
                      in let target_value = L.build_load target_value "" builder

                      in let (inner_cond_value, scope') = codegen_target inner_target target_value
                        in let cond_value = L.build_and enum_cond_value inner_cond_value "" builder
                          in (cond_value, scope')
                  | SCatchAll ->
                    let const_int_location = L.build_alloca i1_t "" builder
                    in let _ = L.build_store (L.const_int i1_t 1) const_int_location builder
                      in (L.build_load const_int_location "" builder, scope)
                      (* in (L.const_int i1_t 1, scope) *)
                  in codegen_target target value

              in let cond_value' = L.build_and cond_value target_cond "accumulated-match" builder
                in (cond_value', scope'))
              (L.const_int i1_t 1, scope)
              target_vals

          in let _ = L.position_at_end then_bb builder
          in let then_value = expr builder scope' gamma sexpr
          in let then_value_location = L.build_alloca (L.type_of then_value) "" builder
          in let _ = L.build_store then_value then_value_location builder
          in let then_source_bb = L.instr_parent then_value_location
          in let _ = L.position_at_end then_source_bb builder
          in let branch = L.build_cond_br cond_value merge_bb next_bb builder

          in let _ = L.position_at_end then_source_bb builder
            in ((then_value, then_source_bb) :: cases, then_bb))
        ([(default_value, default_bb)], default_bb)
        bodies
      
      in let _ = L.position_at_end start_bb builder
      in let _ = L.build_br first_bb builder

      in let _ = L.position_at_end merge_bb builder
      in let incoming = cases
      in let phi = L.build_phi incoming "switchtmp" builder

      in let _ = L.move_block_after first_bb merge_bb
      in let _ = L.move_block_after first_bb default_bb
      in let _ = L.position_at_end merge_bb builder
        in phi
  | SIf (cond_sexpr, then_sexpr, else_sexpr) ->
    let cond_value = expr builder scope gamma cond_sexpr
    in let start_bb = L.insertion_block builder
    in let the_function = L.block_parent start_bb

    in let then_bb = L.append_block context "ifthen" the_function
    in let _ = L.position_at_end then_bb builder
    in let then_value = expr builder scope gamma then_sexpr
    in let then_bb_end = L.insertion_block builder

    in let else_bb = L.append_block context "ifelse" the_function
    in let _ = L.position_at_end else_bb builder
    in let else_value = expr builder scope gamma else_sexpr
    in let else_bb_end = L.insertion_block builder

    in let merge_bb = L.append_block context "ifcont" the_function
    in let _ = L.position_at_end merge_bb builder
    in let incoming = [(then_value, then_bb_end); (else_value, else_bb_end)]
    in let phi = L.build_phi incoming "iftmp" builder

    in let _ = L.position_at_end start_bb builder
    in let _ = L.build_cond_br cond_value then_bb else_bb builder

    in let _ = L.position_at_end then_bb_end builder
    in let _ = L.build_br merge_bb builder

    in let _ = L.position_at_end else_bb_end builder
    in let _ = L.build_br merge_bb builder

    in let _ = L.position_at_end merge_bb builder in phi
  | _ -> raise (Failure ("sexpr " ^ (Sast.string_of_sexpr (t,e)) ^ " not yet implemented"))

  
in let populate_function fun_type fun_defn fun_builder sexpr =
  let add_formal scope (name, ty) param =
    let local = L.build_alloca (ltype_of_typ ty) "" fun_builder in
    let _ = L.build_store param local fun_builder in
      (StringMap.add name local scope) in 
  let add_formal_typ gamma (name, ty) = (StringMap.add name ty gamma)
  in match sexpr with (_, SFunction (binds, body)) -> 
    let params = Array.to_list (L.params fun_defn)

    in let scope = List.fold_left2 add_formal StringMap.empty binds params
    in let gamma' = List.fold_left add_formal_typ gamma binds
    in let value = expr fun_builder scope gamma' body
      in L.build_ret value fun_builder

in let _ = List.map
  (fun (((name, _), sexpr) : bind * sexpr) ->
    let (fun_type, fun_defn, fun_builder) = (try StringMap.find name user_functions with Not_found -> raise (Failure name))
      in populate_function fun_type fun_defn fun_builder sexpr)
  fns

in let _ = expr main_builder StringMap.empty gamma letb
in let _ = L.build_ret (L.const_int i32_t 0) main_builder
in grp_module 