module L = Llvm

open Ast
open Sast

module StringMap = Map.Make(String)
let translate ((* types *) _, letb) =
  let context = L.global_context () in 

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
    | StructTypeExpr(fields) -> struct_t (Array.of_list (List.map (fun (_, typ) -> ltype_of_typ typ) fields))
    | ty -> raise (Failure ("type not implemented: " ^ string_of_type_expr ty))


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

  let rec expr builder scope ((t,e) : sexpr) = match e with
    SLiteral i -> L.const_int i32_t i
  | SBoolLit b -> L.const_int i1_t (if b then 1 else 0)
  | SFliteral l -> L.const_float_of_string float_t l
  | SStringLit str -> L.build_global_stringptr str "" builder
  | SPrint sexpr -> (match sexpr with
      (StringExpr, sx) -> let
        value = expr builder scope (StringExpr, sx) 
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
    left = expr builder scope (tl, sl) and
    right = expr builder scope (tr, sr)
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
    value = expr builder scope (ty, sx)
    in (match uop, ty with
      (Neg, IntExpr)  -> L.build_neg value "" builder
    | (Neg, FloatExpr)-> L.build_fneg value "" builder
    | (Not, BoolExpr) -> L.build_not value "" builder)
  | SLet (binds, body) -> let
    store_val scope ((name, ty), sexpr) = let
      local = L.build_alloca (ltype_of_typ ty) "" builder in let
      value = expr builder scope sexpr in let
      _ = L.build_store value local builder in
        (StringMap.add name local scope) in let
    scope' = List.fold_left 
        store_val
        scope
        binds
      in expr builder scope' body
  | SIf (cond_sexpr, then_sexpr, else_sexpr) ->
    let cond_value = expr builder scope cond_sexpr
    in let start_bb = L.insertion_block builder
    in let the_function = L.block_parent start_bb

    in let then_bb = L.append_block context "then" the_function
    in let _ = L.position_at_end then_bb builder
    in let then_value = expr builder scope then_sexpr
    in let then_bb = L.insertion_block builder

    in let else_bb = L.append_block context "else" the_function
    in let _ = L.position_at_end else_bb builder
    in let else_value = expr builder scope else_sexpr
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
in let _ = expr main_builder StringMap.empty letb
in let _ = L.build_ret (L.const_int i32_t 0) main_builder
in grp_module 