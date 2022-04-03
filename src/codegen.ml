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
  and void_t    = L.void_type   context in
  (* and string_t  = L.pointer_type (L.i8_type context)  *)

  let ltype_of_typ = function
      IntExpr -> i32_t
    | BoolExpr -> i1_t
    | FloatExpr -> float_t
    | VoidExpr -> void_t
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