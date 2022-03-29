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
  (* and void_t    = L.void_type   context
  and string_t  = L.pointer_type (L.i8_type context) *) 

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

  let rec expr builder ((t,e) : sexpr) = match e with
    SLiteral i -> L.const_int i32_t i 
  | SBoolLit b -> L.const_int i1_t (if b then 1 else 0)
  | SFliteral l -> L.const_float_of_string float_t l
  | SStringLit str -> L.const_stringz context str
  | SPrint sexpr -> (match sexpr with
      (StringExpr, sexpr') -> let
        value = expr builder (StringExpr, sexpr') 
          in let sval = match (L.string_of_const value) with
                          Some s -> s
                        | None -> ""
          in let str = L.build_in_bounds_gep (L.build_global_stringptr sval "" builder) [| (L.const_int i32_t 0) |] "" builder
          in let _ = L.build_call print_func [| str |] "printf" builder
            in value
    | _ -> raise (Failure "not yet implemented-- print only expects strings"))
  | SLet ((*binds*) _, body) -> (* Ignores bindings for now, just builds the body basic block *)
      expr builder body
  | SIf cond_sexpr then_sexpr else_sexpr ->
      let cond_value = expr builder cond_sexpr and

      (* create the basic block for combining the branches *)
      merge_bb = L.append_block context "merge" main_defn
      in let branch_instr = L.build_br merge_bb and

      (* create the basic block for the then branch *)
      then_bb = L.append_block context "then" main_defn
      in let then_builder = expr (L.builder_at_end context then_bb) then_sexpr
      in let () = L.add_terminal then_builder branch_instr and

      (* create the basic block for the else branch *)
      else_bb = L.append_block context "else" main_defn
      in let else_builder = expr (L.builder_at_end context else_bb) else_sexpr
      in let () = L.add_terminal else_builder branch_instr in 

      let _ = L.build_cond_br cond_value then_bb else_bb builder
        in L.builder_at_end context merge_bb
    
  | _ -> raise (Failure ("sexpr " ^ (Sast.string_of_sexpr (t,e)) ^ " not yet implemented"))
in let _ = expr main_builder letb
in let _ = L.build_ret (L.const_int i32_t 0) main_builder
in grp_module 