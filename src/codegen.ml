module L = Llvm
module A = Ast
open Sast

module StringMap = Map.Make(String)

let translate (types, letb) = 
  let context = L.global_context in 

  let i32_t     = L.i32_type    context 
  and i8_t      = L.i8_type     context 
  and i1_t      = L.i1_type     context
  and float_t   = L.double_type context
  and void_t    = L.void_type   context
  and string_t  = L.pointer_type i8_t

  and grp_module = L.create_module context "Grouper" in

  let printf_t : L.lltype = 
    L.var_arg_function_type i32_t [| L.pointer_type i8_t |] in
  let printf_func : L.llvalue = 
    L.declare_function "printf" printf_t grp_module in 

  
  let rec expr builder ((t,e) : sexpr) = match e with
    SLiteral i -> L.const_int i32_t i 
  | SBoolLit b -> L.const_int i1_t (if b then 1 else 0)
  | SFliteral l -> L.const_float_of_string float_t l
  | SStringLit str -> L.const_stringz context str
  | SPrint pexpr -> 
      let _ = L.build_call printf_func 
                           [| (L.const_stringz context (Ast.string_of_expr pexpr)) |]
                           "printf"
                           builder
      in expr builder (t, pexpr) 
  | SLet (binds, body) -> 
    List.map (fun (_, bexpr) -> expr builder bexpr) binds
    
    (* Ignores bindings for now, just builds the body basic block *)
  | _ -> Failure "expr " ^ (Ast.string_of_expr expr) ^ " not yet implemented"

  in grp_module 