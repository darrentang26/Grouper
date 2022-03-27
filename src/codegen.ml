
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
    L.var_arg_function_type i32_t [| L.pointer_type i8_t |]

  let rec expr builder ((_,e) : sexpr) = match e with
    SLiteral i -> L.const_int i32_t i 
  | SBoolLit b -> L.const_int i1_t (if b then 1 else 0)
  | SFliteral l -> L.const_float_of_string float_t l
  | SStringLit str -> Failure "Figure out strings in LLVM"
  | SPrint pexpr -> 
      let _ =
      in expr pexpr 
  | SName 