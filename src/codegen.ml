
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