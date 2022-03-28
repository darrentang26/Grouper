(* Semantic Analysis *)

open Ast
open Sast

module StringMap = Map.Make(String)


let pre_check (types, letb) = match letb with
    (Let (bs, e)) -> check ((Let (bs, e)))
    _ -> Failure "illegal toplevel expression"

let check = function

let lookup_type name Gamma = 
    try StringMap.find name Gamma
        with Not_found -> Failure ("unbound identifier " ^ name)

let rec Gamma expr = function
        Literal  l  -> (Int, SLiteral l)
      | Fliteral l  -> (Float, SFliteral l)
      | BoolLit l   -> (Bool, SBoolLit l)
      | StringLit l -> (String, SStringLit l)
      | Name s      -> (lookup_type s Gamma, SName s)
      | 

