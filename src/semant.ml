(* Semantic Analysis *)

open Ast
open Sast

module StringMap = Map.Make(String)


let pre_check (types, letb) = match letb with
    (Let (bs, e)) -> check ((Let (bs, e)))
    _ -> raise (Failure "illegal toplevel expression")

let check = function

let lookup_type name Gamma = 
    try StringMap.find name Gamma
        with Not_found -> raise (Failure, "unbound identifier " ^ name)

let type_eq ty1 ty2 = function

let rec semant Gamma expr = function
        Literal  l  -> (Int, SLiteral l)
      | Fliteral l  -> (Float, SFliteral l)
      | BoolLit l   -> (Bool, SBoolLit l)
      | StringLit l -> (String, SStringLit l)
      | PairExpr (e1, e2) -> let
            (t1, node1) = semant e1 and
            (t2, node2) = semant e2
                in (PairType (t1, t2), SPairExpr (node1, node2))
      | ListExpr es -> let
            (ts, nodes) = List.split (List.map semant es) and
            (* check if list is empty first *)
            hd = List.hd ts and
            _ = List.map
                    (fun (t) -> if ~type_eq hd t 
                        then raise (Failure, "lists must have the same type")
                        else false)
                    ts
                in (ListType hd, SListExpr List.map semant nodes)
      | Name s      -> (lookup_type s Gamma, SName s)
      | 

