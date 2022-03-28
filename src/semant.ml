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
        with Not_found -> raise (Failure "unbound identifier " ^ name)

let type_eq ty1 ty2 = function

let rec semant Gamma expr = function
        Literal  l  -> (Int, SLiteral l)
      | Fliteral l  -> (Float, SFliteral l)
      | BoolLit l   -> (Bool, SBoolLit l)
      | StringLit l -> (String, SStringLit l)
      | PairExpr (e1, e2) -> let
            (t1, s1) = semant Gamma e1 and
            (t2, s2) = semant Gamma e2
                in (PairType (t1, t2), SPairExpr (s1, s2))
      | ConsExpr (expr, EmptyListExpr) -> let
            (t, sexpr) = semant Gamma expr
                in match t with
                    | ListType EmptyListType -> raise (Failure "cannot hae a list of empty lists")
                    | ListType t' -> (t, sexpr) 
                    | _ -> (ListType t, SConsExpr (sexpr, EmptyListExpr))
      | ConsExpr (e1, e2) -> let
            (t1, s1) = semant Gamma e1 and
            (t2, s2) = semant Gamma e2
                in match t2 with
                    | ListType t2' -> if type_eq t1 t2'
                            then (t2, SConsExpr (s1, s2))
                            else raise (Failure "must cons " ^ string_of_type_expr t1 ^ " onto a list of the same type, not " ^ string_of_type_expr t2)
                    | _ -> raise (Failure "must cons onto a list type, not " ^ string_of_type_expr t2)
      | EmptyListExpr -> (EmptyListType, SEmptyListExpr)
      | Name s      -> (lookup_type s Gamma, SName s, raise (Failure "not implemented-- need to figure out how variable environment works"))
      | Binop (e1, op, e2) -> raise (Failure "not implemented-- need to figure out stuff for algebra here")
      | Unop (uop, expr) -> raise (Failure "not implemented-- need to figure out stuff for algebra here")
      | Let (binds, body) -> let
            Gamma' = List.fold_left
                (fun (Gamma, ((tl, name), expr)) -> let
                    (tr, sexpr) = semant Gamma expr and
                    Gamma' = if type_eq tl tr
                        then StringMap.add name tl Gamma
                        else raise (Failure "the left- and right-hand sides of bindings must mach") and
                    _ = raise (Failure "not implemented-- need to figure out out how variable environment works")
                        in Gamma')
                Gamma
                binds
                in semant Gamma' body

