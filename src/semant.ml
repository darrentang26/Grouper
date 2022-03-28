(* Semantic Analysis *)

(* rho = user-type environment *)
(* gamma = name/type environment *)
(* epsilon = name/value environment *)

open Ast
open Sast

module StringMap = Map.Make(String)

exception Failure of string

let lookup_type name gamma = 
    try StringMap.find name gamma
        with Not_found -> raise (Failure ("unbound identifier " ^ name))

(*let type_eq ty1 ty2 = raise (Failure "not implemented")*)

let check (typ_decls, body) = let
    rho = StringMap.empty and
    gamma = StringMap.empty and
    epsilon = StringMap.empty 

    in let rec semant gamma epsilon = function
        Literal  l  -> (IntExpr, SLiteral l)
      | Fliteral l  -> (FloatExpr, SFliteral l)
      | BoolLit l   -> (BoolExpr, SBoolLit l)
      | StringLit l -> (StringExpr, SStringLit l)
      | PairExpr (e1, e2) -> let
            (t1, s1) = semant gamma epsilon e1 and
            (t2, s2) = semant gamma epsilon e2
                in (PairType (t1, t2), SPairExpr ((t1, s1), (t2, s2)))
      | ConsExpr (expr, EmptyListExpr) -> let
            (t, sx) = semant gamma epsilon expr
                in (match t with
                      ListType EmptyListType -> raise (Failure "cannot hae a list of empty lists")
                    | _ -> (ListType t, SConsExpr ((t, sx), (EmptyListType, SEmptyListExpr))))
      | ConsExpr (e1, e2) -> let
            (t1, s1) = semant gamma epsilon e1 and
            (t2, s2) = semant gamma epsilon e2
                in (match t2 with
                     ListType t2' -> if t1 = t2'
                            then (t2, SConsExpr ((t1, s1), (t2, s2)))
                            else raise (Failure ("must cons " ^ string_of_type_expr t1 ^ " onto a list of the same type, not " ^ string_of_type_expr t2))
                    | _ -> raise (Failure ("must cons onto a list type, not " ^ string_of_type_expr t2)))
      | EmptyListExpr -> (EmptyListType, SEmptyListExpr)
      | Name s      -> raise (Failure "not implemented-- need to figure out how variable environment works")
      | Binop (e1, op, e2) -> raise (Failure "not implemented-- need to figure out stuff for algebra here")
      | Unop (uop, expr) -> raise (Failure "not implemented-- need to figure out stuff for algebra here")
      | Let (binds, body) -> let
            gamma' = List.fold_left
                (fun gamma ((name, tl), expr) -> let
                    (tr, sexpr) = semant gamma epsilon expr
                    (* Update epsilon *)
                        in if tl = tr
                            then (StringMap.add name tl gamma)
                            else raise (Failure "the left- and right-hand sides of bindings must mach"))
                gamma
                binds
                in semant gamma' epsilon body
      | Print expr -> let
            (t, sx) = semant gamma epsilon expr
                in (t, SPrint (t, sx))
      | _ -> raise (Failure "Not yet implemented")

        in match body with
        Let _ -> (typ_decls, semant gamma epsilon body)
        | _ -> raise (Failure "top-level expression must be a let expression")
    


