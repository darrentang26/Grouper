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
    (* rho = StringMap.empty and *)
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
      (* | Name s      -> raise (Failure "not implemented-- need to figure out how variable environment works")
      | Binop (e1, op, e2) -> raise (Failure "not implemented-- need to figure out stuff for algebra here")
      | Unop (uop, expr) -> raise (Failure "not implemented-- need to figure out stuff for algebra here") *)
      | Let (binds, body) -> let
            gamma' = List.fold_left
                (fun gamma ((name, tl), expr) -> let
                    (tr, (* sexpr *) _) = semant gamma epsilon expr
                    (* Update epsilon *)
                        in if tl = tr
                            then (StringMap.add name tl gamma)
                            else if tr = EmptyListType then match tl with
                                      ListType tl' -> (StringMap.add name tl gamma) 
                                    | _ -> raise (Failure "the left- and right-hand sides of a let binding must have the same type")
                                else raise (Failure "the left- and right-hand sides of bindings must mach"))
                gamma
                binds and
            sbinds = List.map (fun ((name, tl), expr) -> ((name, tl), semant gamma epsilon expr)) binds
                in let (t, sx) = semant gamma' epsilon body
                    in (t, SLet (sbinds, (t, sx)))
      | If (cond_expr, then_expr, else_expr) -> let
            (cond_t, cond_s) = semant gamma epsilon cond_expr in
            if cond_t != BoolExpr then raise (Failure "if condition expression must be a boolean")
            else let
            (then_t, then_s) = semant gamma epsilon then_expr and
            (else_t, else_s) = semant gamma epsilon else_expr in
            if then_t != else_t then raise (Failure "then and else expressions must have the same type")
            else (then_t, SIf ((cond_t, cond_s), (then_t, then_s), (else_t, else_s)))
      | Print expr -> let
            (t, sx) = semant gamma epsilon expr
                in (t, SPrint (t, sx))
      | _ -> raise (Failure "Not yet implemented")

        in match body with
        Let _ -> (typ_decls, semant gamma epsilon body)
        | _ -> raise (Failure "top-level expression must be a let expression")
    


