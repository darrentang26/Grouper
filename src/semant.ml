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
      | Name s      -> let 
            ty = lookup_type s gamma
                in (ty, SName s)
      | Binop (e1, op, e2) -> let
            (t1, s1) = semant gamma epsilon e1 and
            (t2, s2) = semant gamma epsilon e2
                in if t1 != t2 then raise (Failure ("cannot apply binary operator to arguments of different types (" ^ string_of_type_expr t1 ^ " and " ^ string_of_type_expr t2 ^ ")"))
                    (* Need to change this to work with algebra stuff!!!! *)
                    else (match op, t1 with
                      (Add, IntExpr) | (Add, FloatExpr) | (Add, StringExpr) -> (t1, SBinop ((t1, s1), Add, (t2, s2)))
                    | (Sub, IntExpr) | (Sub, FloatExpr) -> (t1, SBinop ((t1, s1), Sub, (t2, s2)))
                    | (Mult, IntExpr) | (Mult, FloatExpr) -> (t1, SBinop ((t1, s1), Mult, (t2, s2)))
                    | (Div, IntExpr) | (Div, FloatExpr) -> (t1, SBinop ((t1, s1), Div, (t2, s2)))
                    | (Equal, IntExpr) | (Equal, FloatExpr) | (Equal, StringExpr) -> (BoolExpr, SBinop ((t1, s1), Equal, (t2, s2)))
                    | (Neq, IntExpr) | (Neq, FloatExpr) | (Neq, StringExpr) -> (BoolExpr, SBinop ((t1, s1), Neq, (t2, s2)))
                    | (Less, IntExpr) | (Less, FloatExpr) -> (BoolExpr, SBinop ((t1, s1), Less, (t2, s2)))
                    | (Leq, IntExpr) | (Leq, FloatExpr) -> (BoolExpr, SBinop ((t1, s1), Leq, (t2, s2)))
                    | (Greater, IntExpr) | (Greater, FloatExpr) -> (BoolExpr, SBinop ((t1, s1), Greater, (t2, s2)))
                    | (Geq, IntExpr) | (Geq, FloatExpr) -> (BoolExpr, SBinop ((t1, s1), Geq, (t2, s2)))
                    | (And, BoolExpr) -> (t1, SBinop ((BoolExpr, s1), And, (t2, s2)))
                    | (Or, BoolExpr) -> (t1, SBinop ((t1, s1), Or, (t2, s2)))
                    | (Mod, IntExpr) -> (t1, SBinop ((t1, s1), Mod, (t2, s2)))
                    | _ -> raise (Failure ("cannot apply " ^ string_of_op op ^ " to arguments of type " ^ string_of_type_expr t1)))
      | Unop (uop, expr) -> let
            (ty, sx) = semant gamma epsilon expr
                in (match uop, ty with
                      (Neg, IntExpr) | (Neg, FloatExpr) -> (ty, SUnop (Neg, (ty, sx)))
                    | (Not, BoolExpr) -> (ty, SUnop (Not, (ty, sx)))
                    | _ -> raise (Failure ("cannot apply " ^ string_of_uop uop ^ " to argument of type " ^ string_of_type_expr ty)))
                    (* This needs to have algebra added to it *)
      | Let (binds, body) -> let
            (gamma', sbinds) = List.fold_left
                (fun (gamma, sbinds) ((name, tl), expr) -> match tl with
                    FunType _ -> let
                        gamma'' = StringMap.add name tl gamma in let
                        (tr, sx) = semant gamma'' epsilon expr in
                            if tl = tr then (gamma'', ((name, tl), (tr, sx)) :: sbinds)
                                else raise (Failure "the left- and right-hand sides of bindings must mach")
                    | _ -> let
                        (tr, sx) = semant gamma epsilon expr
                            in if tl = tr
                                then ((StringMap.add name tl gamma), ((name, tl), (tr, sx)) :: sbinds)
                                else if tr = EmptyListType then match tl with
                                        ListType tl' -> ((StringMap.add name tl gamma), ((name, tl), (tr, sx)) :: sbinds)
                                        | _ -> raise (Failure "the left- and right-hand sides of a let binding must have the same type")
                                    else raise (Failure "the left- and right-hand sides of bindings must mach"))
                (gamma, [])
                binds in let
            (t, sx) = semant gamma' epsilon body
                in (t, SLet (sbinds, (t, sx)))
      | Function ([(name, ty)], body) -> let
            gamma' = StringMap.add name ty gamma in let
            (bodyty, sbody) = semant gamma' epsilon body
                in (FunType (ty, bodyty), SFunction ((name, ty), (bodyty, sbody)))
      | Function (args, body) -> let
            (name, ty) = List.hd args in let
            gamma' = StringMap.add name ty gamma in let
            (bodyty, sbody) = semant gamma' epsilon (Function (List.tl args, body))
                in (FunType (ty, bodyty), SFunction ((name, ty), (bodyty, sbody)))
      | Call (e1, e2) -> let
            (t1, s1) = semant gamma epsilon e1 and
            (t2, s2) = semant gamma epsilon e2
                in (match t1 with
                  FunType (t3, t4) when t2 = t3 -> (t4, SCall ((t1, s1), (t2, s2)))
                | _ -> raise (Failure ("cannot call a non-function of type " ^ string_of_type_expr t1)))
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
      | x -> raise (Failure ("Not yet implemented: " ^ string_of_expr x))

        in match body with
        Let _ -> (typ_decls, semant gamma epsilon body)
        | _ -> raise (Failure "top-level expression must be a let expression")
