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
    gamma = List.fold_left (fun env (name, texpr) -> StringMap.add name texpr env) 
        StringMap.empty 
        typ_decls and
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
            gamma' = List.fold_left
                (fun gamma ((name, tl), expr) -> let
                    (tr, (* sexpr *) _) = semant gamma epsilon expr
                    (* Update epsilon *)
                        in if tl = tr
                            then (StringMap.add name tl gamma)
                            else if tr = EmptyListType then match tl with
                                      ListType tl' -> (StringMap.add name tl gamma) 
                                    | _ -> raise (Failure "the left- and right-hand sides of a let binding must have the same type")
                                else raise (Failure ("the left- and right-hand sides of bindings must mach: " ^ (string_of_type_expr tl) ^ " =/= " ^ (string_of_type_expr tr))))
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
      | Function (binds, body) -> let
            gamma' = List.fold_left
                (fun gamma (name, tl) -> StringMap.add name tl gamma)
                StringMap.empty
                binds in let
            param_types = List.map
                (fun (name, tl) -> tl)
                binds and
            (rt, sbody) = semant gamma' epsilon body
                in (FunType (ParamType param_types, rt), SFunction (binds, (rt, sbody)))
      | Call (e1, e2) -> semant_call gamma epsilon (Call (e1, e2))
      | StructInit bindsList -> let
            typed_binds = List.map (fun (name, expr) -> 
                                     (name, semant gamma epsilon expr)) 
                                   bindsList in let
            comparable = List.map (fun (name,(typ, expr)) -> (name, typ)) typed_binds in let rec
            struct_type = function
                (name, StructTypeExpr(fields))::binds -> if fields = comparable then
                                                                  name else struct_type binds
             |  _::binds -> struct_type binds
             |  [] -> raise (Failure "initialized a struct that matches no declared struct type") 
                in
            (TypNameExpr(struct_type (StringMap.bindings gamma)), SStructInit(typed_binds))
      | StructRef (var, field) -> let 
        (typ_name, _) = semant gamma epsilon (Name(var)) in (match typ_name with
           TypNameExpr(typ) -> let
             accessed_type = lookup_type typ gamma in (match accessed_type with
                StructTypeExpr(binds) -> let 
                   (_, found_type) = List.find (fun (curr_field, _) -> curr_field = field) binds in
                     (found_type, SStructRef(var,field))
             |  _ -> raise (Failure (var ^ "is not a struct")))
        |  _ -> raise (Failure "What was accessed was not a name"))

      | _ -> raise (Failure "Not yet implemented")

    and semant_call gamma epsilon call =
        let rec semant_call_inner = function
            (* subsequent calls *)
            Call (Call (e1', e2'), e2) ->
                let ((oft, fs), valid, sexpr_list, cft) = semant_call_inner (Call (e1', e2'))
                and (t2, s2) = semant gamma epsilon e2
                    in (match cft with
                        FunType (ParamType (pt :: pts), rt) ->
                            if pt = t2
                                then if pts = []
                                    then ((rt, SCall ((oft, fs), sexpr_list @ [(t2, s2)])), true, [], rt)
                                    else ((oft, fs), false, sexpr_list @ [(t2, s2)], FunType (ParamType pts, rt))
                                else raise (Failure ("cannot apply " ^ string_of_type_expr t2 ^ " to " ^ string_of_type_expr pt))
                      | _ -> raise (Failure ("cannot call a non-function with type " ^ string_of_type_expr cft)))
            (* function expression *)
          | Call (e1, e2) ->
                let (t1, s1) = semant gamma epsilon e1
                and (t2, s2) = semant gamma epsilon e2
                    in (match t1 with
                        FunType (ParamType (pt :: pts), rt) ->
                            if pt = t2
                                then if pts = []
                                    then ((rt, SCall ((t1, s1), [(t2, s2)])), true, [], rt)
                                    else ((t1, s1), false, [(t2, s2)], FunType (ParamType pts, rt))
                                else raise (Failure ("cannot appyly " ^ string_of_type_expr t2 ^ " to " ^ string_of_type_expr pt))
                      | _ -> raise (Failure ("cannot call a non-function with type " ^ string_of_type_expr t1)))
          | _ -> raise (Failure "Cannot call a non-function")

            in let ((ty, sx), valid, _, _) = semant_call_inner call in
                if valid then (ty, sx) else raise (Failure ("functions must be completely applied"))
                    
    
        in match body with
        Let _ -> (typ_decls, semant gamma epsilon body)
        | _ -> raise (Failure "top-level expression must be a let expression")
