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
let eq_type ty1 ty2 = (match ty1, ty2 with
  FunType (ParamType ty1ps, ty1rt), FunType (ParamType ty2ps, ty2rt) ->
    (ParamType ty1ps) = (ParamType ty2ps) && ty1rt = ty2rt
| _ -> ty1 = ty2)

let rec eq_types = function
    t1::t2::ts -> eq_type t1 t2 && eq_types (t1::ts)
|   _          -> true


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
      | ConsExpr (e1, e2) -> let
            (t1, s1) = semant gamma epsilon e1 and
            (t2, s2) = semant gamma epsilon e2
                in (match t2 with
                      ListType t2' -> if t1 = t2'
                            then (t2, SConsExpr ((t1, s1), (t2, s2)))
                            else raise (Failure ("must cons " ^ string_of_type_expr t1 ^ " onto a list of the same type, not " ^ string_of_type_expr t2))
                    | EmptyListType -> (ListType t1, SConsExpr((t1, s1), (t2, s2)))
                    | _ -> raise (Failure ("must cons onto a list type, not " ^ string_of_type_expr t2)))
      | CarExpr (e) -> let
            (t, s) = semant gamma epsilon e in
                (match t with
                    ListType t' -> (t', SCarExpr((t, s)))
                |   PairType (t1, t2) -> (t1, SCarExpr((t, s))))
      | CdrExpr (e) -> let
            (t, s) = semant gamma epsilon e in
                (match t with
                    ListType t' -> (t, SCdrExpr((t, s)))
                |   PairType (t1, t2) -> (t2, SCdrExpr((t, s))))
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
                    gamma' = (match tl with
                              (FunType _) -> StringMap.add name tl gamma
                            | _ -> gamma) in let
                    (tr, (* sexpr *) _) = semant gamma' epsilon expr
                    (* Update epsilon *)
                        in if tl = tr
                            then (StringMap.add name tl gamma)
                            else if tr = EmptyListType then match tl with
                                      ListType tl' -> (StringMap.add name tl gamma) 
                                    | _ -> raise (Failure "the left- and right-hand sides of a let binding must have the same type")
                                else raise (Failure ("the left- and right-hand sides of bindings must mach: " ^ (string_of_type_expr tl) ^ " =/= " ^ (string_of_type_expr tr))))
                gamma
                binds and
            sbinds = List.map (fun ((name, tl), expr) -> let
                gamma = match tl with (FunType _) -> StringMap.add name tl gamma | _ -> gamma
                    in ((name, tl), semant gamma epsilon expr)) binds
                in let (t, sx) = semant gamma' epsilon body
                    in (t, SLet (sbinds, (t, sx)))
      | If (cond_expr, then_expr, else_expr) -> let
            (cond_t, cond_s) = semant gamma epsilon cond_expr in
            if cond_t != BoolExpr then raise (Failure "if condition expression must be a boolean")
            else let
            (then_t, then_s) = semant gamma epsilon then_expr and
            (else_t, else_s) = semant gamma epsilon else_expr in
            (* if then_t != else_t then raise (Failure ("then and else expressions must have the same type; then: " ^ string_of_type_expr then_t ^ " else: " ^ string_of_type_expr else_t)) *)
            if not (eq_type then_t else_t) then raise (Failure ("then and else expressions must have the same type; then: " ^ string_of_type_expr then_t ^ " else: " ^ string_of_type_expr else_t))
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
      | StructInit bindsList -> (*let rec
            check_consec_dupes = function
                x::y::rest -> if x = y then raise (Failure "Struct field names must be unique")
                           else x::(check_consec_dupes (y::rest))
              | x::[] -> x::[] in let               
            get_names = function
                
            _ = check_consec_dupes (List.sort String.compare bindsList) in*) 
            let typed_binds = List.map (fun (name, expr) -> 
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
        (typ_name, sexp) = semant gamma epsilon (Name(var)) in (match typ_name with
           TypNameExpr(typ) -> let
             accessed_type = lookup_type typ gamma in (match accessed_type with
                StructTypeExpr(binds) -> let 
                   (_, found_type) = List.find (fun (curr_field, _) -> curr_field = field) binds in
                     (found_type, SStructRef(var,field))
             |  GroupType ty -> (match sexp with
                  SStructInit xs -> 
                    let (n, (t, s)) = try List.find (fun (name, (ty, sexp)) -> name == field) xs
                                            with Not_Found -> raise (Failure (field ^ " is not a valid group field"))

                    in (t, SStructRef(var, field))
                | _              -> raise (Failure ("Group is not a struct - this is impossible???"))

             |  _ -> raise (Failure (var ^ " is not a struct")))
        |  _ -> raise (Failure "What was accessed was not a name"))
      (*| Group (t, e1, e2, e3, e4) ->
            let bin_check ftype = (match ftype with
                FunType(PairType(t1, t2), t3)
                    -> t1 = t && t2 = t && t3 = t
                | _ -> raise (Failure "Group binop with wrong type")) in
            let neg_check ftype = (match ftype with
                FunType(t1, t2)
                    -> t1 = t && t2 = t
                | _ -> raise (Failure "Group unop wrong type")) in
            let eq_check ftype = (match ftype with
                FunType(PairType(t1, t2), BoolExpr)
                    -> t1 = t && t2 = t
                | _ -> raise (Failure "Eq op wrong type")) in
            (* zero, eq, plus, neg *)
            let (t1, se1) = semant gamma epsilon e1 and
                (t2, se2) = semant gamma epsilon e2 and
                (t3, se3) = semant gamma epsilon e3 and
                (t4, se4) = semant gamma epsilon e4 in
            let sem_list = [(t1, se1); (t2, se2); (t3, se3); (t4, se4)]
              and name_list = ["zero"; "eq"; "plus"; "neg"] in
            let struct_wrap (accum, (t, se), name) = (name, se) :: accum in
                    if eq_check t2 && bin_check t3 && neg_check t4
                    && t1 = t then 
                        (GroupType t, SStructInit(List.fold_left2 struct_wrap [] 
                                                    sem_list, name_list))
                    else raise (Failure "Identity elt wrong type")*)



      | Group (texp, zero, eq, plus, neg) -> 
        let build_group zero eq plus neg =
            SStructInit [("zero", zero); ("equals", eq); ("plus", plus); ("neg", neg)]

        and (t0, s0) = semant gamma epsilon zero
        and (teq, seq) = semant gamma epsilon eq
        and (tpl, spl) = semant gamma epsilon plus
        and (tneg, sneg) = semant gamma epsilon neg
        in (match (t0, teq, tpl, tneg) with
            (t1, FunType (ParamType [t2; t3], BoolExpr), 
                 FunType (ParamType [t4; t5], t6),
                 FunType (ParamType [t7], t8)) -> 
                        if eq_types [texp; t1; t2; t3; t4; t5; t6; t7; t8]
                        then (GroupType(texp), build_group (t0, s0) (teq, seq) (tpl, spl) (tneg, sneg))
                        else raise (Failure "Group parameter has inconsistent type")
        |   _ -> raise (Failure "Equals, plus or negate function had wrong number of arguments"))


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
                                else raise (Failure ("expected parameter of type " ^ string_of_type_expr pt ^ " but recieved argument of type " ^ string_of_type_expr t2))
                      | _ -> raise (Failure ("cannot call a non-function with type " ^ string_of_type_expr t1)))
          | _ -> raise (Failure "Cannot call a non-function")

            in let ((ty, sx), valid, _, _) = semant_call_inner call in
                if valid then (ty, sx) else raise (Failure ("functions must be completely applied"))
                    
    
        in match body with
        Let _ -> (typ_decls, semant gamma epsilon body)
        | _ -> raise (Failure "top-level expression must be a let expression")
