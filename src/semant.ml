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

let compare_type ty = FunType (ParamType [ty; ty], BoolExpr)
let binop_type ty = FunType (ParamType [ty; ty], ty)
let unop_type ty = FunType (ParamType [ty], ty)
let mpoly_type ty = FunType (ParamType [ListType ty], PolyType ty)
let pdeg_type ty = FunType (ParamType [PolyType ty], IntExpr)
let get_fun opp (op_name, sexp) = opp = op_name

(* FIELDMOD *)
let group_list ty = [("zero", ty); ("equals", compare_type ty); ("plus", binop_type ty);
                    ("neg", unop_type ty); ("minus", binop_type ty)]
let field_list ty = (group_list ty) @ [("one", ty); ("times", binop_type ty); 
                       ("inv", unop_type ty); ("div", binop_type ty); 
                       ("make_poly", mpoly_type ty); ("deg", pdeg_type ty);
                       ("poly_neg", unop_type (PolyType ty))]

let build_minus plus neg ty =
    Function([("x", ty); ("y", ty)], Call(Call(plus, Name "x"), Call(neg, Name "y")))
let build_div times inv ty =
    Function([("x", ty); ("y", ty)], Call(Call(times, Name "x"), Call(inv, Name "y")))
let build_mod times div minus ty =
    Function([("x", ty); ("y", ty)], Call(Call(minus, Name "x"), Call(Call(times, Name "y"), (Call(Call(div, Name "x"), Name "y")))))
let make_poly ty =
    Function(["xs", ListType ty;], Name "xs")

let poly_deg ty index =
    let fun_name = "poly_deg." ^ string_of_int index in
    Let([((fun_name, pdeg_type ty), 
        Function([("xs", ListType ty)], 
                    If (Unop(Null, Name "xs"), 
                        Literal 0, 
                        Binop(Literal 1, Add, 
                              Call(Name fun_name, CdrExpr (Name "xs"))))))], 
        Name fun_name)
let poly_neg neg ty index =
    let fun_name = "poly deg." ^ string_of_int index in
    Let([((fun_name, unop_type (ListType ty)),
        Function([("xs", ListType ty)],
                   If (Unop(Null, Name "xs"),
                       EmptyListExpr,
                       ConsExpr(Call(neg, CarExpr (Name "xs")), 
                                Call(Name fun_name, CdrExpr (Name "xs"))))))],
        Name fun_name)
(*let build_poly_plus plus texp inst_num =*)
    

(*let type_eq ty1 ty2 = raise (Failure "not implemented")*)
let rec eq_type ty1 ty2 = (match ty1, ty2 with
  FunType (ParamType ty1ps, ty1rt), FunType (ParamType ty2ps, ty2rt) ->
    (eq_type (ParamType ty1ps) (ParamType ty2ps)) && (eq_type ty1rt ty2rt)
| ListType ty, EmptyListType | EmptyListType, ListType ty -> true
| PolyType t1, ListType t2 | ListType t1, PolyType t2 -> eq_type t1 t2
| ParamType ty1ps, ParamType ty2ps -> List.for_all2 (fun e1 e2 -> eq_type e1 e2) ty1ps ty2ps
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
           (* TODO: figure out poly type here *)
            (t1, s1) = semant gamma epsilon e1 and
            (t2, s2) = semant gamma epsilon e2
                in (match t2 with
                      ListType t2' -> if eq_type t1 t2'
                            then (t2, SConsExpr ((t1, s1), (t2, s2)))
                            else raise (Failure ("must cons " ^ string_of_type_expr t1 ^ " onto a list of the same type, not " ^ string_of_type_expr t2))
                    | EmptyListType -> (ListType t1, SConsExpr((t1, s1), (t2, s2)))
                    | _ -> raise (Failure ("must cons onto a list type, not " ^ string_of_type_expr t2)))
      | CarExpr (e) -> let
            (t, s) = semant gamma epsilon e in
                (match t with
                    ListType t' | PolyType t' -> (t', SCarExpr((t, s)))
                |   EmptyListType -> (raise (Failure "car of empty list"))
                |   PairType (t1, t2) -> (t1, SCarExpr((t, s)))
                |   _ -> raise (Failure (string_of_type_expr t)))
      | CdrExpr (e) -> let
            (t, s) = semant gamma epsilon e in
                (match t with
                    ListType t' | PolyType t' -> (t, SCdrExpr((t, s)))
                |   EmptyListType -> (raise (Failure "cdr of empty list"))
                |   PairType (t1, t2) -> (t2, SCdrExpr((t, s)))
                |   _ -> raise (Failure (string_of_type_expr t)))
      | EmptyListExpr -> (EmptyListType, SEmptyListExpr)
      | Name s      -> let
            ty = lookup_type s gamma in 
            (ty, SName s)

      | Binop (e1, op, e2) -> let
            (t1, s1) = semant gamma epsilon e1 and
            (t2, s2) = semant gamma epsilon e2
                in if not (eq_type t1 t2) then raise (Failure ("cannot apply binary operator to arguments of different types (" ^ string_of_type_expr t1 ^ " and " ^ string_of_type_expr t2 ^ ")"))
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
                    | _ ->
                        let (opp, sexp) = try List.find (get_fun (string_of_op op)) (StringMap.find (string_of_type_expr t1) epsilon)
                        with Not_found -> raise (Failure ("cannot apply " ^ string_of_op op ^ " to arguments of type " ^ string_of_type_expr t1))
                    in  let ty = (match opp with "=" -> BoolExpr | _ -> t1)
                        in (ty, SCall(sexp, [(t1, s1); (t2, s2)])))
      | Unop (uop, expr) -> let
            (ty, sx) = semant gamma epsilon expr
                in (match uop, ty with
                      (Neg, IntExpr) | (Neg, FloatExpr) -> (ty, SUnop (Neg, (ty, sx)))
                    | (Not, BoolExpr) -> (ty, SUnop (Not, (ty, sx)))
                    | (Neg, _) -> let (opp, sexp) = try List.find (get_fun "Neg") (StringMap.find (string_of_type_expr ty) epsilon)
                                                        with Not_found -> raise (Failure ("cannot apply " ^ string_of_uop uop ^ " to argument of type " ^ string_of_type_expr ty))
                                    in (ty, SCall(sexp, [(ty, sx)]))
                    | (Null, ListType tau) -> (BoolExpr, SUnop (Null, (ty, sx)))
                    | (Null, EmptyListType) -> (BoolExpr, SBoolLit true)
                    | _ -> raise (Failure ("cannot apply " ^ string_of_uop uop ^ " to argument of type " ^ string_of_type_expr ty)))
                    (* This needs to have algebra added to it *)
      | Let (binds, body) ->
            let gamma_fun = StringMap.filter 
                (fun name ty -> (match ty with
                                        FunType _ -> true
                                        |       _ -> false))
                gamma in 
            let gamma' = List.fold_left
                (fun gamma ((name, tl), expr) -> let
                    gamma' = (match tl with
                              (FunType _) -> StringMap.add name tl gamma_fun
                            | _ -> gamma) in let
                    (tr, (* sexpr *) _) = semant gamma' epsilon expr
                    (* Update epsilon *) in
                            if eq_type tl tr
                            then (StringMap.add name tl gamma)
                            else if tr = EmptyListType then match tl with
                                      ListType tl' -> (StringMap.add name tl gamma)
                                    | _ -> raise (Failure "the left- and right-hand sides of a let binding must have the same type")
                                else raise (Failure ("the left- and right-hand sides of bindings must match: " ^ (string_of_type_expr tl) ^ " =/= " ^ (string_of_type_expr tr))))
                gamma
                binds and
            sbinds = List.map (fun ((name, tl), expr) -> let
                gamma' = match tl with (FunType _) -> StringMap.add name tl gamma_fun | _ -> gamma
                    in ((name, tl), semant gamma' epsilon expr)) binds
            in let
                epsilon' = List.fold_left
                (fun epsilon (nt, sexpr) -> (match sexpr with
                        (GroupType ty, SStructInit [zero; ("equals", seq); ("plus", spl); 
                                                    ("neg", sneg); ("minus", smin)])
                            -> StringMap.add (string_of_type_expr ty) 
                                            [("=", seq); ("+", spl);
                                             ("n", sneg); ("-", smin)] epsilon
                        | (FieldType ty, SStructInit [zero; ("equals", seq); ("plus", spl); 
                                                    ("neg", sneg); ("minus", smin); one; 
                                                    ("times", stim); inv; ("div", sdiv)])
                            -> StringMap.add (string_of_type_expr ty)
                                            [("=", seq); ("+", spl); ("n", sneg); ("-", smin);
                                             ("*", stim); ("/", sdiv)] epsilon
                        | _ -> epsilon)) epsilon sbinds
                in let (t, sx) = semant gamma' epsilon' body
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
                gamma
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
                |  _ -> raise (Failure (var ^ " is not a struct")))
            |  GroupType ty -> 
                let (n, t) = try List.find (fun (name, tau) -> name = field) (group_list ty)
                                            with Not_found -> raise (Failure (field ^ " is not a valid group element"))

                    in (t, SStructRef(var, field))
            |  FieldType ty ->
                let (n, t) = try List.find (fun (name, tau) -> name = field) (field_list ty)
                                            with Not_found -> raise (Failure (field ^ " is not a valid field element"))
                    in (t, SStructRef(var, field))
            |  _ -> raise (Failure "What was accessed was not a name"))


      | Group (texp, zero, eq, plus, neg) -> 
        let build_group zero eq plus neg min =
            SStructInit [("zero", zero); ("equals", eq); ("plus", plus); ("neg", neg); ("minus", min)]

        and (t0, s0) = semant gamma epsilon zero
        and (teq, seq) = semant gamma epsilon eq
        and (tpl, spl) = semant gamma epsilon plus
        and (tneg, sneg) = semant gamma epsilon neg
        and (tmin, smin) = semant gamma epsilon (build_minus plus neg texp)
        in (match (t0, teq, tpl, tneg) with
            (t1, FunType (ParamType [t2; t3], BoolExpr), 
                 FunType (ParamType [t4; t5], t6),
                 FunType (ParamType [t7], t8)) -> 
                        if eq_types [texp; t1; t2; t3; t4; t5; t6; t7; t8]
                        then (GroupType(texp), build_group (t0, s0) (teq, seq) (tpl, spl) (tneg, sneg) (tmin, smin))
                        else raise (Failure "Group parameter has inconsistent type")
        |   _ -> raise (Failure "Equals, plus or negate function had wrong number of arguments"))
      | Field (texp, zero, eq, plus, neg, one, times, inv) ->
        let field_count = StringMap.cardinal epsilon in
        let build_field zero eq plus neg min one times inv div mpoly deg pneg=
            SStructInit [("zero", zero); ("equals", eq); ("plus", plus); ("neg", neg); ("minus", min);
                         ("one", one); ("times", times); ("inv", inv); ("div", div);
                         ("make_poly", mpoly); ("deg", deg); ("poly_neg", pneg)] 
        and (t0, s0) = semant gamma epsilon zero
        and (teq, seq) = semant gamma epsilon eq
        and (tpl, spl) = semant gamma epsilon plus
        and (tneg, sneg) = semant gamma epsilon neg
        and (tmin, smin) = semant gamma epsilon (build_minus plus neg texp)
        and (t1, s1) = semant gamma epsilon one
        and (ttim, stim) = semant gamma epsilon times
        and (tinv, sinv) = semant gamma epsilon inv
        and (tdiv, sdiv) = semant gamma epsilon (build_div times inv texp)
        and (tmp, smp) = semant gamma epsilon (make_poly texp)
        and (tdeg, sdeg) = semant gamma epsilon (poly_deg texp field_count)
        and (tpneg, spneg) = semant gamma epsilon (poly_neg neg texp field_count)
        (*and (tppl, sppl) = semant gamma epsilon (poly_plus texp plus field_count)*)
        in (match (t0, teq, tpl, tneg, t1, ttim, tinv) with 
            (t1, FunType (ParamType [t2; t3], BoolExpr), 
                 FunType (ParamType [t4; t5], t6),
                 FunType (ParamType [t7], t8),
             t9, FunType (ParamType [t10; t11], t12),
                 FunType (ParamType [t13], t14)) ->
                if eq_types [texp; t1; t2; t3; t4; t5; t6; t7; t8; 
                                   t9; t10; t11; t12; t13; t14]
                then (FieldType texp, build_field (t0, s0) (teq, seq) (tpl, spl) (tneg, sneg)
                                            (tmin, smin) (t1, s1) (ttim, stim) (tinv, sinv)
                                            (tdiv, sdiv) (tmp, smp) (tdeg, sdeg) (tpneg, spneg))
                else raise (Failure "Field parameter has inconsistent type")
            | _ -> raise (Failure "Equals, plus, negate, times or inverse function had wrong number of arguments"))

      | _ -> raise (Failure "Not yet implemented")

    and semant_call gamma epsilon call =
        let rec semant_call_inner = function
            (* subsequent calls *)
            Call (Call (e1', e2'), e2) ->
                let ((oft, fs), valid, sexpr_list, cft) = semant_call_inner (Call (e1', e2'))
                and (t2, s2) = semant gamma epsilon e2
                    in (match cft with
                        FunType (ParamType (pt :: pts), rt) ->
                            if eq_type pt t2
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
                            if eq_type pt t2
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
