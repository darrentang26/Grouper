(* Semantic Analysis *)

(* rho = ADT environment *)
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
let poly_binop_type ty = FunType (ParamType [PolyType ty; PolyType ty; ty], PolyType ty)
let unop_type ty = FunType (ParamType [ty], ty)
let poly_unop_type ty = FunType (ParamType [PolyType ty; ty], PolyType ty)
let mpoly_type ty = FunType (ParamType [ListType ty], PolyType ty)
let pdeg_type ty = FunType (ParamType [PolyType ty], IntExpr)
let comul_type ty = FunType (ParamType [ty; IntExpr; PolyType ty; ty], PolyType ty)
let bterm_type ty = FunType (ParamType [IntExpr; ty], PolyType ty)
let gcd_type ty = FunType (ParamType [ty; ty; ty], ty)

let get_fun opp (op_name, sexp) = opp = op_name

(* FIELDMOD *)
let group_list ty = [("zero", ty); ("equals", compare_type ty); ("plus", binop_type ty);
                    ("neg", unop_type ty); ("minus", binop_type ty)]
let field_list ty = (group_list ty) @ [("one", ty); ("times", binop_type ty); 
                       ("inv", unop_type ty); ("div", binop_type ty); 
                       ("make_poly", mpoly_type ty); ("poly_deg", pdeg_type ty);
                       ("poly_equals", compare_type (PolyType ty));
                       ("poly_plus", poly_binop_type ty);
                       ("poly_minus", poly_binop_type ty);
                       ("poly_neg", unop_type (PolyType ty));
                       ("poly_times", poly_binop_type ty);
                       ("poly_div", poly_binop_type ty);
                       ("poly_mod", poly_binop_type ty);
                       ("poly_gcd", poly_binop_type ty)]
let ring_list ty = (group_list ty) @ [("one", ty); ("times", binop_type ty); 
                       ("div", binop_type ty); ("mod", binop_type ty);
                       ("gcd", gcd_type ty)]
let ring_to_struct ty = StructTypeExpr (ring_list ty)
let field_to_struct ty = StructTypeExpr (field_list ty)

let build_minus plus neg ty =
    Function([("x", ty); ("y", ty)], Call(Call(plus, Name "x"), Call(neg, Name "y")))
let build_div times inv ty =
    Function([("x", ty); ("y", ty)], Call(Call(times, Name "x"), Call(inv, Name "y")))
let build_mod times div minus ty =
    Function([("x", ty); ("y", ty)], Call(Call(minus, Name "x"), Call(Call(times, Name "y"), (Call(Call(div, Name "x"), Name "y")))))
let build_make_poly ty =
    Function(["xs", ListType ty;], Name "xs")

let gcd_bind modd equals ty index body =
    let fun_name = "gcd." ^ string_of_int index in
    Let([((fun_name, gcd_type ty),
        Function([("x", ty); ("y", ty); ("zero", ty)],
            If(Call(Call(equals, Name "y"), Name "zero"),
                Name "x",
                Let([(("rem", ty), Call(Call(modd, Name "x"), Name "y"))],
                    Call(Call(Call(Name fun_name, Name "y"), Name "rem"), Name "zero")))))],
    body)

let poly_deg_bind ty index body =
    let fun_name = "poly_deg." ^ string_of_int index in
    Let([((fun_name, pdeg_type ty), 
        Function([("xs", ListType ty)], 
                    If (Unop(Null, Name "xs"), 
                        Literal (-1), 
                        Binop(Literal 1, Add, 
                              Call(Name fun_name, CdrExpr (Name "xs"))))))], 
        body)
(*let poly_deg ty index =
    let fun_name = "poly_deg." ^ string_of_int index
    in poly_deg_bind ty index (Name fun_name)*)

let poly_neg_bind neg ty index body =
    let fun_name = "poly_neg." ^ string_of_int index in
    Let([((fun_name, unop_type (ListType ty)),
        Function([("xs", ListType ty)],
                   If (Unop(Null, Name "xs"),
                       EmptyListExpr,
                       ConsExpr(Call(neg, CarExpr (Name "xs")), 
                                Call(Name fun_name, CdrExpr (Name "xs"))))))],
        body)
(*let poly_neg neg ty index =
    let fun_name = "poly_neg." ^ string_of_int index 
    in poly_neg_bind neg ty index (Name fun_name)*)

let poly_equals_bind equals ty index body =
    let fun_name = "poly_equals." ^ string_of_int index in
    Let([((fun_name, compare_type(ListType ty)),
        Function([("xs", ListType ty); ("ys", ListType ty)],
            If(Binop(Unop(Null, Name "xs"), And, Unop(Null, Name "ys")),
                BoolLit true,
                If(Binop(Unop(Null, Name "xs"), Or, Unop(Null, Name "ys")),
                   BoolLit false,
                   Binop(Call(Call(equals, CarExpr(Name "xs")), CarExpr (Name "ys")),
                         And,
                         Call(Call(Name fun_name, CdrExpr(Name "xs")), CdrExpr(Name "ys")))))))],
        body)

let poly_reduce_bind equals ty index body =
    let fun_name = "poly_reduce." ^ string_of_int index in
    Let([((fun_name, poly_unop_type ty),
        Function([("xs", ListType ty); ("zero", ty)],
            If(Unop(Null, Name "xs"),
               ConsExpr(Name "zero", EmptyListExpr),
               If(Call(Call(equals, CarExpr(Name "xs")), Name "zero"),
                  Call(Call(Name fun_name, CdrExpr(Name "xs")), Name "zero"),
                  Name "xs"))))],
    body)

let poly_plus_inner_bind plus ty index body =
    let build_name field = field ^ "." ^ string_of_int index in
    let fun_name = build_name "poly_plus_inner"
    and deg_name = build_name "poly_deg" in
    Let([((fun_name, binop_type (ListType ty)),
        Function([("xs", ListType ty); ("ys", ListType ty)],
            If (Binop(Unop(Null, Name "xs"), And, Unop(Null, Name "ys")),
                EmptyListExpr,
                Let([(("x", IntExpr), Call(Name deg_name, Name "xs")); (("y", IntExpr), Call (Name deg_name, Name "ys"))],
                    If (Binop(Name "x", Less, Name "y"), 
                        ConsExpr(CarExpr(Name "ys"), Call(Call(Name fun_name, Name "xs"), CdrExpr(Name "ys"))),
                        If (Binop(Name "x", Greater, Name "y"),
                            ConsExpr(CarExpr(Name "xs"), Call(Call(Name fun_name, Name "ys"), CdrExpr(Name "xs"))),
                            ConsExpr(Call(Call(plus, CarExpr(Name "xs")), CarExpr(Name "ys")),
                                     Call(Call(Name fun_name, CdrExpr(Name "xs")), CdrExpr(Name "ys")))))))))],
            body)


let poly_plus_bind plus ty index body =
    let build_name field = field ^ "." ^ string_of_int index in
    let fun_name = build_name "poly_plus"
    and red_name = build_name "poly_reduce"
    and in_name = build_name "poly_plus_inner" in
    let plus_body = Let([((fun_name, poly_binop_type ty),
        Function([("xs", ListType ty); ("ys", ListType ty); ("zero", ty)],
        Call(Call(Name red_name, Call(Call(Name in_name, Name "xs"), Name "ys")), Name "zero")))],
    body)
    in poly_plus_inner_bind plus ty index plus_body

(*let poly_plus plus ty index =
    let fun_name = "poly_plus." ^ string_of_int index
     in poly_plus_bind plus ty index (Name fun_name)*)

let build_poly_minus ty index =
    let plus_name = "poly_plus." ^ string_of_int index
    and neg_name = "poly_neg." ^ string_of_int index in
    Function([("xs", ListType ty); ("ys", ListType ty); ("zero", ty)],
        Call(Call(Call(Name plus_name, Name "xs"), Call(Name neg_name, Name "ys")), Name "zero"))

let co_mul_bind times ty index body =
    let fun_name = "co_mul." ^ (string_of_int index) in
    Let([((fun_name, comul_type ty), 
        Function([("coeff", ty); ("degree", IntExpr); ("xs", ListType ty); ("zero", ty)],
        If(Binop(Unop(Null, Name "xs"), And, Binop(Name "degree", Equal, Literal 0)),
           EmptyListExpr,
           If(Unop(Null, Name "xs"),
              ConsExpr(Name "zero", Call(Call(Call(Call(Name fun_name, Name "coeff"), Binop(Name "degree", Sub, Literal 1)), Name "xs"), Name "zero")),
              ConsExpr(Call(Call(times, Name "coeff"), CarExpr(Name "xs")),
                       Call(Call(Call(Call(Name fun_name, Name "coeff"), Name "degree"), CdrExpr(Name "xs")), Name "zero"))))))],
    body)

let poly_times_bind  times plus ty index body =
    let build_name field = field ^ "." ^ string_of_int index in
    let fun_name = build_name "poly_times"
    and plus_name = build_name "poly_plus"
    and deg_name = build_name "poly_deg"
    and comul_name = build_name "co_mul" in
    let times_body = Let([((fun_name, poly_binop_type ty),
        Function([("xs", ListType ty); ("ys", ListType ty); ("zero", ty)],
            If(Unop(Null, Name "xs"),
               EmptyListExpr,
               Let([(("x", IntExpr), Call(Name deg_name, Name "xs"))],
                    Call(Call(Call(Name plus_name, Call(Call(Call(Call(Name comul_name, CarExpr(Name "xs")), Call(Name deg_name, Name "xs")), Name "ys"), Name "zero")), 
                         Call(Call(Call(Name fun_name, CdrExpr(Name "xs")), Name "ys"), Name "zero")), Name "zero")))))],
        body) in
     co_mul_bind times ty index times_body 

(*let build_poly_times times plus ty index =
    let fun_name = "poly_times." ^ string_of_int index in
        poly_times_bind times plus ty index (Name fun_name)*)

let build_term_bind ty index body =
    let fun_name = "build_term." ^ string_of_int index in
    Let([((fun_name, bterm_type ty),
        Function([("x", IntExpr); ("zero", ty)],
            If(Binop(Name "x", Equal, Literal 0),
               EmptyListExpr,
               ConsExpr(Name "zero", Call(Call(Name fun_name, Binop(Name "x", Sub, Literal 1)), Name "zero")))))],
    body)

let poly_div_inner_bind div ty index body =
    let build_name field = field ^ "." ^ string_of_int index in
    let fun_name = build_name "poly_div_inner"
    and term_name = build_name "build_term"
    and times_name = build_name "poly_times"
    and deg_name = build_name "poly_deg"
    and eq_name = build_name "poly_equals"
    and poly_min = build_poly_minus ty index in
    let div_body = Let([((fun_name, poly_binop_type ty),
        Function([("xs", ListType ty); ("ys", ListType ty); ("zero", ty)],
            If(Unop(Null, Name "ys"),
               EmptyListExpr,
               Let([(("x", IntExpr), Call(Name deg_name, Name "xs")); (("y", IntExpr), Call(Name deg_name, Name "ys"))],
                    If(Binop(Binop(Name "x", Less, Name "y"), Or, Call(Call(Name eq_name, Name "xs"), ConsExpr(Name "zero", EmptyListExpr))),
                       EmptyListExpr,
                       Let([(("lead_coeff", ty), Call(Call(div, CarExpr(Name "xs")), CarExpr(Name "ys")))],
                       Let([(("lead_term", ListType ty), ConsExpr(Name "lead_coeff", Call(Call(Name term_name, Binop(Name "x", Sub, Name "y")), Name "zero")))],
                       Let([(("diff", ListType ty), Call(Call(Call(poly_min, Name "xs"), Call(Call(Call(Name times_name, Name "lead_term"), Name "ys"), Name "zero")), Name "zero"))],
                            ConsExpr(Name "lead_coeff", Call(Call(Call(Name fun_name, Name "diff"), Name "ys"), Name "zero"))))))))))],
        body) in
        build_term_bind ty index div_body
let poly_div_bind div ty index body =
    let fun_name = "poly_div." ^ string_of_int index
    and inner_name = "poly_div_inner." ^ string_of_int index in
    let div_body = Let([((fun_name, poly_binop_type ty),
        Function([("xs", ListType ty); ("ys", ListType ty); ("zero", ty)],
            Let([(("q", ListType ty), Call(Call(Call(Name inner_name, Name "xs"), Name "ys"), Name "zero"))],
                If(Unop(Null, Name "q"),
                   ConsExpr(Name "zero", Name "q"),
                   Name "q"))))], body)
in poly_div_inner_bind div ty index div_body

let poly_mod_bind div ty index body =
    let build_name field = field ^ "." ^ string_of_int index in
    let fun_name = build_name "poly_mod"
    and term_name = build_name "build_term"
    and times_name = build_name "poly_times"
    and deg_name = build_name "poly_deg"
    and eq_name = build_name "poly_equals"
    and poly_min = build_poly_minus ty index in
    Let([((fun_name, poly_binop_type ty),
        Function([("xs", ListType ty); ("ys", ListType ty); ("zero", ty)],
            If(Unop(Null, Name "ys"),
               Name "xs",
               Let([(("x", IntExpr), Call(Name deg_name, Name "xs")); (("y", IntExpr), Call(Name deg_name, Name "ys"))],
                    If(Binop(Binop(Name "x", Less, Name "y"), Or, Call(Call(Name eq_name, Name "xs"), ConsExpr(Name "zero", EmptyListExpr))),
                       Name "xs",
                       Let([(("lead_coeff", ty), Call(Call(div, CarExpr(Name "xs")), CarExpr(Name "ys")))],
                       Let([(("lead_term", ListType ty), ConsExpr(Name "lead_coeff", Call(Call(Name term_name, Binop(Name "x", Sub, Name "y")), Name "zero")))],
                       Let([(("diff", ListType ty), Call(Call(Call(poly_min, Name "xs"), Call(Call(Call(Name times_name, Name "lead_term"), Name "ys"), Name "zero")), Name "zero"))],
                            Call(Call(Call(Name fun_name, Name "diff"), Name "ys"), Name "zero")))))))))],
        body)
let poly_gcd_bind ty index body =
    let build_name field = field ^ "." ^ string_of_int index in
    let fun_name = build_name "poly_gcd"
    and eq_name = build_name "poly_equals"
    and mod_name = build_name "poly_mod" in
    Let([((fun_name, poly_binop_type ty),
        Function([("xs", ListType ty); ("ys", ListType ty); ("zero", ty)],
            If(Call(Call(Name eq_name, Name "ys"), ConsExpr(Name "zero", EmptyListExpr)),
               Name "xs",
               Let([(("rem", ListType ty), Call(Call(Call(Name mod_name, Name "xs"), Name "ys"), Name "zero"))],
                 Call(Call(Call(Name fun_name, Name "ys"), Name "rem"), Name "zero")))))],
    body)

(*let build_poly_mod ty index =
    let poly_minus = build_poly_minus ty index
    and times_name = "poly_times." ^ string_of_int index
    and div_name = "poly_div." ^ string_of_int index in
        Function([("xs", ListType ty); ("ys", ListType ty); ("zero", ty)],
            Call(Call(Call(poly_minus, Name "xs"), Call(Call(Call(Name times_name, Name "ys"), Call(Call(Call(Name div_name, Name "xs"), Name "ys"), Name "zero")), Name "zero")), Name "zero"))
   *) 
let lookup_adt name rho = 
    try StringMap.find name rho
        with Not_found -> raise (Failure ("unbound identifier " ^ name))

(*let type_eq ty1 ty2 = raise (Failure "not implemented")*)
let rec eq_type ty1 ty2 = (match ty1, ty2 with
  FunType (ParamType ty1ps, ty1rt), FunType (ParamType ty2ps, ty2rt) ->
    (eq_type (ParamType ty1ps) (ParamType ty2ps)) && (eq_type ty1rt ty2rt)
| ListType ty, EmptyListType | EmptyListType, ListType ty
| PolyType ty, EmptyListType | EmptyListType, PolyType ty -> true
| PolyType t1, ListType t2 | ListType t1, PolyType t2 -> eq_type t1 t2
| ParamType ty1ps, ParamType ty2ps -> List.for_all2 (fun e1 e2 -> eq_type e1 e2) ty1ps ty2ps
| _ -> ty1 = ty2)

let rec eq_types = function
    t1::t2::ts -> eq_type t1 t2 && eq_types (t1::ts)
|   _          -> true


let check (typ_decls, body) = let
    gamma = List.fold_left (fun env (name, texpr) -> StringMap.add name texpr env) 
        StringMap.empty 
        typ_decls and 
    
    epsilon = StringMap.empty and
    user_typs = List.fold_left (fun env (name, texpr) -> StringMap.add name texpr env) 
        StringMap.empty 
        typ_decls

    (* check adt types for uniqueness *)
    in let rho = List.fold_left 
        (fun env (name, texpr) -> match texpr with
          AdtTypeExpr (binds) -> List.fold_left
            (fun env (adtname, ty) -> 
                if StringMap.mem adtname env
                    then raise (Failure ("adt " ^ adtname ^ " already defined"))
                    else StringMap.add adtname (name, ty) env)
            env
            binds
        | _ -> env)
        StringMap.empty
        typ_decls

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
                      ListType t2' | PolyType t2' -> if eq_type t1 t2'
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
            (t2, s2) = semant gamma epsilon e2 in
            let unalias = function
              TypNameExpr name -> StringMap.find name user_typs 
            | typ -> typ
                in if not (eq_type (unalias t1) (unalias t2)) then raise (Failure ("cannot apply binary operator to arguments of different types (" ^ string_of_type_expr t1 ^ " and " ^ string_of_type_expr t2 ^ ")"))
                    (* Need to change this to work with algebra stuff!!!! *)
                    else (match op, unalias t1 with
                      (Add, IntExpr) | (Add, FloatExpr) | (Add, StringExpr) -> (t1, SBinop ((t1, s1), Add, (t2, s2)))
                    | (Sub, IntExpr) | (Sub, FloatExpr) -> (t1, SBinop ((t1, s1), Sub, (t2, s2)))
                    | (Mult, IntExpr) | (Mult, FloatExpr) -> (t1, SBinop ((t1, s1), Mult, (t2, s2)))
                    | (Div, IntExpr) | (Div, FloatExpr) -> (t1, SBinop ((t1, s1), Div, (t2, s2)))
                    | (Equal, IntExpr) | (Equal, FloatExpr) | (Equal, StringExpr) | (Equal, EmptyListType) -> (BoolExpr, SBinop ((t1, s1), Equal, (t2, s2))) 
                    | (Equal, StructTypeExpr fields) -> (BoolExpr, SBinop ((StructTypeExpr fields, s1), Equal, (StructTypeExpr fields, s2)))
                    | (Equal, ListType typ) -> (match typ with 
                        FloatExpr | IntExpr | BoolExpr -> (BoolExpr, SBinop((ListType typ, s1), op, (ListType typ, s2)))
                      | StructTypeExpr fields -> (BoolExpr, SBinop((ListType (StructTypeExpr fields), s1), op, (ListType (StructTypeExpr fields), s2)))
                      | _ -> raise (Failure ("Cannot check for equality of list of type " ^ (string_of_type_expr typ))))
                    | (Neq, IntExpr) | (Neq, FloatExpr) | (Neq, StringExpr) -> (BoolExpr, SBinop ((t1, s1), Neq, (t2, s2)))
                    | (Less, IntExpr) | (Less, FloatExpr) -> (BoolExpr, SBinop ((t1, s1), Less, (t2, s2)))
                    | (Leq, IntExpr) | (Leq, FloatExpr) -> (BoolExpr, SBinop ((t1, s1), Leq, (t2, s2)))
                    | (Greater, IntExpr) | (Greater, FloatExpr) -> (BoolExpr, SBinop ((t1, s1), Greater, (t2, s2)))
                    | (Geq, IntExpr) | (Geq, FloatExpr) -> (BoolExpr, SBinop ((t1, s1), Geq, (t2, s2)))
                    | (And, BoolExpr) -> (t1, SBinop ((BoolExpr, s1), And, (t2, s2)))
                    | (Or, BoolExpr) -> (t1, SBinop ((t1, s1), Or, (t2, s2)))
                    | (Mod, IntExpr) -> (t1, SBinop ((t1, s1), Mod, (t2, s2)))
                    | _ ->
                        (match t1 with
                        PolyType tau -> let (opp, sexp) = try List.find (get_fun ("p" ^ string_of_op op)) (StringMap.find (string_of_type_expr tau) epsilon)
                            with Not_found -> raise (Failure ("cannot apply " ^ string_of_op op ^ " to arguments of type " ^ string_of_type_expr t1))
                            in let (_, (_, szero)) = try List.find (get_fun ("zero")) (StringMap.find (string_of_type_expr tau) epsilon)
                                with Not_found -> raise (Failure ("cannot apply " ^ string_of_op op ^ " to arguments of type " ^ string_of_type_expr t1))
                            in let ty = (match opp with "p==" -> BoolExpr | _ -> t1)
                            in (ty, SCall(sexp, [(t1, s1); (t2, s2); (tau, szero)]))

                        | _ -> let (opp, sexp) = try List.find (get_fun (string_of_op op)) (StringMap.find (string_of_type_expr t1) epsilon)
                            with Not_found -> raise (Failure ("cannot apply " ^ string_of_op op ^ " to arguments of type " ^ string_of_type_expr t1))
                            in let ty = (match opp with "==" -> BoolExpr | _ -> t1)
                            in (ty, SCall(sexp, [(t1, s1); (t2, s2)]))))

      | Unop (uop, expr) -> let
            (ty, sx) = semant gamma epsilon expr
                in (match uop, ty with
                      (Neg, IntExpr) | (Neg, FloatExpr) -> (ty, SUnop (Neg, (ty, sx)))
                    | (Not, BoolExpr) -> (ty, SUnop (Not, (ty, sx)))
                    | (Neg, _) -> let (opp, sexp) = try (match ty with
                        PolyType tau -> List.find (get_fun "pn") (StringMap.find (string_of_type_expr tau) epsilon) 
                        | _ -> List.find (get_fun "n") (StringMap.find (string_of_type_expr ty) epsilon))
                            with Not_found -> raise (Failure ("cannot apply " ^ string_of_uop uop ^ " to argument of type " ^ string_of_type_expr ty))
                            in (ty, SCall(sexp, [(ty, sx)]))
                    | (Null, ListType tau) -> (BoolExpr, SUnop (Null, (ty, sx)))
                    | (Null, EmptyListType) -> (BoolExpr, SBoolLit true)
                    | _ -> raise (Failure ("cannot apply " ^ string_of_uop uop ^ " to argument of type " ^ string_of_type_expr ty)))
                    (* This needs to have algebra added to it *)
      | Let (binds, body) ->
            let rec struct_sx sexp = (match sexp with
                                SLet (binds, (ty, sx)) -> struct_sx sx
                            |   SStructInit sexprs -> sexprs
                            | _ -> []) in
            let field_count = StringMap.cardinal epsilon in
            let field_name = "field." ^ string_of_int field_count in
            let ring_name = "ring." ^ string_of_int field_count in
            let gamma_fun = StringMap.filter 
                (fun name ty -> (match ty with
                                        FunType _ -> true
                                        |       _ -> false))
                gamma in 
            let gamma' = List.fold_left
                (fun gamma ((name, tl), expr) -> let
                    gamma' = (match tl with
                              (FunType _) -> StringMap.add name tl gamma_fun
                            | FieldType ty -> StringMap.add field_name (field_to_struct ty) gamma
                            | RingType ty -> StringMap.add ring_name (ring_to_struct ty) gamma
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
                gamma' = match tl with (FunType _) -> StringMap.add name tl gamma_fun 
                        | FieldType ty -> StringMap.add field_name (field_to_struct ty) gamma
                        | RingType ty -> StringMap.add ring_name (ring_to_struct ty) gamma
                        | _ -> gamma
                    in ((name, tl), semant gamma' epsilon expr)) binds
            in let
                epsilon' = List.fold_left
                (fun epsilon ((name, ty), sexpr) -> (match sexpr with
                        (GroupType ty, SStructInit [zero; ("equals", seq); ("plus", spl); 
                                                    ("neg", sneg); ("minus", smin)])
                            -> StringMap.add (string_of_type_expr ty) 
                                            [("==", seq); ("+", spl);
                                             ("n", sneg); ("-", smin)] epsilon
                        | (RingType ty, sx) ->
                        let build_ref ty field = (ty, SName (name ^ "." ^ field))
                        in (match struct_sx sx with
                            [("zero", szero); ("equals", seq); ("plus", spl);
                                   ("neg", sneg); ("minus", smin); one;
                                   ("times", stim); ("div", sdiv);
                                   ("mod", smod); gcd]
                                -> StringMap.add (string_of_type_expr ty)
                                    [("==", seq); ("+", spl); ("n", sneg); ("-", smin);
                                             ("*", stim); ("/", sdiv); ("mod", smod);
                                             ("zero", szero)] epsilon
                                | _ -> epsilon)
                        (*| (FieldType ty, SStructInit [zero; ("equals", seq); ("plus", spl); 
                                                    ("neg", sneg); ("minus", smin); one; 
                                                    ("times", stim); inv; ("div", sdiv)])
                            -> StringMap.add (string_of_type_expr ty)
                                            [("==", seq); ("+", spl); ("n", sneg); ("-", smin);
                                             ("*", stim); ("/", sdiv)] epsilon*)
                        | (FieldType ty, sx) ->
                        let build_ref ty field = (ty, SName (name ^ "." ^ field))
                        in (match struct_sx sx with
                            [("zero", szero); ("equals", seq); ("plus", spl);
                                   ("neg", sneg); ("minus", smin); one;
                                   ("times", stim); inv; ("div", sdiv);
                                   make_poly; poly_deg; ("poly_equals", speq);
                                   ("poly_plus", sppl); ("poly_minus", spmin);
                                   ("poly_neg", spneg); ("poly_times", sptim);
                                   ("poly_div", spdiv); ("poly_mod", spmod);
                                   poly_gcd]
                                -> StringMap.add (string_of_type_expr ty)
                                    [("==", seq); ("+", spl); ("n", sneg); ("-", smin);
                                             ("*", stim); ("/", sdiv); 
                                             ("p==", speq); ("p+", sppl);
                                             ("p-", spmin); ("pn", spneg); ("p*", sptim);
                                             ("p/", spdiv); ("pmod", spmod);
                                             ("zero", szero)] epsilon
                            | _ -> epsilon)
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
      | AdtExpr target -> (match target with
            TargetWildName target_name -> let
                (type_name, arg_type) = lookup_adt target_name rho in
                    if arg_type = VoidExpr
                        then (TypNameExpr type_name, SAdtExpr (STargetWildName target_name))
                        else raise (Failure (target_name ^ " does not take any arguments"))
          | TargetWildApp (target_name, inner_target) -> let
                (type_name, arg_type) = lookup_adt target_name rho in
                    if arg_type = VoidExpr
                        then raise (Failure (target_name ^ " expects nothing as an argument"))
                        else (match inner_target with
                            TargetWildLiteral expr -> let
                                (ty, sx) = semant gamma epsilon expr
                                    in if arg_type = ty
                                        then (TypNameExpr type_name, SAdtExpr (STargetWildApp (target_name, STargetWildLiteral (ty, sx))))
                                        else raise (Failure ("cannot apply " ^ string_of_type_expr ty ^ " to " ^ string_of_type_expr arg_type)))
          | _ -> raise (Failure ("cannot use " ^ string_of_target target ^ " as a top-level target")))
      | StructInit bindsList -> (*let rec
            (heck_consec_dupes = function
                x::y::rest -> if x = y then raise (Failure "Struct field names must be unique")
                           else x::(check_consec_dupes (y::rest))
              | x::[] -> x::[] in let rec
            get_names = function
                
            _ -> check_consec_dupes (List.sort String.compare bindsList) in*) 
            let eq_binds b1s b2s = (match (b1s, b2s) with
                ([], []) -> true
            |   ((n1, t1) :: _, (n2, t2) :: _) -> n1 = n2 && eq_type t1 t2
            |   _ -> false) in
            let typed_binds = List.map (fun (name, expr) -> 
                                     (name, semant gamma epsilon expr)) 
                                   bindsList in let
            comparable = List.map (fun (name,(typ, expr)) -> (name, typ)) typed_binds in let rec
            struct_type = function
                (name, StructTypeExpr(fields))::binds -> if eq_binds fields comparable 
                                                                then if String.starts_with "field." name
                                                                     then let ((_, ty) :: _) = fields in
                                                                        FieldType ty
                                                                     else if String.starts_with "ring." name
                                                                     then let ((_, ty) :: _) = fields in
                                                                        RingType ty
                                                                     else TypNameExpr name
                                                                else struct_type binds
             |  _::binds -> struct_type binds
             |  [] -> raise (Failure "initialized a struct that matches no declared struct type") in
            (struct_type (StringMap.bindings gamma), SStructInit(typed_binds))
      | StructRef (var, field) -> let 
        (typ_name, sexp) = semant gamma epsilon (Name(var)) in (match typ_name with
           TypNameExpr(typ) -> let
             accessed_type = lookup_type typ user_typs in (match accessed_type with
                StructTypeExpr(binds) -> let 
                   (_, found_type) = List.find (fun (curr_field, _) -> curr_field = field) binds in
                     (found_type, SStructRef(var,field))
                |  _ -> raise (Failure (var ^ " is not a struct")))
            |  GroupType ty -> 
                let (n, t) = try List.find (fun (name, tau) -> name = field) (group_list ty)
                                            with Not_found -> raise (Failure (field ^ " is not a valid group element"))

                    in (t, SStructRef(var, field))
            |  RingType ty -> 
                let (n, t) = try List.find (fun (name, tau) -> name = field) (ring_list ty)
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
      | Ring (texp, zero, eq, plus, neg, one, times, div) ->
        let field_count = StringMap.cardinal epsilon in
        let build_ring zero eq plus neg min one times div modd index =
            let str_index = string_of_int index in
            let gen_bind field = (field, Name (field ^ "." ^ str_index)) in
            let struct_body = StructInit [("zero", zero); ("equals", eq); ("plus", plus); 
                                          ("neg", neg); ("minus", min); ("one", one); 
                                          ("times", times); ("div", div); ("mod", modd); gen_bind "gcd"]
            in gcd_bind modd eq texp index struct_body
        and (t0, s0) = semant gamma epsilon zero
        and (teq, seq) = semant gamma epsilon eq
        and (tpl, spl) = semant gamma epsilon plus
        and (tneg, sneg) = semant gamma epsilon neg
        and minus = build_minus plus neg texp
        and (t1, s1) = semant gamma epsilon one
        and (ttim, stim) = semant gamma epsilon times
        and (tdiv, sdiv) = semant gamma epsilon div
        in let modd = build_mod times div minus texp
        in (match (t0, teq, tpl, tneg, t1, ttim, tdiv) with 
            (t1, FunType (ParamType [t2; t3], BoolExpr), 
                 FunType (ParamType [t4; t5], t6),
                 FunType (ParamType [t7], t8),
             t9, FunType (ParamType [t10; t11], t12),
                 FunType (ParamType [t13; t14], t15)) ->
                if eq_types [texp; t1; t2; t3; t4; t5; t6; t7; t8; 
                                   t9; t10; t11; t12; t13; t14; t15]
                then let ring_struct = build_ring zero eq plus neg minus one times div modd field_count
                    in let (t, s) = semant gamma epsilon ring_struct
                    in (RingType texp, s)
                else raise (Failure "Ring parameter has inconsistent type")
            | _ -> raise (Failure "Equals, plus, negate, times or div function had wrong number of arguments"))
      | Field (texp, zero, eq, plus, neg, one, times, inv) ->
        let field_count = StringMap.cardinal epsilon in
        let build_field zero eq plus neg min one times inv div mpoly pmin index =
            let str_index = string_of_int index in
            let gen_bind field = (field, Name (field ^ "." ^ str_index)) in
            let struct_body = StructInit [("zero", zero); ("equals", eq); ("plus", plus); ("neg", neg); ("minus", min);
                         ("one", one); ("times", times); ("inv", inv); ("div", div);
                         ("make_poly", mpoly); gen_bind "poly_deg"; gen_bind "poly_equals";
                         gen_bind "poly_plus"; ("poly_minus", pmin); 
                         gen_bind "poly_neg"; gen_bind "poly_times";
                         gen_bind "poly_div"; gen_bind "poly_mod";
                         gen_bind "poly_gcd"] in
            let gcd_body = poly_gcd_bind texp index struct_body in
            let mod_body = poly_mod_bind div texp index gcd_body in
            let div_body = poly_div_bind div texp index mod_body in
            let times_body = poly_times_bind times plus texp index div_body in
            let plus_body = poly_plus_bind plus texp index times_body in
            let neg_body = poly_neg_bind neg texp index plus_body in
            let eq_body = poly_equals_bind eq texp index neg_body in
            let deg_body = poly_deg_bind texp index eq_body in
            poly_reduce_bind eq texp index deg_body

        and (t0, s0) = semant gamma epsilon zero
        and (teq, seq) = semant gamma epsilon eq
        and (tpl, spl) = semant gamma epsilon plus
        and (tneg, sneg) = semant gamma epsilon neg
        and min = build_minus plus neg texp
        and (t1, s1) = semant gamma epsilon one
        and (ttim, stim) = semant gamma epsilon times
        and (tinv, sinv) = semant gamma epsilon inv
        and div = build_div times inv texp
        and mpoly = build_make_poly texp
        and pmin = build_poly_minus texp field_count
        in (match (t0, teq, tpl, tneg, t1, ttim, tinv) with 
            (t1, FunType (ParamType [t2; t3], BoolExpr), 
                 FunType (ParamType [t4; t5], t6),
                 FunType (ParamType [t7], t8),
             t9, FunType (ParamType [t10; t11], t12),
                 FunType (ParamType [t13], t14)) ->
                if eq_types [texp; t1; t2; t3; t4; t5; t6; t7; t8; 
                                   t9; t10; t11; t12; t13; t14]
                then let field_struct = build_field zero eq plus neg min one times inv div mpoly pmin field_count
                    in let (t, s) = semant gamma epsilon field_struct
                    in (FieldType texp, s)
                else raise (Failure "Field parameter has inconsistent type")
            | _ -> raise (Failure "Equals, plus, negate, times or inverse function had wrong number of arguments"))
      | Match (names, evals) ->
            let binds = List.rev_map (fun (name) -> (name, lookup_type name gamma)) names
            in let sevals: (Sast.spattern * Sast.sexpr) list = List.fold_left
                (fun evals (pattern, expr)->
                    match pattern with Pattern targets ->
                        let (stargets, bound_vars) = (List.fold_left2
                            (fun (stargets, bound_vars) target (name, tl) ->
                                let ((starget, tr), bound_vars') = semant_target gamma epsilon target
                                    in let equal = match (tl, tr) with
                                        (TypNameExpr nl, TypNameExpr nr) -> nl = nr || nl = "_" || nr = "_"
                                      | _ -> tl = tr
                                        in if equal
                                            then (starget :: stargets, bound_vars' @ bound_vars)
                                            else raise (Failure ("cannot match a variable of type " ^ string_of_type_expr tl ^ " on a pattern of type " ^ string_of_type_expr tr)))
                            ([], [])
                            targets
                            binds)
                        (* in let _ = raise (Failure (String.concat ", " (List.map string_of_bind bound_vars))) *)
                        in let sexpr = semant
                            (List.fold_left
                                (fun gamma (name, tl) -> StringMap.add name tl gamma)
                                gamma
                                bound_vars)
                            epsilon
                            expr
                            in ((SPattern stargets), sexpr) :: evals)
                []
                evals
            in let rt: Ast.type_expr = List.fold_left
                (fun rt' (spattern, (rt, sx)) ->
                    if rt != rt'
                        then raise (Failure ("patterns of different types"))
                        else rt')
                (fst (snd (List.hd sevals)))
                sevals
                in (rt, SMatch (binds, sevals))
            
      | Call (e1, e2) -> semant_call gamma epsilon (Call (e1, e2))
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



      | expr -> raise (Failure (string_of_expr expr ^ " not yet implemented"))

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
    
    
    and semant_target gamma epsilon target = match target with
        TargetWildName name -> let (type_name, arg_type) = lookup_adt name rho
            in if arg_type = VoidExpr
                then ((STargetWildName name, TypNameExpr type_name), [])
                else raise (Failure (name ^ " is a constructor on " ^ string_of_type_expr arg_type))
      | TargetWildLiteral expr -> let (t, s) = semant gamma epsilon expr
            in (match s with
                SName n -> ((STargetWildLiteral (t, s), t), [(n, t)])
              | _ -> ((STargetWildLiteral (t, s), t), []))
      | TargetWildApp (name, target) ->
            let (type_name, arg_type) = lookup_adt name rho
            in let ((starget, ty), bound_vars) = match target with
                TargetWildLiteral (Name n) -> 
                    let sname = (arg_type, SName n)
                        in ((STargetWildLiteral (sname), arg_type), [(n, arg_type)])
              | _ -> semant_target gamma epsilon target
            (* use type equal function *)
                in if ty = arg_type || (ty != VoidExpr && target = CatchAll)
                    then ((STargetWildApp (name, starget), TypNameExpr type_name), bound_vars)
                    else raise (Failure ("cannot construct " ^ name ^ " with an expression of type " ^ string_of_type_expr ty))
      | CatchAll -> ((SCatchAll, TypNameExpr "_"), [])
    
        in match body with
        Let _ -> (typ_decls, semant gamma epsilon body)
        | _ -> raise (Failure "top-level expression must be a let expression")
