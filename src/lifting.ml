open Ast
open Sast

module StringSet = Set.Make(String)

exception Failure of string

(* mark all free characters *)
(* the first character in an occurence of a free name is marked with * *)
let mark_free sexpr =
  let rec mark_free' (t, sx) bound_names = match sx with
    SLiteral _ | SFliteral _ | SBoolLit _ | SStringLit _ -> (t, sx)
  | SPairExpr (sexpr1, sexpr2) -> (t, SPairExpr (mark_free' sexpr1 bound_names, mark_free' sexpr2 bound_names))
  | SConsExpr (sexpr1, sexpr2) -> (t, SConsExpr (mark_free' sexpr1 bound_names, mark_free' sexpr2 bound_names))
  | SEmptyListExpr -> (t, sx)
  | SName n -> (t, SName (if (List.exists (fun (x) -> x = n) bound_names) then n else ("*" ^ n)))
  | SBinop (sexpr1, op, sexpr2) -> (t, SBinop (mark_free' sexpr1 bound_names, op, mark_free' sexpr2 bound_names))
  | SUnop (uop, sexpr) -> (t, SUnop (uop, mark_free' sexpr bound_names))
  | SLet (binds, body) -> let
    (bound_names, binds) = List.fold_left
      (fun (bound_names, binds) ((name, tl), sexpr) -> match tl with
          FunType _ -> let
            bound_names = name :: bound_names
            in (bound_names, ((name, tl), mark_free' sexpr bound_names) :: binds)
          | _ -> (name :: bound_names, ((name, tl), sexpr) :: binds))
      (bound_names, [])
      binds
      in (t, SLet (binds, mark_free' body bound_names))
  | SFunction ([(name, ty)], body) -> (t, SFunction ([(name, ty)], mark_free' body [name]))
  | SCall (s1, s2) -> (t, SCall (mark_free' s1 bound_names, mark_free' s2 bound_names))
  | SIf (s1, s2, s3) -> (t, SIf (mark_free' s1 bound_names, mark_free' s2 bound_names, mark_free' s3 bound_names))
  | SPrint sexpr -> (t, SPrint (mark_free' sexpr bound_names))
  in mark_free' sexpr []

let rec get_free (t, sx) = match sx with
  SLiteral _ | SFliteral _ | SBoolLit _ | SStringLit _ -> []
| SPairExpr (sexpr1, sexpr2) -> get_free sexpr1 @ get_free sexpr2
| SConsExpr (sexpr1, sexpr2) -> get_free sexpr1 @ get_free sexpr2
| SEmptyListExpr -> []
| SName n -> if (String.get n 0) = '*' then [(n, t)] else []
| SBinop (sexpr1, op, sexpr2) -> get_free sexpr1 @ get_free sexpr2
| SUnop (uop, sexpr) -> get_free sexpr
| SLet (binds, body) -> let
  bind_frees = List.fold_left 
    (fun (bind_frees) ((name, tl), sexpr) -> match tl with
        FunType _ -> (bind_frees)
        | _ -> (get_free sexpr) @ (bind_frees))
    []
    binds
    in get_free body @ bind_frees
| SFunction ([(name, ty)], body) -> let
  body_frees = get_free body
    in []
    (* List.fold_left
      (fun (free_variables) (n, t) -> if n = "*" ^ name then free_variables else (n, t) :: free_variables)
      []
      body_frees *)
| SCall (s1, s2) -> get_free s1 @ get_free s2
| SIf (s1, s2, s3) -> get_free s1 @ get_free s2 @ get_free s3
| SPrint sexpr -> get_free sexpr

(* name all functions *)
let name_all sexpr = 
  let rec name_all' (t, sx) named = match sx with
    SLiteral _ | SFliteral _ | SBoolLit _ | SStringLit _ -> (t, sx) 
  | SPairExpr (sexpr1, sexpr2) -> (t, SPairExpr (name_all' sexpr1 false, name_all' sexpr2 false))
  | SConsExpr (sexpr1, sexpr2) -> (t, SConsExpr (name_all' sexpr1 false, name_all' sexpr2 false))
  | SEmptyListExpr -> (t, sx)
  | SName n -> (t, SName n)
  | SBinop (sexpr1, op, sexpr2) -> (t, SBinop (name_all' sexpr1 false, op, name_all' sexpr2 false))
  | SUnop (uop, sexpr) -> (t, SUnop (uop, name_all' sexpr false))
  | SLet (binds, body) -> let
    binds = List.fold_left
      (fun binds ((name, tl), sexpr) -> match tl with
          FunType _ -> ((name, tl), name_all' sexpr true) :: binds
          | _ -> ((name, tl), name_all' sexpr false) :: binds)
      []
      binds
      in (t, SLet (binds, name_all' body false))
  | SFunction ([(name, ty)], body) -> let
    body = name_all' body false
      in if named
        then (t, SFunction ([(name, ty)], body))
        else let
          free_variables = get_free body in let
          free_variables = List.rev (List.fold_left
            (fun (free_variables) (n, t) -> if n = "*" ^ name then free_variables else (n, t) :: free_variables)
            []
            free_variables)
            (* name: z, free_variables: *x, *y *)
            in let
              bind_type = List.fold_left 
                (fun (bt) (name, param_type) -> 
                  FunType (param_type, bt))
                t
                free_variables in let
              _, letbody = List.fold_left 
                (fun (FunType (_, rt), lb) (name, param_type) -> 
                  (rt, (rt, SCall (lb, (param_type, SName name)))))
                (bind_type, (bind_type, SName ("funname_" ^ name)))
                free_variables in let
              with_free_params = (bind_type, SFunction (free_variables @ [(name, ty)], body))
                in (t, SLet ([((("funname_" ^ name), bind_type), with_free_params)], letbody))
  (* | SFunction ([(name, ty)], body) -> (match t with FunType (_, rt) -> if named
      then (t, SFunction ([(name, ty)], name_all' body false))
      else let
        free_variables = get_free body in let
        free_variables = List.rev (List.fold_left
          (fun (free_variables) (name, ty) -> if List.exists (fun (n, t) -> n = name) free_variables then free_variables else (name, ty) :: free_variables)
          []
          free_variables) in let
        call = List.fold_left
          (fun (ft, sx) (free, free_type') ->
            (* raise (Failure ("free variables:\n[" ^ String.concat ", " (List.map string_of_bind free_variables) ^ "]"))) *)
            match ft with 
              FunType (free_type, ret_type) ->
                (ret_type, SCall((ft, sx), (free_type, SName free)))
            | _ -> (ft, sx))
          (t, SName "funname")
          free_variables
          in (t, SLet ([(("funname", t), (t, SFunction ([(name, ty)], name_all' body false)))],
            call))) *)
  | SCall (s1, s2) -> (t, SCall (name_all' s1 false, name_all' s2 false))
  | SIf (s1, s2, s3) -> (t, SIf (name_all' s1 false, name_all' s2 false, name_all' s3 false))
  | SPrint sexpr -> (t, SPrint (name_all' sexpr false))
  in name_all' sexpr false

(* lift free variables in to function definitions *)
let rec lift_free (t, sx) = match sx with
  SLiteral _ | SFliteral _ | SBoolLit _ | SStringLit _ -> (t, sx)
| SPairExpr (sexpr1, sexpr2) -> (t, SPairExpr (lift_free sexpr1, lift_free sexpr2))
| SConsExpr (sexpr1, sexpr2) -> (t, SConsExpr (lift_free sexpr1, lift_free sexpr2))
| SEmptyListExpr -> (t, sx)
| SName n -> (t, SName n)
| SBinop (sexpr1, op, sexpr2) -> (t, SBinop (lift_free sexpr1, op, lift_free sexpr2))
| SUnop (uop, sexpr) -> (t, SUnop (uop, lift_free sexpr))
| SLet (binds, body) -> let
  binds = List.fold_left
    (fun (binds) ((name, tl), sexpr) -> ((name, tl), lift_free sexpr) :: binds)
    []
    binds
    in (t, SLet (binds, lift_free body))
| SFunction ([(name, ty)], body) -> let
  free_variables = get_free body in let
  free_variables = List.fold_left
    (fun (free_variables) (name, ty) -> if List.exists (fun (n, t) -> n = name) free_variables then free_variables else (name, ty) :: free_variables)
    []
    free_variables
  in (t, SFunction (free_variables @ [(name, ty)], lift_free body))
| SCall (s1, s2) -> (t, SCall (lift_free s1, lift_free s2))
| SIf (s1, s2, s3) -> (t, SIf (lift_free s1, lift_free s2, lift_free s3))
| SPrint sexpr -> (t, SPrint (lift_free sexpr))

(* extract all local functions and create a sprogram_lifted *)
let lift_functions sexpr =
  let rec lift_functions' (t, sx) = match sx with
      SLiteral _ | SFliteral _ | SBoolLit _ | SStringLit _ -> ((t, sx), [])
    | SPairExpr (sexpr1, sexpr2) -> let
      (sexpr1, functions1) = lift_functions' sexpr1 and
      (sexpr2, functions2) = lift_functions' sexpr2
        in ((t, SPairExpr (sexpr1, sexpr2)), functions1 @ functions2)
    | SConsExpr (sexpr1, sexpr2) -> let
      (sexpr1, functions1) = lift_functions' sexpr1 and
      (sexpr2, functions2) = lift_functions' sexpr2
        in ((t, SConsExpr (sexpr1, sexpr2)), functions1 @ functions2)
    | SEmptyListExpr -> ((t, sx), [])
    | SName n -> ((t, SName n), [])
    | SBinop (sexpr1, op, sexpr2) -> let
      (sexpr1, functions1) = lift_functions' sexpr1 and
      (sexpr2, functions2) = lift_functions' sexpr2
        in ((t, SBinop (sexpr1, op, sexpr2)), functions1 @ functions2)
    | SUnop (uop, sexpr) -> let
      (sexpr, inner_functions) = lift_functions' sexpr
        in ((t, SUnop (uop, sexpr)), inner_functions)
    | SLet (binds, body) -> let
      (binds, functions) = List.fold_left
        (fun (binds, functions) ((name, tl), sexpr) -> let
          (sexpr, inner_functions) = lift_functions' sexpr
          in match tl with
            FunType _ -> (binds, functions @ inner_functions @ [((name, tl), sexpr)])
          | _ -> (((name, tl), sexpr) :: binds, functions @ inner_functions))
        ([], [])
        binds
        in let
          (sexpr, inner_functions) = lift_functions' body
          in (match binds with
            [] -> (sexpr, inner_functions @ functions)
          | _ -> ((t, SLet (binds, sexpr)), inner_functions @ functions))
    | SFunction (binds, body) -> 
      let (body, inner_functions) = lift_functions' body in 
        ((t, SFunction (binds, body)), inner_functions)
    | SCall (sexpr1, sexpr2) ->  let
      (sexpr1, functions1) = lift_functions' sexpr1 and
      (sexpr2, functions2) = lift_functions' sexpr2
        in ((t, SCall (sexpr1, sexpr2)), functions1 @ functions2)
    | SIf (sexpr1, sexpr2, sexpr3) ->  let
      (sexpr1, functions1) = lift_functions' sexpr1 and
      (sexpr2, functions2) = lift_functions' sexpr1 and
      (sexpr3, functions3) = lift_functions' sexpr2
        in ((t, SIf (sexpr1, sexpr2, sexpr3)), functions1 @ functions2 @ functions3)
    | SPrint sexpr ->  let
      (sexpr, inner_functions) = lift_functions' sexpr
        in ((t, SPrint sexpr), inner_functions)
    in lift_functions' sexpr
  
let lift_program (typ_decls, sexpr) = let
  (sexpr, functions) = lift_functions (name_all (mark_free sexpr))
  in (typ_decls, functions, sexpr)

(* ------- lifting finished *)
