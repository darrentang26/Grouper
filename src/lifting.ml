(* Lambda Lifting *)

open Ast
open Sast

module StringMap = Map.Make(String)

exception Failure of string

let is_previously_named prev_names name = 
  List.exists (fun (n) -> n = name) prev_names

let add_to_previous prev_names name = 
  if is_previously_named prev_names name then
    prev_names
  else
    name :: prev_names

(* names all functions *)
let name_all (typ_decls, sexpr) =
  let rec name_all' (ty, sx) prev_names is_named = match sx with
    SLiteral _ | SFliteral _ | SBoolLit _ | SStringLit _ -> ((ty, sx), prev_names)
  | SPairExpr (s1, s2) ->
      let (s1', prev_names1) = name_all' s1 prev_names false
      in let (s2', prev_names2) = name_all' s2 prev_names1 false
        in ((ty, SPairExpr (s1', s2')), prev_names2)
  | SConsExpr (s1, s2) ->
      let (s1', prev_names1) = name_all' s1 prev_names false
      in let (s2', prev_names2) = name_all' s2 prev_names1 false
        in ((ty, SConsExpr (s1', s2')), prev_names2)
  | SEmptyListExpr -> ((ty, SEmptyListExpr), prev_names)
  | SName n -> ((ty, SName n), prev_names)
  | SBinop (s1, op, s2) ->
      let (s1', prev_names1) = name_all' s1 prev_names false
      in let (s2', prev_names2) = name_all' s2 prev_names1 false
        in ((ty, SBinop (s1', op, s2')), prev_names2)
  | SUnop (op, sexpr) ->
      let (sexpr', prev_names) = name_all' sexpr prev_names false
        in ((ty, SUnop (op, sexpr')), prev_names)
  | SLet (bound_vars, body) ->
      let (bound_vars', prev_names') = List.fold_left
        (fun (bound_vars, prev_names) ((name, ty), sexpr) ->
          let (sexpr', prev_names') = name_all' sexpr prev_names true
            in (((name, ty), sexpr') :: bound_vars, prev_names'))
        ([], prev_names)
        bound_vars
      in let (body', prev_names'') = name_all' body prev_names' false
        in ((ty, SLet (bound_vars', body')), prev_names'')
  | SFunction (params, body) ->
    let (body', prev_names') = name_all' body prev_names false
      in if is_named
        then ((ty, SFunction (params, body')), prev_names')
        else
          let function_name = "f." ^ Int.to_string (List.length prev_names')
          in let bind = (function_name, ty)
          and right = (ty, SFunction (params, body'))
          and body = (ty, SName function_name)
            in ((ty, SLet ([(bind, right)], body)), add_to_previous prev_names' function_name)
  | SStructInit (inits) ->
    let (inits', prev_names') = List.fold_left
      (fun (inits, prev_names) (name, sexpr) ->
        let (sexpr', prev_names') = name_all' sexpr prev_names true
          in ((name, sexpr') :: inits, prev_names'))
      ([], prev_names)
      inits
      in ((ty, SStructInit (inits')), prev_names')
  | SStructRef (struct_name, field) ->
    let prev_names' = add_to_previous prev_names struct_name
      in ((ty, SStructRef (struct_name, field)), prev_names')
  | SCall (fsexpr, sexprs) ->
    let (fsexpr', prev_names1) = name_all' fsexpr prev_names false
    in let (sexprs', prev_names2) = List.fold_left
      (fun (sexprs, prev_names) sexpr ->
        let (sexpr', prev_names') = name_all' sexpr prev_names false
          in (sexpr' :: sexprs, prev_names'))
      ([], prev_names1)
      sexprs
      in ((ty, SCall (fsexpr', List.rev sexprs')), prev_names2)
  | SIf (cond, s1, s2) ->
    let (cond', prev_names') = name_all' cond prev_names false
    in let (s1', prev_names1) = name_all' s1 prev_names' false
    in let (s2', prev_names2) = name_all' s2 prev_names1 false
      in ((ty, SIf (cond', s1', s2')), prev_names2)
  | SPrint sexpr -> 
    let (sexpr', prev_names') = name_all' sexpr prev_names false
      in ((ty, SPrint sexpr'), prev_names')

  in let (named, _) = name_all' sexpr [] false
    in (typ_decls, named)

(* lift lambda/let pairs *)
let lift_lambdas (typ_decls, sexpr) =
    let rec lift_lambdas' (ty, sx) = match sx with
      SLiteral _ | SFliteral _ | SBoolLit _ | SStringLit _ -> ((ty, sx), [])
    | SPairExpr (s1, s2) ->
        let (s1', fs1) = lift_lambdas' s1
        and (s2', fs2) = lift_lambdas' s2
          in ((ty, SPairExpr (s1', s2')), fs1 @ fs2)
    | SConsExpr (s1, s2) ->
        let (s1', fs1) = lift_lambdas' s1
        and (s2', fs2) = lift_lambdas' s2
          in ((ty, SConsExpr (s1', s2')), fs1 @ fs2)
    | SEmptyListExpr -> ((ty, SEmptyListExpr), [])
    | SName n -> ((ty, SName n), [])
    | SBinop (s1, op, s2) ->
        let (s1', fs1) = lift_lambdas' s1
        and (s2', fs2) = lift_lambdas' s2
          in ((ty, SBinop (s1', op, s2')), fs1 @ fs2)
    | SUnop (op, sexpr) ->
        let (sexpr', fs) = lift_lambdas' sexpr
          in ((ty, SUnop (op, sexpr')), fs)
    | SLet (bound_vars, body) ->
        let (bound_vars, fs) = List.fold_left
          (fun (bound_vars, fs) ((name, ty), sexpr) ->
            let ((ty', sx'), fs') = lift_lambdas' sexpr
              in match sx' with
                SFunction _ ->
                  (bound_vars, ((name, ty), (ty', sx')) :: fs' @ fs)
              | _ -> (((name, ty), (ty', sx')) :: bound_vars, fs))
              (* in match ty with
                FunType _ -> 
                  (bound_vars, ((name, ty), (ty', sx')) :: fs' @ fs)
              | _ -> (((name, ty), (ty', sx')) :: bound_vars, fs)) *)
          ([], [])
          bound_vars
        and (body', fs') = lift_lambdas' body
          in if bound_vars = []
            then (body', fs @ fs')
            else ((ty, SLet (bound_vars, body')), fs @ fs')
    | SFunction (params, body) ->
        let (body', fs) = lift_lambdas' body
          in ((ty, SFunction (params, body')), fs)
    | SStructInit (inits) ->
        let (inits', fs) = List.fold_left
          (fun (inits, fs) (name, sexpr) ->
            let (sexpr', fs') = lift_lambdas' sexpr
              in ((name, sexpr') :: inits, fs' @ fs))
          ([], [])
          inits
          in ((ty, SStructInit (inits')), fs)
    | SStructRef (struct_name, field) -> ((ty, SStructRef (struct_name, field)), [])
    | SCall (fsexpr, sexprs) ->
        let (fsexpr', fs1) = lift_lambdas' fsexpr
        in let (sexprs', fs2) = List.fold_left
          (fun (sexprs, fs) sexpr ->
            let (sexpr', fs') = lift_lambdas' sexpr
              in (sexpr' :: sexprs, fs' @ fs))
          ([], fs1)
          sexprs
          in ((ty, SCall (fsexpr', List.rev sexprs')), fs2)
    | SIf (cond, s1, s2) ->
        let (cond', fs') = lift_lambdas' cond
        and (s1', fs1) = lift_lambdas' s1
        and (s2', fs2) = lift_lambdas' s2
          in ((ty, SIf (cond', s1', s2')), fs2 @ fs1 @ fs')
    | SPrint sexpr ->
        let (sexpr', fs) = lift_lambdas' sexpr
          in ((ty, SPrint sexpr'), fs)

    in let (named, fs) = lift_lambdas' sexpr
      in (typ_decls, fs, named)
      
let lift_program sast = 
  lift_lambdas (name_all sast)
  (* match (name_all sast) with (typ_decls, sexpr) -> (typ_decls, [], sexpr) *)
