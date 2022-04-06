open Ast
open Sast

exception Failure of string

(* the first character in an occurence of a free name is marked with * *)
let rec mark_free (t, sx) bound_names = match sx with
  SLiteral _ | SFliteral _ | SBoolLit _ | SStringLit _ -> (t, sx)
| SPairExpr (sexpr1, sexpr2) -> (t, SPairExpr (mark_free sexpr1 bound_names, mark_free sexpr2 bound_names))
| SConsExpr (sexpr1, sexpr2) -> (t, SConsExpr (mark_free sexpr1 bound_names, mark_free sexpr2 bound_names))
| SEmptyListExpr -> (t, sx)
| SName n -> (t, SName (if (List.exists (fun (x) -> x = n) bound_names) then n else ("*" ^ n)))
| SBinop (sexpr1, op, sexpr2) -> (t, SBinop (mark_free sexpr1 bound_names, op, mark_free sexpr2 bound_names))
| SUnop (uop, sexpr) -> (t, SUnop (uop, mark_free sexpr bound_names))
| SLet (binds, body) -> let
  (bound_names, binds) = List.fold_left
    (fun (bound_names, binds) ((name, tl), sexpr) -> match tl with
        FunType _ -> let
          bound_names = name :: bound_names
          in (bound_names, ((name, tl), mark_free sexpr bound_names) :: binds)
        | _ -> (name :: bound_names, ((name, tl), sexpr) :: binds))
    (bound_names, [])
    binds
    in (t, SLet (binds, mark_free body bound_names))
| SFunction ((name, ty), body) -> (t, SFunction ((name, ty), mark_free body [name]))
| SCall (s1, s2) -> (t, SCall (mark_free s1 bound_names, mark_free s2 bound_names))
| SIf (s1, s2, s3) -> (t, SIf (mark_free s1 bound_names, mark_free s2 bound_names, mark_free s3 bound_names))
| SPrint sexpr -> (t, SPrint (mark_free sexpr bound_names))

(* check for recursive variables in semant step *)


