(*test_typeeq.ml*)

open Ast


let () =
    let a = AdtTypeExpr([("a", IntExpr); ("b", ListType(BoolExpr));]) in
    let b = AdtTypeExpr([("a", IntExpr); ("c", ListType(BoolExpr));])
in if a = b then print_string "success" else print_string "failure"
