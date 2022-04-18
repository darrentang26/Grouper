
   type action = Ast | Sast | Lifting | LLVM_IR | Compile

   let () =
     let action = ref Compile in
     let set_action a () = action := a in
     let speclist = [
       ("-a", Arg.Unit (set_action Ast), "Print the AST");
       ("-s", Arg.Unit (set_action Sast), "Print the SAST");
       ("-f", Arg.Unit (set_action Lifting), "Print the lifted SAST");
       ("-l", Arg.Unit (set_action LLVM_IR), "Print the generated LLVM IR");
       ("-c", Arg.Unit (set_action Compile),
         "Check and print the generated LLVM IR (default)");
     ] in  
     let usage_msg = "usage: ./microc.native [-a|-s|-l|-c] [filename.grp]" in
     let channel = ref stdin in
     Arg.parse speclist (fun filename -> channel := open_in filename) usage_msg;
     
     let lexbuf = Lexing.from_channel !channel in
     let ast = Parser.program Scanner.token lexbuf in  
     match !action with
       Ast -> print_string (Ast.string_of_program ast)
     | _ -> let sast = Semant.check ast in
       match !action with
         Ast     -> ()
       | Sast    -> print_string (Sast.string_of_sprogram sast)
       | Lifting -> print_string (Sast.string_of_sprogram_lifted (Lifting.lift_program sast))
       | LLVM_IR -> print_string (Llvm.string_of_llmodule (Codegen.translate (Lifting.lift_program sast)))
       | Compile -> let m = Codegen.translate (Lifting.lift_program sast) in
     Llvm_analysis.assert_valid_module m;
     print_string (Llvm.string_of_llmodule m)
   