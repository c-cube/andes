
(** {1 TIP frontend} *)

module Ast = Ast
module Compile = Compile

let parse_file file : _ Result.result =
  Ast.parse ~include_dir:(Filename.dirname file) ~file Ast.Smtlib

let parse_stdin () : _ Result.result = Ast.parse_stdin Ast.Smtlib
