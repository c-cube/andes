
(** {1 TIP frontend} *)

module Ast = Ast
module Compile = Compile

val parse_file : string -> (Ast.statement list, string) Result.result

val parse_stdin : unit -> (Ast.statement list, string) Result.result
