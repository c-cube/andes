
(** {1 Compile TIP problem into Logic problem} *)

module Term = Andes.Term

type t

val goal : t -> Term.t list

val stmts : Ast.statement list -> t
