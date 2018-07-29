
(** {1 Simplification} *)

open Types

val simplify_c : Clause.t -> Clause.t option

val simplify_rule : Rule.t -> Rule.t option

